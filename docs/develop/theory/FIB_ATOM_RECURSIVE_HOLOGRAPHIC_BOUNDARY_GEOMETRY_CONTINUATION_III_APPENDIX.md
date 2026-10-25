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
但它们的联合目标分别为 $(1/3,2)$ 与 $(0,1)$。

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

### 97.5 相对正则区域的合法解析片与联合响应乘积

**定义（完整来源与相对边界）。** 本小节复用
[严格实数联合相交支持卷](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md)
定义 1.1、12.2、14.1 的同一个来源模型。固定
$H_4=(0,J,24,M,147/5,J,24,M,18)$，随后按原始时钟取得两个 $M$
读数 $p,v$。令 $X$ 为满足该历史的完整严格实数世界

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
c=\frac{r(1-r)}b,
$$

其中始终要求

$$
0<r<1,\qquad b>0,\qquad c>0,\qquad
0\ne g\in\mathbb R[s],\quad\deg g\le3,\qquad d\in\mathbb R,
\qquad p\ne24.
$$

每个世界使用同一个完整多项式 $g$、同一个漂移 $d$，满足全部原始读数与
源方程；保留低次增益、采样零点、重复根、零漂移和奇异来源。所用图表的
非零分母守卫仍须成立，不能通过除去 $\Lambda=0$ 或 $F_0=0$ 来删去
合法世界。$X$ 取来源条目、补齐为四个的增益系数和漂移的通常拓扑。定义

$$
Y=\{(p,v)\in\mathbb R^2:p\ne24\},\qquad
\pi:X\longrightarrow Y,\quad \pi(W)=(p(W),v(W)),\qquad
C(p,v)=\pi^{-1}(p,v).
$$

这里 $q=(p,v)$ 仅表示基点，不与 §92 的 $q$-only 观察商混同。
令 $\mathcal B_\partial$ 为 DEV 定义 12.2 中四个带守卫的非负边界面
的基值像与两个角点基值之并，仅保留 $p\ne24$ 的点。DEV 定理 12.3
给出的相对非适当值集恰为

$$
\mathcal B_\partial\cup\{q_\infty\},\qquad
q_\infty=(-216/5,-225).
$$

这些边界来源不属于严格合法世界。令
$\Sigma_{\rm crit}\subset Y$ 为完整父曲面上
$\operatorname{rank}(d\pi)<2$ 的点的像；这里使用完整世界投影的微分。

**命题（DEV 定理 14.2 的来源特定应用；repo-derived）。** 设
$\mathcal U\subset Y$ 连通、可缩、开，且

$$
\mathcal U\cap
\bigl(\mathcal B_\partial\cup\{q_\infty\}\cup\Sigma_{\rm crit}\bigr)
=\varnothing.
$$

则 $\pi$ 在 $\mathcal U$ 的紧子集上适当，且存在常数
$0\le N\le24$ 与两两不同的合法解析截面
$W_i:\mathcal U\to X$，使每个完整纤维恰为
$C(q)=\{W_1(q),\ldots,W_N(q)\}$。取空乘积为 $1$，定义

$$
\begin{aligned}
\Delta_J(q)&=\prod_{1\le i<j\le N}
 \bigl(f_{MJ}(W_i(q))-f_{MJ}(W_j(q))\bigr),\\
\Delta_M(q)&=\prod_{1\le i<j\le N}
 \bigl(f_{MM}(W_i(q))-f_{MM}(W_j(q))\bigr).
\end{aligned}
$$

于是对每个 $q\in\mathcal U$，有精确等价

$$
q\in D_J\cap D_M
\quad\Longleftrightarrow\quad
\Delta_J(q)=\Delta_M(q)=0.
$$

若 $N<2$，两乘积均为 $1$，因而该区域没有任一种终端碰撞。
两个乘积可以由重叠或不交的配对分别归零，两对的公共终端值无需相同。

**证明。** 完整来源、目标域与排除集正是 DEV 定理 14.2 的对象与假设，
故直接应用该定理取得适当性、常数 $N$ 和穷尽完整纤维的解析截面；
$24$ 的界沿用其既有完整世界界，不另作估计。在实数域中，有限乘积
为零当且仅当至少一个因子为零。由于截面在每个基点两两不同，
$\Delta_J(q)=0$ 恰给出 $C(q)$ 中一对不同世界的 $f_{MJ}$ 相等；
$\Delta_M(q)=0$ 对 $f_{MM}$ 同理。两者在同一个 $q$ 成立正是联合事件
的量词，不附加跨配对的互异性或终端值相等条件。证毕。

**推论（严格世界内合并的必要边界）。** 在上述相对正则分析片的语境中，若
$W_n\ne W'_n$ 是不同的合法世界、$\pi(W_n)=\pi(W'_n)$，且两列都收敛到同一个
合法有限严格世界 $W_*\in X$，则 $W_*$ 必为 $\pi$ 的临界点，因而
$\pi(W_*)\in\Sigma_{\rm crit}$。该蕴含只讨论这种严格域内的有限合法极限；非法
边界极限与向 $q_\infty$ 的逃逸仍由排除集单独控制。

**证明。** 非临界点附近由逆函数定理存在 $\pi$ 单射的邻域。两列最终
都在其中，同基就迫使相等，矛盾。这只是严格域内合并的必要条件，
不保证临界点存在碰撞，也不保证配对互异性在极限中保留。证毕。

合法截面的乘积判据与 §97.2 的投影行列式及 $Z_E$ 有不同作用：前者在
上述区域内已经逐世界保留严格合法性，因而给出联合事件的等价刻画；
后两者只给出相应图表或异常包含扇区的必要外部条件，仍需严格实数提升。
解析截面是可能世界的数学标签，不是新增的可获取读数。即使两个零条件
足以判定这里的联合事件，也不由此恢复完整来源、统一度量或运输。

**命题（单终端碰撞的边界失标）。** DEV 定理 15.2--15.4 与推论 15.5
给出同一个相对域 $Y$ 内的解析基点族 $q(t)$，其中
$0\le t\le10^{-80}$。对每个 $t>0$，完整纤维恰有三个严格世界
$A(t),B(t),Q(t)$，其唯一无序 $f_{MM}$ 碰撞对为
$\{A(t),B(t)\}$，而 $f_{MJ}$ 在整个纤维上单射。$A$ 的严格守卫为

$$
b(A(t))=t>0,\qquad r(A(t))=1-u(t)t\in(0,1),\qquad 1<u(t)<2.
$$

在 $t=0$，$A$ 的辅助边界标签满足 $b=0,r=1$，失去严格合法性；
完整合法纤维只剩 $B(0),Q(0)$，且两个终端映射都单射。因此

$$
q(t)\in D_M\setminus D_J\quad(0<t\le10^{-80}),\qquad
q(t)\longrightarrow q_0=q(0)\in Y\setminus(D_J\cup D_M).
$$

特别地，$D_M$ 相对于 $Y$ 不闭；即使两个碰撞端点均要求 $b<1$，
其端点 $b$ 也不存在统一正下界。

**证明。** 世界穷尽性、唯一配对和两个终端映射的单射性直接复用
DEV 定理 15.4，其前提中的完整纤维过滤由定理 15.3 给出。
整个族保留 $3<p(t)<4$，故极限仍在 $p\ne24$ 的相对域中。
$A$ 的边界标签虽保留代数响应，却违反 $b>0,r<1$，不能补回合法纤维。
所以该 $D_M$ 中的基点序列在 $Y$ 内有不属于 $D_M$ 的极限，证明不闭。
又因 $b(A(t))=t\downarrow0$ 且 $b(B(t))<309/1000<1$，任何统一
正下界都被这族碰撞端点否定。证毕。

此族没有 $J$ 碰撞，因而不是联合碰撞或其存在性证据；结论中的不闭性
只属于该严格来源模型的终端 $M$ 碰撞基点集，不是物理空间的不闭性。
边界失标与前述严格世界内的临界合并是两种不同的极限机制。

**桥接条件（原生来源到完整载体）。** 一个足够的后续来源桥是：定义
同一历史的原生合法来源集合 $\mathcal S_{\rm native}$、基点映射
$q_{\rm native}$、两个原生终端响应
$F_{\rm native,MJ},F_{\rm native,MM}$，并构造
$L:\mathcal S_{\rm native}\to X$，使其在每个固定读出纤维上双射到
$C(p,v)$，同时满足

$$
\pi\circ L=q_{\rm native},\qquad
f_{MJ}\circ L=F_{\rm native,MJ},\qquad
f_{MM}\circ L=F_{\rm native,MM}.
$$

这些是待证的来源对应条件；若成立，双射保留配对内的互异性，交换关系
保留两种响应相等，故可把该区域的乘积判据拉回原生来源。它们仍不提供
§93 的统一度量控制或 §98 的光滑运输、测度、时钟与细化极限。
区域外的临界层、非适当边界和全局 $D_J\cap D_M$ 分类仍保持开放。

## 98. qutrit 上下文图的三维局部秩，不是物理空间维数

最新 DEV 的 `StabilizerCHSHGraphRegularity` 给出了一个精确的局部结果。
对素数 $p$，令 $G_p$ 的顶点是

$$
V_p=\mathbb Z_p^3,
$$

并用 `vertexProj` 取相应的 CHSH 稳定子秩一投影。该结果证明：

$$
|V_p|=p^3,
\qquad
\deg_{G_p}(v)=(2p-1)(p-1).
\tag{98.1}
$$

所以 qutrit 情形 $p=3$ 有 27 个顶点、10-regular 正交图。这里的 3
首先是每个局部 Hilbert 空间的维数；顶点实际位于
$\mathbb C^3\otimes\mathbb C^3$ 的秩一投影空间。它不能仅由顶点个数、
度数或正交关系改写成物理空间的三个坐标方向。

**命题 98.1（三个维数不可混同）。** 对局部 qutrit 有：

$$
\dim_{\mathbb C}\mathcal H_{\rm loc}=3,
\qquad
\dim_{\mathbb R}\mathbb {CP}^{2}=4.
\tag{98.2}
$$

对双 qutrit 的纯态射影空间则有：

$$
\dim_{\mathbb C}(\mathcal H_A\otimes\mathcal H_B)=9,
\qquad
\dim_{\mathbb R}\mathbb {CP}^{8}=16.
\tag{98.3}
$$

**证明。** $\mathbb {CP}^{d-1}$ 的实维数为 $2(d-1)$；代入 $d=3$ 与
$d=9$ 即得。□

因此同一段理论中至少同时出现 Hilbert 维数、纯态流形维数和上下文图的
组合规模。它们都可以出现数字 3 的幂或因子，但没有同构映射时不能互相
替代。

**命题 98.2（图正则性不决定空间维数）。** 设只给定有限抽象图 $G$ 的
顶点、边和正则度。则这些数据不能确定一个物理度量空间的维数。

**证明。** 图正则性的定义只涉及 $V$ 与 $E$，不含距离 $d$、测度 $\mu$、
边长、时间或运输算子。固定同一个 $G_p$，可以在其顶点上赋离散度量

$$
d_{\rm disc}(v,w)=\mathbf 1_{v\ne w},
$$

也可以取任意一组 $\mathbb R^3$ 中的互异点并赋其欧氏距离
$d_3(v,w)=|x_v-x_w|$。两种赋值保留完全相同的图和正则度，却给出不同的
几何数据。更高维的欧氏赋值同理。故若要谈空间维数，必须把度量及其与
边的局部性关系作为额外结构声明。□

这不是说图不能承载空间；它说明“能承载”需要一项桥接定理。特别地，
把 10-regular 读成“每点有十个空间邻方向”，或把 $p^3$ 读成“三维体积”，
都超出了 (98.1) 的量词。

## 定义 98.3　三维接口的桥接证书

对第 $j$ 个有限层，定义候选桥接实现：

$$
\mathfrak B_j=(\mathcal S_j,G_j,\pi_j,d_j,\mu_j,\partial_j,
\mathsf U_j,\vartheta_j).
\tag{98.4}
$$

其中 $\mathcal S_j$ 是真实 FIB 来源，$\pi_j:\mathcal S_j\to V(G_j)$ 是
来源到上下文顶点的映射，$d_j,\mu_j$ 是空间度量和测度，$\partial_j$ 是
边界，$\mathsf U_j$ 是合法运输的方向或局部酉作用，而 $\vartheta_j$ 是
时钟与边界响应记录。称它满足三维桥接证书，如果同时验证：

$$
\begin{array}{ll}
\text{(B1) 来源忠实性：}&
\pi_j\text{ 的纤维与声明的局部观察、任务和合法域一致};\\
\text{(B2) 局部秩：}&
\text{正则极限分支为光滑流形，运输生成元张成}\\
&\text{光滑常秩分布 }\mathcal D,\quad\operatorname{rank}\mathcal D=3;\\
\text{(B3) 运输局部性：}&
\text{一次合法更新只跨越受 }d_j\text{ 控制的半径};\\
\text{(B4) 对合与回路闭合：}&
\forall X,Y\in\Gamma^\infty(\mathcal D),\quad
 [X,Y]\in\Gamma^\infty(\mathcal D),\\
&[\mathcal D,\mathcal D]\subseteq\mathcal D,\quad
 \text{允许的 holonomy 留在接口纤维内};\\
\text{(B5) 体积窗口：}&
 c r^3\le\mu_j(B_{d_j}(x,r))\le C r^3;\\
\text{(B6) 递归相容：}&
\pi_j,d_j,\mathsf U_j,\vartheta_j\text{ 在细化接缝下有一致的限制与响应}.
\end{array}
\tag{98.5}
$$

其中 (B2)、(B4) 的光滑性、常秩三与对光滑截面的对合性须在同一正则
极限分支上成立；点态存在三个无关方向不能替代这些假设。(B3) 只约束
运输局部性，不单独供给可积性。

其中 (B5) 的常数和尺度窗口必须明确说明是否随 $j$ 一致；单层有限图
不能替代无限细化的体积估计。对上下文图，还需另加：

$$
\text{(B7)}\qquad
\text{图边由实际来源接缝和运输关系产生，而不是只由投影正交定义。}
\tag{98.6}
$$

**定理 98.4（桥接证书给出条件性的三维极限）。** 假设一列
$\mathfrak B_j$ 在给定的中尺度窗口满足 (B1)--(B7)，并且极限空间的测度
满足与度量球相同的局部上下界：

$$
0<c r^3\le\mu(B_d(x,r))\le C r^3<\infty
\tag{98.7}
$$

且 $\mu$ 与三维 Hausdorff 测度在该窗口相互绝对连续、密度有界。则每个
正则极限分支是局部 3-Ahlfors 正则的，因而其 Hausdorff 维数为 3；
(B2) 与 (B4) 在上述光滑、常秩条件下由 Frobenius 定理给出局部三维
积分切面，(B3) 另行约束合法运输的局部性。

**证明。** (98.7) 的上界给出任意 $s>3$ 时的 $s$ 维 Hausdorff 测度为零：
用半径 $r_i$ 的球覆盖并令 $r_i\to0$，有
$\sum_i r_i^s\le r_{\max}^{s-3}c^{-1}\sum_i\mu(B_i)\to0$。
下界和质量分布原理给出任意 $s<3$ 时的 $s$ 维 Hausdorff 测度为无穷，
所以维数恰为 3。B2 给出正则极限分支上的光滑常秩三分布
$\mathcal D$；B4 对所有光滑截面要求
$[\mathcal D,\mathcal D]\subseteq\mathcal D$。这正是光滑常秩分布的
Frobenius 对合假设，故得到局部三维积分切面。B3 是独立的运输局部性
条件，不参与这一步可积性推论。□

定理 98.4 的关键是条件的联合，而非任意一项单独成立。当前 DEV 的
CHSH 正则性只直接提供 (98.1) 所需的投影单射、秩一性质、迹归一和图度数；
它没有提供 $\pi_j,d_j,\mu_j,\partial_j,\vartheta_j$，也没有提供
(B3)--(B7)。所以它是局部上下文结构的精确结果，尚不是“物理空间为三维”
的证明。

## 推论 98.5　最新 DEV 如何修正边界读取

最新 DEV 的标量任务纤维结果还给出一个直接的边界警告：实际 Choi 序列
与显式可分 partner 可以具有相同的局部边缘和全部所声明的 SIC/MUB 标量
范数，却对固定精确任务具有不同的最优误差。于是，若 $\pi_j$ 只保留
上下文图的局部标量读数，就可能把两种不同的运输/任务响应放进同一观察
纤维。

因此三维桥接证书必须把“图上的局部投影”与“完整 FIB 任务响应”分开
登记：

$$
\boxed{
\text{上下文图正则性}
\;+
\text{来源映射与运输局部性}
\;+
\text{联合任务响应充分性}
}
\tag{98.8}
$$

才足以作为空间解释的候选接口。缺少任何一项时，最多得到局部 Hilbert
结构或一个有限图模型；不能把 qutrit 的 3 自动升级为物理空间的 3。

**开放边界 98.6。** 目前尚未证明 FIB 原生有序二叉树与 CHSH 投影图之间
存在满足 (B1)--(B7) 的统一来源到空间映射，也未证明存在一致的 $d_j$、
边界时钟和运输算子使 (98.7) 在细化极限成立。尤其是，有限 27 顶点的
qutrit 图不携带自身的无限尺度体积增长；需要另建细化族、接缝规则和
谱/运输收敛证明。该缺口是桥接义务，不是对已有 CHSH 正则性定理的反例。

## 99. 把三维桥接义务改写成体积、热核与谱的检验

§98 的 (B5) 和 (B6) 仍是结构性要求。为了让它们可以在 FIB 细化族上
被反驳或支持，必须把“维数”拆成不同的可测量量。对带权图

$$
\mathcal G_j=(V_j,E_j,c_j,\mu_j)
$$

取合法边的最短路距离 $d_j$，定义球体积：

$$
V_j(x,r)=\mu_j\bigl(B_{d_j}(x,r)\bigr).
\tag{99.1}
$$

在两个半径 $r_2>r_1$ 的有限尺度窗口中，定义局部体积维估计：

$$
\widehat d_{V,j}(x;r_1,r_2)
  =
\frac{\log V_j(x,r_2)-\log V_j(x,r_1)}
     {\log r_2-\log r_1}.
\tag{99.2}
$$

这不是把顶点度数当作空间维数；它测量的是球体积随半径的增长。

令 $L_j$ 是由 $c_j,\mu_j$ 定义的非负传播算子，令

$$
K_j(t)=e^{-tL_j},
\qquad
p_j(t,x)=K_j(t;x,x).
$$

在无边界的齐次窗口中，取平均返回概率

$$
P_j(t)=\frac1{\mu_j(V_j)}
\sum_{x\in V_j}\mu_j(x)p_j(t,x),
$$

并定义谱维估计：

$$
\widehat d_{s,j}(t_1,t_2)
  =
-2\frac{\log P_j(t_2)-\log P_j(t_1)}
          {\log t_2-\log t_1},
\qquad t_2>t_1.
\tag{99.3}
$$

若在某个窗口内具有标度关系

$$
p_j(t,x)\asymp t^{-d_s/2},
\qquad
\mathbb E_x d_j(X_t,x)^2\asymp t^{2/w},
$$

则：

$$
\boxed{d_s=\frac{2d_V}{w}.}
\tag{99.4}
$$

其中 $d_V$ 是体积维，$d_s$ 是谱维，$w$ 是游走维。二阶局部传播要求
$w=2$；异常扩散不能把 $d_s$ 直接当成空间切维数。

**命题 99.1（正则度数不决定体积维或谱维）。** 存在两个 10-regular
有限图族，它们的中尺度增长和热传播不同。

**证明。** 一族取三维离散环面的 Cayley 图：

$$
V_n=(\mathbb Z/n\mathbb Z)^3,
\qquad n\ge5\text{ odd},
$$

生成元取

$$
S=\{\pm e_1,\pm e_2,\pm e_3,
       \pm(e_1+e_2),\pm(e_1-e_2)\}.
$$

它是 10-regular；在 $1\ll r\ll n$ 的窗口，

$$
|B(v,r)|\asymp r^3,
$$

并且最近邻拉普拉斯具有扩散标度 $w=2$。另一族取存在的 10-regular
expander 族。其有统一正谱隙，在 $1\ll r\lesssim\log |V_n|$ 的窗口内，
球体积至少以

$$
|B(v,r)|\ge(1+\delta)^r
$$

的形式增长，其中 $\delta>0$ 与层级无关；其热核在相应窗口也不具有三维
环面的 $t^{-3/2}$ 返回概率标度。两族的每个顶点度数都等于 10，但
$(d_V,d_s,w)$ 不同。因此仅由 (98.1) 的正则度不能推出空间维数。□

这个反例也适用于 qutrit CHSH 图：$G_3$ 只有 27 个顶点，因而甚至没有
可供 $r\to\infty$ 的尺度窗口。把它与三维环面同样称为“10-regular”并
不能提供一个统一的空间实现。

**定义 99.2（有限层三维谱证书）。** 一列 FIB 图实现具有窗口
$[r_-,r_+]\times[t_-,t_+]$ 的三维谱证书，如果存在 $\epsilon_j\to0$，
使得对所有声明的体点和窗口端点：

$$
\begin{aligned}
\left|\widehat d_{V,j}-3\right|&\le\epsilon_j,\\
\left|\widehat d_{s,j}-3\right|&\le\epsilon_j,\\
\left|\frac{2\widehat d_{V,j}}{\widehat d_{s,j}}-2\right|&\le\epsilon_j,
\end{aligned}
\tag{99.5}
$$

并且边界影响满足：把 $x$ 限制在距 $\partial V_j$ 至少 $R_j$ 的区域时，
球体积和返回概率的相对误差趋于零；$R_j$ 覆盖所声明的整个窗口。该
证书还必须和 (B1)--(B4) 的来源、运输和回路条件联合，而不能只提交三条
数值斜率。

**定理 99.3（热核桥接到二阶三维稳定窗口）。** 假设一列 FIB 实现满足：

$$
\begin{array}{ll}
\text{(C1)}&\text{一致的局部 3-Ahlfors 体积界};\\
\text{(C2)}&\text{窗口内的双边高斯热核估计 }p_j(t,x,y)
  \asymp t^{-3/2}e^{-d_j(x,y)^2/(ct)};\\
\text{(C3)}&\text{运输更新的生成元在细化下收敛到 }-\kappa\Delta;\\
\text{(C4)}&\text{边界 Schur 响应和任务读出在同一来源纤维上收敛};\\
\text{(C5)}&\text{无横向运输泄漏，且边界不会隐藏负谱方向}.
\end{array}
\tag{99.6}
$$

则在该窗口：

$$
d_V=3,
\qquad d_s=3,
\qquad w=2.
\tag{99.7}
$$

若吸引核由同一个二阶 Green 算子产生，且局域化代价具有二阶缩放，
则第五至第六章的双尺度判据给出有限尺度稳定窗口

$$
2<d_V<4,
$$

其整数维解释为 $d_V=3$。

**证明。** (C1) 直接给出 $d_V=3$。将变量 $t=d_j(x,y)^2s$ 代入 (C2)
的热核积分，得到返回概率 $p_j(t,x,x)\asymp t^{-3/2}$，故 $d_s=3$；
典型位移为 $t^{1/2}$，故 $w=2$，也满足 (99.4)。(C3) 使该热核标度属于
同一个二阶传播，而不是另一个与 FIB 无关的赋值。(C4) 保证消去内部后，
谱和任务响应仍是同一对象的响应。(C5) 排除用投影删掉不稳定内部方向或
用非可积运输制造额外可达方向。于是可以应用此前二阶点源模型的远场和
局域化判据。□

定理 99.3 的结论是条件性桥接，不是对当前 CHSH 图的自动应用。当前
DEV 结果提供了局部投影图的精确正则性，却没有给出 (C1)--(C5) 中的
任意一组细化族数据。因此下一项实际检验应按顺序登记：

$$
\boxed{
\pi_j\;\longrightarrow\;d_j,\mu_j\;\longrightarrow\;L_j,K_j
\;\longrightarrow\;\text{边界 Schur 响应}\;\longrightarrow\;
\text{任务纤维充分性}.
}
\tag{99.8}
$$

不能先从 $p=3$ 或度数 10 预设 $d_V=3$，再反过来选择度量和热核。

**开放边界 99.4。** FIB 原生来源目前仍没有已证明的 $\pi_j$ 与合法
最短路 $d_j$，也没有可供 (99.2)--(99.5) 计算的无限细化图族。即便
未来得到三维体积和二阶热核，还须继续验证边界任务响应、负谱方向和
回路运输相容性；谱维证书不能单独替代全息边界充分性。

## 100. 联合多数任务：局部边界与联合支持约束

最新 DEV 的
`D5.S3.Quantum.Information.HedgingMajorityThreshold.result`
给出了一个适合接入本卷的联合任务样例。它研究 $n$ 个并行的二量子比特
游戏，初始共享振幅由 $\alpha$ 给出，单局成功投影由 $\theta$ 给出。令

$$
R_\alpha=\operatorname{diag}(\alpha^2,1-\alpha^2),
\qquad
D_\theta=\operatorname{diag}(\sin^2\theta,-\cos^2\theta),
$$

并写

$$
T_\theta=I\otimes D_\theta.
$$

设 $\Pi_{n,k,\theta}$ 是至少有 $k$ 局成功的联合投影，$\rho$ 是 Bob
施加任意有限 Kraus 通道后得到的输出。这里要求

$$
n<2k\le 2n,
\qquad
0<\alpha\le1,
$$

并把通道完整性写成 $\sum_lK_l^\dagger K_l=I$。

**定理 100.1（严格多数的联合支持门）。** 在上述模型中，存在一个保迹
通道使

$$
\operatorname{tr}(\Pi_{n,k,\theta}\rho)=1
$$

当且仅当

$$
\boxed{\alpha^2=\cos^2\theta.}
$$

该命题已由上述 DEV 声明的 `result` 在 Lean 中证明。它的量词是固定的：
有限 $n,k$、严格多数、给定实参数、有限 Kraus 家族，以及该声明中的二
量子比特来源。它没有覆盖 $k\le n/2$ 的多数以下任务，也没有给出一般
量子联合任务的局部到整体准则。

**证明机制。** 每个严格多数的两个成功词共享一个坐标，在该坐标上压缩
到 $T_\theta$ 的成功投影为零。因此

$$
\Pi_{n,k,\theta}
T_\theta^{\otimes n}
\Pi_{n,k,\theta}=0.
\tag{100.1}
$$

另一方面，保迹通道不改变 Alice 的边缘态，所以输出的 $T_\theta^{\otimes n}$
期望值由局部边缘完全确定：

$$
\operatorname{tr}(T_\theta^{\otimes n}\rho)
  =\operatorname{tr}(D_\theta R_\alpha)^n
  =(\alpha^2-\cos^2\theta)^n.
\tag{100.2}
$$

若联合输出全部落在 $\Pi_{n,k,\theta}$ 的像中，(100.1) 迫使 (100.2)
为零。严格多数条件给出 $n\ge1$，于是得到 $\alpha^2=\cos^2\theta$。
反向方向使用一个对 Bob 的单局对角单位变换，并取其 $n$ 重张量积；在该
等式成立时，它把初始单局向量变到成功向量，从而全部 $n$ 局同时成功。

这个证明显示一种特殊的局部—联合闭合：

$$
\boxed{
\text{局部边缘守恒}
\;+
\text{联合支持零压缩}
\;\Longrightarrow\;
\text{严格多数的必要条件}.
}
\tag{100.3}
$$

其中第二项是联合对象，不能从一组独立的单局数值自动重建。局部边缘
只负责给出 (100.2)；联合投影的像空间负责把它压成零。两者必须来自同一
个输出态和同一个任务，而不能把分别可实现的边缘响应拼成一个联合证书。

**反例 100.2（相同边缘，不同联合任务）。** 在两个二值寄存器上取

$$
\rho_{\mathrm{same}}
 =\tfrac12\lvert00\rangle\langle00\rvert
  +\tfrac12\lvert11\rangle\langle11\rvert,
$$

$$
\rho_{\mathrm{diff}}
 =\tfrac12\lvert01\rangle\langle01\rvert
  +\tfrac12\lvert10\rangle\langle10\rvert.
$$

两者的每个单寄存器边缘都是 $I/2$，但“两个结果相同”的联合投影在前者
上的概率为 $1$，在后者上为 $0$。因此，保存所有单局边缘并不等于保存
联合支持、回路关联或多数事件的可判定性。

在 FIB 的边界语言中，这给出一个更窄但可计算的结论。若任务只要求判断
本定理中的严格多数可达性，则局部参数 $R_\alpha$ 加上声明的联合投影
规则足以给出精确门槛；若任务改成恢复任意联合输出、联合来源或操作合法
域，则边界还必须保留相应的联合响应或一个等价的支持见证。单独的三分量
接口、单局边缘或单个静态谱值，都不能替代这个见证。

这也修正“局部边界充分”的用法：它不是一个只看接口维数的性质，而是相
对于目标和允许操作的性质。定理 100.1 证明了一个特定量子联合任务中的
局部不变量与联合支持约束如何闭合；它没有证明 FIB 原生来源已经产生了
物理三维空间，也没有消除 §95--§99 所列的运输、测度、时钟、边界和无限
细化义务。
## 101. A positive full-domain binding threshold for the higher-order added law

**Definition 101.1 (fixed field and variational threshold).** Retain precisely the source of Continuation III, §§82–87: $G=H^1\times\mathbb R$, its unit source $e$, Lebesgue Haar measure $d\mu=dx\,dy\,dz\,dw$, the original horizontal fields $X_i$, the original free generator $L$ and its clock, and its positive degree-$-3$ Green field $\Gamma$. In the shear coordinates $\xi=(x,y,z)$, $s=w-xy/2$, write $\mathcal G(\xi,s)=\Gamma(x,y,z,s+xy/2)$. For $\sigma>2$ use the complex distributional form domain $\mathcal E_\sigma$ of (87.1), with no central band or common central budget, and put

$$
\begin{gathered}
T[\psi]=\sum_{i=1}^3\|X_i\psi\|_2^2,\qquad
D_\nu[\psi]=\big\||D_w|^{\nu/2}\psi\big\|_2^2,\qquad
V[\psi]=\int_G\Gamma|\psi|^2d\mu,\\
S_{a,\eta}[\psi]=aT[\psi]+\eta D_\sigma[\psi],\qquad
q_{a,\eta,g}[\psi]=S_{a,\eta}[\psi]-gV[\psi],\\
I_\sigma(a,\eta,g)=\inf_{\substack{\psi\in\mathcal E_\sigma\\\|\psi\|_2=1}}
 q_{a,\eta,g}[\psi],\qquad
 g_\sigma^*(a,\eta)=\inf_{0\ne\psi\in\mathcal E_\sigma}
 \frac{S_{a,\eta}[\psi]}{V[\psi]},\\
\alpha=\frac{2\sigma-3}{2\sigma-2},\qquad
\beta=\frac1{2\sigma-2},\qquad \alpha+\beta=1,\qquad a,\eta>0,\quad g\ge0.
\end{gathered}
\tag{101.1}
$$

Theorem 87.2 gives $\mathcal E_\sigma\subset\mathcal E_2\subset D(M_{\sqrt\Gamma})$, and $T,D_\sigma,V$ are finite and strictly positive at every nonzero state of this domain. Amplitude normalization therefore leaves the threshold quotient unchanged. This is the added kinetic law; the field in $V$ remains the Green field of the original $L$, rather than a Green field regenerated from the added operator.

**Proposition 101.2 (norm-free estimate for the actual full field).** On the entire $\mathcal E_\sigma$, for every nonzero complex state,

$$
D_1[\psi]\le T[\psi],\qquad
0<V[\psi]<\frac18\,T[\psi]^\alpha D_\sigma[\psi]^\beta.
\tag{101.2}
$$

In particular the bound involves no power of $\|\psi\|_2$ and no projection of the potential. Its constant $1/8$ is a sufficient constant here; its optimality for $\sigma>2$ is not asserted.

**Proof.** Use the actual unitary central transform $b(\xi,\lambda)$ of (87.2). In the magnetic fibre (85.7) put

$$
A_\lambda=\partial_x-i\lambda y/2,\qquad
B_\lambda=\partial_y+i\lambda x/2.
$$

They are skew symmetric on compact smooth functions, and $[A_\lambda,B_\lambda]=i\lambda$. Integration by parts gives, for $\lambda\ne0$,

$$
\begin{aligned}
t_\lambda[f]
 &=\|(A_\lambda-i\operatorname{sgn}(\lambda)B_\lambda)f\|_2^2
   +|\lambda|\|f\|_2^2+\|\partial_zf\|_2^2\\
 &\ge |\lambda|\|f\|_2^2.
\end{aligned}
\tag{101.3}
$$

Closure extends the inequality to the fibre form domain; at $\lambda=0$ its asserted lower bound is zero. Integration over all central frequencies, using the closed free direct integral of Proposition 85.2, proves $D_1\le T$ on $D(L^{1/2})$. In particular this controls the actual central first moment, without replacing magnetic derivatives by ordinary derivatives.

With $\theta=(\sigma-2)/(\sigma-1)$, the identity $2=\theta+(1-\theta)\sigma$ and Hölder applied to $|b|^2d\xi d\lambda$ give

$$
D_2\le D_1^{(\sigma-2)/(\sigma-1)}D_\sigma^{1/(\sigma-1)}.
\tag{101.4}
$$

The strict actual-field endpoint (87.3), followed by (101.4) and $D_1\le T$, yields

$$
V<\frac18\sqrt{TD_2}
 \le\frac18 T^{1/2}D_1^{(\sigma-2)/(2\sigma-2)}D_\sigma^{1/(2\sigma-2)}
 \le\frac18 T^\alpha D_\sigma^\beta.
$$

All quantities are those of the same state. The zero vector satisfies the non-strict continuous version with both sides zero. $\square$

**Theorem 101.3 (finite positive threshold and the binding alternatives).** Define the explicit sufficient coupling

$$
g_{\rm suf}(a,\eta)=\frac{8a^\alpha\eta^\beta}{\alpha^\alpha\beta^\beta}.
\tag{101.5}
$$

Then

$$
0<g_{\rm suf}(a,\eta)\le g_\sigma^*(a,\eta)<\infty,
\qquad
\begin{cases}
I_\sigma(a,\eta,g)=0,&0\le g\le g_\sigma^*(a,\eta),\\
-\infty<I_\sigma(a,\eta,g)<0,&g>g_\sigma^*(a,\eta).
\end{cases}
\tag{101.6}
$$

For every $0\le g<g_\sigma^*(a,\eta)$ the zero infimum is not attained, and more precisely

$$
q_{a,\eta,g}[\psi]\ge
 \left(1-\frac{g}{g_\sigma^*(a,\eta)}\right)S_{a,\eta}[\psi]>0
 \quad(0\ne\psi\in\mathcal E_\sigma).
\tag{101.7}
$$

The explicit range $0\le g\le g_{\rm suf}$ also has strictly positive energy at every nonzero state and no normalized minimizer, including its endpoint. For $g>g_\sigma^*$ the negative infimum is attained by a normalized state in exactly $\mathcal E_\sigma$, and this state is an eigenvector of the represented self-adjoint operator. No positivity or simplicity of that eigenvector is part of this assertion.

**Proof.** Weighted arithmetic–geometric mean gives

$$
T^\alpha D_\sigma^\beta
 \le\frac{\alpha^\alpha\beta^\beta}{a^\alpha\eta^\beta}
      (aT+\eta D_\sigma).
\tag{101.8}
$$

Thus (101.2) gives $V<S_{a,\eta}/g_{\rm suf}$ at every nonzero state, proving the positive lower bound for the threshold and the claimed strict positivity throughout the sufficient range. Any fixed nonzero punctured core state has $0<V<\infty$ and finite $S_{a,\eta}$, so its quotient proves that the threshold is finite. The infimum may equivalently be taken over that core: its density in $\mathcal E_\sigma$ is (87.1), and (87.4), applied to differences, gives convergence in $L^2(G,\Gamma d\mu)$ under form-norm approximation. Consequently the quotient converges at every nonzero limit state.

The defining infimum implies $S_{a,\eta}\ge g_\sigma^*V$ on the whole domain, giving (101.7) and nonnegativity also at $g=g_\sigma^*$. For the matching zero upper bound take a normalized core state and the outward Carnot dilation

$$
\delta_R(x,y,z,w)=(Rx,Ry,Rz,R^2w),\qquad
(U_R\psi)(p)=R^{-5/2}\psi(\delta_{1/R}p).
$$

The same Haar measure, horizontal fields and original degree-$-3$ field give the exact identities

$$
\|U_R\psi\|_2=\|\psi\|_2,\qquad
T[U_R\psi]=R^{-2}T[\psi],\qquad
D_\sigma[U_R\psi]=R^{-2\sigma}D_\sigma[\psi],\qquad
V[U_R\psi]=R^{-3}V[\psi].
\tag{101.9}
$$

Each $U_R$ is a bijection of $\mathcal E_\sigma$. Letting $R\to\infty$ proves $I_\sigma\le0$ for every finite $g$. Strict per-state positivity excludes attainment in the stated ranges; it does not furnish a uniform gap on the normalized sphere.

If $g>g_\sigma^*$, the definition of infimum supplies a genuine state whose quotient is less than $g$. Its normalization has negative energy. The semiboundedness, exact closed form domain, full weighted compactness and negative-infimum attainment are precisely Theorem 87.5, applied to this $a,\eta,\sigma,g$ and this unchanged $V$. They give finiteness and the normalized eigenvector. This use requires an already established negative trial; weighted compactness alone is not a zero-energy attainment assertion. $\square$

**Theorem 101.4 (exact coefficient scaling and an actual-field trial bound).** Put

$$
\mathcal C_\sigma=\sup_{0\ne\psi\in\mathcal E_\sigma}
 \frac{V[\psi]}{T[\psi]^\alpha D_\sigma[\psi]^\beta},\qquad
\kappa_\sigma=g_\sigma^*(1,1).
\tag{101.10}
$$

These constants refer to the full actual-field domain, and

$$
0<\mathcal C_\sigma\le\frac18,\qquad
\kappa_\sigma=\frac1{\alpha^\alpha\beta^\beta\mathcal C_\sigma},\qquad
g_\sigma^*(a,\eta)=a^\alpha\eta^\beta\kappa_\sigma.
\tag{101.11}
$$

For all $g\ge0$ the energy scaling is exactly

$$
I_\sigma(a,\eta,g)
 =a^{\sigma/(\sigma-1)}\eta^{-1/(\sigma-1)}
 I_\sigma\!\left(1,1,\frac{g}{a^\alpha\eta^\beta}\right).
\tag{101.12}
$$

For any normalized nonzero actual form trial $v$, writing $T_v=T[v]$, $d_v=D_\sigma[v]$ and $V_v=V[v]$, its optimally dilated quotient supplies

$$
\begin{gathered}
R_v=\left(\frac{(2\sigma-3)\eta d_v}{aT_v}\right)^{1/(2\sigma-2)},\\
g_\sigma^*(a,\eta)\le
 \frac{(aT_v)^\alpha(\eta d_v)^\beta}{\alpha^\alpha\beta^\beta V_v}.
\end{gathered}
\tag{101.13}
$$

In particular a fixed trial, with no change of field or carrier, is

$$
v_0(x,y,z,w)=\pi^{-1}
 \exp\!\left[-\frac{x^2+y^2+z^2+(w-xy/2)^2}{2}\right],\qquad
M_\sigma=\frac{\Gamma_{\!E}((\sigma+1)/2)}{\sqrt\pi},
\tag{101.14}
$$

where $\Gamma_{\!E}$ denotes Euler's gamma function. It has norm one, belongs to $\mathcal E_\sigma$ for every finite $\sigma>0$, and satisfies

$$
\begin{gathered}
T[v_0]=\frac{13}{8},\qquad D_\sigma[v_0]=M_\sigma,\\
\mathcal V_0:=V[v_0]
 =\frac1{\pi^2}\int\mathcal G(\xi,s)e^{-|\xi|^2-s^2}d\xi ds\\
 =\frac1{\pi^{5/2}}\int_0^\infty\!\int_0^\infty
 \frac{e^{-\lambda^2/4}\lambda}
 {\sqrt{1+4t}\,\sinh(\lambda t)\,[4+\lambda\coth(\lambda t)]}
 \,dt\,d\lambda\ \in(0,\infty),\\
g_\sigma^*(a,\eta)\le
 \frac{(13a/8)^\alpha(\eta M_\sigma)^\beta}
 {\alpha^\alpha\beta^\beta\mathcal V_0}.
\end{gathered}
\tag{101.15}
$$

This is an actual-field trial upper bound, not an asserted value of the exact threshold. A completely elementary, less precise upper bound follows by replacing $\mathcal V_0$ in its denominator by

$$
\mathcal V_{\rm low}
 =\frac{e^{-1/4}}{3\pi^{5/2}\sinh(2)[4+\coth(1)]}
 \le\mathcal V_0.
\tag{101.16}
$$

**Proof.** From (101.9), the quotient along the orbit of $v$ is

$$
\frac{S_{a,\eta}[U_Rv]}{V[U_Rv]}
 =\frac{aT_vR+\eta d_vR^{3-2\sigma}}{V_v}.
\tag{101.17}
$$

Its derivative vanishes at exactly $R_v$; it diverges at both ends because $2\sigma-3>0$. Its minimum is the right side of (101.13). Taking the infimum over all nonzero $v$ is the same as taking the infimum over all states and all $R>0$, since each $U_R$ is a domain bijection and $R=1$ is allowed. The infimum of $T^\alpha D_\sigma^\beta/V$ is $1/\mathcal C_\sigma$. Positivity and finiteness of this supremum follow from (101.2) and any nonzero trial, proving (101.11).

For energy scaling choose $\rho=(\eta/a)^\beta$. Then

$$
\begin{aligned}
q_{a,\eta,g}[U_\rho\psi]
 &=a\rho^{-2}\left(T[\psi]+D_\sigma[\psi]
       -\frac{g}{a\rho}V[\psi]\right),\\
a\rho&=a^\alpha\eta^\beta,\qquad
a\rho^{-2}=a^{\sigma/(\sigma-1)}\eta^{-1/(\sigma-1)}.
\end{aligned}
\tag{101.18}
$$

The unitary domain bijection makes the normalized infima equal, proving (101.12), including where they vanish.

For the Gaussian, the shear has Jacobian one. In $(\xi,s)$ coordinates the three derivatives are $(-x+ys/2)v_0$, $(-y-xs/2)v_0$, and $-zv_0$. Their mixed terms cancel. Each coordinate has variance $1/2$ under $|v_0|^2$, giving $T=3/2+1/8$. The unitary central Fourier transform of the normalized one-dimensional Gaussian is itself, so its $|\lambda|^\sigma$ moment is $M_\sigma$. These facts also check membership in the actual distributional domain, rather than only an ordinary Sobolev domain.

For the potential use the original central Green transform $K_\xi(\lambda)$ of (85.12). Pairing its inverse with $e^{-s^2}$ supplies $\sqrt\pi e^{-\lambda^2/4}/(2\pi)$. The $z$ Gaussian integral of its heat integrand supplies $(1+4t)^{-1/2}$, and the $(x,y)$ integral supplies

$$
\frac{|\lambda|}
 {\sinh(|\lambda|t)\,[4+|\lambda|\coth(|\lambda|t)]}.
$$

Together with $\pi^{-2}$ and the two frequency signs this is exactly (101.15). The pointwise inverse is valid for $\xi\ne0$ by Proposition 85.4. The bound $0<K_\xi(\lambda)\le(4\pi|\xi|)^{-1}$ makes its Gaussian Fourier pairing integrable in $(\xi,\lambda)$; the nonnegative heat integrand then permits Tonelli. Alternatively finiteness already follows from (87.4). The Gaussian never replaces $\mathcal G$ by its marginal.

To obtain (101.16), restrict the positive double integral to $0<\lambda<1$, $1<t<2$. There $e^{-\lambda^2/4}\ge e^{-1/4}$, $\sqrt{1+4t}\le3$, $\lambda/\sinh(\lambda t)\ge1/\sinh(2)$, and $\lambda\coth(\lambda t)\le\coth(1)$. The last two bounds follow from the decrease of $u/\sinh u$ and the increase of $u\coth u$ on $(0,\infty)$. This rectangle has area one. Substitution into (101.13) gives both trial bounds without a numerical sharpness assertion. $\square$

**Theorem 101.5 (critical extremizers and the necessary virial balance).** Let $g=g_\sigma^*(a,\eta)$ and let $H_{a,\eta,g}$ be the operator represented by the closed form on $\mathcal E_\sigma$. The following existence statements are equivalent:

- the normalized infimum $I_\sigma(a,\eta,g)=0$ is attained;
- the quotient $S_{a,\eta}/V$ attains $g_\sigma^*(a,\eta)$ at a nonzero $L^2$ form state;
- $\ker H_{a,\eta,g}\ne\{0\}$;
- the supremum $\mathcal C_\sigma$ in (101.10) is attained by a nonzero state in $\mathcal E_\sigma$.

Every critical zero state $\psi$ satisfies both the weak equation

$$
a\,t(\phi,\psi)+\eta\,d_\sigma(\phi,\psi)
 =g_\sigma^*(a,\eta)\,v(\phi,\psi)
 \qquad(\phi\in\mathcal E_\sigma),
\tag{101.19}
$$

and the balances

$$
\begin{gathered}
g_\sigma^*V[\psi]=aT[\psi]+\eta D_\sigma[\psi],\\
2aT[\psi]+2\sigma\eta D_\sigma[\psi]=3g_\sigma^*V[\psi],\\
aT[\psi]=(2\sigma-3)\eta D_\sigma[\psi],\qquad
 aT[\psi]=\alpha g_\sigma^*V[\psi],\quad
 \eta D_\sigma[\psi]=\beta g_\sigma^*V[\psi].
\end{gathered}
\tag{101.20}
$$

Here $t,d_\sigma,v$ are the sesquilinear forms polarized from $T,D_\sigma,V$, with $v(\phi,\psi)=\int\Gamma\overline\phi\psi\,d\mu$. The converse extremizer correspondence is precise: if $v$ attains $\mathcal C_\sigma$, then $U_{R_v}v$, after amplitude normalization, is a critical zero state; any critical zero state already attains $\mathcal C_\sigma$ and has $R_\psi=1$.

**Proof.** At critical coupling the closed form is nonnegative on exactly $\mathcal E_\sigma$ by Theorems 87.5 and 101.3. Thus zero energy is equivalent to quotient equality, and homogeneity permits normalization. Cauchy–Schwarz for the nonnegative form shows that $q[\psi]=0$ implies $q(\phi,\psi)=0$ for all form tests. Form representation then puts $\psi$ in $D(H_{a,\eta,g})$ with $H_{a,\eta,g}\psi=0$; the converse follows from the same representation. This proves (101.19), without requiring the separate multiplier vector $\Gamma\psi$ to lie in $L^2$.

For a critical zero state, the real scalar function $q[U_R\psi]$ is nonnegative for every $R>0$ and vanishes at $R=1$. Its exact expression (101.9) is differentiable even when the state has no dilation-generator derivative in $L^2$. Differentiation of that scalar expression gives the second line of (101.20); combining it with $q[\psi]=0$ gives the remaining balances. Equivalently the state minimizes its dilation-orbit quotient at $R=1$. Its equality in the global quotient and in (101.17)'s orbit minimum, together with (101.11), forces $V/(T^\alpha D_\sigma^\beta)=\mathcal C_\sigma$. Conversely an extremizer of this last ratio reaches the global quotient at its explicit $R_v$, giving zero energy there. $\square$

**Definition 101.6 (supplier correspondence and the unresolved critical alternative).** The source-specific inference is repository-derived: the actual magnetic first-moment bound (101.3), spectral interpolation and the actual-field endpoint combine to make a positive threshold on the full domain, followed by dilation optimization and the binding classification. Its mature intermediate supplies have the following limited roles.

The [Krötz–Thangavelu–Xu primary text](https://arxiv.org/abs/math/0401243v2), §4.1, equation (4.1.2), uses $n=1$, Lebesgue Haar measure and the symmetric Heisenberg product used in (85.1). Its partial central transform uses $e^{+i\lambda s}$, whereas (87.2) uses $e^{-i\lambda s}$; changing $\lambda$ to $-\lambda$ leaves the radial heat coefficient even. Multiplication by the independent $z$ heat factor $(4\pi t)^{-1/2}e^{-z^2/(4t)}$ gives exactly the original $H^1\times\mathbb R$ integrand in (85.12), hence the field used in (101.15). Its §2 full Laplacian, containing an additional central second derivative, is a different generator. The commutator calculation (101.3) uses the actual fibre derivatives and does not transfer a heat estimate from that different generator.

The [Alvino–Ferone–Volpicelli primary text](https://arxiv.org/abs/1105.0335v1), Theorem 1.1 and equation (8), has $n=4$, $\beta_{\rm AFV}=2$ in the supplier of (87.5): its constant is $H(4,2)=2/\pi$ on each halfspace, and hence $4/\pi$ on both. The parameter $\beta_{\rm AFV}$ is unrelated to the exponent $\beta$ in (101.1). The passage from that trace inequality to the strict actual-field endpoint is Theorem 87.2; the halfspace trace weight is not the original potential. [Teschl's primary text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), Theorems 6.24 and 2.13, supplies KLMN and closed-form representation on the Hilbert space $L^2(G,d\mu)$. Their client hypotheses and the full weighted compactness required for negative attainment are those proved in Theorem 87.5, not a new assertion that form compactness preserves mass at zero energy.

Whether any of the equivalent critical existence statements in Theorem 101.5 holds for this actual $\mathcal E_\sigma$ and $\Gamma$ remains unresolved here. In particular boundedness of a quotient-minimizing sequence in the homogeneous kinetic quantity does not itself bound its $L^2$ mass, and inhomogeneous weighted compactness from §87.5 does not supply that missing bound. The virial balance is necessary and is not asserted sufficient without the extremizer condition. Neither $\mathcal C_\sigma$ nor $\kappa_\sigma$ is evaluated sharply; $g_{\rm suf}$ and the trial bounds are only certified bounds. The correspondence asserts no exhaustive literature novelty.

The mathematical carrier, original field, Haar measure, horizontal kinetic form and clock in these statements are fixed throughout. There is no finite-band restriction, marginal-field substitution or modification of the original-law fixed-budget problem. No positive heat or Markov law for the $\sigma>2$ added kinetic operator is assumed. A native source-to-state realization and a physical dimension conclusion require additional bridges not contained in these variational statements.

## 追加锚（本行以下为增补区）

## 102. Actual critical zero states from a source-specific mass bound

**Definition 102.1 (unchanged source and auxiliary constants).** Use exactly Definition 101.1, including the complex domain $\mathcal E_\sigma$, the original degree-$-3$ field $\Gamma$, Lebesgue Haar measure, and $\sigma>2$, $a,\eta>0$. Put

$$
\begin{gathered}
s=w-xy/2,\qquad \xi=(x,y,z),\qquad
\rho(p)=\bigl(|\xi|^4+s^2\bigr)^{1/4},\\
B_\Gamma=\sup_{p\ne e}\rho(p)^3\Gamma(p),\qquad
Z_\sigma=|D_w|^\sigma,\qquad
A=aL+\eta Z_\sigma.
\end{gathered}
\tag{102.1}
$$

The sum defining $A$ is the nonnegative joint spectral sum of the strongly commuting free operators, not the interacting operator. Its represented form is $S_{a,\eta}$ on $\mathcal E_\sigma$. Write $H_{a,\eta,g}$ for the represented interacting operator of §101.5, and retain the sesquilinear forms $t,d_\sigma,v$ and inner product convention of that section.

The gauge $\rho$ is the homogeneous norm already used in the proof of (85.28). In shear coordinates the group product is the symmetric Heisenberg product times the independent $z$ addition; its first stratum has dimension three and its second stratum dimension one. Thus its homogeneous dimension is $Q=3+2=5$, its dilations are precisely (101.9), and the shear has Jacobian one. Smoothness and degree $-3$ of the actual Green field on the compact unit $\rho$ sphere give

$$
0<B_\Gamma<\infty,\qquad
0<\Gamma(p)\le B_\Gamma\rho(p)^{-3}\quad(p\ne e).
\tag{102.2}
$$

Fix finite constants $h_1,h_2$ supplied by Ciatti–Cowling–Ricci, *Hardy and uncertainty inequalities on stratified Lie groups*, [primary text](https://arxiv.org/html/1308.2373v1), Theorem A, Theorem 3.1 and Corollary 3.2, for this norm, this sub-Laplacian and $p=2$, at orders $1$ and $2$, respectively. Both orders lie strictly below $Q/p=5/2$. Set $K_\Gamma=B_\Gamma h_1h_2$. These constants are finite control constants; no optimal value is assigned to them.

**Theorem 102.2 (uniform mass control for actual nonpositive-energy states).** Suppose $g\ge0$, $\varepsilon\ge0$ and $u\in\mathcal E_\sigma$ satisfy the actual weak equation

$$
a\,t(\phi,u)+\eta\,d_\sigma(\phi,u)
 -g\,v(\phi,u)=-\varepsilon\langle\phi,u\rangle
 \qquad(\phi\in\mathcal E_\sigma).
\tag{102.3}
$$

Then

$$
\|u\|_2\le\frac{gK_\Gamma}{a}\sqrt{T[u]}.
\tag{102.4}
$$

In particular, every nonpositive-energy eigenstate of $H_{a,\eta,g}$ obeys this bound, uniformly as its eigenvalue approaches zero. If also $V[u]=1$, then

$$
S_{a,\eta}[u]=g-\varepsilon\|u\|_2^2\le g,
\qquad
\|u\|_2^2\le\frac{K_\Gamma^2g^3}{a^3}.
\tag{102.5}
$$

The estimate requires the equation; it is not a bound for arbitrary states with bounded homogeneous kinetic quantity.

**Proof.** The cited Hardy inequalities, as mature intermediates, give on $C_c^\infty(G)$

$$
\|\rho^{-1}f\|_2\le h_1\|L^{1/2}f\|_2,
\qquad
\|\rho^{-2}f\|_2\le h_2\|Lf\|_2.
\tag{102.6}
$$

Their client sub-Laplacian is exactly $L=-X_1^2-X_2^2-X_3^2$ from (84.1): the three original horizontal fields form a basis of the first stratum and have zero divergence for the stated Haar measure. Passing to shear coordinates changes neither the measure nor this operator, and does not add a central second derivative. The supplier's homogeneous norm may be chosen to be $\rho$; no equivalence with an unverified explicit Green formula is required. The first inequality is used only at order one, and the second is the order-two Rellich inequality furnished by the same corollary.

Here are the core and closure details for extending (102.6). For a smooth compact approximate identity $\kappa_j$ on $G$, convolution $\kappa_j*f$ is an average of left translates of $f$. Left translation commutes with every $X_i$ and preserves the closed free form. Its unitary action therefore commutes with the represented $L$. Consequently, for $f\in D(L)$,

$$
L(\kappa_j*f)=\kappa_j*(Lf),\qquad
\kappa_j*f\longrightarrow f\quad\hbox{in }D(L)
\tag{102.7}
$$

with its graph norm. For $f\in D(L^{1/2})$, the identities $X_i(\kappa_j*f)=\kappa_j*(X_if)$ give the corresponding convergence in the free form norm. These convergence statements follow from strong continuity of translations on $L^2$, applied also to $Lf$ or $X_if$. Convolution is smooth: after changing the integration variable, local derivatives fall on the smooth compact convolution factor, and are locally integrable against $f\in L^2$.

To obtain compact support, take a smooth compact $\chi$ equal to one near $e$ and put $\chi_R=\chi\circ\delta_{1/R}$. Homogeneity gives $\|X_i\chi_R\|_\infty=O(R^{-1})$ and $\|L\chi_R\|_\infty=O(R^{-2})$. For a fixed smoothed function $f_j=\kappa_j*f$, the distributional product identity is

$$
L(\chi_Rf_j)=\chi_RLf_j
 -2\sum_i(X_i\chi_R)(X_if_j)+(L\chi_R)f_j.
\tag{102.8}
$$

If $f\in D(L)$, all terms on the right are in $L^2$, since $D(L)\subset D(L^{1/2})$. Dominated convergence for the first term and the displayed derivative bounds for the other terms give graph convergence as $R\to\infty$. The product is in $C_c^\infty(G)$, so it is in the domain of the represented free operator; (102.8) is its operator action. The first-derivative product rule proves the same cutoff convergence in the free form norm. Choosing $R$ after $j$ proves that $C_c^\infty(G)$ is a core both for $L$ and for its form. These are free cores; no interacting operator core is asserted or used.

Apply (102.6) to differences of these core approximants. The weighted functions are Cauchy in $L^2$, and a subsequence converging almost everywhere in the unweighted $L^2$ space identifies their limits with $\rho^{-1}f$ or $\rho^{-2}f$, respectively. The identity element is a Haar-null set. Thus the first inequality extends to all of $D(L^{1/2})$, and the second to all of $D(L)$. In particular (102.2), Cauchy–Schwarz and these extended inequalities give the actual, absolutely convergent pairing estimate

$$
\begin{aligned}
\int_G\Gamma|\overline\phi u|\,d\mu
 &\le B_\Gamma\|\rho^{-2}\phi\|_2\|\rho^{-1}u\|_2\\
 &\le K_\Gamma\|L\phi\|_2\sqrt{T[u]}
 \qquad\bigl(\phi\in D(L),\ u\in D(L^{1/2})\bigr).
\end{aligned}
\tag{102.9}
$$

This is a pairing estimate, not the assertion $\Gamma u\in L^2$.

For completeness, the free resolvent used as a form test has the required domain on the full central spectrum. Proposition 85.2 identifies $L$ with its actual central direct integral and gives strong commutation with the central spectral projections. Thus $L$ and $Z_\sigma$ have a joint spectral measure on $[0,\infty)^2$, with variables $(\ell,\omega)$. The multiplier $a\ell+\eta\omega$ defines $A$. Its square-root domain is exactly

$$
D(A^{1/2})=D(L^{1/2})\cap D(Z_\sigma^{1/2})
 =\mathcal E_\sigma,
\qquad
D(A)=D(L)\cap D(Z_\sigma).
\tag{102.10}
$$

Indeed, its form integrability is equivalent to that of $\ell+\omega$, and its squared multiplier is bounded above and below by positive multiples of $\ell^2+\omega^2$. This also identifies its form with $a t+\eta d_\sigma$, by integration in that joint measure and polarization. It uses the original closed free domains, not an observer representation of the interaction. For every $r>0$ the bounded inverse $R_r=(A+r)^{-1}$ consequently satisfies

$$
R_rf\in D(A)\subset\mathcal E_\sigma\cap D(L),\qquad
\|LR_rf\|_2\le a^{-1}\|f\|_2
\quad(f\in L^2),
\tag{102.11}
$$

because $\ell/(a\ell+\eta\omega+r)\le1/a$. The represented-form identity on such tests is

$$
a\,t(R_rf,u)+\eta\,d_\sigma(R_rf,u)
 =\langle AR_rf,u\rangle\qquad(u\in\mathcal E_\sigma).
\tag{102.12}
$$

It follows either from the same joint integral or from closed-form representation. No core for $A$ and no separate multiplier domain for $\Gamma$ is needed here.

Take $\phi=R_{\varepsilon+\delta}f$ in (102.3), with $f\in L^2$ arbitrary and $\delta>0$. Equations (102.9)–(102.12) give

$$
\begin{aligned}
\left|\left\langle
 (I-\delta R_{\varepsilon+\delta})f,u\right\rangle\right|
 &=g\,|v(R_{\varepsilon+\delta}f,u)|\\
 &\le\frac{gK_\Gamma}{a}\sqrt{T[u]}\,\|f\|_2.
\end{aligned}
\tag{102.13}
$$

There is no zero spectral atom of $A$. In fact $A u=0$ implies $D_\sigma[u]=0$, while the actual central Fourier transform of an $L^2$ state with this property is supported at the null singleton $\lambda=0$ and is zero. Hence, also when $\varepsilon=0$, the spectral theorem and dominated convergence give

$$
\delta R_{\varepsilon+\delta}f\longrightarrow0
 \quad\hbox{in }L^2\quad(\delta\downarrow0).
\tag{102.14}
$$

Taking this limit in (102.13) and then taking the supremum over $\|f\|_2=1$ proves (102.4). Testing (102.3) with $u$ itself gives (102.5), using $aT[u]\le S_{a,\eta}[u]$. All tests were in the original full form domain. In particular neither a positivity-preserving heat law for $A$ nor an order comparison of noncommuting inverses has entered the proof. $\square$

**Theorem 102.3 (actual critical attainment and strict threshold refinements).** For every $\sigma>2$ and $a,\eta>0$, the true threshold $g_\sigma^*(a,\eta)$ of (101.1) is attained by a nonzero actual state $u\in\mathcal E_\sigma$. It may be chosen so that

$$
V[u]=1,\qquad S_{a,\eta}[u]=g_\sigma^*(a,\eta).
\tag{102.15}
$$

Consequently $u/\|u\|_2$ is an actual normalized zero eigenvector of $H_{a,\eta,g_\sigma^*}$, and all four equivalent critical existence statements in Theorem 101.5 hold. In the exact notation of (101.1), (101.5) and (101.10),

$$
0<\mathcal C_\sigma<\frac18,\qquad
 g_\sigma^*(a,\eta)>g_{\rm suf}(a,\eta)
 =\frac{8a^\alpha\eta^\beta}{\alpha^\alpha\beta^\beta}.
\tag{102.16}
$$

**Proof.** Write $g_*=g_\sigma^*(a,\eta)$ and $g_n=g_*+1/n$. Theorem 101.3 gives $0<g_*<\infty$ and, for each $n$, an actual normalized negative-energy eigenstate $v_n\in\mathcal E_\sigma$ of $H_{a,\eta,g_n}$, with eigenvalue $-\varepsilon_n<0$. Its represented form and exact domain are those of Theorem 87.5. In particular its equation holds for every test in $\mathcal E_\sigma$. Since $0<V[v_n]<\infty$, set

$$
u_n=\frac{v_n}{\sqrt{V[v_n]}}.
\tag{102.17}
$$

Amplitude rescaling preserves that weak equation. Threshold nonnegativity and its negative-energy identity give

$$
V[u_n]=1,\qquad
 g_*\le S_{a,\eta}[u_n]
 =g_n-\varepsilon_n\|u_n\|_2^2<g_n.
\tag{102.18}
$$

Now apply Theorem 102.2 to these actual equation-satisfying states, not to an arbitrary quotient-minimizing sequence. It gives

$$
\|u_n\|_2^2\le\frac{K_\Gamma^2g_n^3}{a^3}
 \le\frac{K_\Gamma^2(g_*+1)^3}{a^3}.
\tag{102.19}
$$

Together with (102.18), this bounds the complete Hilbert norm of $\mathcal E_\sigma$. Take a subsequence weakly converging there to $u$. The full actual-field compact embedding of Theorem 87.5 gives, after further subselection, strong convergence in $L^2(G,\Gamma d\mu)$ to that same $u$. Hence $V[u]=1$. Weak lower semicontinuity and (102.18) imply $S_{a,\eta}[u]\le g_*$, while the defining threshold inequality on the entire $\mathcal E_\sigma$ implies $S_{a,\eta}[u]\ge g_*V[u]=g_*$. This proves (102.15). In particular $u$ is a nonzero $L^2$ function with the original distributional horizontal derivatives and the required central moment, not merely a vector in a homogeneous completion. No convergence of the total $L^2$ masses or limiting eigenvalues was presumed.

To identify the actual operator domain, the closed form $q_{a,\eta,g_*}$ is nonnegative on exactly $\mathcal E_\sigma$, by Theorems 87.5 and 101.3, and has value zero at $u$. Cauchy–Schwarz for that nonnegative Hermitian form gives $q_{a,\eta,g_*}(\phi,u)=0$ for every $\phi\in\mathcal E_\sigma$. The characterization of the represented operator domain therefore puts $u\in D(H_{a,\eta,g_*})$ with $H_{a,\eta,g_*}u=0$: the representing vector is the actual zero vector of $L^2$. This argument does not split the represented operator into separately defined vectors $Au$ and $\Gamma u$. Since $0<\|u\|_2<\infty$, normalization gives the asserted zero eigenvector.

By Theorem 101.5 this same state attains $\mathcal C_\sigma$, and its virial balance is (101.20). Apply the strict per-state bound (101.2) to this nonzero extremizer:

$$
\mathcal C_\sigma
 =\frac{V[u]}{T[u]^\alpha D_\sigma[u]^\beta}<\frac18.
\tag{102.20}
$$

Positivity is already (101.11). Substitution into the exact coefficient identity from Theorem 101.4,

$$
g_\sigma^*(a,\eta)
 =\frac{a^\alpha\eta^\beta}
 {\alpha^\alpha\beta^\beta\mathcal C_\sigma},
\tag{102.21}
$$

proves the strict second refinement in (102.16). The strict supremum bound follows from actual attainment together with the strict per-state inequality; the latter alone would not prove it. $\square$

**Proposition 102.4 (the mass bound does not extend to arbitrary quotient minimizers).** Even after imposing $V=1$, a sequence with $S_{a,\eta}/V\to g_\sigma^*(a,\eta)$ need not be bounded in $L^2$.

**Proof.** Choose $u$ from (102.15) and a fixed normalized nonzero punctured core state $h$. For $R\to\infty$ put $b_R=R^{1/2}U_Rh$, with the original Carnot dilation (101.9). Then

$$
\begin{gathered}
\|b_R\|_2^2=R,\qquad
T[b_R]=R^{-1}T[h],\\
D_\sigma[b_R]=R^{1-2\sigma}D_\sigma[h],\qquad
V[b_R]=R^{-2}V[h].
\end{gathered}
\tag{102.22}
$$

Thus $S_{a,\eta}[b_R]\to0$ and $V[b_R]\to0$. Cauchy–Schwarz separately for the two nonnegative kinetic forms and for the actual weighted inner product gives

$$
S_{a,\eta}[u+b_R]\longrightarrow g_*,\qquad
V[u+b_R]\longrightarrow1.
\tag{102.23}
$$

For sufficiently large $R$, define $w_R=(u+b_R)/\sqrt{V[u+b_R]}$. Each $w_R$ is an actual form state with $V[w_R]=1$ and quotient tending to $g_*$. But the reverse triangle inequality gives

$$
\|w_R\|_2\ge
 \frac{R^{1/2}-\|u\|_2}{\sqrt{V[u+b_R]}}\longrightarrow\infty.
\tag{102.24}
$$

No disjoint-support or local central-operator assumption is used: all cross terms were controlled by their corresponding Hilbert seminorms. This example explains the need for the equation in Theorem 102.2 and the choice of actual negative eigenstates in the proof of Theorem 102.3. $\square$

**Definition 102.5 (mathematical attribution and scope).** The Hardy and Rellich estimates (102.6) are literature-attested intermediates, with the precise correspondence to Ciatti–Cowling–Ricci given above. Their §2 uses Lebesgue Haar measure in exponential coordinates and the sub-Laplacian formed from a basis of the first stratum; the shear identifies those conventions with this source without a measure rescaling. Their adjoint identity (3.1) concerns the bounded weighted Riesz operator and its adjoint. It does not assert that $\Gamma u$ lies in ordinary $L^2$, nor that an everywhere-defined unweighted inverse exists at zero. The form pairing (102.9) and regularized resolvent tests (102.11)–(102.14) supply the client passage instead. Their positive free heat kernel is a fact about $L$; no such property is transferred to $A$.

The new source-specific deductions are the uniform equation-based mass estimate, its use with the existing full-field compactness and negative eigenstates to obtain an actual critical state, and the resulting strict refinements of the constants in §101. The free domains, strong central reduction, actual Green bound, higher-order weighted compactness and critical quotient/operator equivalences remain the supplies of §§84–87 and §101. These deductions are repository-derived; neither the general Hardy/Rellich mechanism nor an exhaustive literature novelty claim is attributed to them.

All conclusions concern the original $H^1\times\mathbb R$ carrier, full complex domain, original source, Haar measure, degree-$-3$ field, actual horizontal kinetic form and clock. No marginal field, band restriction, new source or Green kernel of the added law is substituted. A full homogeneous-completion reconstruction theorem is not asserted. No exact sharp numerical value of $\mathcal C_\sigma$ or $g_\sigma^*$, positivity or simplicity of a critical eigenstate, extension to $\sigma=2$, native source-to-state realization or physical dimension conclusion is supplied.

## 追加锚（本行以下为增补区）

## 103. Fixed-source endpoint limits of actual critical states

**Definition 103.1 (fixed data, common spaces and normalization).** Work on precisely the group of (82.5), with product $pp'=(x+x',y+y',z+z',w+w'+xy')$, identity $e$, Lebesgue Haar measure $d\mu=dx\,dy\,dz\,dw$, and

$$
X_1=\partial_x,\qquad X_2=\partial_y+x\partial_w,\qquad
X_3=\partial_z,\qquad L=-\sum_{i=1}^3X_i^2,\qquad D_w=-i\partial_w.
\tag{103.1}
$$

The operator $L$ is the original nonnegative free realization, its clock remains $e^{-tL}$, and $\Gamma=\int_0^\infty h_t\,dt$ is its original positive degree-$-3$ Green field with unit source $L\Gamma=\delta_e$. Fix $a,\eta>0$. All powers of $|D_w|$, all logarithms below and all central cutoffs use one fixed original coordinate and fixed spectral units, without a parameter-dependent rescaling. For complex states and $\nu>0$ use the full distributional spaces and forms (with $\sigma>2$ in the threshold and product expressions)

$$
\begin{gathered}
\mathcal E_\nu=D(L^{1/2})\cap D(|D_w|^{\nu/2}),\qquad
\|u\|_{\mathcal E_\nu}^2=\|u\|_2^2+T[u]+D_\nu[u],\\
T[u]=\sum_i\|X_i u\|_2^2,\qquad
D_\nu[u]=\||D_w|^{\nu/2}u\|_2^2,\qquad
V[u]=\|\sqrt\Gamma u\|_2^2,\\
g_\sigma=g_\sigma^*(a,\eta)
 =\inf_{0\ne u\in\mathcal E_\sigma}\frac{aT[u]+\eta D_\sigma[u]}{V[u]},\\
\alpha_\sigma=\frac{2\sigma-3}{2\sigma-2},\qquad
\beta_\sigma=\frac1{2\sigma-2},\qquad
\mathcal C_\sigma=\sup_{0\ne u\in\mathcal E_\sigma}
 \frac{V[u]}{T[u]^{\alpha_\sigma}D_\sigma[u]^{\beta_\sigma}},\\
g_c=16\sqrt{a\eta},\qquad t_c=\frac{g_c}{2a},\qquad
 d_c=\frac{g_c}{2\eta},\qquad t_cd_c=64,\\
q_c[u]=aT[u]+\eta D_2[u]-g_cV[u]\quad(u\in\mathcal E_2).
\end{gathered}
\tag{103.2}
$$

The critical Friedrichs space $\mathcal Q_c$ and form $\overline q_c$ are exactly those of Theorem 87.4, with norm squared $\|u\|_2^2+\overline q_c[u]$. In particular $\mathcal E_2\subset\mathcal Q_c$, $\overline q_c=q_c$ there, and the zero kernel in the whole $\mathcal Q_c$ is already established. The field, threshold and product definitions are those of §§87 and 101, not new objects generated from the added kinetic operator.

For every sequence $\sigma_n>2$ tending to $2$, choose **any** nonzero actual critical zero state supplied by Theorem 102.3, and rescale only its amplitude to obtain $u_n\in\mathcal E_{\sigma_n}$ with $V[u_n]=1$. Put $g_n=g_{\sigma_n}$ and $M_n=\|u_n\|_2^2>0$. Every such selection satisfies the actual weak equation and the existing virial identities

$$
\begin{gathered}
a\,t(\phi,u_n)+\eta\,d_{\sigma_n}(\phi,u_n)
 =g_n v(\phi,u_n)\quad(\phi\in\mathcal E_{\sigma_n}),\\
aT[u_n]=\alpha_{\sigma_n}g_n,\qquad
\eta D_{\sigma_n}[u_n]=\beta_{\sigma_n}g_n.
\end{gathered}
\tag{103.3}
$$

Here the $L^2$ inner product is antilinear in the first argument, $t(\phi,u)=\sum_i\langle X_i\phi,X_i u\rangle$, $d_\nu(\phi,u)=\langle|D_w|^{\nu/2}\phi,|D_w|^{\nu/2}u\rangle$, and $v(\phi,u)=\int\Gamma\overline\phi u\,d\mu$. The punctured core is $\mathcal D_0=C_c^\infty(G\setminus\{e\};\mathbb C)$. No positivity, simplicity, uniqueness, chosen profile or compactness uniform in $\sigma$ is assumed. Limits of finite measures below are narrow: they are tested against every bounded continuous complex function on the original $G$.

**Theorem 103.2 (true threshold and sharp product limit).** At the fixed data of Definition 103.1,

$$
\lim_{\sigma\downarrow2}g_\sigma=g_c,\qquad
\lim_{\sigma\downarrow2}\mathcal C_\sigma=\frac18.
\tag{103.4}
$$

**Proof.** The sufficient bound and exact coefficient relation from (101.5), (101.11) are

$$
g_\sigma\ge b_\sigma:=
 \frac{8a^{\alpha_\sigma}\eta^{\beta_\sigma}}
 {\alpha_\sigma^{\alpha_\sigma}\beta_\sigma^{\beta_\sigma}},\qquad
\mathcal C_\sigma=
 \frac{a^{\alpha_\sigma}\eta^{\beta_\sigma}}
 {\alpha_\sigma^{\alpha_\sigma}\beta_\sigma^{\beta_\sigma}g_\sigma}.
\tag{103.5}
$$

Since $\alpha_\sigma,\beta_\sigma\to1/2$, $b_\sigma\to g_c$. For the reverse bound, Proposition 87.3 supplies, for each $\delta>0$, a fixed nonzero punctured core state $f\in\mathcal D_0$ with $(aT[f]+\eta D_2[f])/V[f]<g_c+\delta$. Such an $f$ belongs to every finite-order domain. For $2\le\sigma\le3$, its central spectral integral is dominated by $(1+|\lambda|^3)|b_f(\xi,\lambda)|^2$, which is integrable. Hence $D_\sigma[f]\to D_2[f]$, and the defining infimum gives

$$
\limsup_{\sigma\downarrow2}g_\sigma
 \le\frac{aT[f]+\eta D_2[f]}{V[f]}<g_c+\delta.
$$

Let $\delta\downarrow0$ and use (103.5). This proves both limits. The core endpoint sharpness and the coefficient formula are reused, not re-proved as new results. This argument alone makes no assertion about monotonicity or the side of approach. $\square$

**Theorem 103.3 (actual states in the common endpoint topology).** For every selection in Definition 103.1,

$$
\begin{gathered}
T[u_n]\longrightarrow t_c,\qquad
D_{\sigma_n}[u_n]\longrightarrow d_c,\qquad
D_2[u_n]\longrightarrow d_c,\qquad q_c[u_n]\longrightarrow0,\\
u_n\rightharpoonup0\ \hbox{in }\mathcal E_2,\qquad
M_n\longrightarrow0,\qquad
\|\rho^{-1}u_n\|_2\longrightarrow0,\qquad
\|u_n\|_{\mathcal Q_c}\longrightarrow0,
\end{gathered}
\tag{103.6}
$$

where $\rho=(|\xi|^4+(w-xy/2)^2)^{1/4}$ is the original homogeneous norm of (102.1). Thus the convergence in ordinary $L^2$ is strong. To remove any ambiguity about weighted-norm conventions, (103.6) means $\int\rho^{-2}|u_n|^2d\mu\to0$; also $\int\rho^{-1}|u_n|^2d\mu\to0$. There is no strongly convergent subsequence in $\mathcal E_2$ or in $L^2(G,\Gamma d\mu)$.

**Proof.** The first two kinetic limits follow directly from (103.3) and (103.4). The equation-based estimate (102.5) gives the uniform bound $M_n\le K_\Gamma^2g_n^3/a^3$. To control the endpoint central derivative without changing the state, use (87.3) and (101.4): with $\theta_n=(\sigma_n-2)/(\sigma_n-1)$,

$$
\frac{64}{T[u_n]}<D_2[u_n]
 \le D_1[u_n]^{\theta_n}D_{\sigma_n}[u_n]^{1-\theta_n}
 \le T[u_n]^{\theta_n}D_{\sigma_n}[u_n]^{1-\theta_n}.
\tag{103.7}
$$

Both outside expressions tend to $d_c$, because $t_cd_c=64$. Consequently $D_2[u_n]\to d_c$ and $q_c[u_n]\to at_c+\eta d_c-g_c=0$. The sequence is bounded in the actual Hilbert space $\mathcal E_2$.

The inclusion $\mathcal E_2\to\mathcal Q_c$ is bounded: $0\le q_c[u]\le aT[u]+\eta D_2[u]$. Every weakly convergent $\mathcal E_2$ subsequence therefore converges weakly in $\mathcal Q_c$ to the same actual $L^2$ function $u$. Weak lower semicontinuity gives $\overline q_c[u]\le\liminf q_c[u_n]=0$. The zero-kernel result (87.19) forces $u=0$. Boundedness and weak subsequence extraction in this Hilbert space now show that the full sequence converges weakly to zero in $\mathcal E_2$.

On every fixed compact coordinate box, the actual derivatives $X_1u_n,X_2u_n,X_3u_n,\partial_wu_n$ control all ordinary first derivatives: $\partial_yu_n=X_2u_n-x\partial_wu_n$, and $x$ is bounded there. Multiplication by a fixed smooth compact cutoff thus gives a bounded ordinary $H^1(\mathbb R^4)$ sequence. Rellich compactness and the just-identified weak limit give $u_n\to0$ in $L^2$ on every compact set, for the full sequence. This is local compactness only.

Positivity, smoothness and degree $-3$ of the same $\Gamma$ on the compact unit $\rho$ sphere supply constants

$$
0<b_\Gamma:=\min_{\rho=1}\Gamma
 \le \rho(p)^3\Gamma(p)\le B_\Gamma<\infty\quad(p\ne e).
\tag{103.8}
$$

For $0<r<R$, the inner and outer parts of the softer weighted norm satisfy

$$
\int_{\rho<r}\rho^{-2}|u_n|^2d\mu\le\frac r{b_\Gamma}V[u_n]=\frac r{b_\Gamma},\qquad
\int_{\rho>R}\rho^{-2}|u_n|^2d\mu\le R^{-2}M_n.
\tag{103.9}
$$

The compact annulus $r\le\rho\le R$ contributes a quantity tending to zero by local $L^2$ convergence. First fix $r,R$ and let $n\to\infty$, then let $r\downarrow0$, $R\to\infty$. The uniform mass bound proves $\|\rho^{-1}u_n\|_2\to0$ without assuming global strong convergence.

The actual equation supplies the missing global implication. For each $n$, set $A_n=aL+\eta|D_w|^{\sigma_n}$ and $R_{n,\delta}=(A_n+\delta)^{-1}$. The legal full-spectrum tests of (102.10)–(102.14) give $R_{n,\delta}f\in\mathcal E_{\sigma_n}\cap D(L)$ and $\|LR_{n,\delta}f\|_2\le a^{-1}\|f\|_2$. The order-two Hardy/Rellich supply in (102.6) gives the more useful version of the pairing bound,

$$
\begin{aligned}
|v(\phi,u_n)|
 &\le B_\Gamma\|\rho^{-2}\phi\|_2\|\rho^{-1}u_n\|_2\\
 &\le B_\Gamma h_2\|L\phi\|_2\|\rho^{-1}u_n\|_2
 \quad(\phi\in D(L)).
\end{aligned}
\tag{103.10}
$$

Insert $\phi=R_{n,\delta}f$ into (103.3), using closed-form representation exactly as in (102.12). It follows that

$$
\left|\left\langle(I-\delta R_{n,\delta})f,u_n\right\rangle\right|
 \le\frac{g_n B_\Gamma h_2}{a}\|f\|_2\|\rho^{-1}u_n\|_2.
\tag{103.11}
$$

For each fixed $n$, $\ker A_n=\{0\}$ and $\delta R_{n,\delta}f\to0$ as $\delta\downarrow0$, by the original central spectral measure. Taking that limit first, and then the supremum over $\|f\|_2=1$, yields

$$
\|u_n\|_2\le\frac{g_n B_\Gamma h_2}{a}\|\rho^{-1}u_n\|_2\longrightarrow0.
\tag{103.12}
$$

No uniform limit in $(n,\delta)$, assertion $\Gamma u_n\in L^2$, or interacting operator core is used. Cauchy–Schwarz also gives $\int\rho^{-1}|u_n|^2d\mu\le\|u_n\|_2\|\rho^{-1}u_n\|_2\to0$. Since $\overline q_c[u_n]=q_c[u_n]\to0$, (103.12) proves strong convergence in $\mathcal Q_c$ with exactly the norm stated above.

On the other hand, $\|u_n\|_{\mathcal E_2}^2\to t_c+d_c>0$, while the only weak $\mathcal E_2$ limit is zero. This excludes every strongly convergent subsequence there. If a subsequence converged strongly in $L^2(G,\Gamma d\mu)$, then on each compact annulus (103.8) would identify its limit with the local $L^2$ limit zero. Exhaustion identifies the weighted limit as zero almost everywhere, contradicting $V[u_n]=1$. These are the precise failures of strong compactness despite strong convergence in the weaker spaces. $\square$

**Theorem 103.4 (concentration of potential and local endpoint kinetic resources).** In the same $V=1$ normalization, the actual finite measures satisfy

$$
\Gamma|u_n|^2d\mu\ \longrightarrow\ \delta_e,\qquad
\sum_{i=1}^3|X_i u_n|^2d\mu\ \longrightarrow\ t_c\delta_e,\qquad
|\partial_wu_n|^2d\mu\ \longrightarrow\ d_c\delta_e
\tag{103.13}
$$

narrowly on $G$. These are potential and local endpoint kinetic resources; the last measure belongs to $D_2$, and no local density for the fractional functional $D_{\sigma_n}$ is introduced.

**Proof.** For every fixed $r>0$, (103.8) and $M_n\to0$ give

$$
\int_{\rho\ge r}\Gamma|u_n|^2d\mu\le B_\Gamma r^{-3}M_n\longrightarrow0.
\tag{103.14}
$$

The potential measure has total one, proving its claimed limit.

For the two kinetic measures, choose real smooth $\chi,\zeta$ with $\chi^2+\zeta^2=1$, $\chi=0$ on $\rho\le r/2$, and $\chi=1$ on $\rho\ge r$. For example use the sine and cosine of a smooth function of $\rho$ constant at $0$ and $\pi/2$ on these regions. Their derivatives are supported on a compact annulus and bounded. Both products with $u_n$ belong to $\mathcal E_2$. The first-order product rules and cancellation of mixed terms give the exact local endpoint identity

$$
\begin{aligned}
q_c[\chi u_n]+q_c[\zeta u_n]
 &=q_c[u_n]+\int_G W_r|u_n|^2d\mu,\\
W_r&=a\sum_i\bigl(|X_i\chi|^2+|X_i\zeta|^2\bigr)
 +\eta\bigl(|\partial_w\chi|^2+|\partial_w\zeta|^2\bigr),\qquad
\|W_r\|_\infty<\infty.
\end{aligned}
\tag{103.15}
$$

The potential term splits here because this is multiplication by a partition of unity. Nonnegativity of the endpoint form implies $0\le q_c[\chi u_n]\le q_c[u_n]+\|W_r\|_\infty M_n\to0$. Also $V[\chi u_n]\le B_\Gamma(r/2)^{-3}M_n\to0$. Consequently

$$
aT[\chi u_n]+\eta D_2[\chi u_n]
 =q_c[\chi u_n]+g_cV[\chi u_n]\longrightarrow0.
\tag{103.16}
$$

On $\rho\ge r$, these derivatives equal those of $u_n$. Thus each kinetic measure has mass tending to zero outside every such neighbourhood of $e$, including the whole exterior tail. Their total masses tend to $t_c,d_c$ by (103.6). For any bounded continuous test, continuity at $e$ controls its variation inside a sufficiently small $\rho$ ball, and its supremum controls the vanishing exterior contribution. This proves all three narrow limits, without assuming tightness in advance. $\square$

**Proposition 103.5 (every fixed original central band loses its resource budgets).** Fix any $0\le\Lambda<\infty$ in the original units and let $P=P_\Lambda=\mathbf1_{[0,\Lambda]}(|D_w|)$, $Q=I-P$. In the notation of Definition 103.1,

$$
\begin{array}{c|cccc}
 &V&T&D_2&D_{\sigma_n}\\ \hline
Pu_n&0&0&0&0\\
Qu_n&1&t_c&d_c&d_c
\end{array}
\quad\hbox{are the respective limits.}
\tag{103.17}
$$

Each entry means the functional of the **projected state**: for example $V[Pu_n]=\|\sqrt\Gamma Pu_n\|_2^2$, $T[Pu_n]=\sum_i\|X_iPu_n\|_2^2$ and $D_{\sigma_n}[Pu_n]=\||D_w|^{\sigma_n/2}Pu_n\|_2^2$. It does not mean a projection applied to a local resource density or to $\sqrt\Gamma u_n$. The kinetic orthogonal splittings are exact; the potential need not commute with $P$ and need not split additively.

**Proof.** The original strong free reduction of Proposition 85.2 makes $P,Q$ preserve every relevant free form domain, with orthogonal splitting for $T,D_2,D_{\sigma_n}$. The sequence $\sigma_n$ is bounded, so for $\Lambda>0$

$$
D_2[Pu_n]\le\Lambda^2M_n\to0,\qquad
D_{\sigma_n}[Pu_n]\le\max\{1,\Lambda^{\sup_n\sigma_n}\}M_n\to0.
\tag{103.18}
$$

Since $T[Pu_n]\le T[u_n]$ is bounded, the endpoint estimate gives $V[Pu_n]\le\frac18\sqrt{T[Pu_n]D_2[Pu_n]}\to0$. To obtain the horizontal budget, use the actual equation with the legitimate test $Pu_n\in\mathcal E_{\sigma_n}$:

$$
0\le aT[Pu_n]+\eta D_{\sigma_n}[Pu_n]
 =g_n v(Pu_n,u_n)\le g_n\sqrt{V[Pu_n]V[u_n]}\longrightarrow0.
\tag{103.19}
$$

The middle pairing is real and nonnegative by the equality; its absolute value is bounded by weighted Cauchy–Schwarz. Orthogonal kinetic splitting and (103.6) give the complementary kinetic limits. For the potential, use the weighted triangle inequality instead:

$$
\left|\sqrt{V[Qu_n]}-\sqrt{V[u_n]}\right|
 \le\sqrt{V[Pu_n]}\longrightarrow0.
\tag{103.20}
$$

The cross pairing $v(Pu_n,Qu_n)$ tends to zero as well, by the same weighted inequality and boundedness of $V[Qu_n]$. When $\Lambda=0$, $P=0$ on the actual $L^2$ central spectrum and the assertions follow directly. Thus a fixed band cannot retain any of the stated potential or kinetic budgets, although no fractional spatial-density localization has been asserted. $\square$

**Corollary 103.6 (what amplitude normalization to $L^2=1$ preserves).** Set $v_n=u_n/\sqrt{M_n}$. Then $\|v_n\|_2=1$, $M_n\to0$, and exactly

$$
\begin{gathered}
V[v_n]=M_n^{-1}\longrightarrow\infty,\qquad
\frac{T[v_n]}{V[v_n]}=T[u_n]\longrightarrow t_c,\\
\frac{D_{\sigma_n}[v_n]}{V[v_n]}=D_{\sigma_n}[u_n]\longrightarrow d_c,\qquad
\frac{D_2[v_n]}{V[v_n]}=D_2[u_n]\longrightarrow d_c.
\end{gathered}
\tag{103.21}
$$

In particular each of the three kinetic totals diverges, $T[v_n]/D_2[v_n]\to t_c/d_c=\eta/a$, and $D_{\sigma_n}[v_n]/D_2[v_n]\to1$. The relative resource measures are amplitude invariant:

$$
\begin{gathered}
\frac{\Gamma|v_n|^2d\mu}{V[v_n]}=\Gamma|u_n|^2d\mu\longrightarrow\delta_e,\\
\frac{\sum_i|X_iv_n|^2d\mu}{T[v_n]}
 =\frac{\sum_i|X_iu_n|^2d\mu}{T[u_n]}\longrightarrow\delta_e,\\
\frac{|\partial_wv_n|^2d\mu}{D_2[v_n]}
 =\frac{|\partial_wu_n|^2d\mu}{D_2[u_n]}\longrightarrow\delta_e.
\end{gathered}
\tag{103.22}
$$

For each fixed $\Lambda$, the fractions $F[P_\Lambda v_n]/F[v_n]$ tend to zero and $F[(I-P_\Lambda)v_n]/F[v_n]$ tend to one, for $F=V,T,D_2,D_{\sigma_n}$. These are again functionals of projected states. No conclusion about the location or tightness of the unweighted probability measures $|v_n|^2d\mu$, or a weak or strong state limit or profile for $v_n$, is made.

**Proof.** Every indicated form and each displayed local measure is quadratic under amplitude scaling. Divide the identities and limits of Theorems 103.3–103.4 and Proposition 103.5 by the positive $M_n$, or by the corresponding positive total resource, as appropriate. No statement about $|u_n|^2/M_n$ follows from the unnormalized convergence $u_n\to0$ in $L^2$ or from the relative resource identities alone. $\square$

**Theorem 103.7 (infinite difference quotients and a subexponential mass restriction).** In the fixed units of Definition 103.1,

$$
\lim_{\sigma\downarrow2}\frac{g_\sigma-g_c}{\sigma-2}=+\infty,\qquad
\lim_{\sigma\downarrow2}\frac{1/8-\mathcal C_\sigma}{\sigma-2}=+\infty.
\tag{103.23}
$$

For every actual $V=1$ selection in that definition,

$$
(\sigma_n-2)\log(1/M_n)\longrightarrow0.
\tag{103.24}
$$

In particular $g_\sigma>g_c$ for all sufficiently small positive $\sigma-2$. For every fixed $K>0$, both positive gaps in (103.23) eventually exceed $K(\sigma-2)$. For every $c>0$, eventually $M_n>\exp[-c/(\sigma_n-2)]$, while $M_n\to0$. These statements give neither monotonicity nor a sharp asymptotic rate or spatial scale.

**Proof.** Write $\epsilon_n=\sigma_n-2$. Same-state spectral interpolation (87.12) gives

$$
D_2[u_n]^{\sigma_n}\le D_{\sigma_n}[u_n]^2M_n^{\epsilon_n}.
$$

Since $M_n<1$ eventually, logarithms and (103.6) imply

$$
0\le\epsilon_n\log(1/M_n)
 \le2\log D_{\sigma_n}[u_n]-\sigma_n\log D_2[u_n]\longrightarrow0.
\tag{103.25}
$$

This proves (103.24) without prescribing a profile or a relation between central and spatial scales.

For the threshold difference quotient, the norm-bearing endpoint estimate (87.4) and the exact virial identities give

$$
1=V[u_n]\le\frac18
 \left(\frac{\alpha_{\sigma_n}g_n}{a}\right)^{1/2}
 \left(\frac{\beta_{\sigma_n}g_n}{\eta}\right)^{1/\sigma_n}
 M_n^{\epsilon_n/(2\sigma_n)}.
\tag{103.26}
$$

Define the scalar functions, smooth from the right at $2$,

$$
r_\sigma=\frac12+\frac1\sigma,\qquad
F_\sigma=\frac12\log\frac{\alpha_\sigma g_c}{a}
 +\frac1\sigma\log\frac{\beta_\sigma g_c}{\eta}-\log8.
\tag{103.27}
$$

Here $F_2=\frac12\log(t_cd_c)-\log8=0$, so $|F_\sigma|\le C(\sigma-2)$ near $2$. Taking logarithms in (103.26) consequently yields

$$
r_{\sigma_n}\frac{\log(g_n/g_c)}{\epsilon_n}
 \ge\frac{\log(1/M_n)}{2\sigma_n}-C\longrightarrow+\infty.
\tag{103.28}
$$

Use $M_n\to0$, $r_{\sigma_n}\to1$ and $g_n\to g_c$ to obtain $(g_n-g_c)/\epsilon_n\to+\infty$. The sequence $\sigma_n\downarrow2$ was arbitrary in the sense of approach from above, without a monotonicity requirement, and each such sequence admits an actual selection by §102.3. Thus this is the full first limit in (103.23).

Finally (103.5) gives $g_\sigma/b_\sigma=1/(8\mathcal C_\sigma)$. The function $b_\sigma$ is smooth at $2$ with $b_2=g_c$, so $\log(b_\sigma/g_c)=O(\sigma-2)$. Hence

$$
\frac{\log(1/(8\mathcal C_\sigma))}{\sigma-2}
 =\frac{\log(g_\sigma/g_c)-\log(b_\sigma/g_c)}{\sigma-2}
 \longrightarrow+\infty.
\tag{103.29}
$$

As $\mathcal C_\sigma\to1/8$ from below by (102.16), $\log(1/(8\mathcal C_\sigma))\sim8(1/8-\mathcal C_\sigma)$. This proves the second limit and the stated eventual implications. $\square$

**Definition 103.8 (supplier correspondence, new content and remaining boundaries).** The repository supplies used here are: the original positive smooth homogeneous unit-source field and coordinate conventions from §§82–85; the sharp whole-domain endpoint inequality and core threshold from §§87.2–87.3; the actual critical Friedrichs extension and its zero kernel from §87.4; the first-moment interpolation, exact coefficient identity and actual virial balance from §§101.2, 101.4–101.5; and the equation-based mass bound, legal free resolvent tests and actual critical attainment from §§102.2–102.3. None of those earlier results is claimed as a new theorem of this section or as newly Lean-verified.

The literature intermediates have specific consumed roles. Ciatti–Cowling–Ricci, [*Hardy and uncertainty inequalities on stratified Lie groups*, primary text](https://arxiv.org/html/1308.2373v1), Theorem A, Theorem 3.1 and Corollary 3.2, give $\|\rho^{-k}f\|_2\le h_k\|L^{k/2}f\|_2$ for $k=1,2$: this is the original stratified $G$ with homogeneous dimension $Q=5$, $p=2$ and $k<Q/p=5/2$. Order one enters through §102's initial uniform mass bound; order two, extended to $D(L)$ there, is directly consumed in (103.10). Their theorem is an inequality for the original sub-Laplacian and a homogeneous norm, not for a newly generated Green field or a positivity-preserving higher-order law.

Alvino–Ferone–Volpicelli, [*Sharp Hardy inequalities in the half space with trace remainder term*, primary text](https://arxiv.org/html/1105.0335v1), Theorem 1.1 and (8), at $n=4$, $\beta_{\rm AFV}=2$, supply the existing trace intermediate with constant $2/\pi$ on each halfspace, hence $4/\pi$ on both. Its passage to the actual full-field sharp endpoint, its core sharpness and zero-kernel comparison were proved in §87 and are used here through those results; the halfspace trace potential is never substituted for $\Gamma$. Teschl, [*Mathematical Methods in Quantum Mechanics*, primary text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), Theorem 2.13, supplies closed-form representation on $L^2(G,d\mu)$, consumed through the represented equations and the tests (103.11). Its KLMN Theorem 6.24 is already used in the higher-order closed-domain and existence supply, not invoked at relative bound one to claim closedness on $\mathcal E_2$. The Hilbert weak-compactness, local Euclidean Rellich, product-rule localization, Fourier interpolation and measure arguments used in the proofs are mature intermediate methods.

The source-specific additional deductions are the limits of the true thresholds and sharp product constants; the universal, amplitude-normalized actual-state endpoint convergence and its two failures of strong compactness; localization of the actual potential and endpoint kinetic measures; escape of the projected-state resource budgets from every fixed central band; and the difference-quotient and subexponential restrictions. The source correspondence and repository overlap scope concern these fixed-field deductions and the indicated intermediates. They assert no exhaustive literature search or world-originality judgment.

At fixed $\sigma>2$, §102 furnishes an actual critical zero state. At $\sigma=2$, §87.4 excludes such a nonzero state even in $\mathcal Q_c$. Equations (103.6), (103.13) and (103.17) give a precise way those statements coexist: under $V=1$, ordinary mass disappears and the state tends strongly to zero in the closed critical form norm, whereas nonzero potential and endpoint kinetic resources concentrate at the same original source and leave every fixed central band. This is not loss or concentration of a normalized probability mass. After $L^2=1$ normalization only the exact totals, ratios and relative resource conclusions above are asserted; its unweighted probability location, tightness, weak or strong limit, spatial/central profile and sharp scale remain unproved here. No positivity, simplicity, uniqueness, resonance classification, native source-to-state realization or physical dimension conclusion is obtained. All proofs are ordinary mathematics on the full complex actual domains; no Lean verification or completion of the continuing why-three research goal is claimed.

## 追加锚（本行以下为增补区）
