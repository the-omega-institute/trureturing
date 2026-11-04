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

## 104. Actual endpoint probability: domain defects, excluded scales and singular reweighting

**Definition 104.1 (actual selections and probability conventions).** Retain all data, full complex domains and arbitrary critical-state selections of Definition 103.1. In particular the source is $e$, $G=H^1\times\mathbb R$, $d\mu$ is Lebesgue Haar measure, $\Gamma$ is the original unit-source degree-$-3$ Green field, and $a,\eta$, the horizontal operator $L$, its clock and the central spectral units are fixed. For every sequence $\sigma_n>2$ tending to $2$, take any of those actual states, with the two amplitude normalizations

$$
\begin{gathered}
V[u_n]=1,\qquad M_n=\|u_n\|_2^2,\qquad
v_n=M_n^{-1/2}u_n,\qquad \|v_n\|_2=1,\\
\ell_n=\sqrt{M_n},\qquad \epsilon_n=\sigma_n-2,\qquad
d_n=D_2[u_n],\\
\mu_n=|v_n|^2d\mu,\qquad
\nu_n=M_n\Gamma\,\mu_n=\Gamma|u_n|^2d\mu.
\end{gathered}
\tag{104.1}
$$

Both $\mu_n$ and $\nu_n$ are probability measures. The supplies used below, without a new existence or endpoint-limit claim, are (103.3), (103.6) and (103.24):

$$
\begin{gathered}
g_n\to g_c,\quad T[u_n]\to t_c,\quad
D_{\sigma_n}[u_n]\to d_c,\quad d_n\to d_c>0,\\
M_n\to0,\qquad \epsilon_n\log(1/M_n)\to0,\qquad
at_c+\eta d_c=g_c.
\end{gathered}
\tag{104.2}
$$

Write $\xi=(x,y,z)$, $s=w-xy/2$ and $\rho=(|\xi|^4+s^2)^{1/4}$, as in (102.1). Set $B_\rho(p,r)=\{q:\rho(p^{-1}q)<r\}$ and retain $B_\Gamma=\sup_{q\ne e}\rho(q)^3\Gamma(q)<\infty$. A central section of a measurable set is its section at fixed $\xi$, measured in $dw$ or, equivalently, $ds$. Let $\widehat v_n(\xi,\lambda)$ denote the unitary central transform in shear coordinates. The actual spectral probability $\vartheta_n$ on $[0,\infty)$ is defined, for bounded Borel $f$, by

$$
\int f(x)\,d\vartheta_n(x)
 =\int f(\ell_n|\lambda|)|\widehat v_n(\xi,\lambda)|^2\,d\xi d\lambda.
\tag{104.3}
$$

Analytic changes of variables used to study these measures do not change the original law or spectral units. Weak state limits below are in the common $L^2(G,d\mu)$; local strong convergence is on compact subsets of $G\setminus\{e\}$. Measure convergence on $G\cup\{\infty\}$ means weak convergence against continuous functions on its one-point compactification, whereas convergence of $\vartheta_n$ is narrow convergence on $[0,\infty)$.

**Theorem 104.2 (local probability compactness and the maximal-domain defect).** For every $\chi\in C_c^\infty(G\setminus\{e\};\mathbb C)$ there is a constant $C_\chi$ such that, eventually,

$$
T[\chi v_n]+D_{\sigma_n}[\chi v_n]+D_2[\chi v_n]
 +\|\chi v_n\|_{H^1(\mathbb R^4)}^2+\|\chi v_n\|_4^2\le C_\chi.
\tag{104.4}
$$

Here the Euclidean norm uses the original coordinate chart. Constants and the sufficiently small interval of $\sigma-2$ can be chosen independently of the actual critical-state selection. Every sequence has a subsequence converging weakly globally in $L^2$ and strongly locally in $L^2$ off $e$ to the same $v$. Define the densely defined symmetric operator and its maximal zero space by

$$
S\phi=(aL+\eta D_w^2-g_c\Gamma)\phi,\qquad
D(S)=\mathcal D_0,\qquad \mathcal N_0=\ker S^*.
\tag{104.5}
$$

Every such $v$ belongs to $\mathcal N_0$, and

$$
\mathcal N_0\cap\mathcal Q_c=\{0\}.
\tag{104.6}
$$

After further subselection the probability measures have exactly the decomposition

$$
\mu_n\longrightarrow |v|^2d\mu+m_e\delta_e+m_\infty\delta_\infty,
\qquad m_e,m_\infty\ge0,\qquad
\|v\|_2^2+m_e+m_\infty=1.
\tag{104.7}
$$

This describes every subsequential limit, by taking a common subsequence for states and measures; it is not a claim that every proposed triple is realizable. The decomposition retains both possible defects simultaneously, without asserting that either is nonzero. Neither coefficient nor the triviality of $\mathcal N_0$ is specified.

**Proof.** The actual equation is (103.3), also for $v_n$ by homogeneity. Its localization requires control uniform in the varying central order. Spectral Hölder and (104.2) give, eventually with $0<\epsilon_n\le1/2$,

$$
D_{\epsilon_n}[v_n]
 \le D_{\sigma_n}[v_n]^{\epsilon_n/\sigma_n}
 =\left(\frac{D_{\sigma_n}[u_n]}{M_n}\right)^{\epsilon_n/\sigma_n}
 \longrightarrow1.
\tag{104.8}
$$

Only boundedness of the left side is inferred; equality or convergence of that moment is not asserted.

For a real $\chi$ as above, the central Fourier calculation needed in this proof is

$$
\left|D_\sigma[\chi f]-\operatorname{Re}d_\sigma(\chi^2f,f)\right|
 \le C_\chi\bigl(\|f\|_2^2+D_{\sigma-2}[f]\bigr),
\qquad 2<\sigma\le5/2.
\tag{104.9}
$$

To verify both its order and its uniform constant, first use smooth $f$ and take the Fourier transform in $w$ at each $\xi$. For $p_\sigma(\lambda)=|\lambda|^\sigma$ the left-side difference is the quadratic pairing of $\frac12[\chi,[p_\sigma(D_w),\chi]]$. Symmetrizing the two cutoff Fourier variables $h,k$ gives, up to sign and the fixed Fourier constants, the symbol

$$
p_\sigma(\lambda+h+k)-p_\sigma(\lambda+h)
 -p_\sigma(\lambda+k)+p_\sigma(\lambda).
$$

The fundamental theorem of calculus applied twice bounds its absolute value by

$$
C|hk|(1+|\lambda|+|h|+|k|)^{\sigma-2},
\tag{104.10}
$$

with one $C$ on $[2,5/2]$, since $p_\sigma''(t)=\sigma(\sigma-1)|t|^{\sigma-2}$. Put $\langle\lambda\rangle=(1+\lambda^2)^{1/2}$. For $0\le\epsilon\le1/2$, the weight in (104.10) is bounded by
$C\langle\lambda\rangle^{\epsilon/2}\langle\lambda+h+k\rangle^{\epsilon/2}\langle h\rangle^2\langle k\rangle^2$.
The Fourier transforms of $\chi(\xi,\cdot)$ have uniformly bounded Schwartz seminorms. Thus Cauchy–Schwarz in $\lambda$ and integration in $h,k$ bound the pairing by
$C_\chi\int\langle\lambda\rangle^\epsilon|\widehat f(\xi,\lambda)|^2d\xi d\lambda$,
which is at most the right side of (104.9). This proves (104.9) with no constant singular at $\sigma=2$. Smooth approximation extends it to the central form domain. The same Fourier convolution bounds show that multiplication by $\chi$ or $\chi^2$ preserves that domain. The horizontal product rule, with bounded $X_i\chi$, shows preservation of $\mathcal E_\sigma$.

Consequently $\chi^2v_n$ is a legal test. Taking real parts of its actual equation, using the horizontal product rule and (104.9), yields

$$
\begin{aligned}
aT[\chi v_n]+\eta D_{\sigma_n}[\chi v_n]
 &=g_nV[\chi v_n]
   +a\int\sum_i|X_i\chi|^2|v_n|^2d\mu+\eta R_n,\\
|R_n|&\le C_\chi(1+D_{\epsilon_n}[v_n]).
\end{aligned}
\tag{104.11}
$$

The original $\Gamma$ is bounded on the compact support of $\chi$, and $g_n$ is bounded. Equations (104.8)–(104.11) give the uniform kinetic bound. The scalar inequality $|\lambda|^2\le1+|\lambda|^{\sigma_n}$ bounds $D_2[\chi v_n]$. On this support $x$ is bounded and $\partial_y=X_2-x\partial_w$, so all four ordinary first derivatives are controlled. The ordinary four-dimensional Sobolev embedding $H^1\to L^4$ gives the last term in (104.4). Applying the real-cutoff argument to the real and imaginary parts of $\chi$ gives the complex-cutoff assertion. These are consumed product, Fourier and Sobolev estimates, not separate new inequalities.

The estimates hold uniformly near $2$ over all actual selections: if the needed bound in (104.8) failed uniformly, one could choose $\sigma_j\to2$ and violating actual states, contradicting the universal sequential assertion (104.2). The other constants in (104.11) depend only on the fixed data and $\chi$.

Weak compactness of the unit ball of global $L^2$, local Rellich compactness from (104.4), and a countable exhaustion off $e$ give the state subsequence. For $\phi\in\mathcal D_0$, move all free derivatives onto this smooth test in the actual weak equation:

$$
a\langle L\phi,v_n\rangle+
\eta\langle|D_w|^{\sigma_n}\phi,v_n\rangle
 =g_n\langle\Gamma\phi,v_n\rangle.
\tag{104.12}
$$

Here $|D_w|^{\sigma_n}\phi\to D_w^2\phi$ strongly in $L^2$, by Fourier dominated convergence, and $\Gamma\phi\in L^2$ because the support avoids $e$. Global weak convergence therefore gives $\langle S\phi,v\rangle=0$ for every $\phi\in D(S)$. By the definition of the adjoint this is precisely $`v\in D(S^*)`$ and $`S^*v=0`$; no global vector $\Gamma v$ is required.

If also $v\in\mathcal Q_c$, approximate it in that closed form norm by $\phi_j\in\mathcal D_0$. For each fixed $\phi\in\mathcal D_0$, approximation in the second slot gives $\overline q_c(\phi,v)=\langle S\phi,v\rangle=0$. Density then gives $\overline q_c[v]=0$, and (87.19) gives $v=0$. This proves (104.6) without equating maximal and Friedrichs domains.

Finally $G\cup\{\infty\}$ is compact metrizable, so the probability measures have a weakly convergent subsequence. On every compact subset off $e$, strong $L^2$ convergence gives $|v_n|^2\to|v|^2$ in $L^1$. Hence the limiting measure agrees with $|v|^2d\mu$ on $G\setminus\{e\}$; its remaining support is contained in $\{e,\infty\}$. Positivity and total mass one give (104.7). Conversely any measure limit can first be retained and then refined by the state compactness just proved, so every measure limit has this representation. This converse concerns subsequence refinement, not realizability of arbitrary coefficients. $\square$

**Theorem 104.3 (actual probability excludes both inverse-kinetic scales).** For every fixed $0<C<\infty$,

$$
\sup_{b\in\mathbb R^3}
 \mu_n\{(\xi,w):|\xi-b|<C\ell_n\}\longrightarrow0.
\tag{104.13}
$$

The actual central spectral laws satisfy

$$
\vartheta_n\longrightarrow\delta_0,\qquad
\int x^2d\vartheta_n(x)=d_n\longrightarrow d_c>0.
\tag{104.14}
$$

In physical central coordinates there is the uniform conclusion

$$
\sup_{\substack{E\subset G\ \mathrm{measurable}\\
 \operatorname*{ess\,sup}_\xi |E_\xi|\le C\ell_n}}
 \mu_n(E)\longrightarrow0.
\tag{104.15}
$$

The sections can have arbitrary moving centres, shapes and dependence on $\xi$, and may be specified in $w$ or in $s$. Thus (104.14) is weak concentration of the rescaled spectral probability at zero with a nonvanishing second moment; it is not convergence of second moments to the moment of $\delta_0$.

**Proof.** Use the nonlinear comparison (87.10)–(87.11) with its two exact probability preservations. Define

$$
U_n(\xi,t)=\mathcal F_s^{-1}|\widehat v_n|(\xi,t),\qquad
f_n(\xi,t)=\ell_n^2U_n(\ell_n\xi,\ell_n t).
\tag{104.16}
$$

The dilation here is Euclidean in the four auxiliary variables, not a Carnot dilation of the original law. Put $A[f]=\|\nabla_\xi f\|_2^2$, $C[f]=\|\partial_t f\|_2^2$ and $J[f]=\int|\xi|^{-1}|f(\xi,0)|^2d\xi$. The existing comparison and its marginal and spectral equalities give, for bounded Borel $F$ in the last line,

$$
\begin{gathered}
\|f_n\|_2=1,\qquad A[f_n]\le T[u_n],\qquad C[f_n]=d_n,\qquad
J[f_n]=M_nJ[U_n]\ge4\pi,\\
\int|f_n(\xi,t)|^2dt
 =\ell_n^3\int|v_n(\ell_n\xi,w)|^2dw,\\
\int F(|\lambda|)|\widehat f_n(\xi,\lambda)|^2d\xi d\lambda
 =\int F(\ell_n|\lambda|)|\widehat v_n(\xi,\lambda)|^2d\xi d\lambda.
\end{gathered}
\tag{104.17}
$$

In the marginal equality the shear is only a translation on each central fibre. No pointwise central spatial probability equality is used.

The nonnegative auxiliary trace form

$$
\mathfrak h[f]=aA[f]+\eta C[f]-\frac{4\sqrt{a\eta}}{\pi}J[f]
\tag{104.18}
$$

has the closed extension with zero kernel furnished by (87.8)–(87.9), after the fixed central change of variable $\kappa=\sqrt{\eta/a}$. More explicitly $F(\xi,t)=\kappa^{1/2}f(\xi,\kappa t)$ gives $\mathfrak h[f]=a\mathfrak t[F]$. It is not asserted closed on $H^1$. Equations (104.2) and (104.17) imply

$$
0\le\mathfrak h[f_n]
 \le aT[u_n]+\eta d_n-g_c\longrightarrow0.
\tag{104.19}
$$

The sequence is bounded in ordinary $H^1(\mathbb R^4)$. The bounded inclusion of $H^1$ into the closed trace form domain, followed by weak lower semicontinuity and its zero kernel, shows that every weak $H^1$ limit is zero. Thus $f_n\rightharpoonup0$ in $H^1$ and $f_n\to0$ in $L^2$ on every compact set, for the full sequence.

The following localization is needed to transfer probability information. Fix $r>0$. Choose real smooth $\chi,\zeta$ with $\chi^2+\zeta^2=1$, $\chi=0$ on the Euclidean ball of radius $r$ in $(\xi,t)$ and $\chi=1$ outside its radius-$2r$ ball. The ordinary gradient IMS identity gives

$$
\mathfrak h[\chi f_n]+\mathfrak h[\zeta f_n]
 =\mathfrak h[f_n]+\int
 \left(a(|\nabla_\xi\chi|^2+|\nabla_\xi\zeta|^2)
 +\eta(|\partial_t\chi|^2+|\partial_t\zeta|^2)\right)|f_n|^2.
\tag{104.20}
$$

The error tends to zero by local strong $L^2$ convergence. Both forms on the left are nonnegative. Also $J[\chi f_n]\to0$: on $t=0$ it vanishes for $|\xi|\le r$; on each fixed annulus $r<|\xi|<R$ the traces converge strongly to zero in $L^2$; and on $|\xi|>R$ its contribution is bounded by $R^{-1}\|f_n(\cdot,0)\|_2^2\le C/R$. For completeness, the annular trace convergence follows by applying the one-dimensional trace estimate to a compactly supported cutoff of $f_n$: its $L^2$ norm tends to zero and its first derivative remains bounded. The same estimate without a cutoff gives the uniform global trace bound used for the tail. Hence (104.18)–(104.20) imply

$$
aA[\chi f_n]+\eta C[\chi f_n]\longrightarrow0,\qquad
\|f_n-\chi f_n\|_2\longrightarrow0.
\tag{104.21}
$$

Only the second assertion concerns probability; the first controls the exterior derivatives.

For each fixed $c>0$, Plancherel now gives

$$
\|\mathbf1_{(c,\infty)}(|D_t|)f_n\|_2
 \le\|f_n-\chi f_n\|_2+c^{-1}\|\partial_t(\chi f_n)\|_2
 \longrightarrow0.
\tag{104.22}
$$

By the last equality in (104.17), this is $\vartheta_n((c,\infty))\to0$, proving its narrow limit. Its second moment is exactly $M_nD_2[v_n]=d_n$.

For horizontal probability, the ordinary three-dimensional Sobolev inequality and Hölder, applied at almost every $t$ and integrated, give
$\int_{|\xi-b|<C}|h(\xi,t)|^2d\xi dt\le C' C^2 A[h]$
for $h\in H^1(\mathbb R^4)$, uniformly in $b$. Apply this consumed estimate to $h=\chi f_n$, and use (104.21) to replace $h$ by $f_n$ with an $L^2$ error tending to zero. The marginal identity (104.17) proves (104.13), including arbitrary moving horizontal centres.

To pass to actual central spatial probability, fix $c>0$ and set $P_n=\mathbf1_{[0,c/\ell_n]}(|D_w|)$ and $Q_n=I-P_n$. Equation (104.22) gives $\|Q_nv_n\|_2\to0$. Fourier Cauchy–Schwarz in each actual central fibre gives

$$
\operatorname*{ess\,sup}_w|P_nv_n(\xi,w)|^2
 \le\frac{c}{\pi\ell_n}\int|v_n(\xi,w)|^2dw.
$$

Therefore every $E$ in (104.15) satisfies

$$
\|\mathbf1_Ev_n\|_2
 \le\sqrt{Cc/\pi}+\|Q_nv_n\|_2.
\tag{104.23}
$$

First let $n\to\infty$, then $c\downarrow0$. The estimate is uniform in $E$. A shear translates each section without changing its length, proving the stated coordinate and moving-centre quantifiers. All transfers from $f_n$ use only the two equalities in (104.17) and the actual central Fourier projection; the nonlinear comparison is never inverted. $\square$

**Theorem 104.4 (moving-band probability/resource separation and absence of small Carnot profiles).** For every fixed $c>0$, use the actual $P_n,Q_n$ of the preceding proof. Then

$$
\|P_nv_n\|_2^2\to1,\qquad \|Q_nv_n\|_2^2\to0,\qquad
\frac{F[P_nv_n]}{F[v_n]}\to0,\qquad
\frac{F[Q_nv_n]}{F[v_n]}\to1
\quad(F=V,T,D_2,D_{\sigma_n}).
\tag{104.24}
$$

Each $F$ is evaluated on the projected state. In particular no additive or commuting decomposition of $V$ is asserted. For every fixed $0<C<\infty$,

$$
\sup_{p\in G}\mu_n(B_\rho(p,C M_n^{1/4}))\longrightarrow0.
\tag{104.25}
$$

The same conclusion holds for balls of any fixed Carnot–Carathéodory distance of the original horizontal geometry. More precisely, for arbitrary $p_n\in G$ and $0<r_n\le C M_n^{1/4}$, the norm-one states

$$
w_n(q)=r_n^{5/2}v_n(p_n\delta_{r_n}q)
 =\frac{r_n^{5/2}}{\sqrt{M_n}}u_n(p_n\delta_{r_n}q)
\tag{104.26}
$$

converge strongly to zero in $L^2$ on every compact subset of $G$, and weakly to zero in global $L^2$. They have no globally strongly convergent subsequence. This excludes any nonzero local $L^2$ profile at these radii even after arbitrary moving translations and the required probability normalization.

**Proof.** The probability assertions in (104.24) are (104.14). For the resources, the same actual law gives

$$
\begin{aligned}
D_2[P_nu_n]&=\int_{[0,c]}x^2d\vartheta_n(x)\longrightarrow0,\\
D_{\sigma_n}[P_nu_n]
 &=\ell_n^{-\epsilon_n}\int_{[0,c]}x^{2+\epsilon_n}d\vartheta_n(x)
 \longrightarrow0.
\end{aligned}
\tag{104.27}
$$

Indeed $\ell_n^{-\epsilon_n}\to1$ by (104.2). For either integral, its part on $[0,\delta]$ is uniformly $O(\delta^2)$ and its part on $[\delta,c]$ tends to zero by (104.14); then let $\delta\downarrow0$. This handles the sharp cutoff without a continuity assumption at $c$.

The genuine free reduction of Proposition 85.2 gives $T[P_nu_n]\le T[u_n]$ and preserves $\mathcal E_{\sigma_n}$ for each $n$. The whole-domain endpoint inequality gives
$V[P_nu_n]\le\frac18\sqrt{T[P_nu_n]D_2[P_nu_n]}\to0$.
Use the legitimate test $P_nu_n$ in the actual equation:

$$
0\le aT[P_nu_n]+\eta D_{\sigma_n}[P_nu_n]
 =g_n v(P_nu_n,u_n)
 \le g_n\sqrt{V[P_nu_n]V[u_n]}\longrightarrow0.
\tag{104.28}
$$

The equality makes the pairing real and nonnegative. Orthogonal kinetic splitting gives the complementary limits $t_c,d_c,d_c$. For the potential, the weighted triangle inequality gives
$|\sqrt{V[Q_nu_n]}-1|\le\sqrt{V[P_nu_n]}\to0$.
Divide by the positive full-state resource totals, using (104.2). Amplitude homogeneity identifies the resulting fractions with those for $v_n$. This proves (104.24), without ever applying a central projector to $\Gamma|v_n|^2$.

Every left-translated $\rho$ ball of radius $r$ has central sections of length at most $2r^2$: in symmetric shear coordinates the group product translates the central coordinate by an affine function of $\xi$, while the defining inequality bounds its remaining displacement by $r^2$. At $r=C M_n^{1/4}$ these lengths are at most $2C^2\ell_n$, so (104.15) proves (104.25) uniformly in the centre. Fixed Carnot–Carathéodory balls are contained in fixed multiples of these balls, by homogeneity and boundedness of their unit ball in $\rho$.

Left translation preserves Haar measure and $\delta_r$ has Jacobian $r^5$. Thus (104.26) has norm one. Every compact $K\subset G$ is contained in some $B_\rho(e,R)$, and

$$
\int_K|w_n|^2d\mu
 =\int_{p_n\delta_{r_n}K}|v_n|^2d\mu
 \le\mu_n(B_\rho(p_n,Rr_n))\longrightarrow0.
\tag{104.29}
$$

Compactly supported $L^2$ tests are dense in global $L^2$, proving weak convergence to zero. A global strong limit would then be zero, contradicting the conserved norm one. $\square$

**Theorem 104.5 (quantitative separation of probability and the same-state potential probability).** For every $n$, $p\in G$ and $r>0$,

$$
\begin{aligned}
\mu_n(B_\rho(p,r))
 &\le\min\left\{1,\ 2r^2\sqrt{d_n/M_n}\right\},\\
\nu_n(G\setminus B_\rho(e,r))
 &\le\min\left\{1,\ \frac{6B_\Gamma\sqrt{M_nd_n}}r\right\}.
\end{aligned}
\tag{104.30}
$$

In particular, for every fixed $1/4<\alpha<1/2$,

$$
\mu_n(B_\rho(e,M_n^\alpha))\longrightarrow0,\qquad
\nu_n(G\setminus B_\rho(e,M_n^\alpha))\longrightarrow0,
\qquad d_{\rm TV}(\mu_n,\nu_n)\longrightarrow1,
\tag{104.31}
$$

where $d_{\rm TV}(\mu,\nu)=\sup_E|\mu(E)-\nu(E)|$ for probability measures. Thus the normalized potential resource is asymptotically supported on sets carrying vanishing unweighted probability of the very same actual state.

**Proof.** The one-dimensional Sobolev estimate
$\|h\|_\infty^2\le\|h\|_2\|h'\|_2$
for $h\in H^1(\mathbb R)$ follows by integrating the derivative of $|h|^2$ towards both infinities, adding the two bounds and applying Cauchy–Schwarz. Apply it to almost every central fibre of the actual $v_n$, which belongs to $\mathcal E_2$. Integrating the fibre suprema and using Cauchy–Schwarz in $\xi$ gives

$$
\int\operatorname*{ess\,sup}_w|v_n(\xi,w)|^2d\xi
 \le\|v_n\|_2\|\partial_wv_n\|_2
 =\sqrt{d_n/M_n}.
\tag{104.32}
$$

The central section length bound $2r^2$ used in the proof of (104.25) now gives the first estimate of (104.30), uniformly in $p$. This estimate uses actual central derivatives and probability, with no substitution of a marginal field.

Put $A_n=\sqrt{d_n/M_n}$. Tonelli's theorem and the first estimate, with centre $e$, give

$$
\begin{aligned}
\int_{\rho\ge r}\rho^{-3}d\mu_n
 &=3\int_r^\infty t^{-4}\mu_n\{r\le\rho<t\}\,dt\\
 &\le3\int_r^\infty t^{-4}\mu_n(B_\rho(e,t))\,dt
 \le6A_n/r.
\end{aligned}
\tag{104.33}
$$

Multiplication by $M_nB_\Gamma$ and the actual bound $\Gamma\le B_\Gamma\rho^{-3}$ prove the second estimate in (104.30). Both measures have mass one, giving the stated minima. Substituting $r=M_n^\alpha$ gives upper bounds $2\sqrt{d_n}M_n^{2\alpha-1/2}$ and $6B_\Gamma\sqrt{d_n}M_n^{1/2-\alpha}$, respectively, and both vanish in the prescribed open interval. On the same moving ball $\nu_n$ tends to one while $\mu_n$ tends to zero; hence $1\ge d_{\rm TV}(\mu_n,\nu_n)\to1$. With the alternative convention $\|\mu-\nu\|_{\rm variation}$ the limit is $2$. These elementary inequalities are proof intermediates for the actual-state conclusion, not additional stand-alone novelty claims. $\square$

**Definition 104.6 (mathematical attribution and unresolved boundaries).** The fixed source and its genuine central projections are supplied by §§82–85. The precise Fourier-modulus comparison, its preserved horizontal marginal and central spectral probability, the sharp trace intermediate, and the actual critical Friedrichs zero kernel are those of §§87.2–87.4. The actual full-domain equation and critical states are supplied by §§101.5 and 102.3; all endpoint resource and mass inputs are exactly (104.2) from §103. No trial family replaces an actual state in the assertions above.

Alvino–Ferone–Volpicelli, [*Sharp Hardy inequalities in the half space with trace remainder term*, Theorem 1.1 and (8)](https://arxiv.org/html/1105.0335v1), at $n=4$, $\beta=2$, supply the existing $2/\pi$ halfspace trace constant, hence $4/\pi$ on both halfspaces. Its extension to complex $H^1$ functions and its closed auxiliary zero-kernel passage are the supplies proved in §87. The use here is precisely the scaled form (104.18), not a replacement of $\Gamma$ by its marginal and not an inverse of the nonlinear comparison.

Lundholm–Nam–Portmann, [*Fractional Hardy–Lieb–Thirring and related inequalities for interacting systems*, Lemma 14 and Remark 13](https://arxiv.org/html/1501.04570v3), give a fractional IMS localization formula for fixed order $s>0$ on bounded Euclidean domains, with a lower-order error. That is mature localization context. Its constants and the order of its error do not by themselves give the uniform estimate required here as $s=\sigma/2\downarrow1$. The whole-central-line double-commutator bound (104.9)–(104.10), its uniform $D_{\sigma-2}$ error and its consumption of (103.24) provide that passage explicitly.

Ciatti–Cowling–Ricci, [*Hardy and uncertainty inequalities on stratified Lie groups*, Theorem A, Theorem 3.1 and Corollary 3.2](https://arxiv.org/html/1308.2373v1), enter only through the already proved §102–§103 mass supplies: their $p=2$ orders $1,2$ are below $Q/p=5/2$ for this $Q=5$ group, the original $L$ and the homogeneous norm $\rho$. Teschl, [*Mathematical Methods in Quantum Mechanics*, §2.2, (2.19)–(2.20), and §2.3, Theorems 2.12–2.13](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), supplies the mature adjoint and closed-form representation principles. Here the ambient Hilbert space is exactly $L^2(G,d\mu)$, the symmetric initial operator is (104.5), and its Friedrichs form domain is the existing $\mathcal Q_c$. The adjoint test in (104.12) supplies maximal-domain membership, while form-core density and (87.19) supply (104.6); no literature theorem identifies those domains for this singular field. Ordinary Sobolev, Rellich, Plancherel, trace, probability compactness and layer-cake estimates are consumed only inside these deductions.

The repository-derived content is the actual normalized-state local bounds and simultaneous defect representation, the excluded moving probability scales and spectral probability/resource split, and the quantitative singular reweighting of those same actual states. These are fixed-source deductions with the stated supplier correspondence, not a claim of exhaustive literature priority. Equations (104.13)–(104.15) exclude concentration on the inverse-kinetic horizontal and central scales, and (104.25) excludes even translated Carnot profiles of radius $O(M_n^{1/4})$. They select no larger spatial scale or limiting shape. Equation (104.30) also controls potential-probability tails whenever $r_n/\sqrt{M_n}\to\infty$, but does not identify a rescaled potential-probability distribution at $r_n\asymp\sqrt{M_n}$.

The values of $m_e,m_\infty$, existence or nonexistence of nonzero elements of $\mathcal N_0$, attainability of the defect triples, and normalized-probability tightness on the original $G$ remain unresolved. Any nonzero weak profile lies outside $\mathcal Q_c$ by (104.6); no alternate self-adjoint extension is selected. No positivity, simplicity, uniqueness, resonance classification, source-to-state physical realization or physical space-dimension conclusion is implied.

## 追加锚（本行以下为增补区）

## 105. Actual endpoint probability cannot escape to infinity

**Theorem 105.1 (unconditional exterior probability compactness).** Keep exactly the original group, Haar measure, field, operators, clock, central spectral units and fixed $a,\eta>0$ of Definitions 103.1 and 104.1. For every sequence $\sigma_n>2$ tending to $2$, without a monotonicity requirement, choose any nonzero actual attained critical zero states in the full complex $\mathcal E_{\sigma_n}$ and normalize their amplitudes by

$$
V[u_n]=1,\qquad M_n=\|u_n\|_2^2,\qquad
v_n=M_n^{-1/2}u_n,\qquad \|v_n\|_2=1.
$$

Then their original-space probabilities satisfy

$$
\lim_{R\to\infty}\limsup_{n\to\infty}
 \int_{\{\rho>R\}}|v_n|^2\,d\mu=0.
\tag{105.1}
$$

In every simultaneous subsequential decomposition (104.7), consequently,

$$
m_\infty=0,\qquad \|v\|_2^2+m_e=1.
\tag{105.2}
$$

Along each of the weak state subsequences of Theorem 104.2, every fixed bounded measurable cutoff $\zeta$ that vanishes on a neighborhood of $e$ satisfies

$$
\zeta v_n\longrightarrow\zeta v
 \quad\hbox{strongly in }L^2(G,d\mu).
\tag{105.3}
$$

In particular this holds for smooth exterior cutoffs equal to one outside a compact set. No value of $m_e$, nonzero maximal-adjoint profile, positivity, simplicity or uniqueness is asserted.

**Proof.** All free realizations below are those of §§85.2 and 102.2 on the common Hilbert space $L^2(G,d\mu)$. Write $D=D_w$, $\epsilon_n=\sigma_n-2$ and

$$
A_\sigma=aL+\eta|D|^\sigma,\qquad
R_{\sigma,r}=(A_\sigma+r)^{-1}\quad(r>0).
$$

We use $2\le\sigma\le5/2$ for uniform estimates; every sequence in the statement eventually lies in this interval. The strong commutation and the actual magnetic estimate (101.3) put the joint spectral variables $(\ell,\lambda)$ of $(L,D)$ in

$$
\ell\ge|\lambda|,\qquad
A_\sigma(\ell,\lambda)=a\ell+\eta|\lambda|^\sigma.
\tag{105.4}
$$

The passage from (101.3) to this spectral support uses the original direct integral: each central fibre has $L_\lambda\ge|\lambda|$, so its spectral projection below $|\lambda|$ vanishes. The domain and form identities are (102.10)–(102.12). Both $L$ and $A_\sigma$ have zero kernel, since a zero vector of either has central Fourier support in the Haar-null singleton $\lambda=0$.

We first record the precise free inverse estimates consumed by the actual-state proof. The order-two Hardy–Rellich inequality extended to $D(L)$ in (102.6), together with the joint multiplier bound, gives

$$
\|\rho^{-2}R_{\sigma,r}F\|_2
 \le h_2\|LR_{\sigma,r}F\|_2
 \le\frac{h_2}{a}\|F\|_2.
\tag{105.5}
$$

If $f\in L^2$ and $\rho^2f\in L^2$, duality therefore gives $\|R_{\sigma,r}f\|_2\le(h_2/a)\|\rho^2f\|_2$. The spectral theorem and monotone convergence as $r\downarrow0$ imply $f\in D(A_\sigma^{-1})$, and then dominated convergence gives

$$
R_{\sigma,r}f\longrightarrow A_\sigma^{-1}f\quad\hbox{in }L^2,
\qquad
\|A_\sigma^{-1}f\|_2\le\frac{h_2}{a}\|\rho^2f\|_2.
\tag{105.6}
$$

Here $A_\sigma^{-1}$ is its spectral inverse on its actual domain, not an everywhere bounded inverse. A second inverse expression used below is the bounded joint multiplier

$$
T_\sigma=\frac{D}{A_\sigma},\qquad
T_\sigma(\ell,\lambda)=\frac{\lambda}{a\ell+\eta|\lambda|^\sigma},
\qquad \|T_\sigma\|\le a^{-1}.
\tag{105.7}
$$

It is defined on all $L^2$ by (105.4), even when $Dh$ is only a distribution. The multipliers $DR_{\sigma,r}$ converge strongly to $T_\sigma$ by dominated convergence. None of these assertions uses an interacting operator domain or a positive heat kernel for $A_\sigma$.

The needed localized inverses are compact, including at zero energy, and continuous as $\sigma\downarrow2$. Here are the low-frequency details. For the original free $L$, let $E_I$ be its spectral projection on $I$. The original sub-Laplacian heat kernel, obtained from the $n=1$ Heisenberg kernel (4.1.2) of Krötz–Thangavelu–Xu and the independent $z$ Gaussian, has

$$
h_t(e)=c_Lt^{-5/2}\quad(0<t<\infty),\qquad 0<c_L<\infty.
$$

Indeed its central integral at the identity is a fixed positive constant times $\int_{\mathbb R}\lambda/\sinh(t\lambda)\,d\lambda$, which scales as $t^{-2}$, and the independent Gaussian contributes $t^{-1/2}$. The constants and the clock are the original ones of (85.12). Left invariance, the symmetry and semigroup identity of this free kernel give, for every bounded compactly supported multiplier $m$,

$$
\|e^{-tL/2}m\|_{\rm HS}^2=h_t(e)\|m\|_2^2,
\qquad
\|E_{[0,b]}m\|_{\rm HS}^2\le Cb^{5/2}\|m\|_2^2.
\tag{105.8}
$$

In the first formula $m$ denotes multiplication by that function; its Hilbert–Schmidt norm follows by integrating the squared convolution kernel. For the second formula factor $E_{[0,b]}m$ through $e^{-L/(2b)}m$; the remaining spectral multiplier has norm at most $e^{1/2}$. In particular the estimate holds for the indicator of any compact set. Splitting $(0,\delta]$ into $(2^{-j-1}\delta,2^{-j}\delta]$ and using orthogonality of the spectral ranges yields

$$
\|L^{-1}E_{(0,\delta]}m\|_{\rm HS}^2
 \le C\|m\|_2^2\delta^{1/2}
       \sum_{j\ge0}2^{-j/2}.
\tag{105.9}
$$

This is the place where the original homogeneous dimension $5>4$ is used. The inverse at low frequency is justified by the convergent spectral sum, rather than by a spectral gap.

On $\ell> K$ the multiplier $A_\sigma^{-1}$ is at most $(aK)^{-1}$. On $0<\ell\le\delta$, factor it as a contraction of norm at most $a^{-1}$ times $L^{-1}$ and use (105.9). On $\delta\le\ell\le K$, (105.8) supplies compactness after multiplication by $m$, and the inverse multipliers converge uniformly to those at $\sigma=2$: the denominator is at least $a\delta$ and $|\lambda|\le K$. First choosing small $\delta$ and large $K$, and then taking $\sigma\downarrow2$, proves

$$
A_\sigma^{-1}m\text{ is compact},\qquad
\|A_\sigma^{-1}m-A_2^{-1}m\|\longrightarrow0.
\tag{105.10}
$$

These compositions have their legal domain by (105.6), since $m$ has bounded support. Their compactness also follows from the displayed spectral approximations, which converge in operator norm.

For $\ell\ge1$, $|\lambda|\ge1$ implies $A_\sigma\ge a\ell+\eta|\lambda|^2$, while $|\lambda|<1$ gives $|\lambda|/A_\sigma\le(a\ell)^{-1}$. Consequently

$$
\sup_{\substack{\ell>K\\|\lambda|\le\ell}}
 \frac{|\lambda|}{a\ell+\eta|\lambda|^\sigma}
 \le CK^{-1/2}\quad(K\ge1).
\tag{105.11}
$$

For $0<\ell\le K$, the difference between the multipliers of $T_\sigma$ and $T_2$ is bounded by

$$
\frac{\eta|\lambda|\bigl||\lambda|^\sigma-|\lambda|^2\bigr|}
 {a^2\ell^2}
 \le\frac{\eta}{a^2}
       \bigl||\lambda|^{\sigma-1}-|\lambda|\bigr|.
$$

The last expression tends to zero uniformly on $|\lambda|\le K$, including zero. Thus (105.8) and (105.11) prove

$$
T_\sigma m\text{ is compact},\qquad
\|T_\sigma-T_2\|\longrightarrow0.
\tag{105.12}
$$

The compactness follows by approximating with $T_\sigma E_{[0,K]}m$, which is Hilbert–Schmidt. The convergence assertion is for bounded operators on all $L^2$.

We now apply these supplies to the actual states. The only extra small-order moment needed for a single central commutator follows directly from (104.2). Spectral Hölder, with $2\epsilon_n\le\sigma_n$, gives

$$
D_{2\epsilon_n}[v_n]
 \le\left(\frac{D_{\sigma_n}[u_n]}{M_n}\right)^{2\epsilon_n/\sigma_n}
 =O(1),\qquad
\|\langle D\rangle^{\epsilon_n}v_n\|_2=O(1).
\tag{105.13}
$$

The logarithm of the first right-hand side tends to zero, by $D_{\sigma_n}[u_n]\to d_c>0$ and $\epsilon_n\log(1/M_n)\to0$. Only boundedness of the moment is asserted. These bounds and (104.4) are uniform over actual critical-state choices sufficiently near $2$: a failure of such boundedness would choose a sequence of orders tending to $2$ and violating actual states, contrary to those universal sequential supplies.

Fix a real $\chi\in C_c^\infty(G)$ with $0\le\chi\le1$ and $\chi=1$ on a neighborhood of $e$. Put $\psi=1-\chi$ and $w_n=\psi v_n$. The horizontal and central multiplier estimates used in §104 show that $w_n\in\mathcal E_{\sigma_n}$. To handle the central part without an unproved uniform single-commutator estimate, let primes denote differentiation in the original $w$ coordinate and set

$$
h_n=-i\sigma_n\chi'|D|^{\epsilon_n}v_n.
$$

There are $k_n\in L^2$ such that, as distributions on the original group,

$$
[|D|^{\sigma_n},\chi]v_n=Dh_n+k_n,\qquad
\|h_n\|_2+\|k_n\|_2\le C.
\tag{105.14}
$$

Here $h_n$ has support in the fixed compact support of $\chi'$. To prove the assertion, at each fixed $\xi=(x,y,z)$ use the central transform and write its input frequency as $\mu$ and the cutoff frequency as $h$. Taylor's formula gives, for $p_\sigma(t)=|t|^\sigma$ and $\epsilon=\sigma-2\in[0,1/2]$,

$$
\begin{aligned}
p_\sigma(\mu+h)-p_\sigma(\mu)
 &=\sigma h\mu|\mu|^\epsilon+r_\sigma(\mu,h),\\
|r_\sigma(\mu,h)|
 &\le C|h|^2(\langle\mu\rangle^\epsilon+
                         \langle h\rangle^\epsilon).
\end{aligned}
\tag{105.15}
$$

The constant is uniform because $p_\sigma''(t)=\sigma(\sigma-1)|t|^\epsilon$. The leading operator is $-i\sigma\chi'D|D|^\epsilon$, which equals $D(-i\sigma\chi'|D|^\epsilon)+\sigma\chi''|D|^\epsilon$. The Fourier transforms of the smooth central sections of $\chi$ have uniformly bounded weighted $L^1$ norms. Young's inequality applied to the remainder in (105.15), followed by integration in $\xi$, bounds its $L^2$ norm by $C\|\langle D\rangle^\epsilon v_n\|_2$. Equation (105.13) proves (105.14). Smooth central Fourier approximation gives the identity on the stated actual domains; the remainder is an $L^2$ operator with exactly this bound. Only the actual domains and (105.13) were used; no reality condition on $v_n$ was imposed.

The remainder also has a uniform weighted tail, which is essential for a zero inverse. Choose a compact horizontal set $K_\xi$ and $J\ge1$ with $\operatorname{supp}\chi\subset K_\xi\times[-J,J]$ in the original coordinates. Then $k_n$ is zero outside $K_\xi\times\mathbb R$. For $|w|>2J$ both cutoff terms in $Dh_n$ vanish, and (105.14) gives

$$
k_n(\xi,w)=|D|^{\sigma_n}(\chi v_n)(\xi,w).
$$

For completeness, the off-support kernel here needs no higher-order positive semigroup. For $0<\epsilon\le1/2$ put

$$
c_\epsilon=
 \left(2\int_0^\infty\frac{1-\cos r}{r^{1+\epsilon}}\,dr\right)^{-1}.
$$

The integral is finite and positive. Its integral over $[\pi/2,\pi]$ bounds it below uniformly, so $c_\epsilon$ is uniformly bounded. Fourier inversion of $1-\cos(\lambda r)$ gives the usual $|D|^\epsilon$ singular integral. For a function $g$ supported in $[-J,J]$, away from that interval it is $-c_\epsilon\int g(t)|w-t|^{-1-\epsilon}dt$. Applying $D^2=-\partial_w^2$ there gives

$$
|D|^{2+\epsilon}g(w)
 =c_\epsilon(1+\epsilon)(2+\epsilon)
   \int\frac{g(t)}{|w-t|^{3+\epsilon}}\,dt.
$$

This calculation starts with smooth $g$ and extends to compactly supported $L^2$ functions distributionally and pointwise off their support by the absolutely convergent integral. It proves the uniform estimate

$$
|k_n(\xi,w)|
 \le C|w|^{-1-\sigma_n}
          \int_{-J}^{J}|\chi v_n(\xi,t)|\,dt
 \quad(|w|>2J).
\tag{105.16}
$$

On $K_\xi\times\mathbb R$, the original shear gives $\rho^2\le C(1+|w|)$. Cauchy–Schwarz in $t$, $\|v_n\|_2=1$, and (105.16) imply, for $W>2J$,

$$
\int_{|w|>W}\rho^4|k_n|^2\,d\mu
 \le C\int_W^\infty t^{-2\sigma_n}\,dt
 \le CW^{-3}.
\tag{105.17}
$$

Together with (105.14), this proves $\rho^2k_n\in L^2$ and uniformly vanishing weighted tails as $\rho\to\infty$. The compact horizontal support is important here: on it, $\rho\to\infty$ forces $|w|\to\infty$. The calculation treats the actual central line, not an auxiliary inverse profile correspondence.

The actual equation (103.3), valid also for $v_n$ by amplitude homogeneity, now localizes to

$$
\begin{gathered}
A_{\sigma_n}w_n=f_n-\eta Dh_n,\\
f_n=g_n\Gamma w_n+b_n-\eta k_n,\qquad
b_n=-a(L\chi)v_n+2a\sum_i(X_i\chi)(X_iv_n).
\end{gathered}
\tag{105.18}
$$

This is an identity of free form functionals, with a distributional derivative in its last term. The supports of $L\chi$ and $X_i\chi$ are compact and avoid $e$; (104.4) therefore bounds $b_n$ in $L^2$ on a fixed compact set. Since $\psi$ vanishes near $e$, $\Gamma\psi$ is bounded. Its weighted tail satisfies

$$
\|\mathbf1_{\{\rho>R\}}\rho^2\Gamma w_n\|_2
 \le\frac{B_\Gamma}{R}\|v_n\|_2=\frac{B_\Gamma}{R}.
$$

Consequently (105.14) and (105.17) give the simultaneous source bounds

$$
\sup_n\bigl(\|f_n\|_2+\|\rho^2f_n\|_2\bigr)<\infty,
\qquad
\lim_{R\to\infty}\sup_n
 \|\mathbf1_{\{\rho>R\}}\rho^2f_n\|_2=0,
\tag{105.19}
$$

after discarding finitely many indices. All constants depend only on the fixed cutoff, fixed model and the uniform endpoint supplies, not on a phase, sign or chosen critical vector.

We justify inversion of (105.18) on its exact domains. Multiplication by $\psi$ preserves $\mathcal E_{\sigma_n}$ by the horizontal product rule and the same central Fourier multiplier bounds used in (105.15). The localized equation first follows on smooth tests from (103.3). Its right-hand side is continuous in the free form norm: $f_n\in L^2$, $h_n\in L^2$ and $\|D\phi\|_2^2\le\|\phi\|_2^2+D_{\sigma_n}[\phi]$. Core density thus extends it to every test in $\mathcal E_{\sigma_n}$. This uses neither $\Gamma v_n\in L^2$ nor a separate operator action on that singular product.

For an arbitrary $F\in L^2$ take the legal free test $R_{\sigma_n,r}F\in D(A_{\sigma_n})\subset\mathcal E_{\sigma_n}$ in this identity. Its central derivative is in $L^2$ by (105.4), and the represented-form identity gives the equality of $L^2$ vectors

$$
(I-rR_{\sigma_n,r})w_n
 =R_{\sigma_n,r}f_n-\eta DR_{\sigma_n,r}h_n.
$$

Here $n$ is fixed while $r\downarrow0$. The zero kernel of $A_{\sigma_n}$ makes the left side tend strongly to $w_n$. Equations (105.6), (105.7) and (105.19) justify the two right-side limits, yielding the actual identity

$$
w_n=A_{\sigma_n}^{-1}f_n-\eta T_{\sigma_n}h_n
 \quad\hbox{in }L^2(G,d\mu).
\tag{105.20}
$$

Thus no unbounded inverse was applied to an unspecified distribution, and no exchange between the $r$ and $n$ limits is required.

For fixed $R$, let $m_R=\mathbf1_{\{\rho\le R\}}$. By (105.10), the bounded sequence $A_{\sigma_n}^{-1}m_Rf_n$ is relatively compact: it differs in norm by a quantity tending to zero from the image of a bounded sequence under the compact operator $A_2^{-1}m_R$. The remaining part has, by (105.6) and (105.19), norm bounded by

$$
\frac{h_2}{a}\|\rho^2(1-m_R)f_n\|_2,
$$

uniformly tending to zero as $R\to\infty$. Hence $\{A_{\sigma_n}^{-1}f_n\}$ is relatively compact in global $L^2$. The $h_n$ are bounded and supported in one fixed compact set. Equation (105.12) gives the same relative compactness for $\{T_{\sigma_n}h_n\}$. Equation (105.20) proves that the actual exterior states $\{\psi v_n\}$ are relatively compact in global $L^2$.

A relatively compact subset of $L^2(G,d\mu)$ has uniformly vanishing tails outside $\rho$ balls: cover it by finitely many $L^2$ balls, use the individual tail limits of their centers, and then shrink the covering radius. Outside a fixed compact set $\psi=1$, so this proves exactly (105.1), with $n\to\infty$ first and $R\to\infty$ second. This argument holds for each arbitrary actual-state selection in the statement.

Finally take any weak subsequence from Theorem 104.2. On compact annuli about $e$ it already converges strongly in $L^2$ to $v$. For a fixed $\zeta$ in (105.3), its support avoids some neighborhood of $e$ and

$$
\limsup_n\|\mathbf1_{\{\rho>R\}}\zeta(v_n-v)\|_2^2
 \le2\|\zeta\|_\infty^2
 \left(\limsup_n\int_{\rho>R}|v_n|^2d\mu
                      +\int_{\rho>R}|v|^2d\mu\right).
$$

Both terms tend to zero as $R\to\infty$, the first by (105.1) and the second since $v\in L^2$. The compact annular part converges strongly by §104. This proves (105.3) along the existing subsequence, without requiring further extraction. The same tail estimate excludes an atom at infinity in each measure limit (104.7); its mass identity becomes (105.2). It gives no exclusion of the source atom. $\square$

**Definition 105.2 (primary suppliers, correspondence and remaining boundary).** The source-specific input is the full complex actual equation and critical attainment of §§101.5 and 102.3, the universal endpoint and subexponential limits (104.2), and the punctured local bounds and subsequences of Theorem 104.2. These are reused results, not new claims of attainment or local compactness. The free joint realization, core and legal resolvent tests are those of §§85.2 and 102.2; the fibre support (105.4) is exactly the magnetic estimate (101.3).

Ciatti–Cowling–Ricci, [*Hardy and uncertainty inequalities on stratified Lie groups*, Theorem A and Corollary 3.2](https://arxiv.org/html/1308.2373v1), supply the order-two inequality used in (105.5): $p=2$, order $2<Q/p=5/2$, the original sub-Laplacian and the homogeneous norm $\rho$. Its extension to $D(L)$ is already (102.6). The weighted zero inverse (105.6) is obtained by duality and spectral limits on the specified domain; the citation is not an everywhere-defined unweighted inverse theorem.

Krötz–Thangavelu–Xu, [*The heat kernel transform for the Heisenberg group*, §4.1, equation (4.1.2)](https://arxiv.org/html/math/0401243v2), supply the Heisenberg sub-Laplacian kernel at $n=1$. The shear has Jacobian one and identifies their symmetric group product with the original one; reversing their central Fourier sign leaves the diagonal coefficient even. Multiplication by the independent original $z$ Gaussian gives the original $L$ heat kernel and the $t^{-5/2}$ diagonal used in (105.8). Their full Laplacian with an extra central second derivative is not used. Spectral localization, Hilbert–Schmidt compactness, the one-dimensional Fourier singular-integral identity, Taylor's formula, Young's inequality and the regularized free-form inversion are consumed mathematical intermediates inside this proof. No varying-order single-commutator theorem is imported from a fixed-order fractional IMS formula.

The additional conclusion is repository-derived for the same actual states: no probability mass escapes to infinity, and fixed exterior cutoffs converge strongly along the existing weak subsequences. It is not a new heat law, an inverse of the auxiliary AFV comparison, a resource-measure conclusion or an exhaustive literature-priority claim. The coefficient $m_e$, whether $\ker S^*$ contains nonzero elements, which such elements and source defects are attained by actual selections, and any surviving source scale or profile remain unresolved. Equation (104.6) continues to put any nonzero weak profile outside $\mathcal Q_c$; no source boundary condition or maximal/Friedrichs domain identity is imposed. No native source-to-state realization or physical space-dimension conclusion follows.

## 追加锚（本行以下为增补区）

## 106. Actual probability vanishes on every shrinking diagnostic annulus

**Definition 106.1 (fixed diagnostic and the actual selections).** Retain the original $G=H^1\times\mathbb R$, product, Haar measure, unit-source Green field $\Gamma$, horizontal $L$, free clock and central spectral units of Definition 103.1. Fix the same $a,\eta>0$ and set

$$
\kappa=\sqrt{\eta/a},\qquad \xi=(x,y,z),\qquad s=w-xy/2,
\qquad R_\kappa(p)=\bigl(|\xi|^2+(s/\kappa)^2\bigr)^{1/2}.
\tag{106.1}
$$

This is a fixed analytic diagnostic on the original group, not a new group norm, kinetic law, heat clock or source. For every sequence $\sigma_n>2$ tending to $2$, without monotonicity, select any nonzero attained complex critical zero states on the full $\mathcal E_{\sigma_n}$, and normalize only their amplitudes by

$$
V[u_n]=1,\qquad M_n=\|u_n\|_2^2,\qquad
v_n=M_n^{-1/2}u_n,\qquad \|v_n\|_2=1,\qquad
\epsilon_n=\sigma_n-2.
\tag{106.2}
$$

These are exactly the selections of Definitions 103.1 and 104.1. Their existence, full form equation, endpoint kinetic limits, $M_n\to0$ and $\epsilon_n\log(1/M_n)\to0$ are supplied by §§101–104. No sign, positivity, simplicity, uniqueness or profile condition is imposed. All state limits use the fixed complex Hilbert spaces with the indicated Lebesgue measures.

**Theorem 106.2 (all shrinking annuli and diagnostic zooms of actual states).** For every selection in Definition 106.1, every sequence $r_n>0$ tending to zero and every fixed $0<c<C<\infty$,

$$
\int_{\{c r_n<R_\kappa<C r_n\}}|v_n|^2d\mu\longrightarrow0.
\tag{106.3}
$$

In particular the order of limits in the following uniform small-radius assertion is valid:

$$
\lim_{\delta\downarrow0}\limsup_{n\to\infty}
 \sup_{0<r\le\delta}
 \int_{\{cr<R_\kappa<Cr\}}|v_n|^2d\mu=0.
\tag{106.4}
$$

The conclusion is also uniform over the actual critical-state choices. Precisely, if $\mathcal Z_\sigma$ is the set of all $L^2$-normalized attained complex critical zero states in the original $\mathcal E_\sigma$, then

$$
\lim_{\delta\downarrow0}\limsup_{\sigma\downarrow2}
 \sup_{v\in\mathcal Z_\sigma}\sup_{0<r\le\delta}
 \int_{\{cr<R_\kappa<Cr\}}|v|^2d\mu=0.
\tag{106.5}
$$

Here $\sigma\downarrow2$ means approach from above, without a monotonicity requirement. The inner limiting operations in (106.4)–(106.5) precede $\delta\downarrow0$; neither formula asserts a rate in $r$ for a fixed order.

Equivalently, for every such $r_n$, the actual norm-one diagnostic zooms

$$
\begin{aligned}
F_n(X,t)
 &=\kappa^{1/2}r_n^2\,
 v_n\!\left(r_nX_1,r_nX_2,r_nX_3,
       \kappa r_nt+\tfrac12r_n^2X_1X_2\right),\\
\|F_n\|_{L^2(\mathbb R^4,dXdt)}&=1
\end{aligned}
\tag{106.6}
$$

converge weakly to zero in global $L^2(\mathbb R^4)$ and strongly to zero in $L^2(K)$ for every compact $K\subset\mathbb R^4\setminus\{0\}$. They have no globally strongly convergent subsequence. The shear and the Jacobian $d\mu=\kappa r_n^4dXdt$ in (106.6) are those of the original states; no nonlinear Fourier-modulus comparison is inverted.

**Proof.** Write $\mathcal G(\xi,s)=\Gamma(\xi,s+x y/2)$ and, for $r>0$, put

$$
\begin{gathered}
W_r(X,t)=r^2\mathcal G(rX,\kappa rt),\\
Y_{1,r}=\partial_{X_1}-\frac{rX_2}{2\kappa}\partial_t,
\quad Y_{2,r}=\partial_{X_2}+\frac{rX_1}{2\kappa}\partial_t,
\quad Y_{3,r}=\partial_{X_3},\qquad
\mathcal L_r=-\sum_iY_{i,r}^2.
\end{gathered}
\tag{106.7}
$$

The exact original marginal and homogeneous bound, already supplied by §§82–85 and (102.2), imply

$$
\begin{gathered}
\int_{\mathbb R}W_r(X,t)dt=\frac1{4\pi\kappa|X|}
 \quad(X\ne0),\\
0\le W_r(X,t)
 \le B_\Gamma r^{1/2}
          \bigl(r^2|X|^4+\kappa^2t^2\bigr)^{-3/4}.
\end{gathered}
\tag{106.8}
$$

The second formula is only an upper bound for the same $\Gamma$. In particular, for fixed $d>0$, $W_r\le C_d r^{1/2}$ on $|t|\ge d$, and its central mass outside $|t|<d$ is $O(r^{1/2}d^{-1/2})$, uniformly in $X$. Together with the first formula this is an approximate identity in the central variable on each compact set $0<b\le|X|\le B$. It is not a pointwise replacement of the original field by a trace multiplier.

We shall use two direct consequences on sets away from the diagnostic origin. First, for each compact $K\subset\mathbb R^4\setminus\{0\}$ and each $\tau>0$, there is $C_{K,\tau}$, independent of $0<r\le1$, such that

$$
\int W_r|h|^2dXdt
 \le\tau\|\partial_th\|_2^2+C_{K,\tau}\|h\|_2^2
 \quad\bigl(h\in H^1(\mathbb R^4),\ \operatorname{supp}h\subset K\bigr).
\tag{106.9}
$$

To see this, choose $b,d>0$ so that $K\cap\{|X|<b\}$ is contained in $\{|t|\ge d\}$. On $|X|<b$ the second bound in (106.8) bounds the integral by $C_d\|h\|_2^2$. On $|X|\ge b$ its marginal bounds it by $(4\pi\kappa b)^{-1}\int\sup_t|h(X,t)|^2dX$. The one-dimensional inequality used in (104.32) bounds this last integral by $\|h\|_2\|\partial_th\|_2$. Young's inequality gives (106.9). This proof applies to complex $h$.

Second, if $r_j\to0$, $H_j$ is bounded in $H^1$ locally off zero, and $H_j\to H$ strongly in $L^2$ locally off zero, then for every $\phi\in C_c^\infty(\mathbb R^4\setminus\{0\};\mathbb C)$,

$$
\int W_{r_j}\overline\phi H_jdXdt
 \longrightarrow\frac1{4\pi\kappa}
       \int_{\mathbb R^3}\frac{\overline{\phi(X,0)}H(X,0)}{|X|}dX.
\tag{106.10}
$$

Here the right side uses the local Sobolev trace. For a detailed justification, split the support of $\phi$ into a part away from $t=0$ and a part with $|X|$ bounded below. The first part tends to zero by (106.8) and the local $L^2$ bound. On the second part insert a fixed smooth cutoff, supported away from zero and equal to one on a neighborhood of that part and its projection onto $t=0$. For the resulting $h_j=\overline\phi H_j$, both the $H^1$ norms and the horizontal supports are bounded. Its traces converge strongly in $L^2$: the squared trace norm of a compactly supported difference is bounded by its $L^2$ norm times a bounded central derivative norm, using the same one-dimensional trace inequality. For almost every $X$,

$$
|h_j(X,t)-h_j(X,0)|
 \le |t|^{1/2}\|\partial_th_j(X,\cdot)\|_2.
$$

On $|t|<d$, integration against $W_{r_j}$ and its marginal gives an error at most $C d^{1/2}$, by Cauchy–Schwarz in the bounded horizontal support. On $|t|\ge d$, the bound $C r_j^{1/2}|t|^{-3/2}$ controls the integral of $h_j$ by its bounded compact-support $L^1$ norm and controls the subtracted trace by $C r_j^{1/2}d^{-1/2}$ times its bounded $L^1$ norm. Fix $d$, let $j\to\infty$, and then let $d\downarrow0$. The marginal identity and strong trace convergence give (106.10). Smooth partitions of the support justify the indicated split, including where $X=0$ but $t\ne0$.

We next prove the local bounds needed to apply (106.10) to the actual zooms. First restrict to any subsequence on which

$$
r_n\ge\ell_n:=\sqrt{M_n}.
\tag{106.11}
$$

Since $r_n\to0$ and $\epsilon_n\log(1/M_n)\to0$, its central coefficient satisfies

$$
b_n=(\kappa r_n)^{-\epsilon_n}\longrightarrow1.
\tag{106.12}
$$

Indeed eventually $\kappa r_n<1$, and
$0\le-\epsilon_n\log(\kappa r_n)
\le\epsilon_n\log(1/M_n)/2+\epsilon_n|\log\kappa|$.
The unitary coordinate map in (106.6) sends the original full form domain exactly onto the distributional intersection defined by $Y_{i,r_n}F\in L^2$ and $|D_t|^{\sigma_n/2}F\in L^2$. Changing variables in the actual full form equation, and dividing its kinetic coefficient by $a r_n^{-2}$, gives on that entire transformed domain

$$
\sum_i\langle Y_{i,r_n}\psi,Y_{i,r_n}F_n\rangle
 +b_n\langle|D_t|^{\sigma_n/2}\psi,
                |D_t|^{\sigma_n/2}F_n\rangle
 =\frac{g_n}{a}\int W_{r_n}\overline\psi F_ndXdt.
\tag{106.13}
$$

There is no change of source, central spectral convention or interacting operator domain in this identity. In particular it holds for complex states and their legitimate form tests, without requiring $\Gamma v_n\in L^2$.

The global low-order moment in the commutator estimate is bounded. Using the unitary central transform and spectral Hölder as in (104.8),

$$
\begin{gathered}
D_{\epsilon_n}[v_n]
 \le\left(\frac{D_{\sigma_n}[u_n]}{M_n}\right)^{\epsilon_n/\sigma_n}
 =O(1),\\
D_{\epsilon_n}[F_n]
 =(\kappa r_n)^{\epsilon_n}D_{\epsilon_n}[v_n],\qquad
b_n\bigl(1+D_{\epsilon_n}[F_n]\bigr)
 =b_n+D_{\epsilon_n}[v_n]=O(1).
\end{gathered}
\tag{106.14}
$$

Here $D_\nu[F]=\||D_t|^{\nu/2}F\|_2^2$ for diagnostic functions, and $D_\nu[v_n]$ still uses the original $w$ coordinate. The boundedness is a consequence of the supplied actual-state limits, not an extra spectral cutoff.

Fix a real $\chi\in C_c^\infty(\mathbb R^4\setminus\{0\})$. Multiplication by $\chi$ and $\chi^2$ preserves the transformed domain. For the central domain this is the Fourier convolution multiplier bound of §104.2; for the horizontal derivatives it is the distributional product rule with $Y_{i,r_n}\chi$ bounded uniformly for $r_n\le1$. Thus $\psi=\chi^2F_n$ is a legal test in (106.13). The same whole-line double-commutator estimate (104.9), now in $t$ and multiplied by $b_n$, and the horizontal product rule give

$$
\begin{aligned}
\sum_i\|Y_{i,r_n}(\chi F_n)\|_2^2
 +b_nD_{\sigma_n}[\chi F_n]
 &\le\frac{g_n}{a}\int W_{r_n}|\chi F_n|^2dXdt\\
 &\quad+C_\chi\{1+b_n(1+D_{\epsilon_n}[F_n])\}.
\end{aligned}
\tag{106.15}
$$

The constants in (104.9) are uniform for $2<\sigma_n\le5/2$ and depend only on the fixed cutoff's central Fourier seminorms. This use of (104.9) includes its control of the nonlocal tails; localization has not been replaced by a fixed-test convergence argument. For each $n$, $\chi F_n\in H^1$: its central derivative is in $L^2$ since $\sigma_n>2$, and its ordinary horizontal derivatives follow from (106.7) on the compact support. No uniform bound has yet been assumed.

Apply (106.9) to the potential term. The inequality $D_2[h]\le\|h\|_2^2+D_{\sigma_n}[h]$, the bounded $g_n$, and $b_n\to1$ allow a fixed sufficiently small $\tau$ to absorb its central derivative term into the left side of (106.15). Since $\|F_n\|_2=1$ and (106.14) bounds the error, this proves

$$
\sum_i\|Y_{i,r_n}(\chi F_n)\|_2^2
 +D_{\sigma_n}[\chi F_n]+\|\chi F_n\|_{H^1(\mathbb R^4)}^2
 \le C_\chi.
\tag{106.16}
$$

For the last bound solve (106.7) for the ordinary horizontal derivatives; their extra coefficients are bounded on this support. Thus every subsequence satisfying (106.11) has a further subsequence with $F_n\rightharpoonup F$ in global $L^2$, with weak $H^1$ and strong $L^2$ convergence locally off zero. The local limits agree with the global weak limit. This uses ordinary Rellich compactness and a countable exhaustion, not a bound on the full global $H^1$ norms.

Move the free operators onto a fixed smooth compact test $\phi$ off zero in (106.13). One has
$\mathcal L_{r_n}\phi\to-\Delta_X\phi$ strongly in global $L^2$, directly from its polynomial coefficients, and
$b_n|D_t|^{\sigma_n}\phi\to-\partial_t^2\phi$ strongly in global $L^2$, by (106.12) and Fourier dominated convergence. This last convergence is on the whole central line, including the nonlocal tails. Equation (106.10) handles the actual potential term, and $g_n\to g_c$ with $g_c/(4\pi a\kappa)=4/\pi$ gives

$$
\int_{\mathbb R^4}\nabla\overline\phi\cdot\nabla F\,dXdt
 =\frac4\pi\int_{\mathbb R^3}
        \frac{\overline{\phi(X,0)}F(X,0)}{|X|}dX
 \quad\bigl(\phi\in C_c^\infty(\mathbb R^4\setminus\{0\})\bigr).
\tag{106.17}
$$

The left side uses the local $H^1$ limit. This is a conclusion about a diagnostic limit of actual states, rather than a hypothesis prescribing that limit. It imposes no Friedrichs boundary condition at the puncture.

We prove that (106.17) has no nonzero solution in $L^2(\mathbb R^4)\cap H^1_{\rm loc}(\mathbb R^4\setminus\{0\})$. This consumed intermediate uses separation of radial and angular variables, not identification with the original maximal operator. On $S^3\subset\mathbb R^4$ let $\Sigma=\{t=0\}\cap S^3=S^2$ and consider the angular form

$$
\mathfrak a[h,k]=\int_{S^3}\nabla_S\overline h\cdot\nabla_Sk\,d\omega
 -\frac4\pi\int_\Sigma\overline h k\,d\omega_\Sigma,
 \qquad D(\mathfrak a)=H^1(S^3).
\tag{106.18}
$$

This is a closed lower-bounded complex form with compact resolvent. Here are its needed hypotheses: the trace estimate on a tubular neighborhood of the compact equator gives
$\|h|_\Sigma\|_2^2\le\tau\|\nabla_Sh\|_2^2+C_\tau\|h\|_2^2$
for every $\tau>0$. It follows by integrating the one-dimensional normal trace estimate in finitely many smooth charts; the chart Jacobians are bounded above and below. For sufficiently small $\tau$, adding a fixed multiple of $\|h\|_2^2$ to (106.18) makes its norm equivalent to the complete $H^1$ norm, proving closedness and a lower bound. For a sufficiently large positive shift, the represented inverse maps bounded $L^2$ sets into bounded $H^1$ sets by coercivity of the shifted form. Compactness of $H^1(S^3)\hookrightarrow L^2(S^3)$ therefore makes that inverse compact. It is self-adjoint and injective. Closed-form representation and the compact self-adjoint spectral theorem therefore give a complete orthonormal basis $e_j\in H^1(S^3)$ with real eigenvalues $\lambda_j$ and
$\mathfrak a(h,e_j)=\lambda_j\langle h,e_j\rangle$ for all $h\in H^1(S^3)$. No angular simplicity, sign or sharp lower bound for $\lambda_j$ is needed.

Write $R=(|X|^2+t^2)^{1/2}$ and
$f_j(R)=\langle e_j,F(R,\cdot)\rangle_{L^2(S^3)}$. Local $H^1$ regularity off zero and the trace inequality extend (106.17), by smooth density, to compactly supported $H^1$ tests on every radial annulus. In particular $\phi=\zeta(R)e_j(\omega)$ is legal for $\zeta\in C_c^\infty(0,\infty)$. In polar variables the interface term has radial factor $R\,dR$, since $dX=R^2dR\,d\omega_\Sigma$ on $t=0$ and its weight is $R^{-1}$. The angular gradient term has the same factor. Consequently

$$
\int_0^\infty
 \bigl(R^3\overline{\zeta'}f_j'+\lambda_jR\overline\zeta f_j\bigr)dR=0,
\qquad
\int_0^\infty R^3|f_j(R)|^2dR<\infty.
\tag{106.19}
$$

The first equation is the Euler equation
$-f_j''-3R^{-1}f_j'+\lambda_jR^{-2}f_j=0$
distributionally on $(0,\infty)$; its solutions are classical there. If $\lambda_j>-1$, put $\nu_j=\sqrt{1+\lambda_j}>0$. Then
$f_j=A_jR^{-1+\nu_j}+B_jR^{-1-\nu_j}$.
Integrability at infinity first forces $A_j=0$. When $\nu_j\le1$ it also forces $B_j=0$, including the logarithmically divergent case $\nu_j=1$. When $\nu_j>1$, integrability at zero forces $B_j=0$. If $\lambda_j=-1$, the solutions are $R^{-1}(A_j+B_j\log R)$ and no nonzero solution is integrable at infinity with weight $R^3$. If $\lambda_j<-1$, the solutions are $R^{-1}(A_je^{i\tau_j\log R}+B_je^{-i\tau_j\log R})$, $\tau_j=\sqrt{-1-\lambda_j}$. For a nonzero pair the nonnegative squared oscillatory factor has a positive mean over its logarithmic period, so the weighted integral at infinity diverges. Thus $f_j=0$ for every $j$. Completeness of the angular basis, and the countability of that basis, give $F=0$ almost everywhere. This proves the intermediate at precisely the punctured local-regularity level obtained from the actual equation; no extension condition at $R=0$ was inserted.

Every subsequential limit extracted under (106.11) is therefore zero. The relative compactness in (106.16) on each compact set off zero implies strong local convergence of the entire subsequence there. Global weak convergence to zero follows by testing first on compact sets away from zero, whose $L^2$ functions are dense in global $L^2$, and using $\|F_n\|_2=1$.

It remains to handle the indices with $r_n<\ell_n$, without assuming (106.12) on those indices. A compact diagnostic set in (106.6) is contained in $|X|\le B$, $|t|\le B$ for some $B<\infty$. Its original image has central sections of length at most $2\kappa B r_n\le2\kappa B\ell_n$. The actual-state estimate (104.15), valid for arbitrary moving central sections, shows that its probability tends to zero. Thus on these indices $F_n\to0$ strongly on every compact set, including sets meeting zero, and hence weakly in global $L^2$. Combining the two sets of indices proves the zoom conclusions for every $r_n\to0$.

By the exact Jacobian in (106.6), the diagnostic annulus in (106.3) corresponds to $c<(|X|^2+t^2)^{1/2}<C$. Its closure is compact and avoids zero, proving (106.3). Conversely (106.3) for all fixed $c,C$ contains every compact set off zero in such an annulus, so it implies strong convergence there and then global weak convergence by density. The conserved norm excludes a globally strongly convergent subsequence.

Finally, if (106.4) failed, choose $\delta_j\downarrow0$, strictly increasing indices $n_j$ and $0<r_j\le\delta_j$ with annular masses bounded below by a fixed positive number. Apply (106.3) to that subsequence to obtain a contradiction. A failure of (106.5) similarly chooses orders $\sigma_j\to2$, actual states in $\mathcal Z_{\sigma_j}$ and $r_j\to0$ with a positive lower bound. Normalize those states to $V=1$ and apply the theorem, whose inputs and proof hold for every actual selection. This proves both uniform assertions in their stated order of limits. $\square$

**Corollary 106.3 (centered original Carnot zooms at arbitrary shrinking radii).** Under Definition 106.1, let $h_n>0$ be any sequence tending to zero. Use the original dilation $\delta_h(x,y,z,w)=(hx,hy,hz,h^2w)$ and set

$$
Z_n(q)=h_n^{5/2}v_n(\delta_{h_n}q),\qquad
\mathcal A=\{q:\xi(q)=0\}.
\tag{106.20}
$$

Then $\|Z_n\|_{L^2(G,d\mu)}=1$, $Z_n\rightharpoonup0$ in global $L^2(G,d\mu)$, and $Z_n\to0$ strongly in $L^2(K,d\mu)$ for every compact $K\subset G\setminus\mathcal A$. There is no globally strongly convergent subsequence. The exceptional set is explicitly the central line $x=y=z=0$; no strong conclusion on compact sets meeting that line is asserted at arbitrary radii.

**Proof.** The original Haar Jacobian of $\delta_h$ is $h^5$. In the original shear coordinate $s(\delta_hq)=h^2s(q)$, so

$$
R_\kappa(\delta_hq)
 =h\bigl(|\xi(q)|^2+h^2(s(q)/\kappa)^2\bigr)^{1/2}.
\tag{106.21}
$$

On each indicated compact $K$, $|\xi|$ has a strictly positive lower bound, while $|\xi|$ and $|s|$ are bounded above. Hence its image under $\delta_{h_n}$ lies in a diagnostic annulus $c h_n<R_\kappa<C h_n$ with fixed positive $c,C$. Equations (106.3) and (106.21) prove the strong local assertion. The line $\mathcal A$ has Haar measure zero, so compactly supported $L^2$ tests avoiding it are dense in global $L^2$. The norm bound gives global weak convergence to zero; norm one excludes global strong subsequences.

The radius quantifier here extends to every centered $h_n\to0$, but the local conclusion avoids $\mathcal A$. At $h_n=O(M_n^{1/4})$, Theorem 104.4 already gives the stronger conclusion on every compact set and after arbitrary moving translations. That result is reused as stated; this corollary neither extends its moving-center quantifier to larger radii nor supplies its full compact-set conclusion at arbitrary radii. $\square$

**Proposition 106.4 (annular vanishing alone does not remove a source atom).** The conclusions (106.3)–(106.5), considered as statements about probabilities and shrinking annuli, do not imply that a source defect is zero. In the same original chart let $\omega_3=|S^3|$ and define the absolutely continuous probability measures

$$
d\pi_j(p)=\frac{1}{\kappa\omega_3j}
 R_\kappa(p)^{-4}
 \mathbf1_{\{e^{-2j}<R_\kappa(p)<e^{-j}\}}d\mu(p),
 \qquad j=1,2,\ldots.
\tag{106.22}
$$

They converge narrowly to $\delta_e$, while for every $0<c<C<\infty$,

$$
\sup_{r>0}\pi_j\{cr<R_\kappa<Cr\}
 \le\frac{\log(C/c)}j\longrightarrow0.
\tag{106.23}
$$

**Proof.** The shear followed by $s=\kappa t$ gives $d\mu=\kappa\,d\xi dt$, so radial integration in four variables gives total mass $j^{-1}\int_{e^{-2j}}^{e^{-j}}dR/R=1$. An annulus intersects a logarithmic interval of length at most $\log(C/c)$, giving (106.23). The supports shrink to $e$ in the original topology, proving the narrow limit. These are measure examples only; they are not asserted to solve an actual critical equation or to realize any of its defects. Their role is the exact logical distinction between vanishing fixed-ratio annuli and exclusion of logarithmically spread source probability. $\square$

**Definition 106.5 (suppliers, correspondence and the remaining source problem).** The original field's marginal, positivity, homogeneity and Haar/shear conventions are the supplies of §§82–85, (102.2) and (103.8). Attainment and the actual full-complex equation are §§101.5 and 102.3. The endpoint and subexponential limits used in (106.12)–(106.14) are §103, not new mass or resource estimates. The varying-order localization estimate, its multiplier/domain justification and the actual short-central-section probability bound are (104.9) and (104.15). The exterior probability theorem §105 remains in force without a second proof.

Alvino–Ferone–Volpicelli, [*Sharp Hardy inequalities in the half space with trace remainder term*, arXiv:1105.0335v1, Theorem 1.1 and (8)](https://arxiv.org/abs/1105.0335v1), give the mature halfspace trace supply underlying §87 at $n=4$, $\beta_{\rm AFV}=2$: $H(4,2)=2/\pi$ per halfspace and $4/\pi$ on both. The primary theorem is for real functions; the complex extension and its actual-field comparison are the already supplied §87.2. Neither that theorem nor its nonattainment statement is used as an assertion about a maximal punctured domain. In (106.17) the same numerical coefficient is obtained directly from the original marginal and $g_c/(4\pi a\kappa)=4/\pi$. The angular spectral decomposition and its radial integrability proof above explicitly exclude all punctured local-$H^1$, global-$L^2$ solutions of this auxiliary limiting interface equation, rather than inferring that exclusion from the smaller closed trace form's zero kernel.

Closed-form representation and the compact self-adjoint spectral theorem are mature supplies, as in [Teschl, *Mathematical Methods in Quantum Mechanics*, authorized online edition, version February 12, 2009, Theorems 2.13 and 6.6](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf). Their client here is the angular form (106.18) on $L^2(S^3)$, with closedness, lower bound and compact embedding proved above. They do not identify any original singular operator domain. Ordinary one-dimensional trace estimates, Sobolev/Rellich compactness, spectral Hölder, Fourier dominated convergence, polar coordinates and the Euler equation are consumed intermediates inside the actual-state proof. The source-specific deduction is repository-derived: the exact diagnostic equation, uniform local control, its actual-to-interface limit, and the exclusion of every shrinking fixed-ratio probability annulus, with the directly consumed zoom consequences. No exhaustive literature-priority or world-originality assertion is attached to these deductions.

For the original maximal operator $S^*$ of (104.5), §§104–105 still yield exactly

$$
v\in\ker S^*,\qquad m_\infty=0,\qquad
\|v\|_2^2+m_e=1,\qquad
\ker S^*\cap\mathcal Q_c=\{0\}.
\tag{106.24}
$$

Theorem 106.2 does not determine $m_e$, prove triviality or existence of $\ker S^*$, or decide which maximal zero states or defects are attained by actual selections. Its auxiliary interface equation arises only after a shrinking diagnostic change of variables; its zero-space result is not a domain identification for $S^*$ or a replacement source law. The remaining obligations are a genuinely actual-state bound excluding or determining logarithmic source spreading, an original maximal-domain/attainability analysis, and a surviving probability scale or profile if one exists. No positivity, simplicity, uniqueness, native source-to-state realization or physical space-dimension conclusion follows. These are ordinary theoretical statements; they supply no Lean certification and do not complete the continuing why-three problem.

## 追加锚（本行以下为增补区）

## 107. Critical-form energy and an excluded actual source ball

**Definition 107.1 (unchanged source, actual states and the energy length).** Retain the original product
$pp'=(x+x',y+y',z+z',w+w'+xy')$ on $G=H^1\times\mathbb R$, identity $e$, Lebesgue Haar measure $d\mu=dx\,dy\,dz\,dw$, and
$X_1=\partial_x$, $X_2=\partial_y+x\partial_w$, $X_3=\partial_z$.
The nonnegative free realization is $L=-\sum_iX_i^2$, its clock is $e^{-tL}$, and $\Gamma=\int_0^\infty h_t\,dt$ is its original positive degree-$-3$ unit-source Green field, $L\Gamma=\delta_e$. Fix the original $a,\eta>0$ and central coordinate and spectral units. With $D_w=-i\partial_w$, use exactly the full complex spaces and functionals of (103.2):
$\mathcal E_\nu=D(L^{1/2})\cap D(|D_w|^{\nu/2})$,
$T[u]=\sum_i\|X_iu\|_2^2$, $D_\nu[u]=\||D_w|^{\nu/2}u\|_2^2$ and
$V[u]=\int\Gamma|u|^2d\mu$.
Write

$$
\begin{gathered}
g_\sigma=\inf_{0\ne u\in\mathcal E_\sigma}
 \frac{aT[u]+\eta D_\sigma[u]}{V[u]},\qquad
g_c=16\sqrt{a\eta},\\
q_c[u]=aT[u]+\eta D_2[u]-g_cV[u]\quad(u\in\mathcal E_2),\\
\kappa=\sqrt{\eta/a},\qquad \xi=(x,y,z),\qquad s=w-xy/2,\qquad
R_\kappa=\bigl(|\xi|^2+(s/\kappa)^2\bigr)^{1/2}.
\end{gathered}
\tag{107.1}
$$

The nonnegative closed form $\overline q_c$ on $\mathcal Q_c$ is the critical Friedrichs form of §87.4, with norm squared $\|u\|_2^2+\overline q_c[u]$; it equals $q_c$ on $\mathcal E_2$. The diagnostic $R_\kappa$ changes neither the original product nor the source.

For every sequence $\sigma_n>2$ tending to $2$, without monotonicity, select any nonzero attained critical zero states in the original complex $\mathcal E_{\sigma_n}$, and rescale only amplitudes so that $V[u_n]=1$. Attainment and their full-domain equation are those of §§101.5 and 102.3, equivalently (103.3). Put

$$
\begin{gathered}
M_n=\|u_n\|_2^2>0,\qquad
v_n=M_n^{-1/2}u_n,\qquad \|v_n\|_2=1,\qquad
\ell_n=\sqrt{M_n},\\
\delta_n=q_c[u_n],\qquad
E_n=q_c[v_n]=\delta_n/M_n,\qquad
\epsilon_n=\sigma_n-2,\qquad g_n=g_{\sigma_n}.
\end{gathered}
\tag{107.2}
$$

All limits below concern every such actual selection on the fixed Hilbert space $L^2(G,d\mu)$. There is no assumption on sign, positivity, simplicity, uniqueness or a chosen profile.

**Lemma 107.2 (closed trace concentration and its exact original marginal consumer).** Let $\Phi$, $\mathcal Q_\delta$ and $\mathfrak t$ be exactly the auxiliary profile, closed domain and form of (87.6)–(87.8). Thus, writing $r=|\xi|$ and $\varrho=(r^2+t^2)^{1/2}$ in the auxiliary $\mathbb R^4$,

$$
\begin{gathered}
\Phi(\xi,t)=\frac2{\pi r}\arctan\frac r{|t|},\qquad
\Phi(\xi,0)=r^{-1},\qquad \Phi(0,t)=\frac2{\pi|t|},\qquad
\frac2{\pi\varrho}\le\Phi\le\frac1\varrho,\\
\mathfrak t[f]=\int_{\mathbb R^4}\Phi^2|\nabla(f/\Phi)|^2\,d\xi\,dt
 \quad(f\in\mathcal Q_\delta).
\end{gathered}
\tag{107.3}
$$

The domain is the closure of $C_c^\infty(\mathbb R^4\setminus\{0\};\mathbb C)$ for the norm squared $\|f\|_2^2+\mathfrak t[f]$ specified in §87. For every complex $f$ in this whole domain and every $b>0$,

$$
\int_{\mathbb R^4}\frac{|f|^2}{|\xi|}\,d\xi\,dt
 \le\pi^2\|f\|_2\sqrt{\mathfrak t[f]},
\qquad
\int_{\{|\xi|<b\}}|f|^2\,d\xi\,dt
 \le\pi^2 b\|f\|_2\sqrt{\mathfrak t[f]}.
\tag{107.4}
$$

Consequently every $\psi\in\mathcal Q_c$, including its singular elements outside $\mathcal E_2$, satisfies the original-space bounds

$$
\int_G\frac{|\psi|^2}{|\xi|}\,d\mu
 \le\frac{\pi^2}{\sqrt a}\|\psi\|_2\sqrt{\overline q_c[\psi]},
\qquad
\int_{\{|\xi|<b\}}|\psi|^2\,d\mu
 \le\frac{\pi^2b}{\sqrt a}\|\psi\|_2\sqrt{\overline q_c[\psi]}.
\tag{107.5}
$$

The constant is a sufficient constant, with no sharpness assertion.

**Proof.** First take $f$ in the punctured smooth core and put $g=f/\Phi$, $W=\varrho^{-2}$. On its support $g$ is bounded and locally $H^1$, also across $t=0$, because $\Phi$ is positive and locally Lipschitz away from the origin. For $r>0$ introduce the bounded real vector field

$$
F(\xi,t)=\frac{(\xi,t)}{\varrho}+\left(\frac{\xi}{r},0\right),
\qquad |F|\le2.
$$

A direct divergence calculation in four Euclidean variables gives

$$
\begin{aligned}
\operatorname{div}(WF)
 &=\frac W\varrho+\frac{2Wt^2}{r\varrho^2}\\
 &=\frac Wr\left[u+2(1-u^2)\right]\ge\frac Wr,
 \qquad u=\frac r\varrho\in[0,1].
\end{aligned}
\tag{107.6}
$$

Indeed $u+2(1-u^2)-1=(1-u)(2u+1)\ge0$. The integration by parts against $|g|^2$ is valid on $r>\tau$, followed by $\tau\downarrow0$. The support is compact and avoids the origin; on its intersection with $r=\tau$ the weight and $g$ are uniformly bounded for small $\tau$. The cylindrical boundary flux is therefore $O(\tau^2)$ and tends to zero. The divergence is locally integrable across that axis on this support. There is no interface boundary term: $g$ is a single $H^1$ function across $t=0$, and $WF$ is smooth there when $r>0$. It follows that

$$
\begin{aligned}
\int\frac W r|g|^2
 &\le\int\operatorname{div}(WF)|g|^2
 =-2\operatorname{Re}\int W\overline g\,F\cdot\nabla g\\
 &\le4\left(\int W|g|^2\right)^{1/2}
       \left(\int W|\nabla g|^2\right)^{1/2}.
\end{aligned}
\tag{107.7}
$$

Since $\Phi^2\le W\le(\pi^2/4)\Phi^2$, the left side dominates $\int |f|^2/r$, whereas the last line is at most $\pi^2\|f\|_2\sqrt{\mathfrak t[f]}$. This proves the first inequality of (107.4) on the core with the real part required for arbitrary complex $f$. For any $f\in\mathcal Q_\delta$, choose core approximants converging in the closed form norm. Their $L^2$ norms and form values converge. An almost everywhere convergent subsequence and Fatou's lemma give the first inequality on all of $\mathcal Q_\delta$. The second follows from $1\le b/r$ on $0<r<b$. In particular the proof requires no separate finiteness of the gradient and trace terms whose difference defines the core form.

The auxiliary homogeneity is exact on this closure. For $\lambda>0$, set
$\mathscr D_\lambda f(\xi,t)=\lambda^2 f(\lambda\xi,\lambda t)$.
The profile has degree $-1$, so the change of variables in (107.3) yields, first on the core,

$$
\|\mathscr D_\lambda f\|_2=\|f\|_2,\qquad
\mathfrak t[\mathscr D_\lambda f]=\lambda^2\mathfrak t[f],\qquad
\int\frac{|\mathscr D_\lambda f|^2}{r}
 =\lambda\int\frac{|f|^2}{r}.
\tag{107.8}
$$

Core approximation and the inverse $\mathscr D_{1/\lambda}$ extend the domain invariance and form identity to $\mathcal Q_\delta$; the weighted integral identity follows directly by change of variables. Both sides of the first inequality in (107.4) scale by $\lambda$; its cylinder bound at radius $b$ for $\mathscr D_\lambda f$ is the bound at radius $\lambda b$ for $f$. These auxiliary Euclidean dilations are not asserted to dilate the original source law.

To pass to the actual original space, use only the established forward map (87.26). In shear coordinates set $\Psi(\xi,s)=\psi(\xi,s+xy/2)$ and let $b_\psi=\mathcal F_s\Psi$ be the unitary central transform. Define on every $L^2$ state

$$
\mathcal M\psi(\xi,t)=
 \kappa^{1/2}\bigl(\mathcal F_s^{-1}|b_\psi|\bigr)(\xi,\kappa t).
$$

For every Borel $A\subset\mathbb R^3$, fibrewise Plancherel, Tonelli's theorem and $dw=ds$ give the exact identity

$$
\begin{aligned}
\int_{A\times\mathbb R}|\mathcal M\psi(\xi,t)|^2d\xi\,dt
 &=\int_{A\times\mathbb R}|b_\psi(\xi,\lambda)|^2d\xi\,d\lambda\\
 &=\int_{\{p\in G:\xi(p)\in A\}}|\psi(p)|^2d\mu(p).
\end{aligned}
\tag{107.9}
$$

This is a marginal identity for all complex $L^2$ states; it makes no pointwise density identification in the central variable. It also holds with any nonnegative measurable function of $\xi$ as multiplier, by simple-function approximation.

The norm-preserving map $\mathcal M$ is $L^2$-Lipschitz because the modulus is a contraction before inverse Fourier transformation. On the original punctured core (87.27) gives $\mathfrak t[\mathcal M\psi]\le q_c[\psi]/a$. Its constants are unchanged: if $U=\mathcal F_s^{-1}|b_\psi|$, then $A[\mathcal M\psi]=A[U]\le T[\psi]$, $C[\mathcal M\psi]=\kappa^2D_2[\psi]$, $J[\mathcal M\psi]=\kappa J[U]$, and the actual source bound is $V[\psi]\le J[U]/(4\pi)$. Here $A$, $C$ and $J$ are precisely (87.5), while $a\kappa^2=\eta$ and $g_c/(4\pi)=4a\kappa/\pi$. For a $\mathcal Q_c$ core approximating sequence, its images therefore converge in $L^2$ with bounded $\mathfrak t$ values. Lower semicontinuity of the nonnegative closed form, extended by $+\infty$ outside $\mathcal Q_\delta$, gives exactly the whole-closure comparison (87.28):
$\mathcal M\psi\in\mathcal Q_\delta$ and
$\mathfrak t[\mathcal M\psi]\le\overline q_c[\psi]/a$.
This uses no estimate on differences of the images in the form norm. Apply (107.4) to this image, then (107.9) with multiplier $1/r$ and with $A=\{r<b\}$. Norm preservation proves (107.5), without an inverse map or an original-domain identification. $\square$

**Theorem 107.3 (divergent critical energy and exclusion at its own length).** For every actual selection of Definition 107.1, $\delta_n>0$ for every $n$, so that the energy length

$$
h_n=\sqrt{a/E_n}
\tag{107.10}
$$

is well-defined. The following limits all hold:

$$
\begin{gathered}
\delta_n\longrightarrow0,\qquad
E_n\longrightarrow+\infty,\qquad
\frac{M_n}{g_{\sigma_n}-g_c}\longrightarrow0,\\
h_n\longrightarrow0,\qquad
\frac{h_n}{\ell_n}\longrightarrow+\infty,\\
\text{for every fixed }C>0,\qquad
\int_{\{R_\kappa<C h_n\}}|v_n|^2d\mu\longrightarrow0.
\end{gathered}
\tag{107.11}
$$

The threshold-gap ratio is taken on its eventual positive denominator. In addition, the estimate consumed in the last assertion is, for every $n$ and every $b>0$,

$$
\int_{\{|\xi|<b\}}|v_n|^2d\mu\le\pi^2\,b/h_n.
\tag{107.12}
$$

**Proof.** The inclusion $\mathcal E_{\sigma_n}\subset\mathcal E_2\subset\mathcal Q_c$ follows from $|\lambda|^2\le1+|\lambda|^{\sigma_n}$. Since $u_n\ne0$, the zero-kernel assertion (87.19) for the whole critical closed form gives $\delta_n>0$. Its limit zero and $M_n\to0$ are the existing actual-state limits (103.6). Equation (107.5), applied to $v_n$ of norm one and form value $E_n$, gives (107.12).

Suppose $E_n$ did not tend to infinity. Along a subsequence it would be bounded by a fixed $B>0$, so the $v_n$ would be bounded in the Hilbert space $\mathcal Q_c$. Take a further weak subsequence there. Its weak $L^2$ limit is the same vector $v\in\mathcal Q_c$. Theorem 104.2, after further extraction if necessary, puts this same actual weak profile in $\mathcal N_0=\ker S^*$, where $S$ is exactly (104.5). Thus (104.6) forces $v=0$. Equation (105.3) now gives, for every fixed $b>0$,

$$
\int_{\{R_\kappa\ge b\}}|v_n|^2d\mu\longrightarrow0.
$$

The indicator of this exterior is a legitimate bounded measurable cutoff vanishing near $e$. Since $\{R_\kappa<b\}\subset\{|\xi|<b\}$, (107.5) gives along this subsequence

$$
1\le\frac{\pi^2b}{\sqrt a}\sqrt B+o(1).
\tag{107.13}
$$

Choosing a fixed $0<b<\sqrt a/(2\pi^2\sqrt B)$ is a contradiction. Hence $E_n\to+\infty$. This step uses exterior strong convergence and the intersection $\mathcal N_0\cap\mathcal Q_c=\{0\}$, without identifying the maximal and Friedrichs domains.

For the threshold-gap comparison, test the original full-domain equation (103.3) with $u_n$ itself. It gives the exact same-state identity

$$
\delta_n=(g_n-g_c)+\eta\bigl(D_2[u_n]-D_{\sigma_n}[u_n]\bigr).
\tag{107.14}
$$

For $\epsilon>0$ and $x\ge0$, the difference $x^2-x^{2+\epsilon}$ is nonpositive when $x\ge1$, while for $0<x<1$,

$$
x^2(1-x^\epsilon)\le-\epsilon x^2\log x
 \le\frac{\epsilon}{2\mathrm e}.
$$

The last bound follows by maximizing $-x^2\log x$ on $(0,1)$; at $x=0$ the difference is zero. Plancherel with the original fixed central units therefore gives

$$
D_2[u_n]-D_{\sigma_n}[u_n]\le
 \frac{\epsilon_n}{2\mathrm e}M_n,\qquad
\frac{g_n-g_c}{M_n}
 \ge E_n-\frac{\eta\epsilon_n}{2\mathrm e}\longrightarrow+\infty.
\tag{107.15}
$$

The denominator $g_n-g_c$ is consequently positive eventually, and its stated reciprocal ratio tends to zero. Both central moments in (107.14) are finite on the original $\mathcal E_{\sigma_n}$; no order comparison between those moments is presumed. The two length limits follow from $E_n\to\infty$ and the exact identity

$$
\frac{h_n}{\ell_n}=\sqrt{\frac a{\delta_n}}\longrightarrow+\infty.
\tag{107.16}
$$

Finally fix $C>0$ and then any $0<c<C$. Since $h_n\to0$, the actual annular exclusion (106.3), with $r_n=h_n$, gives

$$
\int_{\{c h_n<R_\kappa<C h_n\}}|v_n|^2d\mu\longrightarrow0.
$$

The inner diagnostic ball is contained in $|\xi|<c h_n$, so (107.12) bounds its probability by $\pi^2c$. Diagnostic spheres have Haar measure zero, since in $(\xi,s/\kappa)$ they are Euclidean spheres and $d\mu=\kappa\,d\xi\,d(s/\kappa)$. It follows that

$$
0\le\limsup_{n\to\infty}
 \int_{\{R_\kappa<C h_n\}}|v_n|^2d\mu\le\pi^2c.
\tag{107.17}
$$

Letting $c\downarrow0$ proves the last assertion of (107.11). Every step applies to arbitrary actual selections and to approach from above without monotonicity. $\square$

**Definition 107.4 (mathematical correspondence and remaining limits).** The original model, source normalization and full-complex actual equation are those of §§82–87 and §§101–103. The closure and forward comparison used here are precisely (87.6)–(87.8) and (87.26)–(87.28). The actual-state consumers are (103.3), (103.6), (104.6), exterior strong convergence (105.3), and the arbitrary shrinking annuli (106.3). The proof of Lemma 107.2 supplies the additional weighted divergence estimate on the whole closed trace form; (107.9) is the exact horizontal marginal, rather than an inverse auxiliary correspondence.

Alvino–Ferone–Volpicelli, [*Sharp Hardy inequalities in the half space with trace remainder term*, arXiv:1105.0335v1, Theorem 1.1 and (8), (12)](https://arxiv.org/abs/1105.0335v1), supply the trace intermediate already consumed in §87. At $n=4$, $\beta_{\rm AFV}=2$, the bulk Hardy term vanishes and (8) gives $H(4,2)=2/\pi$ per halfspace, hence $4/\pi$ for the two halfspaces. Formula (12) becomes $\int_0^\infty((a+t)^2+r^2)^{-1}da=r^{-1}\arctan(r/t)$ for $t>0$; boundary normalization by $2/\pi$ and even reflection give exactly (107.3). The primary theorem concerns real functions; the complex ground-state representation and closed-form comparison are the established §87 supplies, and the real-part argument and closure passage in (107.7) prove the additional estimate for the full complex domain.

Kalaman–Yessirkegenov, [*Cylindrical Hardy, Sobolev type and Caffarelli–Kohn–Nirenberg type inequalities and identities*, arXiv:2407.08393v1, §3.1, Theorem 2(i), (3.1)](https://arxiv.org/abs/2407.08393v1), give a complex cylindrical Hardy inequality on $C_c^\infty(\mathbb R^n\setminus\{x'=0\})$. With $n=4$, $k=3$, $p=2$, $\alpha=2$, $x'=\xi$ and $x''=t$, it reads
$\frac14\int |f|^2/r^2\le\int|\xi\cdot\nabla_\xi f|^2/r^2\le\int|\nabla_\xi f|^2$
on that test domain. This identifies the overlap in cylindrical divergence methods. That theorem supplies no bound by the critical form after trace subtraction, nor an extension to $\mathcal Q_\delta$ or an actual-state assertion. Those passages are proved in (107.6)–(107.9), so its test-domain estimate is not used in place of them. The new source-specific conclusion is the actual-state theorem (107.11), deduced using the stated existing supplies; there is no exhaustive literature-priority claim.

The energy length is an excluded source-ball scale. It is not a proved surviving scale or a probability profile. In every subsequential decomposition of §§104–105 the only asserted defect identity remains

$$
v\in\mathcal N_0,\qquad m_\infty=0,\qquad
\|v\|_2^2+m_e=1,\qquad \mathcal N_0\cap\mathcal Q_c=\{0\}.
\tag{107.18}
$$

Neither $m_e=0$, $m_e=1$ nor a strictly intermediate value is selected. Cumulative source probability at radii large compared with $h_n$, existence and dimension of nonzero $\mathcal N_0$, actual attainability of its profiles and defects, and any surviving probability scale or profile remain unresolved. No positivity, simplicity, uniqueness, new source boundary condition or maximal/Friedrichs identification is imposed. No native source-to-state realization or physical why-three conclusion follows. These ordinary mathematical proofs make no claim of Lean verification.

## 追加锚（本行以下为增补区）

## 108. A necessary source germ for every original maximal zero mode

**Definition 108.1 (original critical operator and source annuli).** Retain the group, Lebesgue Haar measure, unit-source field, horizontal generator and clock of (82.5), (82.8) and (107.1). Thus $G=H^1\times\mathbb R$, $d\mu=dx\,dy\,dz\,dw$, $L=-\sum_{i=1}^3X_i^2$, with $X_1=\partial_x$, $X_2=\partial_y+x\partial_w$, $X_3=\partial_z$, and $\Gamma$ is the original positive degree-$-3$ field satisfying $L\Gamma=\delta_e$. Fix the same $a,\eta>0$, central units, $D_w=-i\partial_w$ and $g_c=16\sqrt{a\eta}$. The spaces and forms are precisely those of §§87.1, 87.4 and 104.2:

$$
\begin{gathered}
\mathcal E_2=D(L^{1/2})\cap D(D_w),\qquad
K[u]=aT[u]+\eta D_2[u],\qquad
q_c[u]=K[u]-g_cV[u]\quad(u\in\mathcal E_2),\\
S\phi=(aL+\eta D_w^2-g_c\Gamma)\phi,
\qquad D(S)=\mathcal D_0=C_c^\infty(G\setminus\{e\};\mathbb C),
\qquad \mathcal N_0=\ker S^*.
\end{gathered}
\tag{108.1}
$$

Write $\overline q_c$ for the nonnegative Friedrichs closure of the core form, with domain $\mathcal Q_c$. In particular $\mathcal E_2\subset\mathcal Q_c$, the two forms agree on $\mathcal E_2$, and $\mathcal N_0\cap\mathcal Q_c=\{0\}$ by (104.6). These are existing supplies, not an identification of the maximal and Friedrichs domains. Put

$$
\kappa=\sqrt{\eta/a},\qquad \xi=(x,y,z),\qquad
s=w-xy/2,\qquad t=s/\kappa,\qquad
R_\kappa=(|\xi|^2+t^2)^{1/2},\qquad
A_{c,C}(r)=\{p:cr<R_\kappa(p)<Cr\}.
\tag{108.2}
$$

All zero modes and form domains are complex. The diagnostic annuli in (108.2) are in the original space; no change of source, measure or differential operator is made.

**Theorem 108.2 (every nonzero maximal zero mode has a divergent annular germ).** For every $v\in\mathcal N_0\setminus\{0\}$ and every fixed $0<c<C<\infty$,

$$
\lim_{r\downarrow0}\frac1{r^2}
 \int_{A_{c,C}(r)}|v|^2\,d\mu=+\infty.
\tag{108.3}
$$

Equivalently, if a vector $v\in\mathcal N_0$ has a finite lower limit in (108.3) for even one such pair $c,C$, it is zero. The limit is for each fixed vector and pair; no uniform rate over nonzero zero modes is asserted.

**Proof.** First justify the original exterior-domain statement needed to use a source cutoff. By the definition of $S^*$, $v$ solves $(aL+\eta D_w^2-g_c\Gamma)v=0$ distributionally on $G\setminus\{e\}$. The principal symbol of its free part, in the original chart, is

$$
a\bigl(\zeta_x^2+(\zeta_y+x\zeta_w)^2+\zeta_z^2\bigr)
 +\eta\zeta_w^2.
\tag{108.4}
$$

It is bounded below by a positive multiple of $|\zeta|^2$ on each compact coordinate set. The coefficients and $\Gamma$ are smooth off $e$. Local distributional elliptic regularity therefore gives $v\in H^2_{\mathrm{loc}}(G\setminus\{e\})$. This is the local regularity supply in Shubin, [*Essential self-adjointness for semi-bounded magnetic Schrödinger operators on non-compact manifolds*, arXiv:math/0007019v1, §5.1, Lemma 5.1](https://arxiv.org/html/math/0007019v1). Its correspondence here uses the smooth dual metric with squared covector norm (108.4), zero magnetic one-form, the same smooth positive measure $d\mu$, and potential $-g_c\Gamma$, which is locally bounded on the punctured manifold. All $X_i$ and $\partial_w$ have zero divergence for $d\mu$, so its free differential expression is exactly $aL+\eta D_w^2$. Only the local lemma is used; no completeness or essential self-adjointness assertion on the punctured space is required.

For a real smooth function $f$, denote its cutoff cost by

$$
\mathcal C[f]=a\sum_i|X_if|^2+\eta|\partial_wf|^2.
\tag{108.5}
$$

If $f\in C_c^\infty(G\setminus\{e\};\mathbb R)$, then $fv\in\mathcal E_2$. The weak equation can be tested with $f^2v$: on its compact support the coefficients and potential are bounded and $v\in H^1$, so compact smooth approximation extends the equation to this test. Expanding the product derivatives and taking real parts gives the exact identity

$$
q_c[fv]=\int_G\mathcal C[f]|v|^2\,d\mu.
\tag{108.6}
$$

All integrals in this step are on a compact set separated from $e$. The same approximation puts $fv$ in the core-form closure and agrees with the finite-integral form. This is the usual complex cutoff identity, corresponding to Shubin's §5.1, (5.2)–(5.3); the real part handles arbitrary complex $v$.

Now let $\zeta\in C^\infty(G;[0,1])$ vanish on a neighborhood of $e$ and have compactly supported differential. It need not have compact support. Choose a fixed $\chi\in C_c^\infty(G;[0,1])$ equal to one near $e$, and set $\chi_H=\chi\circ\delta_{1/H}$, where $\delta_H$ is the original Carnot dilation and $H\to\infty$. Homogeneity of the original vector fields gives

$$
\|X_i\chi_H\|_\infty\le C H^{-1},\qquad
\|\partial_w\chi_H\|_\infty\le C H^{-2},\qquad
\|\mathcal C[\chi_H]\|_\infty\le C(aH^{-2}+\eta H^{-4}).
\tag{108.7}
$$

For all sufficiently large $H$, $\chi_H=1$ on the compact support of $d\zeta$. Thus the two cutoff differentials have disjoint supports. Apply (108.6) with $f=\zeta\chi_H$ to obtain

$$
q_c[\zeta\chi_Hv]
 =\int_G\mathcal C[\zeta]|v|^2\,d\mu
  +\int_G\zeta^2\mathcal C[\chi_H]|v|^2\,d\mu.
\tag{108.8}
$$

The first integral is finite because its coefficient is bounded and compactly supported. Also $\Gamma$ is bounded on the complement of any neighborhood of $e$: the original homogeneous estimate $\Gamma\le B_\Gamma\rho^{-3}$, with $\rho=(|\xi|^4+s^2)^{1/4}$, gives decay at infinity, and smoothness gives the remaining compact bound. Hence $V[\zeta\chi_Hv]\le B_\zeta\|v\|_2^2$. Since $K=q_c+g_cV$ on $\mathcal E_2$, (108.7)–(108.8) bound $K[\zeta\chi_Hv]$ uniformly for large $H$.

On each compact set $\chi_H$ is identically one for all sufficiently large $H$. Exhausting $G$ by compact sets in this kinetic bound shows that the distributional derivatives $X_i(\zeta v)$ and $\partial_w(\zeta v)$ are globally square integrable. The free domain characterization (84.2) and the ordinary central Sobolev characterization therefore give $\zeta v\in\mathcal E_2$. The product rule now proves $\chi_H\zeta v\to\zeta v$ in $\mathcal E_2$: terms with $\chi_H-1$ tend to zero by dominated convergence against these square-integrable derivatives, and terms with a derivative of $\chi_H$ tend to zero by (108.7) and $v\in L^2$. The potential terms converge as well because $\Gamma$ is bounded where $\zeta\ne0$. Passing to the limit in (108.8) consequently proves the needed exterior identity

$$
\zeta v\in\mathcal E_2\subset\mathcal Q_c,\qquad
\overline q_c[\zeta v]=q_c[\zeta v]
 =\int_G\mathcal C[\zeta]|v|^2\,d\mu.
\tag{108.9}
$$

This passage uses no global finiteness of the uncut kinetic or potential integrals of $v$, and no assertion that $\Gamma v\in L^2$.

Fix $c,C$ as in the theorem. Choose a real $\theta\in C^\infty([0,\infty);[0,1])$ equal to zero for $u\le c$ and to one for $u\ge C$, with $\operatorname{supp}\theta'\subset(c,C)$, and put $\zeta_r=\theta(R_\kappa/r)$. This is a smooth exterior cutoff of the kind just treated. The original fields in the $(\xi,t)$ chart are
$X_1=\partial_x-y\partial_t/(2\kappa)$, $X_2=\partial_y+x\partial_t/(2\kappa)$, $X_3=\partial_z$, and $\partial_w=\kappa^{-1}\partial_t$. Therefore, at $R_\kappa>0$, using $\eta/\kappa^2=a$,

$$
\mathcal C[R_\kappa]
 =a\left(1+\frac{(x^2+y^2)t^2}{4\kappa^2R_\kappa^2}\right)
 \le a\left(1+\frac{R_\kappa^2}{4\kappa^2}\right).
\tag{108.10}
$$

The chain rule and (108.9) give, for $0<r\le1$,

$$
0\le\overline q_c[\zeta_rv]
 \le\frac{B_{c,C}}{r^2}\int_{A_{c,C}(r)}|v|^2\,d\mu,
\qquad
B_{c,C}=a\|\theta'\|_\infty^2
       \left(1+\frac{C^2}{4\kappa^2}\right)<\infty.
\tag{108.11}
$$

Suppose the annular ratio in (108.3) were bounded along some sequence $r_j\downarrow0$. Equation (108.11) and $\|\zeta_{r_j}v\|_2\le\|v\|_2$ would bound $\zeta_{r_j}v$ in the Hilbert space $\mathcal Q_c$, equipped with norm squared $\|\cdot\|_2^2+\overline q_c[\cdot]$. Take a weakly convergent subsequence in that space. Its continuous inclusion into $L^2$ sends this subsequence to its weak $L^2$ limit. But dominated convergence gives $\zeta_{r_j}v\to v$ strongly in $L^2$, since $\zeta_{r_j}\to1$ off the Haar-null point $e$. The weak form-space limit is consequently the vector $v$, so $v\in\mathcal Q_c$. Since also $v\in\mathcal N_0$, (104.6) forces $v=0$.

For a nonzero $v$, no sequence approaching zero can thus have bounded annular ratio. The nonnegative ratio must tend to $+\infty$, which proves (108.3). In particular the argument uses boundedness in the complete form norm and weak compactness, not a Cauchy claim about shrinking source cutoffs. It imposes no sign or symmetry on $v$. $\square$

**Corollary 108.3 (necessary germ of an attained subsequential weak profile).** Let $\sigma_n>2$ tend to $2$, and choose any nonzero attained critical zero states in the original full complex $\mathcal E_{\sigma_n}$ as in Definition 107.1. Normalize amplitudes by $V[u_n]=1$, put $M_n=\|u_n\|_2^2$ and $v_n=u_n/\sqrt{M_n}$, so $\|v_n\|_2=1$. Along any common subsequence furnished by §§104–105, use exactly their state and probability limits:

$$
v_n\rightharpoonup v\text{ in }L^2(G,d\mu),\qquad
|v_n|^2d\mu\longrightarrow|v|^2d\mu+m_e\delta_e,
\qquad v\in\mathcal N_0,\qquad \|v\|_2^2=1-m_e.
\tag{108.12}
$$

The measure convergence here is on the one-point compactification, and its infinity coefficient is zero by §105. If $m_e<1$, the normalized nonzero profile $w=v/\sqrt{1-m_e}$ belongs to $\mathcal N_0$, has norm one, and for every fixed $0<c<C<\infty$,

$$
\lim_{r\downarrow0}r^{-2}\int_{A_{c,C}(r)}|v|^2\,d\mu
 =\lim_{r\downarrow0}r^{-2}\int_{A_{c,C}(r)}|w|^2\,d\mu
 =+\infty.
\tag{108.13}
$$

Conversely, if the weak profile in (108.12) has finite lower limit of this annular ratio for one pair $c,C$, then $v=0$ and $m_e=1$.

**Proof.** The identity $\|v\|_2^2=1-m_e$ in the already established defect representation makes $v$ nonzero exactly when $m_e<1$. The space $\mathcal N_0$ is complex linear. Apply Theorem 108.2 to $v$ and to its positive scalar normalization $w$. Its equivalent zero criterion proves the converse, after which the same defect identity gives $m_e=1$. No resource measure, shrinking-scale limit of $v_n$, or new existence or attainability assertion enters this implication. $\square$

**Definition 108.4 (supplier correspondence and unresolved alternatives).** The free distributional domain used in (108.9) is (84.2), the punctured free-core density and inclusion $\mathcal E_2\subset\mathcal Q_c$ are §§87.1 and 87.4, and the maximal/Friedrichs intersection and actual defect representation are (104.6) and (105.2). The local regularity and compact cutoff identity are the mature intermediate supplies identified with Shubin's Lemma 5.1 and (5.3) above. His global self-adjointness theorems are not applied to the puncture. The closed form Hilbert-space construction is the one in Teschl, [*Mathematical Methods in Quantum Mechanics*, §2.3, (2.45)–(2.47), Theorems 2.12–2.13](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), already used in §87.4; continuous inclusion and Hilbert weak compactness give the bounded-cutoff passage here. These suppliers neither replace $\Gamma$ nor identify $D(S^*)$ with $\mathcal Q_c$. The original exterior passage (108.7)–(108.9), diagnostic cutoff cost (108.10) and their source-germ consequence (108.3) give the deduction for this fixed operator; no general cutoff or elliptic regularity theorem is proposed as a new result.

Theorem 108.2 is a necessary condition for nonzero elements of the original maximal zero space. It does not prove that this space is nonzero, determine its dimension or classify its elements. Corollary 108.3 does not construct a nonzero actual weak profile, determine $m_e$, or show that any prescribed zero mode or defect is attained. The ratio in (108.3) is a germ of a fixed limiting vector; it is not a joint limit in $n,r$, a cumulative probability bound for the actual sequence, or a surviving scale. In particular the excluded length $h_n$ of §107 is not turned into a surviving length. Existence and dimension of $\mathcal N_0$, actual profile attainability, source-atom selection, cumulative actual probability and surviving scales remain unresolved. Neither a new source boundary condition nor a native or physical spatial-dimension conclusion is obtained.

## 追加锚（本行以下为增补区）

## 109. One source coefficient for the entire original maximal zero space

**Definition 109.1 (fixed original domains and a linear diagnostic).** Retain exactly (108.1): the original $G=H^1\times\mathbb R$, raw Lebesgue Haar measure, unit-source $L$-Green field $\Gamma$, horizontal operator and clock, fixed $a,\eta>0$, original central units, punctured complex core $D(S)=\mathcal D_0$, maximal zero space $\mathcal N_0=\ker S^*$, and Friedrichs form $(\overline q_c,\mathcal Q_c)$. In particular $g_c=16\sqrt{a\eta}$ and $\mathcal N_0\cap\mathcal Q_c=\{0\}$ are the supplies of §§87 and 104. Write

$$
\kappa=\sqrt{\eta/a},\qquad s=w-xy/2,\qquad t=s/\kappa,
\qquad Z=(\xi,t),\qquad R=|Z|,
\qquad \mathcal G(\xi,s)=\Gamma(\xi,s+xy/2).
\tag{109.1}
$$

For an original vector $v$, the following is a linear unitary coordinate map, followed by a local radial conjugation:

$$
f_v(\xi,t)=\kappa^{1/2}v(x,y,z,\kappa t+xy/2),\qquad
H_v(\tau,\omega)=e^{-\tau}f_v(e^{-\tau}\omega),
\qquad \tau=-\log R,\quad \omega\in S^3.
\tag{109.2}
$$

Thus $f_v(R\omega)=R^{-1}H_v(-\log R,\omega)$ and
$\int_{R<e^{-T}}|f_v|^2dZ=\int_T^\infty e^{-2\tau}\|H_v(\tau)\|_{L^2(S^3)}^2d\tau$. These are coordinates and a diagnostic conjugation of the original equation; they introduce neither a new source nor an extension condition.

Let $\mathfrak a$ be exactly the auxiliary angular form (106.18), on $H^1(S^3;\mathbb C)$, and let $B$ represent $\mathfrak b=\mathfrak a+\langle\cdot,\cdot\rangle$. Define the fixed real unit vector

$$
e_0=\frac{\Phi|_{S^3}}{\|\Phi|_{S^3}\|_2},
\qquad
\Phi(\xi,t)=\frac2{\pi|\xi|}\arctan\frac{|\xi|}{|t|},
\tag{109.3}
$$

with the continuous values in (87.6). The choice in (109.3) normalizes an auxiliary angular coordinate, not the phase, sign or symmetry of an original state.

**Theorem 109.2 (original maximal rank and its source coefficient).** For every fixed original $a,\eta>0$ there are complex-linear coefficient maps $A,B_\mathrm{src}:\mathcal N_0\to\mathbb C$ such that every $v\in\mathcal N_0$ has, for all sufficiently large $T$,

$$
H_v(\tau,\omega)
 =\bigl(A(v)+\tau B_\mathrm{src}(v)\bigr)e_0(\omega)+Z_v(\tau,\omega),
\qquad
 e^{\tau/8}Z_v\in H^1((T,\infty)\times S^3).
\tag{109.4}
$$

The maps and the remainder are defined on all complex maximal zero modes. The coefficient $B_\mathrm{src}$ is injective. Consequently

$$
\dim_{\mathbb C}\mathcal N_0\le1.
\tag{109.5}
$$

In particular no existence, positivity, reality, parity or Friedrichs-domain hypothesis is imposed on $v$.

**Proof.** We first establish the spectral interval needed for a weighted argument, then verify the original thin-layer error and the maximal-domain passage.

In spherical coordinates $(\xi,t)=(\sin\theta\,\Omega,\cos\theta)$ on $S^3$, $0<\theta<\pi$, $\Omega\in S^2$, expand in the ordinary complete spherical harmonics of $S^2$. In degree $l$, multiplication of the radial coefficient by $\sin\theta$ changes $B$ to the interval form

$$
 b_l[y]=\int_0^\pi\left(|y'|^2+
             \frac{l(l+1)}{\sin^2\theta}|y|^2\right)d\theta
              -\frac4\pi|y(\pi/2)|^2.
\tag{109.6}
$$

For $l=0$ its domain is $H_0^1(0,\pi)$; for $l\ge1$ it is the subspace on which the displayed positive integral is finite. This identification follows first for smooth spherical functions by integration by parts, using
$\int\sin^2\theta\,|\partial_\theta(y/\sin\theta)|^2
=\int(|y'|^2-|y|^2)$, and then by form density. The endpoint term vanishes for $H_0^1$ functions because $|y(\theta)|^2/\theta\to0$ and its analogue at $\pi$ follow from Cauchy--Schwarz and absolute continuity.

Writing $L_*=\pi/2$, Cauchy--Schwarz on each half interval gives
$\int_0^\pi|y'|^2\ge2|y(L_*)|^2/L_*$.
Thus $b_0\ge0$, and its kernel is exactly the span of
$y_0(\theta)=\min(\theta,\pi-\theta)$. Its positive spectrum is at least $4$. Indeed reflection about $L_*$ commutes with this form. In the odd subspace the midpoint value is zero and the first half-interval Dirichlet eigenvalue is $4$. In the even subspace a positive eigenvalue $k^2$ has the Robin condition
$y'(L_*)=y(L_*)/L_*$ and hence
$kL_*\cot(kL_*)=1$. There is no root with $0<kL_*<\pi$: the function $\sin z-z\cos z$ has derivative $z\sin z>0$ there, so $z\cot z<1$ on $(0,\pi/2)$, while the cotangent is nonpositive on $[\pi/2,\pi)$. The endpoint $kL_*=\pi$ cannot satisfy the Robin condition. These exhaust the separated interval eigenfunctions, by the compact self-adjoint interval realization. For $l\ge1$, (109.6) is at least $b_0+2\|y\|_2^2$. Completeness of the spherical harmonics, or equivalently finite angular sums followed by form closure, therefore gives

$$
B\ge0,\qquad \ker B=\mathbb C e_0,\qquad
B|_{e_0^\perp}\ge2.
\tag{109.7}
$$

The closedness and compact angular resolvent are already established in §106. The norm of $(B+1)^{1/2}$ is equivalent to the ordinary $H^1(S^3)$ norm: the upper bound is the trace bound, and its arbitrarily small gradient coefficient gives the reverse bound after adding a sufficiently large $L^2$ term; nonnegativity of $B$ absorbs that extra term. This also fixes the Sobolev scales used below.

We now pay the original-source comparison. In the coordinates (109.1), $a^{-1}q_c$ on compact punctured $H^1$ functions is the sesquilinear polarization of

$$
\begin{aligned}
\mathfrak p[f]&=\int\left(
 |\partial_xf-y\partial_tf/(2\kappa)|^2+
 |\partial_yf+x\partial_tf/(2\kappa)|^2+
 |\partial_zf|^2+|\partial_tf|^2\right)dZ\\
 &\hspace{12mm}-16\kappa\int\mathcal G(\xi,\kappa t)|f|^2dZ.
\end{aligned}
\tag{109.8}
$$

The factor $16\kappa=g_c/a$ and the unitary factor $\kappa^{1/2}$ follow directly from the original Haar Jacobian. For $r>0$, set
$W_r(X,u)=r^2\mathcal G(rX,\kappa ru)$ as in (106.7). The actual marginal and homogeneous bound imply, for any fixed $0<\alpha<1/2$,

$$
\begin{gathered}
\int W_r(X,u)du=\frac1{4\pi\kappa|X|},\\
\int |u|^\alpha W_r(X,u)du
 \le C_{\alpha,\kappa}r^\alpha|X|^{2\alpha-1},\\
W_r(X,u)\le C_d r^{1/2}\quad (|u|\ge d>0).
\end{gathered}
\tag{109.9}
$$

For the middle line use the change $s=\kappa ru$, Carnot homogeneity, and
$\int|s|^\alpha\mathcal G(X,s)ds\le C_\alpha|X|^{2\alpha-1}$, obtained by $s=|X|^2v$ in the bound $(|X|^4+s^2)^{-3/4}$. The tail integral converges because $\alpha<1/2$. The last line follows from (106.8).

On any fixed compact annulus $K\subset\mathbb R^4\setminus\{0\}$, these identities give the bilinear estimate

$$
\left|\int W_r\overline h k\,dXdu
 -\frac1{4\pi\kappa}\int\frac{\overline{h(X,0)}k(X,0)}{|X|}dX\right|
 \le C_K r^\alpha\|h\|_{H^1}\|k\|_{H^1},
\quad 0<r\le1,
\tag{109.10}
$$

for $h,k\in H^1(\mathbb R^4)$ supported in $K$. Here is a uniform proof, including the horizontal axis. Choose $b,d>0$ so that $K\cap\{|X|<2b\}$ lies in $|u|\ge d$. In $|X|<b$ both traces vanish and the last line of (109.9) controls the product integral by $Cr^{1/2}\|h\|_2\|k\|_2$. For $|X|\ge b$, the one-dimensional Sobolev and fundamental-theorem estimates give

$$
|\overline{h(X,u)}k(X,u)-\overline{h(X,0)}k(X,0)|
 \le C|u|^\alpha
       \|h(X,\cdot)\|_{H^1(\mathbb R)}
       \|k(X,\cdot)\|_{H^1(\mathbb R)}.
\tag{109.11}
$$

For $|u|\le1$ use the $1/2$ Hölder bound for each factor and its supremum bound; for $|u|>1$ use just the supremum bounds. The bounded horizontal support, the middle line of (109.9), and Cauchy--Schwarz in $X$ prove (109.10). All steps hold for complex factors.

After $Z=r(X,u)$, put $h(X,u)=r f(rX,ru)$, and use the same change for the second form slot. On a fixed annulus the kinetic coefficients in (109.8) differ from the Euclidean ones by $O(r)$ in the bilinear $H^1$ bound. Equations (109.9)--(109.10) consequently compare the actual form with
$\int|\nabla h|^2-(4/\pi)\int|h(X,0)|^2/|X|$ with error at most $Cr^\alpha$ times the two $H^1$ norms. This is an estimate for the original linear forms, not an inverse of the Fourier-modulus map.

Under $f(R\omega)=R^{-1}H(\tau,\omega)$, the latter comparison form becomes, for compactly supported cylinder functions,

$$
\mathfrak p_0[H]=\int_{\mathbb R}
    \left(\|\partial_\tau H\|_2^2+
                 \|(B)^{1/2}H\|_2^2\right)d\tau.
\tag{109.12}
$$

Indeed the radial term is $|H+\partial_\tau H|^2$, its integrated cross term is zero, and the angular term is $\mathfrak a[H]$. Multiplication by $R^{-1}$ and polar coordinates have bounded $H^1$ norms in both directions on any fixed annulus. Covering the end $\tau>T$ by overlapping slabs of fixed length therefore turns the preceding error into a local form $\mathfrak e=\mathfrak p-\mathfrak p_0$ satisfying, with $\alpha=1/4$,

$$
|\mathfrak e(J,K)|
 \le C\sum_{j\ge j_0}e^{-j/4}
       \|J\|_{H^1(I_j\times S^3)}
       \|K\|_{H^1(I_j\times S^3)}.
\tag{109.13}
$$

One can take $I_j=(j-2,j+2)$ and finitely modify the starting slabs. To obtain this bound use a smooth partition of unity in $\tau$ in one slot, and a cutoff equal to one on its support in the other slot. The derivatives of these cutoffs are uniformly bounded. Both the original and comparison forms are local, so the partition sums to their exact difference. This also proves (109.13) for arbitrary compactly supported $H^1$ cylinder functions by density. Extend $\mathfrak e$ to the whole cylinder by cutting both slots off below $T$ and keeping it unchanged above $T+1$.

For real $\delta$ let $\mathscr H^1_\delta$ be the space of distributions $J$ such that $e^{-\delta\tau}J\in H^1(\mathbb R\times S^3)$, and let $\mathscr H^{-1}_\delta$ mean $e^{-\delta\tau}F\in H^{-1}$, with distributional multiplication understood in the latter definition. The unweighted norm is equivalently
$\int(\|J'\|_2^2+\|(B+1)^{1/2}J\|_2^2)$ and its dual. Weighted Cauchy--Schwarz in (109.13), including the bounded derivatives of the weights, proves that the distributional operator $E$ of this extended form satisfies

$$
E:\mathscr H^1_\delta\longrightarrow
                 \mathscr H^{-1}_{\delta-1/4}
\quad\hbox{continuously, for every fixed }\delta.
\tag{109.14}
$$

Explicitly the second slot is paired with a test in $\mathscr H^1_{-(\delta-1/4)}$; its slab weight and that of the first slot cancel $e^{-j/4}$. Finite overlap bounds the sum. This verification uses no derivatives of the thin potential and no pointwise angular convergence of it.

We record the elementary weighted inverse used here. By (109.7),

$$
P_0=-\partial_\tau^2+B:
\mathscr H^1_\delta\longrightarrow\mathscr H^{-1}_\delta
\quad\hbox{is an isomorphism if }0<|\delta|\le1.
\tag{109.15}
$$

Conjugate by $e^{-\delta\tau}$, Fourier transform in $\tau$, and use the complete angular eigenbasis, with eigenvalues $\mu$. The symbols are
$p_{\delta,\mu}(\zeta)=\mu+\zeta^2-\delta^2-2i\delta\zeta$.
For $\mu=0$ their modulus is $\zeta^2+\delta^2$; for $\mu\ge2$ their real part is at least $\zeta^2+\mu-1$. Thus for each fixed allowed $\delta$,
$|p_{\delta,\mu}(\zeta)|\ge c_\delta(1+\zeta^2+\mu)$, with the reverse bound as well. Multiplication by the reciprocal gives exactly the bounded inverse between the indicated dual Sobolev spaces. It also proves uniqueness and surjectivity there.

If a distribution $F$ belongs to both right-hand spaces for $-1\le\delta'<\delta\le1$, neither weight zero, let $J_\delta,J_{\delta'}$ be these inverses. Their difference solves $P_0J=0$. On $\tau>0$ it is in $\mathscr H^1_\delta$ and on $\tau<0$ it is in $\mathscr H^1_{\delta'}$. Projection on each angular eigenfunction gives $-j''+\mu j=0$. For $\mu\ge2$ the exponents $\pm\sqrt\mu$ cannot satisfy these two end conditions. For $\mu=0$ the solutions are affine. They satisfy both conditions exactly when $\delta'<0<\delta$. Completeness of the angular basis therefore proves

$$
J_\delta=J_{\delta'}\quad(0<\delta'<\delta\le1),
\qquad
J_\delta-J_{\delta'}\in
       \{(A+\tau C)e_0:A,C\in\mathbb C\}
       \quad(\delta'<0<\delta).
\tag{109.16}
$$

All projections are legitimate weak $H^1$ tests, by angular form density. Thus (109.15)--(109.16) require no unproved asymptotic theorem for an operator with a singular angular coefficient.

We next start this weighted argument for every original maximal zero mode. By §108.2, $v\in\mathcal N_0$ is locally $H^2$ off $e$ and satisfies the original weak equation on every compact punctured $H^1$ test. Its $f_v$ has the same regularity in (109.1). There is a uniform annular estimate

$$
\|H_v\|_{H^1((j,j+1)\times S^3)}
 \le C\|H_v\|_{L^2((j-1,j+2)\times S^3)}
\quad(j\hbox{ sufficiently large}).
\tag{109.17}
$$

To verify the uniform constant, use $r=e^{-j}$ and $h_r(X,u)=r f_v(rX,ru)$ on two fixed nested annuli. In its exact equation the vector fields are $Y_{i,r}$ of (106.7), the central kinetic coefficient is one, and the potential is $16\kappa W_r$. Test with a fixed real annular cutoff squared times $h_r$. Its product-rule error is at most $C\|h_r\|_2^2$. The original potential estimate (106.9), with a fixed sufficiently small coefficient, absorbs its $\partial_u$ term into the free kinetic form. The $Y_{i,r}$ and $\partial_u$ together control the full Euclidean gradient uniformly on these annuli, since their shear coefficients are bounded there for $r\le1$. This proves the Caccioppoli bound for $h_r$; (109.2) on fixed annuli gives (109.17). If necessary enlarge the two fixed annuli by another fixed factor; finite overlap and fixed slab lengths give the same weighted conclusion. No global kinetic integral of $v$ is used.

The $L^2$ identity after (109.2), (109.17), and finite overlap imply $H_v\in\mathscr H^1_1$ on the positive end. Choose a smooth $\chi(\tau)$ equal to zero below $T+1$ and one above $T+2$, and extend $J=\chi H_v$ by zero to the whole cylinder. Then $J\in\mathscr H^1_1$. The exact original equation, the local conjugation (109.12), and the extension of $E$ give

$$
(P_0+E)J=F_0,
\qquad F_0\in H^{-1}\hbox{ with compact cylinder support}.
\tag{109.18}
$$

The support assertion follows because $J=0$ below the transition and equals the original solution above it. All commutator terms in the transition define $H^{-1}$ functionals on that compact slab by local $H^1$ regularity and the local form bound. Hence $F_0$ belongs to every weighted $\mathscr H^{-1}_\delta$.

Starting at $\delta=1$, (109.14) shows that $F_0-EJ$ belongs also to $\mathscr H^{-1}_{\delta-1/8}$ whenever $J\in\mathscr H^1_\delta$ and $\delta\ge1/4$. The improvement by $1/8$, rather than $1/4$, uses that $EJ$ is supported in a fixed lower half-cylinder complement; on that support the stronger decay weight includes the weaker one. Apply (109.15) at $\delta$ and $\delta-1/8$, and then the first identity in (109.16). Successive steps give
$J\in\mathscr H^1_{7/8},\mathscr H^1_{6/8},\ldots,\mathscr H^1_{1/8}$.
At the last weight (109.14) gives $F_0-EJ\in\mathscr H^{-1}_{-1/8}$. The second identity in (109.16) now yields
$J=(A+\tau C)e_0+Z$, with $Z\in\mathscr H^1_{-1/8}$. Restriction to the positive end is (109.4). The two coefficients are unique because a nonzero affine function is not in that weighted space on the positive end; their linearity follows from linearity of the original equation, all changes of variables and the inverse construction.

It remains to show that $C=0$ forces the original Friedrichs-domain membership, rather than imposing it. In this case $H_v=Ae_0+Z$ on the end and $e^{\tau/8}Z\in H^1$. Take a fixed outer source cutoff $\eta_0(\tau)$, equal to zero before a fixed large $T_0$ and one after $T_0+1$. Let $\theta_N$ equal one for $\tau\le N$, zero for $\tau\ge2N$, and satisfy $|\theta_N'|\le C/N$. The corresponding original vectors have compact punctured support and belong to $\mathcal E_2\subset\mathcal Q_c$. For their cylinder functions $\eta_0\theta_NH_v$, (109.12) and $Be_0=0$ bound the model form by
$C_v+C|A|^2/N$, uniformly in $N$. The terms involving $Z$ are bounded by its unweighted $H^1$ norm and the fixed transition terms; positivity of $B$ controls cross terms by Cauchy--Schwarz. The error (109.13) is uniformly bounded as well: the constant angular term has $H^1$ norm bounded on each slab and $\sum e^{-j/4}<\infty$, while $Z$ and the cutoff derivatives have bounded unweighted $H^1$ contributions. Consequently these original vectors have uniformly bounded $\overline q_c+\|\cdot\|_2^2$ norm.

They converge strongly in the original $L^2$ to the source part of $v$, by dominated convergence. Weak compactness of the complete form space, exactly as in §108.2, puts this source part in $\mathcal Q_c$. Its complementary exterior part belongs to $\mathcal E_2$ by (108.9). Thus $v\in\mathcal Q_c$. The already established $\mathcal N_0\cap\mathcal Q_c=\{0\}$ forces $v=0$. This proves injectivity of $B_\mathrm{src}(v)=C$ and (109.5), on the entire original maximal zero space. $\square$

**Corollary 109.3 (every-choice actual profile restriction).** Fix the original data of Definition 103.1. For every sequence $\sigma_n>2$ tending to $2$, without monotonicity, and every selection of nonzero actual attained critical zero states in the full complex $\mathcal E_{\sigma_n}$, use $V[u_n]=1$, $M_n=\|u_n\|_2^2$, and $v_n=u_n/\sqrt{M_n}$. On every common state-and-measure subsequence of §§104--105,

$$
\begin{gathered}
v_n\rightharpoonup v\text{ in the common }L^2(G,d\mu),\qquad
\zeta v_n\to\zeta v\text{ strongly in }L^2(G,d\mu),\\
|v_n|^2d\mu\longrightarrow |v|^2d\mu+m_e\delta_e,
\qquad v\in\mathcal N_0,\qquad \|v\|_2^2=1-m_e,
\end{gathered}
\tag{109.19}
$$

where $\zeta$ is any fixed bounded measurable cutoff vanishing near $e$, and the measure convergence is on the one-point compactification, with zero infinity atom. If $\mathcal N_0=\{0\}$, all these profiles are zero and all defects equal one; for each such actual selection the full sequences satisfy $v_n\rightharpoonup0$ and $|v_n|^2d\mu\to\delta_e$. If $\mathcal N_0\ne\{0\}$, fix any one unit vector $w$ in it. Every possible weak profile of every such selection, after the common subsequence refinement, has the form

$$
v=cw,\qquad |c|\le1,\qquad
m_e=1-|c|^2,\qquad
|v_n|^2d\mu\longrightarrow |c|^2|w|^2d\mu+(1-|c|^2)\delta_e.
\tag{109.20}
$$

Thus all nonzero weak profiles lie in one fixed complex line for the fixed $a,\eta$; after norm normalization their probability density is $|w|^2$. The scalar $c$ can depend on the sequence, the actual-state selection, its phases and the subsequence. Along a common subsequence, $m_e=0$ implies global strong $L^2$ convergence to $cw$, and global strong convergence implies $m_e=0$.

**Proof.** Equation (109.19) is precisely §§104--105 and is reused. Theorem 109.2 restricts its vector $v$ to a complex space of dimension at most one. In the nonzero case write $v=cw$ and use the existing mass identity; Hilbert weak convergence together with equality of the limiting and approximating norms is equivalent here to strong convergence. In the zero-space case every common refined subsequence has vector limit zero and measure limit $\delta_e$. Weak compactness of the $L^2$ unit ball, metrizability on it, and compactness of probabilities on the one-point compactification then give the asserted full-sequence convergence: a violating subsequence would have a common further subsequence with the already specified limits. This is a restriction on all possible limits, not a claim that any prescribed $c$ or any nonzero limit is attained. $\square$

**Definition 109.4 (attribution and unpaid boundaries).** The unchanged Green source, its positivity, homogeneous bound, exact Haar marginal and units are supplied by §§82--87 and (106.8). The closed angular realization, the original local regularity and exterior-domain statement, the Friedrichs zero-kernel intersection, and every-choice actual compactness and defect representation are the existing results of §§104--108. The halfspace profile in (109.3) retains the precise correspondence to Alvino--Ferone--Volpicelli, [*Sharp Hardy inequalities in the half space with trace remainder term*, arXiv:1105.0335v1, (12)](https://arxiv.org/html/1105.0335v1), already given in §§87 and 107. Ordinary spherical harmonics, interval Sturm--Liouville theory, Sobolev trace estimates, Caccioppoli localization, Fourier multipliers and Hilbert weak compactness are mature intermediate methods.

The logarithmic cylinder and weighted inverse method have classical conic precedents, for example Lesch, [*Differential Operators of Fuchs Type, Conical Singularities, and Asymptotic Methods*, arXiv:dg-ga/9607005v1, Definition 1.1.2 and §1.3](https://arxiv.org/html/dg-ga/9607005v1). That coefficient class does not by itself include this concentrating angular potential, and its domain or index theorems are not substituted for the verified estimates (109.9)--(109.18). Likewise Gesztesy--Mitrea--Nenciu--Teschl, [*Decoupling of Deficiency Indices and Applications to Schrödinger-Type Operators with Possibly Strongly Singular Potentials*, arXiv:1509.01748v2, Theorem 1.1 and §5](https://arxiv.org/html/1509.01748v2), localize singularities and treat specified inverse-square models; their statements alone supply no original thin-layer classification or zero-energy rank here. The source-specific form comparison, weighted maximal-solution expansion, injective source coefficient and its actual-profile consumer are repository-derived deductions with the complete original correspondence proved above, not an assertion of worldwide priority.

The rank bound permits both $\mathcal N_0=\{0\}$ and a one-dimensional space. It proves neither existence of a global original $L^2$ zero mode nor nonzero attainment by an actual critical-state subsequence. It does not select $m_e$, establish source tightness of the actual probabilities, identify a surviving scale or a varying-scale actual profile, or turn the fixed-vector expansion (109.4) into a joint estimate for $v_n$ and shrinking radii. No assertion of positivity, uniqueness of actual states, a selected phase, equality of maximal and Friedrichs domains, native realization or physical spatial dimension is made.

## 追加锚（本行以下为增补区）

## 110. A global original maximal zero mode with unit logarithmic coefficient

**Definition 110.1 (unchanged operator and the two domains).** Retain precisely Definitions 103.1, 107.1 and 109.1: the original product on $G=H^1\times\mathbb R$, raw Lebesgue Haar measure, $X_1=\partial_x$, $X_2=\partial_y+x\partial_w$, $X_3=\partial_z$, $L=-\sum_iX_i^2$, the clock $e^{-tL}$, and its positive degree-$-3$ unit-source Green field $\Gamma$, with $L\Gamma=\delta_e$. Fix the original $a,\eta>0$ and central coordinate and spectral units. Set

$$
A_0=aL+\eta D_w^2,\qquad g_c=16\sqrt{a\eta},\qquad
S=(A_0-g_c\Gamma)|_{\mathcal D_0},\qquad
\mathcal D_0=C_c^\infty(G\setminus\{e\};\mathbb C).
\tag{110.1}
$$

Here $A_0$ is the original free joint spectral sum. Write $H_F$ for the Friedrichs operator of $S$, with form $(\overline q_c,\mathcal Q_c)$, and retain $\mathcal N_0=\ker S^*$ and the complex-linear coefficient $B_\mathrm{src}$ of Theorem 109.2. In particular $\ker H_F=\{0\}$ and $\mathcal N_0\cap\mathcal Q_c=\{0\}$. The coordinate map $v\mapsto f_v$, cylinder function $H_v$, angular vector $e_0$, angular operator $B$ and spaces $\mathscr H^1_\delta,\mathscr H^{-1}_\delta$ below are exactly (109.1)--(109.15). No identification of $\mathcal Q_c$ with $D(S^*)$ is made.

**Theorem 110.2 (global existence on the original maximal class).** For every fixed original $a,\eta>0$ there is a vector $w_*\in L^2(G,d\mu;\mathbb C)$ such that

$$
w_*\in D(S^*),\qquad S^*w_*=0,\qquad B_\mathrm{src}(w_*)=1.
\tag{110.2}
$$

Consequently $0<\|w_*\|_2<\infty$, $w_*\notin\mathcal Q_c$, and, by the existing injectivity theorem,

$$
\mathcal N_0=\mathbb C w_*,\qquad \dim_{\mathbb C}\mathcal N_0=1.
\tag{110.3}
$$

The vector with coefficient one is unique. This normalization fixes the diagnostic coefficient, without changing $\Gamma$, its unit source, the original operator or the phase of any actual critical state.

**Proof.** We construct an exact local logarithmic solution, correct its compactly supported error in the original Friedrichs domain, and verify that the correction has no logarithmic term. Two domain estimates needed for this construction are proved first.

For a compactly supported cylinder function $J\in H^1(\mathbb R\times S^3)$, put

$$
\mathcal E_0[J]=\int_{\mathbb R}
 \bigl(\|\partial_\tau J\|_2^2+\|B^{1/2}J\|_2^2\bigr)d\tau.
\tag{110.4}
$$

Suppose $J=0$ for $\tau\le T$. Decompose $J=h e_0+J_\perp$. The already established $B|_{e_0^\perp}\ge2$ controls the $L^2$ norm of $J_\perp$ by its angular energy, while $h(T)=0$ and

$$
|h(\tau)|^2\le(\tau-T)\int_T^\infty|h'(s)|^2ds
\quad(\tau\ge T).
\tag{110.5}
$$

The equivalence of the $(B+1)^{1/2}$ and ordinary angular $H^1$ norms from §109 then gives

$$
\int_T^\infty e^{-\tau/4}
 \bigl(\|\partial_\tau J\|_2^2+\|J\|_{H^1(S^3)}^2\bigr)d\tau
 \le C e^{-T/4}\mathcal E_0[J].
\tag{110.6}
$$

Indeed the perpendicular and derivative terms use $e^{-\tau/4}\le e^{-T/4}$; the scalar term uses
$\int_T^\infty e^{-\tau/4}(\tau-T)d\tau=16e^{-T/4}$.
Finite overlap of the slabs in (109.13) converts this bound into
$|\mathfrak e(J,J)|\le Ce^{-T/4}\mathcal E_0[J]$.
For all sufficiently large fixed $T$, the original form comparison therefore gives

$$
\frac12\mathcal E_0[J]
 \le a^{-1}q_c[u_J]\le\frac32\mathcal E_0[J],
\qquad f_{u_J}(R\omega)=R^{-1}J(-\log R,\omega).
\tag{110.7}
$$

These inequalities initially concern compact punctured $H^1$ vectors, which belong to $\mathcal E_2$; no separate infinite kinetic or potential integral is used.

We deduce a necessary source-domain property for every $y\in\mathcal Q_c$. Choose a smooth real angle $\theta(\tau)$ equal to zero for $\tau\le T$ and $\pi/2$ for $\tau\ge T+1$. The corresponding original multipliers $\alpha=\sin\theta$ and $\beta=\cos\theta$ extend smoothly across $e$ by their constant values. They satisfy $\alpha^2+\beta^2=1$ and have differentials supported on a fixed compact punctured annulus. On the punctured core the product rule gives

$$
q_c[\alpha u]+q_c[\beta u]
 =q_c[u]+\int_G\bigl(\mathcal C[\alpha]+\mathcal C[\beta]\bigr)|u|^2d\mu,
\quad
\mathcal C[\gamma]=a\sum_i|X_i\gamma|^2+\eta|\partial_w\gamma|^2.
\tag{110.8}
$$

Nonnegativity of both localized forms bounds each multiplier in the $\mathcal Q_c$ norm; applying the same inequality to differences extends both multipliers to all of $\mathcal Q_c$ by core closure. If $u_j\to y$ in that norm, (110.7)--(110.8) bound $\mathcal E_0[H_{\alpha u_j}]$ uniformly. On every finite cylinder interval the physical $L^2$ convergence is ordinary cylinder $L^2$ convergence, since its density is $e^{-2\tau}$. Weak compactness of the bounded derivative and angular-energy terms on increasing finite intervals, followed by lower semicontinuity, consequently gives

$$
\partial_\tau H_y\in L^2((T+1,\infty)\times S^3),\qquad
B^{1/2}H_y\in L^2((T+1,\infty)\times S^3)
\quad(y\in\mathcal Q_c).
\tag{110.9}
$$

In this passage (110.5) controls the scalar component on each finite interval; the angular gap controls the perpendicular component. Thus the weak limits are the distributional derivatives and angular form components of the actual $H_y$. In particular an expansion
$H_y=(A+\tau C)e_0+Z$ with $e^{\tau/8}Z\in H^1$ can have $y\in\mathcal Q_c$ only if $C=0$.

The same localization also supplies the exterior-domain fact used below. If $\psi$ is a fixed smooth real exterior cutoff, zero near $e$ and one outside a compact set, it can be chosen as the cosine of a smooth angle, with its sine giving the complementary partition. Equation (110.8) makes multiplication by $\psi$ bounded on $\mathcal Q_c$. Since $\Gamma$ is bounded on $\operatorname{supp}\psi$, core differences satisfy

$$
aT[\psi u]+\eta D_2[\psi u]
 =q_c[\psi u]+g_cV[\psi u]
 \le C_\psi\bigl(q_c[u]+\|u\|_2^2\bigr).
\tag{110.10}
$$

The completeness of the original free space $\mathcal E_2$ therefore proves $\psi y\in\mathcal E_2$ for every $y\in\mathcal Q_c$. This assertion uses the exterior cutoff, not equality of the original domains.

We now construct the local solution. Let $P_0=-\partial_\tau^2+B$ and fix $\delta=-1/8$. Extend the error form of (109.13) to the whole cylinder by multiplying both slots by a smooth cutoff zero below $T$ and one above $T+1$; denote its distributional operator by $E_T$. Weighted Cauchy--Schwarz in that same slab estimate gives

$$
\|E_T\|_{\mathscr H^1_\delta\to\mathscr H^{-1}_\delta}
 \le C_\delta e^{-T/4}.
\tag{110.11}
$$

The cutoff derivatives have uniformly bounded size, and the weights in the two dual slots cancel on each slab, so the constant is independent of sufficiently large $T$. The already proved inverse (109.15), and a Neumann series for sufficiently large $T$, make $P_0+E_T$ an isomorphism between these two weighted spaces.

Let $J_0(\tau,\omega)=\tau e_0(\omega)$. Although $J_0$ is not in $\mathscr H^1_{-1/8}$ on the positive end, $E_TJ_0$ is well defined and belongs to $\mathscr H^{-1}_{-1/8}$. To check this directly, its slab pairing is bounded by a constant times
$e^{-j/4}(1+|j|)$ times the $H^1$ norm of the test on that slab. A dual test has weight $e^{-\tau/8}$; the remaining coefficients are bounded by $C(1+j)e^{-j/8}$ on the positive end and are square summable. The extension vanishes below a fixed cylinder level. Thus

$$
Z=-(P_0+E_T)^{-1}E_TJ_0\in\mathscr H^1_{-1/8},
\qquad H=J_0+Z
\tag{110.12}
$$

is well defined. Since $P_0J_0=0$ distributionally, $(P_0+E_T)H=0$. Above $T+1$ this is exactly the original weak equation after (109.2), with the actual error form, not its interface approximation. The associated local original vector $v_{\mathrm{loc}}$ obeys

$$
H_{v_{\mathrm{loc}}}=\tau e_0+Z,\qquad
 e^{\tau/8}Z\in H^1((T+1,\infty)\times S^3).
\tag{110.13}
$$

It is in original $L^2$ near $e$, since $\int_{T+1}^\infty e^{-2\tau}(1+\tau^2)d\tau<\infty$. On every compact punctured annulus it is $H^1$ and satisfies the original uniformly elliptic equation with smooth coefficients and potential. The local elliptic regularity used in §108 upgrades it there to a smooth solution, including across the coordinate hypersurface $t=0$.

Multiply this vector by a smooth source cutoff, one for $\tau\ge T+3$ and zero for $\tau\le T+2$, and extend by zero to obtain $g\in L^2(G)$ with compact support. Its equation is exact near the puncture, and its cutoff error is a smooth function $F$ supported on a compact punctured annulus. Thus, directly on every test in $\mathcal D_0$,

$$
g\in D(S^*),\qquad S^*g=F\in C_c^\infty(G\setminus\{e\}),
\qquad H_g=\tau e_0+Z\quad(\tau\ge T+3).
\tag{110.14}
$$

A distribution at the excluded point need not be assigned to $S^*g$; its adjoint action here is defined by the original punctured tests.

For completeness we prove the global zero-energy range assertion needed to remove $F$. For every compactly supported $f\in L^2(G)$,

$$
\sup_{0<r\le1}\|(H_F+r)^{-1}f\|_2<\infty,
\qquad f\in\operatorname{ran}H_F.
\tag{110.15}
$$

The free estimate (105.5), by its duality argument, supplies

$$
\|(A_0+r)^{-1}h\|_2\le\frac{h_2}{a}\|\rho^2h\|_2
\quad(r>0,\ h,\rho^2h\in L^2),
\qquad \rho=(|\xi|^4+s^2)^{1/4}.
\tag{110.16}
$$

This is the existing original order-two Hardy--Rellich supply; it is uniform in $r$ and does not assert a bounded inverse on all $L^2$ at zero.

If the first assertion in (110.15) failed for a fixed $f$, choose $r_j\in(0,1]$ with
$t_j=\|(H_F+r_j)^{-1}f\|_2\to\infty$, and set
$z_j=(H_F+r_j)^{-1}f/t_j$. Then

$$
\|z_j\|_2=1,\qquad
(H_F+r_j)z_j=f/t_j,\qquad
0\le\overline q_c[z_j]+r_j
 =\operatorname{Re}\langle z_j,f/t_j\rangle
 \le\|f\|_2/t_j\longrightarrow0.
\tag{110.17}
$$

The actual whole-closure cylinder estimate (107.5) now gives, for every fixed $b>0$,

$$
\int_{\{|\xi|<b\}}|z_j|^2d\mu
 \le\frac{\pi^2b}{\sqrt a}\sqrt{\overline q_c[z_j]}
 \longrightarrow0.
\tag{110.18}
$$

In particular $z_j\to0$ in $L^2$ on every compact subset of the original space, including the source. On compact subsets off $e$ the equation in (110.17) gives also $z_j\to0$ locally in ordinary $H^1$. Here is the needed uniform regularity estimate: for nested compact coordinate sets $K\subset\operatorname{int}K'\subset G\setminus\{e\}$, test the equation by a real cutoff squared times $z_j$. The potential is bounded on $K'$, $0<r_j\le1$, and the actual free symbol is uniformly elliptic there by (108.4). Cauchy--Schwarz and absorption of the cutoff cross terms give

$$
\|z_j\|_{H^1(K)}
 \le C_{K,K'}\bigl(\|z_j\|_{L^2(K')}+t_j^{-1}\|f\|_{L^2(K')}\bigr)
 \longrightarrow0.
\tag{110.19}
$$

Local $H^2$ regularity for the $L^2$ forcing justifies these tests; alternatively smooth approximation gives the same weak cutoff identity. No estimate across $e$ is used in (110.19).

Fix an exterior cutoff $\psi$ as in (110.10), and put $p_j=\psi z_j\in\mathcal E_2$. The exact original localized equation is

$$
(A_0+r_j)p_j=g_c\Gamma p_j+b_j+\psi f/t_j,
\qquad b_j=[A_0,\psi]z_j.
\tag{110.20}
$$

The commutator has order one with smooth coefficients on the fixed compact punctured support of $d\psi$, so (110.19) gives $b_j\to0$ in $L^2$ there. All terms on the right of (110.20) belong to $L^2$, and their products by $\rho^2$ also belong to $L^2$: for the potential term this follows from $\psi=0$ near $e$ and $\rho^2\Gamma\le B_\Gamma/\rho$ at infinity. The distributional equation extends to the free form domain by the original free-core density. Since $p_j\in\mathcal E_2$, free form representation therefore puts $p_j\in D(A_0)$ and makes application of $(A_0+r_j)^{-1}$ legitimate.

Applying (110.16) and separating a large fixed $\rho$ ball gives

$$
\begin{aligned}
\|p_j\|_2
 &\le\frac{g_ch_2}{a}\|\rho^2\Gamma p_j\|_2+o(1)\\
 &\le\frac{g_ch_2}{a}
       \|\mathbf1_{\{\rho\le R\}}\rho^2\Gamma\psi z_j\|_2
       +\frac{g_ch_2B_\Gamma}{aR}\|p_j\|_2+o(1).
\end{aligned}
\tag{110.21}
$$

For fixed $R$ the first norm tends to zero by (110.18), because its multiplier is bounded and compactly supported away from $e$. The other two forcing terms in (110.20) give $o(1)$ in (110.21) by their compact supports and $t_j\to\infty$. Choose $R$ so that $g_ch_2B_\Gamma/(aR)<1/2$. Absorption shows $p_j\to0$ globally in $L^2$. Also $(1-\psi)z_j\to0$ in $L^2$ by (110.18), since $1-\psi$ has compact support. This contradicts $\|z_j\|_2=1$, proving the resolvent bound.

Let $d\nu_f(\lambda)$ be the spectral measure of $f$ for $H_F\ge0$. The bound just proved and monotone convergence give
$\int_{(0,\infty)}\lambda^{-2}d\nu_f(\lambda)<\infty$.
The zero atom is absent because $\ker H_F=\{0\}$. Hence the spectral vector $y=H_F^{-1}f$ belongs to $L^2$ and to $D(H_F)$, satisfies $H_Fy=f$, and is the strong $L^2$ limit of $(H_F+r)^{-1}f$ as $r\downarrow0$. This proves (110.15) on exactly its asserted compact-source class. The spectral inverse remains an unbounded operator on its full domain; no positive spectral gap has been introduced.

Apply this range assertion to the actual $F$ in (110.14), and let $y\in D(H_F)$ satisfy $H_Fy=F$. Since $H_F$ extends $S$ and is self-adjoint, $D(H_F)\subset D(S^*)$ and the two actions agree there. Therefore

$$
w_*=g-y\in D(S^*),\qquad S^*w_*=0,\qquad w_*\in L^2(G,d\mu).
\tag{110.22}
$$

It remains to check its coefficient. Theorem 109.2 applies to this global vector and gives
$H_{w_*}=(A(w_*)+\tau B_\mathrm{src}(w_*))e_0+Z_{w_*}$,
with $e^{\tau/8}Z_{w_*}\in H^1$ on the positive end. Subtracting from (110.14) yields

$$
H_y=\bigl(-A(w_*)+\tau(1-B_\mathrm{src}(w_*))\bigr)e_0
                 +Z-Z_{w_*}.
\tag{110.23}
$$

Both remainder derivatives are square integrable on that end. Since $y\in D(H_F)\subset\mathcal Q_c$, (110.9) makes $\partial_\tau H_y$ square integrable as well. A nonzero constant multiple of $e_0$ on an infinite cylinder cannot have this property, even after adding an $L^2$ derivative. Thus $B_\mathrm{src}(w_*)=1$. This proves (110.2), in particular nonvanishing, for the same vector that satisfies the global original equation and global original $L^2$ condition. Injectivity of $B_\mathrm{src}$ and the maximal/Friedrichs intersection, already proved in §§104 and 109, give all the remaining assertions. $\square$

**Corollary 110.3 (the existing actual-family statement with a proved generator).** Fix the original data and put $w=w_*/\|w_*\|_2$. For every sequence $\sigma_n>2$ tending to $2$, without monotonicity, and every choice of nonzero actual attained complex critical zero states in the full spaces
$\mathcal E_{\sigma_n}=D(L^{1/2})\cap D(|D_w|^{\sigma_n/2})$, normalize amplitudes by
$V[u_n]=1$, $M_n=\|u_n\|_2^2$ and $v_n=u_n/\sqrt{M_n}$ in the common original complex $L^2(G,d\mu)$. Every subsequence has a further common state-and-measure subsequence on which, for some $c\in\mathbb C$ with $|c|\le1$,

$$
\begin{gathered}
v_n\rightharpoonup cw\quad\text{in }L^2(G,d\mu),\qquad
v_n\to cw\quad\text{in }L^2_{\mathrm{loc}}(G\setminus\{e\}),\\
\zeta v_n\longrightarrow c\zeta w\quad\text{strongly in }L^2(G,d\mu),\\
|v_n|^2d\mu\longrightarrow
 |c|^2|w|^2d\mu+(1-|c|^2)\delta_e,\qquad m_\infty=0.
\end{gathered}
\tag{110.24}
$$

Here $\zeta$ is every fixed bounded measurable cutoff vanishing near $e$, and probability convergence is against continuous functions on the one-point compactification of the original space. The same common subsequence serves these conclusions. Its source atom is $m_e=1-|c|^2$; along it global strong $L^2$ convergence holds exactly when $m_e=0$.

**Proof.** Apply Corollary 109.3, with its topology and probability decomposition from §§104--105, to the nonzero generator supplied by Theorem 110.2. This is a reuse of that actual-family restriction, with its previously unresolved nonzero-space alternative now established; it is not a second existence or compactness theorem for actual states. $\square$

**Definition 110.4 (attribution and remaining mathematical boundaries).** The source, Green bound, exact Haar marginal, free domains, Hardy--Rellich constant $h_2$ and weighted free resolvent estimate are the existing supplies of §§82--87, 102 and 105. The whole-closure source-cylinder estimate is (107.5); the original punctured elliptic regularity is §108; the angular gap, bilinear original thin-layer estimate, weighted cylinder inverse and injective logarithmic coefficient are §109. The profile underlying $e_0$ retains the Alvino--Ferone--Volpicelli correspondence at $n=4$, $\beta=2$, in [arXiv:1105.0335v1, Theorem 1.1 and (12)](https://arxiv.org/html/1105.0335v1). These results are reused, without replacing the source by the auxiliary interface.

Neumann inversion, the cutoff form identity and nonnegative self-adjoint spectral calculus are mature methods. Pinchover--Tintarev, [*A ground state alternative for singular Schrödinger operators*, arXiv:math/0411658v1, Theorem 1.4 and Corollary 2.3](https://arxiv.org/html/math/0411658v1), distinguish a weighted spectral gap from a null state for locally uniformly elliptic real divergence-form operators on an open domain with locally $L^p$, $p>d/2$, potential. On the punctured original coordinate domain those local coefficient and potential hypotheses hold, and the real core form is nonnegative. Their dichotomy does not give (110.15) or an original global $L^2$ logarithmic mode; no choice between its alternatives is substituted for the range proof above. Likewise the domain decompositions in [*A Survey on the Krein--von Neumann Extension*, arXiv:1203.5713v1, Theorem 2.1, (2.9)--(2.11)](https://arxiv.org/html/1203.5713v1), are stated there under a strictly positive lower bound $S\ge\varepsilon I$, $\varepsilon>0$. That hypothesis is unavailable here by §87.4, so those inverse and decomposition formulas are not applied. The local exact construction, source-domain derivative restriction, compact-source interacting range argument and their gluing into (110.2) are repository-derived deductions for the fixed original family; no worldwide novelty claim is made.

Existence of $w_*$ is an assertion about the abstract original maximal zero space. It does not imply that an actual critical-state selection has $c\ne0$ in (110.24), fix $m_e$, prove source tightness, choose a phase or coefficient for actual states, identify a surviving shrinking scale, or supply a joint limit in $n$ and the source radius. The physical source remains unit normalized regardless of $B_\mathrm{src}(w_*)=1$. The maximal and Friedrichs domains remain distinct, no positivity or symmetry of actual states is assumed, and no native realization or physical spatial-dimension conclusion follows.

## 追加锚（本行以下为增补区）

## 111. Actual source tightness and convergence to the original maximal zero line

**Definition 111.1 (fixed original family and normalizations).** Keep exactly the product, source and units of Definitions 103.1 and 110.1:

$$
\begin{gathered}
G=H^1\times\mathbb R,\qquad
pp'=(x+x',y+y',z+z',w+w'+xy'),\qquad d\mu=dx\,dy\,dz\,dw,\\
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad X_3=\partial_z,
\quad L=-\sum_iX_i^2,\quad D_w=-i\partial_w,\\
\Gamma=\int_0^\infty h_t\,dt>0,\quad L\Gamma=\delta_e,
\quad \Gamma\circ\delta_r=r^{-3}\Gamma,\quad
\delta_r(x,y,z,w)=(rx,ry,rz,r^2w).
\end{gathered}
\tag{111.1}
$$

The free realization and clock are the original ones, $e^{-tL}$. Fix the original $a,\eta>0$. On the entire complex domain set

$$
\begin{gathered}
\mathcal E_\sigma=D(L^{1/2})\cap D(|D_w|^{\sigma/2}),\qquad
T[u]=\sum_i\|X_i u\|_2^2,\quad
D_\nu[u]=\||D_w|^{\nu/2}u\|_2^2,\quad
V[u]=\int_G\Gamma|u|^2d\mu,\\
g_\sigma=\inf_{0\ne u\in\mathcal E_\sigma}
\frac{aT[u]+\eta D_\sigma[u]}{V[u]},\qquad
q_\sigma[u]=aT[u]+\eta D_\sigma[u]-g_\sigma V[u],\\
H_\sigma\text{ represents }q_\sigma,\qquad
\mathcal Z_\sigma=\{v\in\ker H_\sigma:\|v\|_2=1\},\qquad \sigma>2.
\end{gathered}
\tag{111.2}
$$

The nonnegative closed form, attainment, and full-domain equation are the existing supplies of §§101.5 and 102.3. Every vector in $\mathcal Z_\sigma$ is an actual attained critical state: form representation gives $q_\sigma[v]=0$, and $0<V[v]<\infty$ by §87.2. Conversely a nonzero minimizer is a null vector of this nonnegative represented form, hence belongs to $\ker H_\sigma$. Thus (111.2) includes the entire zero eigenspace, not a selected family of minimizers.

For every sequence $\sigma_n>2$ tending to $2$, without monotonicity, and every selection $v_n\in\mathcal Z_{\sigma_n}$, put

$$
\begin{gathered}
u_n=\frac{v_n}{\sqrt{V[v_n]}},\qquad
V[u_n]=1,\qquad M_n=\|u_n\|_2^2,\qquad
v_n=\frac{u_n}{\sqrt{M_n}},\\
\epsilon_n=\sigma_n-2,\qquad \ell_n=\sqrt{M_n},\qquad
\Lambda_n=\log(1/\ell_n),\qquad g_n=g_{\sigma_n},\qquad
\kappa=\sqrt{\eta/a},\qquad g_c=16\sqrt{a\eta}.
\end{gathered}
\tag{111.3}
$$

All state limits use the same original complex $L^2(G,d\mu)$. The original generator is precisely $w=w_*/\|w_*\|_2$ of Theorem 110.2. In particular
$\ker S^*=\mathbb Cw$, whereas $w\notin\mathcal Q_c$ and $\ker H_F=\{0\}$. These maximal and Friedrichs assertions retain their distinct domains.

Use the linear unitary chart and logarithmic diagnostic of §109:

$$
\begin{gathered}
s=w-xy/2,\quad t=s/\kappa,\quad Z=(\xi,t),\quad
R_\kappa=(|\xi|^2+t^2)^{1/2},\quad \tau=-\log R_\kappa,\quad \omega=Z/|Z|,\quad
\mathcal G(\xi,s)=\Gamma(\xi,s+xy/2),\\
\phi_n(\xi,t)=\kappa^{1/2}v_n(x,y,z,\kappa t+xy/2),\qquad
H_n(\tau,\omega)=e^{-\tau}\phi_n(e^{-\tau}\omega),\\
F_{n,r}(X,t)=r^2\phi_n(rX,rt),\qquad
\|F_{n,r}\|_{L^2(\mathbb R^4)}=1,\\
\int_{\{R_\kappa<e^{-T}\}}|v_n|^2d\mu
 =\int_T^\infty e^{-2\tau}\|H_n(\tau)\|_{L^2(S^3)}^2d\tau.
\end{gathered}
\tag{111.4}
$$

In the first line $w$ inside the coordinate $s$ denotes the original central coordinate; the unit vector $w$ retains its meaning elsewhere. No nonlinear modulus map is inverted. The existing actual-state supplies (103.6), (103.24) give

$$
M_n\to0,\quad \Lambda_n\to\infty,\quad
\epsilon_n\Lambda_n\to0,\quad g_n\to g_c,\quad
D_{\sigma_n}[u_n]=O(1).
\tag{111.5}
$$

Their sequential statements hold for every selection. A violation of uniform boundedness near $2$ would itself select an order sequence and actual vectors violating those statements. This observation will also be used for uniform conclusions below. No positivity, symmetry, phase, simplicity or extension hypothesis is imposed on the actual vectors.

**Lemma 111.2 (annular gain and varying-order residual for actual zooms).** Fix a positive constant $c_0$ and smooth compact annular cutoffs. For all sufficiently small fixed $r_0>0$, eventually uniformly over
$c_0\ell_n\le r\le r_0$, each such cutoff $\theta$ satisfies

$$
\|\theta F_{n,r}\|_{H^{5/4}(\mathbb R^4)}\le C_\theta.
\tag{111.6}
$$

Here and below these are ordinary isotropic Euclidean Sobolev norms. For every smooth compact cutoff $\chi$ off zero one consequently has, with its nested cutoffs included in the preceding choice,

$$
\big\|\chi\bigl(|D_t|^{2+\epsilon_n}-D_t^2\bigr)F_{n,r}
       \big\|_{H^{-1}(\mathbb R^4)}\le C_\chi\epsilon_n.
\tag{111.7}
$$

The constants are independent of $n,r$ and the actual vector. The sufficiently small $r_0$ may depend on the fixed cutoffs and original data.

**Proof.** Set $k_{n,r}=(\kappa r)^{-\epsilon_n}$. The exact zoom equation, vector fields $Y_{i,r}$ and same-field potential $W_r$ are (106.7), (106.13):

$$
\left(\mathcal L_r+k_{n,r}|D_t|^{2+\epsilon_n}\right)F_{n,r}
 =\frac{g_n}{a}W_rF_{n,r},\qquad
\mathcal L_r=-\sum_iY_{i,r}^2,\qquad
W_r(X,t)=r^2\mathcal G(rX,\kappa rt).
\tag{111.8}
$$

This is initially the actual full form equation and hence also a distributional identity. Spectral Hölder and (111.5) give, eventually,

$$
\begin{gathered}
D_{\epsilon_n}[v_n]\le
 \left(\frac{D_{\sigma_n}[u_n]}{M_n}\right)^{\epsilon_n/\sigma_n}
 =O(1),\\
D_{\epsilon_n}[F_{n,r}]=(\kappa r)^{\epsilon_n}D_{\epsilon_n}[v_n],\qquad
k_{n,r}(1+D_{\epsilon_n}[F_{n,r}])
 =k_{n,r}+D_{\epsilon_n}[v_n]=O(1),\\
\sup_{c_0\ell_n\le r\le r_0}|k_{n,r}-1|
 \le C\epsilon_n(1+\Lambda_n)\longrightarrow0.
\end{gathered}
\tag{111.9}
$$

For the last line choose $\kappa r_0<1$ and use
$|\log(\kappa r)|\le\Lambda_n+C_{c_0,\kappa}$ on this range, followed by $|e^x-1|\le |x|e^{|x|}$. In particular $k_{n,r}$ stays bounded above and below. These are exactly the parameters needed in the proof of (106.15)--(106.16). That proof, using the whole-line double commutator (104.9) and the infinitesimal annular bound (106.9), therefore gives

$$
\|\theta F_{n,r}\|_{H^1}^2+
 D_{2+\epsilon_n}[\theta F_{n,r}]\le C_\theta
\tag{111.10}
$$

throughout the stated range, including $c_0<1$. The only global commutator input there is the middle line of (111.9); no monotonicity of $r$ or $\sigma_n$ is used. Multiplication preserves the exact zoom form domain, by the same central Fourier convolution and horizontal product rules. Thus all cutoffs used here are legitimate form vectors. This is annular control of actual solutions, not absorption of the global critical potential on arbitrary states.

We first bound the actual potential in a slightly better negative norm. If $h\in H^1$ is supported on a fixed compact annulus $K$, then

$$
\|W_rh\|_{H^{-3/4}}\le C_K\|h\|_{H^1},\qquad 0<r\le1.
\tag{111.11}
$$

Choose $b,d>0$ so that $K\cap\{|X|<b\}$ lies in $|t|\ge d$. On this part (106.8) gives $W_r\le C_dr^{1/2}$, so the pairing with a test $z\in H^{3/4}$ is bounded by $C\|h\|_2\|z\|_2$. On $|X|\ge b$, the exact original marginal is
$\int W_r(X,t)dt=(4\pi\kappa|X|)^{-1}\le(4\pi\kappa b)^{-1}$.
The one-dimensional Sobolev embeddings give

$$
\sup_t|h(X,t)|\le C\|h(X,\cdot)\|_{H^1_t},\qquad
\sup_t|z(X,t)|\le C\|z(X,\cdot)\|_{H^{3/4}_t}.
$$

Integrating their product in $X$ and applying Cauchy--Schwarz proves (111.11), since the partial central norms are bounded by the corresponding full positive Sobolev norms. The argument keeps the full potential and applies to complex factors.

The separated central tails have an extra small coefficient. For $0<\epsilon\le1/8$, the usual one-dimensional fractional Fourier formula gives, off the support of $g$,

$$
\begin{gathered}
|D_t|^{2+\epsilon}g(t)
 =c_\epsilon(1+\epsilon)(2+\epsilon)
       \int\frac{g(s)}{|t-s|^{3+\epsilon}}ds,\\
c_\epsilon=
 \left(2\int_0^\infty(1-\cos s)s^{-1-\epsilon}ds\right)^{-1}
 \le C\epsilon.
\end{gathered}
\tag{111.12}
$$

For the bound integrate over fixed-length subintervals of each period on which $1-\cos s\ge1/2$; their sum is bounded below by $C\sum_{m\ge1}m^{-1-\epsilon}\ge C'/\epsilon$. The kernel formula follows by applying $-\partial_t^2$ to the off-support formula for $|D_t|^\epsilon$, as in (105.16). At separation $|t-s|\ge d>0$ its absolute kernel has both Schur integrals bounded by $C_d\epsilon$. It therefore defines an $L^2$ operator of norm at most $C_d\epsilon$, also for inputs of unbounded central support, by truncation and that bound. This retains the whole central tail.

Let $\widetilde\theta=1$ on a neighborhood of $\operatorname{supp}\theta$, still supported on a compact annulus. For $p_\epsilon(\lambda)=|\lambda|^{2+\epsilon}$, Fourier convolution in the central variable and the mean value bound

$$
|p_\epsilon(\mu+h)-p_\epsilon(\mu)|
 \le C|h|\bigl(\langle\mu\rangle^{1+\epsilon}
                      +\langle h\rangle^{1+\epsilon}\bigr)
\tag{111.13}
$$

show that $[p_\epsilon(D_t),\theta]$ maps $L^2_XH^1_t$ to $L^2_XH^{-3/4}_t$ uniformly for $0<\epsilon\le1/8$. Indeed the output weight $\langle\mu+h\rangle^{-3/4}$ leaves at most $\langle\mu\rangle^{1/4+\epsilon}$ on the input, bounded by its $H^1_t$ weight; the remaining powers of $h$ are absorbed by the cutoff's uniformly bounded weighted Fourier $L^1$ norms. Young's inequality completes this estimate at each $X$, then integration in $X$ gives it globally. The latter partial negative norm dominates the isotropic $H^{-3/4}$ norm.

Apply this estimate to $\widetilde\theta F_{n,r}$, using (111.10). The remainder of the commutator is
$-\theta p_{\epsilon_n}(D_t)((1-\widetilde\theta)F_{n,r})$.
For every fixed $X$ contributing to $\theta$, its two central supports have a fixed positive separation: Euclidean separation of the nested supports gives central separation when $X$ is the same. Equation (111.12) bounds this remainder in $L^2$ by $C\epsilon_n\|F_{n,r}\|_2$. Hence the entire central commutator is uniformly bounded in $H^{-3/4}$. Horizontal commutators are bounded there already by the local $H^1$ estimate. No off-region term is dropped.

Here is the regularity and domain argument. Write

$$
K_{n,r}=-\Delta_X+k_{n,r}|D_t|^{2+\epsilon_n}+1.
$$

Its Fourier symbol $m=|\zeta|^2+k_{n,r}|\lambda|^{2+\epsilon_n}+1$ satisfies
$m\ge c\langle\zeta,\lambda\rangle^2$ uniformly. Consequently
$K_{n,r}^{-1}:H^{-3/4}\to H^{5/4}$ is uniformly bounded. On a neighborhood of the cutoff support, the differential difference $\mathcal L_r+\Delta_X$ is a symmetric divergence-form operator with coefficients and all needed derivatives $O(r)$, by the explicit $Y_{i,r}$ in (106.7). Multiply its coefficient matrix by a fixed smooth horizontal cutoff, equal to one there, to extend it to an operator $C_r$ on all $\mathbb R^4$. Its coefficients are bounded and

$$
\|C_r\|_{H^{5/4}\to H^{-3/4}}\le Cr.
\tag{111.14}
$$

This is the ordinary Sobolev multiplication bound for smooth bounded coefficients, followed by two distributional derivatives. The extended quadratic form differs from that of $K_{n,r}$ by at most $Cr\|h\|_{H^1}^2$. The free form of $K_{n,r}$ controls this norm uniformly, since $\lambda^2\le1+|\lambda|^{2+\epsilon_n}$. For sufficiently small $r_0$ the extended form is therefore coercive on its exact free domain.

The localized equation for $\theta F_{n,r}$ is now
$(K_{n,r}+C_r)(\theta F_{n,r})=G_{n,r}$,
with $\|G_{n,r}\|_{H^{-3/4}}\le C_\theta$. This follows from (111.11), the commutator estimates, and the harmless added term $\theta F_{n,r}$. Choose $r_0$ so that the norm of $K_{n,r}^{-1}C_r$ on $H^{5/4}$ is less than $1/2$. Its Neumann series produces a solution in $H^{5/4}$, with uniform norm. This solution belongs to the free form domain: $1+\epsilon_n/2<5/4$, so the isotropic $H^{5/4}$ norm controls both its ordinary first derivatives and its central $H^{1+\epsilon_n/2}$ norm. The given cutoff vector belongs to that same free form domain by (111.10). Their distributional equations extend to form tests by smooth density, since the forcing is in $H^{-3/4}$ and that free domain embeds continuously in $H^1$. Coercivity gives uniqueness there. The two solutions coincide, proving (111.6) without an operator-core assertion.

Finally, the scalar Fourier bound

$$
\sup_{\lambda\in\mathbb R}
 \frac{|\lambda|^2\bigl||\lambda|^\epsilon-1\bigr|}
      {\langle\lambda\rangle^{9/4}}
 \le C\epsilon,\qquad 0<\epsilon\le1/8,
\tag{111.15}
$$

follows from the mean value formula: on $|\lambda|\ge1$ use
$\epsilon\log|\lambda|\,|\lambda|^{\epsilon-1/4}$, and on $0<|\lambda|<1$ use $\epsilon|\lambda|^2|\log|\lambda||$. Its value at zero is zero. The full isotropic denominator is larger than this central denominator. Thus
$\|(p_\epsilon(D_t)-D_t^2)h\|_{H^{-1}}\le C\epsilon\|h\|_{H^{5/4}}$.
For $\theta=1$ near $\operatorname{supp}\chi$, apply it to $\theta F_{n,r}$. In the remaining input $(1-\theta)F_{n,r}$ the local $D_t^2$ term vanishes on $\operatorname{supp}\chi$, and (111.12) bounds the nonlocal term by $C\epsilon_n$ in $L^2$. This proves (111.7). The extra quarter derivative is essential here; no smallness from $H^1$ to $H^{-1}$ is asserted. $\square$

**Lemma 111.3 (a finite-cylinder inward estimate for every actual selection).** Write $H_n$ as in (111.4). There are finite constants $T_0,C$, depending only on the original data and fixed cutoff widths, such that for each fixed integer $T\ge T_0$, eventually

$$
\begin{aligned}
\int_{\{R_\kappa<e^{-(T+8)}\}}|v_n|^2d\mu
 &\le C\bigl(A_n(T)+B_n+\epsilon_n^2(1+\Lambda_n)\bigr)
       +\int_{\{R_\kappa<e^4\ell_n\}}|v_n|^2d\mu,\\
A_n(T)&=\int_{T-4}^{T+4}e^{-2\tau}
 \left(\|\partial_\tau H_n\|_2^2+\|H_n\|_{H^1(S^3)}^2\right)d\tau,\\
B_n&=\int_{\Lambda_n-4}^{\Lambda_n+4}e^{-2\tau}
 \left(\|\partial_\tau H_n\|_2^2+\|H_n\|_{H^1(S^3)}^2\right)d\tau.
\end{aligned}
\tag{111.16}
$$

For every such selection,

$$
B_n\to0,\qquad \epsilon_n^2(1+\Lambda_n)\to0,\qquad
\int_{\{R_\kappa<e^4\ell_n\}}|v_n|^2d\mu\to0.
\tag{111.17}
$$

The radius $e^{-(T+8)}$ is fixed before $n$ tends to infinity.

**Proof.** Use exactly the comparison angular realization $B$ of (109.3), (109.6), with
$\ker B=\mathbb Ce_0$ and $B|_{e_0^\perp}\ge2$. It is a comparison operator, not a global reducing channel for the original operator. Set $P_0=-\partial_\tau^2+B$. The already proved weighted inverse (109.15), at $\delta=1$, gives

$$
\|J\|_{\mathscr H^1_1}\le C_P\|P_0J\|_{\mathscr H^{-1}_1},\qquad
\|J\|_{\mathscr H^1_1}=\|e^{-\tau}J\|_{H^1(\mathbb R\times S^3)}.
\tag{111.18}
$$

The negative norm means $\|e^{-\tau}F\|_{H^{-1}}$, with multiplication understood distributionally, as in (109.14). The angular form norm of $B+1$ is equivalent to the ordinary $H^1(S^3)$ norm by §109. To recall why this particular weight is allowed, conjugation and Fourier transformation give the symbols
$\mu+\zeta^2-1-2i\zeta$. Their moduli are $\zeta^2+1$ for $\mu=0$, and at least $\zeta^2+\mu-1$ for $\mu\ge2$. They therefore dominate $c(1+\zeta^2+\mu)$, precisely the estimate needed between these two Sobolev spaces.

Consider a fixed-width cylinder slab centered at integer $j$, and put $r=e^{-j}$. Under (111.4), the form-normalized annular vector is
$h_{n,j}(X,t)=r\phi_n(rX,rt)=r^{-1}F_{n,r}(X,t)$.
The smooth annulus-to-slab maps and their inverses have bounded Sobolev norms independent of $j$. Comparing its exact equation (111.8) with the local endpoint equation gives

$$
\begin{aligned}
\|P_0H_n\|_{H^{-1}(I_j\times S^3)}
 &\le C\left(e^{-j/4}+|g_n-g_c|+|k_{n,e^{-j}}-1|\right)
             \|H_n\|_{H^1(I_j^+\times S^3)}
       +C\epsilon_ne^j.
\end{aligned}
\tag{111.19}
$$

Here $I_j=(j-1,j+1)$ and $I_j^+=(j-2,j+2)$ can be used; fixed nested cutoffs are understood in these local norms. The estimate holds uniformly for the finitely many slabs meeting $(T,\Lambda_n)$ and their fixed enlargements. Lemma 111.2 applies with a fixed $c_0<e^{-4}$, and $T_0$ is enlarged so that all their radii are below its $r_0$.

Every term in (111.19) has a specified origin. The horizontal coefficients give $O(r)$ in the local $H^1$ bilinear norm. The original thin-layer estimate (109.10)--(109.13), with exponent $1/4$, compares the full $W_r$ pairing with its trace pairing, giving $O(r^{1/4})$. It uses the exact marginal $1/(4\pi\kappa|X|)$ and $g_c/(4\pi a\kappa)=4/\pi$. The coefficient difference $g_n-g_c$ is bounded against the actual $W_r$ by the polarized annular form bound (106.9). The term $k_{n,r}-1$ multiplies the local $D_t^2$ form and is bounded by the local $H^1$ norm. The remaining varying-order term is (111.7), multiplied by bounded $k_{n,r}$ and by the exact amplitude $r^{-1}=e^j$. This proves the last term as written. All tests are compactly supported on the slab, then extended by $H^1$ density. No sign, cancellation or frequency-diagonal potential pairing has entered this estimate.

Take a real smooth $\chi_{T,n}$ supported in $(T,\Lambda_n)$, equal to one on $[T+1,\Lambda_n-1]$, with uniformly bounded first two derivatives. This is possible eventually for every fixed $T$. Put $J_n=\chi_{T,n}H_n$, extended by zero to the whole cylinder. Its support is finite and (111.10) gives local $H^1$, so $J_n\in\mathscr H^1_1$.

A fixed-overlap smooth partition of unity in $\tau$, multiplication by $e^{-\tau}$ and weighted Cauchy--Schwarz sum (111.19) to

$$
\begin{aligned}
\|P_0J_n\|_{\mathscr H^{-1}_1}
 &\le C d_n(T)\|J_n\|_{\mathscr H^1_1}
       +C\bigl(A_n(T)+B_n\bigr)^{1/2}
       +C\epsilon_n\sqrt{1+\Lambda_n},\\
d_n(T)&=e^{-T/4}+|g_n-g_c|+\epsilon_n(1+\Lambda_n).
\end{aligned}
\tag{111.20}
$$

For clarity, on each fixed-width slab the weighted negative norm is bounded by $Ce^{-j}$ times its unweighted negative norm. Pairing each localized residual with the correspondingly localized dual test, Cauchy--Schwarz and finite overlap bound the square of the global norm by the sum of these weighted squares. The absolute remainder in (111.19) therefore contributes
$C\sum_j e^{-2j}(\epsilon_ne^j)^2\le C\epsilon_n^2(1+\Lambda_n)$.
This accounts for the full growing interval, not only a fixed compact cutoff.

Only indices with $I_j$ meeting $(T,\Lambda_n)$ contribute to the localized residual. Their enlarged intervals lie in $(T-3,\Lambda_n+3)$. On $[T+1,\Lambda_n-1]$ one has $H_n=J_n$; all remaining parts of those enlarged intervals lie in the boundary strips of (111.16). Finite overlap therefore gives

$$
\sum_{j\ \mathrm{active}} e^{-2j}
 \|H_n\|_{H^1(I_j^+\times S^3)}^2
 \le C\left(\|J_n\|_{\mathscr H^1_1}^2+A_n(T)+B_n\right).
$$

Apply this bound to the relative errors after multiplying each localized residual by $\chi_{T,n}$, which is uniformly bounded on $H^{-1}$. This gives the first term of (111.20) and a boundary contribution bounded by its second term, since $d_n(T)$ is bounded eventually. Finally
$[P_0,\chi_{T,n}]H_n=-\chi_{T,n}''H_n-2\chi_{T,n}'\partial_\tau H_n$
is supported in those boundary strips and has that weighted negative-norm bound as well. These observations justify (111.20), including its localization terms.

Choose $T_0$ large enough and then $n$ large enough for each fixed $T\ge T_0$ that $CC_Pd_n(T)<1/2$, using (111.5). Absorb the first term with (111.18). Squaring yields

$$
\|J_n\|_{\mathscr H^1_1}^2
 \le C\bigl(A_n(T)+B_n+\epsilon_n^2(1+\Lambda_n)\bigr).
\tag{111.21}
$$

The weighted $L^2$ part controls the mass for $T+8<\tau<\Lambda_n-1$. The remaining mass above $\Lambda_n-1$ lies in $R_\kappa<e\ell_n$, hence in the final ball of (111.16). The exact mass identity (111.4) proves (111.16). This argument imposes no source boundary condition: the inner part is retained as an actual ball integral.

That ball has original central sections of length at most $2\kappa e^4\ell_n$. The all-choice short-section estimate (104.15) therefore proves its vanishing. More generally the same estimate and the exact Jacobian imply
$F_{n,\ell_n}\to0$ in $L^2$ on every fixed compact subset of $\mathbb R^4$. Lemma 111.2 bounds its nested annular cutoffs in $H^{5/4}$. The Fourier interpolation inequality
$\|h\|_{H^1}\le\|h\|_2^{1/5}\|h\|_{H^{5/4}}^{4/5}$
then gives strong $H^1$ convergence to zero on every fixed compact annulus. With $\tau=\Lambda_n+s$, (111.4) reads

$$
H_n(\Lambda_n+s,\omega)
 =\ell_n^{-1}e^{-s}F_{n,\ell_n}(e^{-s}\omega),\qquad
 e^{-2(\Lambda_n+s)}=\ell_n^2e^{-2s}.
\tag{111.22}
$$

The factors $\ell_n^{-1}$ and $\ell_n^2$ cancel in the squared weighted norm. On $|s|\le4$ this is precisely a bounded annulus-to-slab change of variables, so the just proved strong $H^1$ convergence gives $B_n\to0$. Finally $\epsilon_n^2(1+\Lambda_n)\to0$ follows from $\epsilon_n\Lambda_n\to0$ and $\epsilon_n\to0$. This proves (111.17). $\square$

**Theorem 111.4 (zero source defect and all-choice convergence).** At the unchanged original data,

$$
\begin{gathered}
\lim_{r\downarrow0}\limsup_{\sigma\downarrow2}
 \sup_{v\in\mathcal Z_\sigma}\int_{\{R_\kappa<r\}}|v|^2d\mu=0,\\
\lim_{\sigma\downarrow2}\sup_{v\in\mathcal Z_\sigma}
 \inf_{|z|=1}\|v-zw\|_2=0.
\end{gathered}
\tag{111.23}
$$

On every common state-and-measure subsequence of (110.24), its coefficient satisfies $|c|^2=1$, its source defect is $m_e=0$, and $v_n\to cw$ strongly in global original $L^2$. The infinity defect remains zero. In particular the explicit every-choice coefficient lower bound is $s=1$. For every selection, the full probability sequence converges narrowly on the original space, and also on its one-point compactification, to $|w|^2d\mu$. Its phases need not converge.

There is also a finite constant $C_1$, independent of the actual state and the fixed integer $T\ge T_0$, for which

$$
\lim_{\sigma\downarrow2}\sup_{v\in\mathcal Z_\sigma}
 \left[
 \int_{\{R_\kappa<e^{-(T+8)}\}}|v|^2d\mu
 -C_1\int_{\{e^{-(T+6)}<R_\kappa<e^{-(T-6)}\}}|v|^2d\mu
 \right]_+=0.
\tag{111.24}
$$

Here $[x]_+=\max\{x,0\}$; both radii and $T$ are fixed before the order limit. The comparison annulus lies outside the inner ball.

**Proof.** Start with an arbitrary actual selection and a common subsequence furnished by (110.24), with weak vector limit $cw$ and measure limit
$|c|^2|w|^2d\mu+(1-|c|^2)\delta_e$. On every fixed compact punctured annulus, Lemma 111.2 at a fixed sufficiently small $r$ gives a uniform $H^{5/4}$ bound for cutoffs of $\phi_n$. The already supplied strong local $L^2$ convergence, weak boundedness in $H^{5/4}$, and the interpolation inequality used above imply strong local $H^1$ convergence to $c\phi_w$. Hence, for every fixed $T\ge T_0$,

$$
A_n(T)\longrightarrow |c|^2A_w(T),
\tag{111.25}
$$

where $A_w$ uses the same linear chart and the same strip as in (111.16). The fixed original maximal solution $w$ satisfies the uniform annular Caccioppoli estimate (109.17). Integrating it over the eight unit slabs, and comparing the weight on each fixed-width interval, gives

$$
A_w(T)\le C_0\int_{T-6}^{T+6}
               e^{-2\tau}\|H_w(\tau)\|_2^2d\tau
 \longrightarrow0\quad(T\to\infty).
\tag{111.26}
$$

The constant $C_0$ is independent of sufficiently large $T$. The limit uses only $w\in L^2$ and (111.4), not its global kinetic energy.

Apply (111.16) with $T$ fixed and let $n\to\infty$. By (111.17), only (111.25) remains on its right. The sphere $R_\kappa=e^{-(T+8)}$ is null for the absolutely continuous part of the limiting measure and avoids its source atom. Weak probability convergence therefore gives

$$
1-|c|^2+|c|^2\int_{\{R_\kappa<e^{-(T+8)}\}}|w|^2d\mu
 \le C|c|^2A_w(T).
\tag{111.27}
$$

Let the integer $T$ tend to infinity and use (111.26). Since $|c|\le1$, this forces $1-|c|^2=0$. Thus every common refined subsequence has norm-one weak limit $cw$. Equality of the limiting and approximating Hilbert norms gives global strong convergence along that subsequence. All arguments applied to an arbitrary selection, including every vector of any actual kernel multiplicity.

If the second limit of (111.23) failed, one could select orders tending to $2$ and actual unit kernel vectors whose distance from the unit phase orbit stayed bounded below. The existing common subsequence and the just proved strong convergence to a unit phase multiple of $w$ contradict this. For any measurable $E$ and unit vector $v$, comparison with a unit phase $zw$ gives

$$
\left|\int_E|v|^2d\mu-\int_E|w|^2d\mu\right|
 \le\big\||v|^2-|w|^2\big\|_1
 \le2\|v-zw\|_2.
\tag{111.28}
$$

Taking the phase infimum and then $E=\{R_\kappa<r\}$ proves the first limit of (111.23), since the integral of $|w|^2$ over these shrinking balls tends to zero. It also proves total variation convergence of every actual probability selection to $|w|^2d\mu$, and hence the stated narrow convergence, independently of phases.

Finally, before sending $T$ to infinity, (111.16), (111.25) and (111.26) imply that the subsequential upper limit of the inner-ball mass is at most $CC_0$ times the limiting mass of the fixed comparison annulus in (111.24). Its two boundary spheres are also null for the limiting measure. Thus the positive part in (111.24) tends to zero along every common refinement, with $C_1=CC_0$. A violation of its uniform all-choice assertion would supply a contradicting sequence of orders and states. This proves (111.24) with the stated order of limits. $\square$

**Corollary 111.5 (the entire actual zero projection and the fixed detector).** For all sufficiently small positive $\sigma-2$,

$$
\dim_{\mathbb C}\ker H_\sigma=1,\qquad
\left\|P_\sigma-|w\rangle\langle w|\right\|_{L^2\to L^2}\longrightarrow0,
\qquad P_\sigma=\mathbf1_{\{0\}}(H_\sigma).
\tag{111.29}
$$

Retain the prescribed fixed exterior detector and its fixed positive weight,

$$
f=\frac{\chi_{j_0}w}{\|\chi_{j_0}w\|_2},\qquad
\beta=|\langle w,f\rangle|^2>0,\qquad
b_\sigma=\|P_\sigma f\|_2^2.
\tag{111.30}
$$

Here $\chi_{j_0}$ is the prescribed fixed exterior cutoff; it is separate from every annular or cylinder cutoff above. Equivalently the conclusion below holds for any already fixed unit detector $f$ with that nonzero overlap. In (111.30) $b_\sigma$ denotes the zero-atom weight, distinct from the sufficient coupling bound denoted by the same letter in (103.5). Then

$$
b_\sigma\longrightarrow\beta>0,\qquad
b_\sigma\ge\beta/2\quad\hbox{for all sufficiently small }\sigma-2>0.
\tag{111.31}
$$

**Proof.** Attainment makes every kernel nonzero. If dimensions at least two occurred along orders tending to $2$, the linear functional $v\mapsto\langle w,v\rangle$ would have a nonzero kernel on each such eigenspace. Choose a unit vector there. Its distance from every unit phase multiple of $w$ is $\sqrt2$, contradicting the uniform all-choice limit (111.23). Thus the kernels are one dimensional near $2$, with no prior simplicity premise.

For unit spanning vectors $v_\sigma$, choose phases $z_\sigma$ realizing the phase distance, which tends to zero. The rank-one identity and the triangle inequality give

$$
\bigl\||v_\sigma\rangle\langle v_\sigma|
             -|w\rangle\langle w|\bigr\|
 \le2\|v_\sigma-z_\sigma w\|_2\longrightarrow0.
$$

These are the actual spectral projections onto the entire zero eigenspaces. Applying them to the unchanged $f$ yields (111.31); for example
$|b_\sigma-\beta|=|\langle f,(P_\sigma-|w\rangle\langle w|)f\rangle|
\le\|P_\sigma-|w\rangle\langle w|\|$.
This is a zero spectral atom assertion. No inference from a positive fixed spectral shift or a resolvent response is used. $\square$

**Definition 111.6 (supplier correspondence and mathematical limits).** The original field, raw Haar marginal and homogeneous bound are exactly Proposition 82.4, (82.8)--(82.10), (103.8) and (106.8). Their correspondence to Folland, [*Subelliptic estimates and function spaces on nilpotent Lie groups*, doi:10.1007/BF02386204](https://doi.org/10.1007/BF02386204), Theorem 3.1 and Proposition 3.17 at order $2$, retains the original sub-Laplacian and clock on homogeneous dimension $5$. Its actual central marginal is $(4\pi|\xi|)^{-1}$; after the fixed chart and zoom it is $(4\pi\kappa|X|)^{-1}$. No explicit H-type Green formula is inserted.

The actual attained full-complex form equation, $g_n\to g_c$, $M_n\to0$ and the subexponential restriction are §§101--103. The whole-line localization and short-central-section estimate are (104.9), (104.15); exterior strong compactness and zero infinity defect are Theorem 105.1. The exact zoom domain and local bounds are (106.13)--(106.16). The thin-layer bilinear estimate, angular gap, weighted comparison inverse and maximal Caccioppoli estimate are (109.7), (109.10)--(109.17). The generator and common subsequence are Theorem 110.2 and (110.24). The new original-family deductions are (111.6)--(111.7), their finite-cylinder consumer (111.16)--(111.17), and the actual source, state and zero-projection conclusions (111.23)--(111.31).

The auxiliary angular profile retains the Alvino--Ferone--Volpicelli correspondence in [*Sharp Hardy inequalities in the half space with trace remainder term*, arXiv:1105.0335v1, Theorem 1.1, (8) and (12)](https://arxiv.org/html/1105.0335v1). At $n=4$, $\beta_{\rm AFV}=2$, the bulk term vanishes, the constant is $2/\pi$ per halfspace, and (12) is proportional to $|\xi|^{-1}\arctan(|\xi|/t)$. The normalization $2/\pi$ and even reflection give exactly (109.3). Its real halfspace theorem supplies only the existing comparison ingredient; the complex forms, original thin-layer error and weighted inverse used here are the separately proved repository results.

The fractional singular integral and Fourier symbol used in (111.12) are mature methods, as in Di Nezza--Palatucci--Valdinoci, [*Hitchhiker's guide to the fractional Sobolev spaces*, arXiv:1104.4345v3, §3, (3.1)--(3.2), Proposition 3.8](https://arxiv.org/html/1104.4345v3). The parameters here are dimension one and their fractional power $s=\epsilon/2$, so their $C(1,s)$ is exactly $c_\epsilon$. Applying the local second derivative gives order $2+\epsilon$ only off the separated support; the $O(\epsilon)$ coefficient, unbounded-support Schur bound and actual residual consumer are proved in (111.12)--(111.15). Their fixed-order definition alone is not a varying-order localized estimate.

One-dimensional Sobolev embedding, Fourier interpolation, multiplication by smooth coefficients, Neumann inversion, form uniqueness and elementary projection geometry are mature intermediates. Closed-form representation retains the correspondence with Teschl, [*Mathematical Methods in Quantum Mechanics*, §2.3, Theorem 2.13](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), on the actual nonnegative closed $q_\sigma$. It does not identify maximal and Friedrichs domains or assert an original operator core. The estimates and their original-family composition above are repository-derived; no worldwide novelty claim is attached.

The nonconclusions concerning $c$, source tightness and actual zero multiplicity in Definitions 109.4 and 110.4 are resolved by Theorem 111.4 and Corollary 111.5 to exactly their stated extent. Arbitrary phases remain unrestricted. There is no asserted rate for $M_\sigma$, state or projection convergence, or for any kinetic or potential resource scale. In fact (103.21)--(103.22) still give divergent kinetic totals and concentrated normalized resource measures, despite the unweighted probability convergence above. Strong $L^2$ convergence does not put $w$ in $\mathcal Q_c$ or imply endpoint energy convergence. No all-state source-supported gap, global Bessel reduction, source boundary condition, native realization or physical spatial-dimension conclusion is supplied.

## 追加锚（本行以下为增补区）

## 112. The original maximal-domain selector and the full endpoint propagation limit

**Definition 112.1 (original operators and source coefficients).** Retain the original complex Hilbert space $\mathcal H=L^2(G,d\mu;\mathbb C)$, group, raw Lebesgue Haar measure, unit-source field $\Gamma$, horizontal generator, central units and clock of (111.1). Fix the same $a,\eta>0$. Throughout this section

$$
\begin{gathered}
S=(aL+\eta D_w^2-g_c\Gamma)|_{\mathcal D_0},\qquad
\mathcal D_0=C_c^\infty(G\setminus\{e\};\mathbb C),\qquad
g_c=16\sqrt{a\eta},\\
F=H_F,\qquad D(F^{1/2})=\mathcal Q_c,\qquad
w=w_*/\|w_*\|_2,\qquad \ker S^*=\mathbb Cw.
\end{gathered}
\tag{112.1}
$$

Here $F$ and $w_*$ are exactly those of §§87.4 and 110.2; in particular $F\ge0$, $\ker F=\{0\}$, $w\notin\mathcal Q_c$ and $B_{\rm src}(w_*)=1$. The construction of this global $L^2$ vector uses the compactly supported original $L^2$ range assertion (110.15), including compact sources meeting $e$. Its inverse is not a bounded inverse on all of $\mathcal H$.

Use the unitary chart $u\mapsto f_u$, cylinder function $H_u$, angular vector $e_0$, angular operator $B$ and weighted spaces of (109.1)--(109.15), for any original $L^2$ vector. The notation $H_h$ for an $L^2$ forcing $h$ denotes this same coordinate transform; it makes no differentiability assertion about $h$. The inner product is antilinear in its first argument. Write $\overline S$ for the operator graph closure of $S$.

**Theorem 112.2 (full original maximal domain and the derived selector).** The coefficient maps of Theorem 109.2 extend uniquely to complex-linear maps $A,C:D(S^*)\to\mathbb C$ such that, for every $u\in D(S^*)$ and all sufficiently large $T$,

$$
H_u=(A(u)+\tau C(u))e_0+Z_u,\qquad
 e^{\tau/8}Z_u\in H^1((T,\infty)\times S^3).
\tag{112.2}
$$

On $\ker S^*$, $C=B_{\rm src}$. In the original domains one has

$$
\begin{gathered}
D(F)=\{u\in D(S^*):C(u)=0\},\qquad
D(S^*)=D(F)\dotplus\mathbb Cw,\\
\langle u,S^*v\rangle-\langle S^*u,v\rangle
 =a\bigl(\overline{C(u)}A(v)-\overline{A(u)}C(v)\bigr)
 \quad(u,v\in D(S^*)).
\end{gathered}
\tag{112.3}
$$

The number $\rho=A(w)/C(w)$ is real and is fixed by the original global vector $w$, with $C(w)=\|w_*\|_2^{-1}\ne0$. Define

$$
D(T)=\mathcal D_0\dotplus\mathbb Cw,\qquad
T(\phi+cw)=S\phi.
\tag{112.4}
$$

This densely defined nonnegative operator is essentially self-adjoint. Its closure $H_{\rm end}$ has the following equivalent actual maximal-domain selectors:

$$
\begin{aligned}
D(H_{\rm end})
 &=\{u\in D(S^*):\langle w,S^*u\rangle=0\}\\
 &=\{u\in D(S^*):A(u)=\rho C(u)\}\\
 &=D(\overline S)\dotplus\mathbb Cw,\qquad
 H_{\rm end}u=S^*u,\\
D(\overline S)
 &=\{y\in D(F):\langle w,Fy\rangle=0\}
  =\{u\in D(S^*):A(u)=C(u)=0\}.
\end{aligned}
\tag{112.5}
$$

In particular $H_{\rm end}\ge0$, $\ker H_{\rm end}=\mathbb Cw$, and $H_{\rm end}\ne F$. Neither $\rho$ nor a deficiency dimension is an input to these assertions.

**Proof.** Put $h=S^*u\in\mathcal H$. The original uniformly elliptic symbol (108.4), smooth coefficients and locally bounded potential off $e$ give $u\in H^2_{\rm loc}(G\setminus\{e\})$. This is the inhomogeneous local regularity in Shubin, [*Essential self-adjointness for semi-bounded magnetic Schrödinger operators on non-compact manifolds*, arXiv:math/0007019v1, Lemma 5.1](https://arxiv.org/html/math/0007019v1), with zero magnetic form, the dual metric (108.4) and the original smooth positive measure. The local hypotheses hold on the punctured manifold; no complete-manifold theorem is applied there.

First extend the exterior argument of §108 to this forcing. For a compact real punctured cutoff $f$, the complex product rule, local smooth approximation and real parts give

$$
q_c[fu]=\operatorname{Re}\langle f^2u,h\rangle
       +\int\mathcal C[f]|u|^2d\mu,\qquad
\mathcal C[f]=a\sum_i|X_if|^2+\eta|\partial_wf|^2.
\tag{112.6}
$$

This is precisely the cutoff identity in Shubin's (5.3), now retaining its forcing term. Let $\zeta$ be a smooth exterior cutoff, zero near $e$, one outside a compact set, and $0\le\zeta\le1$. Insert $f=\zeta\chi_H$, with the original Carnot cutoffs of (108.7). The forcing term is bounded by $\|u\|_2\|h\|_2$. The $d\zeta$ term has bounded compact support, and the $d\chi_H$ cost tends to zero. Nonnegativity and the boundedness of $\Gamma$ on $\operatorname{supp}\zeta$ therefore bound

$$
\|\zeta\chi_Hu\|_2^2+K[\zeta\chi_Hu]
 \le C_\zeta\bigl(\|u\|_2^2+\|u\|_2\|h\|_2\bigr).
\tag{112.7}
$$

The compact exhaustion and product-rule passage used in (108.8)--(108.9) now apply: the distributional free derivatives of $\zeta u$ are square integrable, and $\zeta\chi_Hu\to\zeta u$ in $\mathcal E_2$. Consequently
$\zeta u\in\mathcal E_2\subset\mathcal Q_c$. This assertion holds for every $u\in D(S^*)$, without separate integrability of its uncut kinetic or potential expressions.

Next establish the source expansion with this same $h$. On nested fixed zoom annuli, testing the scaled equation by a real cutoff squared times the scaled $u$ gives the proof of (109.17) with one extra $L^2$ forcing term. Its scaled forcing is $a^{-1}r^3f_h(r\,\cdot)$, where $r=e^{-j}$. Estimate (106.9) absorbs the potential into the central kinetic term, and the uniformly bounded shear coefficients control the remaining full gradient. Cauchy--Schwarz on the forcing term and the physical/cylinder Jacobian give

$$
\|H_u\|_{H^1((j,j+1)\times S^3)}
 \le C\left(\|H_u\|_{L^2((j-2,j+3)\times S^3)}
       +e^{-2j}\|H_h\|_{L^2((j-2,j+3)\times S^3)}\right).
\tag{112.8}
$$

Here and below constants may depend on the fixed original $a,\eta$ and fixed annuli, not on large $j$. Indeed the zoom equation has kinetic coefficient one after division by $a$, source multiplier $16\kappa W_r$, and forcing as displayed; the scaled annular $L^2$ norm of $r^3f_h(r\,\cdot)$ is comparable to $r^2$ times the cylinder $L^2$ norm of $H_h$. This verifies the factor in (112.8).

For each $v\in\{u,h\}$ the exact physical identity gives
$\int_T^\infty e^{-2\tau}\|H_v(\tau)\|_2^2d\tau<\infty$.
Multiply the square of (112.8) by $e^{-2j}$ and sum with finite overlap. Thus $H_u\in\mathscr H^1_1$ on the positive end. If $\chi$ is zero below a fixed large $T+1$ and one above $T+2$, the zero extension $J=\chi H_u$ satisfies, for the same extended error operator $E$ as in (109.18),

$$
(P_0+E)J=F_0+G,\qquad
P_0=-\partial_\tau^2+B,\qquad
G=a^{-1}\chi e^{-2\tau}H_h,
\tag{112.9}
$$

where $F_0\in H^{-1}$ has compact cylinder support. The factor $e^{-2\tau}$ follows directly by multiplying the transformed original equation by $R^3$: $f_u=R^{-1}H_u$, whereas its right side is $a^{-1}R^3f_h=a^{-1}R^2H_h$. In particular

$$
\|e^\tau G\|_{L^2}
 \le a^{-1}\|\chi e^{-\tau}H_h\|_{L^2}<\infty.
\tag{112.10}
$$

Thus $G\in\mathscr H^{-1}_{-1}$ and, by its lower support bound, in every $\mathscr H^{-1}_\delta$ with $\delta\ge-1$. No derivative of $h$ is used.

Apply the already proved error improvement (109.14), inverse (109.15) and inverse-difference identity (109.16) to (112.9). Starting with $J\in\mathscr H^1_1$, successive positive weights
$1,7/8,6/8,\ldots,1/8$ give the same vector, since no angular exponent lies between them. At the last step $EJ\in\mathscr H^{-1}_{-1/8}$ and (112.10) puts the forcing there too. Crossing from $1/8$ to $-1/8$ adds exactly $(A+\tau C)e_0$. The negative-weight remainder belongs to $\mathscr H^1_{-1/8}$. Restriction to the positive end proves (112.2). Uniqueness of an affine term modulo that remainder proves linearity and agreement with (109.4) on $\ker S^*$.

If $C(u)=0$, use the source cutoff $\eta_0$ and logarithmic cutoffs $\theta_N$ from the last paragraph of the proof of Theorem 109.2. This part of that argument depends only on the expansion, not on a homogeneous equation. For $H_u=A(u)e_0+Z_u$, $Be_0=0$ gives a model energy bound independent of $N$: the constant component's remote transition costs at most $C|A(u)|^2/N$, and the decaying remainder has finite $H^1$ energy. The error (109.13) is bounded because $\sum_{j\ge T}e^{-j/4}<\infty$. Hence the original compact punctured vectors with cylinder functions $\eta_0\theta_NH_u$ have bounded $\mathcal Q_c$ norm and converge in physical $L^2$ to the source part of $u$. Weak compactness of this complete form space puts that part in $\mathcal Q_c$. Its exterior complement belongs to $\mathcal E_2$ by (112.7). Thus $u\in\mathcal Q_c$.

For any $u\in\mathcal Q_c\cap D(S^*)$, core approximation in the second form slot gives
$\overline q_c(\phi,u)=\langle S\phi,u\rangle=\langle\phi,h\rangle$ for $\phi\in\mathcal D_0$. Form density extends this identity to every $\phi\in\mathcal Q_c$. Closed-form representation, as in Teschl, [*Mathematical Methods in Quantum Mechanics*, authorized online edition, version February 12, 2009, Theorem 2.13](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), therefore gives $u\in D(F)$ and $Fu=h$. Conversely, $u\in D(F)\subset\mathcal Q_c$ satisfies (110.9). Applying (112.2), its square-integrable cylinder derivative forces $C(u)=0$. We have proved the first equality in (112.3). Since $C(w)\ne0$, subtraction of $C(u)w/C(w)$ proves the direct decomposition there.

We justify the boundary pairing, including both ends of the original space. On punctured compact coordinate regions, local $H^2$ regularity permits the ordinary weak Green identity. The potential is real and cancels. At infinity insert the Carnot cutoffs $\chi_H$; (112.7) gives square-integrable free derivatives for both vectors there, while (108.7) bounds the cutoff differentials by quantities tending to zero. Cauchy--Schwarz makes all outer error terms tend to zero. The remaining $L^2$ pairings converge because $S^*u,S^*v,u,v\in\mathcal H$.

At the inner sphere $R=e^{-\tau}$ the unitary chart makes the free principal matrix $a(I+O(R))$, by (109.8). The inward normal of its exterior is $-\partial_R$. For the Euclidean part the flux is exactly

$$
a\bigl(\langle\partial_\tau H_u,H_v\rangle_{S^3}
             -\langle H_u,\partial_\tau H_v\rangle_{S^3}\bigr).
\tag{112.11}
$$

The additional flux is bounded by $Ce^{-\tau}$ times the product of the slice norms of $H_u,H_v$ and their radial and angular first derivatives. To evaluate it rigorously, the two weighted remainder estimates in (112.2) allow a common sequence $\tau_j\in(j,j+1)$ on which

$$
\|Z_u(\tau_j)\|_{H^1(S^3)}+
\|\partial_\tau Z_u(\tau_j)\|_2+
\|Z_v(\tau_j)\|_{H^1(S^3)}+
\|\partial_\tau Z_v(\tau_j)\|_2
 \le C_{u,v}e^{-j/8}.
\tag{112.12}
$$

Choose such slices also among the full-measure radii where the weak Green identity holds. The remaining affine slice norms grow at most linearly in $j$. Hence the additional flux tends to zero, and substitution in (112.11) gives the second line of (112.3). The interior integrals have the same limit along these radii by their global $L^1$ bounds, so this computes the full boundary pairing. In particular applying it to $u=v=w$ proves $\rho\in\mathbb R$, and applying it with $u=w$ proves equivalence of the first two selectors in (112.5).

It remains to establish the operator core rather than impose an extension. The sum in (112.4) is direct because $w\notin\mathcal Q_c$. For $\phi\in\mathcal D_0$, $\langle w,S\phi\rangle=0$, so $T$ is symmetric and
$\langle\phi+cw,T(\phi+cw)\rangle=\langle\phi,S\phi\rangle\ge0$.
Its adjoint is obtained directly by testing against $\mathcal D_0$ and then $w$:

$$
D(T^*)=\{u\in D(S^*):\langle w,S^*u\rangle=0\},
\qquad T^*u=S^*u.
\tag{112.13}
$$

Write $u=y+cw$ and $v=z+dw$ using (112.3). Membership in this adjoint domain says $\langle w,Fy\rangle=\langle w,Fz\rangle=0$. Therefore

$$
\langle u,T^*v\rangle=\langle y,Fz\rangle
 =\langle Fy,z\rangle=\langle T^*u,v\rangle.
\tag{112.14}
$$

Thus $T^*$ is symmetric. Since $T$ is densely defined and symmetric, adjoint reversal gives
$\overline T=T^{**}\subset T^*\subset T^{**}$; hence $T^*=\overline T$ is self-adjoint. Its nonnegativity follows by graph closure of $T$. This proves essential self-adjointness and the first two selectors.

For completeness, $D(\overline S)\subset D(F)$ and $\langle w,Fy\rangle=0$ on that domain. Conversely let $y\in D(F)$ have this pairing zero. For every $z+cw\in D(S^*)$, the decomposition (112.3) gives
$\langle S^*(z+cw),y\rangle=\langle Fz,y\rangle=\langle z+cw,Fy\rangle$.
The definition of $(S^*)^*=\overline S$ puts $y$ in $D(\overline S)$. This proves its first description in (112.5), and (112.3) with $C(w)\ne0$ gives its two-zero-coefficient description. Equations (112.13) and (112.3) now give $D(H_{\rm end})=D(\overline S)\dotplus\mathbb Cw$. As $\mathcal D_0$ is a graph core of $\overline S$, $\mathcal D_0+\mathbb Cw$ is a graph core of this actual self-adjoint $H_{\rm end}$. Its kernel is $\ker S^*=\mathbb Cw$, whereas $\ker F=\{0\}$. $\square$

**Corollary 112.3 (the original negative-defect test).** For the same original maximal operator,

$$
\begin{gathered}
n=w-(F+I)^{-1}w,\qquad
\ker(S^*+I)=\mathbb Cn,\\
\langle w,n\rangle
 =\int_{[0,\infty)}\frac{\lambda}{\lambda+1}\,d\nu_w^F(\lambda)>0,
\qquad
\ker(S^*+I)\cap w^\perp=\{0\}.
\end{gathered}
\tag{112.15}
$$

Here $\nu_w^F$ is the spectral measure of the unit vector $w$ for $F$. These are conclusions for the original operator, not assumptions inferred from its zero-kernel rank.

**Proof.** If $u=y+cw$ is the decomposition (112.3), then $(S^*+I)u=0$ is exactly $(F+I)y=-cw$, so $u=cn$. Direct computation also gives $S^*n=-n$. The spectral formula in (112.15) follows from $n=F(F+I)^{-1}w$. Its integral is strictly positive because $\|w\|_2=1$ and $\ker F=\{0\}$. It follows that $n\ne0$ and no nonzero vector of that line is orthogonal to $w$. Only the bounded shifted resolvent $(F+I)^{-1}$ is used. $\square$

**Theorem 112.4 (the actual full endpoint and fixed-time propagation).** Let $H_\sigma$ be exactly the nonnegative self-adjoint operator of (111.2), on the entire original complex form domain $\mathcal E_\sigma$, at its actual critical coupling $g_\sigma$. For every sequence $\sigma_n>2$ tending to $2$, without monotonicity, every $f\in\mathcal H$, every $z\in\mathbb C\setminus\mathbb R$ and every $r>0$,

$$
\begin{gathered}
(H_{\sigma_n}-z)^{-1}f\longrightarrow(H_{\rm end}-z)^{-1}f,\\
(H_{\sigma_n}+r)^{-1}f\longrightarrow(H_{\rm end}+r)^{-1}f
 \qquad\text{in }\mathcal H.
\end{gathered}
\tag{112.16}
$$

For every fixed allowed time the full actual propagators satisfy

$$
\begin{aligned}
e^{-itH_{\sigma_n}}f&\longrightarrow e^{-itH_{\rm end}}f
 &&(t\in\mathbb R),\\
e^{-tH_{\sigma_n}}f&\longrightarrow e^{-tH_{\rm end}}f
 &&(t\ge0),
\end{aligned}
\qquad\text{strongly in the same }\mathcal H.
\tag{112.17}
$$

Each assertion also holds with inputs $f_n\to f$ in $\mathcal H$ on the left. No sign, phase, symmetry or simplicity premise is imposed on states. The endpoint and its selector are those derived in Theorem 112.2. These statements assert strong convergence for each fixed time and input; they contain no operator-norm estimate, rate or uniform assertion for growing times.

**Proof.** The existing actual-family result (111.29) gives
$P_\sigma\to P_w=|w\rangle\langle w|$ in operator norm, where $P_\sigma=\mathbf1_{\{0\}}(H_\sigma)$ is the entire actual zero projection. In particular, for all sufficiently large $n$,

$$
w_n=\frac{P_{\sigma_n}w}{\|P_{\sigma_n}w\|_2}
 \in D(H_{\sigma_n}),\qquad
H_{\sigma_n}w_n=0,\qquad w_n\to w.
\tag{112.18}
$$

The denominator tends to one. This chooses graph approximants from already proved actual kernels; it assumes neither a phase for an arbitrary actual state nor a boundary law for $H_\sigma$.

For $\phi\in\mathcal D_0$, smooth compact support gives membership in every finite-order central operator domain and $L\phi\in\mathcal H$. Also $\Gamma\phi\in\mathcal H$, since its support avoids $e$. Integration by parts and central spectral calculus on the full form domain therefore give

$$
\begin{gathered}
\phi\in D(H_\sigma),\qquad
H_\sigma\phi=aL\phi+\eta|D_w|^\sigma\phi-g_\sigma\Gamma\phi,\\
H_{\sigma_n}\phi\longrightarrow S\phi\quad\text{in }\mathcal H.
\end{gathered}
\tag{112.19}
$$

For the limit, $g_{\sigma_n}\to g_c$ is (103.4). Central Plancherel and dominated convergence give $|D_w|^{\sigma_n}\phi\to D_w^2\phi$: eventually $2<\sigma_n\le3$, and the squared Fourier difference is bounded by $C(1+|\lambda|^6)|\widehat\phi(\xi,\lambda)|^2$, an integrable function. The potential form pairing is the ordinary $L^2$ pairing with $\Gamma\phi$; no bound on $\Gamma$ at the puncture is asserted.

For every $v=\phi+cw$ in the graph core $D(T)$ of Theorem 112.2, take $v_n=\phi+cw_n$. Equations (112.18)--(112.19) give

$$
v_n\to v,\qquad H_{\sigma_n}v_n\to S\phi=H_{\rm end}v
 \quad\text{in }\mathcal H.
\tag{112.20}
$$

Apply only the abstract varying-vector graph-core criterion, Lemma 13.1 of [*Native spatial cap retained and resonant limits*](FIB_NATIVE_SPATIAL_CAP_RETAINED_AND_RESONANT_LIMITS.md#13-common-weighted-cylinder-spaces-and-the-graph-core-criterion), with its $H_j=H_{\sigma_n}$, $H=H_{\rm end}$ and $\mathcal D=D(T)$. Both operators are self-adjoint on the same $\mathcal H$, the graph-core hypothesis is proved above, and (112.20) is its full approximation hypothesis. This proves the nonreal part of (112.16). For $z=-r$, the identical dense-range argument in that lemma uses the common nonnegative bound $\|(H_{\sigma_n}+r)^{-1}\|\le1/r$ and the onto map $H_{\rm end}+r$; it proves the second part. No native operator, domain decomposition or source law from that volume is transferred.

For the propagation passage use the mature continuous functional calculus under strong resolvent convergence, Teschl, [*Mathematical Methods in Quantum Mechanics*, Theorem 6.31 and Corollary 6.33](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), on the common full Hilbert space. Its unitary function is $\lambda\mapsto e^{-it\lambda}$, bounded and continuous for each fixed real $t$. For $t\ge0$ the heat function on the common spectra $[0,\infty)$ is bounded and continuous; equivalently extend it to the bounded continuous function $\lambda\mapsto e^{-t\max(\lambda,0)}$ on $\mathbb R$. Thus all hypotheses, including the common lower bound for heat propagation, are satisfied.

Explicitly, this strong-calculus passage requires no tail regularity of $f$. For a continuous compact spectral cutoff $0\le\chi_R\le1$ equal to one on $[-R,R]$, strong resolvent convergence gives both $\chi_R(H_{\sigma_n})f\to\chi_R(H_{\rm end})f$ and $(b\chi_R)(H_{\sigma_n})f\to(b\chi_R)(H_{\rm end})f$ for each bounded continuous propagation function $b$. Moreover

$$
\limsup_{n\to\infty}\|(1-\chi_R(H_{\sigma_n}))f\|_2
 \le\|(1-\chi_R(H_{\rm end}))f\|_2\longrightarrow0
 \quad(R\to\infty).
\tag{112.21}
$$

The uniform bound on $b$ controls the discarded tails. This proves (112.17), including $t=0$. Resolvent bounds, unitary norm one and heat contraction norm at most one then absorb $f_n-f$, proving the varying-input statements.

The local regularity and cutoff supplies used above are exactly Shubin's Lemma 5.1 and (5.3), matched to (108.4) and the raw Haar measure, not his complete-manifold essential self-adjointness theorem. The original thin-layer error, angular gap and weighted inverse are (109.7), (109.13)--(109.16); the forcing factor and its admissible weight in (112.9)--(112.10) establish their use on the full maximal domain. The global generator retains the compact-source range proof (110.15) and the source-domain restriction (110.9). Closed-form representation and strong continuous functional calculus retain the exact Teschl correspondences stated in the proofs. These mature intermediates do not supply the original domain selectors or the actual graph approximants without those original-field arguments.

In [*A Survey on the Krein--von Neumann Extension*, arXiv:1203.5713v1, Theorem 2.1, (2.9)--(2.11)](https://arxiv.org/html/1203.5713v1), the displayed domain decompositions assume $S\ge\varepsilon I$, $\varepsilon>0$. That hypothesis is absent here by §87.4. The decomposition (112.3), selectors (112.5) and negative-defect line (112.15) have instead been derived directly for the original zero-gap problem. The use of these methods here retains the original $S$, $F$ and $w$ throughout. $\square$

## 追加锚（本行以下为增补区）

## 113. Full-unit-input norm resolvents of the actual critical family

**Definition 113.1 (fixed original responses).** Retain the original group, raw Haar measure, unit-source field, horizontal generator and clock, central spectral units, fixed $a,\eta>0$, entire complex form domains and actual critical couplings of (111.1)--(111.3). Write $D=D_w$ and

$$
\begin{gathered}
\mathcal H=L^2(G,d\mu;\mathbb C),\quad
A_\sigma=aL+\eta|D_w|^\sigma,\quad
Q_{\sigma,r}=(A_\sigma+r)^{-1},\\
R_{\sigma,r}=(H_\sigma+r)^{-1},\qquad
R_{{\rm end},r}=(H_{\rm end}+r)^{-1},\qquad r>0.
\end{gathered}
\tag{113.1}
$$

Here $H_{\rm end}$ is precisely the actual selector (112.5), including its zero mode; $Q_{2,r}$ is a free resolvent and $R_{{\rm end},r}$ is not the Friedrichs resolvent. Use the linear unitary chart, $\kappa=\sqrt{\eta/a}$, $R_\kappa$, cylinder function $H_u$ and angular operator $B$ of §§109 and 112. The notation $f_u$ denotes the unitary coordinate transform of $u$, so $H_u(\tau,\omega)=e^{-\tau}f_u(e^{-\tau}\omega)$. All limits $\sigma\downarrow2$ allow arbitrary sequences from above. The source-specific statements below are repo-derived ordinary deductions; the previously proved domain, zero-projection and strong-resolvent statements of §§110--112 are suppliers.

**Lemma 113.2 (subexponential moments on bounded actual energy balls).** For fixed $N,B_0>0$ put
$\mathcal B_\sigma=\{u\in\mathcal E_\sigma:\|u\|_2\le N,\ q_\sigma[u]\le B_0\}$ and $\epsilon=\sigma-2$. Then

$$
\lim_{\sigma\downarrow2}\ \sup_{u\in\mathcal B_\sigma}
 \epsilon\log(1+D_\sigma[u])=0.
\tag{113.2}
$$

For every fixed $b>0$, $D_{b\epsilon}[u]$ is uniformly bounded on these balls for orders sufficiently close to $2$. No uniform bound on $D_2$, $D_\sigma$ or $T$ is asserted.

**Proof.** The original same-field inequality (87.3), completion of the square in $\sqrt{T[u]}$, and the spectral interpolation (87.12) give, with $t=D_\sigma[u]$,

$$
q_\sigma[u]\ge\eta t-J_\sigma D_2[u]
 \ge\eta t-J_\sigma N^{2\epsilon/\sigma}t^{2/\sigma},
\qquad J_\sigma=\frac{g_\sigma^2}{256a}\longrightarrow\eta.
\tag{113.3}
$$

The last convergence is exactly Theorem 103.2, with no rate. For any fixed $M>B_0/\eta$, $t\ge M$ implies

$$
t^{\epsilon/\sigma}\le
 \frac{J_\sigma N^{2\epsilon/\sigma}}{\eta-B_0/M}.
\tag{113.4}
$$

For $t<M$, $\epsilon\log(1+t)\le\epsilon\log(1+M)$. For $t\ge M$, (113.4) bounds its upper limit, uniformly in $u$, by $2\log(\eta/(\eta-B_0/M))$. Let $M\to\infty$ to prove (113.2). In particular each supremum is finite. For $b\epsilon\le\sigma$, spectral Hölder gives
$D_{b\epsilon}[u]\le t^{b\epsilon/\sigma}N^{2-2b\epsilon/\sigma}$; (113.2) proves the stated boundedness. The zero vector is included by continuity. $\square$

**Lemma 113.3 (forced source tightness on the whole input ball).** For every fixed $r>0$,

$$
\lim_{s\downarrow0}\limsup_{\sigma\downarrow2}
 \sup_{\|f\|_2\le1}
 \int_{\{R_\kappa<s\}}|R_{\sigma,r}f|^2d\mu=0.
\tag{113.5}
$$

For every sequence $\sigma_n\downarrow2$ and bounded inputs $f_n$, the corresponding responses are relatively compact in $L^2$ after multiplication by any bounded compactly supported function. The inputs may vary with the order and meet the source.

**Proof.** By amplitude scaling it suffices to use $\|f_n\|_2\le1$. Put $u_n=R_{\sigma_n,r}f_n$, $h_n=H_{\sigma_n}u_n=f_n-ru_n$, $g_n=g_{\sigma_n}$, $\epsilon_n=\sigma_n-2$ and $t_n=D_{\sigma_n}[u_n]$. Nonnegative spectral calculus gives

$$
\|u_n\|_2\le r^{-1},\qquad
\|h_n\|_2\le1,\qquad
q_{\sigma_n}[u_n]\le(4r)^{-1}.
\tag{113.6}
$$

Thus Lemma 113.2 applies. Choose an auxiliary inner radius, depending on this response only for the proof,

$$
d_n=\frac{\exp(-\epsilon_n^{-1/2})}{1+t_n},\qquad
\Lambda_n=\log(1/d_n),\qquad
\epsilon_n\Lambda_n\longrightarrow0.
\tag{113.7}
$$

There is no change of the actual operator or its units. For a measurable set $E$ with central sections of length at most $C d_n$, the one-dimensional inequality $\|v\|_\infty^2\le2\|v\|_2\|v'\|_2$, integrated in $\xi$, gives

$$
\int_E|u_n|^2d\mu
 \le2Cd_n\|u_n\|_2\sqrt{D_2[u_n]}
 \le C_r\frac{e^{-\epsilon_n^{-1/2}}t_n^{1/\sigma_n}}{1+t_n}
 \longrightarrow0.
\tag{113.8}
$$

This applies in $w$ or in the sheared coordinate $s$, since their sections differ by translation. Unlike (104.15), (113.8) uses no critical-state virial identity.

We specify the forced adaptations of the annular estimates, including the accumulated forcing. Set
$F_{n,s}(Z)=s^2f_{u_n}(sZ)$ and $k_{n,s}=(\kappa s)^{-\epsilon_n}$. The exact zoom equation, on the unchanged domain (106.13), is

$$
(\mathcal L_s+k_{n,s}|D_t|^{2+\epsilon_n})F_{n,s}
 =\frac{g_n}{a}W_sF_{n,s}+G_{n,s},\qquad
G_{n,s}(Z)=a^{-1}s^4f_{h_n}(sZ),\quad
\|G_{n,s}\|_2\le a^{-1}s^2.
\tag{113.9}
$$

For every fixed $c_0>0$, uniformly for $c_0d_n\le s\le s_0$ with $s_0$ sufficiently small,

$$
\begin{gathered}
\|F_{n,s}\|_2\le r^{-1},\qquad
k_{n,s}\bigl(\|F_{n,s}\|_2^2+D_{\epsilon_n}[F_{n,s}]\bigr)
 =k_{n,s}\|u_n\|_2^2+D_{\epsilon_n}[u_n]=O_r(1),\\
\sup_{c_0d_n\le s\le s_0}|k_{n,s}-1|
 \le C\epsilon_n(1+\Lambda_n)\longrightarrow0.
\end{gathered}
\tag{113.10}
$$

These follow from (113.2), (113.7) and the exact central scaling. The cutoff test in (106.15)--(106.16) now has the extra pairing $\langle\theta^2F_{n,s},G_{n,s}\rangle$, bounded by $C_rs^2$. The double commutator (104.9) is bounded by the middle line of (113.10), and (106.9) still absorbs the same original annular potential. Hence each fixed compact annular cutoff $\theta$ satisfies
$\|\theta F_{n,s}\|_{H^1}^2+D_{2+\epsilon_n}[\theta F_{n,s}]\le C_{r,\theta}$.
All tests belong to the exact form domain by the multiplier argument in (104.9).

The regularity proof of Lemma 111.2 applies to (113.9) with precisely one extra term: the localized $G_{n,s}$ in $L^2\subset H^{-3/4}$, of norm at most $Cs^2$. Its other hypotheses are the just obtained $H^1$ bound and (113.10). In particular the same coercive extended operator $K_{n,s}+C_s$, the bound (111.14), and uniqueness in its free form domain give

$$
\|\theta F_{n,s}\|_{H^{5/4}}\le C_{r,\theta},\qquad
\|\theta(|D_t|^{2+\epsilon_n}-D_t^2)F_{n,s}\|_{H^{-1}}
 \le C_{r,\theta}\epsilon_n.
\tag{113.11}
$$

For the second assertion use (111.15) on a nested cutoff and the whole separated-support kernel (111.12) on its complement. The latter has both Schur bounds $O(\epsilon_n)$ and uses the full $L^2$ bound in (113.10), so no remote central tail is discarded. Its literature ingredient is Di Nezza--Palatucci--Valdinoci, [*Hitchhiker's guide to the fractional Sobolev spaces*, §3, (3.1)--(3.2), Proposition 3.8](https://arxiv.org/html/1104.4345v3), with dimension one and fractional power $\epsilon_n/2$ before applying $D_t^2$ off support. The varying-order estimates themselves are the supplied (111.12)--(111.15).

Write $H_n=H_{u_n}$, $P_0=-\partial_\tau^2+B$, and $I_j=(j-1,j+1)$, $I_j^+=(j-2,j+2)$ with the fixed nested cutoffs of §111. For $T\le j\le\Lambda_n$, (109.10)--(109.13) and (113.11) give the forced counterpart of (111.19):

$$
\begin{aligned}
\|P_0H_n\|_{H^{-1}(I_j\times S^3)}
 &\le C_r\bigl(e^{-j/4}+|g_n-g_c|+|k_{n,e^{-j}}-1|\bigr)
             \|H_n\|_{H^1(I_j^+\times S^3)}\\
 &\quad+C_r\epsilon_ne^j+C_r e^{-j}.
\end{aligned}
\tag{113.12}
$$

Indeed the form-normalized annular function is $s^{-1}F_{n,s}$, $s=e^{-j}$. Its forcing in (113.9) is $s^{-1}G_{n,s}$, of norm at most $a^{-1}s$; the annulus-to-slab maps are bounded on these fixed annuli. This proves the last term in (113.12), including its power and its uniformity for arbitrary $h_n$. The other terms are exactly the original thin-layer, coefficient and varying-order errors of (111.19).

Let $A_n(T),B_n$ be the two strip integrals in (111.16), with $H_n$ as here and $\Lambda_n$ as in (113.7). Cut off $H_n$ between $T$ and $\Lambda_n$ by the fixed-width cutoff used there, obtaining $J_n$. The same finite-overlap summation, now applied to (113.12), and the already proved inverse (109.15) at weight $1$ yield

$$
\begin{aligned}
\|P_0J_n\|_{\mathscr H^{-1}_1}
 &\le C_r\delta_n(T)\|J_n\|_{\mathscr H^1_1}
  +C_r(A_n(T)+B_n)^{1/2}
  +C_r\epsilon_n\sqrt{1+\Lambda_n}+C_r e^{-2T},\\
\delta_n(T)&=e^{-T/4}+|g_n-g_c|+\epsilon_n(1+\Lambda_n).
\end{aligned}
\tag{113.13}
$$

The additional forcing contributes at most $C\sum_{j\ge T-4}e^{-4j}\le Ce^{-4T}$ to the square of the weighted negative norm: the weight contributes $e^{-j}$ and (113.12) contributes another $e^{-j}$. The absolute fractional remainder contributes $C\epsilon_n^2(1+\Lambda_n)$ as in (111.20). Cutoff commutators occupy only the two strips defining $A_n(T),B_n$. Thus all terms over the growing interval are accounted for. First choose a fixed sufficiently large integer $T$, then $n$ large; (113.7) absorbs the first term by (111.18). The mass identity (111.4) consequently gives

$$
\int_{\{R_\kappa<e^{-(T+8)}\}}|u_n|^2d\mu
 \le C_r\bigl(A_n(T)+B_n+\epsilon_n^2(1+\Lambda_n)+e^{-4T}\bigr)
       +\int_{\{R_\kappa<e^4d_n\}}|u_n|^2d\mu.
\tag{113.14}
$$

The last ball has central sections of length at most $2\kappa e^4d_n$, so (113.8) makes its mass tend to zero. The same argument puts $F_{n,d_n}\to0$ in $L^2$ on every fixed compact set. Its annular $H^{5/4}$ bound (113.11) and $\|v\|_{H^1}\le\|v\|_2^{1/5}\|v\|_{H^{5/4}}^{4/5}$ give annular strong $H^1$ convergence to zero. The exact change of variables (111.22), with $d_n$ replacing $\ell_n$, then gives $B_n\to0$. Also $\epsilon_n^2(1+\Lambda_n)\to0$ by (113.7).

Extract $f_n\rightharpoonup f$. Self-adjointness and Theorem 112.4 imply $u_n\rightharpoonup u=R_{{\rm end},r}f$: test against $v$ and use $R_{\sigma_n,r}v\to R_{{\rm end},r}v$ strongly. On fixed compact sets off $e$, the forced version of (104.11) has only the additional bounded pairing $\langle\chi^2u_n,h_n\rangle$; Lemma 113.2 controls its double commutator. This gives local $H^1$ bounds and local strong $L^2$ convergence after extraction. On every fixed sufficiently small annulus, (113.11) and interpolation strengthen this to strong $H^1$ convergence. In particular $A_n(T)\to A_u(T)$ for each fixed sufficiently large integer $T$.

Since $u\in D(H_{\rm end})\subset D(S^*)$, the full maximal-domain expansion (112.2) gives $H_u=(A(u)+\tau C(u))e_0+Z_u$ with $e^{\tau/8}Z_u\in H^1$ on the positive end. It follows directly that $A_u(T)\to0$ as $T\to\infty$. Take the upper limit in (113.14), then let $T\to\infty$. This proves source tightness for every such sequence of responses. A failure of the uniform double limit (113.5) would choose $\sigma_n\to2$, unit-ball inputs and shrinking radii contradicting this sequential conclusion. Finally split a fixed compact set into a small source ball and a compact punctured part. Source tightness and local Rellich compactness prove the last assertion. $\square$

**Theorem 113.4 (actual full-space norm resolvents).** For the unchanged actual critical family, for every fixed $r>0$,

$$
\lim_{\sigma\downarrow2}
 \bigl\|(H_\sigma+r)^{-1}-(H_{\rm end}+r)^{-1}\bigr\|_{\mathcal H\to\mathcal H}=0.
\tag{113.15}
$$

In addition $R_{{\rm end},r}-Q_{2,r}$ is compact. The assertion is on the whole original complex $L^2$ unit ball; it assumes neither a positive spectral gap nor a uniform global endpoint kinetic bound, imposes no sign or symmetry, and specifies no rate.

**Proof.** We first verify the free estimates used in the relative response. The actual joint support is $\ell\ge|\lambda|$ by (105.4). On $\ell>K$, $(a\ell+\eta|\lambda|^\sigma+r)^{-1}\le(aK)^{-1}$; on $\ell\le K$ the shifted multipliers converge uniformly, since $|\lambda|\le K$ and their denominators are at least $r$. Thus

$$
\|Q_{\sigma,r}-Q_{2,r}\|\longrightarrow0.
\tag{113.16}
$$

For any bounded compactly supported multiplier $m$, $Q_{\sigma,r}m$ is compact: truncate to $\ell\le K$ and use the already proved Hilbert--Schmidt bound (105.8), while the discarded norm is at most $\|m\|_\infty/(aK)$. It converges in norm to $Q_{2,r}m$ by (113.16). Further, $DQ_{\sigma,r}m$ is compact and norm continuous at $2$. Indeed the already proved bounded operators $T_\sigma=D/A_\sigma$ satisfy (105.12), including compactness of $T_\sigma m$, and

$$
DQ_{\sigma,r}m
 =T_\sigma m-rT_\sigma Q_{\sigma,r}m.
\tag{113.17}
$$

Only bounded compositions occur here; no zero-energy inverse is applied to a response.

For any sequence $\sigma_n\to2$ and $\|f_n\|_2\le1$, put $u_n=R_{\sigma_n,r}f_n$. Fix a real $\chi\in C_c^\infty(G)$, equal to one near $e$, and set $\psi=1-\chi$. Lemma 113.2 supplies $\|\langle D\rangle^{\epsilon_n}u_n\|_2=O_r(1)$. The central commutator calculation (105.14)--(105.17), whose hypotheses are precisely this bound and the $L^2$ bound, therefore gives

$$
\begin{gathered}
[|D|^{\sigma_n},\chi]u_n=Dp_n+k_n,\qquad
p_n=-i\sigma_n\chi'|D|^{\epsilon_n}u_n,\\
\|p_n\|_2+\|k_n\|_2\le C_r.
\end{gathered}
\tag{113.18}
$$

Here $p_n$ has fixed compact support; $k_n$ has fixed compact horizontal support and uniformly vanishing $L^2$ tails in the central variable. Explicitly, if $\operatorname{supp}\chi\subset K_\xi\times[-J,J]$, then for $|w|>2J$,
$|k_n(\xi,w)|\le C|w|^{-1-\sigma_n}\int_{-J}^{J}|\chi u_n(\xi,t)|dt$ as in (105.16). Integration and Cauchy--Schwarz give the required uniform tail. This retains the entire original central line.

The forced local bound used in Lemma 113.3 gives a bounded compactly supported $L^2$ sequence
$b_n=-a(L\chi)u_n+2a\sum_i(X_i\chi)(X_i u_n)$, since these derivatives of $\chi$ avoid $e$. Define
$F_n=g_n\Gamma\psi u_n+b_n-\eta k_n$. The original field is bounded off the source and $\Gamma\le B_\Gamma\rho^{-3}$. Hence $F_n$ is bounded in $L^2$ and has uniformly vanishing $L^2$ tails as $\rho\to\infty$. Localization of the actual form equation yields

$$
(A_{\sigma_n}+r)(\psi u_n)=\psi f_n+F_n-\eta Dp_n,
\qquad
\psi u_n=Q_{\sigma_n,r}(\psi f_n+F_n)
                  -\eta DQ_{\sigma_n,r}p_n.
\tag{113.19}
$$

To justify the second identity, $\psi u_n\in\mathcal E_{\sigma_n}$ by the product and Fourier multiplier bounds of §104. The first identity initially holds on smooth tests and extends to the free form domain: $F_n,p_n,f_n\in L^2$ and $\|D\phi\|_2^2\le\|\phi\|_2^2+D_{\sigma_n}[\phi]$. Test by $Q_{\sigma_n,r}v\in D(A_{\sigma_n})$ for arbitrary $v\in L^2$. Its derivative is in $L^2$ by the joint spectral bound, and the represented-form identity gives the second equality. Neither $\Gamma u_n\in L^2$ nor a separate operator action on that singular product is assumed.

Subtract the free response in (113.19). With $K_\sigma=R_{\sigma,r}-Q_{\sigma,r}$ this gives

$$
K_{\sigma_n}f_n
 =\chi u_n-Q_{\sigma_n,r}\chi f_n
       +Q_{\sigma_n,r}F_n-\eta DQ_{\sigma_n,r}p_n.
\tag{113.20}
$$

Each sequence on the right is relatively compact. For $\chi u_n$ this is Lemma 113.3. For the second and fourth terms it follows from the compact, norm-continuous localized free operators just proved and the bounded inputs with fixed compact support. For the third term truncate $F_n$ to $\rho\le R$. The localized free operators give relative compactness for fixed $R$; the remaining norm is at most $r^{-1}\|\mathbf1_{\{\rho>R\}}F_n\|_2$, uniformly tending to zero. Thus for every sequence of orders approaching $2$ and bounded inputs, the relative responses in (113.20) have a strongly convergent subsequence. This is relative compactness of the interaction correction, not compactness of the full free or interacting resolvent on the noncompact group.

By Theorem 112.4 and (113.16), $K_\sigma\to K=R_{{\rm end},r}-Q_{2,r}$ strongly, and these are self-adjoint bounded operators. The following elementary compactness passage is included to specify the use of the mature collective-compactness method of Anselone--Palmer, [*Collectively compact sets of linear operators*, Pacific J. Math. 25, 417--422, Theorem 3.4](https://doi.org/10.2140/pjm.1968.25.417). For any bounded sequence $v_j$, choose $\sigma_j\to2$ so close that $\|K_{\sigma_j}v_j-Kv_j\|_2<1/j$, using strong convergence separately for each fixed $v_j$. Equation (113.20) gives a convergent subsequence, so $K$ is compact. If $v_n\rightharpoonup0$ and $\sigma_n\to2$, every norm limit of $K_{\sigma_n}v_n$ is zero: for fixed $z$,
$\langle z,K_{\sigma_n}v_n\rangle=\langle K_{\sigma_n}z,v_n\rangle\to0$ by self-adjointness and strong convergence. Relative compactness then gives $\|K_{\sigma_n}v_n\|_2\to0$.

Finally, if $\|K_\sigma-K\|$ did not tend to zero, choose unit-ball inputs witnessing the failure and extract $f_n\rightharpoonup f$. The preceding conclusion applied to $f_n-f$, compactness of $K$, and strong convergence on $f$ give
$(K_{\sigma_n}-K)f_n\to0$, a contradiction. Thus $\|K_\sigma-K\|\to0$. Combining this with (113.16) proves (113.15).

The mature halfspace comparison underlying $B$ retains the parameters $n=4$, $\beta=2$ in Alvino--Ferone--Volpicelli, [*Sharp Hardy inequalities in the half space with trace remainder term*, Theorem 1.1, (8), (12)](https://arxiv.org/html/1105.0335v1); the original full-field transfer and weighted inverse are exactly §§87 and 109. The free heat-kernel localization is (105.8) for the original homogeneous dimension $5$ and clock. Those supplies do not by themselves give uniform-input source tightness: (113.2), the response-dependent inner radius (113.7), and the accumulated forced estimate (113.13)--(113.14) supply that step. The conclusion concerns only these specified mathematical operators; it supplies no native realization or physical spatial-dimension assertion. $\square$

## 追加锚（本行以下为增补区）
