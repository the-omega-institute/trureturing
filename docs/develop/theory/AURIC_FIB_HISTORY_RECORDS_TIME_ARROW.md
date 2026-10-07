# Auric：FIB-ATOM 续篇——差异边界、记录几何与时间箭头

## 116. 同组成来源的两叶差异边界

**定义 116.1（续卷载体与叶序）。** 本卷续接[《Auric：二元来源的三维二阶关系完成》](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)，沿用其第102、106–110、115章的类型与条件。密度态记为 $\varrho$；$\rho$ 专指原生树替换。原生来源是保留叶标签、左右顺序和括号的自由有序二叉树，采用[《FIB关系延拓几何》，版本cd077854c1e3df8b987f1ab9d6abee7554434e85，定义1.1、1.3及定理1.2](https://github.com/the-omega-institute/trureturing/blob/cd077854c1e3df8b987f1ab9d6abee7554434e85/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)的替换、组成和数量读出。令

$$
T_0=\alpha,\quad T_1=\beta,\quad
T_{n+2}=\langle T_{n+1},T_n\rangle=\rho^{n+2}\alpha,
\qquad n\ge0,
$$

$$
t_n^+=\rho^n\langle\beta,\alpha\rangle
=\langle T_{n+1},T_n\rangle,\qquad
t_n^-=\rho^n\langle\alpha,\beta\rangle
=\langle T_n,T_{n+1}\rangle.
$$

叶序映射 $\operatorname{wd}$ 将二叉节点映成有序串接：$\operatorname{wd}(\alpha)=\alpha$、$\operatorname{wd}(\beta)=\beta$、$\operatorname{wd}(\langle s,t\rangle)=\operatorname{wd}(s)\operatorname{wd}(t)$。写

$$
W_0=\alpha,\quad W_1=\beta,\quad W_{n+2}=W_{n+1}W_n,
\qquad u_n=W_{n+1}W_n,\quad v_n=W_nW_{n+1}.
$$

于是 $\operatorname{wd}(t_n^+)=u_n$、$\operatorname{wd}(t_n^-)=v_n$。空词记为 $\epsilon$。$F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$；本卷的 $\log$ 均为自然对数。

**定理 116.2（来源差异的有限叶序支撑）。** 对每个整数 $n\ge0$，存在共同前缀 $C_n$，满足

$$
C_0=\epsilon,\qquad C_n=W_nC_{n-1}\quad(n\ge1),
$$

$$
\begin{array}{c|cc}
&u_n&v_n\\\hline
n\text{ 偶}&C_n\beta\alpha&C_n\alpha\beta\\
n\text{ 奇}&C_n\alpha\beta&C_n\beta\alpha
\end{array}
$$

两树组成相同、来源不同；两叶序的汉明距离恰为二，而且

$$
|W_n|=F_{n+1},\qquad |u_n|=|v_n|=F_{n+3},\qquad
\frac{d_{\rm Ham}(u_n,v_n)}{F_{n+3}}=\frac2{F_{n+3}}\longrightarrow0.
$$

证明（116.2）。组成的加法性给 $c(t_n^+)=c(t_n^-)$，亦可直接引用前卷定理106.2的 $M^n(1,1)^T$。叶序部分使用经典 Fibonacci word 的近乎交换关系作为中间步骤：José L. Ramírez、Gustavo N. Rubiano，[*Properties and Generalizations of the Fibonacci Word Fractal*, The Mathematica Journal 16，DOI:10.3888/tmj.16-2，§3](https://www.mathematica-journal.com/2014/02/19/properties-and-generalizations-of-the-fibonacci-word-fractal/)，讨论相邻 Fibonacci words 串接只在末两符号不同。为固定此处的叶标签、索引与奇偶方向，归纳如下。

$n=0$ 时 $u_0=\beta\alpha,v_0=\alpha\beta$，结论成立。对 $n\ge1$，递推给

$$
u_n=(W_nW_{n-1})W_n=W_nv_{n-1},\qquad
v_n=W_n(W_nW_{n-1})=W_nu_{n-1}.
$$

两个旧词的末两标签交换，前面加上共同的 $W_n$，恰使奇偶方向翻转，并给 $C_n=W_nC_{n-1}$。不同叶标签 $\alpha,\beta$ 在这两个尾部位置各不相同，其他位置相同，故汉明距离严格为二。叶序不同推出原树不同，但反向不成立，因为叶序映射忘括号。

长度从初值 $1,1$ 及相同 Fibonacci 递推得到 $|W_n|=F_{n+1}$，再相加得 $F_{n+3}$，所以 $|C_n|=F_{n+3}-2$。$F_j$ 在 $j\ge2$ 正且不减，$F_{j+2}\ge2F_j$，故趋于无穷，所列比例趋零。$\square$

**假设 116.3（差异边界的类型）。** 后文将此叶序支撑接入固定酉原子与逐位置记录。两叶差异是忘括号后的词关系，不是整棵有序树仅有两个节点不同，也不是全部来源信息的距离。原树替换、叶序串接、矩阵乘法、物理执行时序使用各自的映射；只有另供相应实际操作，数学来源才能作为执行线路。

## 117. 两叶支撑、稳定相位与目标校准

**定义 117.1（固定原子的有序求值）。** 沿用前卷定义101.1及106.1，在 $\mathbb C^2$ 上取

$$
a=-iX,\qquad b=-iY,\qquad
U_\alpha=a,\quad U_\beta=b,\quad
U_{\langle s,t\rangle}=U_sU_t.
$$

对词 $w=w_1\cdots w_L$ 令 $U_w=U_{w_1}\cdots U_{w_L}$，$U_\epsilon=I$；矩阵结合性给 $U_t=U_{\operatorname{wd}(t)}$。右因子先作用，故书写在词尾的原子在此求值中先执行。

**定理 117.2（相位差的两叶支撑与固定原子校准）。** 上述 Pauli 提升满足

$$
U_{t_n^-}=-U_{t_n^+}\qquad(n\ge0).
$$

更一般，固定同一非零有限维复 Hilbert 载体上的酉原子 $A,B$，分别求值叶 $\alpha,\beta$。令 $\mathsf U_n=U_{u_n}$、$\mathsf V_n=U_{v_n}$、$Q_n=U_{C_n}$。不要求 $A,B$ 反对易，仍有

$$
\mathsf U_n+\mathsf V_n=Q_n(AB+BA),\qquad
\|\mathsf U_n+\mathsf V_n\|_{\rm op}=\|AB+BA\|_{\rm op}.
$$

若实际供应前卷定义107.1的相位相容受控比较门、$|+\rangle$ 准备和控制 $X$ 读出，则对任意单位输入 $\psi$，控制得到 $+$ 的概率为

$$
p_+(n,\psi)=\frac14\|(AB+BA)\psi\|^2
\le\frac14\|AB+BA\|_{\rm op}^2.
$$

证明（117.2）。第116.2条使偶数阶两矩阵为 $Q_nBA,Q_nAB$，奇数阶互换。相加与奇偶无关，给第一式。$Q_n$ 是同一组固定酉原子的乘积，所以酉；对每个向量，左乘它保持范数，再取单位球上的上确界给算子范数等式。

取 $A=a,B=b$，前卷定理101.2给 $ba=-ab$，故两支总差负号。这与前卷定理102.2、106.2的全树相位保持结论一致；这里叶序公式给出其可定位的差异支撑，而不是重新以有限表示替代原树。

已供给的受控门输出

$$
\frac{|0\rangle\mathsf U_n\psi+|1\rangle\mathsf V_n\psi}{\sqrt2}.
$$

投影到控制 $|+\rangle$ 得目标向量 $(\mathsf U_n+\mathsf V_n)\psi/2$，其范数平方为概率；左乘 $Q_n$ 不改变该范数，最后用算子范数定义得界。Pauli 情形 $AB+BA=0$，故 $p_+=0$，控制恒为负结果。$\square$

**假设 117.3（校准范围）。** 概率公式要求两来源使用真正相同、固定的原子和共同前缀，并已有同参照相干比较的实际实现。普通通道名称 $\operatorname{Ad}_U$ 不确定受控相位，沿用前卷第107章的限制。逐次原子漂移、路径依赖噪声及分支环境记录不满足本条无记录线路合同；有记录时须使用第118–120章的联合模型。

因此 $2/F_{n+3}\to0$ 不能推出全部实际量子实验近似等价：Pauli 校准下相对相位仍被确定读取。任何近似等价判断须先固定目标实验及误差量。词的数学尾部不自动对应物理执行的最后时刻；在本乘序中恰是右因子先作用。逐叶执行若按来源展开，原子次数仍为 $F_{n+3}$，有限表示的相位周期不给固定执行成本。

## 118. 逐位置共同档案与不增长的分支区分

**定义 118.1（只记录叶标签的独立位置载体）。** 给同一记录 Hilbert 空间中的单位向量 $e_\alpha,e_\beta$，记

$$
\kappa=\langle e_\beta|e_\alpha\rangle,\qquad |\kappa|\le1.
$$

对每个词位置使用新准备的记录载体，联合记录为

$$
E(w)=\bigotimes_{j=1}^{|w|}e_{w_j}.
$$

同长度两词在相同位置载体中比较。本模型仅对给定叶标签制备记录，不记录括号、整体分支编号或其他背景，不是复制未知量子态的操作。

**定理 118.2（FIB共同前缀的记录区分不随深度增加）。** 对第116章的两词，

$$
\langle E(v_n)|E(u_n)\rangle=|\kappa|^2\qquad(n\ge0).
$$

若两系统过程按第117章的 Pauli 合同已供应相对负号，并使用本定义的记录等距，则任意目标密度输入的约化控制态为

$$
\varrho_C^{(n)}=\frac12
\begin{pmatrix}1&-|\kappa|^2\\-|\kappa|^2&1\end{pmatrix}.
$$

在允许控制相位扫描的读出中，可见度及控制 von Neumann 熵分别为

$$
\mathcal V_n=|\kappa|^2,\qquad
S(\varrho_C^{(n)})=h\!\left(\frac{1+|\kappa|^2}{2}\right),
$$

其中 $h(p)=-p\log p-(1-p)\log(1-p)$，端点以 $0\log0=0$ 延拓。两记录态的迹距离为 $\sqrt{1-|\kappa|^4}$；以上各量均与 $n$ 无关。

证明（118.2）。张量内积是逐位置内积的乘积。共同前缀各位置给单位范数平方一；尾部两位置贡献 $\langle e_\alpha|e_\beta\rangle\langle e_\beta|e_\alpha\rangle=\overline\kappa\kappa$，奇数阶交换次序不改变积。

在前卷定义108.1的同一等距中代入 $U=U_{t_n^+},V=-U$，第108.2条给控制非对角元 $\langle E(v_n)|E(u_n)\rangle\operatorname{tr}(U\varrho(-U)^\dagger)/2=-|\kappa|^2/2$。所列二阶矩阵的本征值为 $(1\pm|\kappa|^2)/2$，故熵为二元熵。控制相位的极值概率为 $(1\pm|\kappa|^2)/2$，得可见度；同一条纯记录迹距离公式以重叠 $|\kappa|^2$ 给最后结论。$\square$

**定理 118.3（共同档案与区分信息的分离）。** 在定义118.1的固定二分支任务中，增加共同前缀的记录不增加分支区分信息，虽然总档案长度为 $F_{n+3}$。

证明（118.3）。在每个 $n$，两分支记录都可写成同一个单位向量 $E(C_n)$ 与两个尾部记录的张量积。奇偶改变时，用交换两个尾部张量因子的同一个酉即可对齐两分支，不改变固定分支先验。添入这一共同纯因子是等距嵌入，迹掉它是逆向的迹保持恢复；两操作均不改变可以实现的二分支判断。若任意联合效果 $F$ 作用于共同因子和尾部，其尾部有效效果为 $\langle E(C_n)|F|E(C_n)\rangle$，满足同一效果界，给完全相同的概率。反向任意尾部效果可张量恒等扩展，所以两处的实验集合等价。

档案长短与制备、存储费用是另一任务。若记录包含括号、整体分支、漂移或会再接入的共同环境，本定理的纯共同因子分解不再由定义保证。即使记录被丢弃，前卷定理108.3仍排除仅环境上迹保持操作恢复无条件控制干涉；恢复须另供联合逆操作或有记录的条件反馈。$\square$

## 119. 持续追加可区分记录的强度与熵

**定义 119.1（固定区别的独立重复记录）。** 与逐叶共同档案区别，现对同一二分支区别重复记录。每次给新准备且与其他次数独立的环境，两分支单位记录 $f_+,f_-$ 满足

$$
\langle f_-|f_+\rangle=|\kappa|^2=:c\in[0,1].
$$

追加 $m\ge0$ 次后的记录为 $f_+^{\otimes m},f_-^{\otimes m}$，$m=0$ 时两者均为空张量的单位标量。仍供同一相对负号的系统过程和等权控制准备。

**定理 119.2（独立追加的可加强度与有界熵）。** 定义

$$
\mathcal V_0=1,\qquad
\mathcal V_m=c^m=|\kappa|^{2m}\quad(m\ge1),\qquad
S_m=h\!\left(\frac{1+\mathcal V_m}{2}\right).
$$

当 $0<|\kappa|<1$ 时，

$$
\tau_{\rm rec}(m)=-\log\mathcal V_m=-2m\log|\kappa|,
\qquad \tau_{\rm rec}(m+\ell)=\tau_{\rm rec}(m)+\tau_{\rm rec}(\ell).
$$

此时 $\tau_{\rm rec}(m)$ 随 $m$ 无界增长，而 $S_m$ 非减、$0\le S_m\le\log2$，且趋于 $\log2$。边界 $|\kappa|=0$ 时 $\mathcal V_m=0,S_m=\log2$ 对每个 $m\ge1$ 成立；$|\kappa|=1$ 时所有 $\mathcal V_m=1,S_m=0$。所有情形 $m=0$ 均给 $\mathcal V_0=1,S_0=0$。

证明（119.2）。独立张量因子使重叠为 $\prod_{j=1}^m c$，空积为一，不需使用未定义的 $0^0$。前卷第108.2条的控制矩阵本征值公式给熵与可见度。对 $0<c<1$，乘积变成对数的和，$-\log c>0$，得到可加性及无界增长。$\mathcal V_m$ 从一向零下降，$p_m=(1+\mathcal V_m)/2$ 从一向 $1/2$ 下降；在 $1/2<p<1$，

$$
h'(p)=\log\frac{1-p}{p}<0,
$$

所以 $h(p_m)$ 非减，连续延拓及 $h(1/2)=\log2$ 给界和极限。两个端点直接由空积及正次数乘积得到。若将强度扩到 $c=0$，只能记 $\tau_{\rm rec}(0)=0$、正次数为 $+\infty$；它不是有限熵。$\square$

**假设 119.3（记录计数与时间的分型）。** $n$ 是原树替换深度，$F_{n+3}$ 是叶数，$m$ 是本模型的区分记录次数，$\tau_{\rm rec}$ 是相干衰减的对数强度；均不自动是物理钟读数。指定实际追加率及其时钟合同后才可校准物理时间。此处单个控制位的熵有界，不能用它等同总档案熵或无界记录强度。

独立新环境是乘积公式的实质前提。复用前卷命题110.4：两次作用同一个 CNOT 环境会恢复初态，两次新环境则保持退相干，所以重复一次局部退相干读数不确定以后是否回流。F. Ciccarello、G. M. Palma、V. Giovannetti，[*Collision-model-based approach to non-Markovian quantum dynamics*, Physical Review A 87，040103(R)，DOI:10.1103/PhysRevA.87.040103](https://doi.org/10.1103/PhysRevA.87.040103)，讨论通过辅助粒子间碰撞引入记忆、在无记忆碰撞与持续接触同一辅助粒子之间插值的模型。此处只引用这一记忆与独立性的研究背景；本条记录乘法及其端点由明列假设和上述证明承担。

## 120. 可见历史的时间接续与共同正性

**定义 120.1（同一标签集上的可见接续）。** 固定非空有限历史标签集 $H$，$d=|H|$。在同一个历史基上，$\Gamma_1,\Gamma_2$ 是 Hermitian 半正定、对角全为一的相关矩阵，沿用前卷定义109.1的索引约定。对全部矩阵定义

$$
\Phi_\Gamma(\varrho)=\Gamma\circ\varrho,
$$

其中 $\circ$ 为逐项乘法。另要求 $\Gamma_{1,hk}\ne0$ 对所有 $h,k$ 成立。接续操作只访问当前可见历史态，以同一个 CPTP 映射作用全部输入，不再次访问原隐藏环境，不更改来源准备。

**定理 120.2（FIB历史可见接续的比值判据）。** 在定义120.1下，存在上述 CPTP 映射 $\Lambda$，使

$$
\Phi_{\Gamma_2}=\Lambda\circ\Phi_{\Gamma_1}
$$

对全部密度输入成立，当且仅当

$$
C_{hk}=\frac{\Gamma_{2,hk}}{\Gamma_{1,hk}}
$$

所成矩阵 $C$ 半正定。若存在，$\Lambda$ 唯一且等于 Schur 映射 $\Phi_C$。

证明（120.2）。前卷定理109.2已经给出相关矩阵与 Schur 通道的共同实现条件，此处使用其线性映射及 Choi 形式。密度矩阵的实线性包络是全部 Hermitian 矩阵：任意 Hermitian 矩阵的正、负谱部分各为非负标量乘密度矩阵；一般复矩阵再分为两个 Hermitian 部分。故两复线性映射若在全部密度态上一致，即在全部矩阵上一致。

在矩阵单位 $|h\rangle\langle k|$ 上，$\Phi_{\Gamma_1}$ 乘以非零标量 $\Gamma_{1,hk}$，因此线性可逆；其逆不必为正映射。唯一候选为

$$
\Lambda=\Phi_{\Gamma_2}\Phi_{\Gamma_1}^{-1}=\Phi_C.
$$

相关矩阵的 Hermitian 性及非零分母给 $C_{kh}=\overline{C_{hk}}$，对角为一。经典 Choi 完全正判据作为中间工具给归一化 Choi 矩阵

$$
J(\Phi_C)=\frac1d\sum_{h,k}C_{hk}|h,h\rangle\langle k,k|.
$$

令 $F|h\rangle=|h,h\rangle$，则 $J(\Phi_C)=FCF^\dagger/d$；在 $F$ 的像上同构于 $C/d$，正交补上为零。因此 $\Phi_C$ 完全正当且仅当 $C\ge0$。对角为一又使 $\operatorname{tr}\Phi_C(A)=\operatorname{tr}A$ 对全部 $A$ 成立。反向 $C\ge0$ 时直接用前卷定理109.2或其记录分解，得 CPTP 接续及所需复合等式。$\square$

Satvik Singh、Nilanjana Datta，[*Detecting positive quantum capacities of quantum channels*, npj Quantum Information 8，50，DOI:10.1038/s41534-022-00550-2](https://www.nature.com/articles/s41534-022-00550-2)，式(55)以相关矩阵参数化广义退相干通道，Theorem II.28的证明给其 Choi 矩阵形式。该文的目标是量子容量；这里只取 Schur/Choi 的成熟中间工具，全部输入上的接续比值等价由本条线性可逆性论证承担。

**定理 120.3（逐对相干减小而无共同可见接续）。** 在同一个三历史载体上，取

$$
\Gamma_1=\begin{pmatrix}
1&1/5&1/5\\1/5&1&1/5\\1/5&1/5&1
\end{pmatrix},\qquad
\Gamma_2=\begin{pmatrix}
1&9/50&9/50\\9/50&1&-9/50\\9/50&-9/50&1
\end{pmatrix}.
$$

两阶段都可由共同记录实现，所有非对角元的模严格减小，但不存在定义120.1的 CPTP 接续。

证明（120.3）。$\Gamma_1=(4/5)I+(1/5)\mathbf1\mathbf1^T$，本征值为 $7/5,4/5,4/5$。令 $w=(-1,1,1)^T$，则

$$
\Gamma_2=\frac{59}{50}I-\frac9{50}ww^T,
$$

在 $w$ 方向本征值为 $16/25$，其正交补上为 $59/50$，均严格正。两矩阵对角一，前卷第109.2条给各自合法的联合记录；且 $9/50<1/5$。

逐项比值得

$$
C=\begin{pmatrix}1&9/10&9/10\\9/10&1&-9/10\\9/10&-9/10&1\end{pmatrix}
=\frac{19}{10}I-\frac9{10}ww^T.
$$

这正是前卷命题109.3的三态证书，本征值为 $-4/5,19/10,19/10$，不半正定。第120.2条排除共同可见接续。$\square$

**假设 120.4（接续判据的边界）。** 若 $\Gamma_1$ 有零条目，Schur 映射不再线性可逆，本定理的比值与唯一性论证均不适用。此处不给完整的零条目接续判据。$\Gamma_2$ 自身可实现、改变准备可得到它、再次访问旧环境可改变状态，与从 $\Phi_{\Gamma_1}$ 当前输出作独立 CPTP 后处理是不同量词。有限阶段各自正性和成对衰减不提供整个多时刻过程的无记忆实现。

## 121. 有限来源记录几何的 Gaussian 接续

**定义 121.1（同一有限历史的记录坐标）。** 令 $H$ 为一个固定有限任务的非空实际合法 FIB 历史集。另供有限整数 $k\ge0$ 和每个历史的实坐标 $r_h\in\mathbb R^k$；坐标的取得是新增记录合同，不从原树自动导出。对 $1\le a\le k$ 定义实对角自伴算子

$$
R_a=\sum_{h\in H}r_h^a|h\rangle\langle h|.
$$

给方差参数 $t\ge0$，令 $Z_t$ 的单时刻分布为 $N(0,tI_k)$，并定义

$$
\Phi_t(\varrho)=\mathbb E\left[
\exp\!\left(-i\sum_aZ_t^aR_a\right)\varrho
\exp\!\left(+i\sum_aZ_t^aR_a\right)\right].
$$

$t=0$ 时分布为原点的点质量。$k=0$ 时坐标空间只含一个点，指数空和为零，所有 $\Phi_t$ 为恒等；以下空和均取零。

**定理 121.2（记录坐标产生共同正的可见耗散）。** 在定义121.1下，每个 $\Phi_t$ 为 CPTP，并在同一历史基上满足

$$
[\Phi_t(\varrho)]_{h\ell}
=\exp\!\left(-\frac t2\|r_h-r_\ell\|^2\right)\varrho_{h\ell},
\qquad \Phi_{t+s}=\Phi_t\circ\Phi_s\quad(t,s\ge0).
$$

其生成元为

$$
\mathcal L(\varrho)=-\frac12\sum_{a=1}^k[R_a,[R_a,\varrho]].
$$

同一记录坐标给出了第120章的合法正向接续；重合坐标的相干不衰减，$t=0$ 时所有条目保持。

证明（121.2）。每个指数是实自伴矩阵乘 $-i$ 的指数，故酉；对任意未触及参考，酉共轭保持联合正性，取概率平均仍正，且迹保持。因此平均通道完全正且迹保持。

Gaussian 来源族采用前卷假设14.1、定理14.3的连续变量合同；经典特征函数仅作为本记录综合的中间步骤。独立标准实 Gaussian 的线性组合具有方差 $t\|v\|^2$，一维 Gaussian 积分的 Fourier 变换给

$$
\mathbb E e^{-iZ_t\cdot v}=e^{-t\|v\|^2/2}.
$$

在 $|h\rangle\langle\ell|$ 上，酉左右共轭恰乘以 $e^{-iZ_t\cdot(r_h-r_\ell)}$，于是给矩阵元公式。该因子还可由同一 $L^2(N(0,tI_k))$ 空间中的单位记录函数 $e_h(z)=e^{-iz\cdot r_h}$ 写成 $\langle e_\ell|e_h\rangle$，所以与前卷第109.2条的共同记录正性相容。它不是为每一对独立择取记录后拼成的矩阵。

逐矩阵单位上相乘因子等于参数 $t+s$ 的因子，所以得到半群式。对 $t$ 求导，矩阵元乘以 $-\|r_h-r_\ell\|^2/2$；而

$$
[R_a,[R_a,\varrho]]_{h\ell}
=(r_h^a-r_\ell^a)^2\varrho_{h\ell},
$$

求和恰给生成元。有限历史载体使这些导数都是有限矩阵导数。两个端点直接代入所列指数公式。$\square$

**定理 121.3（固定记录几何的接续方向）。** 若 $t_2\ge t_1\ge0$，上述通道族的当前可见 CPTP 接续为 $\Phi_{t_2-t_1}$。若至少有一对历史坐标不同且 $0\le t_2<t_1$，则不存在对全部输入的当前可见 CPTP 接续 $\Phi_{t_2}=\Lambda\Phi_{t_1}$。

证明（121.3）。第一项用半群式。所有 Gaussian 因子非零，第120.2条适用；第二项的比值矩阵在该不同坐标的二阶主块上有对角一、非对角

$$
c=\exp\!\left(\frac{t_1-t_2}{2}\|r_h-r_\ell\|^2\right)>1.
$$

其行列式 $1-c^2<0$，故比值矩阵不半正定。若全部坐标重合，所有通道都是恒等，此障碍消失。$\square$

**假设 121.4（Gaussian参数、Markov过程与原生取得）。** $t$ 首先是方差参数；只有供应实际噪声率、时钟和耦合校准，才能称物理时间。随机酉的实际准备与耦合须另外供应，平均公式本身不授予连续相位控制权限。$k$ 只是记录坐标的有限维数，未由本条证明等于三；此 Gaussian 模型不是把非负整数树组成直接假设成 Gaussian。

单时刻 Gaussian 分布给出了上述通道族，但不决定装置在多时刻怎样保存、重用环境。若要由实际随机酉过程实现此半群，再给 $Z_t=B_t$ 为具有独立平稳增量的同一 $\mathbb R^k$ Brownian 过程，并固定同一耦合：增量独立且 $R_a$ 彼此对易，使各时间段的随机相位相加，条件于过去的增量平均为相应 $\Phi_s$。这才供给所需 Markov 过程合同；不能由一组边缘 Gaussian 或半群公式推定全部实际多时刻实验均无记忆。回用旧环境仍须保留前卷第110章的联合边界。

## 122. 五模式配置图的平稳路径箭头

**定义 122.1（固定外接缝的配置更新图）。** 两侧外接缝均为空，位串始终按低到高书写。取原五个合法模式

$$
s_0=\mathrm{null}=000,\quad s_1=[2]=100,\quad
s_2=[25]=101,\quad s_3=[5]=001,\quad s_4=[3]=010.
$$

两模式相连当且仅当它们恰差一个占位位。图为方形 $0\!-!1\!-!2\!-!3\!-!0$ 加支路 $0\!-!4$。例如 $100\to101$ 翻转高端位，$000\to010$ 翻转中位；其他不同点对至少差两个位。这里的边是配置更新，区别于前卷第25、29、90章高到低即时窗口读者的输入续接；$\rho$ 不因此被指定为随机翻位动力学。

**定义 122.2（附加的平稳随机动力学）。** 明确增加 $p,q,r>0$、$p+q+r<1$ 的 Markov 合同。方形正向取 $0\to1\to2\to3\to0$，对应概率 $p$，反向概率 $q$，支路两向概率 $r$。行表示出发状态，令

$$
P=\begin{pmatrix}
1-p-q-r&p&0&q&r\\
q&1-p-q&p&0&0\\
0&q&1-p-q&p&0\\
p&0&q&1-p-q&0\\
r&0&0&0&1-r
\end{pmatrix},\qquad \pi_i=\frac15.
$$

启动分布固定为 $\pi$。路径倒序是 $(x_0,\ldots,x_N)\mapsto(x_N,\ldots,x_0)$；不将树替换、物理反转或位打印方向认作该操作。沿用[《有限奇偶马尔可夫核的隐藏时间箭头与信息阈值》，版本cd077854c1e3df8b987f1ab9d6abee7554434e85，定义1.2](https://github.com/the-omega-institute/trureturing/blob/cd077854c1e3df8b987f1ab9d6abee7554434e85/docs/develop/theory/PARITY_HIDDEN_ARROW.md)的平稳路径相对熵原理，定义

$$
\sigma(P)=\sum_{i,j}\pi_iP_{ij}
\log\frac{\pi_iP_{ij}}{\pi_jP_{ji}}.
$$

共同为零的有向项贡献零；本模型其余转移均有正反两向支持。

**定理 122.3（单时刻熵固定而路径不可逆）。** 上述链双随机，$\pi$ 平稳，且对全部 $n\ge0$，

$$
H(X_n)=\log5,\qquad
\sigma(P)=\frac45(p-q)\log\frac pq.
$$

该率非负，严格正当且仅当 $p\ne q$。取 $p=1/4,q=r=1/8$，有 $\sigma(P)=\log2/10$。

证明（122.3）。各行直接相加为一；第零列为 $(1-p-q-r)+q+p+r=1$，其余各列分别由一个 $p$、一个 $q$ 和自环组成，或由支路 $r$ 与 $1-r$ 组成，也为一。所有给定非零转移严格正，故 $\pi P=\pi$；由启动和平稳性，每个 $X_n$ 都均匀，单时刻熵为 $-5(1/5)\log(1/5)=\log5$。

每一条无向方形边的两项之和为

$$
\frac p5\log\frac pq+\frac q5\log\frac qp
=\frac{p-q}{5}\log\frac pq.
$$

四条相加给所列率。支路两向流相同，自环与自身比较，均贡献零；缺边两向为零。对数严格递增，所以 $p-q$ 与 $\log(p/q)$ 同号，等号恰在 $p=q$。给定数值中 $p-q=1/8$、$p/q=2$，代入得 $\log2/10$。$\square$

**假设 122.4（路径方向与物理热的边界）。** $\sigma$ 是所声明平稳路径律的相对熵率；没有额外热浴、能量函数与局部详细平衡合同，不称物理热或热耗散。状态熵不增长与路径时间箭头严格正可同时成立。该五模式图给实际合法配置上的明确随机模型，不把经典路径 KL 工具或双随机性独立包装成原生 FIB 的新动力学定律。

## 123. 箭头似然统计量与预测边界的区别

**定义 123.1（固定时域的路径电流）。** 在第122章的固定平稳模型中，令整数 $N\ge0$，合法路径 $\gamma=(x_0,\ldots,x_N)$ 的正向概率为

$$
\mathbb P_N(\gamma)=\frac15\prod_{j=0}^{N-1}P_{x_jx_{j+1}}.
$$

合法指所有路径转移具有正概率；$N=0$ 的空乘积为一。倒序映射 $\mathcal R\gamma=(x_N,\ldots,x_0)$ 保持合法路径集，反向比较律定义为 $\mathbb Q_N(\gamma)=\mathbb P_N(\mathcal R\gamma)$。令 $W(\gamma)$ 为正向方形步数减去反向方形步数，支路和自环贡献零；于是 $W(\mathcal R\gamma)=-W(\gamma)$。

**定理 123.2（完整箭头似然及其充分统计量）。** 对全部 $N\ge0$ 与合法路径，

$$
\log\frac{\mathbb P_N(\gamma)}{\mathbb Q_N(\gamma)}
=W(\gamma)\log\frac pq,
\qquad D(\mathbb P_N\Vert\mathbb Q_N)=N\sigma(P).
$$

正向律下的有限时域涨落式为

$$
\Pr(W=w)=\left(\frac pq\right)^w\Pr(W=-w),\qquad
\mathbb E\exp\!\left(-W\log\frac pq\right)=1.
$$

$W$ 保留这两个固定路径律的全部似然比，并且其推前律满足

$$
D(W_\#\mathbb P_N\Vert W_\#\mathbb Q_N)
=D(\mathbb P_N\Vert\mathbb Q_N).
$$

所以它是本固定模型和固定时域的正反方向判别充分统计量；这里不主张最小性。

证明（123.2）。初始均匀因子在路径比中相消，每条正向方形边贡献 $p/q$，反向边贡献 $q/p$，支路与自环贡献一。相乘再取对数得到第一式。平稳性给每一时刻有向边分布 $\pi_iP_{ij}$，故各步对数比的期望为 $\sigma(P)$；有限项线性相加给 KL 等式。这是在本五模式图上应用定义122.2所引用的经典平稳路径 KL 中间原理，不需要独立边假设。

在 $W=w$ 的纤维上，第一式的概率比恒为 $(p/q)^w$。倒序将该纤维双射到 $W=-w$ 的纤维，逐路径求和给涨落式；不可达的两个纤维均为零，等式仍成立。再直接计算

$$
\sum_\gamma\mathbb P_N(\gamma)
e^{-W(\gamma)\log(p/q)}
=\sum_\gamma\mathbb Q_N(\gamma)=1.
$$

写 $P_W(w)=\mathbb P_N(W=w)$、$Q_W(w)=\mathbb Q_N(W=w)$。同一纤维的恒定比值给 $P_W(w)/Q_W(w)=(p/q)^w$；对正质量纤维，条件路径律满足

$$
\mathbb P_N(\gamma\mid W=w)=\mathbb Q_N(\gamma\mid W=w).
$$

因而在正反二元假设、任意固定先验的判别中，观察 $W$ 后整条路径不再追加关于假设的区别。其推前 KL 直接为 $\sum_wP_W(w)w\log(p/q)$，等于原路径 KL。$p=q$ 时两律相同，$N=0$ 时 $W=0$；所有公式保留这些退化情形，不由充分性推出唯一或最小摘要。$\square$

**定理 123.3（四类型不是本配置链的自治预测状态）。** 将模式 $[3]$ 与 $[25]$ 合并为前卷第24–25、90章的同一非零类型，其他三个模式各保留一类。所得四类型合并不是本链的强 Markov 可合并，也不在平稳启动下给自治的一阶 Markov 预测边界。

证明（123.3）。令合并类 $B=\{s_2,s_4\}$。从 $s_4=[3]$ 下一步进入单点类 $\{s_0\}$ 的概率为 $r$；从 $s_2=[25]$ 该概率为零。同一块内到另一块的总转移概率不同，已违背对全部微观初态下降到同一转移核的必要条件。

即使固定为均匀启动，也有两段正概率的可见过去。由单点 $[2]=s_1$ 进入 $B$ 时，只能到 $s_2$，概率 $p>0$；由单点 $\mathrm{null}=s_0$ 进入 $B$ 时，只能到 $s_4$，概率 $r>0$。于是，记类型过程为 $Y_j$，

$$
\Pr(Y_2=\mathrm{null}\mid Y_0=[2],Y_1=B)=0,
$$

$$
\Pr(Y_2=\mathrm{null}\mid Y_0=\mathrm{null},Y_1=B)=r.
$$

这两个条件事件分别有概率 $p/5,r/5$，均可实际出现。当前类型相同而下一步分布随过去不同，所以没有以当前四类型为唯一状态的自治一阶核。$\square$

**假设 123.4（任务与实际未来菜单）。** $W$ 的充分性只针对固定模型的有限正反路径律判别；它不是继续生成路径的全预测状态，也不保留量子历史的非对角块。四类型的预测障碍在本章是配置图转移概率障碍，前卷五模式接缝的障碍则是即时读者合法性障碍，两者的操作不同。实际未来概率须依可用效果和仪器定义，沿用[《递归关系观察：联合来源、量子关系与有限时钟》，版本cd077854c1e3df8b987f1ab9d6abee7554434e85，命题2.2–2.4](https://github.com/the-omega-institute/trureturing/blob/cd077854c1e3df8b987f1ab9d6abee7554434e85/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md)的实际效果空间及逐分支合同；形式上可写的算子或事后箭头统计量不自动成为全部未来实验的充分边界。

## 124. 同一配置闭路的相位与概率方向

**定义 124.1（显式供给的边运输）。** 在第122章的同一五模式配置图上，另供一个目标 $\mathbb C^2$ 及具体酉边运输。记 $G_{ji}$ 为沿 $i\to j$ 的目标作用，按执行次序的右因子先作用。固定 $a=-iX,b=-iY$，令

$$
G_{10}=a,\quad G_{21}=b,\quad
G_{32}=a^{-1},\quad G_{03}=b^{-1},\qquad
G_{ij}=G_{ji}^{-1}
$$

对上述反向边成立；支路两向及自环可取 $I$。这些是明确附加的运输权限，不由位翻转标签、原生 $M$ 或 $\rho$ 自动提供。还须另供相位相容的闭路与恒等线路的相干控制比较，才可读取相对过程符号。

**定理 124.2（反向相位相同而路径概率不同）。** 正向方形闭路 $\gamma_+=(0,1,2,3,0)$ 的运输及其反向 $\gamma_-=(0,3,2,1,0)$ 的运输均为 $-I$。若实际供应定义124.1的相干比较，两闭路分别与恒等线路比较都给控制负结果，所以该中心符号本身不区分顺逆。它们的平稳路径概率却满足

$$
\mathbb P_4(\gamma_+)=\frac{p^4}{5},\qquad
\mathbb P_4(\gamma_-)=\frac{q^4}{5},\qquad
\log\frac{\mathbb P_4(\gamma_+)}{\mathbb P_4(\gamma_-)}
=4\log\frac pq.
$$

证明（124.2）。边运输按时间逆序写乘积，故

$$
G_{03}G_{32}G_{21}G_{10}=b^{-1}a^{-1}ba.
$$

前卷第101.2条给 $a^{-1}=-a,b^{-1}=-b$、$ba=c$、$c^2=-I$，所以该积为 $(ba)^2=-I$。反向路径的每条运输取逆，整体运输为此积的逆，仍为 $(-I)^{-1}=-I$。这是前卷第104章已有四元数闭路工具在本图的具体赋值，不是把原生树循环认作闭路。

前卷第107.2条对已供比较门给 $W_{I,-I}(|+\rangle\psi)=|-\rangle\psi$；两向各得到同一负结果，单系统闭路通道更均为恒等。概率是同一 Markov 核沿实际路径的转移积；两路径的四步分别全为 $p$ 和 $q$，均匀起点因子相同，得到概率及比值。$\square$

**假设 124.3（独立的运输和箭头桥）。** 中心相位、概率电流和空间镜像手性是不同关系。本图中 $p\ne q$ 是独立声明的概率偏置，闭路 $-I$ 是独立声明的酉运输。配置图的方向不自动代表物理空间反射，普通酉通道也不包含相干受控相位的执行能力。由分别可取的 $p,q$ 和 $a,b$，不能断言同一原生局域相互作用已经联合导出非零概率箭头及该相位回路；这一共同取得条件仍待证明。

## 125. 有限共同历史中权重、作用与记录的分离

**定义 125.1（同一联合实现的有限三类数据）。** 固定非空有限实际合法历史集 $H$、非零有限维目标载体 $\mathcal K$，以及同一个记录空间 $\mathcal E$。给与未知目标输入无关的权重 $p_h\ge0$、$\sum_hp_h=1$，给具体且相位已定的目标酉 $U_h$，并给 $\mathcal E$ 中的单位记录 $e_h$。历史寄存器具有正交基 $|h\rangle$，记录矩阵为

$$
\Gamma_{hk}=\langle e_k|e_h\rangle.
$$

所有标签、酉和记录属于同一份联合模型。定义线性映射

$$
V:\mathcal K\longrightarrow\mathbb C^H\otimes\mathcal K\otimes\mathcal E,
\qquad V\psi=\sum_h\sqrt{p_h}|h\rangle\otimes U_h\psi\otimes e_h.
$$

若实际历史由一般输入依赖的仪器产生，其 $p(h)$ 与分支作用应采用前卷第73、110章的 Kraus 合同；不能以状态依赖的 $\sqrt{p_h(\psi)}$ 代入本定义并冒称同一个线性等距。

**定理 125.2（共同有限历史的兼容性与记录分解）。** 定义125.1的 $V$ 为等距，且对任意目标密度态，迹掉记录后得到

$$
\Omega=\sum_{h,k}\sqrt{p_hp_k}\,\Gamma_{hk}
|h\rangle\langle k|\otimes U_h\varrho U_k^\dagger\ge0,
\qquad\operatorname{tr}\Omega=1.
$$

历史测量概率为 $p_h$；再忽略历史得到目标随机酉通道 $\sum_hp_hU_h\varrho U_h^\dagger$，但共同历史间的相干还依赖 $\Gamma$ 及具体酉相位。任意给定的有限概率权重、酉族和相关矩阵都在此抽象等距合同内有联合实现。

证明（125.2）。标签正交消去 $V^\dagger V$ 中的 $h\ne k$ 交叉项，单位记录及酉性给

$$
V^\dagger V=\sum_hp_hU_h^\dagger U_h=I.
$$

展开 $V\varrho V^\dagger$，记录块为 $|e_h\rangle\langle e_k|$；其迹恰为 $\langle e_k|e_h\rangle=\Gamma_{hk}$，得到所列 $\Omega$。等距共轭及部分迹保持正性与迹；同一操作对任意未触及参考也完全正。取 $h$ 对角块的迹得 $p_h$，再取历史迹则消去非对角块，给随机酉通道。若起初只给 $\Gamma\ge0$、对角一，前卷第109.2条在同一个有限记录空间构造全部 $e_h$，再使用本定义即得兼容性。它不允许把不同实际对象中分别合法的最优记录拼成未满足共同正性的矩阵。

这种分解不是对三类参数的唯一反演断言。零权重历史不影响输出；而替换 $U_h\mapsto e^{i\theta_h}U_h$、$e_h\mapsto e^{-i\theta_h}e_h$ 不改变每个联合项及 $V$，使记录矩阵变为 $\Gamma_{hk}\mapsto e^{-i\theta_h+i\theta_k}\Gamma_{hk}$。所以分别解释过程相位与记录相位须固定共同参照。已有参照后，改变 $p$ 改变对角历史质量，改变相对 $U$ 改变目标作用及历史间过程关系，改变 $\Gamma$ 改变记录所保留的相干；不能由相同经典概率反演全部三类数据。$\square$

**定理 125.3（来源长度、记录接续与路径箭头在同一对象中的条件汇合）。** 若 $H$ 取第122章任一固定有限长度的全部合法路径，令 $p_h=\mathbb P_N(h)$，$U_h$ 为定义124.1的沿路径运输，$\Gamma$ 为同一组单位记录的相关矩阵，则第125.2条给共同正的有限历史态。同时，以下各项在自己的附加条件下成立：第116–117章的两叶来源支撑与固定原子比较，第118–119章的两类档案区分，第120章的可见 CP 接续，第121章的 Gaussian 记录半群，以及第122–124章的概率箭头与闭路相位区别。

证明（125.3）。有限长度路径集有限且非空，初始质量及各行归一化使其路径概率和为一。每个实际路径的边运输乘积酉；共同记录给相关矩阵正性。因此全部量符合定义125.1，使用同一个 $V$，而不是只把三类各自存在的对象并列。此处的相干路径准备是额外等距合同，普通 Markov 抽样只给对角概率，不自动供给其非对角相干。

若另供来源到历史标签的对应 $t_n^\pm\mapsto h_\pm$，并要求这两个标签的实际 $U_h$、记录及控制准备确实满足第117–119章的合同，方可在同一对象上应用其来源结论。路径标签本身不给这种对应；第118–119章的等权控制准备也不由一般路径权重自动提供。对应已给时，第116.2条只定位忘括号后的两叶差异，固定原子及实际比较给第117.2条的相位校准。第118章要求逐位置新记录，第119章要求重复区别的新环境，二者的张量合同不同。

对同一固定标签载体施加额外 Schur 记录时，$|h\rangle\langle k|$ 块整体乘相应因子，包括其目标矩阵 $U_h\varrho U_k^\dagger$；第120章的接续因而也适用于与目标及参考共同保留的历史载体，但不替代目标运输或逆操作。第121章的共同 Gaussian 因子给正向可行接续；只有另有独立增量过程，才供实际多时刻的无记忆合同。固定 Markov 路径律给第123.2条的 $W$ 似然比，第124.2条说明同一路径对的酉中心符号不承担该似然方向。

在每个实际历史阶段继续组合时，调用前卷第110.2条的同一相位保持等距，历史块按

$$
\Xi_{ha,kb}'=K_{a|h}\Xi_{hk}K_{b|k}^\dagger
$$

更新。该式已经证明保持联合正性，不能只更新 $p_h$ 后任意填入非对角块；有隐藏 Kraus 指标时使用第110.3条的扩展环境，旧环境将再参与时使用第110.1、110.4条的完整联合载体。以上把来源差异、记录和箭头对应到同一有限历史对象，仍没有扩大任何实际操作权限。$\square$

**假设 125.4（反演、后处理与未来菜单的未决边界）。** 权重的路径倒序、酉运输的逆、相关矩阵的当前可见 CP 接续与实际环境联合反转，是不同合同。原生树到叶序忘括号，叶序到有限酉表示继续忘其他区别，经典历史概率又忘非对角关系。对实际未来充分性的判断必须保留所需原树、次序、括号、进位、读者接缝，以及会再进入的控制、时钟和共同环境；第123章的箭头统计量不替代这些边界。有限正性、等距实现和可见接续不说明原生来源已能高效制备它们，也不提供无界递归的统一执行或存储预算。

记录方差、记录对数强度、FIB深度、路径步数和物理时钟需分别校准，参见所引《联合来源、量子关系与有限时钟》命题1.1的有向时钟条件。热解释须另供热浴与详细平衡；位置解释须另供实际距离、运输及跨接缝共同度量。量子关系维数、记录坐标维数、配置图与局部法向维数不能叠加为物理空间维数；连续空间和无限时域的桥均未在此建立。

**假设 125.5（共同原生交互的待证断言）。** 待证目标是在明确的同一个原生局域交互、共同来源、接缝及资源合同下，联合导出所需路径权重 $p$、相位相容作用 $U$ 与共同记录矩阵 $\Gamma$，并证明其对全部声明的未来实验充分。数学有限兼容性是第125.2–125.3条的结论；原生共同可取得性、相位控制与保护、物理距离和时间的忠实运输，以及无界成本的可支付性仍是独立未证前提。分别选择最优 $p,U,\Gamma$ 不证明它们由同一实际交互共同可达。

## 追加锚（本行以下为增补区）

## 126. 跨输入的共同等距条件与唯一后继记录

**定义 126.1（配置、内部载体与记录）。** 令 $X$ 为有限配置集，内部空间为
$K=\mathbb C^d$，其中 $1\le d<\infty$。给定随机矩阵 $P=(P_{ij})$，满足
$P_{ij}\ge0$ 且 $\sum_jP_{ij}=1$，并在每条允许边 $i\to j$ 上给定酉
$U_{ji}\in\mathsf U(K)$。记录向量 $e_{ji}$ 属于有限维空间 $E$，且
$\langle e_{ji},e_{ji}\rangle=1$。候选共同实现定义在
$\mathbb C^X\otimes K$ 上：
$$
 V(|i\rangle\otimes\psi)=\sum_j\sqrt{P_{ij}}\,|j\rangle\otimes U_{ji}\psi\otimes e_{ji}.
$$
这里的 $V$ 同时承载概率、内部酉和记录；三者不能先分别选出再假定具有共同实现。

**定理 126.2（跨输入等距判据）。** 上式延拓为等距映射 $V$ 当且仅当对任意
$i,k\in X$，有算子恒等式
$$
 \sum_j\sqrt{P_{ij}P_{kj}}\,
 \langle e_{ji},e_{jk}\rangle\,U_{ji}^{\dagger}U_{jk}
 =\delta_{ik}I_K. \tag{126.1}
$$

**证明。** 对任意基向量和内部向量，展开两边内积，输出配置的正交性只留下共同后继 $j$，所得系数正是左端。输入基向量的内积为 $\delta_{ik}\langle\psi,\phi\rangle$，因而所有 $\psi,\phi$ 的内积相等恰好等价于 (126.1)。当 $i=k$ 时，记录归一化和酉性把左端化为 $\sum_jP_{ij}I_K=I_K$。当 $i\ne k$ 时，条件是不同输入之间的算子抵消关系，记录 Gram 矩阵的正性和各条边的合法性都不能代替它。有限 Stinespring 扩展与丢弃记录只是实现等距后的标准操作；本定理要求的是整个来源叠加域上的共同算子，因此强于第125章固定准备历史的等距式：后者以正交历史标签保证一个内部输入的范数，本式还检验不同配置来源之间的全部相干叠加。 $\square$

**引理 126.3（唯一共同后继强制正交记录）。** 若 $i\ne k$ 只有一个共同后继 $j$，且 $P_{ij}P_{kj}>0$，则
$\langle e_{ji},e_{jk}\rangle=0$。

证明中 (126.1) 只剩非零标量乘以可逆酉 $U_{ji}^{\dagger}U_{jk}$，故该标量必须为零。若共同后继不止一个，各项可以在算子意义下相消，不能把“合流必正交”推广到这种情形。该判据与有限维通道的 Kraus/Stinespring 表示相容；参见 M.-D. Choi, “Completely positive linear maps on complex matrices”, *Linear Algebra Appl.* 10 (1975), 285–290，以及 W. F. Stinespring, “Positive functions on $C^*$-algebras”, *Proc. Amer. Math. Soc.* 6 (1955), 211–216。有限维表示的教学来源为 IBM Quantum Learning, [“Channel representations”](https://quantum.cloud.ibm.com/learning/en/courses/general-formulation-of-quantum-information/quantum-channels/representations-of-channels)：其 Kraus、Choi 与 Stinespring 表示说明实现框架，不提供额外的原生取得权限。

## 127. 五模式配置图与指定的边运输

固定外接缝为空，取五个配置
$$
 s_0=\mathrm{null}=000,\quad s_1=2,\quad s_2=25,\quad
 s_3=5,\quad s_4=3.
$$
配置图是方形边 $0\!-\!1\!-\!2\!-\!3\!-\!0$ 加支边 $0\!-\!4$，每条边表示一次合法单比特翻转。它是配置更新图，不是任意窗口串接的 Zeckendorf 词；与第122章的图相同。

给每个配置附加 $K=\mathbb C^2$，故完整可见载体为
$\mathbb C^5\otimes\mathbb C^2$，维数为 $10$。令
$$
 a=-\mathrm iX,\qquad b=-\mathrm iY,\qquad c=ba=\mathrm iZ,
$$
其中 $X,Y,Z$ 是 Pauli 矩阵。于是
$$
 a^2=b^2=c^2=-I,\qquad ac=-ca.
$$
指定正向方形边
$$
 U_{10}=a,\quad U_{21}=c,\quad U_{32}=a^\dagger,\quad U_{03}=c^\dagger.\tag{127.1}
$$
支边 $U_{40}=b$，反向边取伴随，自环取 $I$。这是一项明确的内部运输合同；五个模式的名称或裸的树替换 $\rho$ 都不唯一强迫它。两端位置变化由 $a,c$ 的反对易实现，中间支路由 $b$ 实现；树来源的非单射性、右因子先作用和接缝保留为独立条件。

## 128. 反对易闭路、相干混合与测量次序

本章的参数合同独立于第129章：$p\in[0,1]$、$q=1-p$，故 $p+q=1$，不含 $r$。先去掉支边和自环，考虑四态方形 $0,1,2,3$ 上的酉循环 $S$：
$$
 S|0,\psi\rangle=|1,a\psi\rangle,\quad
 S|1,\psi\rangle=|2,c\psi\rangle,\quad
 S|2,\psi\rangle=|3,a^\dagger\psi\rangle,\quad
 S|3,\psi\rangle=|0,c^\dagger\psi\rangle.
$$
每个输入位置被送到不同的输出位置，内部算子又都酉，故 $S$ 保持任意输入的内积且满射，确为酉。从根 $0$ 返回的内部算子为 $c^\dagger a^\dagger ca=-I$，其他根的闭路算子与之共轭，故
$$
 S^4=-I.\tag{128.1}
$$
取 $p\in[0,1]$、$q=1-p$，并令
$$
 W_p=\sqrt p\,S+\sqrt q\,S^\dagger .
$$
由 $S^{-2}=-S^2$ 和 $p+q=1$，
$$
 W_p^\dagger W_p=I+\sqrt{pq}(S^2+S^{-2})=I.\tag{128.2}
$$
因此负的中心闭路相位使正振幅的两条交叉路径抵消。若把 (128.1) 改成 $S^4=I$，则一般得到 $I+2\sqrt{pq}\,S^2$，只有 $p=0$ 或 $q=0$ 时仍自动酉。

从位置 $0$ 出发，
$$
 W_p^2=2\sqrt{pq}\,I+(p-q)S^2.\tag{128.3}
$$
从确定位置单步出发，正、反两个输出位置正交，概率分别为 $p,q$，与内部态无关。不在中间测量时，两步回到原位置的概率为 $4pq$，因为同一内部态的两条回返振幅相干相加。逐步测量使用同一个明确仪器
$$
 \mathcal J_j(\varrho)=\Pi_jW_p\varrho W_p^\dagger\Pi_j,
 \qquad \Pi_j=|j\rangle\langle j|\otimes I_2,
 \qquad \sum_j\mathcal J_j\text{ 为 CPTP}.
$$
每次实际记录位置后，再作用 $W_p$；正后反、反后正两条回返历史各有概率 $pq$，总和为 $2pq$。这项仪器权限和记录保留是新增条件。当 $p=q=\tfrac12$ 时 $W_p^2=I$，但逐步测量的两步回返概率仍为 $\tfrac12$。输出位置 $I$ 与 $S^2$ 不同，故这些概率对任意内部密度态都成立；单步的 $P$ 不决定多时刻相干。量子行走背景为 Mario Szegedy, [“Spectra of Quantized Walks and a $\sqrt{\delta\epsilon}$ rule”](https://arxiv.org/abs/quant-ph/0401053)。该文研究量子化二部行走、谱及相应搜索模型；本章的四态反对易闭路与测量次序结论由上述有限酉计算证明，不援引其搜索加速结论。

## 129. 第五模式的记录下界与无记录缺陷

取 $p,q,r>0$ 且 $p+q+r<1$，令配置转移矩阵为
$$
 P=\begin{pmatrix}
 1-p-q-r&p&0&q&r\\
 q&1-p-q&p&0&0\\
 0&q&1-p-q&p&0\\
 p&0&q&1-p-q&0\\
 r&0&0&0&1-r
 \end{pmatrix}.\tag{129.1}
$$
输入 $1$ 的正支撑为 $\{0,1,2\}$，输入 $4$ 的正支撑为 $\{0,4\}$，唯一共同后继为 $0$，其概率分别为 $q,r$。输入 $3$ 的正支撑为 $\{0,2,3\}$，与输入 $4$ 的唯一共同后继仍为 $0$，概率分别为 $p,r$。由引理126.3，任何共同等距实现必须满足
$$
 \langle e_{0,1},e_{0,4}\rangle=0,\qquad
 \langle e_{0,3},e_{0,4}\rangle=0.\tag{129.2}
$$
因此记录空间至少含两个正交方向。这是矩阵 (129.1)、边酉和全输入叠加的共同合同的结论，不是任意五态量子实现的普遍下界。

若强令所有记录相同，则候选 $V_0$ 在输入块 $(1,4)$ 上的缺陷为
$$
 (V_0^\dagger V_0-I)_{1,4}
 =\sqrt{qr}\,U_{0,1}^\dagger U_{0,4}.\tag{129.3}
$$
故 $\|V_0^\dagger V_0-I\|\ge\sqrt{qr}$。例如 $p=\tfrac14,q=r=\tfrac18$ 时下界为 $1/8$，属于结构缺陷而非数值误差。确切地说，该块是用两个正交配置投影对总缺陷作压缩，压缩的算子范数不超过总范数；其中酉乘积的范数为一，故给出所述下界。两项正交条件不要求 $e_{0,1}$ 与 $e_{0,3}$ 也互相正交。分别检查每个输入的记录 Gram 矩阵仍不能消除跨输入的算子块。

## 130. 同一边仪器产生概率、酉运输与记录相关矩阵

在 $\mathbb C^5\otimes\mathbb C^2$ 上定义边 Kraus 算子
$$
 K_{ji}=\sqrt{P_{ij}}\,|j\rangle\langle i|\otimes U_{ji}
$$
并给每条正边一个互相正交的记录向量 $|i\to j\rangle$。正边数为
$4+3+3+3+2=15$，等距为
$$
 V_{\rm edge}=\sum_{i,j}K_{ji}\otimes|i\to j\rangle.
$$
逐边有
$$
 K_{ji}^\dagger K_{ji}=P_{ij}|i\rangle\langle i|\otimes I_2,
 \qquad K_{ji}K_{ji}^\dagger=P_{ij}|j\rangle\langle j|\otimes I_2.
$$
因此行随机性给出 $\sum_{ji}K_{ji}^\dagger K_{ji}=I$，所以
$\mathcal E(\varrho)=\sum_{ij}K_{ji}\varrho K_{ji}^\dagger$ 是 CPTP；(129.1) 的列和也为一，故同一通道还是 unital。

**定义 130.1（初始化与实际历史）。** 每轮使用一份新的边记录系统，并实际供应边仪器 $\mathcal J_{ji}(\varrho)=K_{ji}\varrho K_{ji}^\dagger$ 及其记录读取。历史输入有以下两种明确合同：一是固定已知起点 $i_0$，其内部态任意，亦可与未触动参考相关；二是实际供应配置准备或初始化记录，使起点具有声明的分布 $\pi$，并保留正交初始记录 $|i_0\rangle_{R_0}$。例如允许的块对角初始来源为
$$
 \varrho_{\mathrm{in}}=\sum_i\pi_i|i\rangle\langle i|\otimes\varrho_i,
 \qquad \pi_i\ge0,\quad\sum_i\pi_i=1,
$$
并实际关联 $R_0$。若要从任意相干配置取得这个起点记录，须另外供应
$J(|i\rangle\otimes\psi)=|i\rangle\otimes\psi\otimes|i\rangle_{R_0}$；读取或丢弃 $R_0$ 会影响配置相干，不能作为免费初始化。内部态 $\varrho_i$ 不被初始配置标签取代。

对 $N\ge1$ 的实际边历史 $h=(i_0,\ldots,i_N)$，相乘同一仪器的 Kraus 算子得
$$
 K_h=K_{i_Ni_{N-1}}\cdots K_{i_1i_0}
 =\sqrt{\prod_{t=1}^NP_{i_{t-1}i_t}}\,
 |i_N\rangle\langle i_0|\otimes U_h,
$$
$$
 p_h=\pi_{i_0}\prod_{t=1}^N P_{i_{t-1}i_t},\qquad
 U_h=U_{i_Ni_{N-1}}\cdots U_{i_1i_0}.\tag{130.1}
$$
这里 $P$ 的行指标始终是来源，列指标是后继。因为
$K_h^\dagger K_h=(\prod_tP_{i_{t-1}i_t})|i_0\rangle\langle i_0|\otimes I_2$，其迹给出 $p_h$，正概率历史的条件内部态为 $U_h\varrho_{i_0}U_h^\dagger$；加入参考时改用 $U_h\otimes I$。故路径权重和条件运输均由这些实际边分支产生。

固定根时取
$|e_h\rangle=\bigotimes_{t=1}^N|i_{t-1}\to i_t\rangle$；多起点合同则取
$|e_h\rangle=|i_0\rangle_{R_0}\otimes\bigotimes_{t=1}^N|i_{t-1}\to i_t\rangle$。两种合同都给出 $\Gamma_{hk}=\langle e_k|e_h\rangle=\delta_{hk}$：非空的不同路径至少有一条边标签不同；多起点时初始标签也可区分。$N=0$ 时乘积为一、$U_h=I_2$；固定根域只有一条空边历史，而多起点域由实际保留的 $R_0$ 保证不同单点历史正交。没有固定根或初始记录，空边记录都相同，不能宣称此时 $\Gamma=\delta$。同一起点下不同未知内部来源亦不由历史标签自动区分。

于是 $p,U,\Gamma$ 来自同一边仪器及明列的初始化，而非分别择优。经典读取记录不会自动反演为相干分支；这仍需保留相关记录系统、相位相容控制及实际联合反转权限。

不同 $|j\rangle\langle i|$ 的向量化彼此 Hilbert–Schmidt 正交，故这一个完整边通道的 15 个非零 Kraus 算子线性无关，Choi 矩阵
$$
 J(\mathcal E)=\sum_{ij}|\operatorname{vec}K_{ji}\rangle\langle\operatorname{vec}K_{ji}|
$$
的 15 个非零正交方向使其秩恰为 $15$：每个向量的范数平方为 $\operatorname{tr}(K_{ji}^\dagger K_{ji})=2P_{ij}>0$，不同边的内积为零。若纯初始环境维数为 $m$，对环境基取分量最多得到 $m$ 个 Kraus 算子，故 $\operatorname{rank}J\le m$；这里 $m\ge15$，边记录实现达到。此数是一轮指定通道的最小纯环境维数，不包含多起点初始化记录、时钟或全部历史档案的累计资源。这个数只属于指定的完整边通道；不能推广为所有具有同一 $P$ 的量子实现都至少需要 $15$ 维环境。Choi 秩与最小 Kraus 数的标准事实参见 Choi 1975 及 John Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018，[第2章，定理2.22及推论2.27](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)。

## 131. 端点因子化、绕行数与中心相位

令
$$
 G_0=I,\quad G_1=a,\quad G_2=ca=-b,\quad
 G_3=a^\dagger ca=-c,\quad G_4=b,
$$
并令 $d_0,d_1,d_2,d_3,d_4=0,1,2,3,0$。对有向边定义权重 $w_{ji}$：正方形正向为 $+1$，反向为 $-1$，支边和自环为 $0$。置
$$
 \nu_{ji}=\frac{w_{ji}-d_j+d_i}{4}.\tag{131.1}
$$
它为整数，唯一非零情形是 $3\to0$ 的 $\nu=1$ 与反向 $0\to3$ 的 $\nu=-1$。逐边直接验证
$$
 U_{ji}=(-1)^{\nu_{ji}}G_jG_i^\dagger.\tag{131.2}
$$
证明可逐边穷尽：生成树上的 $0\to1,1\to2,2\to3,0\to4$ 分别由 $G_1=aG_0,G_2=cG_1,G_3=a^\dagger G_2,G_4=bG_0$ 得到，且这些边的 $\nu=0$。切边 $3\to0$ 有 $\nu=1$，由 $G_3=-c$ 得 $-G_0G_3^\dagger=c^\dagger=U_{03}$。反向边取伴随时 $\nu$ 变号，而中心实符号保持；自环为 $G_iG_i^\dagger=I$。这覆盖全部15条正边。
对路径 $h=(i_0,\ldots,i_N)$，令 $W(h)=\sum_tw_{i_ti_{t-1}}$、$k(h)=\sum_t\nu_{i_ti_{t-1}}$。相邻端点因子望远镜相消，得到
$$
 k(h)=\frac{W(h)-d_{i_N}+d_{i_0}}4,\qquad
 U_h=(-1)^{k(h)}G_{i_N}G_{i_0}^\dagger.\tag{131.3}
$$
闭路满足 $W=4k$，酉为 $(-1)^kI$，所以中心相位只看净绕行的奇偶；同一路径的概率偏置另给正特征 $(p/q)^{4k}$。二者是不同观测量。在声明的 $Q_8$ 提升中，同步替换 $a\mapsto b,b\mapsto c$ 给出 $c=ba\mapsto cb=a$，且固定中心 $-I$。故把每条边的原子表达式按此自同构运输，方形负闭路符号仍保持；概率 $P$、配置图合法性与实际操作菜单的运输必须另行指定。这不把有向三循环、原树增长和带符号提升混为同一过程。

## 132. 可移动的三维关系块与端点 holonomy

对任意 $A\in M_2(\mathbb C)$，定义随配置框架移动的关系块
$$
 \overline A=\sum_i|i\rangle\langle i|\otimes G_iAG_i^\dagger.\tag{132.1}
$$
若 $\mathcal E^*$ 是边通道的 Heisenberg 对偶，则由 (131.2)
$$
 \mathcal E^*(\overline A)
 =\sum_{i,j}P_{ij}|i\rangle\langle i|\otimes G_iAG_i^\dagger
 =\overline A.\tag{132.2}
$$
映射 $A\mapsto\overline A$ 还是保持单位和伴随的单射代数表示，因为逐块有
$$
 \overline A\,\overline B=\overline{AB},\quad
 \overline{A^\dagger}=(\overline A)^\dagger,\quad
 \overline I=I_{10}.
$$
其中配置 $0$ 的块就是 $A$，故核为零，说明单射性。
因此
$$
 \overline X^2=\overline Y^2=\overline Z^2=I_{10},\qquad
 \overline X\overline Y=\mathrm i\overline Z,\quad
 \overline Y\overline Z=\mathrm i\overline X,\quad
 \overline Z\overline X=\mathrm i\overline Y,
$$
反向乘积各取负号，$\operatorname{span}_{\mathbb C}\{I_{10},\overline X,\overline Y,\overline Z\}$ 表示完整 $M_2(\mathbb C)$。同一边运输固定全部 $\overline A$，包括三个非恒定实 Pauli 方向；这些是内部逻辑坐标，不是配置位置轴。

取 $D=\sum_i|i\rangle\langle i|\otimes G_i^\dagger$，则
$$
 DK_{ji}D^\dagger=(-1)^{\nu_{ji}}\sqrt{P_{ij}}\,|j\rangle\langle i|\otimes I_2.\tag{132.3}
$$
故共轭后的通道为 $\widetilde{\mathcal E}=\mathcal P\otimes\operatorname{id}_{2}$，其中配置通道必须明确定义为
$$
 \mathcal P(A)=\sum_{i,j}P_{ij}\langle i|A|i\rangle\,|j\rangle\langle j|.\tag{132.4}
$$
它删除配置非对角元并执行 Markov 推进；随机矩阵 $P$ 本身不是量子通道。对任意配置—逻辑—参考联合密度态 $\omega_{CLR}$，取框架变换后的输入，乘积通道给出
$$
 \operatorname{Tr}_C[(\mathcal P\otimes\operatorname{id}_{LR})(\omega_{CLR})]
 =\operatorname{Tr}_C\omega_{CLR}.
$$
证明是将 $\omega=\sum_{i,k}|i\rangle\langle k|\otimes\omega_{ik}$ 展开；输出为
$\sum_{i,j}P_{ij}|j\rangle\langle j|\otimes\omega_{ii}$，对配置取迹并用行和一即得。这对全部密度态及未触动参考成立，保留完整逻辑密度和其参考关联，不只三个标签；配置相干及配置与逻辑的全部联合态并不保持。环境只记录配置边，不读逻辑因子，增加会读取该因子的耦合后不能沿用此保护结论。实际框架读取和运输资源仍须供应。这里是一个具体的逻辑接口实例，不是对所有无噪声子系统的新一般定理；可参见 David W. Kribs、Raymond Laflamme、David Poulin、Maia Lesosky, [“Operator quantum error correction”](https://arxiv.org/abs/quant-ph/0504189), *Quantum Information and Computation* 6 (2006), 382–399。该文统一标准纠错、无退相干子空间和无噪声子系统；本图的保护由上述乘积通道直接证明。

**定理 132.1（端点密度态充分性）。** 在有限连通无向图上，为每条定向边供应酉，并明确要求反向边为其逆 $U_{ij}=U_{ji}^{-1}=U_{ji}^\dagger$；空路径取 $I$。对全部内部密度态，路径伴随作用只依赖起终点，当且仅当每个闭路满足 $U_\gamma=e^{\mathrm i\theta_\gamma}I$。

**证明。** 必要性比较同一顶点的空路径与任意闭路。若 $\operatorname{Ad}_{U_\gamma}$ 固定全部密度态，则固定全部秩一投影；这些投影实线性张成 Hermitian 矩阵，故 $U_\gamma$ 与全部复矩阵相交换。矩阵单位的交换关系迫使它为标量，酉性给出模一相位。充分性取同端点路径 $h,k$。反向边的逆假设保证 $U_{k^{-1}}=U_k^\dagger$，故先走 $h$ 再反走 $k$ 的闭路酉为 $U_k^\dagger U_h=e^{\mathrm i\theta}I$，于是两路径的伴随作用相同。连通性保证所需端点路径存在。 $\square$

反向运输若未供应为正向运输的逆，就不能由“相对路径是闭路”推出此判据。对态的充分性不等于对带控制的相干路径比较的充分性，因为中心相位仍可被实际提供的干涉读出。

## 133. 稳定块、平稳熵与严格路径箭头

以均匀初始分布 $\pi_i=1/5$ 按定义130.1的初始化启动 (129.1) 的边仪器，每轮使用新记录并实际取得边标签。双随机性使每步配置分布仍为均匀分布。令 $h^\leftarrow$ 为路径倒序，定义长度 $N$ 的路径箭头
$\Sigma_N=D_{\rm KL}(P_N\Vert P_N^\leftarrow)$。正方形边的正、反概率分别为 $p,q$，每个分支边和自环在倒序中相互抵消，因而
$$
 \log\frac{\Pr(h)}{\Pr(h^\leftarrow)}=W(h)\log\frac pq,\qquad
 \Sigma_N=N\,\frac45(p-q)\log\frac pq.\tag{133.1}
$$
平稳时单步绕行增量的期望为 $\mathbb E w=4(p-q)/5$；相加 $N$ 步，(133.1) 即由路径对数比的期望得到。四条方形无向边各贡献 $\frac15(p-q)\log(p/q)$，故 (133.1) 在 $N\ge1$、$p\ne q$ 时严格为正；$N=0$ 时为零，平衡情形 $p=q$ 也为零。

由于列和为一，完整可见载体上的
$\varrho_* =I_{10}/10$ 是固定态，且其 von Neumann 熵恒为 $\log10$。因此同一明确操作可以同时保持逻辑 Pauli 关系、保持该可见固定态的熵，并具有严格的记录路径箭头。这里的倒序是路径分布的比较，不是包含全部微观自由度、热浴或局部详细平衡的物理时间反演；故 (133.1) 不单独等同于热力学熵产生。中心相位特征 $(-1)^{k(h)}$ 在 $p=q$ 时仍可非平凡，概率特征 $(p/q)^{4k}$ 则在平衡时为一；交换 $p,q$ 只反转后者的方向。Joel L. Lebowitz、Herbert Spohn, [“A Gallavotti-Cohen Type Symmetry in the Large Deviation Functional for Stochastic Dynamics”](https://arxiv.org/abs/cond-mat/9811220) 研究 Markov 过程的涨落对称，并在局部详细平衡条件下联系熵产生；本章有限离散路径公式由直接相乘证明，不从该文借入未供应的热浴条件。

## 134. 小任务边界与任意相干全历史的残余代价

固定初始配置 $i_0=0$ 和长度 $N$。对合法路径定义
$$
 B(h)=(i_N,W(h)).
$$
该摘要不存储未知内部量子态 $\psi$；完整逻辑态仍需另外保留量子载体。令第133章的平稳路径律为
$$
 P_N^{\mathrm{stat}}(h)=\frac15\prod_{t=1}^NP_{i_{t-1}i_t},\qquad
 \ell_{\mathrm{stat}}(h)=\log\frac{P_N^{\mathrm{stat}}(h)}{P_N^{\mathrm{stat}}(h^\leftarrow)}
 =W(h)\log(p/q).
$$
本章只把这个具名的平稳比较量 $\ell_{\mathrm{stat}}$ 限制到固定根历史，不把它改成固定 $\delta_0$ 初始律自身的倒序比值。确切地说
$P_N^0(h)=\mathbf1_{i_0=0}\prod_tP_{i_{t-1}i_t}$，其自身倒序律在 $h$ 上为 $P_N^0(h^\leftarrow)$。一步见证 $h=(0,1)$ 有正向概率 $p$，倒序路径 $(1,0)$ 在同一 $\delta_0$ 初始律下概率为零；而平稳比较的两权重为 $p/5,q/5$，给出有限 $\ell_{\mathrm{stat}}=\log(p/q)$。两个比较问题必须区分。
它最多取 $5(2N+1)$ 个值，并可按边更新
$$
 (i,w)\longmapsto(j,w+w_{ji}),\qquad
 \Pi_{n+1}(j,w)=\sum_iP_{ij}\Pi_n(i,w-w_{ji}).\tag{134.1}
$$
递推初始化为 $\Pi_0(j,w)=\mathbf1_{j=0}\mathbf1_{w=0}$，$\Pi_n$ 是实际固定根路径摘要的概率分布。给定 $B(h)$，终点配置、后续 Markov 律、(131.3) 的全部内部酉和具名比较量 $\ell_{\mathrm{stat}}(h)$ 都已确定，因为 $k=(W-d_{i_N})/4$；这不读取未知 $\psi$。令实际标签数为 $C_N=|B(\mathcal H_N(0))|$，则
$$
 C_N\le5(2N+1),\qquad
 L_N=\lceil\log_2 C_N\rceil\le\lceil\log_2[5(2N+1)]\rceil.
$$
左侧 $C_N$ 是标签数，$L_N$ 才是固定长度二进制编码的比特数，固定模型下 $L_N=O(\log(N+1))$。$N=0$ 时只有历史 $(0)$，$C_0=1,L_0=0$。标签量小不表示时钟、实际边读数和原生读取资源免费，未执行的分支也不能冒充已取得的读数。

考虑更强的任意合法历史寄存器相干域，要求等距作用
$$
 |h\rangle\otimes\psi\longmapsto |B(h)\rangle\otimes U_h\psi\otimes|r_h\rangle.\tag{134.2}
$$
若 $h\ne k$ 而 $B(h)=B(k)$，则全体 $\psi,\phi$ 的输入正交性给出
$\langle r_h,r_k\rangle\langle\psi,U_h^\dagger U_k\phi\rangle=0$。对任意单位 $\psi$ 取 $\phi=U_k^\dagger U_h\psi$，第二因子为一，故 $\langle r_h,r_k\rangle=0$。同一纤维的记录遂两两正交；映射的等距性也要求每个 $r_h$ 归一化。因此
$$
 \dim R\ \ge\ \max_b|B^{-1}(b)|.\tag{134.3}
$$
若声称精确最小值，还需给出每个纤维的正交残差编码上界；这里只使用下界。由 (129.1) 的严格参数域，每个顶点至少有两个正概率后继；长度零有一条路径，每条路径每步至少可作两种不同延长，归纳得从起点 $0$ 的合法路径数至少为 $2^N$。按至多 $5(2N+1)$ 个纤维作抽屉原理，存在纤维大小
$$
 \max_b|B^{-1}(b)|\ge
 \left\lceil\frac{2^N}{5(2N+1)}\right\rceil,\qquad
 \log_2\dim R\ge N-\log_2(5(2N+1)).\tag{134.4}
$$
(134.4) 是任意相干全历史域的残余记录下界；它不适用于只准备好的实际历史像，也不是末端通道 $\mathcal E^N$ 的最小环境维数指数下界。此处 (134.2) 要对整个 $\operatorname{span}\{|h\rangle:h\in\mathcal H_N(0)\}\otimes\mathbb C^2$ 以及其任意叠加保持内积；一组制备好的分支振幅或单个末端通道不提供这个域。把同一终端态映射与保留全部历史当作同一合同，会错误地抹去旧来源与接缝关联。

## 135. 共同实现、中心循环、移动保护与记录成本

**定理 135.1（五模式相干接缝的有限共同实现）。** 在完整五态参数 $p,q,r>0,p+q+r<1$、矩阵 (129.1)、边酉 (127.1)、正交边记录及定义130.1的初始化与实际读取合同下，下列结论成立；其中第2项为具有独立参数的四态对照：

1. 跨输入共同等距的充要条件是 (126.1)；唯一共同正后继强制正交记录，故第五模式的两条合流分别给出 (129.2)。
2. 只含方形且无自环的四态对照取 $p_4\in[0,1],q_4=1-p_4$，允许 (128.2) 的反对易相干混合 $W_{p_4}$。这个 $p_4+q_4=1$ 的参数域与完整五态的 $p+q+r<1$ 分开，不能把它当作完整五态的无记录实现。
3. 完整边仪器 $V_{\rm edge}$ 按来源行的路径权重 (130.1) 同时产生 $p_h$、条件酉 $U_h$ 和记录 $\Gamma_{hk}=\delta_{hk}$；空边历史也遵守固定根或正交初始化记录的条件。该指定的一轮通道的 Choi 秩恰为 $15$，不推广到所有同 $P$ 的量子实现。
4. 因子化 (131.3) 给出中心闭路；反向边明确为逆时，定理132.1给出全部内部密度态端点充分的充要条件。同一框架下 (132.2) 固定完整逻辑 $M_2$ 代数，乘积通道保持任意逻辑密度及其未触动参考关联；三个 Pauli 方向是其非恒定实坐标。
5. 在 $N\ge1,p\ne q$ 时，均匀平稳块的可见熵保持与 (133.1) 的严格正路径箭头共存；$N=0$ 或 $p=q$ 时该箭头为零。中心相位和概率偏置分别属于酉与统计两类读出。
6. 固定根小任务摘要 $B=(i_N,W)$ 确定未来配置律、内部酉和 $\ell_{\mathrm{stat}}=W\log(p/q)$，其标签比特数为 $O(\log(N+1))$；它不存储未知量子态，也不替代自身 $\delta_0$ 初始律的倒序比较。任意相干全历史输入域仍受 (134.3)–(134.4) 的残余记录下界约束。

**证明。** 第1项由定理126.2及引理126.3，代入五模式的共同支撑即得；第2项由 (128.1)–(128.3)，四态对照只检验反对易闭路的相干抵消；第3项由 Kraus 算子正交、行、列随机性及 (130.1)；第4项由逐边端点因子望远镜、反向逆边的闭路标量判据及乘积通道的参考保持式；第5项由 unital 固定态、平稳路径倒序似然比和 $(p-q)\log(p/q)>0$ 的条件；第6项由初始化后的 (134.1)、具名平稳比较量及任意相干全域内积条件和抽屉原理。各项所需的概率、控制、辅助记录和新环境均是本定理明列的合同，不从原生树语法或实际三维空间自动取得。 $\square$

原生来源、五模式接缝和配置语义承接钉版 [《FIB_RELATIONAL_CONTINUATION_GEOMETRY》](https://github.com/the-omega-institute/trureturing/blob/6247af628aac8e4688aedb6a4cb1cd42642b578a/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)。实际 Read、事件取得、控制与时钟权限必须按原接口供应；本篇的 Read 指定义130.1实际取得边仪器标签的事件，可分辨或全路径公式不等于已取得某条历史。同版 [《联合来源、量子关系与有限时钟》命题1.1](https://github.com/the-omega-institute/trureturing/blob/6247af628aac8e4688aedb6a4cb1cd42642b578a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md) 给出数值编码不等于可取得操作及有向时钟的边界，不供应额外读数权限。Felix A. Pollock、César Rodríguez-Rosario、Thomas Frauenheim、Mauro Paternostro、Kavan Modi, [“Operational Markov condition for quantum processes”](https://arxiv.org/abs/1801.09811) 讨论操作意义的多时刻 Markov 条件和记忆，不从一时刻通道推出多时刻相干。Paolo Facchi、Saverio Pascazio, [“Quantum Zeno dynamics: mathematical and physical aspects”](https://arxiv.org/abs/0903.3297) 是前卷投影保护的背景综述，允许投影子空间内继续演化；本篇边通道的保护由第132章直接证明，并非 Zeno 冻结。共同原生交互能否同时产生所选 $P,U,\Gamma$，相位控制、长程资源、无限递归成本、实际距离和物理三维空间桥，仍是未证条件。

## 追加锚（第126–135章以下为增补区）

## 136. 观察者实际取得的对象与量具联合关系

**定义 136.1（取得、保存与继续使用）。** 固定观察者 $O$。一个实际关系接口包含：已经取得的初始参照事件及当前可用记录 $r_0$；在当前记录和来源条件下允许执行的动作；动作实际返回的结果；把需要的区别留在可再次访问载体上的保存操作；以及以这些记录为输入的后续比较和动作。一次接续写为

$$
r\xrightarrow{(a,y)}r',
$$

表示动作 $a$ 已被允许并实际执行、结果 $y$ 已返回，而且 $r'$ 是接续后实际保留、能够继续使用的记录。可写下动作名称不等于已取得动作；能在表达式中保留 $y$ 不等于已实现记录载体。若比较需要旧读数，须在比较时仍可取到旧记录，或明确使用仍保存该区别的旧来源、环境等耦合载体。来源受动作改变时，改变也属于接口条件，不把各次读数当成同一未变来源的独立副本。

这里的起点是观察者已取得的内部关系，不要求另有观察者完整读取所有外部状态，也不裁定外界存在与否。前卷的准备态、环境、相位控制及本卷的历史边界都是各自条件模型的来源结构；把它们接入此接口，仍须取得并维持相应实际实现。参照事件是观察者已经取得并选定的比较起点；只有进一步取得位移比较时，才能相对于它称一个仿射原点，不能外加绝对位置。

**假设 136.2（局部线性读出合同）。** 在一个已经取得、可比较的局部实二维线性载体中，选表示

$$
c=\begin{pmatrix}u\\v\end{pmatrix},\qquad \ell=(a,b).
$$

$c$ 表示对象，$\ell$ 表示量具。声明允许的对象操作矩阵集合 $\mathcal A$；只有实际执行并返回结果的 $A\in\mathcal A$ 才供给读数

$$
y_A=\ell Ac.
$$

本式假定读出是无偏线性的，矩阵含义已知。固定量具指同一次运行内维持同一个 $\ell$ 及同一标度，而不是凭符号宣布量具不变。对树来源采用此载体，还须另供来源到 $c$ 的读出；载体坐标并不等于来源的全部有序信息。

**定理 136.3（联合关系及共同换基不变量）。** 令 $R=c\ell$。对每个允许且已执行的 $A$，有 $y_A=\operatorname{tr}(AR)$。若可逆 $S$ 同时改变对象、量具和操作的表示，

$$
c'=Sc,\qquad \ell'=\ell S^{-1},\qquad
A'=SAS^{-1},\qquad R'=SRS^{-1},
$$

则 $\ell'A'c'=y_A$，亦即 $\operatorname{tr}(A'R')=\operatorname{tr}(AR)$。

证明（136.3）。迹的坐标展开为 $\operatorname{tr}(Ac\ell)=\sum_i(Ac)_i\ell_i=\ell Ac$；同时换基后，$c'\ell'=Sc\ell S^{-1}$，且

$$
\ell S^{-1}(SAS^{-1})Sc=\ell Ac.
$$

这是同一关系的共同表示变换。它不宣布 $S$ 已成为新的实际操作，也不把换基后仍须运输的量具免费留在旧坐标中。$\square$

**命题 136.4（共同尺度与相对尺度）。** 对任意 $s\in\mathbb R\setminus\{0\}$，共同变化 $c\mapsto sc,\ell\mapsto s^{-1}\ell$ 保持 $R$ 和全部 $y_A$。只将对象改为 $sc$ 而保持量具，则每个读数改为 $s y_A$；这与共同变化不同，只有在相应读数为零或 $s=1$ 时才不改变该读数。

证明（136.4）。两因子相乘时尺度抵消，单改对象时线性读出带因子 $s$。例如 $c=(1,0)^T,\ell=(1,0),A=I$ 给读数一，单改对象后为 $s$。即便以后精确恢复 $R$，共同尺度仍给多种对象—量具分解；若对象或量具为零，分解还更不唯一。因此恢复联合关系不能称为分别取得两个绝对表示。$\square$

**来源 136.5（复用范围）。** [《FIB 自校准关系数学》，版本6247af628aac8e4688aedb6a4cb1cd42642b578a，第1–6章及定义10.1、10.2](https://raw.githubusercontent.com/the-omega-institute/trureturing/6247af628aac8e4688aedb6a4cb1cd42642b578a/docs/develop/theory/FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md)给出迹读出、共同规范及固定量具累计路径。本章沿用这些关系结果；其正实秩一来源域及正尺度分类不被扩成任意实向量的正性声明。本章允许实线性局部表示，实际可达的来源子集仍由已取得接口指定。

## 137. FIB 推进、交换次序差与单链恢复

**定义 137.1（原树、组成与另声明的交换）。** 原生来源是以 $\alpha,\beta$ 为叶的自由有序二叉树，节点 $\langle s,t\rangle$ 保留左右次序和括号。替换 $\rho$ 满足

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

组成读出另定义为 $c(\alpha)=e_1,c(\beta)=e_2$ 及 $c(\langle s,t\rangle)=c(s)+c(t)$。由结构归纳，$c(\rho t)=Mc(t)$，其中

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

归纳的叶步分别为 $e_1\mapsto e_2$ 和 $e_2\mapsto e_1+e_2$；节点步使用 $M$ 的线性性。这只证明所定义的组成读出相容，不证明组成能恢复原树。

标签交换或线性坐标交换 $J$ 是另声明的动作，其局部矩阵为

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

原树标签交换若实际取得，可定义为同时交换所有叶标签而保留括号；局部组成上对应 $J$。仅由 $\beta=\rho\alpha$ 不能取得这个逆向交换，更不能取得交换门的物理执行权。

**定理 137.2（次序差的四周期结构）。** 在实线性表达层，

$$
MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\qquad
JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
K=MJ-JM=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

因此 $K^2=-I,K^4=I,K^TK=I$，且 $JKJ=-K$。对标准内积中的非零 $u$，四点 $u,Ku,-u,-Ku$ 是以零为中心的正方形；$K$ 依次循环这四点，交换标签改变其绕行方向。

证明（137.2）。相乘给所列矩阵；$K(x,y)^T=(-y,x)^T$，再作用一次为 $(-x,-y)^T$，给平方与四次幂。$K^T=-K$，故 $K^TK=-K^2=I$；$JKJ$ 的两个非零元与 $K$ 相反。于是 $u$ 与 $Ku$ 等长且正交，非零时四点互异。相邻边为 $Ku-u$ 与 $-u-Ku$，平方长度都为 $2\|u\|^2$，内积为零；其余边由 $K$ 运输，故构成正方。$JK=-KJ$ 表明同一循环经 $J$ 改写后成为反向循环。$\square$

$MJ-JM$ 的减法属于线性表达。实际执行 $MJ$ 与 $JM$ 的两次序不等于实际执行它们的差；物理过程未必允许相减，也未必允许在两个分支上使用同一未知来源。故本定理首先给 $K$ 的可表达性，尚未给 $K$ 门。

**假设 137.3（固定量具的一条实际链）。** 在定义136.1的接口内，另已取得 $M,J$ 两动作，使用同一个固定量具。初始累计矩阵 $A_0=I$，初始读数计入读取次数；第 $i$ 次动作 $E_i$ 执行后，$A_i=E_iA_{i-1}$。实际先后执行 $E_1=M,E_2=J,E_3=M$，并分别取得、保存初始及三个终态的读数：

$$
A_0=I,\quad A_1=M,\quad A_2=JM,\quad A_3=MJM,
\qquad z_i=\ell A_i c=\operatorname{tr}(A_iR).
$$

这里 $i$ 是动作完成后的累计索引，不是物理时间；矩阵右因子先作用。读取及保存必须符合该链的模型：对象只按声明的动作变化，没有另一个未计入的读出扰动。本合同不重置、不复制未知来源，也不读取尚未执行的另一支 $MJ$。

**定理 137.4（既有逆式的反对称关系读数）。** 令 $R=\begin{pmatrix}p&q\\r&s\end{pmatrix}$。上述实际四读数满足

$$
z_0=p+s,\qquad z_1=q+r+s,\qquad
z_2=p+r+s,\qquad z_3=q+r+2s.
$$

因而

$$
\operatorname{tr}(KR)=q-r=2z_0+2z_1-2z_2-z_3.
$$

证明（137.4）。直接使用《FIB 自校准关系数学》定理4.1的既有关系逆式：$q=z_0+2z_1-z_2-z_3$、$r=z_2-z_0$，相减即得。$KR$ 的对角元为 $-r,q$，其迹为 $q-r$。四读数来自假设137.3的同一累计链，所以不需混用两条实验支路。这个数是由保存读数恢复的关系值，未提供 $K$ 门，也未把已推进的对象恢复到初始对象。$\square$

**定理 137.5（固定模型内的七倍误差界）。** 假定链的矩阵、量具和标度固定，真实值仍为定理137.4的 $z_i$。若已保存的数 $\widehat z_i=z_i+e_i$ 满足 $|e_i|\le\delta$，$\delta\ge0$，则

$$
\left|2\widehat z_0+2\widehat z_1-2\widehat z_2-\widehat z_3
-\operatorname{tr}(KR)\right|\le7\delta.
$$

证明（137.5）。误差是 $2e_0+2e_1-2e_2-e_3$；三角不等式给 $(2+2+2+1)\delta$。对独立区间误差而言，$e_0=e_1=\delta,e_2=e_3=-\delta$ 达到该界，不要求误差独立随机或零均值。$\square$

**边界 137.6（误差与取得）。** 七倍界只约束同一个无偏固定模型的四项数值误差。量具漂移、未知增益、对象受到未建模扰动、动作矩阵失准或记录损坏，若未被证明归入所给 $e_i$ 界，就不在保证内；也不能把源卷第9章的未知固定偏移直接塞进此四读数公式。四数的取得、保存和相同标定是此推论的前提，不是其结论。

## 138. 保长条件下的正方、三角、圆与三周期

**定理 138.1（保四周期的二次尺）。** 已选择实对称正定矩阵 $G$ 为二次尺，若 $K^TGK=G$，则 $G=\lambda I$，$\lambda>0$；反向每个这样的 $G$ 都满足保长条件。

证明（138.1）。写 $G=\begin{pmatrix}a&b\\b&d\end{pmatrix}$，计算得 $K^TGK=\begin{pmatrix}d&-b\\-b&a\end{pmatrix}$。相等强制 $a=d,b=0$；正定性强制 $a>0$。反向用 $K^TK=I$ 即得。$\square$

这项唯一性是在已选二次型及 $K$ 保长条件下的尺子唯一性，不是裸 FIB 给出全部距离。对整体单位作共同选择可取 $\lambda=1$，但改变对象而不共同运输量具不是单位选择。以下采用已声明的标准尺，写 $g(u,v)=u^Tv$、$\|u\|^2=g(u,u)$。

**定理 138.2（长度与有序面积的二阶母式）。** 选定平面定向使 $K$ 为正向四分之一转，定义

$$
\omega_O(u,v)=(Ku)^Tv=u_1v_2-u_2v_1.
$$

则对任意 $u,v\in\mathbb R^2$，

$$
g(u,v)^2+\omega_O(u,v)^2=\|u\|^2\|v\|^2,
$$

$$
\|u-v\|^2=\|u\|^2+\|v\|^2-2g(u,v),\qquad
\Delta(0,u,v)=\frac{|\omega_O(u,v)|}{2}.
$$

若 $u,v$ 非零，定义 $\cos\theta=g(u,v)/(\|u\|\|v\|)$ 和 $\sin\theta=\omega_O(u,v)/(\|u\|\|v\|)$，则两数在单位圆上；它们确定相对有向角模 $2\pi$。若至少一个向量为零，保留上述母式而不定义此角。

证明（138.2）。展开 $(u_1v_1+u_2v_2)^2+(u_1v_2-u_2v_1)^2$，两个混合项抵消，余项为 $(u_1^2+u_2^2)(v_1^2+v_2^2)$。第三边式是前卷定理49.2的内积母式。非退化时，沿 $u$ 的底长为 $\|u\|$，$v$ 到该直线的高度为 $|\omega_O(u,v)|/\|u\|$，底乘高除二给面积；退化时行列式与面积都为零。非零时除以正的范数乘积平方即得单位圆条件。长度与面积绝对值不决定 $\omega_O$ 的符号；此符号依赖已保留的有序对和定向。$\square$

**命题 138.3（经典极化与实际组合条件）。** 实内积载体中的平行四边形式及极化式为

$$
\|u+v\|^2+\|u-v\|^2=2\|u\|^2+2\|v\|^2,\qquad
 g(u,v)=\frac{\|u+v\|^2-\|u-v\|^2}{4}.
$$

在实范数向量空间中，若第一式对全部向量成立，则第二式定义产生原范数的内积。

证明（138.3）。前向和反向均复用前卷定理51.2；反向的经典中间工具是钉版 Mathlib [Analysis/InnerProductSpace/OfNorm.lean，`InnerProductSpace.ofNorm`](https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/OfNorm.lean)。其条件是范数加法交换群、实范数空间及对全部 $u,v$ 成立的平行四边形律；实齐次性以范数连续性和有理数稠密为依据。不是只检验几个长度就取得全部内积。$\square$

在实际任务中，组成 $u+v,u-v$、保持比较参照、读取并保存相应长度，都须由定义136.1的接口取得；组合可能改变来源。极化公式不供应四个同时存在而不受扰动的长度读数，也不将来源的树节点加法读出自动变成可执行向量减法。

**定理 138.4（有理比例参数的圆图与缺失半圈）。** 对每个实数 $t$ 定义表达矩阵

$$
\mathcal R(t)=\frac{(1-t^2)I+2tK}{1+t^2}.
$$

它满足 $\mathcal R(t)^T\mathcal R(t)=I,\det\mathcal R(t)=1$，且

$$
\mathcal R(t)e_1=
\begin{pmatrix}(1-t^2)/(1+t^2)\\2t/(1+t^2)\end{pmatrix}
=\begin{pmatrix}x\\y\end{pmatrix},\qquad x^2+y^2=1.
$$

这些点恰为单位圆除 $(-1,0)$ 外的全部点。对实 $s,t$，若 $st\ne1$，则

$$
\mathcal R(s)\mathcal R(t)=
\mathcal R\!\left(\frac{s+t}{1-st}\right);
$$

若 $st=1$，则乘积为 $-I$，即本有限参数图缺失的半圈。

证明（138.4）。用 $K^T=-K,K^2=-I$，分子与其转置相乘为 $((1-t^2)^2+4t^2)I=(1+t^2)^2I$；矩阵形为 $xI+yK$，行列式为 $x^2+y^2=1$。若 $x^2+y^2=1$ 且 $x\ne-1$，取 $t=y/(1+x)$，则 $1+t^2=2/(1+x)$；代回恢复 $x,y$，证明图的范围。任何有限 $t$ 都有 $1+x=2/(1+t^2)>0$，所以缺点确实不被取得。

乘积的分子为

$$
\big((1-s^2)(1-t^2)-4st\big)I
+2(s+t)(1-st)K.
$$

置 $a=1-st,b=s+t$，有 $a^2+b^2=(1+s^2)(1+t^2)$，而两个系数为 $a^2-b^2,2ab$。$a\ne0$ 时除以 $a^2$ 得所列参数合成。$a=0$ 时 $s,t$ 同号且非零，故 $b\ne0$，系数归一化为 $-1,0$，乘积为 $-I$。$\square$

$t$ 是关系比例参数，不是预置物理时间。有理 $t$ 的每个表达只需有限分子分母；这不保证操作 $\mathcal R(t)$ 已可执行。数学上，以有理参数逼近实参数，再以 $|t|\to\infty$ 加上缺点，可得到整圆的完备化；用到了实数连续性和极限，不供应免费的无限精度读出或无限操作资源。

**定理 138.5（三周期的另一把尺）。** 在表达层令

$$
Z=I+2J-2M=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
C=ZM=\begin{pmatrix}0&1\\-1&-1\end{pmatrix}.
$$

有 $C^2+C+I=0,C^3=I$。它保持

$$
Q(a,b)=a^2+ab+b^2,
\qquad G_{\triangle}=\begin{pmatrix}1&1/2\\1/2&1\end{pmatrix}>0,
\qquad C^TG_{\triangle}C=G_{\triangle},
$$

但不保持标准尺 $I$。在对应内积下，同一映射可表示为转角绝对值 $120^\circ$ 的旋转；这须共同变换向量、坐标和量具。

证明（138.5）。直接计算 $C^2=\begin{pmatrix}-1&-1\\1&0\end{pmatrix}$，加 $C+I$ 为零；乘以 $C-I$ 给 $C^3-I=0$。$C(a,b)^T=(b,-a-b)^T$，代入 $Q$ 得 $b^2-b(a+b)+(a+b)^2=a^2+ab+b^2$。$Q=(a+b/2)^2+3b^2/4$ 给正定性及矩阵保长。标准尺下 $\|Ce_2\|^2=2$，而 $\|e_2\|^2=1$，所以不能冒用原来的直角尺。

取

$$
P=\begin{pmatrix}1&1/2\\0&\sqrt3/2\end{pmatrix},\qquad
P^TP=G_{\triangle},\qquad
PCP^{-1}=\begin{pmatrix}-1/2&\sqrt3/2\\-\sqrt3/2&-1/2\end{pmatrix}.
$$

新表示 $Pc$ 与按 $P^{-1}$ 运输的量具给同一关系；所列矩阵在新标准尺上是有向 $-120^\circ$ 旋转。反选定向会改角的符号。经典因式分解

$$
a^3-b^3=(a-b)(a^2+ab+b^2)
$$

含有同一个二次型，沿用前卷第30–31、49、52章的条件平面解释；不是立方次数决定三维空间。$Z$ 使用的加减仍是表达运算，不由这个恒等式取得反射门或 $C$ 门。$\square$

## 139. 单位定向体积、手性与法向接口

**假设 139.1（已建立的三维内积与体积）。** 本章仅在已经声明的三维实内积空间 $(V,g)$ 中讨论。观察者选择并保存一个定向 $O$，并取与 $g$ 相容的单位定向体积 $\operatorname{Vol}_O$：对任何同定向的正交单位基 $(e_1,e_2,e_3)$，$\operatorname{Vol}_O(e_1,e_2,e_3)=1$。体积是交替三线性形式；实际空间若要采用它，还须取得标定、保存定向及所需比较。仅取得某个非零体积形式而不标定单位，不能使用下面的单位范数公式。

**定理 139.2（体积定义法向及规范化条件）。** 对任意 $u,v\in V$，存在唯一向量 $B_O(u,v)$，满足对全部 $w\in V$

$$
g(B_O(u,v),w)=\operatorname{Vol}_O(u,v,w).
$$

它对 $u,v$ 双线性，$B_O(v,u)=-B_O(u,v)$，且垂直于 $u,v$。在假设139.1的单位体积下，

$$
\|B_O(u,v)\|^2=\|u\|^2\|v\|^2-g(u,v)^2.
$$

若改用 $\widetilde{\operatorname{Vol}}=\kappa\operatorname{Vol}_O$，$\kappa\ne0$，则 $\widetilde B=\kappa B_O$，范数平方为上述右边的 $\kappa^2$ 倍。

证明（139.2）。在正交单位基中，任一线性泛函 $L$ 由 $b=\sum_iL(e_i)e_i$ 表示为 $L(w)=g(b,w)$。若两向量都表示它，它们之差 $d$ 对全部 $w$ 内积为零，取 $w=d$ 得 $d=0$；这就是有限维内积非退化的表示论证。用于 $L(w)=\operatorname{Vol}_O(u,v,w)$ 即给存在唯一性，并由唯一性得双线性和反序负号。取 $w=u,v$，交替性给零，所以垂直。

在同定向的正交单位基中，表示向量的坐标为

$$
B_O(u,v)=
(u_2v_3-u_3v_2,\ u_3v_1-u_1v_3,\ u_1v_2-u_2v_1).
$$

三项平方和为 $\sum_{i<j}(u_iv_j-u_jv_i)^2$；展开后正是 $(\sum_i u_i^2)(\sum_i v_i^2)-(\sum_i u_iv_i)^2$，得范数式。改变体积尺度时，$\kappa B_O$ 满足新的表示等式，唯一性给最后结论。例如原单位基下 $B_O(e_1,e_2)=e_3$；将体积乘二后为 $2e_3$，范数平方四，不能仍写成一。$\square$

**命题 139.3（单位法向、两侧与共同运输）。** 非共线 $u,v$ 给单位法向 $N_O(u,v)=B_O(u,v)/\|B_O(u,v)\|$。面内次序与周围三维定向共同决定它；只有面内绕行，不能决定周围空间的哪一侧。若同时运输 $g,\operatorname{Vol}_O$，使线性同构 $S$ 满足

$$
g'(Sx,Sy)=g(x,y),\qquad
\operatorname{Vol}'(Sx,Sy,Sz)=\operatorname{Vol}_O(x,y,z),
$$

则 $B'(Su,Sv)=SB_O(u,v)$，单位法向亦相同运输。特别地，固定 $g,\operatorname{Vol}_O$ 的正定向等距满足叉积等变。

证明（139.3）。若 $u\ne0$，分解 $v=\lambda u+v_\perp$；范数式右边为 $\|u\|^2\|v_\perp\|^2$，非共线时严格为正，故可归一化。反转空间定向把体积和 $B_O$ 同时反号，却保留全部面内长度及同一有序绕行，给两个外部两侧的模型。运输后的 $SB_O$ 对任意 $Sw$ 的 $g'$ 内积等于原体积，也等于新体积；因 $S$ 满射，唯一性证明运输公式。$\square$

在维数 $n>3$ 的实内积空间中，非共线两向量的正交补维数为 $n-2>1$；单位法向组成该补空间的单位球，单个正负号不能选定其中全部方向。这里不重新证明前卷定理92.2的全旋转法向合同，也不由本章已假定的三维推出原生物理三维。

**定义 139.4（独立的叉积树读出）。** 在标准定向的 $\mathbb R^3$ 中，用本章的单位体积叉积定义

$$
q_{\mathrm{cross}}(\alpha)=e_1,\qquad
q_{\mathrm{cross}}(\beta)=e_2,\qquad
q_{\mathrm{cross}}(\langle s,t\rangle)
=q_{\mathrm{cross}}(s)\times q_{\mathrm{cross}}(t).
$$

这是几何读出的新声明；符号 $q_{\mathrm{cross}}$ 与前卷第87、103章取值于 $\mathbb F_3$ 的负加法读出 $q_3$ 分开。两者既不同域值，也不同节点运算。对 $\gamma=\langle\beta,\alpha\rangle$，此几何读出为 $-e_3$。

**定理 139.5（包含退化子树的全树三周期相容）。** 令

$$
R_3=\begin{pmatrix}0&0&-1\\1&0&0\\0&-1&0\end{pmatrix}.
$$

它保持标准内积及定向，满足 $R_3^3=I$，并对全部原树 $t$ 有

$$
q_{\mathrm{cross}}(\rho t)=R_3q_{\mathrm{cross}}(t).
$$

证明（139.5）。$R_3$ 的列为 $e_2,-e_3,-e_1$，是正交单位基，其行列式为一；它使 $e_1\mapsto e_2\mapsto-e_3\mapsto e_1$，因此三次幂为恒等。命题139.3在固定单位体积下给

$$
(R_3u)\times(R_3v)=R_3(u\times v).
$$

叶 $\alpha$ 的等式为 $e_2=R_3e_1$；叶 $\beta$ 的等式为 $e_2\times e_1=-e_3=R_3e_2$。若两子树已成立，则

$$
\begin{aligned}
q_{\mathrm{cross}}(\rho\langle s,t\rangle)
&=q_{\mathrm{cross}}(\rho s)\times q_{\mathrm{cross}}(\rho t)\\
&=(R_3q_{\mathrm{cross}}(s))\times(R_3q_{\mathrm{cross}}(t))\\
&=R_3q_{\mathrm{cross}}(\langle s,t\rangle).
\end{aligned}
$$

结构归纳覆盖全部树。它不在节点上归一化；例如 $q_{\mathrm{cross}}(\langle\alpha,\alpha\rangle)=0$，零向量仍满足相容公式，所以退化子树并未被排除。$\square$

**来源与边界 139.6（经典定向背景及实际取得）。** 钉版 Mathlib [Analysis/InnerProductSpace/Orientation.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/Orientation.lean)的 `Orientation.volumeForm` 以实内积、给定定向和维数等于索引数为条件；`volumeForm_robust` 用兼容的正交单位基行列式表示体积，`abs_volumeForm_apply_of_orthonormal` 给单位基绝对体积一。`volumeForm_map` 共同运输定向；在同一定向上使用 `volumeForm_comp_linearIsometryEquiv` 还要求等距自同构的行列式为正。这些是经典中间条件，不直接供应本章的原生树几何实现。

组成读出 $c(\langle s,t\rangle)=c(s)+c(t)$ 是另一个接口；它不等于叉积。相同输入时和为两倍输入，叉积却为零，故不能把同一节点的和直接当法向。本章的三维载体、标定体积、来源到 $q_{\mathrm{cross}}$ 的实际读出和对应操作的取得均须各自承担；全树数学相容没有选出物理空间的三维。

## 140. 五模式的联合响应与零差异纤维

**定义 140.1（固定占位配置）。** 用 $x,y,z$ 分别表示 $2,5,3$ 位置的占位指示，配置坐标按 $(x,y,z)$ 排列：

$$
\begin{array}{c|ccc}
140\text{ 的模式}&x&y&z\\\hline
\mathrm{null}&0&0&0\\
2&1&0&0\\
5&0&1&0\\
25&1&1&0\\
3&0&0&1
\end{array}
$$

与前卷定义38.1低到高印刷的 $(x,z,y)$ 位序相比，这里只把后两坐标交换；例如模式 $25$ 的原印刷 $101$ 现在写为 $(1,1,0)$，模式含义不变。前四点是配置上的正方四角，另一个点独立于该面；这是占位配置几何，不是物理位置。

$\mathrm{null}$ 是一个合法配置结果。尚未读取、读取结束以及策略决定停止是协议状态，须使用与五个结果标签分开的记号；只有一次合法读取实际返回 $\mathrm{null}$，才拥有这个配置读数。

**定理 140.2（五点读出的唯一联合展开）。** 对固定五模式域上的任意实函数 $f$，唯一展开为

$$
f=c_0+c_2x+c_5y+c_3z+c_{25}xy,
$$

其中

$$
\begin{aligned}
c_0&=f(\mathrm{null}),&c_2&=f(2)-f(\mathrm{null}),\\
c_5&=f(5)-f(\mathrm{null}),&c_3&=f(3)-f(\mathrm{null}),\\
c_{25}&=f(25)-f(2)-f(5)+f(\mathrm{null}).
\end{aligned}
$$

证明（140.2）。这是前卷定理39.2在明示坐标置换后的同一个函数基。依次评价 $\mathrm{null},2,5,3$，强制前四个系数；评价 $25$，强制 $c_{25}=f(25)-c_0-c_2-c_5$。反向逐点代入恢复五个值，所以存在且唯一。$\square$

$xy$ 在此合法域上恰为联合模式 $25$ 的指示；$c_{25}\ne0$ 时，只有两个单位置响应及常数项不能解释四角响应。但 $c_{25}=0$ 不说明联合来源不存在。四角值若要用于实际计算，须由同一响应合同实际取得并可共同比较；它们不免费同时共存，也不保证比较或准备不改变来源。

**命题 140.3（零差异不等于空来源）。** 令 $d=x-y$。模式 $\mathrm{null},3,25$ 都给 $d=0$，但它们对合法函数 $z$ 或 $xy$ 有不同响应。因此 $d$ 不足以承担任何包含这些区别的未来任务；只对其继续允许的全部任务始终不区分的类别，才可作任务商合并。

证明（140.3）。三个模式的 $(x,y)$ 分别为 $(0,0),(0,0),(1,1)$，差都为零。$z(3)=1$，在另两点为零；$xy(25)=1$，在另两点为零。所以相同当前差读数并不决定这两种后续响应。如果观察者已实际取得相应后续读取权，合并会丢失未来所需区别，必须补存能区别它们的记录。若没有这种读取权，仅能报告当前已取得的差，不宣称已经执行了区分。$\square$

**定义 140.4（任务相对可继续商）。** 固定观察者、来源合同、后续任务与权限。两个来源可合并，要求任一声明的后续动作在二者上的合法性相同，并且每个允许继续链的任务响应相同；有分支时按该任务指定的结果关系或概率律比较。保存商类还须能按实际返回结果继续更新到后继商类。

此条件保证商上的动作合法性、响应和后继不依赖所选代表：换代表时三者均不变，故定义良好。若其中一项不同，同一商符号就会要求两个不同动作或结果，不能承担该任务。任务商只保本观察者未来实际可区别的关系；它不把全部不可访问来源当成已经读取的资料，也不预先宣布所有未来任务永远不变。

## 141. 无免费记录的容量与量子内积相容

**假设 141.1（有限经典无损合同）。** 给有限来源集 $X$ 和实际粗读 $q:X\to B$。指定的无损输出完全由 $(q(x),m_x)$ 构成，其中 $m_x\in M$ 是实际可保留、可访问的记录符号；无损指映射

$$
F:X\longrightarrow B\times M,\qquad F(x)=(q(x),m_x)
$$

单射。若还保留可访问的旧来源或其他耦合载体，必须把它们并入此完整输出，不以不可访问的符号历史代替记录。

**定理 141.2（同纤维的记录容量）。** 若 $X\ne\varnothing$，则可达读出域 $B_{\rm reach}=q(X)$ 非空，且

$$
|M|\ge\max_{b\in B_{\rm reach}}|q^{-1}(b)|.
$$

若 $X=\varnothing$，约定空族最大值为零，则容量下界为零，不强求存在可达读出。就抽象有限集合的编码而言，非空情形的下界可达到；达到不等于观察者已取得该编码的执行和保持。

证明（141.2）。固定可达 $b$。若同纤维的两个不同来源使用同一记录，$F$ 的两个输出相同，违反单射。因此 $x\mapsto m_x$ 在每个纤维上单射，记录数至少为该纤维大小；取有限非空纤维族的最大值。空来源时没有需要区分的输入，空映射为单射，下界零。抽象达到时，令 $m$ 为最大纤维大小，各纤维独立编号到 $\{1,\ldots,m\}$，用编号作记录；同纤维编号不同，不同纤维的粗读不同，所以整体单射。$\square$

同一推理说明：在完整单射过程内，粗读合并的区别必须留在实际记录、旧来源或其他仍可用载体上。若过程本来有损，不能据此声称区别仍在观察者手中。热浴、温度、擦除协议和物理实现尚未给定时，有限符号容量不能换算能耗，也不证明热力学熵。

**假设 141.3（不扰输入的量子记录）。** 在同一个复 Hilbert 系统和记录载体上，指定单位纯态族 $\{\psi_i\}$、固定单位初始记录 $m_0$，以及同一个等距过程 $V$，满足

$$
V(\psi_i\otimes m_0)=\psi_i\otimes m_i,
\qquad \|m_i\|=1.
$$

条件指定的是同一过程对全部这些输入的作用。源相关相位若存在，须吸收进同一联合输出的 $m_i$ 后按本等式比较；不能各对输入另选过程。

**定理 141.4（非正交输入不留下可区别的无扰记录）。** 在假设141.3下，

$$
\langle\psi_i|\psi_j\rangle
=\langle\psi_i|\psi_j\rangle\langle m_i|m_j\rangle.
$$

若 $\langle\psi_i|\psi_j\rangle\ne0$，则 $\langle m_i|m_j\rangle=1$，因而 $m_i=m_j$，记录不能区分这两个输入。沿非正交关联链连通的指定态，都使用同一记录。

证明（141.4）。等距保持输入内积；输入记录相同且单位，输入内积为 $\langle\psi_i|\psi_j\rangle$。输出张量内积为两个内积之积，得等式。非零时消去系统内积；两个单位向量的距离平方为 $2-2\operatorname{Re}\langle m_i|m_j\rangle=0$，故相同。逐边相同沿任意有限关联链传递，给最后结论。$\square$

**命题 141.5（共同内积条件的充分性与正交记录）。** 对有限指定态族及单位记录族，存在定义在输入张成空间上的上述等距映射，当且仅当每对满足定理141.4的内积等式。有限正交单位输入可以在数学上使用相互正交的记录；这不主张所有未知纯态都能复制。

证明（141.5）。必要性已经证明。充分性把每个生成元 $\psi_i\otimes m_0$ 送到 $\psi_i\otimes m_i$，再线性延伸。任意两个线性组合的内积由成对内积确定；输入和输出的 Gram 相同，所以内积保持。尤其输入表示为零的组合，其输出范数平方为零，也是零，因此线性延伸良定义，是张成空间上的等距。它不自动给已取得的全空间设备或环境初始化。

正交单位输入 $\{e_i\}$ 可选正交单位记录 $\{m_i\}$，因为不同输入内积零，等式自动满足。此时输入 $\sum_i a_ie_i$ 的输出是 $\sum_i a_ie_i\otimes m_i$；若有至少两个非零系数，就不是输入与一个独立记录的张量积：投影到各非零的 $e_i$ 分量会要求同一个独立记录同时等于不同的正交 $m_i$，不可能成立。系统约化态也丢去相应非对角元。因此指定正交标签的记录不扩成全部叠加态的不扰复制。$\square$

本章的内积条件是等距定义的直接后果；前卷第109章的共同记录正性、本卷第126章的跨输入等距条件继续限定各自过程。经典纤维计数与量子内积几何不可互换：正交历史标签可以留下不同记录，而非正交的不扰输入受到本章限制。两种情形都要求同一实际过程及可保持的记录载体。

## 142. 固定未来任务内的观察者不确定量

**定义 142.1（共同有限候选、权限与任务宇宙）。** 固定观察者 $O$、一个有限任务范围、有限动作权限菜单和有限候选延拓宇宙 $\mathcal U_O$。每个候选携带此范围内的来源关系、动作合法性和所需未来响应规则；按全部这些任务的响应及合法性相同取类别，$\mathcal U_O$ 表示所得类别集。范围与权限在下面的比较中不变；候选可以描述尚未执行的延拓，但不表示观察者已取得这些反事实的读数。这里的“宇宙”仅指任务内声明的有限候选全集，不是外部宇宙状态全集或可随意调用的仪器库存。

对当前实际记录 $r$，声明其相容类别集 $C_O(r)\subseteq\mathcal U_O$，并要求实际合法记录至少有一个相容延拓。因此 $C_O(r)$ 有限非空。所选有限候选对实际合法记录的覆盖是本模型的前提，不能仅从已经得到一个读数推出该覆盖。相容还包括记录所用来源、标度、动作次序与权限合同；不能只按几个边缘读数相等就假定同一联合实现。若记录矛盾或损坏而无相容候选，本定义不为它赋有限不确定量。

定义任务计数不确定量

$$
H_{\rm count}(r)=\log_2|C_O(r)|.
$$

此处显式使用以二为底的对数，不改变前面各章自然对数的约定。它是剩余任务类别的对数计数，不需等概率先验；仅有一个类别时为零，也不意味着没有来源或没有实际记录。

**定理 142.2（新增实际读数的条件收缩）。** 同一任务及权限宇宙内，实际允许并执行的动作 $a$ 返回 $y$，且旧记录被保留。令 $E_{a,y}(r)\subseteq\mathcal U_O$ 表示与这个动作、结果及来源更新相容的类别；若更新合同为

$$
C_O(r,a,y)=C_O(r)\cap E_{a,y}(r),
$$

且此实际记录合法，则

$$
\varnothing\ne C_O(r,a,y)\subseteq C_O(r),\qquad
H_{\rm count}(r,a,y)\le H_{\rm count}(r).
$$

证明（142.2）。交集是原集合的子集；合法性提供其中至少一个候选。有限正整数基数因此不增，对数 $\log_2$ 严格递增，给不确定量不增。没有用候选等概率，也没有把未执行动作的结果加入交集。$\square$

若动作改变来源，$\mathcal U_O$ 必须从一开始描述该有限范围内的完整候选延拓，使 $E_{a,y}(r)$ 在同一候选宇宙中表达变化。若改为统计更新后新对象的另一个候选域，不能凭两个集合的名字推出本定理的子集关系。

**定理 142.3（忘记细节的并集扩张）。** 在同一 $\mathcal U_O$、同一任务与权限合同内，设可达细记录集合为 $\mathscr R$，忘记映射为 $Q:\mathscr R\to\overline{\mathscr R}$。粗记录 $\bar r=Q(r)$ 的相容集定义为

$$
\overline C_O(\bar r)=
\bigcup_{r'\in\mathscr R:\ Q(r')=\bar r}C_O(r').
$$

则 $C_O(r)\subseteq\overline C_O(Q(r))$，后者仍有限非空，且

$$
\log_2|\overline C_O(Q(r))|\ge H_{\rm count}(r).
$$

证明（142.3）。并集的索引包含实际细记录 $r$，所以包含其全部候选；它仍是固定有限 $\mathcal U_O$ 的子集，并包含非空的 $C_O(r)$。基数不减及对数单调性给结论。$\square$

**边界 142.4（计数、概率与实际关系）。** 两个单调结论只比较同一观察者、同一候选类别、同一有限任务和权限宇宙中的合法记录。改变任务、量具、可执行菜单，或发生记录损坏，不是上述无条件单调结论的实例。忘记还可能失去原有执行权限；只有权限合同保持时才适用定理142.3。

Shannon 熵需另给候选概率律；即使已有概率，随机结果的逐次条件熵也不能仅由候选计数推断。量子熵需合法态及明确的实际可访问关系代数，并说明保留、约化的载体。本章的 $H_{\rm count}$ 既不是热熵，也不是整个宇宙的熵。经典状态压缩须保存未来相关区别这一原则，复用《FIB 自校准关系数学》定理29.1、29.2的充分续行状态及反例；其中实际字母成本、初始空词和左乘接续也保留，不能由终端参数相同推出中间状态可合并。

## 143. 关系接续、有序差异与有限条件整合

**定义 143.1（接续序列先于钟与速率）。** 观察者实际关系按

$$
r_0\xrightarrow{(a_1,y_1)}r_1
\xrightarrow{(a_2,y_2)}r_2\xrightarrow{(a_3,y_3)}\cdots
$$

接续；任一有限段包含动作合法性、执行后的返回结果和实际保留记录。下标只标已经完成的接续次序。只有再取得稳定可比较、可保存的钟读数 $\tau_i$，以及其标度和维护条件，才能定义时长 $\tau_j-\tau_i$；只有在对应时长非零且被测量量已可比较时，才可定义相应差商速率。接续次序本身不供应钟、物理时长或频率，也不保证旧历史始终有免费副本。

**定理 143.2（FIB 面积反号不要求信息损失）。** 在第138章已标定的平面中，对有序向量对以同一系数矩阵 $M$ 定义表达更新 $(u,v)\mapsto(v,u+v)$；这是两槽的线性组合，不额外宣称已取得这样的物理组合门。则

$$
\omega_O(v,u+v)=-\omega_O(u,v).
$$

有序面积大小保持而定向反号；此更新在实向量对上可逆，所以负号不要求丢失该对的信息。

证明（143.2）。交替双线性给 $\omega_O(v,u+v)=\omega_O(v,u)+\omega_O(v,v)=-\omega_O(u,v)$。从更新后 $(v,w)$ 可恢复原 $(w-v,v)$；因此线性更新单射且满射。实线性逆的存在不宣布原生来源允许执行该逆。矩阵层的同一结论是 $\det M=-1$，与第137章 $K$ 的保定向四周期不同。$\square$

若观察者标架也改变，须共同运输内积、面积形式及比较参照。一般可逆 $S$ 下，将面积定义为 $\omega'_O(Su,Sv)=\omega_O(u,v)$ 才比较同一关系；仅在固定旧坐标中取新分量，会混入标架变换的行列式因子。先后的动作次序、几何手性与记录损失因此是不同判据：可逆反号给手性变化而没有此对的信息损失；忘记第140章不同模式的共同零读数可以丢失未来区别，却没有给出任何空间反射；二者都可以发生在同一有序接续链中。

**定理 143.3（观察者关系优先的条件整合）。** 在定义136.1的实际接口中，分别供应下列条件时，各结论可以按相同来源与标定接续使用：固定局部线性量具及已取得的 $M,J$ 实际链；声明的保长二次尺和面内定向；三维内积及相容单位体积；五模式任务响应及可继续记录；同一无损经典过程或同一量子等距记录过程；固定有限候选、权限与任务宇宙。于是有以下完整条件链。

$M,J$ 的表达差给 $K$ 及四周期正方，实际四读数可以恢复其反对称关系值；保长二次尺把四周期接到标准内积，长度和有序面积共同确定三角夹角及手性，有理比例图给条件圆关系；另选三周期相容尺给 $C$ 的平面旋转。三维接口加入单位标定体积后给法向及全树 $q_{\mathrm{cross}}$ 相容。五模式函数保留联合项，并排除把中间态的零差异当成空来源；保存未来区别则受经典纤维容量或量子共同内积条件约束。在同一有限未来任务中，保留旧记录并取得新读数使候选收缩，按同一权限合同忘记细节使候选并集扩张。

证明（143.3）。定理136.3、136.4保持对象—量具共同表示与尺度条件；定理137.2给表达差，假设137.3和定理137.4、137.5把它连接到真正执行的一条链，而非另一支的未读结果。定理138.1只在已选二次尺上给唯一性，定理138.2及既有极化138.3给条件内积与面积；定理138.4、138.5的圆图和三周期尺都留有操作取得边界。定理139.2、139.5在另声明的三维单位体积上给法向及全树相容，使用与原模三读出不同的记号和运算。定理140.2复用既有函数展开，命题140.3及定义140.4指出继续任务需要的区别。定理141.2和141.4、141.5分别限制同一经典无损和量子等距过程，不能把两个互不相容的实现拼成一个。定理142.2、142.3只在固定共同有限宇宙中组合相容集合。每一步的使用都有其已声明或实际取得的前提，故整合不反向供应这些前提。$\square$

**来源 143.4（继承结果的准确范围）。** 前卷[《Auric · FIB-ATOM 续篇：二元来源的三维二阶关系完成》，版本b9b4a62b69908c14f2b3ceb07204620db61aa862](https://raw.githubusercontent.com/the-omega-institute/trureturing/b9b4a62b69908c14f2b3ceb07204620db61aa862/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)第38–39章承担五函数代数，第49–52、56章承担内积与 Gram 几何，第92–93章承担独立法向合同与几何桥，第106–110、115章区分来源、相干控制、共同环境、记录及物理解释。它们各自是条件结果，不是免费仪器。经典极化和单位定向体积分别按来源138.3、139.6的钉版条件使用；这里的矩阵、圆图、叉积树接口及有限候选结论由各自普通证明承担，不把经典中间步骤称为新发现。

**未决边界 143.5（最少结构与物理空间）。** 在没有外加绝对尺、没有免费复制或历史保存时，同时维持距离、手性和后续可用关系所需的最少观察者结构尚未证明。原生树如何取得局部线性或量子载体、交换与相位控制如何实现、量具与记录如何长期维护、共同来源如何在允许操作下拼接、连续度量及定向如何成为实际比较，也未由这些有限条件推导解决。三维只在第139章作为明确接口使用，没有证明物理空间本来三维。

先表达所需关系，随后逐项承担取得、执行、保存和未来使用的证明义务，才能把数学接口接成实际观察。本续篇给普通数学定义、条件与证明，不把符号相容冒充物理执行，也不宣称本文已经由 Lean 核验。

## 追加锚（第136–143章以下为增补区）

## 144. 完整实际事件与可追回的单前沿

**定义 144.1（实际事件和策略的输入）。** 固定观察者、有限协议视界及实际取得接口，沿用定义136.1。一次实际事件写为 $e=(a,y,\kappa)$：$a$ 是本次实际执行的动作，$y$ 是本次实际取得的返回，$\kappa$ 保存本次任务需要再次使用的量具、控制、来源和标定标记。请求了但未完成的动作不能填成已完成动作；未取得的结果不能填入 $y$。若接口只取得一组同时读数而没有取得其内部先后，就把这组读数作为一个带类型的复合事件，不补造内部顺序。

初始已取得的参照和协议固定在共同上下文中，新增事件历史从空词 $h_0=\varepsilon$ 开始。策略在第 $n$ 步的动作选择及停止选择只依赖当时已获记录和已获控制信息。执行并取得 $e_{n+1}$ 后，历史为

$$
h_n=e_1\cdots e_n,\qquad h_{n+1}=h_ne_{n+1}.
$$

合法后继是协议在该前缀下允许的完整事件，不是仅有动作名的后继。一个动作可以有多个允许结果；策略没有预先取得其中哪一个会发生。

**假设 144.2（有限树上的完整事件编码）。** 原始树域为

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

这是定义137.1的自由有序树；$\beta=\rho\alpha$ 表示替换结果，不把两个叶标签认作同一个叶。对本协议的完整事件域 $\mathcal E$，供应单射 $E:\mathcal E\to\mathcal T$ 和其像上的解码函数 $D_E$，满足 $D_E(Ee)=e$。在有限事件域上，可以用带标签的有限字段编码后配对，得到这样的编码；标签、字段边界及解码规则属于协议。若结果本来取任意不可数域，有限树域是可数的，因而不存在对全部这样的结果的单射编码。此时须声明有限精度、受限结果域或另一个载体，不能无损地把任意实读数塞进有限树。

数学上的可解码还须与实际保存、读取和解码权限区分。称观察者“可追回”历史时，要求事件码留在实际可再次访问的载体上，且相应读取与解码可执行；只声明一个不可读的编码函数不满足这个取得接口。

**定义 144.3（五模式码与完整字段）。** 令 $\gamma=\langle\beta,\alpha\rangle$。五模式的一个符号码为

$$
\begin{aligned}
E_{[2]}&=\alpha,& E_{[3]}&=\beta,& E_{[5]}&=\gamma,\\
E_{[25]}&=\langle\gamma,\alpha\rangle,&
E_{\mathrm{null}}&=\langle\alpha,\alpha\rangle.
\end{aligned}
$$

这五棵树互异：前两棵是不同叶；后三棵的根分别具有左右子树 $(\beta,\alpha)$、$(\gamma,\alpha)$、$(\alpha,\alpha)$，自由树的根分解唯一，且 $\beta,\gamma,\alpha$ 互异。这里只编码模式字段。若事件还含动作、读数、量具或来源标记，可例如用固定括号格式

$$
E(a,y,\kappa)=\langle C_a(a),\langle C_y(y),C_\kappa(\kappa)\rangle\rangle,
$$

其中各字段码在其声明域上单射并可解码；$C_y$ 内部再保留模式及读数的其余字段。逐根解码即得完整三元组，故此格式单射。把整个 $E(a,y,\kappa)$ 换成单独的 $E_{[w]}$，一般就丢失其他字段。

模式 $\mathrm{null}$ 表示已经读到的零占位窗口。它的事件码仍是非空树，组成为 $(2,0)^T$，叶数为二；占位读出为零不使这个事件码成为零树。未读没有该次返回，$\mathrm{End}$ 是表示合同中的结束标记，$\mathrm{Stop}$ 是策略停止选择。若后两者实际作为事件记录，须有各自完整码；若没有发生这样的事件，不凭空追加码。四者的区分继承[《FIB 关系延拓几何》，版本2bf48d5375954170bae475578dc4d93ce77f8384，定义2.4](https://raw.githubusercontent.com/the-omega-institute/trureturing/2bf48d5375954170bae475578dc4d93ce77f8384/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)。

**定义 144.4（左前缀档案）。** 对有限完整事件词定义

$$
\mathcal H(\varepsilon)=\alpha,\qquad
\mathcal H(he)=\langle\mathcal H(h),Ee\rangle,
\qquad H_n=\mathcal H(h_n).
$$

只在此档案像上定义追加深度

$$
\tau(\alpha)=0,\qquad
\tau(\langle H,Ee\rangle)=\tau(H)+1.
$$

一般树的通常高度另记为 $\operatorname{ht}$，叶高度为零，节点高度为 $1+\max(\operatorname{ht}s,\operatorname{ht}t)$。$\tau$ 是档案的左前缀深度，不是对任意树的高度定义。

**定理 144.5（完整档案的单射与唯一已发生链）。** 在假设144.2下，$\mathcal H$ 对所有有限完整事件词单射。任意非初始合法档案有唯一前缀档案和唯一末事件，递归取前缀恰回到 $\alpha$，且

$$
\tau(H_n)=n,\qquad
H_0\prec H_1\prec\cdots\prec H_n,
$$

其中 $\prec$ 指非空追加所得的档案前缀关系。已发生的 $h_n$ 给唯一这条链，不要求协议的全部合法后继唯一。

证明（144.5）。自由树中的叶与节点不相等，且节点相等当且仅当左右子树分别相等。因此空词码不能等于非空词码；两个非空词的码相等时，根分解给前缀码相等、末事件码相等。$E$ 的单射性给末事件相等，递归对前缀使用同一论证，最终得到长度及每个事件相等。此递归同时给唯一解码：遇到 $\alpha$ 停止，遇到档案节点就解码右事件并继续读取左前缀。

由构造每次增加一次左前缀层，归纳得 $\tau(H_n)=n$。非空追加必使此整数严格增加，故链中各项互异，也不存在非空追加回到原档案的回路。若同一 $h$ 后有两个不同合法事件 $e,e'$，则 $\mathcal H(he)\ne\mathcal H(he')$；这表示两个允许后继，不把它们都认作已经发生的历史。$\square$

**定理 144.6（叶数增长与删除的准确类型）。** 令 $\nu(\alpha)=\nu(\beta)=1$，$\nu(\langle s,t\rangle)=\nu(s)+\nu(t)$。则

$$
\nu(H_n)=1+\sum_{j=1}^{n}\nu(Ee_j),\qquad
\nu(H_{n+1})>\nu(H_n).
$$

通常树高度却可能在一步追加中增加多层。取左子树给一个数学上可定义的前缀删除映射；本结论没有证明这样的物理删除或对象逆变换不可能。

证明（144.6）。配对的叶数加法给所列和式；每棵有限树至少有一片叶，故每次差为 $\nu(Ee_{n+1})\ge1$。例如以五模式码 $E_{[25]}$ 追加到 $H_0=\alpha$，事件码通常高度为二，所得档案通常高度为三，但追加深度仅为一。这排除了把两种高度混同。左投影 $\langle H,Ee\rangle\mapsto H$ 在档案像上良定义；它会去掉末事件区别，与保留全部历史的追加合同是不同操作。数学投影的存在和物理实现权限仍须分别判断。$\square$

## 145. 保留式自变化与偶步 Fibonacci 组成

**定义 145.1（符号来源的保留式替换）。** 对已给定的有限来源树定义

$$
\widehat\rho(t)=\langle t,\rho t\rangle,
\qquad S_0=\alpha,\qquad S_{n+1}=\widehat\rho(S_n).
$$

左支保留原树，右支保留原替换结果。这是由既有 $\rho$ 和有序配对构成的符号操作。它没有定义在任意未知量子态上的复制通道；若要在一个物理来源上同时保存输入和产生输出，须另外供应符合第141章内积条件的过程。

**定理 145.2（同组成的偶步推进与逐树交换）。** 在定义137.1的组成 $c$ 下，对每个 $t\in\mathcal T$ 有

$$
c(\widehat\rho t)=(I+M)c(t)=M^2c(t),\qquad
\rho(\widehat\rho t)=\widehat\rho(\rho t),
\qquad M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

因此 $c(S_n)=M^{2n}(1,0)^T$。但 $\widehat\rho$ 与 $\rho^2$ 并非相同的树操作。

证明（145.2）。组成加法和既有 $c\rho=Mc$ 给 $c(\langle t,\rho t\rangle)=c(t)+Mc(t)$；既有 $M^2=M+I$ 给第一式。替换保持配对，故

$$
\rho\langle t,\rho t\rangle
=\langle\rho t,\rho^2t\rangle
=\widehat\rho(\rho t).
$$

这是真正的逐树等式，而不只是组成相等。对 $S_n$ 归纳即得偶次幂。另一方面

$$
\widehat\rho\alpha=\langle\alpha,\beta\rangle,
\qquad \rho^2\alpha=\langle\beta,\alpha\rangle;
$$

它们组成均为 $(1,1)^T$，但左右顺序不同，自由树中不相等。$\square$

**定理 145.3（保留展开的精确叶数）。** 采用 $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$。零层为 $c(S_0)=(1,0)^T$、$\nu(S_0)=1$；对 $n\ge1$，

$$
c(S_n)=\begin{pmatrix}F_{2n-1}\\F_{2n}\end{pmatrix},
\qquad \nu(S_n)=F_{2n+1}.
$$

后一叶数式亦适用于 $n=0$，其前七项为 $1,2,5,13,34,89,233$。

证明（145.3）。每片 $\alpha$、$\beta$ 各贡献一个组成坐标，故 $\nu(t)=(1,1)c(t)$。已有来源 Fibonacci 递推及组成桥见上述钉版《FIB 关系延拓几何》定义1.3、定理1.4。对其矩阵递推取偶数阶，$M^{2n}(1,0)^T=(F_{2n-1},F_{2n})^T$，$n\ge1$：$n=1$ 时为 $(1,1)^T$，乘 $M$ 将相邻项 $(F_{k-1},F_k)^T$ 送到 $(F_k,F_{k+1})^T$，再乘一次即前进两项。两坐标相加给 $F_{2n+1}$。零层直接计算，不引入负索引 Fibonacci 数。$\square$

**命题 145.4（来源保留不等于取得未知事实）。** 在前卷定义106.1的固定相位表示下，$\widehat\rho\alpha$ 与 $\rho^2\alpha$ 的酉表达相反，虽然组成相同；可观测的相干比较仍以定义107.1的实际比较合同为条件。若初始树和替换规则完全已知，则全部 $S_n$ 已由它们确定，单纯展开不取得另一项未知来源事实。

证明（145.4）。前卷定理106.2已给 $U_{\langle\beta,\alpha\rangle}=-U_{\langle\alpha,\beta\rangle}$，直接代入定理145.2中的两树即可。前卷定理107.2只在实际共同控制和相位参照已供应时把此符号差接到读数，所以不能由来源表达免费取得比较门。对完全已知的输入和规则，$S_{n+1}$ 是 $S_n$ 的确定函数；在任一只含这同一已知输入的候选模型中，展开结果取相同值，不切细候选纤维。计算、显式存储和再次读取仍各需要其载体及操作资源，确定性并不使它们免费。$\square$

## 146. 同一候选域上的档案塔与五模式创新

**定义 146.1（共同有限实现与参考内积）。** 固定同一个非空有限候选集合 $\Omega$、有限协议阶段 $0,\ldots,N$ 及严格正权 $\mu(\omega)>0$。候选含这一视界需要的初态、来源、控制和返回机制；若协议涉及随机性，也将其所需的种子或噪声来源纳入这个共同实现。种子属于模型不表示观察者已读到种子。$\mu$ 是声明的参考权，不是唯一宇宙先验；除以总权可归一成概率，以下投影不变。

在每个候选上，协议定义实际会纳入档案的记录

$$
R_n:\Omega\longrightarrow B_n=R_n(\Omega),\qquad
R_n=d_n\circ R_{n+1}.
$$

$R_n$ 同时描述全部候选的档案映射，不表示全部候选历史都已发生。观察者只有实际候选 $\omega_*$ 的记录 $R_n(\omega_*)$。阶段 $n$ 若不是统一的事件次数，须保留该候选实际事件次数字段；已经停止的候选不因阶段推进而被填入 $\mathrm{null}$。在每个候选恰执行 $n$ 次追加的合同中，$R_n$ 可取定义144.4的完整档案，$d_n$ 就是左前缀读取。

取同一实 Hilbert 空间及可见子空间

$$
\mathcal L=\mathbb R^\Omega,\qquad
\langle f,g\rangle_\mu=\sum_{\omega\in\Omega}\mu(\omega)f(\omega)g(\omega),
\qquad V_n=\{b\circ R_n:b:B_n\to\mathbb R\}.
$$

对纤维 $C_n(\omega)=R_n^{-1}(R_n(\omega))$，使用有限条件期望

$$
(P_nf)(\omega)=
\frac{\sum_{\eta\in C_n(\omega)}\mu(\eta)f(\eta)}
{\sum_{\eta\in C_n(\omega)}\mu(\eta)}.
$$

严格正权保证分母正并保留所有候选区别。$P_n$ 是到 $V_n$ 的正交投影。这里直接使用[《递归关系的观察商、严格拼接与相容完备化》，版本86577a9c5c0e1a38bf7e6d6a69bf473725402289，§121.1–121.6](https://raw.githubusercontent.com/the-omega-institute/trureturing/86577a9c5c0e1a38bf7e6d6a69bf473725402289/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)的档案塔，而不另立一般投影定理。其经典接口为钉版 Mathlib [CondexpL2.lean，`MeasureTheory.condExpL2` 与 `inner_condExpL2_eq_inner_fun`](https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean)：条件为子 $\sigma$ 代数包含关系、$L^2$ 输入及完备实或复内积目标；本节有限正权实模型满足这些条件。此处按普通数学使用该经典中间结果。

**定理 146.2（实际档案接口中的目标创新）。** 在定义146.1中，$V_n\subseteq V_{n+1}$。固定同一个目标函数 $f:\Omega\to\mathbb R$，令 $\Delta_n=P_{n+1}-P_n$，则

$$
\Delta_n^*=\Delta_n,\qquad \Delta_n^2=\Delta_n,\qquad
\Delta_i\Delta_j=0\quad(i\ne j),
$$

$$
P_{n+1}f=P_nf+\Delta_nf,\qquad
\|P_{n+1}f\|_\mu^2=\|P_nf\|_\mu^2+\|\Delta_nf\|_\mu^2.
$$

固定目标的累计可见能量增益满足

$$
\mathcal I_n(f):=\|P_nf\|_\mu^2-\|P_0f\|_\mu^2
=\sum_{k=0}^{n-1}\|\Delta_kf\|_\mu^2,
\qquad \mathcal I_0(f)=0,
$$

$$
\|f\|_\mu^2=\|P_nf\|_\mu^2+\|f-P_nf\|_\mu^2.
$$

因此 $\mathcal I_{n+1}(f)>\mathcal I_n(f)$ 当且仅当 $\Delta_nf\ne0$。新事件被保留不要求这个固定目标严格增益。

证明（146.2）。完整事件档案经 $d_n$ 回到旧档案，故 $b\circ R_n=(b\circ d_n)\circ R_{n+1}$，得到所需的子空间包含接口。随后直接应用上述档案塔§121.4–121.6：对应 $q_n=R_n$、$\pi_n=d_n$、$\Pi_n=P_n$、权为归一的 $\mu$；若不归一，全部范数平方只乘同一正总权，等式和零点不变。该既有结果给嵌套投影、互相正交的差投影及含最终余项的完整分解，即全部所列等式。严格正权下范数平方为零恰是函数逐点为零，所以一步严格性恰由本目标的非零创新判定。$\square$

**定理 146.3（五模式依次读取的四层分区）。** 在已声明的五模式候选域

$$
\Omega_5=\{\mathrm{null},[2],[5],[25],[3]\}
$$

上，按 $(x,y,z)$ 分别指示最低 $2$ 位、最高 $5$ 位、中间 $3$ 位：五点依次为 $(0,0,0),(1,0,0),(0,1,0),(1,1,0),(0,0,1)$。固定任意严格正权。依次记录常量、$x$、$(x,y)$、$(x,y,z)$，所得空间维数为

$$
1\longrightarrow2\longrightarrow4\longrightarrow5,
\qquad \dim\operatorname{im}\Delta_0=1,\quad
\dim\operatorname{im}\Delta_1=2,\quad
\dim\operatorname{im}\Delta_2=1.
$$

每一步固定目标的创新向量 $\Delta_nf$ 唯一；中间一步的新可见空间却是二维，并非所有创新都平行。

证明（146.3）。常量记录只有一个纤维。读取 $x$ 后有纤维 $\{\mathrm{null},[5],[3]\}$ 和 $\{[2],[25]\}$。再读 $y$，前者分成 $\{\mathrm{null},[3]\}$ 与 $\{[5]\}$，后者分成 $\{[2]\}$ 与 $\{[25]\}$，共四个纤维。最后 $z$ 切开 $\{\mathrm{null},[3]\}$，得到五个单点。正权下各纤维指标构成纤维常值函数空间的一组基，故维数恰为纤维数；嵌套正交差空间的维数是相邻维数之差。

为展示第二步的两个方向，写模式权为 $m_w=\mu(w)>0$。函数

$$
 u=\frac{\mathbf1_{\{[5]\}}}{m_{[5]}}
 -\frac{\mathbf1_{\{\mathrm{null},[3]\}}}{m_{\mathrm{null}}+m_{[3]}},
\qquad
 v=\frac{\mathbf1_{\{[25]\}}}{m_{[25]}}
 -\frac{\mathbf1_{\{[2]\}}}{m_{[2]}}
$$

均只依赖 $(x,y)$，并在各旧 $x$ 纤维上的加权和为零，故属于 $V_2\cap V_1^\perp$。它们非零且支撑不交，所以互相正交，张成这个二维空间。一个二值读数能同时切开多个旧纤维，故其新空间不必只有一维。正交投影规定每个 $f$ 的唯一分量，却不把不同 $f$ 的分量变成同一方向。$\square$

**命题 146.4（事件、目标信息与空间方向的不同计数）。** 在上述五模式模型中，读取更多字段可以增加分区维数而对某个目标零增益；固定有限 $\Omega$ 不能支持无限多个非零正交创新空间。式 $2+1=3$ 只在旧可见空间恰为二维、另实际取得一个独立的一维创新且保持同一内积时给三维可见空间；它不导出物理空间三维。

证明（146.4）。例如目标 $f=x$ 已属于 $V_1$，所以 $P_2f=P_1f=f$，尽管第二步空间维数从二增到四。更一般地，$\mathcal I_n(f)\le\|f\|_\mu^2-\|P_0f\|_\mu^2$，事件数不能当作目标能量增益。所有新空间互相正交，且总空间维数为 $|\Omega|$；严格增加空间的步数最多为 $|\Omega|-\dim V_0$，不保证这些步在预先指定的早期阶段发生。若无限协议每步供应新的独立随机比特，就不再属于这个固定有限共同域。

对 $\dim V_n=2$ 且 $\dim(V_{n+1}\cap V_n^\perp)=1$ 的另一个实际记录合同，正交直和才给 $\dim V_{n+1}=3$。这些向量是候选上的函数，不是位置轴；把它们解释为几何方向还需实际度量、运输和定向标定。即使在函数空间中选了定向，这也不自动给第139章的物理法向接口。$\square$

## 147. 低到高守卫上的额外黄金区间尺度

**定义 147.1（守卫接缝和窗口索引）。** 使用钉版《FIB 关系延拓几何》定义2.2、定理2.3的原低到高守卫。输入接缝 $i\in\{0,1\}$ 表示当前窗口下方紧邻位是否占用；输出接缝 $j$ 是本窗口最高位的占用。每个具体模式分支为

$$
\begin{array}{c|c|l}
i&j&\text{合法模式}\\\hline
0&0&\mathrm{null},[2],[3]\\
0&1&[25],[5]\\
1&0&\mathrm{null},[3]\\
1&1&[5]
\end{array}
\qquad A=\begin{pmatrix}3&2\\2&1\end{pmatrix}.
$$

矩阵 $A$ 的行是输入接缝、列是输出接缝，元素是具体分支数。它不是第122章正方加支路配置链的概率矩阵 $P$，也不是从高到低读取既有窗口的读者；那些系统的状态和合法菜单不同。长度 $n$ 词包含恰好 $n$ 个已读窗口，$n=0$ 是空词。只有每个实际事件恰登记一个窗口时，这里的窗口数才等于第144章的事件追加深度；复合读取、重复读取和非窗口动作都须另计。

**假设 147.2（同类型的精确区间分割）。** 另供两种原型半开区间 $I_i=[0,r_i)$，$r_0,r_1>0$，以及共同比例 $1/\lambda$。每个 $i\to j$ 的具体合法模式分支对应一个保持端点次序的 $I_j$ 仿射副本，长度为 $r_j/\lambda$；这些副本互不重叠并精确分割 $I_i$。可以固定定义147.1的模式次序依次排列，输入一时只保留其三条合法分支。所有内部接缝由右侧区间收左端点、左侧区间不收右端点；根域也采用半开区间。若改用闭根域，必须另声明全局最右端点的归属规则。以下采用半开合同。

每次接续在已选子区间内重用其输出接缝类型的同一分割。该合同是额外的几何模型，不从树语法或守卫计数自动得到。其存在问题与正长度兼容条件由下一条给出。

**定理 147.3（精确分割强制的黄金比例）。** 在假设147.2下，

$$
\lambda r_0=3r_0+2r_1,\qquad
\lambda r_1=2r_0+r_1,\qquad
\lambda=2+\sqrt5=\phi^3,\qquad
\frac{r_0}{r_1}=\phi,\quad \phi=\frac{1+\sqrt5}{2}.
$$

反向，取 $r_0=\phi,r_1=1,\lambda=\phi^3$，按固定次序排列这些副本，确实产生精确半开分割。共同改变长度单位不改变分支比例。

证明（147.3）。把父区间内各分支长度相加并乘 $\lambda$，得到两式。令 $q=r_0/r_1>0$，第二式给 $\lambda=2q+1$，第一式给 $(2q+1)q=3q+2$，即 $q^2-q-1=0$。唯一正根为 $\phi$；于是 $\lambda=2\phi+1=2+\sqrt5=\phi^3>1$，其中 $\phi^2=\phi+1$。负根不能作为正长度之比。

反向各分支长度为正，按已定次序以累计端点构成半开区间；两行长度和分别等于父长，故无间隙、无重叠并覆盖父区间。相同构造可在每个子区间中仿射重用。若同时乘 $r_0,r_1$ 以正数 $s$，所有父子长度同乘 $s$，比例不变。$r_0=\phi,r_1=1$ 只是共同单位的选择。$\square$

**定理 147.4（逐模式比例、历史长度与边界修正）。** 在上述区间合同中，具体分支 $w:i\to j$ 的长度比例为

$$
p_i(w)=\frac{r_j}{\phi^3r_i}.
$$

因此 $0\to0$ 的三分支各为 $\phi^{-3}$，$0\to1$ 的两分支各为 $\phi^{-4}$，$1\to0$ 的两分支各为 $\phi^{-2}$，$1\to1$ 的唯一分支为 $\phi^{-3}$。每行具体分支比例和为一，各比例严格在零与一之间。

从接缝 $i_0$ 开始，将初区间归一为长度一。任一合法模式历史 $h=w_1\cdots w_n$，接缝序列为 $i_0,\ldots,i_n$，其唯一历史区间 $J_h$ 满足

$$
|J_h|=\prod_{k=1}^n p_{i_{k-1}}(w_k)
=\phi^{-3n}\frac{r_{i_n}}{r_{i_0}}.
$$

定义本章的二进制区间分辨量及修正时标

$$
\mathcal I(h)=-\log_2|J_h|
=3n\log_2\phi+\log_2r_{i_0}-\log_2r_{i_n},
$$

$$
\Theta(h)=\frac{\mathcal I(h)-\log_2r_{i_0}+\log_2r_{i_n}}
{3\log_2\phi}=n.
$$

每步 $\mathcal I$ 的增量仅为 $2\log_2\phi,3\log_2\phi,4\log_2\phi$，均严格正。

证明（147.4）。代入 $r_0/r_1=\phi$ 得四类比例。父区间的精确分割给行和一，$\phi>1$ 给各比例小于一。逐层按相同半开规则分割，归纳得到每个合法词的唯一子区间，固定深度的所有词区间互不相交并覆盖初区间；每个点只落入一个该深度区间。长度逐次乘分支比例，所有相邻 $r_{i_k}$ 相消，得到首尾式。空词的空乘积是一，$i_n=i_0$，故 $n=0$ 时 $\mathcal I=\Theta=0$。取以二为底的对数得到主体增长项和接缝修正项；再次消去首尾项得 $\Theta=n$。最后每步取四类比例的负对数即得三个严格正值。$\square$

**命题 147.5（尺度、历史和目标知识的非等价）。** $\mathcal I$ 与 $\Theta$ 是额外区间模型的内部窗口尺度，不是物理钟、目标知识量或完整档案。它们与定义146.1的 $\mu$ 没有免费等价关系；同一个 $n$、末接缝及 $\mathcal I$ 不能恢复历史。

证明（147.5）。初接缝零时，一步词 $\mathrm{null},[2],[3]$ 都终止在接缝零，长度同为 $\phi^{-3}$，分辨量同为 $3\log_2\phi$，但三词和完整事件档案不同。在已知确定下一模式的候选模型中，追加一个窗口仍使 $\mathcal I$ 严格增加，却不切细候选纤维，所以每个目标创新都可以为零。

若额外把根点声明为均匀随机来源并按区间解码，长度比例才成为该模型的条件概率；也可以在固定有限深度按 $|J_h|$ 声明参考权。原假设没有提供这样的随机来源，也没有约束任意给定的 $\mu$ 必须取这些权。故不能把长度比例称为原生自然概率，或把 $\mathcal I(h)$ 当作任意模型的惊讶量。$\Theta$ 计数窗口接续而不规定持续时间；若事件不与窗口一一对应，它也不等于事件深度。共同单位只改变首尾长度对数的同一加数，不能消去这些不同类型的取得条件。$\square$

## 148. 周期读出、执行次序与不断追加的档案

**定义 148.1（表达词与实际先后）。** 沿用第137章的 $M,J,K$。矩阵表达词 $MJ$ 表示矩阵乘积 $M\cdot J$，在列向量上右因子先作用。另用实际事件词 $e_Me_J$ 表示先执行并取得 $M$ 事件，再执行并取得 $J$ 事件；它的累计矩阵为 $JM$。动作名仅标记事件中的动作字段，完整 $e_M,e_J$ 仍须保存本次返回及量具、来源、控制标记。若协议采用其他词求值约定，须给出到这一列向量约定的明确映射。

**定理 148.2（次序差与档案次序不能互相替代）。** 在实际 $M,J$ 两动作已取得并且所比较的链具有同一初始来源和固定标定的条件下，先 $M$ 再 $J$ 的对象表达为 $JMx$，先 $J$ 再 $M$ 的对象表达为 $MJx$。已有

$$
K=MJ-JM,\qquad K^2=-I,\qquad K^4=I
$$

是实线性表达结果，不自行供应执行差算子的门。两个不同顺序的完整事件词，其档案必不同，即使某个粗响应偶然相同。

证明（148.2）。累计矩阵按假设137.3在每次实际动作后左乘，所以从 $A_0=I$ 开始，$M$ 后接 $J$ 给 $A_1=M,A_2=JM$；反序给 $J,MJ$。矩阵差及四周期直接复用定理137.2，不把表达减法改成实际动作。非零 $x$ 时 $Kx\ne0$，所以在这个精确向量模型中两终态表达不同；但一个粗量具可能对它们给相同响应。完整词 $e_Me_J$ 和 $e'_Je'_M$ 在首动作字段已经不同，定义144.2的完整事件单射与定理144.5保证档案不同，无须量具恰好区分两终态。

若未来仍允许读取或使用这个次序，粗响应相同不能成为合并两历史的依据。只有按定义140.4证明所有允许未来任务的合法性和响应都在该粗纤维上不变，才能使用相应任务商。对象表达是否相同、当前量具是否区分、完整记录是否相同和未来任务是否相容，是四个不同判断。$\square$

**定理 148.3（三周期商与三次实际追加）。** 在组成的模二商上令

$$
\overline M=\begin{pmatrix}0&1\\1&1\end{pmatrix}\quad\text{于 }\mathbb F_2^2.
$$

已有三种非零类型 $(1,0)^T,(0,1)^T,(1,1)^T$ 按 $\alpha\to\beta\to\gamma\to\alpha$ 循环，$\overline M^3=I$。但任意三次实际事件追加都满足

$$
\tau(H_{n+3})=\tau(H_n)+3,\qquad H_{n+3}\ne H_n.
$$

可用离散曲线

$$
\Gamma_n=\left(\cos\frac{2\pi n}{3},\sin\frac{2\pi n}{3},n\right),
\qquad n\in\mathbb N
$$

图示周期读出与追加计数的并存；它不证明物理空间有三个维度。

证明（148.3）。前卷命题22.3、定义23.1及定理32.1已经给此三周期；直接沿矩阵作用也得到 $(1,0)\mapsto(0,1)\mapsto(1,1)\mapsto(1,0)$，零类型另固定，不能把全部树都只当这三个非零类型。这个商忘记许多来源及档案区别。定理144.5对三个完整实际事件连用，深度严格增加三，故档案不相等。所定义 $\Gamma_n$ 的前两坐标每三步重复，第三坐标严格增加；这是把两个数学读出画在一张图上的选择。若将第二坐标取负，绕行手性反向，第三坐标仍为 $n$，同样上升。图示轴、函数空间正交方向和实际位置坐标没有因此被证明等同。$\square$

**命题 148.4（实际逆返回对象而不撤销事件）。** 假设在某个实际对象域上，动作 $A$ 及其实际逆 $A^{-1}$ 都已取得，连续执行时保持其逆关系和读出合同。则对象可经历 $x\mapsto Ax\mapsto x$，档案却经历

$$
\mathcal H(h)\longmapsto\mathcal H(he_A)
\longmapsto\mathcal H(he_Ae_{A^{-1}}),
$$

其追加深度增加二。仅有数学逆式不能替代实际取得；不可恢复的记录擦除不属于保留式合同。

证明（148.4）。对象返回来自所假设的 $A^{-1}A=I$，并须作用于同一个实际对象，不能拼接两次不同准备。每次实际执行和返回仍各形成一个完整事件；定理144.5给两个严格追加层。即使两个对象端点相同，末档案仍能区分“没有执行”与“执行后返回”。若记录过程把中间事件不可恢复地擦除，所得末记录不再具有可追回的完整前缀，故不能使用本命题的档案结论。$\square$

## 149. 全部合法窗口历史的统一恢复容量

**假设 149.1（容量问题的恢复域）。** 固定初接缝零及窗口长度 $n\ge0$。恢复域是定义147.1的全部低到高合法模式词 $G_0^{(n)}$，包括最高窗口为 $\mathrm{null}$ 的词；零层含唯一空词。不把这些词商成自然数规范表示，也不要求每个允许词都已经发生。供应同一存储方案

$$
s_n:G_0^{(n)}\longrightarrow\mathcal S_n,\qquad
D_n:\mathcal S_n\longrightarrow G_0^{(n)},\qquad
D_n(s_n(h))=h\quad\text{对所有 }h\in G_0^{(n)}.
$$

$\mathcal S_n$ 是实际可区别且可读的保存状态域。若还要恢复完整事件的其他字段，须把恢复域改成完整合法事件历史；当其中包含每个模式词的一个完整实现时，其状态需求至少不小于本节下界。若协议只允许更小的实际像，则应按这个较小恢复域重算，不能把“全部守卫合法词”暗换成一个预知轨迹。

**定理 149.2（固定长度全档案的精确状态下界）。** 在假设149.1下，

$$
N_n=|G_0^{(n)}|=F_{3n+2},\qquad
|\mathcal S_n|\ge N_n.
$$

若同一固定长度二进制载体用 $B_n^{\rm bits}$ 位表示全部保存状态，则

$$
B_n^{\rm bits}\ge\left\lceil\log_2F_{3n+2}\right\rceil.
$$

$n=0$ 时 $N_0=1$，下界为零位。

证明（149.2）。精确计数直接复用钉版《FIB 关系延拓几何》定理2.3，不重建已有 Fibonacci 计数定理。其接口是

$$
\begin{pmatrix}a_{n+1}\\b_{n+1}\end{pmatrix}
=A\begin{pmatrix}a_n\\b_n\end{pmatrix},\qquad
 a_0=b_0=1,\qquad a_n=F_{3n+2},\quad b_n=F_{3n+1};
$$

引用式中 $a_n,b_n$ 分别是两个接缝的词数，载体位数则记为 $B_n^{\rm bits}$。计数初值含空词，递推允许末窗口为零，恰与恢复域一致。若 $s_n(h)=s_n(h')$，使用同一 $D_n$ 得 $h=h'$，所以 $s_n$ 单射，实际像至少有 $N_n$ 个状态。这也是定理141.2在只有一个粗读出纤维时的全历史容量实例。固定 $B_n^{\rm bits}$ 位至多给 $2^{B_n^{\rm bits}}$ 个区别，故 $2^{B_n^{\rm bits}}\ge N_n$，取对数和整数上整即得。零层只有空词，确可由一个状态表示。$\square$

**定理 149.3（增长率与窗口尺度的条件对应）。** 对上述统一全历史恢复方案，有

$$
B_n^{\rm bits}\ge3n\log_2\phi-O(1),\qquad
3\log_2\phi\approx2.083.
$$

这个系数是每个窗口的全域容量增长率；只有一事件一窗口时才能称每事件的该增长率。它与第147章的区间主体项同含 $\phi^3$，但容量结论不要求区间模型，也不自动成为 Shannon 熵或热力学界。

证明（149.3）。经典 Binet 公式作为中间工具，取钉版 Mathlib [NumberTheory/Real/GoldenRatio.lean，`Real.coe_fib_eq`](https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/Real/GoldenRatio.lean)：对 $m\in\mathbb N$，$F_0=0,F_1=1$，令 $\psi=(1-\sqrt5)/2=-\phi^{-1}$，有

$$
F_m=\frac{\phi^m-\psi^m}{\sqrt5}
=\frac{\phi^m}{\sqrt5}\left(1-(-\phi^{-2})^m\right).
$$

本节 $m=3n+2\ge2$，故括号至少为固定正数 $1-\phi^{-4}$，至多为 $1+\phi^{-4}$。因此

$$
\log_2F_{3n+2}\ge
3n\log_2\phi+2\log_2\phi-\tfrac12\log_2 5
+\log_2(1-\phi^{-4}).
$$

这给不依赖 $n$ 的常数修正；同样的上界说明其增长率恰为 $3\log_2\phi$。接入定理149.2即可。区间主体项则由 $A$ 的正长度兼容合同推得，两者是同一个守卫矩阵的两种用途；参考概率律、期望长度、物理时间和热浴条件都没有在此证明中供应。$\square$

**命题 149.4（受限任务、已知轨迹与可访问性）。** 上述容量约束的是一个统一方案精确恢复全部合法词的可区别状态数，不约束每个单独词的描述长度。只保存任务摘要或完全已知的确定轨迹时，必须按实际可区别像计算；可读载体条件不可删除，也没有许可复制未知量子态。

证明（149.4）。若恢复对象为任务函数 $q:G_0^{(n)}\to Q$，精确恢复 $q(h)$ 只要求区分 $q(G_0^{(n)})$；常量任务的像只有一项。若初始来源、规则和唯一轨迹事先完全已知，指定长度的恢复域也只有一个词；可以按已知规则重算，但重算、索引、载体和实际读取仍有各自成本。这两个问题都不同于假设149.1的全域逆映射，不能以一个实际前沿只有一个词为由否定全协议下界。

一个个别词可以很短地描述；统一固定载体则必须同时有足够状态容纳最坏情况。若保存载体实际不可访问，观察者没有假设149.1中的可执行解码接口，因而不能称全部历史已保留为可用知识。该证明只用经典区别与恢复映射；量子过程的内积相容条件仍由第141章约束，未出现温度、能量、擦除机制或热浴，所以不产生相应热界。$\square$

## 150. 单一追加链上的有限有根图表达

**定义 150.1（有限简单关系图的登记菜单）。** 给定有限简单无向连通图 $G=(V,\mathcal A)$ 和指定根 $v_0\in V$。简单表示无自环、无重边。先已登记根地址零；若根的属性或来源尚未取得，须先用实际事件取得并登记，不能由地址零推出其未知属性。地址是有限可解码标签，每次使用的地址及关系来源均属于完整事件字段。

声明两类登记动作：第一类在一个已登记父地址下登记一个新地址及两者的父边；第二类在两个不同已登记地址之间登记尚未登记的一条边。每次事件保留实际动作、返回、地址、关系读数及来源标记，按假设144.2编码。对于一个固定有限图表达任务，可以提供足够的有限地址和字段域；若要保留原顶点名字或边属性，亦须编码这些字段。只记录新地址而不记录与原对象的对应，至多恢复重命名后的有根图。

这里区分形式登记菜单与实际取得菜单。表达定理假设可以登记给定图中的所需父边和余边；在未知图研究中，哪些边真实存在、如何取得关系读数以及这些动作是否合法，另由实际接口供应。

**定理 150.2（父先子后的串行表达史）。** 在定义150.1的形式菜单中，任意有限简单无向有根连通图都存在有限串行登记史，解码后得到该图及其根；每条事件只引用已经登记的地址。根已登记时，可以用恰好 $|\mathcal A|$ 个事件，每条图边登记一次。对单顶点图，历史为空。

证明（150.2）。使用经典生成树结果作中间步骤：钉版 Mathlib [Combinatorics/SimpleGraph/Acyclic.lean，`SimpleGraph.Connected.exists_isTree_le`](https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/SimpleGraph/Acyclic.lean)在简单图连通条件下给 $T\le G$ 且 $T$ 为树。本节把其域限制为有限有根图，不从生成树的存在推断未知图已经取得。

以 $v_0$ 为树根，把其余顶点按树距离非减排序；同层可任选固定次序。每个非根顶点有唯一通向根的树路径，其父顶点距离小一，已经在它之前登记。因此逐个使用第一类事件，登记新顶点地址及父边，得到全部顶点和恰好 $|V|-1$ 条树边。再以任意固定次序遍历 $\mathcal A\setminus\mathcal A(T)$，对每条边使用第二类事件；两端此时都已有地址，且边尚未登记，动作满足菜单条件。

简单性保证每条无向边只需登记一次。全部父边和余边的并恰为 $\mathcal A$，无多余边；地址到顶点的双射及根地址保存有根图的重构。事件数为 $(|V|-1)+(|\mathcal A|-|V|+1)=|\mathcal A|$。单顶点连通简单图没有边，所以无需事件。每次都可以按第144章追加一个完整码，形成唯一已发生前缀链。$\square$

**命题 150.3（串行表达不限制关系维度或取得未知图）。** 上述表达合同可用于任何有限连通三角网、方格网及三重笛卡尔网格的关系图；它不把单前沿变成单条空间轴，也不自动取得这些图的实际距离、嵌入或物理维数。

证明（150.3）。这些有限网在连通、无自环和无重边的声明下都是定理150.2的实例，故同一串行菜单可登记全部邻接关系。档案的追加顺序只排序登记事件；新节点仍可与多个已有节点相连，余边可形成多个回路，解码的图不必为路径。邻接图本身不指定边长、夹角或空间嵌入；同一个图可以附不同距离和不同嵌入。因此要主张实际三角长度、手性、三维坐标或真实空间，还需把相应关系测量及其共同标定接入事件，不从表达史的存在得到这些读数。$\square$

**假设 150.4（单电子历史类比的使用范围）。** 历史参照只取 Richard P. Feynman 的诺贝尔演讲 [*The Development of the Space-Time View of Quantum Electrodynamics*，1965年12月11日](https://www.nobelprize.org/prizes/physics/1965/feynman/lecture/)中包含 “I received a telephone call” 的 Wheeler 电话段。原文描述一条在时空中折返的电子世界线，固定时间截面可与它相交多次，反向时间的部分以正电子解释；Feynman 紧接着指出正电子数目的问题，并明确说他没有同样认真接受“所有电子都是同一个电子”的想法。

本节只借用“一条生成关系可以有多个局部读出”的有限结构图景。世界线的正反时间、连续时空截面和粒子解释不属于本卷档案模型：第144章档案仅沿实际事件追加，没有逆向追加的正电子事件，也没有从图登记推出物质同一性。此引文不作为原生 FIB 取得合同、所有物质同一粒子、永恒观察者或真实空间维数的证据。

## 151. 单前沿、正交创新与有限恢复的条件整合

**假设 151.1（同一协议中的五个合同）。** 在固定观察者及有限任务内共同供应以下条件。

第一，实际事件采用定义144.1的完整字段，编码与可访问保存满足假设144.2，档案按定义144.4追加。策略只据已获记录；若同时读数未分内部次序，就保留为复合事件。第二，候选及参考权采用定义146.1的同一有限非空 $\Omega$、严格正 $\mu$、嵌套记录和固定目标 $f$。第三，若要使用黄金分辨量，另供应假设147.2的精确半开区间模型及原低到高守卫，保持首尾接缝；若要把事件深度与窗口时标相等，另要求每个事件恰登记一个窗口。第四，若要使用全历史容量，恢复域和实际可读载体满足假设149.1；若只允许较小域，不把它冒称全部合法词。第五，若要表达有限关系图，供应定义150.1中的地址、完整关系字段和所需登记菜单；实际未知关系仍须取得。

本假设没有要求潜在后继唯一、每一步固定目标创新非零、周期读出无周期、对象不能逆返回，或记录过程对任意人类永远成立。所有结论只在相应合同共同实现时组合；分别可写的合同不自动存在于同一物理实现。

**定理 151.2（单前沿的完整条件链）。** 在假设151.1的对应合同下，成立以下各项。

（1）完整实际历史有唯一可解码档案、唯一前缀及末事件。档案的追加深度每次加一，叶数严格增加；唯一性属于已经发生的前缀链，不排除多个合法结果或多个允许后继。

（2）候选上的可见空间按包含递增，固定目标有唯一正交创新和未观察余项，

$$
f=P_0f+\sum_{k=0}^{n-1}\Delta_kf+(I-P_n)f,\qquad
\|f\|_\mu^2=\|P_0f\|_\mu^2+
\sum_{k=0}^{n-1}\|\Delta_kf\|_\mu^2+\|(I-P_n)f\|_\mu^2.
$$

一步目标可见能量严格增加恰在该步创新非零；不能删去未观察余项。

（3）额外黄金区间模型中的每个合法窗口历史满足

$$
\mathcal I(h)=3n\log_2\phi+\log_2r_{i_0}-\log_2r_{i_n},\qquad
\Theta(h)=n.
$$

这个时标只在一事件一窗口时与档案深度相同，且不因此等于物理钟或目标知识量。

（4）从接缝零起，对全部定长合法窗口历史统一可恢复的经典保存方案至少有 $F_{3n+2}$ 个可区别状态，固定长度二进制容量至少为 $\lceil\log_2F_{3n+2}\rceil$ 位，包含空词和末零窗口。受限任务与已知轨迹按其实际像重算。

（5）有限简单无向有根连通图可由一条父先子后的登记史表达，图的回路和多方向关系与档案的单一实际前缀链相容；表达能力不证明未知图已被取得。

证明（151.2）。第一项由定理144.5、144.6给出，单射依赖完整事件码，不能以五模式码代替未编码字段。第二项把同一协议记录接入定理146.2和已有档案塔§121.6；该正交直和给分量唯一性及两条完整式，非零创新给严格性。第三项直接应用定理147.3、147.4，接缝与半开端点规则使首尾修正和历史区间都良定义；定理147.5排除其与任意参考权、物理钟和知识的免费等同。第四项按假设149.1使用定理149.2、149.3，定理149.4说明统一恢复域不能被一个已知词替代。第五项应用定理150.2、150.3，其实际菜单及地址读数仍属假设。各项共享的只有已声明的协议、来源和相应映射；推导不反向提供缺失的实际实现。$\square$

**命题 151.3（几何接口与三种顺序的边界）。** 以上条件链有三个不同顺序：已发生档案的前缀顺序、同一候选空间内的可见子空间包含顺序、额外区间模型的分辨率细化顺序。它们可相容，但不合成一条 Euclidean 位置轴。第138章的三角内积关系、第137章的正方次序差、第138章的圆周期及本篇追加深度各有其载体；任意两者的桥都须保留实际关系与标定条件。

证明（151.3）。非空追加在第一顺序中严格前进。第二顺序允许相等，且可出现新分区而固定目标零创新，如定理146.3、146.4；第三顺序在所供几何模型内严格缩短区间，却可对已知下一模式不增加任何目标知识，如命题147.5。这些例子已排除三个顺序无条件等价，也排除把事件次数当作一个普遍知识计量。

在第138章平面接口中，若欲由三角长度恢复 $g(u,v)$，须实际取得同一来源、同一尺下的三边 $\|u\|,\|v\|,\|u-v\|$，再用

$$
g(u,v)=\frac{\|u\|^2+\|v\|^2-\|u-v\|^2}{2};
$$

或按命题138.3实际取得相应组合长度并使用极化。只给两范数和面积绝对值，母式一般只能确定 $g^2$，在 $g\ne0$ 时不能决定其符号；有向面积的符号还须已保留次序及定向。三角勾股用于给定内积中的正交分量，不从三边读数免费产生第三个空间方向。$K=MJ-JM$ 的正方结构属于线性表达，只有第137章的实际动作和量具链才能回接实际读数；圆或三周期可以返回同一读出，而完整档案仍追加，见第148章。法向则另依赖第139章的三维内积和单位定向体积，不能用两个面内方向代替该前提。

因此，维持实际距离、手性和全部允许未来所需的最少原生可取得结构，仍须证明来源映射、测量、保存、运输与操作菜单的忠实共同实现。这些普通条件推导不证明人类记忆永不丢失、单一宇宙先验、永恒观察者、未知量子态复制或物理空间三维。$\square$

## 追加锚（第144–151章以下为增补区）

## 152. 已取得的区别、五模式选择与零贡献参照

**假设 152.1（保留记录及继续使用的菜单）。** 固定定义136.1中的观察者、已取得初始参照和有限任务。实际区别由已经执行的动作、实际返回以及本次量具、控制、来源和标定共同给出；需继续使用的字段按定义144.1记入完整事件，并在假设144.2的可访问载体上保留。后续菜单只含已经取得执行权限的动作及比较，策略只据已获记录选择下一步。尚未取得的读数不填入档案；一次合法读取的 $\mathrm{null}$ 返回，与未读、$\mathrm{End}$、$\mathrm{Stop}$ 分别保留。

以下数学接口按所需任务分别附加条件：状态差分要求同一来源链、同一组成更新及固定量具下可比较的读数；窗口接续要求固定读向、初态及接缝；操作词要求实际生成元、明确求值次序和可继续的等价关系；中心相位比较要求同参照相干控制、准备和读出。一个接口可以作为条件模型研究，但只有已实际取得、保留且可以再用的接口才属于该观察者的菜单。分别写出的接口不自动在同一实现上共同可用。

本批中称一个摘要充分，始终相对于这个固定菜单：摘要必须保留所需响应、动作合法性及后继更新。若后来扩大菜单，须重新验证这些条件，不以旧任务中的零差异宣布全部来源等同。

**定义 152.2（原树、局部组成及位序）。** 采用[《FIB 关系延拓几何》，版本2bf48d5375954170bae475578dc4d93ce77f8384，定义1.1、1.3、2.1及2.4](https://github.com/the-omega-institute/trureturing/blob/2bf48d5375954170bae475578dc4d93ce77f8384/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)的自由有序树、替换和零贡献约定。令

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle=\gamma,\qquad
c(\alpha)=\binom10,\quad c(\beta)=\binom01,\quad c(\gamma)=\binom11,
$$

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
\ell=(2,3),\qquad c(\rho t)=Mc(t).
$$

三个位置按低到高写为 $(b_0,b_1,b_2)$，只允许 $b_0b_1=b_1b_2=0$。局部贡献是整数列向量

$$
d_w=b_0c(\alpha)+b_1c(\beta)+b_2c(\gamma)
=\binom{b_0+b_2}{b_1+b_2},\qquad q_w=\ell d_w.
$$

沿用[前卷《Auric · FIB-ATOM 续篇：二元来源的三维二阶关系完成》，版本b9b4a62b69908c14f2b3ceb07204620db61aa862，定义24.1、命题24.2](https://github.com/the-omega-institute/trureturing/blob/b9b4a62b69908c14f2b3ceb07204620db61aa862/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)的表，按本批顺序记为

| 152 的模式 | 低到高三位 | 局部组成 $d_w$ | 零层数量 $q_w$ |
| --- | --- | --- | --- |
| $\mathrm{null}$ | $000$ | $(0,0)^T$ | $0$ |
| $[2]$ | $100$ | $(1,0)^T$ | $2$ |
| $[3]$ | $010$ | $(0,1)^T$ | $3$ |
| $[5]$ | $001$ | $(1,1)^T$ | $5$ |
| $[25]$ | $101$ | $(2,1)^T$ | $7$ |

这里 $[25]$ 是两端同时选中，数量为 $2+5$，不是乘积 $2\cdot5$ 或十进制二十五。三个单选、允许的端点联合及不选，描述同一个局部配置关系的五个结果；不引入五种本体。$\gamma=\rho^2\alpha$ 是有序配对树，不把它认作新的原子叶。跨窗口合法性另由接缝决定，局部表本身尚未给出全部合法串接。

**命题 152.3（零贡献、非空事件码与可继续区别）。** 五模式域中 $d_w=0$ 恰在 $w=\mathrm{null}$。然而，实际取得这个结果的事件既不是未读，也不是零树；使用定义144.3的模式码时，其码的组成反为 $(2,0)^T$。若未来菜单读取事件来源或窗口接缝，单独保留零贡献不能替代完整事件及相应接缝。

证明（152.3）。组成的两个坐标分别为 $b_0+b_2,b_1+b_2$，各项非负。它们同时为零强制三个占位位全为零，反向也成立。这一零属于贡献载体 $\mathbb N^2$。定义144.3给模式码 $E_{\mathrm{null}}=\langle\alpha,\alpha\rangle$，组成加法给 $(2,0)^T$，两叶不是空来源；完整事件码还须保留动作、实际返回及 $\kappa$。

例如，两个实际零返回可使用不同量具或来源标记，贡献相同而完整事件不同；若固定未来菜单会比较这些标记，合并它们就不能给出该比较。接缝也须按相应读者保存或由已证恢复式取得，不能仅由“贡献为零”代替其更新合同。这正是定义140.4的任务商条件在零贡献处的使用：只在未来响应、合法性和后继都相同的纤维内允许合并。$\square$

## 153. 固定 FIB 更新中的组成与差分同信息

**假设 153.1（同一组成轨道及固定读出）。** 取 $K=\mathbb Z$ 或 $\mathbb R$，给定 $c_0\in K^2$，令 $c_{n+1}=Mc_n$，$n\ge0$。定义

$$
\delta_n=c_{n+1}-c_n,\qquad
y_n=\ell c_n,\qquad d_n=y_{n+1}-y_n.
$$

组成来自原树时 $c_n\in\mathbb N^2\setminus\{0\}$，但差分在 $K^2$ 中计算，不要求非负。标量读出始终用同一个 $\ell$。回接实际读数时，要求更新确实为所声明的 $M$，每对参与相减的读数来自这个共同轨道，量具、单位和来源比较合同固定；改变读者、插入其他动作或逐次漂移不属于本假设。数学上可计算差分，不证明这些读数已取得。

**定理 153.2（可逆组成差分及两次标量差分恢复）。** 在假设153.1下，

$$
M-I=M^{-1}=\begin{pmatrix}-1&1\\1&0\end{pmatrix},\qquad
\delta_n=M^{-1}c_n,\qquad c_n=M\delta_n,\qquad
\delta_{n+1}=M\delta_n.
$$

因此完整二维组成和同一步完整二维差分一一对应；此处的一一对应不涉及恢复树的左右次序、括号或事件来源。标量差分满足

$$
d_{n+1}=y_n,\qquad d_{n+2}=d_{n+1}+d_n.
$$

若 $c_0=(a,b)^T$，则

$$
\binom{d_0}{d_1}
=\begin{pmatrix}1&2\\2&3\end{pmatrix}\binom ab,
\qquad
a=2d_1-3d_0,\qquad b=2d_0-d_1.
$$

同样，两次相邻差分 $d_n,d_{n+1}$ 按这个逆式恢复 $c_n$。任意给定的 $d_0,d_1\in K$ 都对应唯一一条本假设中的组成轨道；若还要求来自非负组成，必须另满足 $2d_1-3d_0\ge0$、$2d_0-d_1\ge0$，原树来源还排除二者同时为零。

证明（153.2）。复用钉版基础卷定义1.3的 $M^2=M+I$，得到 $M(M-I)=(M-I)M=I$。矩阵减法即给所列 $M^{-1}$。由轨道合同，$\delta_n=(M-I)c_n=M^{-1}c_n$；左乘 $M$ 恢复 $c_n$。由于 $M^{-1}$ 与 $M$ 交换，

$$
\delta_{n+1}=M^{-1}c_{n+1}=M^{-1}Mc_n
=M(M^{-1}c_n)=M\delta_n.
$$

又由同一个矩阵恒等式，$c_{n+2}=c_{n+1}+c_n$。施加固定 $\ell$ 得 $y_{n+2}=y_{n+1}+y_n$，于是

$$
d_{n+1}=y_{n+2}-y_{n+1}=y_n.
$$

把两个相邻的上述等式相减，得 $d_{n+2}-d_{n+1}=y_{n+1}-y_n=d_n$。直接乘行向量，$\ell(M-I)=(1,2)$、$\ell(M-I)M=(2,3)$，故 $d_0=a+2b,d_1=2a+3b$。其系数矩阵行列式为 $-1$，逆矩阵为

$$
\begin{pmatrix}-3&2\\2&-1\end{pmatrix},
$$

这给两条恢复式，并在 $K=\mathbb Z$ 时也保整数。对任意差分初值按逆式定义 $c_0$，再作 $M$ 递推；所得差分有同一初值及同一二阶递推，故全部一致。非负条件正是恢复的两个坐标非负；在原树的组成像中还须有至少一片叶。把 $n$ 时刻作为初时刻重复这个计算，得到相邻差分的局部恢复式。$\square$

**命题 153.3（无积分常数的适用范围与来源残余）。** 上述恢复不适用于任意动力学，也不使一个标量差分独自恢复一般二维组成。任意固定序列的逐步差分通常丢失常数；本章不需要额外积分常数，依赖完整 FIB 轨道和固定读出合同。

证明（153.3）。原树 $\alpha$ 的初始组成为 $(1,0)^T$，而 $\delta_0=(-1,1)^T$；负坐标表示两个时刻的数量相减，不表示非空树含负叶。任取状态更新 $c_{n+1}=c_n$，全部差分恒零而初态可任意，故一般更新没有本章的可逆性。仅知 $d_0=a+2b$ 时，非负组成 $(2,0)^T$ 与 $(0,1)^T$ 都给二，下一差分却为四与三；一个标量并不足够。

若任意两条标量序列 $u_n,v_n$ 满足 $u_{n+1}-u_n=v_{n+1}-v_n$，归纳得 $v_n-u_n=C$ 为常数。若二者还同时满足本章的 Fibonacci 递推，则把 $v_n=u_n+C$ 代入 $v_{n+2}=v_{n+1}+v_n$，得到 $C=2C$，故 $C=0$。这是“无额外积分常数”的准确原因，并不豁免读数的实际取得和保存。

二维差分则保留组成的全部信息，但组成自身仍是粗观察：钉版基础卷定理1.4的两棵树 $\langle\alpha,\beta\rangle$ 与 $\langle\beta,\alpha\rangle$ 组成相同，遂有相同差分而不是同一来源。$\square$

## 154. 五模式的一次原子替换与局部变化值

**定义 154.1（原子替换的局部标量变化）。** 对定义152.2的五个局部贡献，定义

$$
D(w)=\ell(Md_w-d_w)=\ell(M-I)d_w.
$$

这里比较一个既有局部贡献在原子替换前后；不是向累计读者输入下一个三位窗口。由定理153.2的固定差分行向量，得到

| 154 的模式 | 当前 $\ell d_w$ | 原子替换后 $\ell Md_w$ | 变化值 $D(w)$ |
| --- | --- | --- | --- |
| $\mathrm{null}$ | $0$ | $0$ | $0$ |
| $[2]$ | $2$ | $3$ | $1$ |
| $[3]$ | $3$ | $5$ | $2$ |
| $[5]$ | $5$ | $8$ | $3$ |
| $[25]$ | $7$ | $11$ | $4$ |

表中 $\ell M=(3,5)$、$\ell(M-I)=(1,2)$，因此各行都由同一个替换和量具产生，而非任意给五个模式编号。替换后的组成可以离开原五个局部贡献，例如 $Md_{[5]}=(1,2)^T$；不把原子替换误写成五模式域上的一个置换。

**命题 154.2（局部单射与串接合同的区别）。** $D$ 从五模式域到 $\{0,1,2,3,4\}$ 是双射。在假设152.1、153.1的同一实际局部比较接口中，实际取得的准确变化值可以恢复该局部模式；这个结论不把全局历史变成普通五进制，也不恢复未保存的事件字段。

证明（154.2）。表中五个变化值两两不同且覆盖所列目标集，反查表即给唯一模式。其单射性以局部候选恰是这五个模式、一次 $M$ 替换和固定 $\ell$ 为条件；换候选域、换读者或换更新不由这张表保证单射。

对低到高语法，直接复用钉版基础卷定理2.3：从接缝零出发，长度二合法词有 $F_8=21$ 个，而不是无守卫的五进制两位的 $25$ 个。例如低到高的 $[5][2]$ 被跨缝相邻占位排除；若反转读向，它又是合法的高到低输入，而高到低的 $[2][5]$ 非法。故用 $D$ 逐窗替换标签只是在原有合法语言上重编码，仍需保留其读向、长度和接缝规则。更不能从一个当前局部变化值得到过去全部窗口或本次 $\kappa$。零变化在本表中表示固定零贡献，不表示宇宙本体为空。$\square$

## 155. 零贡献、自身参照与完整状态的三层 null

**定义 155.1（三种零的载体）。** 贡献零是组成载体中的 $0\in K^2$；相对零是对象组成 $c$ 与观察者参照组成 $o$ 之差 $r=c-o=0$；实际 $\mathrm{null}$ 是已执行窗口读取的一种返回。前两者是向量条件，第三者是有来源的事件。自由词中的空词及恒等操作另在第156章定义，均不由这些名称认作全部世界状态。

**命题 155.2（唯一组成不动点及共同变化中的相对零）。** 在 $K=\mathbb Z$ 或 $\mathbb R$ 的组成更新中，$M0=0$，且 $Mc=c$ 当且仅当 $c=0$。非空原始有限树没有 $\rho t=t$。若同一时刻的对象与观察者参照都按同一个 $M$ 更新，则

$$
r'=Mc-Mo=M(c-o)=Mr.
$$

特别地，$c=o$ 时相对零保持，但两者各自可以变化。

证明（155.2）。$Mc=c$ 等价于 $(M-I)c=0$，定理153.2给 $(M-I)^{-1}=M$，故强制 $c=0$；反向直接成立。每棵原始有限树至少有一片 $\alpha$ 或 $\beta$ 叶，组成非负且非零。若 $\rho t=t$，组成会满足 $Mc(t)=c(t)$，与非零矛盾。这里零贡献的固定性并没有添入第三种原子叶。

相对更新式由同一个线性映射的相减得到。取 $c=o=(1,0)^T$，下一步二者都为 $(0,1)^T$，仍相等而各自并未不动。这个例子排除“自身参照为零”推出“观察者未变化”或“世界没有其他状态”。若对象用 $M$ 而参照用另一个 $N$，则

$$
r'=M r+(M-N)o;
$$

未供 $N=M$ 或相应相容条件时，不能套用 $r'=Mr$。数学共同变化也不代替实际取得、运输和标定参照的权限。$\square$

**命题 155.3（完整单元素状态不自生非平凡来源）。** 若完整状态集合确为 $X=\{\mathrm{null}\}$，而全部更新只给 $\rho(\mathrm{null})=\mathrm{null}$，则从它出发的轨道始终为这个元素，不能在同一完整状态合同内生成不同的 $\alpha,\beta$。若仍要区别多个事件或操作，所需关系、控制、位置或记录须出现在扩充后的模型中。

证明（155.3）。零次轨道就是 $\mathrm{null}$，每次施加固定更新仍是 $\mathrm{null}$，归纳给 $\rho^n(\mathrm{null})=\mathrm{null}$。单元素集合没有第二个不同状态，因此不能将非平凡自由树的两个不同叶映成两个不同完整状态。可以给同一对象反复读取并追加不同长度的档案，但此时完整描述已经含事件及档案层，不再只是上述单元素状态。

同理，若不同操作、返回或控制被认为实际可区别，就须保留这些差别的载体与操作语义；不能先把它们删除，再以“零参照”解释其凭空产生。观察者角色保持可以是关系合同中的不变量，不能据此建立外部绝对本体或永恒记忆。$\square$

## 156. 单承载对象上的自由词与实际自作用

**定义 156.1（自由操作词及乘序）。** 给定一个非空承载集合 $O$ 和两个已指定的自映射 $A_\alpha,A_\beta:O\to O$；若用于实际操作，还要求它们属于假设152.1的已取得菜单，并把需要的控制和来源纳入承载状态。符号 $\alpha,\beta$ 在本章先是操作词的字母，不把两个自映射假定为同一个或由恒等凭空生成。

令 $W=\{\alpha,\beta\}^*$ 为自由词幺半群，单位为空词 $\epsilon$，乘法为有序拼接。定义替换

$$
\rho_{\rm op}(\alpha)=\beta,\qquad
\rho_{\rm op}(\beta)=\beta\alpha,\qquad
\rho_{\rm op}(uv)=\rho_{\rm op}(u)\rho_{\rm op}(v),\qquad
\rho_{\rm op}(\epsilon)=\epsilon.
$$

它作用在语法词上，非空迭代开始为

$$
\alpha\longmapsto\beta\longmapsto\beta\alpha
\longmapsto\beta\alpha\beta.
$$

为与定义117.1的叶序乘法一致，求值取

$$
E(w_1\cdots w_k)=A_{w_1}\circ\cdots\circ A_{w_k},\qquad
E(\epsilon)=\operatorname{id}_O.
$$

因此右端字母先执行，$E(uv)=E(u)\circ E(v)$。若实际事件先执行 $A_\alpha$ 再执行 $A_\beta$，累计作用为 $A_\beta\circ A_\alpha=E(\beta\alpha)$，而事件档案按发生顺序记 $e_\alpha e_\beta$。词字母、矩阵乘积与完整事件采用不同类型，不能把字母名代替完整来源码。

**命题 156.2（替换下降到实际求值像的条件与反例）。** 存在映射 $\bar\rho:E(W)\to E(W)$ 使

$$
\bar\rho(E(w))=E(\rho_{\rm op}(w))
$$

当且仅当求值纤维满足

$$
E(u)=E(v)\ \Longrightarrow\
E(\rho_{\rm op}(u))=E(\rho_{\rm op}(v))
\qquad(u,v\in W).
$$

满足时 $\bar\rho$ 唯一且保持该像中的复合及恒等；未满足时，词替换仍良定义，却不能成为实际自映射集合上的这个更新。

证明（156.2）。这里将钉版基础卷定义3.2的稳定纤维检验用于词求值及指定替换。若已有 $\bar\rho$，相同求值经同一个 $\bar\rho$ 必相同，故检验必要。反向，以任一代表 $w$ 定义 $\bar\rho(E(w))$；检验恰保证换代表不改变值，且所得值仍在 $E(W)$。每个像元素都有代表，所以这也给唯一性。对代表 $u,v$，

$$
\begin{aligned}
\bar\rho(E(u)\circ E(v))
&=\bar\rho(E(uv))
=E(\rho_{\rm op}(uv))\\
&=E(\rho_{\rm op}(u))\circ E(\rho_{\rm op}(v)),
\end{aligned}
$$

而空词给 $\bar\rho(\operatorname{id}_O)=\operatorname{id}_O$。这些等式只定义像上的数学更新，不供应实施替换的物理门。

条件并不由“都是 $O\to O$”自动给出。取 $O=\{0,1\}$、$A_\alpha=\operatorname{id}_O$、$A_\beta$ 为交换零与一的自映射。词 $u=\alpha$ 和 $v=\epsilon$ 求值相同；替换后却分别求值为 $A_\beta$ 和 $\operatorname{id}_O$，不同。因此一般自作用关系可能不保替换，不能直接把语法规则施加到任意实际操作等价类。这里的 $E(u)=E(v)$ 比较在整个声明承载域上的映射，不是只比较一个当前输入的返回。若还商去控制或来源，须对这个更粗求值的纤维及全部所需后续任务再验条件。$\square$

**定义 156.3（叶序、恒等与单过程类比的范围）。** 叶序映射沿用定义116.1：$\operatorname{wd}(\langle s,t\rangle)=\operatorname{wd}(s)\operatorname{wd}(t)$。树替换的两个叶规则分别给叶序 $\beta$、$\beta\alpha$，与 $\rho_{\rm op}$ 一致。若对应对两个子树成立，保配对及保拼接给

$$
\operatorname{wd}(\rho\langle s,t\rangle)
=\operatorname{wd}(\rho s)\operatorname{wd}(\rho t)
=\rho_{\rm op}(\operatorname{wd}(s)\operatorname{wd}(t)),
$$

所以结构归纳得到 $\operatorname{wd}\rho=\rho_{\rm op}\operatorname{wd}$。这是原树到操作词的一个对应。它忘括号，不能成为原树的完整替代：前卷命题103.2的 $\langle\langle\alpha,\alpha\rangle,\beta\rangle$ 与 $\langle\alpha,\langle\alpha,\beta\rangle\rangle$ 叶序相同而来源及其三周期读出不同。

空词的求值是承载对象上的恒等操作，不是承载对象全部状态的唯一值，更不是整个宇宙为空。一个对象可以有多个自映射，但这里的非平凡语法已经给了生成元；$\rho_{\rm op}(\epsilon)=\epsilon$ 不自生 $\alpha$。已给语法也不等于实际器具已经取得这些操作。

单过程的历史类比仅取假设150.4所引 Richard P. Feynman，[*The Development of the Space-Time View of Quantum Electrodynamics*，Nobel Lecture，1965年12月11日](https://www.nobelprize.org/prizes/physics/1965/feynman/lecture/)中 “As a by-product of this same view” 起首的 Wheeler 电话段。原文的一条折返世界线可与同一时间截面相交多次，并将逆向时间部分作正电子解释；Feynman指出正电子数量问题，并没有同样认真接受“全部电子是同一个电子”的说法。这里只保留复杂单过程有多个切面读出的图景，不用它证明 FIB 语法、实际单对象仪器、物质同一性或本卷档案的时间模型。

## 157. 高到低窗口的零输入运输与随动坐标

**定义 157.1（固定即时读者及初始化）。** 本章直接采用钉版基础卷定义7.1、定理7.2及前卷定义25.1、29.1的高到低即时读者。组成记为 $x_n$，区别于第158章的占位函数 $x$。初态 $x_0=0,s_0=0$，空输入合法、数量零；允许高端零窗口，每个合法有限前缀立即输出，无 $\mathrm{End}$ 或最高窗非空守卫。第 $n+1$ 个实际输入为 $w_{n+1}$，窗口来自高到低的发生顺序，更新为

$$
S=M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\qquad
x_{n+1}=Sx_n+d_{w_{n+1}}.
$$

若该窗口的低到高三位是 $(b_0,b_1,b_2)$，旧接缝 $s_n$ 是此前较高窗口的最低位。守卫为 $s_nb_2=0$，新接缝为 $s_{n+1}=b_0$：

| 157 的输入 | 允许旧接缝 | 新接缝 |
| --- | --- | --- |
| $\mathrm{null}$ | $0,1$ | $0$ |
| $[2]$ | $0,1$ | $1$ |
| $[3]$ | $0,1$ | $0$ |
| $[5]$ | $0$ | $0$ |
| $[25]$ | $0$ | $1$ |

非法输入进入独立吸收错误态 $\bot$，以下坐标公式只用于合法活态历史。矩阵 $S$ 搬运累计组成；第147章的 $A$ 计数低到高语法分支，第122章的 $P$ 给配置图概率，两者都不是这个组成更新。三位印刷次序仍低到高，不能由此反转实际读取次序。基础卷定理7.2只把完整有限词的反序高读结果与低到高位权和对应，不使两个读向的同时前缀响应相同。

**定理 157.2（零窗口的实际推进与随动增量）。** 对每条合法历史及其已声明层数 $n$，定义

$$
z_n=S^{-n}x_n,\qquad
S^{-1}=\begin{pmatrix}-3&2\\2&-1\end{pmatrix}.
$$

则 $z_0=x_0$，且

$$
z_{n+1}-z_n=S^{-(n+1)}d_{w_{n+1}},\qquad
z_n=x_0+\sum_{j=1}^n S^{-j}d_{w_j},\qquad x_n=S^nz_n.
$$

真实输入 $\mathrm{null}$ 使 $x_{n+1}=Sx_n,s_{n+1}=0$，但在这个坐标中 $z_{n+1}=z_n$。因此随动零增量不使实际窗口动作成为恒等，也不撤销该读取事件。

证明（157.2）。$\det S=-1$，所列整数矩阵与 $S$ 左右相乘均为 $I$，故正负整数次幂在 $K^2$ 上有定义。代入即时更新，

$$
\begin{aligned}
z_{n+1}
&=S^{-(n+1)}(Sx_n+d_{w_{n+1}})\\
&=S^{-n}x_n+S^{-(n+1)}d_{w_{n+1}}
=z_n+S^{-(n+1)}d_{w_{n+1}}.
\end{aligned}
$$

从零层累加得到求和式；乘 $S^n$ 即恢复组成。$z_n$ 可以有负坐标，它属于随动的代数表示，不要求是某棵非负来源树。零模式贡献为零，增量式使 $z$ 固定；原合同仍更新接缝并把层数从 $n$ 改为 $n+1$。

具体从初态实际高读 $[2]$ 再读 $\mathrm{null}$，两步均合法。第一步给 $x_1=(1,0)^T,s_1=1$、数量二；第二步给

$$
x_2=S\binom10=\binom12,\qquad s_2=0,\qquad \ell x_2=8.
$$

而 $z_1=(-3,2)^T=z_2$。一般 $(S-I)x=0$ 在 $K=\mathbb Z$ 或 $\mathbb R$ 上仅有零解，因为 $S-I=\left(\begin{smallmatrix}0&2\\2&2\end{smallmatrix}\right)$ 的行列式为 $-4$。所以非零组成的零窗口运输确实改变组成。初态读取零模式可以使组成仍零，但若这是实际取得的事件，其完整档案仍按定理144.5追加；零组成不能把这次读取变为未读。$\square$

**命题 157.3（坐标恢复所需的层数及来源边界）。** 仅保留 $z_n$ 一般不能恢复当前组成；保留正确层数后才能用 $x_n=S^nz_n$。接缝、完整事件前沿及来源标记须保留，或另给针对其实际像的恢复证明，不能由换坐标自动删除。$S^{-n}$ 是代数换坐标，不供应逆物理门。

证明（157.3）。定理157.2的两个阶段有同一个 $z$ 而不同 $x$，故忘记层数已经造成当前组成的恢复失败；反向给定 $(n,z_n)$ 时恢复式唯一。守卫取决于声明的旧接缝，对新的窗口动作仍须评价 $s_nb_2$；换组成坐标没有建立接缝的恢复函数，也没有把错误态变成合法活态。若其他已存数据确能在实际可达像上恢复接缝，可以使用该证明，不能仅把可逆组成矩阵当作证明。

对完整来源的未来任务，$n$ 也只统计窗口数，复合读取、非窗口事件及来源字段仍按第144章记录，不能反由 $n$ 获得全部 $h_n$。假设152.1若已经供应完整档案，其可访问前缀和末事件按定理144.5保持；数值重表达不改变这些事件。矩阵有逆只证明可以表达同一个向量，不证明观察者取得能使实际对象逆返回的动作；实际逆的条件仍为命题148.4。$\square$

## 158. 五模式函数中的零、整域与实际事件

**定义 158.1（共同模式域的函数代数）。** 沿用前卷定义38.1、定理38.2、39.2及本卷定理140.2，令

$$
L=\{\mathrm{null},[2],[3],[5],[25]\},\qquad
\mathcal A=\mathbb R^L.
$$

函数 $x,z,y$ 分别指示 $2,3,5$ 位置，坐标按 $(x,z,y)$ 的低到高顺序；第140章的 $(x,y,z)$ 只是后两坐标的另一种印刷排列。在同一 $L$ 上的逐点乘法满足已给关系

$$
x^2=x,\quad z^2=z,\quad y^2=y,\qquad xz=yz=0.
$$

为区分五个完整模式，记事件指示函数

$$
e_{25}=xy,\quad e_2=x-xy,\quad e_5=y-xy,\quad
e_3=z,\quad e_{\mathrm{null}}=1-x-y-z+xy.
$$

这里 $1$ 是这个函数代数的恒真单位，$0$ 是恒零函数。不是以 $1$ 证明一种共同物质，或以 $0$ 宣告世界不存在。$e_{\mathrm{null}}$ 指示零占位模式，不把尚无读数的情形补成该模式。

**命题 158.2（事件指示、完整响应与实际像的退化条件）。** 在共同五模式域 $L$ 上，五个 $e_w$ 两两正交幂等，和为 $1$；$e_{\mathrm{null}}\ne0,1$。任意 $f\in\mathcal A$ 使用既有函数基唯一写为

$$
f=c_0+c_2x+c_3z+c_5y+c_{25}xy,\qquad
c_{25}=f([25])-f([2])-f([5])+f(\mathrm{null}).
$$

实际事件若只到达一个非空子集 $L_{\rm act}\subseteq L$，相应完整模式函数空间为 $\mathbb R^{L_{\rm act}}$，维数仅为 $|L_{\rm act}|$。限制后的 $e_{\mathrm{null}}$ 为零恰在零模式不可达，为恒一恰在 $L_{\rm act}=\{\mathrm{null}\}$；这两种退化仍不将它认作全部世界状态。

证明（158.2）。直接复用前卷定理39.2及本卷定理140.2的函数展开，前四系数为 $f(\mathrm{null})$ 及三个单模式值与该值之差，最后系数为所列联合差分。把五个模式的占位代入定义158.1，每个 $e_w$ 在该模式为一，在另外四点为零。因此每个平方等于自身，不同两个的积为零，逐点和为一。零模式点证明 $e_{\mathrm{null}}$ 非恒零，模式 $[2]$ 点证明它非恒一。这里调用既有函数基，不另以五维线性代数宣称新的空间方向。

限制到实际像时，仍可使用每个可达模式的单点指示，它们张成全部实际函数且线性独立，故维数是像的点数。零模式指示的两个退化条件由其值域直接给出；例如只实际取得零模式并不等于取得了另外四个响应值，限制数据不能唯一确定一个未知 $f$ 在整个 $L$ 上的五个系数。对 $L_{\rm act}$ 的函数充分性也只涉及这个已声明像，不扩张为外部宇宙。

若 $\eta$ 从完整已取得事件映到模式，$e_w\circ\eta$ 可以识别事件的模式字段，但会忘动作、量具及 $\kappa$。只有一个未来任务 $F$ 在 $\eta$ 的纤维上恒定时，才有 $F=f\circ\eta$；若还需继续操作，动作合法性、响应和后继必须同时在纤维上稳定，直接应用定义140.4。两个同模式事件的来源标记若被后续读取区分，当前五函数就不能恢复这种区别。恒真函数只说明在已定义域内取值一，零模式指示只说明已经得到一个特定返回，两者都不表示全部原始来源被读出。$\square$

## 159. 变化层的充分性与未消去的来源关系

**假设 159.1（共同合同和来源精度）。** 本章在假设152.1中组合已满足的接口：组成链及固定读出遵守假设153.1；局部变化候选遵守定义154.1；若用高读随动坐标，遵守定义157.1及保留层数、接缝的合同；若用实际操作词，遵守命题156.2的稳定求值纤维；若用相位区别，另供前卷定义107.1、定理107.2及本卷假设117.3要求的同参照相干比较，而不是只有普通通道。所有跨层比较都针对同一来源及所声明的控制和标定。

组成、五模式表和窗口方向引用定义152.2钉版基础卷；函数基和相位接口引用同一定义钉版前卷的第38–39、101–103、106–107章。本卷第116–151章的引用范围以[版本12bd974a853883521871e6226978442d6448c9ad](https://github.com/the-omega-institute/trureturing/blob/12bd974a853883521871e6226978442d6448c9ad/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md)为准。完整事件编码的引用类别为假设144.2，尺度边界及受限恢复域的引用类别分别为命题147.5、命题149.4；相应编号所指合同和数学边界按其陈述使用。

本章对原树的一步组成差分记为 $\delta(t)=c(\rho t)-c(t)$。把组成差分、局部变化、零参照、实际词替换及窗口运输接入固定未来菜单，得到以下条件综合。既有树、计数、函数基及相位结论作为中间结果复用；单过程历史引文只承担定义156.3的类比范围，不承担任何 FIB 或物理证明。

**定理 159.2（组成层同信息与来源层严格残余）。** 在假设159.1的对应条件下，成立以下结论。

（1）一步完整组成差分可逆地恢复同一步完整组成，并继续按 $M$ 递推；两次相邻标量差分可以恢复组成。局部五模式的一次变化值 $0,1,2,3,4$ 可以恢复该局部模式。这些结论的恢复域分别是组成或固定局部模式，不是全部来源树、合法全历史或完整实际事件。

（2）取原树 $t_-=\langle\alpha,\beta\rangle$、$t_+=\langle\beta,\alpha\rangle$。对每个 $n\ge0$，两树经同步原生推进后组成及组成差分相同，但在所指定 Pauli 提升中仍有相反酉表达：

$$
c(\rho^nt_-)=c(\rho^nt_+)=M^n\binom11,\qquad
\delta(\rho^nt_-)=\delta(\rho^nt_+)=M^{-1}M^n\binom11,
$$

$$
U_{\rho^nt_-}=-U_{\rho^nt_+}.
$$

若实际供应所要求的共同相干比较，可读取这项相对相位；若仅有两个目标通道，它们相同，不能声称已经读取中心相位。

（3）在同一个指定 $Q_8$ 提升中，实际先执行 $a=-iX$，再执行 $b=-iY$，再执行 $c=ba=iZ$，累计为

$$
cba=c^2=-I.
$$

三次作用的累计模二类型为零，与空词的当前类型相同，但空词累计为 $I$。相干比较在额外已供合同下区别 $-I$ 与 $I$；若三次作用已作为完整事件取得并保存，档案还严格多出三个事件，即使当前粗读出返回零。

（4）组成贡献零、相对自身零、操作恒等、模式指示及完整零读取事件属于不同载体。随动坐标对零窗口给零增量，原读者却继续运输并更新接缝、层数及事件记录。五模式函数代数的单位为恒真函数，零模式指示只是其中一个幂等；局部模式函数不是完整来源或全部未来任务的自动充分边界。

证明（159.2）。第一项分别应用定理153.2和命题154.2。二维可逆性止于组成像，局部单射止于指定五模式域；命题153.3、154.2明确保留源信息和合法全词的差别。

第二项直接复用前卷定理106.2的全树同组成与持续相反相位，不另以有限表示重新证明树结论。本卷定理116.2、117.2进一步定位忘括号后两叶尾部差异及固定原子的比较合同。将同一个组成乘 $M^{-1}$，给相同差分。前卷定理107.2说明：在已经供应的共同受控门上，两支为 $(U,-U)$ 时，对任意单位输入，控制输出为 $| -\rangle$；相同两支 $(U,U)$ 输出为 $|+\rangle$。而 $\operatorname{Ad}_{-U}=\operatorname{Ad}_U$，故单通道本身不提供这个比较，也不能由无相干准备的记录替代共同控制条件。

第三项采用前卷定义101.1、定理101.2的确切提升和定义148.1的列向量乘序。事件先后为 $e_ae_be_c$，累计右因子先作用，故是 $cba$ 而不是按事件印刷成 $abc$。由 $ba=c,c^2=-I$ 得式；在类型商中，三者分别为 $(1,0),(0,1),(1,1)$，和为零，中心正负被该商忘去。空词用 $I$ 初始化，其类型也零。所供相干比较可以把 $(I,-I)$ 两支确定地区别；普通目标通道则相同。若三个事件确已发生，定理144.5给唯一完整档案及追加深度增加三，不以通道相等撤销已发生记录。

第四项由命题152.3、155.2、155.3、定理157.2及命题158.2组合。相对零只在共同更新合同下保持；恒等操作不把承载对象缩成单元素世界；事件码也不等于它的零贡献。坐标公式恢复组成时仍需层数，继续合法读取仍需接缝及原菜单。五模式代数中的各模式指示划分模式域，却不恢复被模式映射合并的量具、来源或控制；因此其后续充分性仍须定义140.4的条件，而不是函数空间维数给出的物理解释。$\square$

**命题 159.3（回到零的分层判据及继续使用边界）。** 对一个实际过程说“回到 $\mathrm{null}$”时，必须指定是数量为零、当前类型为零、操作为恒等、中心相位相同、随动增量为零，还是完整来源及记录相同。固定一个投影不等于固定全部状态；组成差分再按 FIB 变化也只是在假设153.1下的组成结论。维持原生实际取得、距离、钟、可访问记忆及物理宇宙解释的共同实现仍未在这些条件推导中建立。

证明（159.3）。在非负组成及正量具 $\ell=(2,3)$ 下，数量零确实强制组成零，但组成不保存实际零读取事件。定理159.2的三作用路径与空路径同当前类型而有不同中心相位及档案；定理157.2的连续两阶段同随动坐标而有不同组成、数量、接缝和层数；定理159.2第二项同组成及同差分仍有不同原树与相对相位。这些共同合同内的成对实现逐项反驳从单层固定推出完整状态固定。

若未来菜单只读组成并仅允许已核的组成更新，定理153.2可以在该范围使用差分代替组成；若菜单包含同参照相位比较，上述同差分两树已经证明这个摘要不充分，必须保留相应来源或足够的联合记录。若菜单包含新的窗口动作，命题157.3要求保留或已证恢复其层数和守卫；若菜单包含实际词替换，命题156.2要求求值纤维稳定。这里的“需要”相对于指定任务，不假定全部形式动作已实际取得。

零参照可以保持角色关系，但不取得外部绝对状态，也不保证保存载体永不丢失。事件顺序、组成递推次数、内部黄金尺度及物理钟仍分别按命题147.5和151.3的条件使用；受限任务不能冒领命题149.4之外的全历史恢复。以上是普通数学证明和受限来源引用，不构成 Lean 核验、无界原生操作预算、未知量子态复制、物理空间维数或单一宇宙本体的证明。$\square$

## 追加锚（第152–159章以下为增补区）

## 160. 两原子的端点、顺序面积与线性记录

**假设 160.1（来源、取得与共同几何参照）。** 原生来源仍是钉版基础卷[定义1.1–1.4、2.1–2.4、3.1–3.3、7.1–7.2](https://github.com/the-omega-institute/trureturing/blob/d97800bf7e3690878d6d7c59c8784e719f44a5f7/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)的自由有序树

$$
T::=\alpha\mid\beta\mid\langle T,T\rangle.
$$

左右顺序、括号及实际来源不删除。令 $\operatorname{wd}(\alpha)=\alpha$、$\operatorname{wd}(\beta)=\beta$、$\operatorname{wd}(\langle s,t\rangle)=\operatorname{wd}(s)\operatorname{wd}(t)$，叶序从左到右读取。正词域为 $W_+=\{\alpha,\beta\}^*$；其中空词 $\epsilon$ 只扩展零贡献，不是第三种原生叶，非空词才有原树代表。

另给一个定向欧氏平面、共同原点 $O=(0,0)$、正交等长单位向量 $e_\alpha=(1,0)$、$e_\beta=(0,1)$，单位正方形的面积为一。这是新增的几何读出合同，不从原生树的数量解释推出。词的每片叶分别贡献这两个单位步；路径先读左叶再读右叶，不采用矩阵对状态的执行次序。端点记为 $\mathbf q=(u,v)$，而原来的数量记为 $N=2u+3v$，以免把两种读数混为同一个 $q$。

本章的数学映射可以对整个声明来源族定义。若用于实际观察，还须先实际取得所需叶类型和顺序，保存可精确访问的记录，并取得所用后续操作及共同来源、环境和参照的相容接缝。一个树或词在数学域中存在，不意味着已经执行、读取或保存。几何补弦、数学逆路径和连续曲线均不在这条取得合同中免费供应。

**定义 160.2（折线面积和摘要）。** 对任意有限实折线 $P=(\mathbf q_0,\ldots,\mathbf q_m)$，要求 $\mathbf q_0=0$；允许 $m=0$、重复顶点、自交和重走。定义

$$
\det((x,y),(x',y'))=xy'-yx',\qquad
A(P)=\frac12\sum_{j=1}^m\det(\mathbf q_{j-1},\mathbf q_j),
\qquad G(P)=(\mathbf q_m,A(P)).
$$

将终点以直线补到原点，该补弦的行列式贡献为 $\det(\mathbf q_m,0)/2=0$；它只用于面积计算，不表示实际执行一条逆门。闭合的简单多边形中，上式是按所给定向取正负的通常面积；一般折线中，它是以原点为公共顶点的有向三角形的代数和。前者可由三角剖分得到：每个三角形面积为两边行列式的一半，内部边以相反方向出现并消去，剩下边界和式。自交时仍以这个和式为定义，不把带重数的代数面积改称无重数区域的面积。

对正词或原树的叶路径记 $A(h)$，并记整数面积坐标 $D(h)=2A(h)$。一般实折线的 $D$ 不要求是整数；它和第154章的局部标量变化函数 $D(w)$ 属于不同接口，本章以下的 $D$ 专指两倍面积。

**定理 160.3（同端点的两条路径及叶对分解）。** $\alpha\beta$ 和 $\beta\alpha$ 的路径分别为

$$
0\to(1,0)\to(1,1),\qquad
0\to(0,1)\to(1,1).
$$

二者端点同为 $(1,1)$，数量同为五，面积分别为 $1/2$、$-1/2$，面积差为一。更一般地，若折线的逐步向量为 $\xi_1,\ldots,\xi_m$，则

$$
2A(P)=\sum_{1\le i<j\le m}\det(\xi_i,\xi_j).
$$

证明（160.3）。两条二步路径的唯一非零项分别是 $\det((1,0),(1,1))=1$ 和 $\det((0,1),(1,1))=-1$。把第一条路径接上第二条的反向路径，只作为比较面积的闭边界，恰围成单位正方形；终点相减为零不使这项顺序关系消失。一般式中 $\mathbf q_j=\mathbf q_{j-1}+\xi_j$，故

$$
\det(\mathbf q_{j-1},\mathbf q_j)
=\det(\mathbf q_{j-1},\xi_j)
=\sum_{i<j}\det(\xi_i,\xi_j).
$$

对 $j$ 求和即得结论，包括空和和重复步。$\square$

**定理 160.4（实际折线拼接的面积律与摘要结合性）。** 设 $P$ 从零到 $\mathbf q$，$Q$ 从零到 $\mathbf r$，其面积为 $A,B$。先走 $P$，再走平移了 $\mathbf q$ 的 $Q$，记为 $P\diamond Q$。其摘要为

$$
(\mathbf q,A)\star(\mathbf r,B)
=\left(\mathbf q+\mathbf r,
A+B+\frac12\det(\mathbf q,\mathbf r)\right).
$$

$\star$ 结合，单位为 $(0,0)$。这些等式对原树的配对读出成立，但不授权原生来源免费重括号。

证明（160.4）。写 $Q$ 顶点为 $\mathbf r_0=0,\ldots,\mathbf r_n=\mathbf r$。平移后每一段满足

$$
\begin{aligned}
\det(\mathbf q+\mathbf r_{j-1},\mathbf q+\mathbf r_j)
&=\det(\mathbf r_{j-1},\mathbf r_j)
+\det(\mathbf q,\mathbf r_j-\mathbf r_{j-1}).
\end{aligned}
$$

第二项求和望远镜成 $\det(\mathbf q,\mathbf r)$；加上 $P$ 的面积得拼接律。三个端点 $\mathbf q,\mathbf r,\mathbf s$ 的两种摘要括号都给端点 $\mathbf q+\mathbf r+\mathbf s$，面积的差只涉及

$$
\det(\mathbf q,\mathbf r)+\det(\mathbf q+\mathbf r,\mathbf s)
=\det(\mathbf r,\mathbf s)+\det(\mathbf q,\mathbf r+\mathbf s),
$$

由双线性逐项相等。零端点零面积的摘要代入即为单位。沿树叶序有 $G(\langle s,t\rangle)=G(s)\star G(t)$，于是不同括号可有同一个摘要；树的括号、构造和来源仍不同。$\square$

这条群律是经典 Heisenberg 形式。来源为 J. E. Nelson and R. F. Picken，[*Quantum Holonomies and the Heisenberg Group*，arXiv:1808.08812v1 (2018)](https://arxiv.org/abs/1808.08812)，[v1正文](https://arxiv.org/pdf/1808.08812v1)§3式(13)及§4。其指数坐标 $(a,b,c)$ 对应这里的 $(u,v,A)$，不是 $(u,v,D)$。§4把 $c$ 解释为路径与其弦之间的有向面积，并把群乘法解释为拼接。论文的量子讨论另有 $T^2$ 闭路的 $\mathbb R^2$ 覆盖折线、量子 $SL(2,\mathbb R)$ holonomy和常连接背景；本卷只复用经典群律和面积对应，不用那些条件推出 FIB 原生仪器或本卷指定的 $Q_8$ 提升。

**定理 160.5（同一来源族上的线性解码最少三分量）。** 令来源域含全部原树，或含其全部非空叶词。若记录 $R(h)\in\mathbb R^k$ 能经一个固定实线性映射 $B:\mathbb R^k\to\mathbb R^3$ 同时恢复 $(u(h),v(h),A(h))$，则 $k\ge3$。直接记录 $(u,v,A)$ 达到三；记这个任务的最小线性解码分量数为 $d_{\rm lin}=3$。

证明（160.5）。若实系数满足所有来源上 $\lambda u+\mu v+\nu A=0$，在 $\alpha$ 上得 $\lambda=0$，在 $\beta$ 上得 $\mu=0$，在 $\alpha\beta$ 的任一原树代表上得 $\nu/2=0$。所以三个输出函数线性独立，且三个对应输出向量张成 $\mathbb R^3$。它们都在 $B$ 的像中，故 $\operatorname{rank}B\ge3$；另一方面 $\operatorname{rank}B\le k$，下界成立。三分量记录用恒等解码给上界。$\square$

定理的条件是同一来源族和固定线性解码，不要求记录映射本身线性，也不约束任意非线性编码。原子追加将在第165章给仿射更新，拼接含双线性项；三分量不据此成为全线性自动机，更不是三个物理长度轴、全路径信息或全部任务的最小观察者。正词实际摘要像记为 $S_+=\{(u(h),v(h),D(h)):h\in W_+\}$；第166章给出它的完整奇偶、范围及可达性，而不是把所有整数 $D$ 都预设为正词可达。

## 161. 零端点纤维、逆原子格点与可积分扩展

**定义 161.1（四种路径域）。** 正词域仍为 $W_+$，只含正单位步。逆单位原子完成域另允许字母 $\alpha^{-1},\beta^{-1}$，分别取步 $-e_\alpha,-e_\beta$；词逆取反向次序并把每个步取负。一般折线域允许任意有限实顶点；其整数顶点子域只要求顶点在 $\mathbb Z^2$，不要求每一段是单位轴向步。连续域另取从零出发的连续分段 $C^1$ 路径，或连续有界变差路径；后者的面积用 Riemann–Stieltjes 积分定义。这四种合同没有由名称互相取得的执行权限。

在实摘要坐标中定义

$$
H_{\mathbb R}=\mathbb R^2\times\mathbb R,
\qquad \pi(\mathbf q,A)=\mathbf q,
$$

乘法采用定理160.4。逆单位原子产生的格点用两倍面积坐标表示，定义

$$
H_{\mathbb Z}=\{(u,v,D)\in\mathbb Z^3:D\equiv uv\pmod2\},
$$

$$
(u,v,D)\star(u',v',E)
=(u+u',v+v',D+E+uv'-vu').
$$

同一元素的实坐标是 $((u,v),D/2)$。这个 $H_{\mathbb Z}$ 不能误写为指数面积坐标中的无约束 $\mathbb Z^3$。

**定理 161.2（实群、中心及其全部折线像）。** $H_{\mathbb R}$ 是群，逆元为 $(-\mathbf q,-A)$。其中心和零端点纤维都为 $\{(0,A):A\in\mathbb R\}$，且

$$
(0,A)\star(0,B)=(0,A+B).
$$

所有实摘要均可由一般实折线实现。相同端点的两个摘要满足

$$
(\mathbf q,A)\star(\mathbf q,B)^{-1}=(0,A-B).
$$

证明（161.2）。结合律和单位已经证明，$\det(\mathbf q,-\mathbf q)=0$ 给所列左右逆。直接按拼接律计算群交换子，得到

$$
(\mathbf q,A)\star(\mathbf r,B)\star(\mathbf q,A)^{-1}
\star(\mathbf r,B)^{-1}=(0,\det(\mathbf q,\mathbf r)).
$$

因此零端点元素与所有元素交换；若一个元素中心化所有端点，则取 $\mathbf r=e_\alpha,e_\beta$，两个行列式都为零，强制 $\mathbf q=0$。零端点乘法由同一律得到。任意面积 $C$ 可取矩形折线

$$
0\to(1,0)\to(1,C)\to(0,C)\to0,
$$

其两倍面积为 $2C$，包括 $C<0$ 的反定向和 $C=0$ 的退化情形。先走这条闭路径，再走到任意 $\mathbf q$ 的直线，直线面积零且接缝行列式零，故实现 $(\mathbf q,C)$。最后的同端点差式再用 $\det(\mathbf q,-\mathbf q)=0$。$\square$

同端点中心差对应 Nelson–Picken 的§4式(19)，其中心及交换子对应§3式(14)和§4。这里的逆和闭路径是数学完成中的构造；即使比较对象都是两条已经取得的正历史，也不据此取得物理逆动作。

**定理 161.3（逆单位原子的精确生成格点）。** 逆单位原子域的全部摘要恰为 $H_{\mathbb Z}$。它是 $H_{\mathbb R}$ 的子群；零端点纤维恰为 $D\in2\mathbb Z$，即 $A\in\mathbb Z$。闭路径 $\alpha\beta\alpha^{-1}\beta^{-1}$、它的逆和空路径分别给 $(0,1)$、$(0,-1)$、$(0,0)$ 的实摘要。

证明（161.3）。对满足格点条件的两元素，乘积的两倍面积模二为

$$
uv+u'v'+uv'-vu'\equiv(u+u')(v+v')\pmod2.
$$

故乘法闭合。逆为 $(-u,-v,-D)$，且 $-D\equiv uv=(-u)(-v)\pmod2$；单位也在格点内。四个单位步的摘要都在格点，所以其生成像包含于 $H_{\mathbb Z}$。

记 $g_\alpha=(1,0,0)$、$g_\beta=(0,1,0)$。交换子 $z=g_\alpha\star g_\beta\star g_\alpha^{-1}\star g_\beta^{-1}$ 为 $(0,0,2)$。对任意整数 $u,v$，同轴整数次幂的面积零，故

$$
g_\beta^v\star g_\alpha^u=(u,v,-uv).
$$

给定任意格点 $(u,v,D)$，整数 $j=(D+uv)/2$ 存在；于是 $z^j\star g_\beta^v\star g_\alpha^u=(u,v,D)$。这以有限逆单位词实现全部格点，给反向包含。取 $u=v=0$ 即得纤维为偶数 $D$，并给三条所列路径。$\square$

Nelson–Picken §3在指数坐标中用“$a,b,c$ 全为整数”概括离散群，不能把这句简写直接当成本章生成格点：式(13)给 $(1,0,0)\star(0,1,0)=(1,1,1/2)$。本章的离散闭合性和完整生成像由上面的奇偶证明承担，不借这个简写省略格点条件。

**命题 161.4（正词与整数顶点折线的零纤维不同）。** $S_+$ 的零端点纤维只有空贡献 $(0,0,0)$；非空原树在零端点没有来源。一般整数顶点折线的摘要像却是全部 $(u,v,D)\in\mathbb Z^3$，零端点可有任意整数 $D$。因此它也不等于逆单位原子生成格点。

证明（161.4）。正词端点是两类叶数；非负整数 $u,v$ 同时为零迫使词无叶，面积为零。整数顶点的每个行列式为整数，故摘要的 $u,v,D$ 都是整数。反向，三角形

$$
0\to(1,0)\to(0,1)\to0
$$

给零端点且 $D=1$。正向或反向重复这个三角形可取得任意整数 $D$ 的零端点摘要；再接到任意整数端点的直线，面积不变。由此实现全部整数三元组。三角形含非轴向单位段；$D=1$ 的零端点不满足 $H_{\mathbb Z}$ 的偶性，正是两个合同不能合并的反例。$\square$

**定理 161.5（连续可积分域与圆的完整面积纤维）。** 对定义161.1的连续路径，定义

$$
A(q)=\frac12\int(x\,dy-y\,dx).
$$

拼接、平移及反向仍给定理160.4和161.2的摘要公式。圆路径

$$
q_R(t)=(R(\cos t-1),R\sin t),\qquad0\le t\le2\pi,\quad R\ge0
$$

从零回零，面积为 $\pi R^2$，反向为 $-\pi R^2$；$R=0$ 退化为常路径。允许这些路径时，零端点面积纤维覆盖全部实数。

证明（161.5）。分段 $C^1$ 时按段积分；连续有界变差时，两个坐标都有界变差且被积坐标连续，故两项 Riemann–Stieltjes 积分存在。折线一段的积分等于其端点行列式，所以定义延伸原来的面积。平移 $Q$ 到 $(u,v)$ 后，新增积分为

$$
\frac12\int(u\,dy-v\,dx)
=\frac12(u r_y-v r_x)=\frac12\det(\mathbf q,\mathbf r).
$$

积分对先后路径可加，给拼接律；反向积分变号，若再把起点平移回零，平移项是 $\det(-\mathbf q,-\mathbf q)/2=0$，故逆摘要为 $(-\mathbf q,-A)$。上述积分恒等式在两个域都由有限分割求和及极限保持。

圆的微分给 $x\,dy-y\,dx=R^2(1-\cos t)dt$，故半积分为 $\pi R^2$。反向的积分变号，零半径的积分零。任意实数 $C\ne0$ 取 $R=\sqrt{|C|/\pi}$，并按其符号选方向，即得面积 $C$；$C=0$ 由常路径实现。$\square$

任意连续路径不自动具有这个积分，故本章没有使用无积分合同的“所有连续路径”。连续执行、半径标定、精度和保持资源也没有从圆例取得。某端点观察把多个面积关系都投影到零，与原点作为参照固定相容；是否需要区别它们，由实际未来任务是否读面积或相应关系决定。只读端点且只用端点闭合的操作时可商去面积；一旦未来输出要精确面积，命题161.2中的同端点不同面积已反驳这种合并的充分性。

## 162. 原生替换的内部折线修正与精确闭合

**定义 162.1（树替换和线性弦运输）。** 原生 $\rho$ 仍取基础卷定义1.1：$\alpha\mapsto\beta$、$\beta\mapsto\langle\beta,\alpha\rangle$，并保持有序配对。叶序替换因此为 $\alpha\mapsto\beta$、$\beta\mapsto\beta\alpha$；这个对应由第156.3条的结构归纳复用，包括来源括号的保留。端点更新是

$$
\mathbf q'=M\mathbf q,\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad \det M=-1.
$$

“线性弦运输”指将旧路径的每个顶点直接乘 $M$；“原生折线运输”则按替换后的真实叶序作单位步。二者有相同端点，但后一种还含每片旧 $\beta$ 的内部折线。

**定理 162.2（全部来源的 FIB 面积递推）。** 对每棵原树、每个正叶词及空贡献扩展，端点面积摘要满足

$$
(u,v,A)\longmapsto(v,u+v,-A-v/2),
$$

$$
F(u,v,D)=(v,u+v,-D-v).
$$

这不是只有某个迭代初树上的公式。它保持 $S_+$ 的数学可达像；在该像中仍有 $D\equiv uv\pmod2$。

证明（162.2）。对任意两个平面向量，直接展开二阶行列式得到 $\det(Mp,Mq)=\det(M)\det(p,q)=-\det(p,q)$。把旧路径全部顶点乘 $M$，面积先变为 $-A$。一片旧 $\alpha$ 的直步经 $M$ 是 $e_\beta$，与替换完全相同，没有内部修正。一片旧 $\beta$ 的步经 $M$ 是 $(1,1)$ 的直线，但替换要求先 $e_\beta$ 再 $e_\alpha$。

在任意平移起点 $p$，设二步为 $a,b$。二步折线与同端点直线的两倍面积差为

$$
\begin{aligned}
&\det(p,p+a)+\det(p+a,p+a+b)-\det(p,p+a+b)\\
&=\det(p,a)+\det(p,b)+\det(a,b)-\det(p,a+b)
=\det(a,b).
\end{aligned}
$$

取 $a=e_\beta,b=e_\alpha$ 得 $-1$，即每片旧 $\beta$ 补 $-1/2$。这项与所在位置无关，所有 $v$ 片贡献相加，得 $A'=-A-v/2$，并得 $D'=-D-v$。端点计数给 $(v,u+v)$。空贡献两边均零；全部原树的叶路径已经被逐叶替换覆盖，不需要改其括号。

正词经替换仍为正词，所以更新后的摘要仍在同一个像内。由定理160.3，每个异型叶对贡献 $1$ 或 $-1$，同型对贡献零；异型对共 $uv$ 个，故 $D\equiv uv\pmod2$。代入递推又有

$$
D'\equiv uv+v\equiv v(u+v)=u'v'\pmod2,
$$

使用 $v^2\equiv v$，可见格点奇偶也直接保持。这里可达只指声明来源域中的数学实现，不声称域中每棵树已实际执行。$\square$

**定理 162.3（校准量反号与两步不变）。** 定义面积校准量

$$
J_{\rm area}=D+v-u.
$$

则 $J_{\rm area}(\rho h)=-J_{\rm area}(h)$，从而两步保持。两步完整摘要为

$$
F^2(u,v,D)=(u+v,u+2v,D-u),
$$

空摘要固定。

证明（162.3）。直接代入定理162.2，

$$
J'_{\rm area}=(-D-v)+(u+v)-v=-D+u-v=-J_{\rm area}.
$$

再施一次给 $J''_{\rm area}=J_{\rm area}$。第二次面积坐标是 $-(-D-v)-(u+v)=D-u$，端点是 $M^2(u,v)$，给所列三元组。零三元组代入固定。$\square$

**命题 162.4（完成群上的代数扩展及其权限）。** 同一公式 $F$ 在 $H_{\mathbb R}$ 的两倍面积坐标中是群自同构，并限制为 $H_{\mathbb Z}$ 的自同构，逆式为

$$
F^{-1}(U,V,T)=(V-U,U,-T-U).
$$

它在逆单位词上对应 $\alpha^{-1}\mapsto\beta^{-1}$、$\beta^{-1}\mapsto\alpha^{-1}\beta^{-1}$ 的代数延伸，不把原生正树替换改成可自由逆执行的操作。

证明（162.4）。乘法的中心接缝为 $\det(\mathbf q,\mathbf r)$，$M$ 将其反号；$F$ 的额外中心项是线性函数 $-v$。因此在乘积上作 $F$ 的中心坐标为

$$
-(D+E+\det(\mathbf q,\mathbf r))-(v+v'),
$$

而两个 $F$ 像相乘的中心坐标为

$$
(-D-v)+(-E-v')+\det(M\mathbf q,M\mathbf r),
$$

二者相同，端点也相同。解三个更新等式给所列逆，所以在实群可逆。整数坐标和奇偶经 $F$ 保持；逆式中由 $T\equiv UV$ 得

$$
-T-U\equiv UV+U\equiv(V-U)U\pmod2,
$$

故逆也保格点。生成元的像为 $g_\beta$ 和 $g_\beta\star g_\alpha$；群同态将逆元映成像的逆，即给两条逆字母替换。$\square$

这个逆式不保证保持正词像，例如 $F^{-1}(1,0,0)=(-1,1,-1)$。线性 $M$ 运输与原生折线运输的区别已经在一片 $\beta$ 上可见：前者端点 $(1,1)$、面积零，后者同端点、面积 $-1/2$。知道端点运输并不能省略内部来源路径。组成增长、面积反号或校准量反号也不等于时间倒流、知识减少或熵增；事件和档案仍依已发生顺序保持。

## 163. 五模式的选定来源代表与合法接缝

**定义 163.1（来源代表的固定选择）。** 令 $\gamma=\langle\beta,\alpha\rangle$，另为五个局部模式选定贡献代表

$$
\mathrm{null}\leftrightarrow\epsilon,\quad
[2]\leftrightarrow\alpha,\quad
[3]\leftrightarrow\beta,\quad
[5]\leftrightarrow\gamma,\quad
[25]\leftrightarrow\langle\gamma,\alpha\rangle.
$$

这是前卷第103章来源代表的同一个选择。模式组成由基础卷定义2.1和7.1给出；面积则依本章代表及共同几何参照选择。$\epsilon$ 只给零贡献，不把实际读取 $\mathrm{null}$ 改为未读，不在原树语法新增空叶，也不宣称模式标签唯一指定一棵树。

**命题 163.2（代表的端点、数量和面积表）。** 所选代表有以下读出。

| 模式 | 叶序 | $(u,v)$ | $N=2u+3v$ | $D=2A$ |
| --- | --- | --- | --- | --- |
| $\mathrm{null}$ | $\epsilon$ | $(0,0)$ | $0$ | $0$ |
| $[2]$ | $\alpha$ | $(1,0)$ | $2$ | $0$ |
| $[3]$ | $\beta$ | $(0,1)$ | $3$ | $0$ |
| $[5]$ | $\beta\alpha$ | $(1,1)$ | $5$ | $-1$ |
| $[25]$ | $\beta\alpha\alpha$ | $(2,1)$ | $7$ | $-2$ |

同组成 $(2,1)$ 的自由来源叶序 $\beta\alpha\alpha$、$\alpha\beta\alpha$、$\alpha\alpha\beta$ 分别有 $D=-2,0,2$。

证明（163.2）。空贡献和单步没有非零行列式项。$\beta\alpha$ 的异型叶对给 $-1$；再追加一片 $\alpha$ 又与原有一片 $\beta$ 给 $-1$，所以最后一行为 $-2$。$\alpha\beta\alpha$ 的两个异型对分别给 $+1,-1$；$\alpha\alpha\beta$ 的两个异型对都给 $+1$，得到其余两值。组成按叶数，数量按 $2u+3v$，逐行即得表。每条非空自由词都能以左嵌套配对构成原树，故三条确有自由来源；它们不因此成为三种已经供应的五模式窗口操作。$\square$

**命题 163.3（组成、面积及高到低接缝的独立接口）。** 面积表不替代第157章的高到低守卫。新窗口低到高三位为 $(b_0,b_1,b_2)$ 时，旧接缝 $s$ 的守卫为 $s b_2=0$，新接缝为 $b_0$。特别地，$[3]$ 输出接缝零，而 $[25]$ 输出接缝一；再接 $[5]$，前者合法而后者非法。单次真实 $\mathrm{null}$ 使组成 $x\mapsto M^3x$ 且新接缝零，一般不是恒等。

证明（163.3）。复用定义157.1的窗口表：$[3]=010$、$[25]=101$ 的最低位分别是零、一，故输出接缝如列；$[5]=001$ 的最高位一，守卫分别为 $0\cdot1=0$ 和 $1\cdot1\ne0$。这个判据没有使用面积或酉相位。$\mathrm{null}=000$ 对所有旧接缝允许，并给新接缝零、贡献零；组成仍按固定 $M^3x+d_{\mathrm{null}}=M^3x$ 更新。定理157.2已经给非零组成的实际变化例，不把零贡献重做成恒等解释。$\square$

在定义163.1的完整五模式集合及固定代表上，也可以查表得到局部面积；这只是新增的选定来源接口。若只有宏事件 $[25]$ 及组成 $(2,1)$，未声明或未取得代表的内部叶序，则命题163.2的三个来源已证明面积不能由组成独自恢复。三个词并非三种原生必有窗口返回，所选 $[25]$ 也没有脱离代表的永久唯一相位。数量、组成、面积、实际守卫及事件字段各按其合同使用，不能以一份表取消来源和合法接缝。

## 164. 同组成的面积差与指定四元数相位

**假设 164.1（固定提升与两种次序）。** 本章复用[前卷固定版本的第101–103、106–107章](https://github.com/the-omega-institute/trureturing/blob/b9b4a62b69908c14f2b3ceb07204620db61aa862/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)：在 $\mathbb C^2$ 上取 Pauli 矩阵 $X,Y$，并固定

$$
a=U_\alpha=-iX,\qquad b=U_\beta=-iY,
\qquad U_{\langle s,t\rangle}=U_sU_t.
$$

于是 $a^2=b^2=-I$、$ab=-ba$。空贡献的矩阵读出为 $I$，树读出是有序叶矩阵乘积。对列状态 $U_sU_t$ 的右因子先执行；本卷路径仍按左到右叶序先走 $s$ 再走 $t$。这是两个已分别指定的读出次序，不将路径的时间顺序当作矩阵的实际执行顺序。

这项量子表示是额外数学合同。用于真实相干比较时，还须已取得固定相位的共同实现、控制及参照，并保留将再次接入的环境和来源接缝，条件仍为前卷第107–110章。平面图或 Nelson–Picken 的量子连接背景不供应这里的 $a,b$ 或比较仪器。

**定义 164.2（异型叶对计数）。** 对正叶词 $h$，令 $K(h)$ 为所有异型叶对中 $\alpha$ 位于 $\beta$ 之前的对数。全部异型对数为 $uv$，故 $0\le K\le uv$。本章的 $K$ 是整数计数，不是第160章的线性解码分量数 $d_{\rm lin}$。

**定理 164.3（面积与酉正常形的精确对应）。** 对全部正词和全部原树，有

$$
A(h)=K(h)-\frac{uv}{2},\qquad D(h)=2K(h)-uv,
$$

$$
U_h=(-1)^{K(h)}b^va^u.
$$

空词也满足这些式。相同组成的两来源 $h,h'$ 因而满足

$$
U_h=(-1)^{K(h)-K(h')}U_{h'}
=(-1)^{A(h)-A(h')}U_{h'},
\qquad A(h)-A(h')\in\mathbb Z.
$$

证明（164.3）。定理160.3把两倍面积分成所有叶对的行列式。两个同型单位向量的行列式零；$\alpha$ 先于 $\beta$ 时为一，反向为负一。因此

$$
D=K-(uv-K)=2K-uv,
$$

得到面积式。为整理矩阵词，把所有 $b$ 稳定地移到所有 $a$ 左边，只交换相邻的异型 $ab$。交换一次给 $ab=-ba$ 的一个负号，并使尚未整理的 $\alpha$ 在 $\beta$ 前的叶对数恰减一；其余叶对次序不变。若仍有这种叶对，则至少有一处相邻 $ab$：从一片在某 $b$ 前的 $a$ 向右走，首个 $b$ 的左邻就是 $a$。因此经过恰 $K$ 次交换终止为 $b^va^u$，得到酉式。不将平方产生的中心符号漏掉：它们已经留在整数次幂 $b^v,a^u$ 中；若再约化指数，分别还需 $(-1)^{\lfloor v/2\rfloor+\lfloor u/2\rfloor}$。

相同 $u,v$ 时两正常形的整数次幂完全相同，面积式的 $uv/2$ 消去，故面积差等于整数 $K-K'$，再比较符号得所列关系。空词时三个计数均零，正常形为 $I$。$\square$

**命题 164.4（固定端点的相位奇偶及同步推进）。** 固定已知端点时，上述相对符号由 $K\bmod2$ 决定，等价于在该端点条件下保留 $D\bmod4$；$D\bmod2$ 本身不足够。同步 $\rho$ 推进两个同组成来源，其面积差反号，整数奇偶及相对量子符号保持。

证明（164.4）。在所知 $u,v$ 下，$K=(D+uv)/2$ 是整数；其模二值恰由 $D+uv$ 模四决定。反向，$K\bmod2$ 给 $D\equiv2K-uv\pmod4$。而所有同组成正词都满足 $D\equiv uv\pmod2$，所以模二已经固定；例如 $\alpha\beta$ 与 $\beta\alpha$ 的 $D=1,-1$ 都是奇数，酉却相反。

定理162.2中两个来源有同一个 $v$，故

$$
A(\rho h)-A(\rho h')=-\bigl(A(h)-A(h')\bigr).
$$

端点在同一个 $M$ 下仍相同，归纳给第 $n$ 步差为 $(-1)^n(A(h)-A(h'))$。整数取负不改变奇偶，再用定理164.3得到持续相对符号。这是对前卷第106章持续相位结论的面积表达，不是一条另由几何推出的新量子规律。$\square$

一条路径的 $A$ 可以是半整数，不能把其单独相位一般写成只有正负值的 $(-1)^A$；本章这个幂只对同组成的整数面积差使用。普通目标通道也不读出这项中心符号：对任意密度算子 $\varrho$，

$$
(-U)\varrho(-U)^*=U\varrho U^*.
$$

在前卷定义107.1已经实际供应的共同控制门上，$(U,U)$ 和 $(U,-U)$ 两支才分别把 $|+\rangle\otimes\psi$ 送为 $|+\rangle\otimes U\psi$、$|-\rangle\otimes U\psi$，再由所供控制 $X$ 读取区别；这由展开两支直接得到。面积账不提供该共同实现，也不抹去不同环境导致的可见度条件。仅需固定端点相位奇偶的任务可以只保留相应奇偶，不被精确面积任务的容量界迫使保存全部 $A$。

## 165. 实际逐叶取得、整数记录与继续使用

**假设 165.1（可访问的记录及合法菜单）。** 观察者已逐事件实际取得当前来源的每片叶类型及左到右顺序；不是只有总数、宏模式或未执行分支。初记录为 $(u,v,D)=(0,0,0)$，随后整数记录能够被准确更新、保持并再次访问。菜单先限于自由叶词的实际追加、已取得且有共同接缝的路径拼接，以及已供的指定 $\rho$ 替换；若另纳入窗口事件，就保持第157章的窗口守卫、层数和事件来源。精确整数记录是一项资源合同，其读写、位长、保持和取得费用不由下面的公式省略。

自由词语法的追加、固定词拼接及指定替换有全域数学定义，不设五模式守卫。若实际动作的合法性或选择还依赖来源、环境或控制字段，则这些字段仍须另存并核对，或另证其在摘要纤维上不变；三元组公式只负责端点—面积更新，不自动决定这些权限。

**定理 165.2（实际原子追加的闭合记录）。** 每次取得的下一片叶给更新

$$
\alpha:(u,v,D)\longmapsto(u+1,v,D-v),
\qquad
\beta:(u,v,D)\longmapsto(u,v+1,D+u).
$$

按假设165.1逐次执行这些数学更新，记录在每个有限前缀都等于其端点和两倍面积。

证明（165.2）。单步摘要分别为 $(1,0,0)$ 和 $(0,1,0)$。定理160.4的两倍面积接缝为 $\det((u,v),(1,0))=-v$ 和 $\det((u,v),(0,1))=u$，给两条更新。空前缀记录正确；若当前前缀记录正确，实际新叶按这条拼接律给新路径的正确端点及面积，归纳覆盖全部已取得有限前缀。公式只用当前保留的整数及实际下一叶，不查询未知来源或未执行分支。$\square$

两条更新对三元组分别是仿射映射；给定右侧已取得摘要 $(r,s,E)$，拼接为

$$
(u,v,D)\longmapsto(u+r,v+s,D+E+us-vr).
$$

同时把左右两摘要看成变量时，这里的接缝是双线性项。因此 $d_{\rm lin}=3$ 的解码边界不宣称整套可变拼接是三维全线性状态机。

**定理 165.3（固定端点—面积任务的继续充分性）。** 在假设165.1已实际供给的自由叶菜单内，若输出只依赖 $(u,v,D)$，每次拼接的另一路径摘要也已取得且相容，$\rho$ 按定义162.1执行，则同摘要来源在任意共同合法有限后续中保持同摘要和同输出。这个摘要只对上述输出及更新任务充分，仍忘来源括号和部分叶顺序；动作权限继续按假设165.1的保留字段或纤维证明检验。

证明（165.3）。原子追加由定理165.2下降到三元组；拼接由定理160.4下降；左拼接同理用同一个 $\star$ 公式；$\rho$ 由定理162.2下降。每次更新对相同旧三元组和同一个已供动作、另一摘要给相同结果。空后续同输出，按后续长度归纳得到全部共同有限后续。这验证了基础卷定义3.2的读出及更新纤维条件；实际合法性还按假设165.1的权限字段检验，不能越过所给的动作范围或合法域。

非完整性有两类具体来源。括号不同的 $\langle\langle\alpha,\alpha\rangle,\beta\rangle$ 和 $\langle\alpha,\langle\alpha,\beta\rangle\rangle$ 有相同叶词、相同摘要，却仍是不同原树；前卷命题103.2的其他读出已区别其来源。顺序不同的 $\alpha\beta\beta\alpha$ 和 $\beta\alpha\alpha\beta$ 都有 $(u,v)=(2,2)$、$K=2$，遂由定理164.3都给 $D=0$，但叶序不同。因此需要完整树、全事件字段或其他顺序响应的未来任务必须另存所需记录，不能把本章闭合误读为全来源恢复。$\square$

**命题 165.4（窗口面积更新所需的实际路径提升）。** 仅有第157章的 $x'=M^3x+d_\sigma$ 及窗口守卫，不决定内部面积。若另外已供并实际取得一个路径提升，明确要求旧来源先按 $\rho^3$ 运输，再在其后拼接定义163.1的共同代表，则设 $x=(u,v)$、代表摘要为 $(r,s,E)$，该提升的两倍面积更新恰为

$$
\begin{aligned}
U&=u+2v,\qquad V=2u+3v,\\
D_{\rm new}&=-D-2v+E+Us-Vr.
\end{aligned}
$$

合法性仍由窗口旧接缝和模式判定；未供这条提升时不把此式当作原窗口读者的面积律。

证明（165.4）。依定理162.2三次更新，前两次中心为 $-D-v$、$D-u$，第三次为 $-(D-u)-(u+2v)=-D-2v$；端点为 $M^3(u,v)=(U,V)$。在已经供给的后拼接合同内，再按两倍面积拼接律加 $E+Us-Vr$，得式。这个提升的端点确为 $M^3x+(r,s)$，所以与原数值更新相容。

反向不能从端点更新恢复提升：命题163.2的三个 $(2,1)$ 代表有相同端点和数量，却给不同内部 $E$；即使宏模式固定，未声明其来源代表就没有唯一面积。窗口的非法边仍进入原有错误态，不因平面上存在相同端点的自由词就变合法。$\mathrm{null}$ 的代表空贡献只在这条额外提升中给 $E=r=s=0$；窗口事件仍运输旧来源、更新层数与接缝，并保留已发生读取。$\square$

**约定 165.5（第158章共同域的准确类型）。** 本章接入模式函数时，域明确为完整五模式集合

$$
L=\{\mathrm{null},[2],[3],[5],[25]\},\qquad \mathcal A=\mathbb R^L
$$

及第158.1–158.2条的逐点函数代数。“整域”在那里的标题指全部共同模式域，不作环论无零因子的整环断言。事实上 $e_2,e_3$ 都非零，分别在模式 $[2],[3]$ 取一，但 $e_2e_3=0$，所以 $\mathbb R^L$ 有零因子。该函数接口保存局部模式响应；若实际像只是 $L$ 的子集，就限制到该像，不能假定全部模式已经发生，更不能由模式函数自动取得内部叶序或完整事件码。

## 166. 固定端点的完整面积像与额外容量

**定义 166.1（同组成的完整自由来源族）。** 固定非负整数 $u,v$，令 $W_{u,v}$ 为恰含 $u$ 片 $\alpha$、$v$ 片 $\beta$ 的全部正词。只讨论原生非空树时要求 $u+v>0$；空贡献扩展单列 $W_{0,0}=\{\epsilon\}$。这里的“全部”指自由有序树允许的叶序族，不是所有词都已实际取得，也不是所有词都是合法五模式事件串。

**定理 166.2（所有计数均可达及正词全像）。** $W_{u,v}$ 中的 $K$ 恰取所有整数 $0,1,\ldots,uv$。因此恰有 $uv+1$ 个面积值，分别为

$$
A=-\frac{uv}{2},-\frac{uv}{2}+1,\ldots,\frac{uv}{2},
\qquad D=-uv,-uv+2,\ldots,uv.
$$

定义160.5末段的正词摘要全像恰为

$$
S_+=\{(u,v,D):u,v\in\mathbb N,\ D\in\mathbb Z,
\ |D|\le uv,\ D\equiv uv\pmod2\}.
$$

非空原树的像从中排除 $(0,0,0)$；正词零端点纤维、逆单位原子格点零纤维和实群零纤维因而分别是单点、整数面积和实数面积。

证明（166.2）。$K$ 数异型对，先有 $0\le K\le uv$。对总长度 $u+v$ 归纳证明没有遗漏的整数。若 $u=0$ 或 $v=0$，词只有一种叶型，每词都给 $K=0$，所需区间也是单点，包含空词情形。

若 $u,v\ge1$，最后一片叶只能是 $\alpha$ 或 $\beta$。最后是 $\alpha$ 时，它不在任何 $\beta$ 前，不添计数；按归纳，前缀的可达 $K$ 区间为

$$
I_\alpha=\{0,\ldots,(u-1)v\}.
$$

最后是 $\beta$ 时，它在全部 $u$ 片 $\alpha$ 后，每片都添一个计数；前缀的区间 $0,\ldots,u(v-1)$ 加 $u$，给

$$
I_\beta=\{u,\ldots,uv\}.
$$

两个整数区间的接合无缺口，因为

$$
(u-1)v+1-u=(u-1)(v-1)\ge0.
$$

它们从零覆盖到 $uv$，即完成归纳。这个证明也给明确构造：给定目标整数 $j$，若 $j\le(u-1)v$，构造 $(u-1,v,j)$ 的前缀再加 $\alpha$；否则构造 $(u,v-1,j-u)$ 的前缀再加 $\beta$。后一分支由接合不等式保证 $j\ge u$，且 $j-u\le u(v-1)$。到某个叶数零时只剩唯一同型词，因此有限递归必终止。

定理164.3将 $K$ 一一送到 $D=2K-uv$，得面积列表、个数和奇偶范围。反向，对满足所列范围及奇偶的三元组，$j=(D+uv)/2$ 是 $0\le j\le uv$ 的整数，刚才的构造给实现词；非空词以左嵌套配对给原树。原树无零叶，空扩展是唯一零端点，另外两种纤维由定理161.3、161.2已分别证明。$\square$

**定理 166.3（端点已知时的额外精确记录容量）。** 假定所需来源族确为全部 $W_{u,v}$，端点 $u,v$ 已知且保持可访问；一个记录系统要在每条来源上精确恢复面积，至少有 $uv+1$ 个可区分的额外记录状态。恰 $uv+1$ 个状态可以达到这个界；若用固定长度二进制记录，最小位数为

$$
b_{\rm area}(u,v)=\left\lceil\log_2(uv+1)\right\rceil.
$$

当 $u=0$ 或 $v=0$ 时为零位；空扩展也为零位。

证明（166.3）。给记录映射 $R:W_{u,v}\to C$ 和解码 $f:C\to\mathbb R$，要求 $f(R(h))=A(h)$。定理166.2为每个 $j=0,\ldots,uv$ 提供一个面积不同的词 $h_j$。若两记录值相同，解码返回同一面积，与 $A(h_j)\ne A(h_{j'})$ 矛盾，所以 $|C|\ge uv+1$。

取 $C=\{0,\ldots,uv\}$，记录 $R(h)=K(h)$，用已知端点解码 $A=K-uv/2$，即精确达到上界。计数可以在假设165.1下随实际叶取得：追加 $\alpha$ 不添 $K$，追加 $\beta$ 添旧 $u$；这是异型对定义的直接分解，也可由定理165.2及 $K=(D+uv)/2$ 得到。每个编号都有定理166.2的实现词，因此上界没有空编号。

固定 $b$ 位有 $2^b$ 个码，必要条件为 $2^b\ge uv+1$；满足这个条件时把编号 $0,\ldots,uv$ 作普通固定长二进制编码即可。最小这样的整数 $b$ 正是所列上取整；$uv=0$ 时只有一种面积，空记录已经够用。$\square$

这个容量只计在端点已知且可访问条件下新增的精确面积区别。不计端点本身、括号、档案、控制、环境或仪器的资源，也不是每一条词的最短描述长度、概率熵或全来源容量。全部叶词有 $\binom{u+v}{u}$ 种：选择 $u+v$ 个位置中放 $\alpha$ 的 $u$ 个位置，与叶词一一对应；面积还会合并不同叶词，如定理165.3的两词。完整树还另有括号。若实际来源只占受限子族，则应数该族的面积像，不能对它冒领全族容量下界；若端点没有保存，$K$ 单独也不一般恢复 $A$。

**命题 166.4（规模容量和单轨迹面积的区别）。** 全族的面积种数可随端点规模无界增长；具体追加或 FIB 轨迹的有向面积却不必单调，因此这个种数不定义时间箭头或物理熵。

证明（166.4）。取 $u=v=n$，面积种数为 $n^2+1$，随 $n$ 无界。具体来源 $\beta\alpha\beta$ 的三个非空前缀面积依次为 $0,-1/2,0$，已同时有下降和上升。又 $\alpha$ 的连续 FIB 叶词为 $\alpha,\beta,\beta\alpha,\beta\alpha\beta$，面积为 $0,0,-1/2,0$，同样不单调。这些数直接由定理165.2或162.2取得；没有假设随机律，不能据此命名概率熵。实际事件档案是否追加仍由事件合同判断，不由面积增减判断。$\square$

## 167. 共同尺度、定向与端点—面积任务的整合

**定理 167.1（线性平面变换与退化情形）。** 对任意实线性平面映射 $L$，有限折线及第161章的可积分连续路径都有

$$
A(LP)=\det(L)A(P),\qquad
T_L(\mathbf q,A)=(L\mathbf q,\det(L)A).
$$

$T_L$ 是 $H_{\mathbb R}$ 的群同态；当且仅当 $L$ 可逆时，它是自同构。平面共同缩放 $L=sI$ 给

$$
(u,v,A)\longmapsto(su,sv,s^2A),\qquad s\in\mathbb R.
$$

$s=0$ 将全部摘要送到零，是退化同态；$s\ne0$ 在实群上可逆。一般缩放和一般 $L$ 不自动保持整数单位原子摘要像。

证明（167.1）。写 $L=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)$，对向量 $p,q$ 展开得

$$
\det(Lp,Lq)=(ad-bc)\det(p,q).
$$

有限折线逐段代入面积和式即得。分段 $C^1$ 或连续有界变差路径经线性变换仍属于同一积分域；将 $Lq$ 及 $d(Lq)=L\,dq$ 代入积分，或在 Riemann–Stieltjes 分割和中用同一行列式恒等式，再取极限，得到连续公式。

由 $\det(L\mathbf q,L\mathbf r)=\det(L)\det(\mathbf q,\mathbf r)$，$T_L$ 的乘积中心项与先乘再变换完全一致，端点项也一致，故是同态。$L$ 可逆时 $T_{L^{-1}}$ 是其逆，因为 $\det(L^{-1})\det L=1$。若 $L$ 奇异，则 $\det L=0$，所有 $(0,A)$ 都被送到同一零摘要，已经不单射，不能是自同构；其像端点也只能在 $\operatorname{im}L$ 中。

缩放的行列式为 $s^2$，得到所列式和零缩放的退化。例 $s=1/2$ 将单位 $\alpha$ 的端点变成 $(1/2,0)$，既不在 $S_+$ 也不在 $H_{\mathbb Z}$。即使 $L$ 为整数可逆矩阵，实群同态也不必保持本卷格点：取 $L=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)$，它把 $(0,1,0)$ 送为 $(1,1,0)$ 的两倍面积坐标，违反 $D\equiv uv\pmod2$。因此限制到特定原子像须另验闭合；实群可逆性没有替代这项检查。$\square$

**命题 167.2（交换镜像及共同参照）。** 令 $J(x,y)=(y,x)$，则 $\det J=-1$，摘要变为 $(J\mathbf q,-A)$。它与交换两种正叶标签的路径读出相容，并保持相应正词像。这个反号不是时间倒流或知识减少。被动换观察者坐标时，原点、定向、单位、读出及合法接口须共同运输，不能另置一个未声明的绝对尺。

证明（167.2）。定理167.1给面积反号。交换叶标签使每个单位步经 $J$，所以全路径恰是 $JP$；端点交换，$D$ 取负。若原 $D\equiv uv$ 且 $|D|\le uv$，交换后仍满足 $-D\equiv vu$ 和同一个范围，或直接以交换后的正词给可达性。这个 $J$ 与面积校准量 $J_{\rm area}$ 是不同对象。

若只是用可逆 $L$ 重表达同一相对几何，则新坐标 $(\mathbf q',A')$ 由 $T_L$ 给出；原任务的读出同步改为先用 $T_{L^{-1}}$ 恢复再读。对任何摘要读出 $o$，定义 $o'=o\circ T_{L^{-1}}$，立即有 $o'(T_LG)=o(G)$。原数量行向量也变为 $\ell'=\ell L^{-1}$，不是把相同数字 $\ell$ 强贴在不同量具上。操作及合法域同样按共同变换运输，复合中同一接口的逆变换消去，所以响应保持。原点改选时先将同一来源相对于所选参照表达，再共同变换；不能只移其中一路来源而保持其他读数及权限不动。

缩放中的长度按 $|s|$ 变，面积按 $s^2$ 变，显示面积坐标与长度不同型。负 $s$ 同时反向两根轴，行列式仍正，不把它误称镜像反定向。镜像改变表示的定向符号，没有倒置已发生事件序列；档案仍可按原顺序追加。$\square$

缩放、交换镜像的经典 Heisenberg 背景对应 Nelson–Picken §3.1；该处 dilation 取 $r>0$。本章 $s<0$、$s=0$ 及一般 $L$ 的范围由定理167.1自己的证明给出，零值只称退化同态，不归入文献的自同构。无论用主动几何变换还是被动换坐标，都须区别数学可表达、实际可执行与可认证精度。

**假设 167.3（整合所需的取得、保留和未来合同）。** 首先实际取得相应来源读数及允许操作，保持任务所需的准确可访问记录，并核对共同来源、环境、控制和接缝；这是假设160.1、165.1和前卷第107–110章的条件，不是端点—面积公式的结论。然后固定以下任务范围：原树或正词的几何读出依共同正交单位和定向；自由叶继续菜单采用第165章；五模式继续另保第157章合法窗口合同，若要窗口面积则另外供命题165.4的实际路径提升；逆原子、一般折线及连续积分均只在第161章各自的扩展域使用。涉及量子符号时固定假设164.1的提升；涉及真实相干区别时再供其中的实际比较合同。

**定理 167.4（端点—面积的条件整合与准确边界）。** 在假设167.3各项对应的域及权限内，成立下列结果。

（1）两原子读出有两个端点分量和一个顺序面积分量；同端点可保留非零路径关系。对完整自由来源族、固定实线性解码同时恢复 $u,v,A$，恰需 $d_{\rm lin}=3$，不宣称全线性自动机或物理空间维数。

（2）几何拼接按 $\star$ 精确结合；原生折线替换闭合为 $F(u,v,D)=(v,u+v,-D-v)$，校准量逐次反号。原生括号和实际操作守卫不因摘要结合而删除。正词完整像是 $S_+$，逆单位原子完整像是 $H_{\mathbb Z}$，实折线与已给连续域的摘要像是 $H_{\mathbb R}$；三者的零端点面积分别为零、整数和实数。

（3）固定端点的正词面积差是整数，指定 $Q_8$ 正常形中的相对符号由该差的奇偶决定；固定端点相位奇偶用 $K\bmod2$，等价于所知端点下的 $D\bmod4$。两个目标通道相同不供应相干中心相位的读取。

（4）实际逐叶记录按两条仿射追加式正确继续；只在第165章已供的任务内充分。端点已经准确保留时，完整 $W_{u,v}$ 的额外精确面积容量恰为 $uv+1$ 个状态；受限实际来源像、仅相位任务、全词及完整事件另按自己的合同计量。五模式函数使用的是完整集合 $L$ 及有零因子的 $\mathbb R^L$，不是环论整环，更不是全来源档案。

（5）面积在共同线性平面变换下按 $\det L$ 运输、缩放下按 $s^2$ 运输；可逆 $L$ 才给实群自同构，奇异 $L$ 和 $s=0$ 退化。改变定向、返回零端点或面积下降，都不撤销已取得的事件档案。

证明（167.4）。第一项应用定理160.3和160.5，后者的下界只比较同一自由来源族中的固定线性解码。第二项应用定理160.4、162.2、162.3、166.2、161.3和161.2；连续域的覆盖由定理161.5的圆及其后接直线得到。非空原树排除空贡献；一般整数顶点折线的另一个像由命题161.4给出，不能插入逆单位原子格点。括号遗忘和窗口守卫分别已在定理160.4、命题163.3说明。

第三项由定理164.3、命题164.4给整数差和奇偶，普通通道的等式及实际比较条件在第164章已明示。第四项依定理165.2、165.3及166.3，窗口面积只按命题165.4另给提升；完整模式域的函数类型和零因子由约定165.5给出。第五项直接应用定理167.1、命题167.2；记录本身仍由取得和保持合同管理，不由有向面积的大小管理。所有调用保留假设167.3中各自的来源域、未来任务和权限，不从某一扩展域的存在反推原生执行。$\square$

**问题 167.5（实际零纤维和未来拼接仍需的桥）。** 新读出在普通数学中构造了端点—面积关系，没有建立原生 FIB 几何仪器、免费逆门、无界精确存储、未知量子态复制或三维物理空间。它还忘部分顺序和全部未另存的括号；全来源、全窗口、共同环境及相干未来任务的充分性仍需分别验证。下一步可问：某个实际零读出纤维中哪些来源确已可区别；实际能够取得并保留的记录是否对所供后续拼接和操作稳定。这些是给定来源与菜单上的条件问题，不以零参照直接断言空间或宇宙本体。

## 追加锚（第160–167章以下为增补区）
## 168. 相同端点与面积仍可有不同面积位置

**假设 168.1（先取得来源、记录和任务）。** 使用本批几何关系之前，已实际取得有序叶事件的类型与从左到右的发生顺序；任务所需的精确记录能够更新、保持并再次访问。拼接的来源、参照、环境、控制和接缝已相容，允许的后续动作及输出已声明。自由正词的菜单与五模式窗口的合法菜单分别使用；后者继续保留第157章的接缝、层数及错误记录。第177章只讨论一个已供给的有限、分类型的任务菜单及其有限后续，不把未知未来自动纳入。

所需记录为端点、面积和两个面积位置分量；五个寄存量的位宽随来源规模增长，精确算术、读写和保留具有成本。这些条件沿用假设165.1、167.3及前卷第107–110章的实际取得边界。条件满足时才把下面的数学摘要用于实际来源；定义一个数值映射没有取得仪器、复制未知态或执行未发生分支的效力。

**定义 168.2（树、正词与共同几何参照）。** 原始来源仍为非空自由有序二叉树

$$
T::=\alpha\mid\beta\mid\langle T,T\rangle.
$$

定义左到右叶词映射 $\operatorname{wd}$：两个叶分别送为字母 $a,b$，节点送为左右叶词的连接。令 $W=\{a,b\}^+$ 为非空正词，另添空贡献 $\epsilon$，写 $\widehat W=W\cup\{\epsilon\}$。每个非空词有左嵌套树代表；$\epsilon$ 不是原树或第三种叶。替换保持节点的左右顺序和括号，词上的规则为

$$
\rho(a)=b,\qquad \rho(b)=ba,\qquad
\rho(hk)=\rho(h)\rho(k),\qquad \rho(\epsilon)=\epsilon.
$$

树和组成接口直接采用[基础卷定义1.1、1.3及定理1.4，钉版2e9bab02bb1e6d58f0659418318632e1c12d6938](https://github.com/the-omega-institute/trureturing/blob/2e9bab02bb1e6d58f0659418318632e1c12d6938/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)。叶词映射忘括号，不替代原树身份。

另供一个定向欧氏平面、共同原点 $0$ 和正交等长单位步 $e_a=(1,0),e_b=(0,1)$。原点是相对几何的参照，不是物理容器。沿词从左到右累计这两个单位步，得到 $P(h)$。一般有限实折线、有符号三角形链及分段 $C^1$ 曲线属于另声明的数学扩展域；其负方向和逆路不从正词菜单免费取得。面积沿用定义160.2。

**定理 168.3（四叶反例及准确的最小范围）。** 取

$$
r=abba,\qquad s=baab.
$$

它们的路径、逐边有向三角面积和总摘要前三项如下：

| 168 的来源 | 依次经过的顶点 | 逐边面积 | $(u,v,D)$ |
| --- | --- | --- | --- |
| $r$ | $0,(1,0),(1,1),(1,2),(2,2)$ | $0,\frac12,\frac12,-1$ | $(2,2,0)$ |
| $s$ | $0,(0,1),(1,1),(2,1),(2,2)$ | $0,-\frac12,-\frac12,1$ | $(2,2,0)$ |

将第一条路接上第二条的数学反向路，仅作有向图形比较，差链是左下单位正方形取正、右上单位正方形取负。两个方形中心分别为 $(1/2,1/2)$、$(3/2,3/2)$，所以总面积为零，而有向一阶面积矩之差为 $(-1,-1)$。同端点、同面积而面积位置不同的正词对，其最小正词长度恰为四；这个最小性不涉及树的括号、任意观察者或完整来源恢复。

证明（168.3）。对相邻顶点逐一取行列式的一半。$r$ 的后三个行列式为 $1,1,-2$；$s$ 的后三个为 $-1,-1,2$，各自和为零，端点均为 $(2,2)$。

两条路径从 $(1,1)$ 分开，且在 $(1,1)$ 之前也有两种绕行。$r$ 减 $s$ 的左下边界为

$$
(0,0)\to(1,0)\to(1,1)\to(0,1)\to(0,0),
$$

右上边界为

$$
(1,1)\to(1,2)\to(2,2)\to(2,1)\to(1,1).
$$

前者逆时针、后者顺时针；中心乘有向面积给 $(1/2,1/2)-(3/2,3/2)=(-1,-1)$。这里只使用数学差链，未要求观察者实际倒走任何一步。

正词长度等于 $u+v$，所以同端点的两词必同长度。长度零的空扩展、长度一以及同型的词都只有一个叶词。长度二的混合词 $ab,ba$ 面积为 $1/2,-1/2$。长度三的组成 $(2,1)$ 下，$aab,aba,baa$ 的面积依次为 $1,0,-1$；组成 $(1,2)$ 下，$abb,bab,bba$ 的面积也依次为 $1,0,-1$，由逐边行列式直接得到。因此长度不超过三时，同端点及面积已经指定叶词，不会再有面积位置区别。上面的四叶对给存在性，完成最小性证明。树在长度三已经可以仅因括号而不同，这不落在刚证的叶词最小性中。$\square$

## 169. 不除总面积的中心化一阶面积矩

**定义 169.1（有向三角位置和五量读出）。** 对顶点为 $q_0=0,q_1,\ldots,q_N=q$ 的有限实折线，允许 $N=0$、重复顶点、自交与重走。设

$$
a_j=\frac12\det(q_{j-1},q_j),\qquad
g_j=\frac{q_{j-1}+q_j}{3},\qquad
A=\sum_{j=1}^N a_j,
$$

$$
S=\sum_{j=1}^N a_jg_j,\qquad
m=S-\frac{Aq}{2}
=\sum_{j=1}^N a_j\left(g_j-\frac q2\right)
=(m_x,m_y).
$$

$g_j$ 是三角形 $(0,q_{j-1},q_j)$ 的重心；$S$ 是其有向一阶面积矩之和，$m$ 相对于起终点中点中心化。两者都不除以总面积，故不是 $S/A$ 这样的重心坐标；$A=0$ 时仍有定义且可以非零。空折线的各和式为零。对单位正词定义

$$
D=2A,\qquad E=12m_x,\qquad F_m=12m_y,\qquad
G(h)=(u,v,D,E,F_m),\qquad G(t)=G(\operatorname{wd}(t)).
$$

本批始终用 $F_m$ 表示第五个矩坐标，用 $F_{\mathrm{fib}}$ 表示替换映射，用 $F_n$ 表示 Fibonacci 数。一般实折线的五量在 $\mathbb R^5$ 中；正词的整数性在定理171.3由旧值在线归纳证明，不把任意整数五元组预设为正词可达像。

**定理 169.2（零面积而非零位置的精确数值）。** 定理168.3的两词满足

$$
\begin{aligned}
S(r)=m(r)&=\left(-\frac13,-\frac23\right),&
G(r)&=(2,2,0,-4,-8),\\
S(s)=m(s)&=\left(\frac23,\frac13\right),&
G(s)&=(2,2,0,8,4),\\
m(r)-m(s)&=(-1,-1).
\end{aligned}
$$

证明（169.2）。$r$ 的三个非零三角重心为 $(2/3,1/3),(2/3,1),(1,4/3)$，按面积 $1/2,1/2,-1$ 加权，给

$$
S(r)=\frac12\left(\frac23,\frac13\right)
+\frac12\left(\frac23,1\right)-\left(1,\frac43\right)
=\left(-\frac13,-\frac23\right).
$$

$s$ 的三个非零三角重心为 $(1/3,2/3),(1,2/3),(4/3,1)$，按面积 $-1/2,-1/2,1$ 加权，给

$$
S(s)=-\frac12\left(\frac13,\frac23\right)
-\frac12\left(1,\frac23\right)+\left(\frac43,1\right)
=\left(\frac23,\frac13\right).
$$

两者 $A=0$，所以中心化项为零；乘十二得到整数坐标并相减，结果与两个方形的差链一致。$\square$

**定理 169.3（三量无法事后恢复遗漏的两矩）。** 在包含 $r,s$ 的来源族上，不存在函数仅由 $(u,v,D)$ 精确恢复 $(E,F_m)$，也不存在函数仅由三量恢复 $m_x$ 或 $m_y$。

证明（169.3）。两词三量相同，任何该三量的函数必须返回同值；定理169.2给两个矩分量分别不同，与精确恢复要求矛盾。对旧记录作任意确定后处理仍是旧记录的函数，故同样不能补回这对区别。重新取得实际叶序或新的敏感读出属于增加信息，不在本结论的输入中。$\square$

## 170. 带面积位置的拼接接口

**定义 170.1（共同原点的路径拼接）。** $P$ 从零到 $q$，$Q$ 从零到 $r$，摘要分别为 $(q,A,m)$、$(r,B,n)$。先走 $P$，再走平移了 $q$ 的 $Q$，记 $P\diamond Q$；共同单位与定向固定。一般折线的这项拼接是数学定义，实际执行仍需假设168.1的来源及接缝合同。

**定理 170.2（五量的完整拼接律）。** 拼接摘要只依赖两份摘要，并且

$$
\begin{aligned}
q_{\rm tot}&=q+r,\\
A_{\rm tot}&=A+B+\frac12\det(q,r),\\
m_{\rm tot}&=m+n+\frac{Bq-Ar}{2}
+\frac{\det(q,r)}{12}(q-r).
\end{aligned}
$$

证明（170.2）。令 $c=\det(q,r)/2$。第一条路径的三角扇保持不变，第二条的有向三角扇平移了 $q$，再加接缝三角形 $(0,q,q+r)$。平移的第二扇面积仍为 $B$、非中心矩为 $S_Q+Bq$，接缝三角形面积为 $c$、重心为 $(2q+r)/3$。

上述分解对带负号、自交和退化三角形也成立。具体对第二路径的一条边 $z\to z'$，以三角形链记号 $[p_0,p_1,p_2]$，有

$$
[0,q+z,q+z']=[q,q+z,q+z']
+[0,q,q+z']-[0,q,q+z].
$$

这是平面有向三角形的加法恒等式；面积和一阶矩也可分别用 $\det(p_1-p_0,p_2-p_0)/2$ 及该面积乘 $(p_0+p_1+p_2)/3$ 展开验证。沿全部边求和，最后两项望远镜消去，仅余 $[0,q,q+r]$。所以

$$
A_{\rm tot}=A+B+c,\qquad
S_{\rm tot}=S_P+S_Q+Bq+c\frac{2q+r}{3}.
$$

代入 $S_P=m+Aq/2$、$S_Q=n+Br/2$，再减 $A_{\rm tot}(q+r)/2$，得

$$
\begin{aligned}
m_{\rm tot}
&=m+n+\frac{Aq+Br}{2}+Bq
+c\frac{2q+r}{3}-\frac{(A+B+c)(q+r)}2\\
&=m+n+\frac{Bq-Ar}{2}+\frac c6(q-r).
\end{aligned}
$$

$c/6=\det(q,r)/12$，即所列式。$\square$

**定义 170.3（整数坐标的拼接式及实际像）。** 对左五元组 $(u,v,D,E,F_m)$ 和右五元组 $(p,t,H,I,J)$，令 $c_0=ut-vp$，定义数值接口

$$
\begin{aligned}
&(u,v,D,E,F_m)\star(p,t,H,I,J)\\
&\quad=\bigl(u+p,v+t,D+H+c_0,\
E+I+3(Hu-Dp)+c_0(u-p),\
F_m+J+3(Hv-Dt)+c_0(v-t)\bigr).
\end{aligned}
$$

此式就是定理170.2按 $D=2A,E=12m_x,F_m=12m_y$ 换坐标。写 $\mathcal I_+=G(\widehat W)$ 为正词加空贡献的实际数学像；这里的“像”不声称其中每个词已实际执行。

**定理 170.4（实际路径像上的闭合、结合和零贡献）。** 对正词加空贡献及一般有限折线各自的摘要像，$\star$ 实现路径拼接、结合，并以零五元组为单位。原树的节点读出为 $G(\langle t_1,t_2\rangle)=G(t_1)\star G(t_2)$；这些摘要等式不授权原树免费重括号，也不取代实际动作守卫。

证明（170.4）。定理170.2给 $G(P\diamond Q)=G(P)\star G(Q)$；连接两个正词仍是正词，涉及空贡献时仍在 $\widehat W$，所以闭合。对三条路径，$(P\diamond Q)\diamond R$ 与 $P\diamond(Q\diamond R)$ 的逐步向量及顶点完全相同：第三段在两式中都平移了 $q+r$。同一路径的定义169.1给同一摘要，得到结合律。空路径不添步，定理170.2中的端点、面积、矩及接缝项也全为零，故给左右单位。树节点的叶词按定义168.2连接，直接得到节点式。

该证明止于具有路径代表的像，不要求本批证明全 $\mathbb R^5$ 的群结构、全 $\mathbb Z^5$ 或正词五量的完整可达分类。实际记录已取得时，这条式对声明的端点、面积和位置任务封闭；权限、控制和共有环境继续独立保留。$\square$

## 171. 只用旧值的逐事件精确更新

**假设 171.1（五寄存量的实际在线合同）。** 初始空贡献记录为 $(0,0,0,0,0)$。每次下一叶的类型和顺序已实际取得，五寄存量准确保持可访问；一次更新先保留全部旧值，再同时写入新值。算术精度、保持及读写成本纳入假设168.1，不以五个位置固定为由假定位宽固定。未知来源、未执行分支和丢失的旧叶序不在这条输入合同中。

**定理 171.2（原子追加式）。** 右追加 $a$ 和 $b$ 的更新分别为

$$
\begin{aligned}
a:\quad &(u,v,D,E,F_m)\longmapsto
(u+1,v,D-v,E-3D-uv+v,F_m-v^2),\\
b:\quad &(u,v,D,E,F_m)\longmapsto
(u,v+1,D+u,E+u^2,F_m-3D+uv-u).
\end{aligned}
$$

每一个右端的 $u,v,D,E,F_m$ 都取更新前的值。

证明（171.2）。单步的有向三角形面积和矩均为零，故 $G(a)=(1,0,0,0,0)$、$G(b)=(0,1,0,0,0)$。在定义170.3中右代入 $(1,0,0,0,0)$，有 $c_0=-v$，于是

$$
D'=D-v,\qquad E'=E-3D-v(u-1),\qquad F_m'=F_m-v^2.
$$

右代入 $(0,1,0,0,0)$，有 $c_0=u$，于是

$$
D'=D+u,\qquad E'=E+u^2,\qquad
F_m'=F_m-3D+u(v-1).
$$

端点只加相应单位步，整理即得。推导中的 $D$ 是旧路径面积；先把 $D'$ 写回再用它计算矩会改变公式，所以同时更新或先复制旧值是本结论的明确条件。$\square$

**定理 171.3（所有有限词的准确性、整数性和规模边界）。** 在假设171.1下，逐事件执行定理171.2后，每个有限前缀记录恰等于直接三角和定义的 $G$。全部正词及空贡献的五坐标都是整数。长度为 $N$ 的单位正词有

$$
0\le u,v\le N,\qquad |D|\le N^2,\qquad
|E|,|F_m|\le 7N^3.
$$

这给有限规模的位宽上界，不给无界精确记录的固定容量。

证明（171.3）。空前缀的三角和为零。若当前前缀的记录等于定义值，定理170.2精确计算它与实际新单步的拼接，定理171.2又是该式的代入，故新记录仍等于定义值。按词长归纳即覆盖全部有限词。零五元组是整数，两个更新都只用整数加乘，故同一归纳证明整数性；没有把一般实折线误纳入这条整数论证。

对规模界，第 $j$ 步之前各坐标至多 $j-1$，而单位步的行列式绝对值至多 $j-1$，故

$$
\sum_j|a_j|\le\frac12\sum_{j=1}^N(j-1)=\frac{N(N-1)}4.
$$

于是 $|D|\le N(N-1)/2\le N^2$。每个重心分量至多 $2N/3$、终点中点分量至多 $N/2$，所以 $|g_{j,x}-u/2|,|g_{j,y}-v/2|\le7N/6$。乘上述绝对面积和，再乘十二，给 $|E|,|F_m|\le(7/2)N^2(N-1)\le7N^3$。例如保留有符号整数时，各矩寄存量可用 $1+\lceil\log_2(7N^3+1)\rceil$ 位的符号加定长幅值编码；这是随 $N$ 增长的上界，并不规定实际机器编码。

端点 $u$ 已在 $a^N$ 上无界，不能由一个固定有限状态集精确解码所有长度。矩也确实无界：词 $b^ka^k$ 中前 $k$ 步面积零，其后各步面积 $-k/2$，重心为 $((2j-1)/3,2k/3)$，$j=1,\ldots,k$。求和再减 $A(k,k)/2$，得到

$$
A=-\frac{k^2}{2},\qquad
m=\left(\frac{k^3}{12},-\frac{k^3}{12}\right),\qquad
(E,F_m)=(k^3,-k^3).
$$

所以矩寄存量的精确范围也随规模增长。三量记录过去没有保留的两矩，仍受定理169.3限制，不能因本章给了更新式便事后恢复。$\square$

## 172. 所有有序树的 Fibonacci 五量提升

**定义 172.1（数值替换映射）。** 令

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad \det M=-1,
$$

并定义

$$
F_{\mathrm{fib}}(u,v,D,E,F_m)
=(v,u+v,-D-v,v-F_m,-v-3D-E-F_m).
$$

这个符号区别于旧三量映射及第五矩坐标。前三量直接接续定理162.2；下面证明两个新增矩分量及树接口。

**定理 172.2（全词及全树的精确替换律）。** 对每个非空正词及每棵原树，

$$
G(\rho h)=F_{\mathrm{fib}}(G(h)),\qquad
G(\rho t)=F_{\mathrm{fib}}(G(t)).
$$

空贡献另有 $G(\rho\epsilon)=G(\epsilon)=0$，与数值式相容。以未放大坐标写，替换律为

$$
\begin{aligned}
q'&=Mq, &A'&=-A-\frac v2,\\
m_x'&=-m_y+\frac v{12}, &
m_y'&=-m_x-m_y-\frac A2-\frac v{12}.
\end{aligned}
$$

证明（172.2）。先把原路径每个顶点经 $M$ 线性映射。由于 $\det(Mp,Mr)=-\det(p,r)$，每个三角面积反号、重心变为 $Mg_j$，故该直段路径的面积和中心矩为 $-A,-Mm$。

旧 $a$ 的像步是 $(0,1)$，已是 $b$。旧 $b$ 的像步是 $(1,1)$；真实替换将这条直段改成先 $b$ 后 $a$ 的折线。两者的差链是局部三角形

$$
0\to(0,1)\to(1,1)\to0,
$$

面积为 $-1/2$，重心为 $g_*=(1/3,2/3)$。若旧叶前缀终点为 $p$，该差链在新路径中平移到 $Mp$，所以它添非中心矩 $-(Mp+g_*)/2$；新总端点仍为 $Mq$。

按出现顺序给旧 $b$ 编号 $j=1,\ldots,v$。第 $j$ 个 $b$ 前的旧端点为 $p_j=(x_j,j-1)$，其中 $x_j$ 数它之前的 $a$。设 $K=\sum_jx_j$。由异型叶对分解定理164.3，$A=K-uv/2$；也可直接把每对 $a$在$b$前计 $+1$、反序计 $-1$，总计数 $uv$，得到 $2A=2K-uv$。因此

$$
\sum_{j=1}^v p_j=\left(K,\frac{v(v-1)}2\right),
\qquad K=A+\frac{uv}2.
$$

共有 $v$ 个局部差三角形，故 $A'=-A-v/2$。记线性路径非中心矩为 $-MS$，则替换后非中心矩为

$$
S'=-MS-\frac12M\sum_{j=1}^vp_j-\frac v2g_*.
$$

代入 $S=m+Aq/2$，再减 $A'Mq/2$，原有 $A$ 的中点项抵消，得

$$
m'=-Mm-\frac12M\sum_{j=1}^vp_j
-\frac v2\left(\frac13,\frac23\right)+\frac v4Mq.
$$

由于 $M\sum p_j=(v(v-1)/2,K+v(v-1)/2)$，第一分量为

$$
-m_y-\frac{v(v-1)}4-\frac v6+\frac{v^2}4
=-m_y+\frac v{12},
$$

第二分量为

$$
-m_x-m_y-\frac K2-\frac{v(v-1)}4
-\frac v3+\frac{v(u+v)}4
=-m_x-m_y-\frac A2-\frac v{12}.
$$

把面积乘二、两矩乘十二，便得到定义172.1的五量式。$v=0$ 时差链为空，所有求和仍有效。

树接口另按结构归纳验证 $\operatorname{wd}(\rho t)=\rho(\operatorname{wd}(t))$：$\alpha$ 给 $b$，$\beta$ 给 $ba$；节点保持左右配对，叶词连接与词替换相容。于是已证的词公式对每棵树成立，包括任何括号。空贡献不属于这项非空树归纳；其词替换与零五量直接单列验证。$\square$

**定理 172.3（整数数值环境中的逆及其准确范围）。** 数值线性映射 $F_{\mathrm{fib}}:\mathbb Z^5\to\mathbb Z^5$ 的行列式为 $-1$。若输出记为 $(U,V,H,I,J)$，其逆为

$$
F_{\mathrm{fib}}^{-1}(U,V,H,I,J)
=(V-U,U,-H-U,U+3H+I-J,U-I).
$$

这是整个数值环境中的双射；本结论没有把 $\rho$ 变成正词像上的满射、树单射或实际可执行逆门。

证明（172.3）。映射矩阵为

$$
L=\begin{pmatrix}
0&1&0&0&0\\
1&1&0&0&0\\
0&-1&-1&0&0\\
0&1&0&0&-1\\
0&-1&-3&-1&-1
\end{pmatrix}.
$$

右上 $2\times3$ 块为零，所以其行列式是左上 $M$ 的行列式与右下块的行列式之积。右下块

$$
\begin{pmatrix}-1&0&0\\0&0&-1\\-3&-1&-1\end{pmatrix}
$$

沿首行展开行列式为一，故 $\det L=-1$。从 $U=v,V=u+v,H=-D-v,I=v-F_m$ 先得 $v=U,u=V-U,D=-H-U,F_m=U-I$；代入 $J=-v-3D-E-F_m$ 得 $E=U+3H+I-J$。这些反解逐项代回原式给 $(U,V,H,I,J)$，从原输入反解也给原五量，故是整数双向逆。

范围不能扩大。例如正词 $a$ 的五量有 $U=1,V=0$，其数值逆的第二端点为一、第一端点为 $-1$，不在正词端点域，故 $F_{\mathrm{fib}}(\mathcal I_+)$ 不包含全部 $\mathcal I_+$。又 $G$ 已遗忘不同括号，数值逆没有恢复原树身份。是否供给逆操作由实际菜单决定，不由这个整数矩阵决定。$\square$

## 173. 同步替换保持旧摘要并运输隐藏差

**定义 173.1（同步来源及 Fibonacci 数）。** 令 $r_n=\rho^n(r)$、$s_n=\rho^n(s)$，$n\ge0$，两条来源使用同一个替换步数。记 $\Delta m_n=m(r_n)-m(s_n)$，并令

$$
F_0=0,\qquad F_1=1,\qquad F_{n+2}=F_{n+1}+F_n.
$$

这是数列下标记号，与 $F_m$ 和 $F_{\mathrm{fib}}$ 分开。

**定理 173.2（每一步旧三量相同及矩差的闭式）。** 对所有 $n\ge0$，$r_n,s_n$ 的 $(u,v,D)$ 相同，而

$$
\Delta m_n=(-1)^{n+1}(F_{n+1},F_{n+2}).
$$

证明（173.2）。初始三量由定理168.3相同。替换后的前三量只依赖旧前三量，定义172.1遂按 $n$ 归纳保持相同。两个矩的替换式中，附加项仅依赖共同的 $v,A$，相减消去，留下

$$
\Delta m_{n+1}=-M\Delta m_n,\qquad \Delta m_0=(-1,-1).
$$

再按 $n$ 归纳，$M^0(1,1)=(F_1,F_2)$，而

$$
M(F_{n+1},F_{n+2})=(F_{n+2},F_{n+1}+F_{n+2})
=(F_{n+2},F_{n+3}).
$$

所以 $\Delta m_n=(-M)^n(-1,-1)$ 等于所列闭式。$F_{n+1},F_{n+2}$ 为正，区别不会消失。这是初始已存在区别的运输，不是替换从共同三量凭空创造来源信息。$\square$

**假设 173.3（仅以共同旧摘要预测的新任务）。** 固定实数 $\lambda\ne0$，新目标读出为

$$
f_\lambda(h)=A(h)+\lambda m_x(h).
$$

确定预测器只取得旧三量 $(u,v,D)$，以及在两来源上相同的已声明任务参数；没有额外来源标签、叶序、随机读出或新观测。

**定理 173.4（新增位置任务的误差下界及旧任务有效性）。** 对假设173.3的任意确定预测器，在初始来源 $r,s$ 中至少一个上的绝对误差不小于 $|\lambda|/2$。旧三量对原来端点—面积及第165章的继续任务仍准确；新任务要求更细读出不推翻旧任务的结论。

证明（173.4）。定理169.2给

$$
f_\lambda(r)=-\frac\lambda3,\qquad
f_\lambda(s)=\frac{2\lambda}3.
$$

预测器对共同三量返回同一个数 $z$。由实数三角不等式，

$$
|\lambda|=|f_\lambda(r)-f_\lambda(s)|
\le |f_\lambda(r)-z|+|z-f_\lambda(s)|
\le2\max\{|f_\lambda(r)-z|,|f_\lambda(s)-z|\}.
$$

除以二得到下界。这个界针对所供的确定预测合同，不推出对额外观测或其他随机任务的相同结论。

对旧任务，前三量仍能直接返回端点及 $A=D/2$，它们的更新正是定理165.2和162.2。定理165.3的有限继续论证仍在原菜单成立；本章只增加一个原来未声明的输出，故旧假设与旧结论保持。$\square$

## 174. 保留高到低守卫的五模式来源提升

**定义 174.1（固定代表、独立接缝和事件类型）。** 使用定义163.1及前卷第103章的同一代表选择，词代表与五量为

| 174 的模式 | $w_\sigma$ | $G(w_\sigma)$ | 允许旧接缝 | 新接缝 |
| --- | --- | --- | --- | --- |
| $\mathrm{null}$ | $\epsilon$ | $(0,0,0,0,0)$ | $0,1$ | $0$ |
| $[2]$ | $a$ | $(1,0,0,0,0)$ | $0,1$ | $1$ |
| $[3]$ | $b$ | $(0,1,0,0,0)$ | $0,1$ | $0$ |
| $[5]$ | $ba$ | $(1,1,-1,1,-1)$ | $0$ | $0$ |
| $[25]$ | $baa$ | $(2,1,-2,4,-2)$ | $0$ | $1$ |

接缝按定义157.1和[钉版基础卷定义7.1](https://github.com/the-omega-institute/trureturing/blob/2e9bab02bb1e6d58f0659418318632e1c12d6938/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)从高到低读取；旧接缝一禁止 $[5],[25]$，其他三模式允许旧接缝零或一。非法输入进入独立吸收错误态。$\mathrm{End}$、原过程的 $\mathrm{Stop}$、未读和真实 $\mathrm{null}$ 是不同类型，复用基础卷定义2.4的区分；本即时读者没有 $\mathrm{End}$ 动作，不人为添加一个同零贡献的结束分支。

**假设 174.2（新增且已供给的词层编译）。** 对每一个合法高到低模式输入，明确供给并实际取得如下来源提升：当前词为 $h$ 时先替换三次，再右接固定代表，

$$
h'=\rho^3(h)w_\sigma.
$$

起始词为空贡献、起始接缝为零；仅有原窗口的组成更新不视为已经供给这条内部词编译。实际层数、控制、错误及共有来源仍按假设168.1保存。词提升是数学及取得合同，不把整套五量公式称为原生宏模式仪器。

**定理 174.3（五量提升与旧组成接口相容）。** 在假设174.2的每个合法活态步骤，

$$
G(h')=F_{\mathrm{fib}}^3(G(h))\star G(w_\sigma).
$$

投影到端点恢复原高到低读者

$$
x'=M^3x+d_\sigma,\qquad
M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix}.
$$

表174.1的每个五量均正确。该提升保留原守卫，不把五个模式对象与五个数值寄存量认作同一种对象。

证明（174.3）。空和单叶表值由定义169.1得到。对 $ba$ 从 $b$ 右加 $a$，定理171.2给 $(1,1,-1,1,-1)$；在该旧值上再右加 $a$ 得

$$
(2,1,-2,\ 1-3(-1)-1+1,\ -1-1)
=(2,1,-2,4,-2),
$$

验证末行。其余三行无非零三角形，故表已全证。

定理172.2三次应用得到 $G(\rho^3h)=F_{\mathrm{fib}}^3G(h)$，再用定理170.4拼接代表，得到五量提升。端点投影逐次按 $M$，拼接按向量加法，代表端点正是 $d_\sigma$，故给 $M^3x+d_\sigma$。接缝表直接沿用旧合同，数值提升只在合法边计算；非法边仍到错误态，不由任意自由词的存在转为合法。五模式属于字母表，五量属于记录的数值坐标，前者决定本步骤的标签，后者保存累计路径的关系，表格行数相同不建立二者身份。$\square$

**定理 174.4（真实零窗口仍有运输及事件效果）。** $\mathrm{null}$ 的代表空贡献只表示本步骤没有额外叶词；它使记录变为 $F_{\mathrm{fib}}^3(G(h))$、新接缝为零且层数增加，保留一次实际读取事件。因此它一般不是恒等，与未读、结束和停止均不同。

证明（174.4）。$G(\epsilon)=0$ 是拼接单位，定理174.3给数值运输而非旧值保持。从 $h=a$ 出发，$\rho^3(a)=bab$，直接在线更新给

$$
G(a)=(1,0,0,0,0),\qquad G(bab)=(1,2,0,2,2),
$$

已非恒等；端点也从 $(1,0)$ 变为 $(1,2)$。接缝输出和层数变化由窗口合同给出，即使当前来源为空、数值仍零，也发生了这个输入事件。未读没有这个事件；结束和停止须有其另给的类型和转移，不能借零代表补出。$\square$

## 175. 三角接缝、共同参照、圆链与量纲

**定义 175.1（积分扩展的独立域）。** 对有限区间上的连续分段 $C^1$ 路径 $z(t)=(x(t),y(t))$，以有限个光滑段上的普通积分之和定义

$$
A=\frac12\int\det(z,dz),\qquad
S=\frac13\int z\det(z,dz),\qquad m=S-\frac{Aq}{2},
$$

其中起点为零、终点为 $q$。路径可以自交或回走，不要求正坐标方向；参数改变只在保持方向的分段 $C^1$ 重参数化下作普通变量代换。另允许有限个闭曲线的有向链，系数取整数，其 $A,S$ 按线性相加，净端点为零，故 $m=S$。不通过共同原点的闭分量也可直接用同一坐标积分。这些是正词域之外的数学扩展，不宣称能由原生正叶或窗口读取实际实现。

积分背景采用 Joscha Diehl、Rosa Preiß、Jeremy Reizenstein，[*Conjugation, loop and closure invariants of the iterated-integrals signature*，arXiv:2412.19670v1](https://arxiv.org/abs/2412.19670v1)，版本2024-12-27，[完整正文](https://arxiv.org/pdf/2412.19670v1)。其 §2 pp.3–5、§3 pp.11–13、§4 pp.22–25 分别讨论共轭、闭路换起点和直线闭合，Definition 2.1、Definition 3.1、Proposition 3.2、Definition 4.1及Lemma 4.7的对象和条件各有区别。下列 FIB 接口的计算逐项给出；不把文献的平滑路径和数学反向路径当成已取得的 FIB 操作。

**定理 175.2（积分与三角定义相合及线性运输）。** 定义175.1对有限折线等于定义169.1。对实线性平面映射 $L$，在相同折线或积分域中有

$$
q'=Lq,\qquad A'=\det(L)A,\qquad m'=\det(L)Lm.
$$

特别地，正交 $R$ 给 $(Rq,\det R\,A,\det R\,Rm)$；共同尺度 $s>0$ 给

$$
(q,A,m)\longmapsto(sq,s^2A,s^3m).
$$

五量因此包含两个一阶、一个二阶和两个三阶分量，不是五根等价空间轴。几何运输本身不保证保持正词可达像或实际可执行。

证明（175.2）。对单直段 $z(t)=(1-t)p+tr$，$0\le t\le1$，有

$$
\det(z,z')=\det(p,r),\qquad
\int_0^1z(t)\,dt=\frac{p+r}{2}.
$$

其面积为 $\det(p,r)/2$，矩为 $\det(p,r)(p+r)/6$，正是定义169.1的 $a_jg_j$。逐段相加证明相合，包括退化及负向段。

一般 $L$ 满足 $\det(Lp,Lr)=\det(L)\det(p,r)$。三角形重心经 $L$、端点也经 $L$，逐项代入得到面积及矩公式；在积分域则直接代入 $d(Lz)=L\,dz$，得到相同结果。中心化项 $Aq/2$ 也按 $\det(L)L$ 运输，故 $m$ 的公式成立，即使 $L$ 奇异也有效。取 $L=R$ 或 $sI$ 得特别式。

例如交换两轴 $R(x,y)=(y,x)$ 使面积反号、矩为 $(-m_y,-m_x)$，但没有反转叶事件的发生顺序。缩放后单位步成为长度 $s$ 的步，$s\ne1$ 时不在本批固定单位正词读出中；正交旋转也不一般把两个正原子送回原字母。因此变换公式与正词内部操作闭合是两项不同条件。$\square$

**定理 175.3（共平移、闭路换起点与补弦的区别）。** 物体与观察参照共同平移后，相对顶点、端点、面积和中心矩不变。对同一闭路，只把起点改为原坐标中该路上的点 $t$，再将新起点作为零参照，则

$$
A_{\mathrm{new}}=A,\qquad m_{\mathrm{new}}=m-At.
$$

因此闭路面积的起点不变性不一般扩及两个矩。对从零到 $q$ 的开放路径，沿直弦 $q\to0$ 数学闭合，则

$$
A_{\mathrm{closed}}=A,\qquad m_{\mathrm{closed}}=m+\frac{Aq}{2}.
$$

证明（175.3）。绝对位置和参照同时加向量 $t$ 时，相对坐标为 $(p+t)-(O+t)=p-O$，逐项定义完全不变。这与只移其中一方不同，也与保持物体不动、改用另一条路径起点不同。

闭曲线积分不受循环选择积分起点影响，各段只是循环重排；但以新起点为零时，整条坐标路变为 $z-t$。因为闭路 $\int dz=0$，面积积分满足

$$
\frac12\int\det(z-t,dz)=A-\frac12\det\left(t,\int dz\right)=A.
$$

为计算矩，在任意分段 $C^1$ 闭路上分段积分分部，闭路的边界项消去，得到

$$
S_x=\frac12\oint x^2\,dy,\qquad
S_y=-\frac12\oint y^2\,dx,\qquad
A=\oint x\,dy=-\oint y\,dx.
$$

例如 $\oint d(x^2y)=2\oint xy\,dx+\oint x^2\,dy=0$，代入 $S_x=\frac13\oint(x^2dy-xy\,dx)$ 得首式；第二式由 $d(xy^2)$ 同理得到。将 $x$ 改为 $x-t_x$，$S_x$ 变为 $S_x-t_xA$，因为 $\oint dy=0$；$S_y$ 同理变为 $S_y-t_yA$。闭路端点零，$m=S$，故得到 $m_{\mathrm{new}}=m-At$。若 $A=0$ 或 $t=0$ 则相应不变，不能从退化情形推广为全部闭路不变。

直弦上 $z(\tau)=(1-\tau)q$ 与 $dz$ 共线，所以面积和非中心矩积分都为零。闭合后端点为零，非中心矩仍为 $S$，因此 $m_{\mathrm{closed}}=S=m+Aq/2$。这与开放路径原来的中点中心化不同。

上述区别与所引文献 §3的闭路换起点、§4的直线闭合范围相合。开放路径面积不是一般共轭不变量；文献没有声称本批全部五量都是闭路起点不变量。数学补弦及循环换起点也没有取得任何逆门。$\square$

**定理 175.4（等圆反向的面积消去及位置保留）。** 在定义175.1的有向闭曲线链域中，半径 $R>0$、中心分别为 $c,d$ 的两个圆周，第一条正向、第二条反向，其合成满足

$$
q=0,\qquad A=0,\qquad m=\pi R^2(c-d).
$$

若 $c\ne d$，矩非零。若要求一条以零为基点的连续闭路，可以供给显式往返连接段，得到相同面积及矩；这项存在性仍属于一般曲线域，不属于正词可达或实际装置结论。

证明（175.4）。正向圆参数为 $z(\theta)=c+R(\cos\theta,\sin\theta)$，$0\le\theta\le2\pi$。写 $e=(\cos\theta,\sin\theta)$，有

$$
\det(z,z')=R^2+R(c_x\cos\theta+c_y\sin\theta).
$$

三角函数的一阶积分为零、平方积分为 $\pi$、交叉积分为零，故 $A=\pi R^2$，并且

$$
\begin{aligned}
3S
&=\int_0^{2\pi}(c+Re)\bigl(R^2+R(c\cdot e)\bigr)\,d\theta\\
&=2\pi R^2c+R^2\int_0^{2\pi}e(c\cdot e)\,d\theta
=3\pi R^2c.
\end{aligned}
$$

所以 $S=\pi R^2c$。反向参数使两个积分同时取负，第二圆给 $-\pi R^2$ 和 $-\pi R^2d$。闭链端点为零，线性相加即得式。

具体单闭路可按顺序走：从零直达 $c+(R,0)$、走完整个正向圆、沿同一直段反向回零；再从零直达 $d+(R,0)$、走反向圆、沿其连接段反向回零。连接段与自己的反向段坐标点相同、积分方向相反，所以对 $A,S$ 的贡献成对消去。剩下两个圆的积分，得到所需单闭路。这些连接段含负向步，不能把它们改说成原生正叶的免费实际逆。$\square$

## 176. 固定 Pauli 读口与面积位置记录的不同信息

**假设 176.1（固定表示及乘序）。** 复用[前卷第101–107章，钉版b9b4a62b69908c14f2b3ceb07204620db61aa862](https://github.com/the-omega-institute/trureturing/blob/b9b4a62b69908c14f2b3ceb07204620db61aa862/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)的固定表示，

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
\mathsf a=-iX,\quad \mathsf b=-iY.
$$

词 $h$ 的矩阵读出 $U(h)$ 按印刷顺序将字母替为 $\mathsf a,\mathsf b$ 后相乘；空贡献给 $I$。作为矩阵对态的作用，右因子先执行。几何路径的叶事件从左到右累计，这是另一条合同；若要将矩阵的实际时间执行与叶事件对应，须另供相应编译和取得合同，不能仅借同一个词把二者次序混同。

**定理 176.2（四叶反例在固定读口都为恒等）。** 本章固定表示满足

$$
U(r)=\mathsf a\mathsf b\mathsf b\mathsf a=I,\qquad
U(s)=\mathsf b\mathsf a\mathsf a\mathsf b=I.
$$

因此两个来源的不同面积位置没有由这个固定终端矩阵读口读出；它们作为单系统通道也相同。

证明（176.2）。$X^2=Y^2=I$，所以 $\mathsf a^2=\mathsf b^2=-I$。于是

$$
\mathsf a\mathsf b^2\mathsf a=-\mathsf a^2=I,\qquad
\mathsf b\mathsf a^2\mathsf b=-\mathsf b^2=I.
$$

每个密度算子都被 $I\varrho I^\dagger$ 保持，故通道相同。定理169.2同时给不同矩，说明五量读出与这个矩阵读出保留的区别不同。证明只计算所列两词；没有在本章从此二例外推全部同步 $\rho$ 层上的矩阵恒等。$\square$

**定理 176.3（位置任务需要实际保留或另供敏感读口）。** 若当前实际可访问资料仅为上述相同终端矩阵及共同旧三量，没有来源、叶序或其他相关记录，则不能精确返回两个来源各自的 $m$。若已按假设171.1保留在线五量，位置任务可直接解码；若采用别的后续仪器，则它对来源差的敏感性及共同实现须另外供给。

证明（176.3）。前一种合同把 $r,s$ 送到同一可访问输入；任何精确确定解码都对该输入返回同一值，而定理169.2的 $m$ 不同，构成矛盾。后一种合同中，在线准确性由定理171.3保证，故返回 $(E/12,F_m/12)$ 就是位置矩；这里用了已经取得和保留的记录，没有从终端 $I$ 反推出历史。

若另给仪器 $J$，它必须在所供共同输入及来源接口上确实产生能够区别目标值的响应，才可替代在线记录。前卷第107–110章的相位、控制和环境条件继续是前提；矩阵名字、平面图或整数逆都没有证明这个响应已经实际存在。$\square$

## 177. 五量的非完整性与有限未来的任务充分性

**定理 177.1（不同八叶词仍有相同五量）。** 连接定理168.3的两词，得

$$
rs=abbabaab,\qquad sr=baababba.
$$

二者是不同的八叶正词，却均满足

$$
G(rs)=G(sr)=(4,4,0,4,-4).
$$

因而五量不恢复完整叶词，更不恢复原树括号。

证明（177.1）。直接连接 $abba$ 与 $baab$ 得 $abbabaab$，反序连接得 $baababba$；第一片叶已经不同。两段端点同为 $(2,2)$，面积均零，所以定理170.2的端点接缝行列式及 $Bq-Ar$ 都为零，矩仅相加。定理169.2遂给

$$
q_{\mathrm{tot}}=(4,4),\quad A_{\mathrm{tot}}=0,\quad
m_{\mathrm{tot}}=\left(\frac13,-\frac13\right),
$$

换坐标得到所列五量。分别为两个词选左嵌套树，得到叶序不同的原树反例；此外同一叶词的不同括号也被定义168.2合并。例如 $\langle\langle\alpha,\alpha\rangle,\beta\rangle$ 与 $\langle\alpha,\langle\alpha,\beta\rangle\rangle$ 的叶词同为 $aab$，故五量相同，但仍是不同树。$\square$

**定义 177.2（三个固定任务等价关系）。** 在 $\widehat W$ 上分别定义

$$
\begin{aligned}
h\sim_1 k&\iff q(h)=q(k),\\
h\sim_2 k&\iff (q(h),A(h))=(q(k),A(k)),\\
h\sim_3 k&\iff (q(h),A(h),m(h))=(q(k),A(k),m(k)).
\end{aligned}
$$

树域上的关系是这些关系经叶词映射的拉回；不把任何一个关系等同于树身份。$\sim_3$ 也恰是五量相同，因为 $D,E,F_m$ 与 $A,m$ 的固定放大可逆。

**定理 177.3（严格细化及其终点边界）。** 三个关系满足严格包含

$$
\sim_3\ \subsetneq\ \sim_2\ \subsetneq\ \sim_1,
$$

而 $\sim_3$ 仍严格粗于正词身份。

证明（177.3）。五量相等逐项推出三量、两端点相等，所以包含成立。$ab,ba$ 的端点相同，面积为 $1/2,-1/2$，故在 $\sim_1$ 中而不在 $\sim_2$ 中。$r,s$ 由定理168.3和169.2在 $\sim_2$ 中而不在 $\sim_3$ 中。$rs,sr$ 由定理177.1在 $\sim_3$ 中但正词不同，证明最后的严格性。各对均有原树代表，所以拉回树域的前两项严格性也成立；括号的额外遗忘保持。$\square$

**假设 177.4（有限同菜单、同权限、同接入来源）。** 实际状态由一份来源以及已保留上下文 $c$ 组成；$c$ 含所需接缝、层数、控制、参照、共同环境与事件类型，且具有声明的准确相等关系。活态、非法或执行错误、结束、停止和未读分别标记；终态的传播合同也分别给出。摘要为活态 $(G(h),c)$ 或相应带标记的已保留终态记录。

固定一个有限分类型菜单。活态动作只包括已经供给的 $a,b$ 右追加、指定词或已取得相容路径的左或右拼接、$\rho$ 替换，以及按假设174.2已供给的合法模式提升。每个拼接动作在比较的两条来源上使用同一份已取得的另一摘要及相同接入上下文；不是分别选择两个边缘可达但未共同实现的来源。每个输出是上述摘要的已声明函数。动作的可用性、错误类型和上下文更新必须是该摘要的函数，或已另证在摘要纤维上相同。

比较只使用同一动作序列的有限后续，或由共同摘要及共同读出确定的同一有限决策规则。依赖未保存来源的策略、抽取子树、未知相干控制、未另供给的 $\mathrm{Stop}$ 或 $\mathrm{End}$ 动作不属于这个菜单。若实际合法性需要额外字段，则先保留该字段或补纤维证明，不能用几何公式代替它。

**定理 177.5（有限共同任务的纤维保持及经典三阶对应）。** 在假设168.1、171.1、177.4及其所用模式提升合同下，两个同摘要实际状态经任意共同合法有限后续仍有相同摘要和相同声明输出；同一非法后续也按共同错误合同给相同类型。五量因而只对这份菜单及输出任务充分。用经典三阶对数路径签名的五个系数代替五量，结论不变；这种对应不把五量升级为完整无限签名、完整来源或实际仪器。

证明（177.5）。原子追加由定理171.2下降为五量函数；左或右拼接由定理170.2及170.3下降，且另一份摘要及其相容上下文共同给定；$\rho$ 由定理172.2下降；合法模式提升由定理174.3下降，接缝由表174.1共同判定。上下文更新、权限和输出按假设177.4也下降，所以每个同标签动作对两个同摘要输入给同摘要输出或同类型错误。后续长度零时已同摘要；归纳假设下一步之前同摘要，上述逐动作性质使下一步之后也同摘要，完成有限长度归纳。共同摘要决定的决策规则在两来源上选择同一下一标签，故相同归纳适用；依赖未保存来源的选择没有这个性质，不在结论中。这正是[基础卷定义3.1–3.3](https://github.com/the-omega-institute/trureturing/blob/2e9bab02bb1e6d58f0659418318632e1c12d6938/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)的读出及更新纤维条件在本菜单上的具体实现。

经典积分对应作为上述 FIB 任务的坐标解释，采用 Ilya Chevyrev、Andrey Kormilitzin，[*A Primer on the Signature Method in Machine Learning*，arXiv:1603.03788v2](https://arxiv.org/abs/1603.03788v2)，正文版本2025-01-17，初稿v1为2016-03-11，[完整正文](https://arxiv.org/pdf/1603.03788v2)。对应位置为 Definition 1.4、§1.2.4式(12)的 Lévy 面积、§1.3.2的 shuffle 恒等式、§1.3.3 Theorems 1.17、1.22及Corollary 1.23的 Chen 拼接、§1.3.5的对数签名，以及 §2.1.5 p.48式(41)的三阶系数。这里沿用经典理论，不宣称其原创性；本批的承重连接是有序 FIB 替换、模式提升及有限任务接口。

为明确约定和系数，对从零出发的分段 $C^1$ 路径 $z=(x,y)$，记 $dz_1=dx,dz_2=dy$，定义普通迭代积分

$$
S_{i_1\cdots i_k}
=\int_{t_1<\cdots<t_k}dz_{i_1}(t_1)\cdots dz_{i_k}(t_k),
\qquad S_\emptyset=1.
$$

取两个不交换形式字母 $X_1,X_2$，写 $S_k=\sum S_{i_1\cdots i_k}X_{i_1}\cdots X_{i_k}$。只在次数不超过三的有限截断中定义

$$
\begin{aligned}
L_1&=S_1,\\
L_2&=S_2-\frac12S_1^2,\\
L_3&=S_3-\frac12(S_1S_2+S_2S_1)+\frac13S_1^3.
\end{aligned}
$$

这是形式对数展开到三阶，不涉及无限级数的收敛。令 $[X_1,X_2]=X_1X_2-X_2X_1$。在本批三角矩约定下，精确对应为

$$
L_1=uX_1+vX_2,\qquad
L_2=A[X_1,X_2],
$$

$$
L_3=m_x[X_1,[X_1,X_2]]+m_y[X_2,[X_1,X_2]].
$$

下面给出普通积分推导，避免仅按坐标个数宣称这个对应。重复一维积分给 $S_{11}=u^2/2,S_{22}=v^2/2,S_{111}=u^3/6,S_{222}=v^3/6$；积分分部给

$$
S_{12}=\int x\,dy,\qquad S_{21}=\int y\,dx,\qquad
S_{12}+S_{21}=uv,\qquad S_{12}-S_{21}=2A.
$$

于是对数二阶的混合系数分别为 $A,-A$，纯字母系数为零。

三阶先算 $112$ 的系数。内层两个 $dx$ 的积分为 $x(t)^2/2$，故 $S_{112}=\frac12\int x^2dy$。由定义175.1及

$$
\int d(x^2y)=u^2v=2\int xy\,dx+\int x^2dy
$$

得到开放路径的非中心矩与中心矩

$$
S_x=\frac12\int x^2dy-\frac{u^2v}{6},\qquad
m_x=\frac12\int x^2dy-\frac{u^2v}{6}-\frac{uA}{2}.
$$

另一方面，对数展开的 $112$ 系数为

$$
\begin{aligned}
(L_3)_{112}
&=S_{112}-\frac12(uS_{12}+S_{11}v)+\frac{u^2v}{3}\\
&=\frac12\int x^2dy-\frac{uS_{12}}2+\frac{u^2v}{12}
=m_x,
\end{aligned}
$$

最后一步用 $S_{12}=A+uv/2$。由积分分部或将乘积积分域按时间顺序分开，得到

$$
uS_{12}=2S_{112}+S_{121},\qquad
S_{11}v=S_{112}+S_{121}+S_{211}.
$$

例如第一式也由 $d(xS_{12}(t))=S_{12}(t)dx+x^2dy$ 得到；第二式把两个有序 $dx$ 的时间及一个 $dy$ 的时间按三种位置分区得到，等时集合在普通积分中为零。代入对数式给

$$
(L_3)_{121}=-2m_x,\qquad (L_3)_{211}=m_x.
$$

交换 $x,y$ 同理，开放路径满足

$$
S_y=-\frac12\int y^2dx+\frac{uv^2}{6},\qquad
m_y=-\frac12\int y^2dx+\frac{uv^2}{6}-\frac{vA}{2}.
$$

于是

$$
(L_3)_{221}=-m_y,\qquad
(L_3)_{212}=2m_y,\qquad
(L_3)_{122}=-m_y.
$$

纯字母三阶系数为 $u^3(1/6-1/2+1/3)=0$ 及对应的 $v$ 式。展开两个双交换子分别为 $112-2\,121+211$、$2\,212-221-122$，恰含全部八个三阶字，完成所列 $L_3$ 的推导。

上述乘积积分分区是低阶 shuffle 公式的普通积分来源。拼接时，每个有序积分的时间点按落在第一段还是第二段分为一个前缀和一个后缀，故

$$
S_{i_1\cdots i_k}(P\diamond Q)
=\sum_{j=0}^k S_{i_1\cdots i_j}(P)
S_{i_{j+1}\cdots i_k}(Q),\qquad k\le3.
$$

这就是所引 Chen 拼接在本有限阶数上的直接证明；平移第二段不改其微分，公式与共同端点拼接相容。没有借完整无限理论恢复树括号。

五量与这些经典低阶系数的对应为

$$
(u,v,D,E,F_m)=(u,v,2A,12m_x,12m_y),
$$

所以在同一读出约定下二者互相确定；有限共同菜单的纤维保持不因这种可逆坐标改写而改变。经典完整签名是所有阶的迭代积分序列，路径唯一性还受平移、重参数化及 tree-like 等价的条件约束。这里仅取到三阶，不宣称五量等于完整无限签名。$rs,sr$ 已证明低阶记录不恢复正词；原树括号从叶路径生成时已经遗忘，即使换成完整路径签名，也没有从它恢复该生成括号的依据。$\square$

**定理 177.6（整合的条件范围）。** 在各章明确的来源域、实际取得和菜单条件下：中心化面积矩在零总面积时仍有意义；五量按拼接和实际原子事件准确继续，按所有树的 FIB 替换闭合；旧三量遗漏的位置区别可以沿同步替换运输，但不由旧三量恢复；选定五模式来源提升兼容原组成更新且保留守卫；尺度和定向按各自阶数运输；固定 Pauli 终端读口不一般读取这份位置区别；五量对所供有限菜单充分而仍非全来源记录。

证明（177.6）。零面积的定义及反例由定义169.1、定理169.2给出。拼接和事件准确性分别由定理170.2、170.4、171.2、171.3给出；全树替换由定理172.2及其叶词结构归纳给出，数值逆只在定理172.3的数值环境使用。遗漏及运输由定理169.3、173.2、173.4给出，原端点—面积任务仍保有原范围。模式来源提升调用假设174.2及定理174.3、174.4，不从原组成表反推未供给的内部词。尺度、定向、共平移、循环换起点和补弦分别按定理175.2、175.3使用；圆反向例仅在定义175.1的扩展域内由定理175.4实现。Pauli同读口和实际位置取得分别由定理176.2、176.3给出。最后，非完整性由定理177.1、177.3给出，有限任务充分性恰由假设177.4及定理177.5给出。

这些调用保留同一实际来源、共同实现与可访问记录条件，不能把不同边缘存在的仪器或历史当作一个共同实现。五寄存量的精确有限更新没有完成原生几何仪器、相干硬件、无界存储、所有未来任务或物理空间解释；这些存在与取得要求仍是所列假设，不是整合结论。$\square$

## 追加锚（第168–177章以下为增补区）

## 178. 固定根的实际任务支持、加权准备像与两种通道成本

**假设 178.1（同一十五边仪器与固定输入）。** 本章的普通数学供应源为本卷[固定版本 c32e033a62a0a4a3bd63ab6b7af1d1ea59059651，第126–135章](https://github.com/the-omega-institute/trureturing/blob/c32e033a62a0a4a3bd63ab6b7af1d1ea59059651/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md)。配置依原顺序为 $0,1,2,3,4$，分别表示 $\mathrm{null},[2],[25],[5],[3]$；完整系统仍为 $\mathcal C\otimes K=\mathbb C^5\otimes\mathbb C^2$。固定所有 $p,q,r>0$ 且 $p+q+r<1$，记

$$
\delta=1-p-q-r,\qquad \epsilon=1-p-q,\qquad \zeta=1-r,
\qquad
P=\begin{pmatrix}
\delta&p&0&q&r\\
q&\epsilon&p&0&0\\
0&q&\epsilon&p&0\\
p&0&q&\epsilon&0\\
r&0&0&0&\zeta
\end{pmatrix}.
$$

行是来源，列是后继。五个自环、八条有向方形边及两条支边全部严格为正。内部运输精确使用第127章的 $a=-iX,b=-iY,c=ba=iZ$：

$$
U_{10}=a,\quad U_{21}=c,\quad U_{32}=a^\dagger,
\quad U_{03}=c^\dagger,\quad U_{40}=b,
\qquad U_{ij}=U_{ji}^\dagger,\quad U_{ii}=I_2.
$$

这不采用第124章的另一赋值，也不采用第128章的 $p+q=1$ 四态合同。每轮仍是第130章的同一个分支 $K_{ji}=\sqrt{P_{ij}}|j\rangle\langle i|\otimes U_{ji}$，使用新准备的十五维正交边记录及其明列的实际读取权限。起点已知且固定为 $0$；$N\ge0$ 是公开指定的有限轮数。输入 $\varrho_{KR}$ 任意，$K=\mathbb C^2$ 携带未知量子信息，$R$ 是任意未触及参考，不提供给控制器或解码器。固定根准备、轮数、记录保持和读取均按定义130.1供应，不由编码取得。

**定义 178.2（三个输出接口与全部记录的配对）。** 令 $\mathcal H_N(0)$ 为全部正概率固定根路径 $h=(0,i_1,\ldots,i_N)$，保持所有自环、支叶访问和次序。定义

$$
p_h=\prod_{t=1}^{N}P_{i_{t-1}i_t},\qquad
U_h=U_{i_Ni_{N-1}}\cdots U_{i_1,0},\qquad
|r_h\rangle=\bigotimes_{t=1}^{N}|i_{t-1}\to i_t\rangle.
$$

不同 $h$ 的 $r_h$ 正交。零轮只有 $h=(0)$，$p_h=1,U_h=I_2$，记录为空张量的单位标量。未迹掉环境的纯等距输出为

$$
S_N\psi=\sum_{h\in\mathcal H_N(0)}\sqrt{p_h}\,
|i_N\rangle\otimes U_h\psi\otimes|r_h\rangle.
\tag{178.1}
$$

它是同一 $V_{\rm edge}$ 的新记录迭代，不是独立选取路径权重。$S_N(K)$ 是实际指定准备的二维像；这里没有供应独立的任意 $|h\rangle\otimes\psi$ 输入。

第130章的记录就是有序边张量。若另有实际供应的历史副本 $|h\rangle_H$，如第125章的历史—环境配对，下面的纯像重编码必须同时访问 $H$ 与全部边记录，逐项使用 $|r_h^{\rm all}\rangle=|h\rangle_H\otimes|r_h\rangle$；多个副本同样全部纳入。该规则保持原逐历史配对，不把两个记录副本分别压缩后任意相配。已经读出、复制到不可访问指针或迹掉的记录，不能被当作仍可相干访问。此时应使用实际所得通道，不能用 (178.1) 宣称已撤销读出。

方形正向 $0\to1\to2\to3\to0$ 的电流增量为 $+1$，反向为 $-1$，自环及支边为零。记 $B(h)=(i_N,W(h))$，$\mathcal B_N=B(\mathcal H_N(0))$，并令

$$
\Pi_N(\beta)=\sum_{h:B(h)=\beta}p_h,\qquad
T_N(j)=\sum_{h:i_N=j}p_h=(P^N)_{0j}.
$$

标签写为 $\beta=(j,w)$，区别于 Pauli 原子 $b$。复用 (131.3)，令

$$
(d_0,d_1,d_2,d_3,d_4)=(0,1,2,3,0),\qquad
(G_0,G_1,G_2,G_3,G_4)=(I,a,-b,-c,b),
$$

$$
\sigma_\beta=(-1)^{(w-d_j)/4},\qquad U_\beta=\sigma_\beta G_j,
\qquad U_h=U_{B(h)}.
\tag{178.2}
$$

指数在可达标签上为整数，负整数同样按奇偶取符号。固定根的实际路径分支算子为 $A_h=\sqrt{p_h}|i_N\rangle\otimes U_h$，且 $A_h^\dagger A_h=p_hI_2$，所以路径概率与任意内部—参考输入无关。按任务或端点归并这些实际分支后，得到两种密度输出：

$$
\begin{aligned}
\Phi_{B,N}(A)
&=\sum_{\beta=(j,w)\in\mathcal B_N}\Pi_N(\beta)
|\beta\rangle\langle\beta|_B\otimes|j\rangle\langle j|_{\mathcal C}
\otimes U_\beta A U_\beta^\dagger,\\
\Phi_{T,N}(A)
&=\sum_{j:T_N(j)>0}T_N(j)|j\rangle\langle j|_{\mathcal C}
\otimes G_j A G_j^\dagger.
\end{aligned}
\tag{178.3}
$$

两式的输入域都是整个 $M_2(\mathbb C)$；与 $\operatorname{id}_R$ 张量后给对应参考接口。第一式的 $B$ 是真正经典、对角的任务记录；$\mathcal C$ 是冗余但明确保留的端点，内部密度及其参考关联也保留。它由原历史仪器对实际 $h$ 作经典后处理 $h\mapsto B(h)$ 得到。第二式迹掉全部历史，只保留端点和内部密度；它等于 $\mathcal E^N\circ\iota_0$，$\iota_0(A)=|0\rangle\langle0|\otimes A$，不是输入域为整个 $M_{10}$ 的 $\mathcal E^N$。保留所有纯记录的 $\operatorname{Ad}_{S_N}$ 则是第三个接口，不能与这两个混合输出混为同一问题。

**定理 178.3（全部轮数的精确可达任务支持）。** 对每个 $N\ge0$，

$$
\mathcal B_N=
\{(j,w):j\in\{0,1,2,3\},\ w\equiv j\pmod4,\ |w|\le N\}
\ \cup\
\{(4,4k):k\in\mathbb Z,\ 4|k|+1\le N\}.
\tag{178.4}
$$

每个列出的标签在整个严格参数域中有正质量，不排除 $p=q$。

证明（178.3）。路径的净方形步数为 $W$。每条方形步改变 $d$ 模四恰为该步的电流增量；支边两端 $d$ 都为零，自环不改变它。沿路径相加，得到 $W\equiv d_{i_N}\pmod4$。每步电流绝对值至多一，故 $|W|\le N$。若终点为支叶 $4$，至少有一次 $0\to4$，这一步不添电流；于是 $|W|+1\le N$，且 $W$ 为四的倍数。这证明必要性，允许此前任意次数的支叶访问和自环。

反向，给定方形标签 $(j,w)$，从根沿正方形走 $w$ 步（$w\ge0$），或沿反方形走 $-w$ 步（$w<0$）。终点恰为 $w\bmod4=j$，电流恰为 $w$，长度 $|w|$。在该终点追加 $N-|w|$ 次自环，即得指定轮数路径。$w=0$ 时先取空路，再以根自环补齐。

给定支叶标签 $(4,4k)$，先作同方向的 $4|k|$ 步方形闭路回根，再走 $0\to4$，最后在支叶补 $N-4|k|-1$ 次自环。$k=0$ 时只需进入支叶。每个使用的边在本参数域中严格为正，所以构造的路径权重严格为正；对全部合法路径求和给 $\Pi_N(\beta)>0$。路径的其他实现仍留在原纤维中，没有用这组短路代表替换它们的权重或记录。$\square$

**推论 178.4（精确标签数、位数和端点支持）。**

$$
C_0=1,\qquad
C_N=2N+2+2\left\lfloor\frac{N-1}{4}\right\rfloor
=2N+2\left\lceil\frac N4\right\rceil\quad(N\ge1),
\tag{178.5}
$$

$$
L_N=\lceil\log_2 C_N\rceil,\qquad
\mathcal J_0=\{0\},\quad \mathcal J_1=\{0,1,3,4\},\quad
\mathcal J_N=\{0,1,2,3,4\}\ (N\ge2).
\tag{178.6}
$$

这里 $\mathcal J_N=\{j:T_N(j)>0\}$。$C_N$ 是完整任务字母表大小，$L_N$ 是存这个字母表的最小固定二进制长度；它们不计已经额外保留的控制、时钟或未知内部态。

证明（178.4）。每个整数 $w\in[-N,N]$ 恰给一个方形终点，故方形标签恰有 $2N+1$ 个。$N\ge1$ 时支叶的 $k$ 从 $-\lfloor(N-1)/4\rfloor$ 到正的同一端点，恰有 $2\lfloor(N-1)/4\rfloor+1$ 个。相加得到第一式；对整数 $N\ge1$，$\lfloor(N-1)/4\rfloor+1=\lceil N/4\rceil$。$N=0$ 的支叶集为空，方形只有 $(0,0)$。

一个无损记录须把所有正质量的不同 $B$ 返回区分，少于 $C_N$ 个码无法精确返回整个标签。固定 $L$ 位至多有 $2^L$ 个码，给必要性；逐标签编号给达到。若端点已作为另一个计费载体保留，额外记录可按各端点条件重算，不把那种条件成本称为完整 $B$ 的 $L_N$。端点集合由 (178.4) 投影得出：第二个方形顶点 $2$ 首次在两步可达，其余四个在一步可达；之后正自环补齐全部长度。$\square$

**定义 178.5（不独立择取的精确权重）。** 本章始终使用原仪器的 $\Pi_N$。其全范围计算复用 (134.1)，初始化为 $\Pi_0(j,w)=\mathbf1_{j=0,w=0}$。也可用同一边的 Laurent 矩阵

$$
P(z)=\begin{pmatrix}
\delta&pz&0&qz^{-1}&r\\
qz^{-1}&\epsilon&pz&0&0\\
0&qz^{-1}&\epsilon&pz&0\\
pz&0&qz^{-1}&\epsilon&0\\
r&0&0&0&\zeta
\end{pmatrix},\qquad
\Pi_N(j,w)=[z^w](P(z)^N)_{0j}.
\tag{178.7}
$$

展开矩阵乘法时，每个中间指标就是一次实际边接续；系数为该路径的 $p_h$，幂指数为该路径的 $W$。所以此式不遗漏支边、自环或重复访问，并与原递推相同。$z=1$ 得 $T_N(j)=(P^N)_{0j}$，行归一化给 $\sum_\beta\Pi_N(\beta)=1$。本式在有限 Laurent 多项式环中使用，没有随机酉或独立边缘模型的替换。

**定理 178.6（经典任务通道的最小纯环境）。** 对 (178.3) 指定的整个任务输出接口，最小纯初始环境维数恰为 $C_N$。其占用输出空间为 $2C_N$ 维，嵌入明确保留的 $B\otimes\mathcal C\otimes K$ 后下界和达到仍相同。这与仅写一个具有相同经典概率的相干输出不同。

证明（178.6）。令 $F_B$ 有正交基 $f_\beta$，定义

$$
V_{B,N}\psi=
\sum_{\beta=(j,w)\in\mathcal B_N}\sqrt{\Pi_N(\beta)}
|\beta\rangle_B\otimes|j\rangle_{\mathcal C}\otimes
U_\beta\psi\otimes f_\beta.
\tag{178.8}
$$

因 $U_\beta$ 酉且质量和为一，$V_{B,N}^\dagger V_{B,N}=I_2$。迹掉 $F_B$ 正好得到 (178.3) 的第一式，故有 $C_N$ 维达到。相同等式与 $I_R$ 张量，保留全部未知内部—参考输入。

下界应用标准有限维 Kraus/Choi/Stinespring 供应结果，具体形式为 Watrous 的定理2.22、推论2.27。这里的矩形 Kraus 算子为

$$
A_\beta=\sqrt{\Pi_N(\beta)}\,|\beta\rangle_B\otimes|j\rangle_{\mathcal C}\otimes U_\beta,
\qquad
J(\Phi_{B,N})=\sum_\beta|\operatorname{vec}A_\beta\rangle
\langle\operatorname{vec}A_\beta|.
$$

不同 $\beta$ 的向量因保留的经典输出标签而正交，每个范数平方为 $2\Pi_N(\beta)>0$。因此 Choi 秩恰为 $C_N$。任何纯环境维数 $m$ 的实现最多有 $m$ 个环境基分量作为 Kraus 算子，故 $m\ge\operatorname{rank}J=C_N$。这是同一个已指定通道的下界，允许任意内部态和参考，并非针对某个输入态的输出秩估计。$N=0$ 时它给一维环境；此时通道只是固定标签附加到未知内部态上。$\square$

**定理 178.7（末端通道的最小纯环境）。** 指定的固定根末端通道满足

$$
\min\dim F_T=|\mathcal J_N|=
\begin{cases}1,&N=0,\\4,&N=1,\\5,&N\ge2.\end{cases}
\tag{178.9}
$$

证明（178.7）。取 $F_T$ 中的正交基 $g_j$，定义

$$
V_{T,N}\psi=\sum_{j\in\mathcal J_N}\sqrt{T_N(j)}
|j\rangle_{\mathcal C}\otimes G_j\psi\otimes g_j.
\tag{178.10}
$$

行质量和一给等距，环境迹给 (178.3) 的第二式。其 Kraus 算子 $A_j=\sqrt{T_N(j)}|j\rangle\otimes G_j$ 因不同输出端点而 Hilbert–Schmidt 正交，向量化后的范数平方为 $2T_N(j)>0$。故 Choi 秩为 $|\mathcal J_N|$，同一纯环境下界达到。用 (178.6) 得三种数值。

中心符号在每个 $U_h A U_h^\dagger$ 中相消，所以同端点的所有历史确可合到这个 Kraus 方向。相消只发生在这个密度通道的历史遗忘中；在 (178.1) 的纯输出中不能删去它。$p=q$ 或其他严格域内的参数等式不使正质量的输出端点或任务标签消失，因此不降低任一上述 Choi 秩。$\square$

**命题 178.8（未知逻辑信息和参考的完整保留）。** 两个通道都存在数学 CPTP 左逆恢复整个内部输入。经该左逆，任意 $\varrho_{KR}$ 及其参考关联保持。若全部内部量子信息必须通过同一个有限经典 flag 加 $d_{\rm port}$ 维量子端口，且没有原输入、预共享纠缠或量子旁路，则精确恢复要求 $d_{\rm port}\ge2$；二维护持 $K$ 达到。

证明（178.8）。对末端输出定义

$$
\mathcal L_T(X)=\sum_{j=0}^4 G_j^\dagger
(\langle j|X|j\rangle)G_j,
\qquad \mathcal L_B=\mathcal L_T\circ\operatorname{Tr}_B.
$$

这些矩形 Kraus 分量的平方和为输出单位，故是 CPTP。代入 (178.3)，每项恢复 $A$ 乘对应质量，全部质量和为一，得 $\mathcal L_T\Phi_{T,N}(A)=A$ 和 $\mathcal L_B\Phi_{B,N}(A)=A$。全部式在 $M_2$ 上成立，与 $\operatorname{id}_R$ 张量便是联合恢复，不需估计或读取未知内部态。这是第132章移动逻辑块在固定根及本输出接口上的使用；实际 $G_j^\dagger$ 控制仍须供给。

若 $d_{\rm port}=1$，有限 flag 端口只是经典通信。每个编码分支给一个正线性泛函，每个解码分支准备固定态，复合为测量—准备通道。作用于 $K$ 与二维参考的 Bell 态时，其输出是系统—参考乘积态的凸组合，因此可分；随后任何仅系统上的 CPTP 左逆仍可分，不能恢复原来纠缠的 Bell 态。这与上述精确参考恢复矛盾。$d_{\rm port}$ 是正整数，故至少为二。反向完整保留 $K$ 即可，经典标签及各自环境另计。$\square$

**定理 178.9（原记录中的加权任务纤维与相位正确的端点方向）。** 定义同一实际记录空间内的单位向量

$$
\tau_\beta=\frac1{\sqrt{\Pi_N(\beta)}}
\sum_{h:B(h)=\beta}\sqrt{p_h}|r_h\rangle,
\qquad
\eta_j=\frac1{\sqrt{T_N(j)}}
\sum_{h:i_N=j}\sqrt{p_h}\,\sigma_{B(h)}|r_h\rangle.
\tag{178.11}
$$

分别在可达 $\beta$ 和 $j$ 上定义。$\{\tau_\beta\}$ 是 $C_N$ 个正交单位方向，$\{\eta_j\}$ 是 $|\mathcal J_N|$ 个正交单位方向，且

$$
\eta_j=\sum_{\beta=(j,w)}
\sqrt{\frac{\Pi_N(\beta)}{T_N(j)}}\,\sigma_\beta\tau_\beta,
$$

$$
S_N\psi=
\sum_{\beta=(j,w)}\sqrt{\Pi_N(\beta)}
|j\rangle\otimes U_\beta\psi\otimes\tau_\beta
=\sum_{j\in\mathcal J_N}\sqrt{T_N(j)}
|j\rangle\otimes G_j\psi\otimes\eta_j.
\tag{178.12}
$$

证明（178.9）。原 $r_h$ 的两两正交使同纤维范数平方为该纤维质量；不同任务纤维或端点纤维支撑不交，故方向正交。代入 (178.2) 再按 $B$ 或端点分组给两个等式。符号只在 $\eta_j$ 的相干和内出现，同任务纤维中是同一 $\sigma_\beta$，在 $U_\beta$ 中保留。正负闭路不会使某个向量的范数抵消，因为它们伴随不同的正交历史记录。

若有额外历史副本，所有式逐项改用定义178.2的 $r_h^{\rm all}$，证明仍成立，但操作域变成所有这些记录的联合空间。只访问其中一个而迹掉另一个时，交叉历史块被消去，不能据此假定仍保留这里的纯 $\eta_j$；单路径纤维等退化情形须按实际输出单独判断。$\square$

**命题 178.10（准备像上的三种重编码及其作用域）。** 下列映射都是有限维数学等距，不供应原生门、记录擦除或初始化。

第一，在 $\operatorname{span}\{\tau_\beta\}$ 上定义 $Q_B\tau_\beta=|\beta\rangle$。它把 (178.12) 的第一式变成相干标签输出，保留正确 $U_\beta$ 和原纤维的全部权重；这个输出还不是经典 $\Phi_{B,N}$。若先在原记录上以保持记录的等距追加任务副本 $|r_h\rangle\mapsto|B(h)\rangle_B\otimes|r_h\rangle$，再用 $Q_B$ 重编码余记录（目标基改记为 $f_\beta$），则输出恰为 (178.8)。迹掉该余记录才给经典任务通道。

第二，在 $\operatorname{span}\{\eta_j\}$ 上定义 $Q_T\eta_j=g_j$。它把 (178.12) 的第二式变成 (178.10)，所以原仪器的整个指定纯准备族确与最小末端 dilation 相联系，逐输入和逐参考保持相干。未复制任务标签的原记录约化态为

$$
\operatorname{Tr}_{\mathcal C K}(S_N\varrho_KS_N^\dagger)
=\sum_{j\in\mathcal J_N}T_N(j)|\eta_j\rangle\langle\eta_j|.
\tag{178.13}
$$

因此它的支持维数恰为 $|\mathcal J_N|$。任何只在记录上作等距、保持这个准备族的重编码都不能用更小的记录载体；$Q_T$ 达到。若已相干追加任务副本，余记录态则为 $\sum_\beta\Pi_N(\beta)|\tau_\beta\rangle\langle\tau_\beta|$，其支持恰为 $C_N$，不能用前一个支持维数替代。

第三，整个 $S_N(K)$ 只有二维。以第132章的共同框架

$$
D=\sum_j|j\rangle\langle j|\otimes G_j^\dagger
$$

作用于系统，得到（按张量次序识别）

$$
(D\otimes I)S_N\psi=\xi_N\otimes\psi,
\qquad
\xi_N=\sum_h\sqrt{p_h}\,\sigma_{B(h)}
|i_N\rangle\otimes|r_h\rangle.
\tag{178.14}
$$

$\xi_N$ 是固定单位向量，与未知输入无关。若允许同时访问配置及全部记录，则在这一个准备像上取 $S_N\psi\mapsto\psi$ 是等距，逆为 $\psi\mapsto S_N\psi$；等价地可把固定 $\xi_N$ 送到一个指定单位向量。这个二维像不等于环境因子维数的最优值。

证明（178.10）。前两映射把正交单位组送到正交单位组，故在线性张成空间上保持内积；代入 (178.12) 得所列输出。追加任务副本后，任务副本的正交标签使不同 $\beta$ 的交叉项在余记录约化中消失，得到 $C_N$ 个正方向；未追加时，端点正交使不同 $j$ 消失，内部酉共轭后的密度态迹为一，给 (178.13)。等距不能降低这些正交支持的维数。

原等距满足 $S_N^\dagger S_N=I_2$，故像恰二维；框架共轭消去 $G_j$，直接给 (178.14)，$\|\xi_N\|^2=\sum_hp_h=1$。上述等距可通过补正交基延拓到足够大的环境或共同载体；若采用较小输出因子，需要把输入支持之外的方向留在另一个残余载体。这种延拓没有把整个记录空间压进较小维数，也没有把所有独立 $r_h$ 变成同一个任务标签。

全部重编码的定义依赖已指定 $N,p,q,r$、原相位和联合记录保持。物理实施须供给相应共同相干访问、精确准备、控制、维持及逆；这些没有由等距存在得到。$\operatorname{Ad}_{S_N}$ 将全部记录作为输出保留，本身的 Choi 秩为一，外部纯环境可为一维；这是第三个输出合同的事实，不反驳经典任务通道的 $C_N$ 或末端通道的 (178.9)。$\square$

**命题 178.11（遗忘与后验重采样只恢复边缘通道）。** 对任意 $N$，$\operatorname{Tr}_B\Phi_{B,N}=\Phi_{T,N}$。存在一个仅用末端输出的 CPTP 后处理 $\mathcal R_N$，使 $\mathcal R_N\Phi_{T,N}=\Phi_{B,N}$；它按实际源权重的后验重新生成标签，不恢复某次运行已经取得而后来丢弃的 $B$ 或 $h$。

证明（178.11）。在第一通道中 $\sigma_\beta$ 于密度共轭相消，对同端点求和得 $T_N(j)$，故得到遗忘等式。对 $j\in\mathcal J_N$，令 $\beta_j(\beta)=\Pi_N(\beta)/T_N(j)$，其中 $\beta=(j,w)$。这是正的归一化后验，且与未知内部输入及参考无关。对任意末端矩阵 $X$ 取对角内部块 $X_{jj}=\langle j|X|j\rangle$，定义

$$
\mathcal R_N(X)=
\sum_{j\in\mathcal J_N}\ \sum_{\beta=(j,w)}
\beta_j(\beta)|\beta\rangle\langle\beta|_B
\otimes|j\rangle\langle j|_{\mathcal C}\otimes X_{jj}.
\tag{178.15}
$$

在可达端点直接和上这是 CPTP。要在全部 $M_{10}$ 上定义，对不可达 $j$ 的块追加 $|\beta_0\rangle\langle\beta_0|\otimes|0\rangle\langle0|\otimes X_{jj}$，其中 $\beta_0=(0,0)$ 始终可达。这些补项在 $\Phi_{T,N}$ 的像上为零。每个分量都有明确矩形 Kraus 算子，概率和一，输入端点非对角块被删除，故整个扩展 CPTP。代入末端通道，$T_N(j)\beta_j(\beta)=\Pi_N(\beta)$，且 $U_\beta A U_\beta^\dagger=G_jAG_j^\dagger$，得到通道等式，对全部参考同样成立。

这项等式比较从同一未知输入产生的边缘输出，不比较附有实际过去标签的联合律。后验生成需要额外随机制备或纯环境及输出载体；其存在不供给那个操作。两个接口关于未知逻辑输入可以彼此后处理，而纯环境成本仍不同，因为输出经典随机关系及所迹环境也不同。$\square$

**命题 178.12（两步实际路径的相同末态、不同任务与不同误配率）。** 对全部严格参数，包括 $p=q$，原仪器的两条实际路径

$$
h_+=(0,1,2),\qquad h_-=(0,3,2)
$$

有正权重 $p^2,q^2$，任务标签 $(2,2),(2,-2)$，运输分别为 $ca=-b$、$ac=b$。它们对每个内部—参考密度输入给同一条件末端输出。因此任何仅末端的操作都不能在这两个实际来源上确定返回原来的不同 $B$。

给定终点 $2$ 后，以 (178.15) 独立重采样的 $B'$ 与原来实际 $B$ 的误配概率分别为

$$
\Pr(B'\ne B\mid h_+)=\frac{q^2}{p^2+q^2},\qquad
\Pr(B'\ne B\mid h_-)=\frac{p^2}{p^2+q^2}.
\tag{178.16}
$$

按原后验平均、条件于终点 $2$ 的误配率为

$$
\Pr(B'\ne B\mid i_2=2)=\frac{2p^2q^2}{(p^2+q^2)^2}.
\tag{178.17}
$$

其对所有运行的误配率的终点 $2$ 贡献才是 $2p^2q^2/(p^2+q^2)$；这个贡献不包含其他终点的误配。

证明（178.12）。由同一边权重相乘和运输相乘即得两条路径的值。两步从根到 $2$ 只能经 $1$ 或 $3$，所以 $T_2(2)=p^2+q^2$，后验恰为 $p^2/(p^2+q^2)$ 和 $q^2/(p^2+q^2)$。$(-b\otimes I_R)\varrho_{KR}(-b\otimes I_R)^\dagger=(b\otimes I_R)\varrho_{KR}(b\otimes I_R)^\dagger$，给相同末态。若一个通道对同一输入密度返回两个不同确定标签，就违反映射的单值性，故实际标签不能这样恢复。

在具体来源 $h_+$ 上，猜到另一标签的概率是第二后验；$h_-$ 同理，得到 (178.16)。再按两个源后验加权，得 $2[p^2/(p^2+q^2)][q^2/(p^2+q^2)]$，其分母平方不能漏掉。乘终点事件概率 $p^2+q^2$ 才得到未条件贡献。$p=q$ 时两个具体来源误配率和条件平均都为 $1/2$；平稳似然量此时为零，但 $B$ 与实际路径仍不同。$\square$

**例 178.13（空轮、首轮、二轮和首次非零支叶标签）。** 空轮只有 $(0,0)$，两个密度通道都是固定标签附加到内部恒等，两个最小纯环境均为一维。首轮为

$$
\begin{array}{c|cccc}
\beta&(0,0)&(1,1)&(3,-1)&(4,0)\\\hline
\Pi_1(\beta)&\delta&p&q&r
\end{array}
$$

所以任务和末端最小纯环境此时同为四。二轮的全部六项为

$$
\begin{array}{c|c}
\beta&\Pi_2(\beta)\\\hline
(0,0)&\delta^2+2pq+r^2\\
(1,1)&p(\delta+\epsilon)\\
(3,-1)&q(\delta+\epsilon)\\
(4,0)&r(\delta+\zeta)\\
(2,2)&p^2\\
(2,-2)&q^2
\end{array}
$$

每行按全部实际中间点求和得到；总和为一，不丢弃 $0\to4\to0$ 或自环。此时任务环境六维、末端环境五维。四步方形正、反闭路有 $W=\pm4$、运输均为 $-I$，权重 $p^4,q^4$；根自环四次则为 $I$、权重 $\delta^4$。这些不同历史在纯加权记录中各留原符号。非零支叶标签 $(4,\pm4)$ 首次在 $N=5$ 出现，取相应四步闭路再进入支叶，权重分别为 $p^4r,q^4r$；此前支叶只有 $(4,0)$。更一般 $(4,\pm4k)$ 首次在 $4k+1$ 轮出现，$k\ge1$。

取 $p=1/4,q=r=1/8$，二轮终点 $2$ 的质量为 $5/64$，两个具体来源的误配率为 $1/5,4/5$，条件平均为 $8/25$，未条件的该终点贡献为 $1/40$。取 $p=q=1/8,r=1/4$，这些量分别为 $1/32$、$1/2,1/2$、$1/2$、$1/64$。它们只是公式的参数实例，不代替全范围证明。

**边界 178.14（任意相干历史域与资源分型）。** 第134章的独立全历史输入仍是

$$
\operatorname{span}\{|h\rangle:h\in\mathcal H_N(0)\}\otimes K,
\qquad |h\rangle\psi\longmapsto|B(h)\rangle U_h\psi\otimes r'_h.
$$

其同任务纤维内的正交残差下界 (134.3)–(134.4) 直接复用，不把它重新作为本章成果。与之不同，(178.1) 只在每个未知 $\psi$ 上供应一个已经指定的加权组合；$Q_B,Q_T$ 对这个准备合同的重编码不必对所有独立历史基给相同小记录输出，也没有建立那种全域延拓。反过来，五维末端 dilation 只给指定末端通道，不能保存已经丢弃或根本未供给的过去历史。

各数值属于以下不同输出和计费单位：

| 178 的对象与合同 | 精确值 | 计入的量 |
| --- | --- | --- |
| 实际完整任务标签 $B$ 的可达像 | $C_0=1$；$C_N=2N+2\lceil N/4\rceil$ | 可区别经典字母数 |
| 完整 $B$ 的固定二进制编码 | $\lceil\log_2C_N\rceil$ | 标签位数 |
| 未知内部—参考的精确量子端口 | $2$ | 内部量子载体维数 |
| 指定经典 $B$ 加内部输出的纯环境 | $C_N$ | 整个该通道的辅助输出维数 |
| 指定末端输出的纯环境 | $1,4,5$，按 $N=0,1,\ge2$ | 整个末端通道的辅助输出维数 |
| 完整纯准备像 $S_N(K)$ | $2$ | 输入信息子空间维数 |
| 完整记录也保留为输出的 $\operatorname{Ad}_{S_N}$ | $1$ | 额外纯环境维数 |

纯环境下界包含一切不在已声明输出中的辅助系统；额外随机 flag、混合初始环境的纯化或测量指针不能藏在计费之外。经典 $B$ 的输出本身与使它真正对角的环境是不同载体。控制器完整状态数、程序表、精确参数表示、轮数或结束标记、初始化、时钟、读写、保持寿命、物理制备和擦除费用不由这个表给出。若实际输出还保留来源、标定或其他事件字段，应把它们纳入新的接口；本章不把 $B$ 称为所有实际未来菜单的最小记录。

## 178.99. 供应范围与仍未建立的实际桥

本章在固定版本的普通论文陈述中使用：第130章同一十五边正交记录仪器、初始化和逐路径权重；第131章逐边相位因子化；第132章完整逻辑因子及参考保持；第134章任务更新、具名平稳比较量和独立全历史域下界。精确支持 (178.4)–(178.5)、固定根两通道的 Choi 方向、原记录中的加权方向和后验误配是这些供应结果在本合同内的具体连接，不以检索未命中作全球原创性证据。

比较源 [RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS，同一固定版本，第1–7章](https://github.com/the-omega-institute/trureturing/blob/c32e033a62a0a4a3bd63ab6b7af1d1ea59059651/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS.md) 优化的是完整十维输入上不同的单轮未读或边可读合同，得到 $2,4,15$，并给 $4^N$ 有序记录加末端的全路径上界。它的 $V_2,V_4$ 未读通道不是本章指定的正交边通道；不能用其较小维数替换本章仪器。其第7.4–7.5条保留独立历史域与有限历史最优值的边界，本章只解决所列固定根任务和末端合同。

比较源 [RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY，同一固定版本，第1–5章](https://github.com/the-omega-institute/trureturing/blob/c32e033a62a0a4a3bd63ab6b7af1d1ea59059651/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md) 的来源是 $\mathbb C^5$ 上的指定等待和五个秩一模式读，其首读约化依赖秩一坍缩；这里每条边保留任意 $\mathbb C^2$ 内部输入，合同不同。该源的端口 minimax 常数不进入本章。本卷第168–177章的面积位置、五量及三阶签名另有正叶路径和操作菜单，未把它们识别为此处的 $W$ 或边记录。

有限维通道工具采用 John Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018，[第2章，定理2.22、推论2.27及 §2.5](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)：输入与输出为有限复 Euclidean 空间，Choi 使用未归一化 $\operatorname{vec}(I)$，完全正算子和与环境等距表示匹配，最小 Kraus 数及纯环境维数为 Choi 秩。本章所有 Choi 秩计算均依这一约定；归一化 Choi 只乘正标量，不改变秩。其原始供应出处分别为 M.-D. Choi, [“Completely positive linear maps on complex matrices”, *Linear Algebra and its Applications* 10 (1975), 285–290](https://doi.org/10.1016/0024-3795(75)90075-0)；K. Kraus, [“General state changes in quantum theory”, *Annals of Physics* 64 (1971), 311–335](https://doi.org/10.1016/0003-4916(71)90108-4)；W. F. Stinespring, [“Positive functions on $C^*$-algebras”, *Proceedings of the American Mathematical Society* 6 (1955), 211–216](https://doi.org/10.1090/S0002-9939-1955-0069403-4)。这里复用其成熟有限维结论，不另交付一般 Kraus、Choi 或 Stinespring 定理；本章陈述和证明均为普通数学，未声称 Lean 核验。

固定根和严格正参数是本章的边界。任意相干初始配置、多根初始化、零概率边或任意完整控制历史，不由这些数值直接运输。$W\log(p/q)$ 仍只表示第134章限制到固定根的具名平稳正反比较量，不是 $\delta_0$ 起始律自身的倒序似然；$p=q$ 时该量为零不合并实际 $W$ 标签。未知内部态、未触及参考和原 Pauli 相位没有被经典标签替换。

仍需的实际桥是：在所供原生菜单中取得并维护这些边权、内部运输、新纯记录、相位参照与所需共同记录访问；合法实现加权重编码、经典后验制备、联合逆和任何档案擦除；在控制、标定、钟及允许未来任务也计费时证明相应最小资源。本章没有供给新的 native port、任意相位门、复位、免费时钟或历史访问，没有热力学或空间维数结论，也没有给出任意独立相干历史输入上的新压缩最优值或无界固定总预算。

## 追加锚（本行以下为增补区）
