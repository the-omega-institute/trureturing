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
