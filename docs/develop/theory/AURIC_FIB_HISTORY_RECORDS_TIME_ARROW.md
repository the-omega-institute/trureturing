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
