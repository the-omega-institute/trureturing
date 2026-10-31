# AURIC：二元关系的酉表示与黄金门通用性

从完整三轴编码到内部记录与原生有限门字

定义、定理与纸面证明　v37.0  
2026 年 10 月 31 日　Asia/Singapore

原稿作者元数据：AURIC research continuation。  
原稿主题元数据：Binary positive relations, exact five-mode unitary representation, endogenous records and encoded golden-gate universality。

> 转写说明：本文完整转写所供 XeLaTeX 原稿，保留原稿的版本、日期、历史作者陈述、证明与固定来源。原稿数学宏在各公式中展开，原标签保留为显式锚点；字号、字体、页眉页脚与分页指令改由 Markdown 阅读器排版。原稿编译提示为 XeLaTeX、编译两次，`AURICFontPath` 可指向 Noto CJK OTF 目录。原稿 SHA-256：`05c8f0af8f01014c582699e94cdf359a2e0e6d4e0e8c2022685e78845a683eb9`。作者所说“本轮未执行”等仅指原稿写作轮；文末编者校核注与作者原文分列。

## 摘要

本稿研究“二元概念、关系与归一化是否就是保持酉性的 AURIC 单元，并因而成为通用量子门”。 在明确的复正关系接口下，非零二阶 Gram 矩阵恰由尺度与 Bloch 球完整表示。 本文给出一个固定的五模式等距编码，使原三个占据均值成为同增益、正交标定的完整 qubit 读口； 其像是原金字塔内的圆球，五个同尺度矩满足线性式
$N-X-Y-Z-2\kappa=0$，故任意四项稳定恢复第五项，误差也继承同一线性关系。
全部数学 $U(2)$ 门忠实提升为五模式酉门，并在该球上表现为刚性旋转。 随后证明内部记录的酉扩张、经典读出的信息范围、算子值二元关系的递归完备性。 原生通用性另由项目已有固定黄金门承担：给出其投影、相位、有限阶性质及双地址单比特密度证明， 再沿当前 Jones–Wenzl 桥推广为可扩展编码上的近似通用性。 同一原七地址还可在十三维载体内、准确保留码上相位，近似编译本文新的三轴编码及其全部逻辑门。 可和的酉实现误差则给相对误差门的绝对收敛级数与酉极限。 最后接入本轮新增的旧终端全效果覆盖与统计相容接口。 所有参考、程序、记录与辅助角色均在同一静态整体内部；表示、生成、统计标定及实际取得分别陈述。

<a id="section-1"></a>

## 1. 固定来源、对象类型与本轮结论

本轮固定项目 `dev` 提交为

`3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e`，

时间为 2026-10-31 04:01:27（新加坡），比较基线为 v36 的

`38076d7a280e0e8186c3d5507e3dea59b6d4803c`。

相关五模式、v15 黄金门、v28 二元读出及续卷 II 的原生十三维密度桥保持不变； 本轮直接相关增量是续卷 II 新增的 §§121–125。［[head](#ref-head)，[v15](#ref-v15)，[v28](#ref-v28)，[continuation](#ref-continuation)］

继续固定唯一静态整体 $(\mathcal A,\omega)$。本稿的 Hilbert 子空间、张量因子、程序、记忆与参考， 都表示该整体内部的角色。有限字索引表示内部组合次序，不引入整体外的时钟。 复 Hilbert 结构、正关系、可调用算符、Born 或全效果概率接口分别按其实际使用位置声明。 原五模式数量及总概率一，单独不推导这些附加结构。

全文区分四种结论：数据的完整表示、保持内积的数学门、指定菜单的通用生成、 以及实际取得这些数据和门的协议。项目已经有明确的黄金门通用性纸面定理； 本文不将它降格为一个尚无具体矩阵的猜想，也不把既有稿件入库当作独立形式认证。 本轮只作源码读取、普通证明与文稿排版，未执行 Lean、CAS、数学数值求值或门字搜索。

距离约定为 $D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$ 与
$\operatorname{TV}(p,q)=\tfrac12\|p-q\|_1$。
通道的参考稳定距离为

$$
d_{\rm ref}(\Phi,\Psi)=
\sup_{R,\rho}D\bigl((\Phi\otimes\operatorname{id}_R)\rho,(\Psi\otimes\operatorname{id}_R)\rho\bigr),
$$

其中 $R$ 为有限维内部参考角色，$\rho$ 为联合归一态。

<a id="section-2"></a>

## 2. 二元正关系与酉性的准确合同

**定义 2.1（二元复正关系）。**

在固定复相位约定下，对两个向量 $u,v$ 取
$a=\|u\|^2$、$b=\|v\|^2$、$c=\langle v,u\rangle$，内积对第一变量共轭线性。
其关系矩阵为

$$
G=\begin{pmatrix}a&\bar c\\c&b\end{pmatrix}\ge0,\qquad N=\operatorname{Tr} G.
$$

更一般地，本稿直接把非零 $G\in M_2(\mathbb C)_+$ 作为二元正关系接口。

<a id="thm:gram"></a>

**定理 2.2（尺度与三轴的完备表示）。**

非零二元正关系与 $N>0$、$\mathbf r\in\mathbb R^3$、$|\mathbf r|\le1$ 一一对应：

$$
G=\frac N2(I+r_x\sigma_x+r_y\sigma_y+r_z\sigma_z),\qquad
\mathbf r=\frac1N(2\Re c,2\Im c,a-b).
$$

其中 $\sigma_x,\sigma_y,\sigma_z$ 为标准 Pauli 矩阵。 纯态恰对应 $|\mathbf r|=1$，一般正关系给整个闭球。

**证明。**

$\det G=ab-|c|^2=N^2(1-|\mathbf r|^2)/4$，结合两个对角元非负即得正性等价。
逆式逐项恢复 $a,b,c$。每个正矩阵都可分解为 $V^*V$，故可由 $V$ 的两列实现为 Gram 矩阵。 也可在 $a>0$ 时直接取
$u=(\sqrt a,0)$、$v=(\bar c/\sqrt a,\sqrt{b-|c|^2/a})$；
$a=0$ 时正性强制 $c=0$，单独取 $u=0$ 即可。

∎

该定理的适用对象是已具有完整复关系与正性的二元接口。 例如 $a=b=1,c=2$ 虽有正总量，却不满足正性，不能作为量子二元关系。 如果两个概念仅作为独立相位未固定的射线给出，$c$ 的相位还需要共同相干参考。 项目 v28 已证明复二态的 Bloch 表示，并用其它维数球模型说明： 二元、归一化与各向同性本身不单独选择三维。［[v28](#ref-v28)］

<a id="thm:gramunitary"></a>

**定理 2.3（完整 Gram 保持等价于两概念的酉相容）。**

在同一个有限维 Hilbert 空间中，两对向量 $(u_0,u_1)$ 与 $(v_0,v_1)$ 存在共同酉 $U$ 使 $Uu_i=v_i$，当且仅当

$$
\langle u_i,u_j\rangle=\langle v_i,v_j\rangle\quad(i,j=0,1).
$$

**证明。**

必要性是酉性保持内积。反之，将 $\sum_i\alpha_i u_i$ 映到
$\sum_i\alpha_i v_i$；Gram 相同保证零向量映成零向量，故映射良定义，
并保持所有范数与内积。它是两张成子空间间的等距同构，补全两端正交基即得整体酉。

∎

若输入是正交基 $e_0,e_1$，该条件就是两列归一与交叉正交：

$$
\|Ue_0\|=\|Ue_1\|=1,\qquad \langle Ue_0,Ue_1\rangle=0.
$$

因此全部二元酉矩阵恰可写成

$$
U=\begin{pmatrix}
\alpha&-e^{i\gamma}\bar\beta\\
\beta&e^{i\gamma}\bar\alpha
\end{pmatrix},\qquad |\alpha|^2+|\beta|^2=1.
$$

第二列是第一列正交补中的单位向量，只有一个相位自由度，故该式既充分也穷尽。 这把“两份归一读出加完整关系”变成真正的酉性判据；关系约束作用于全部输入的线性组合。

**命题 2.4（非正交概念的关系度量）。**

设 $V=[u\ v]$ 满列秩，$G=V^*V>0$。坐标更新 $z\mapsto Mz$ 在实际概念子空间保持内积，当且仅当

$$
\boxed{M^*GM=G.}
$$

等价地 $G^{1/2}MG^{-1/2}$ 是通常意义的酉矩阵。

**证明。**

实际范数为 $\|Vz\|^2=z^*Gz$。比较更新前后对全部 $z$ 的二次型， 再用极化恒等式即得结论。

∎

逐态归一不能代替该条件。例如 $T=\operatorname{diag}(2,1)$、
$f(\psi)=T\psi/\|T\psi\|$ 总给单位向量，却将
$|\langle e_0,+\rangle|=1/\sqrt2$ 改为 $2/\sqrt5$。
相反，一个固定复线性算子若对全部输入保持范数，则极化给 $T^*T=I$； 同维有限空间上它才是酉算子。

还应区分两种作用。共同作用于概念向量的同一内部载体上的酉满足
$G(Uu,Uv)=G(u,v)$，所以 Gram 描述约去了共同换框。
将 $G/N$ 当作二元标签上的密度矩阵并施加 $W(G/N)W^*$， 则是另一种已声明的标签空间控制，通常改变三轴。 前者的相对关系不变，不能用于识别哪个共同门已经作用。

<a id="section-3"></a>

## 3. 原五模式中的固定正交三轴编码

沿用原模式顺序 $(0,2,3,5,25)=(000,100,010,001,101)$。 低端、高端、中位占据算子依次写作

$$
N_x=\operatorname{diag}(0,1,0,0,1),\quad
N_y=\operatorname{diag}(0,0,0,1,1),\quad
N_z=\operatorname{diag}(0,0,1,0,0).
$$

它们两两对易；原完整经典函数基为 $\{1,x,y,z,xy\}$。 以下新增一个固定编码，保留这些原模式和原读口，不更换它们的定义。［[foundation](#ref-foundation)，[v28](#ref-v28)］

**定义 3.1（固定五效果）。**

置

$$
\nu=\frac1{1+2\sqrt3+\sqrt{11}},\qquad
a_\nu=\frac{\nu(\sqrt3+\sqrt{11})}{2},\qquad
u_0=(a_\nu,a_\nu,\nu).
$$

在 $\mathbb C^2$ 上定义

$$
\begin{aligned}
E_{25}&=\frac\nu2(\sqrt3 I-\sigma_x-\sigma_y-\sigma_z),&
E_0&=3E_{25},\\
E_2&=\frac\nu2(\sqrt{11}I+3\sigma_x+\sigma_y+\sigma_z),\\
E_5&=\frac\nu2(\sqrt{11}I+\sigma_x+3\sigma_y+\sigma_z),\\
E_3&=\nu(I+\sigma_z).
\end{aligned}
$$

<a id="thm:encoding"></a>

**定理 3.2（全部二元正关系的固定 AURIC 编码）。**

上述五个效果均秩一且非负，和为 $I_2$。 存在固定等距 $J:\mathbb C^2\to\mathbb C^5$，满足
$J^*|s\rangle\langle s|J=E_s$。
对任意归一二元正关系 $\rho=(I+\mathbf r\cdot\boldsymbol\sigma)/2$， 其相干编码 $\rho_F=J\rho J^*$ 的原三占据均值恰为

$$
\boxed{u(\rho)=(X,Y,Z)=u_0+\nu\mathbf r.}
$$

因此同一个编码把整个 Bloch 球表示为原金字塔内的一个圆球， 三个原均值经固定仿射标定即可完整恢复 $\rho$。

**证明。**

对 $tI+v\cdot\sigma$，特征值为 $t\pm|v|$。 上述各式的标量系数等于向量系数的范数：
$\sqrt3=\sqrt{1+1+1}$、$\sqrt{11}=\sqrt{9+1+1}$，以及 $1=|e_z|$。
故各效果非零、正且秩一。相加时三个 Pauli 系数抵消， 常数系数为 $\nu(1+2\sqrt3+\sqrt{11})=1$。

写 $E_s=|\eta_s\rangle\langle\eta_s|$，定义
$J\psi=\sum_s|s\rangle\langle\eta_s,\psi\rangle$。
于是 $J^*J=\sum_sE_s=I$，且模式 PVM 的压缩就是 $E_s$。 直接相加给

$$
J^*N_xJ=a_\nu I+\nu\sigma_x,\quad
J^*N_yJ=a_\nu I+\nu\sigma_y,\quad
J^*N_zJ=\nu I+\nu\sigma_z.
$$

取迹得到均值式；反向 $\mathbf r=(u-u_0)/\nu$ 即唯一恢复状态。 因为每个模式概率非负，所得球全部位于原五模式的可见金字塔内。

∎

<a id="cor:distance"></a>

**推论 3.3（三轴的精确稳定标尺）。**

对任意两个编码 qubit 态，

$$
\boxed{
D(\rho,\widetilde\rho)
=D(J\rho J^*,J\widetilde\rho J^*)
=\frac{\|u(\rho)-u(\widetilde\rho)\|_2}{2\nu}.
}
$$

**证明。**

差矩阵为 $(\mathbf r-\widetilde{\mathbf r})\cdot\sigma/2$， 两个特征值是 $\pm|\mathbf r-\widetilde{\mathbf r}|/2$。 等距编码只附加零奇异值，因此保持迹范数。代入均值式即可。

∎

这里的三个压缩效果有偏且不尖锐。原读口仍来自同一个五结果测量， 没有变成三次同时进行的尖锐 Pauli 测量； 仿射恢复期望值也不等于获得一次同时尖锐结果。 这与来源 v28 §6.5 的联合可测性边界相容。 本构造提供一个明确可行的编码，未讨论 $\nu$ 的最优性。 第 8 节进一步给出同一原生菜单中的有限字逼近。

<a id="thm:four"></a>

**定理 3.4（同尺度四推一及误差关系闭合）。**

对任意 $G\ge0$，令
$w_s=\operatorname{Tr}(GE_s)$、$N=\operatorname{Tr} G$，
$X=w_2+w_{25}$、$Y=w_5+w_{25}$、$Z=w_3$、$\kappa=w_{25}$。
这里 $\kappa$ 对应 v36 的联合读数 $K$，与下文黄金门 $K$ 区分。 则

$$
\boxed{N-X-Y-Z-2\kappa=0.}
$$

其完整相容类恰为

$$
\left\{(N,X,Y,Z,\kappa):
\begin{array}{l}
N\ge0,\quad 2\kappa=N-X-Y-Z,\\
\|(X-a_\nu N,\ Y-a_\nu N,\ Z-\nu N)\|_2\le\nu N
\end{array}
\right\}.
$$

该类上任意四个同尺度矩唯一确定第五个，且任意两份相容重建满足

$$
|\Delta\mu_i|\le2\sum_{j\ne i}|\Delta\mu_j|.
$$

若缺失 $\kappa$，可用更小常数 $1/2$。 此外，两份编码结果之差满足完全相同的线性关系。

**证明。**

$E_0=3E_{25}$ 给 $w_0=3\kappa$。
原五模式双基式 $w_0=N-X-Y-Z+\kappa$ 给所述关系。 写 $G=(NI+t\cdot\sigma)/2$，则
$t=\nu^{-1}(X-a_\nu N,Y-a_\nu N,Z-\nu N)$；
$G\ge0$ 恰为 $N\ge0,|t|\le N$，也证明逆向存在性。

关系式的五个系数为 $(1,-1,-1,-1,-2)$，均非零。 故解出任意一个坐标给唯一恢复；取绝对值给常数 $2$， 而解出 $\kappa$ 时全部系数为 $1/2$。 两个关系式相减给相同的误差关系。

∎

这与 v36 的一般五质量独立性并不冲突：这里增加的是同一个固定量子编码， 它精确选定 $w_0=3w_{25}$ 的状态类。 错误位置仍须已知；单项擦除恢复不能自动定位一个未知位置的损坏。 误差质量可正可负，线性关系闭合不把误差变成正概率态。 先归一化再删除原尺度，仍无法从比值恢复任意原总量。

<a id="section-4"></a>

## 4. 编码内的全部数学酉门与三轴刚性旋转

<a id="thm:lift"></a>

**定理 4.1（忠实五模式酉表示）。**

取 $P_J=JJ^*$。对每个 $U\in U(2)$，定义

$$
\boxed{\iota_J(U)=JUJ^*+(I_5-P_J).}
$$

则 $\iota_J(U)$ 酉，且

$$
\iota_J(U)J=JU,\qquad
\iota_J(UV)=\iota_J(U)\iota_J(V).
$$

这是一个单射群表示；对任意内部参考 $R$， 编码 $J\otimes I_R$ 同样保留全部联合态与其相关性。

**证明。**

编码空间与其正交补之间的交叉项均为零。 在前者上作用是 $U$，在后者上是恒等，因此酉性及乘法式成立。 若两个提升相同，左右乘 $J^*,J$ 得原门相同。 张量内部参考的交织式直接由原式张量 $I_R$ 得到。

∎

<a id="cor:rotation"></a>

**推论 4.2（保持酉性的三轴闭合球）。**

定义 $R_U$ 为 Pauli 共轭的旋转：
$U\sigma_jU^*=\sum_i(R_U)_{ij}\sigma_i$。
则 $R_U\in SO(3)$，并且

$$
\boxed{u(U\rho U^*)=u_0+R_U\bigl(u(\rho)-u_0\bigr).}
$$

编码球在全部提升门下闭合，推论 [3.3](#cor:distance) 的距离精确保持。

**证明。**

共轭保持 Hermitian、无迹空间及迹内积，故 $R_U$ 为实正交矩阵。 连续性和 $U(2)$ 的连通性给 $\det R_U=1$。 状态的 Pauli 系数因此变为 $R_U\mathbf r$，代入定理 [3.2](#thm:encoding) 即得。

∎

这是“结构保持酉性”的正面精确版本： 在已声明的完整状态类与门表示下，原三轴内确有一个被酉作用保持的球。 一般整个金字塔不必在这些旋转下保持不变。 存在数学提升门也不表示原生黄金门菜单自动提供这个特定 $J$ 的全部控制； 后文另给原生编码与生成证明。

**命题 4.3（期望值完备不等于单次经典结果的可逆恢复）。**

令 $\mathcal M(\rho)=\sum_s\operatorname{Tr}(\rho E_s)|s\rangle\langle s|$。 该经典测量通道在全部 qubit 态上没有 CPTP 左逆。

**证明。**

取 $\rho_\pm=(I\pm\sigma_z)/2$，则 $D(\rho_+,\rho_-)=1$。 五结果概率差在 $(0,2,3,5,25)$ 顺序中为
$(-3\nu,\nu,2\nu,\nu,-\nu)$，故输出距离为 $4\nu<1$。
若存在 CPTP 左逆，其迹距离收缩性将给 $1\le4\nu$，矛盾。 收缩性也可由迹距离的效果上确界表达及正保单位的伴随映射直接证明。

∎

因此完整保存 $J\rho J^*$ 是相干编码；取得五结果分布的均值是统计重建接口； 仅存一份经典结果则是更小的读出。三者所保留的信息不同。

<a id="section-5"></a>

## 5. 经典结果与门字如何共同纳入内部酉描述

<a id="thm:record"></a>

**定理 5.1（二元仪器的内部等距记录）。**

设同一有限载体上的两个算子满足 $M_0^*M_0+M_1^*M_1=I$。 令 $R$ 是整体内部的二元记录角色，则

$$
V\psi=|0\rangle_R\otimes M_0\psi+
       |1\rangle_R\otimes M_1\psi
$$

为等距映射，可在系统与记录的同一联合空间中由 ready 子空间扩充为酉算子。 其完整联合态保留分支间的全部相干关系；经典记录概率在 Born 接口下为
$p_i=\operatorname{Tr}(M_i\rho M_i^*)$。

**证明。**

$V^*V=M_0^*M_0+M_1^*M_1=I$。
将 ready 输入子空间的正交基及其像分别补全到联合空间基，得到酉扩张。 取记录投影的期望值给所述概率；不需要整体外的环境。

∎

对完整有限历史树，要求每个长度小于 $n$ 的历史都有完整分支族。若节点 $h$ 满足
$\sum_iM_{i|h}^*M_{i|h}=I$，定义
$K_\varnothing=I$、$K_{hi}=M_{i|h}K_h$，则归纳给

$$
\sum_{|h|=n}K_h^*K_h=I,\qquad
V_n\psi=\sum_{|h|=n}|h\rangle\otimes K_h\psi,\qquad V_n^*V_n=I.
$$

定义 $p(h)=\operatorname{Tr}(K_h\rho K_h^*)$，则每个有限层都可完整地酉记录，且
$\sum_i p(hi)=p(h)$。不同深度的停止叶子须计入完整前沿，或保留停止分支的延续记录。
全部成功、失败与拒绝结果均在相应完整族中；条件态只在其质量为正时定义。 该有限历史结论与来源 v28 §5.6 一致。［[v28](#ref-v28)］

**命题 5.2（已知门字与经典结果通常不决定未知输入）。**

即使门字固定已知，只保留经典结果及其概率律，仍可能丢失量子关系。

**证明。**

取门字为恒等，在计算基读出 $|+\rangle$ 与 $|-\rangle$。 两者结果概率均为 $(1/2,1/2)$，条件系统态也都是相应的 $|i\rangle$； 但两个原输入正交。完整记录等距将相位保存在分支间的联合相干项中， 将描述限制到经典对角记录后，这些项不再被读出。

∎

有限程序集 $\mathsf P$ 也可以成为内部正交记录。若每个字 $p$ 指定数学门 $U_p$， 则

$$
\mathsf E=\sum_{p\in\mathsf P}|p\rangle\langle p|\otimes U_p
$$

是 $\ell^2(\mathsf P)\otimes\mathcal H$ 上的酉算子，逆式逐块取 $U_p^*$； 更大的程序空间上可在未用正交补另补恒等。 这个构造把程序与数据放进同一整体，并未假定原门菜单已经实现该受控执行器。 程序若允许相干叠加，不同分支的相位必须保留：
$U$ 与 $e^{i\theta}U$ 单独给同一状态通道，但受控版本相差程序分支上的相对相位。
例如受控 $I$ 与受控 $-I$ 可把 $|+\rangle$ 分别变为 $|+\rangle$ 与 $|-\rangle$。

<a id="prop:program"></a>

**命题 5.3（精确程序所需的正交性）。**

设同一个固定等距处理器作用于归一程序态，并精确地对所有数据输入实现
$\psi\otimes p_U\mapsto U\psi\otimes q_U$，其中 $q_U$ 与数据输入 $\psi$ 无关。
若 $U,V$ 不仅相差整体相位，则其程序 $p_U,p_V$ 必须正交。

**证明。**

保持任意两份数据输入的内积给

$$
\langle p_U,p_V\rangle I
=\langle q_U,q_V\rangle U^*V.
$$

若右侧程序内积非零，$U^*V$ 必为标量，与前件矛盾。 故两侧程序内积均为零。

∎

这是 Nielsen–Chuang 精确可编程门阵列边界的有限维形式。［[program](#ref-program)］ 它与有限门类型、增长的内部字记录及近似通用性相容； 不能把所有精确连续程序都塞入一个固定有限维程序角色。

<a id="section-6"></a>

## 6. 任意有限上下文：从标量关系到算子值二元递归

一个概念若与其余内部角色纠缠，三条局部均值不能完整记录这种关联。 要继续保留二元结构，可以让“关系”携带其上下文上的算子，而不是删去上下文。

**定义 6.1（带上下文的二元关系单元）。**

在 $\mathbb C^2\otimes\mathcal K$ 上，按二元标签写

$$
\rho=\begin{pmatrix}A&C^*\\C&B\end{pmatrix}\succeq0,
\qquad \operatorname{Tr}(A+B)=1.
$$

定义四个 Hermitian 上下文算子

$$
S=A+B,\qquad Z=A-B,\qquad X=C+C^*,\qquad Y=i(C^*-C).
$$

$S$ 是保留的上下文归一化算子，而 $X,Y,Z$ 是三个算子值关系轴。

<a id="thm:operatoraxes"></a>

**定理 6.2（算子值三轴的完整重建）。**

上述变换是可逆的，其逆为

$$
\boxed{\rho=\frac12
\bigl(I\otimes S+\sigma_x\otimes X+\sigma_y\otimes Y+\sigma_z\otimes Z\bigr).}
$$

完整相容条件是右侧整块正半定及 $\operatorname{Tr} S=1$。 当 $\dim\mathcal K=1$ 时，它准确退化为定理 [2.2](#thm:gram) 的标量 Bloch 球。

**证明。**

对角块给 $A=(S+Z)/2$、$B=(S-Z)/2$； 非对角块给 $C=(X+iY)/2$、$C^*=(X-iY)/2$。 因此所有块被唯一恢复，正性和迹条件也按同一矩阵逐字保留。

∎

这个线性分块恒等式也适用于任意 Hermitian 算子。 递归中的 $X,Y,Z$ 不必分别正半定或归一；状态的正性与归一化施加于完整重组矩阵。

不能在非交换上下文中直接把标量条件换成
$X^2+Y^2+Z^2\preceq S^2$。例如
$|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$ 的密度矩阵给

$$
S=I/2,\qquad X=\sigma_x/2,\qquad Y=-\sigma_y/2,\qquad Z=\sigma_z/2.
$$

整块是合法纯态，但左侧为 $3I/4$，右侧为 $I/4$。 同样，$|\Phi^\pm\rangle$ 的每个单比特约化态都为 $I/2$， 而 $\langle\sigma_x\otimes\sigma_x\rangle$ 分别为 $1,-1$； 只存 $\operatorname{Tr} X,\operatorname{Tr} Y,\operatorname{Tr} Z$ 会丢掉这项内部关系。

**推论 6.3（有限状态的完整二元递归）。**

任意有限维 $D$ 的状态都可等距嵌入 $m=\lceil\log_2D\rceil$ 个二元因子， 再递归使用定理 [6.2](#thm:operatoraxes)，完整表示为二元关系网络。 完整 $m$ 比特载体的一般态有 $4^m-1$ 个独立实系数； 固定 $D$ 维编码族则有 $D^2-1$ 个自由度。 递归不会把这些信息压成单个单元的三个实数。

**证明。**

将任意 $D$ 个正交基送入 $2^m$ 个计算基中的前 $D$ 个。 逐因子应用可逆分块，得到

$$
\rho=2^{-m}\!\!\sum_{\alpha\in\{0,x,y,z\}^{m}}
r_\alpha\,\sigma_{\alpha_1}\otimes\cdots\otimes\sigma_{\alpha_m},
\quad
r_\alpha=\operatorname{Tr}\!\left(\rho\,\sigma_{\alpha_1}\otimes\cdots\otimes\sigma_{\alpha_m}\right),
$$

其中 $\sigma_0=I$、$r_{0\cdots0}=1$。Pauli 张量基的迹正交性给完整性和唯一性。

∎

**命题 6.4（门的二元归一化与交叉关系）。**

设 $U$ 是同一有限空间 $\mathcal H_0\oplus\mathcal H_1$ 上的方块算子。 则 $U$ 酉，当且仅当

$$
\begin{aligned}
U_{00}^*U_{00}+U_{10}^*U_{10}&=I_{\mathcal H_0},\\
U_{01}^*U_{01}+U_{11}^*U_{11}&=I_{\mathcal H_1},\\
U_{00}^*U_{01}+U_{10}^*U_{11}&=0.
\end{aligned}
$$

**证明。**

三式及第三式的伴随恰是 $U^*U=I$ 的四个块。 有限维方阵的等距性同时给满射性，故也有 $UU^*=I$。

∎

**命题 6.5（多个二元单元的共同关系条件）。**

给定有限概念族的候选 Hermitian Gram 表 $G=(g_{ij})$， 存在同一复 Hilbert 载体中的向量族实现全部 $g_{ij}$， 当且仅当 $G\succeq0$；固定载体维数为 $d$ 时还需 $\operatorname{rank} G\le d$。 仅有每一对的二阶子表正半定不足以保证这个全局条件。

**证明。**

若 $G=T^*T$ 为向量列的 Gram 表，必正半定且秩不超过载体维数。 反向以 $G^{1/2}$ 的列实现，或压到其像空间，得到所需向量族。 反例取三个对角元均为一、非对角元均为 $-1$ 的表。 每个二阶子表为 $\left(\begin{smallmatrix}1&-1\\-1&1\end{smallmatrix}\right)\succeq0$， 但全一列向量的二次型为 $-3$，所以全表不正。

∎

这给“二元概念、关系与归一化”的递归精确语义： 态节点要求整块正性与总迹归一，允许非零复相干； 酉门节点要求两个列块各自归一且交叉关系正交。 若进一步把每个上下文块再二分，须保留相应完整块条件。 选择这种网络语义是对有限内部片段的完整表示；它不证明全部概念的物理来源。

<a id="section-7"></a>

## 7. 项目的固定黄金门：从酉性到真正的生成能力

<a id="section-7-1"></a>

### 7.1 原门矩阵及黄金关系

项目固定门稿与 v15 的门约定为以下精确矩阵。这里继续使用原比特顺序， 避免把中央占据模式 $010$ 的位置标签与本稿权重标签 $3$ 混同。［[golden](#ref-golden)，[v15](#ref-v15)］

$$
\varphi=\frac{1+\sqrt5}{2},\quad
\zeta=e^{3\pi i/5},\quad
Q=\begin{pmatrix}\varphi^{-1}&\varphi^{-3/2}\\
                  \varphi^{-3/2}&\varphi^{-2}\end{pmatrix},
\qquad
\mathcal P=n_Ln_R+(1-n_L)(1-n_R)Q_C .
$$

<a id="thm:golden"></a>

**定理 7.1（固定黄金门的精确酉性与正向逆）。**

$$
\boxed{K=\zeta\bigl[I+(\zeta-1)\mathcal P\bigr]}
$$

在完整三比特空间上为酉算子，且

$$
K^{10}=I,\qquad K^{-1}=K^9,\qquad K^5=2\mathcal P-I.
$$

它保持无相邻 $11$ 的五模式合法空间。

**证明。**

$\varphi^{-1}+\varphi^{-2}=1$，故
$Q=qq^*$，其中 $q=(\varphi^{-1/2},\varphi^{-1})^T$ 为单位向量。
左右控制为 $00$ 时 $\mathcal P=Q$，为 $11$ 时为 $I$， 为 $01$ 或 $10$ 时为零；因此 $\mathcal P^2=\mathcal P=\mathcal P^*$。
$K$ 在其核与像上分别取单位模特征值 $\zeta,\zeta^2$。
两者的十次方都为一，五次方分别为 $-1,1$，全部等式成立。 唯一非对角转换为 $000\leftrightarrow010$，它保持合法性。

∎

在原五模式内，这个投影写成

$$
\mathcal P_A=|q_A\rangle\langle q_A|+|101\rangle\langle101|,
\quad
q_A=\varphi^{-1/2}|000\rangle+\varphi^{-1}|010\rangle.
$$

黄金数及相位还带有实际组合关系，不能由归一化单独选定。 Fibonacci 融合的正权重满足 $\varphi^2=\varphi+1$。 若两个投影满足 $PQP=\lambda P$、$QPQ=\lambda Q$，定义
$B_P=s[I+tP]$、$B_Q=s[I+tQ]$，直接展开得到

$$
B_PB_QB_P-B_QB_PB_Q
=s^3t(1+t+\lambda t^2)(P-Q).
$$

非平凡的编织相容要求 $1+t+\lambda t^2=0$。 在 $\lambda=\varphi^{-2}$、$t=z-1$ 时化为
$z^2+\varphi^{-1}z+1=0$，其两个单位模根为 $e^{\pm3\pi i/5}$。
共同相位 $s$ 仍是约定；项目选择 $s=z=\zeta$。 这说明黄金门消费了特定关系与组合相容，提供的信息多于“每列归一”。

<a id="section-7-2"></a>

### 7.2 同一种门的两个地址已产生全部单比特操作

<a id="thm:oneuniversal"></a>

**定理 7.2（项目 v15 的双地址射影通用性）。**

取六位置编码

$$
\widehat J_1|q\rangle=|1\,0\,q\,0\,1\,0\rangle.
$$

分别在中心 $b_0,b_1$ 调用同一个 $K$，其逻辑投影为
$P=|1\rangle\langle1|$ 与上式 $Q$。记对应逻辑门为 $K_P,K_Q$，则

$$
\boxed{\overline{\langle K_P,K_Q\rangle}
=\{U\in U(2):\det U\in\mu_{10}\}.}
$$

因此对任意单比特酉门和任意正精度，存在仅使用这两个地址的有限正向字， 在整体相位意义下达到该精度。

**证明。**

第一个地址左邻为一，投影在码上为 $n_q$；第二个地址两邻为零，投影为 $Q$。 二者都保留此码，且 $\operatorname{Tr}(PQ)=\varphi^{-2}$。 由定理 [7.1](#thm:golden)，第五次幂是实反射
$R_P=2P-I$、$R_Q=2Q-I$，其乘积属于 $SO(2)$，并有

$$
\operatorname{Tr}(R_PR_Q)=4\operatorname{Tr}(PQ)-2=4-2\sqrt5.
$$

若此乘积有限阶，其两个特征值为互逆单位根，迹的所有代数共轭都在 $[-2,2]$。 但上式的另一共轭为 $4+2\sqrt5>2$，矛盾。 故其幂在 $SO(2)$ 圆中稠密。

交换逻辑基次序后 $K_P=\operatorname{diag}(\zeta^2,\zeta)$。 令 $J_0=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$， 则

$$
K_PJ_0K_P^*
=\cos(3\pi/5)J_0-i\sin(3\pi/5)\sigma_x.
$$

这与 $J_0$ 不共线。闭群因而包含两个不共线的一参数子群； 其 Lie 代数含二者及交换子，张成 $\mathfrak{su}(2)$，故含 $SU(2)$。 另一方面 $\det K_P=\det K_Q=\zeta^3$ 是本原十次单位根， 所以闭包的行列式只能属于 $\mu_{10}$，而 $K_P^jSU(2)$ 给齐所有这些陪集。 最后 $K^{-1}=K^9$ 消去全部逆字母。

∎

本证明重述并核对项目 v15 §4 的既有纸面结果。［[v15](#ref-v15)］ 同一固定地址只产生十个幂；同一门类型在指定的不同地址之间组合， 则已产生连续的射影闭包。这正是本项目中“关系参与通用生成”的具体实例。

<a id="section-7-3"></a>

### 7.3 可扩展编码及当前 Jones–Wenzl 密度桥

下面把续卷 II §77 已给的八条编织线、十三维全扇区对应， 按同一个局部表推广到任意 $4n$ 条线。该推广是本稿的纸面推论； 外部密度输入仍是 Freedman–Larsen–Wang 的 Theorem 0.1， 并非重新证明该深层密度定理。［[continuation](#ref-continuation)，[flw](#ref-flw)］

**定义 7.3（可扩展合法载体）。**

对 $n\ge1$，供给 $4n+2$ 个内部位置，顺序为
$b_{-1},b_0,\ldots,b_{4n}$，以及中心 $j=0,\ldots,4n-2$ 的原 $K_j$。
定义

$$
\mathcal H_n=\operatorname{span}
\{|10\,\beta\,010\rangle:
\beta\in\{0,1\}^{4n-3},\ \beta_j\beta_{j+1}=0\}.
$$

逻辑编码为

$$
\widehat J_n|q_1\cdots q_n\rangle
=|10\,(q_1\,010)(q_2\,010)\cdots(q_n\,010)\rangle .
$$

<a id="thm:manyuniversal"></a>

**定理 7.4（原生门的编码近似通用性）。**

每个 $\mathcal H_n$ 在所供给的全部 $K_j$ 下不变，维数为 $F_{4n-1}$。 这些原生正向有限字的射影闭包为 $PU(\mathcal H_n)$。 因此对每个 $U\in U(2^n)$、$\varepsilon>0$，存在有限正向字 $w$ 与相位 $\gamma$，使

$$
\boxed{\|K_w\widehat J_n-e^{i\gamma}\widehat J_nU\|_{\rm op}<\varepsilon.}
$$

在 Born/CP 接口下，此界对任意内部参考稳定，编码输出通道的半 diamond 距离至多
$\varepsilon$，终态逸出逻辑码的概率至多 $\varepsilon^2$。

**证明。**

每个门只可能在邻位皆零时翻转中心，因而保持禁邻接条件。 左端中心 $b_0$ 的左邻固定为一，右端中心 $b_{4n-2}$ 的右邻固定为一， 故两端固定位置也保持不变。 长度 $m$ 的合法二元串数量满足 $a_m=a_{m-1}+a_{m-2}$、
$a_0=1,a_1=2$，所以维数为 $F_{m+2}=F_{4n-1}$。

把 $b_j=1$ 对应为 Fibonacci 前缀标签 $x_{j+1}=\mathbf1$， 令 $x_0=x_{4n}=\mathbf1$。融合规则
$\mathbf1\otimes\tau=\tau$、$\tau\otimes\tau=\mathbf1\oplus\tau$
恰对应上述禁邻接。固定末旁观位不改变所用地址。 定义高度

$$
h_k=\begin{cases}
0,&k\text{ 偶},\ x_k=\mathbf1,\\
2,&k\text{ 偶},\ x_k=\tau,\\
3,&k\text{ 奇},\ x_k=\mathbf1,\\
1,&k\text{ 奇},\ x_k=\tau .
\end{cases}
$$

于是高度在 $0,1,2,3$ 中、每步改变一、首尾为零。 上升步把该步序号放入 Young 表第一行，下落步放入第二行， 得到形状 $\lambda_n=(2n,2n)$ 的整个 $(k,r)=(2,5)$ 可容许标准表基， 并且可逆。这给同一个酉基对应 $W_n$。

为验证全部生成元而非只匹配维数，取
$q=e^{2\pi i/5}$、$q^{1/2}=e^{\pi i/5}$，
$[a]=(q^{a/2}-q^{-a/2})/(q^{1/2}-q^{-1/2})$。
若表中 $i$ 的行列位置为 $(r_i,c_i)$， 置 $d_{t,i}=(c_i-c_{i+1})-(r_i-r_{i+1})$。 FLW §2 的表投影对角元为
$a_{t,i}=[d_{t,i}+1]/([2][d_{t,i}])$，
非对角元为正平方根 $\sqrt{a_{t,i}(1-a_{t,i})}$。 局部对应与总长度无关：

| 外侧标签 | 中间标签 | $d_{t,i}$（$i$ 奇／偶） | $a_{t,i}$ |
| --- | --- | --- | --- |
| $\mathbf1,\mathbf1$ | $\tau$ | $1/-4$ | $1$ |
| $\mathbf1,\tau$ 或 $\tau,\mathbf1$ | $\tau$ | $-1/-1$ | $0$ |
| $\tau,\tau$ | $\tau$ | $-3/2$ | $\varphi^{-1}$ |
| $\tau,\tau$ | $\mathbf1$ | $3/-2$ | $\varphi^{-2}$ |

此处斜线分隔奇、偶两值，而非表示除法。 前两行仅有一维块；后两行之间的非对角元为 $\varphi^{-3/2}$， 故投影正是 $\mathcal P$ 的三个控制块。 左右端点分别给邻近自由位的占据投影，也包含在同表中。 由 FLW 编织定义 $\rho(\sigma_i)=qI-(1+q)E_i$，统一得到

$$
W_n(K_{i-1}|_{\mathcal H_n})W_n^{-1}
=e^{\pi i/5}\rho_{\lambda_n}^{(2,5)}(\sigma_i),
\qquad 1\le i\le4n-1.
$$

这使用该文明确的 Jones–Wenzl 表示； 没有把其 §6 印刷的非酉 $F$ 显示式默默改写为另一矩阵。

FLW Theorem 0.1 对 $r=5$、线数 $4n\ge4$ 适用， 给整个该扇区的闭像包含 $SU(F_{4n-1})$。 统一标量及基对应保持射影闭包，故得到 $PU(\mathcal H_n)$。 再把逻辑 $U$ 延拓为
$\widehat J_nU\widehat J_n^*+(I-\widehat J_n\widehat J_n^*)$，
应用此密度即可。逆字母用 $K_j^9$ 替换；原 $L$ 字母的编织字 至多变为 $9L$ 次原门调用，不增加逼近误差。

最后，两等距算子相差至多 $\varepsilon$ 时，张量任意参考后仍如此。 将输出密度之差拆为两项，迹范数至多 $2\varepsilon$； 投影到理想码的正交补，向量范数至多 $\varepsilon$。 分别给通道界和逸出概率界。

∎

“可扩展”明确要求相应数量的内部位置与地址。 固定十三维扇区只对应 $n=2$，本身并不容纳任意多逻辑比特。 通用性是每个目标、每个精度存在有限字； 本稿没有据此宣称所有任意 $n$ 比特酉矩阵都有关于 $n$ 的多项式长度描述。

对同一固定最近邻菜单，完整未编码寄存器还满足

$$
[K_j,D_i]=0,\qquad D_i=n_in_{i+1}.
$$

因为唯一中心翻转需要两个邻位为零，任何相邻双占据缺陷都不能改变。 例如全零基态与含一个相邻 $11$ 的基态不可能被这些门互换。 这与共同零缺陷合法扇区内的编码通用性完全相容；项目 v15 §7 已明确此范围。［[v15](#ref-v15)］

<a id="section-8"></a>

## 8. 把新的三轴编码接到原七地址：一个实际菜单内的桥

<a id="section-8-1"></a>

### 8.1 两个码之间的原生编译

现在取上述 $n=2$ 的同一个十三维载体

$$
\mathcal H=\operatorname{span}\{e_\beta=|10\,\beta\,010\rangle:
|\beta|=5,\ \beta\text{ 无相邻 }11\}.
$$

原七个地址为 $0,\ldots,6$，唯一旧种子为 $v=e_{00100}$， 仍保留原十位终端的全部 $1024$ 个标签。［[continuation](#ref-continuation)］ 令

$$
\begin{array}{c|ccccc}
s&0&2&3&5&25\\ \hline
L|s\rangle&e_{00000}&e_{10000}&e_{01000}&e_{00100}&e_{10100}
\end{array}
$$

并取 $R|0\rangle=e_{00100}$、$R|1\rangle=e_{10100}$。 这里 $R$ 是既有两逻辑比特码中第二比特固定为零的子码， 而 $L$ 只是原五模式在同一载体中的固定基嵌入。 记新目标码为 $V=LJ$。

<a id="lem:sudensity"></a>

**引理 8.1（有限行列式与射影密度）。**

若 $G$ 是 $U(d)$ 的闭子群、$\det G$ 有限且其射影像为 $PU(d)$， 则 $G$ 包含 $SU(d)$。

**证明。**

闭矩阵子群是紧 Lie 群，故只有有限多个连通分支。 其单位分支 $G^0$ 的行列式恒为一，所以 $G^0\subset SU(d)$。
$\pi(G^0)$ 是 $PU(d)$ 的有限指数闭正规子群；
连通群的这种子群只能是全群。
$G^0$ 上射影映射的核包含于有限中心 $\mu_d$，
因而其维数为 $d^2-1$。$SU(d)$ 中这个同维的闭连通子群即为 $SU(d)$。

∎

<a id="thm:nativeJ"></a>

**定理 8.2（新三轴编码的原生有限字实现）。**

对任意 $U\in U(2)$ 和 $\varepsilon>0$，存在仅调用原七地址的有限正向字 $w$，使

$$
\boxed{\|K_wR-LJU\|_{\rm op}<\varepsilon.}
$$

此处可以准确对齐码上的相位，无需在结论中额外忽略一个未知整体相位。 所用数学延拓只用于指定编译目标，不增加新的可调用门。

**证明。**

$R$ 与 $LJU$ 都是二至十三维等距映射。
将它们的像基各自补全，得到 $S_U\in U(13)$ 满足 $S_UR=LJU$。 在输入码的十一维正交补上调整一个相位，可使 $\det S_U=1$ 而不改变该等式。 不能以 $LJU R^*+(I-RR^*)$ 代替这项补全：两个码像不同时，该式通常不酉。

令

$$
G=\overline{\langle K_0|_{\mathcal H},\ldots,K_6|_{\mathcal H}\rangle}.
$$

源 §77 的射影密度与定理 [7.1](#thm:golden) 给
$\pi(G)=PU(13)$、$\det G\subset\mu_{10}$。
引理 [8.1](#lem:sudensity) 给 $SU(13)\subset G$。 于是可以用原门字逼近上述 $S_U$ 而不需舍弃相位。
$K_j^{-1}=K_j^9$ 又把字改为正向，限制到 $R$ 即得。

∎

这比单纯存在数学编码更强：原菜单已经能逐精度编译这个编码。 不过源模型直接供应的初始态仍只有 $v=R|0\rangle$。 对全部 $R|\psi\rangle$ 的不等式是统一的编码通道保证； 任意未知逻辑输入已经接入 $R$ 并不是密度定理自动提供的事实。 已知纯目标可以连同编码一起近似准备；未知输入、混态源或参考的实际接入仍按各自接口说明。

<a id="section-8-2"></a>

### 8.2 同一码上的闭合门表示与完整读出误差

从 $R$ 码到 $V$ 码的编码操作不应直接当作同一码上的门连续相乘。 固定一次初始化后，可用下面的相位平衡表示保持递归闭合。

<a id="thm:balanced"></a>

**定理 8.3（码内门的相位平衡原生表示）。**

固定单位向量 $\eta\perp\operatorname{ran}V$，令 $P_V=VV^*$、
$P_\eta=|\eta\rangle\langle\eta|$。则

$$
\mathcal G_U=VUV^*+\det(U)^{-1}P_\eta+
(I-P_V-P_\eta)
$$

定义一个忠实的群同态 $U(2)\to SU(13)$，满足
$\mathcal G_UV=VU$。每个 $\mathcal G_U$ 都能用同一原七地址的正向有限字
在算符范数下任意逼近。

**证明。**

在正交分解 $\operatorname{ran}V\oplus\mathbb C\eta\oplus (\operatorname{ran}V+\mathbb C\eta)^\perp$ 中，该算子为
$U,\det(U)^{-1},I$ 三个块。
因此酉、行列式一，乘法性由行列式乘法性给出，单射性由首块给出。 原生逼近来自上一证明的 $SU(13)$ 闭包。

∎

相位补偿发生在同一载体的内部正交补，不改变码内目标。 这保证在此数学编译问题中相位可以正确保留； 它不额外宣称任意相干受控程序选择器已由原菜单供应。

<a id="cor:nativeread"></a>

**推论 8.4（旧终端的三轴读出与泄漏预算）。**

在已声明的 Born/CP 读出接口下，定理 [8.2](#thm:nativeJ) 的实际有限字与理想输出 $LJU$ 在任意内部参考上的半 diamond 距离至多 $\varepsilon$。 对全部旧终端标签保留无条件概率时，终端总变差至多 $\varepsilon$，且

$$
\Pr(\text{所选五模式外})\le\varepsilon^2.
$$

取旧终端中 $\beta_1,\beta_3,\beta_2$ 三个位的占据事件，它们各自的概率误差至多
$\varepsilon$，其理想压缩效果恰为

$$
U^*(a_\nu I+\nu\sigma_x)U,\quad
U^*(a_\nu I+\nu\sigma_y)U,\quad
U^*\nu(I+\sigma_z)U.
$$

**证明。**

$L^*n_{\beta_1}L=N_x$、$L^*n_{\beta_3}L=N_y$、
$L^*n_{\beta_2}L=N_z$，所以理想效果由定理 [3.2](#thm:encoding) 给出。
两等距通道之差的迹范数拆分界为 $2\varepsilon$， 测量的收缩性给总变差与各事件界。 理想像在 $\operatorname{ran}L$ 内，正交补上的实际向量范数至多 $\varepsilon$。

∎

**推论 8.5（原生编译的有限递归及相干误差）。**

若同一码 $V$ 上各目标门 $U_j$ 的原生字 $W_j$ 满足
$\|W_jV-VU_j\|\le\varepsilon_j$，则

$$
\|W_m\cdots W_1V-VU_m\cdots U_1\|
\le\sum_{j=1}^m\varepsilon_j.
$$

若先从 $R$ 编码，另加初始误差 $\varepsilon_0$。 完整终端 TV 至多为该总误差，最终码外概率至多为总误差的平方。

**证明。**

在第 $j$ 步的差中插入
$W_jVU_{j-1}\cdots U_1$。
第一项是上一步误差左乘酉 $W_j$，第二项范数至多 $\varepsilon_j$； 归纳即得。该论证允许实际中间态有少量码外分量。

∎

相干累积的一般界是 $(\varepsilon_0+\sum_j\varepsilon_j)^2$； 没有额外条件时不能换成各步泄漏概率的平方和。 精确原门始终保持 $\mathcal H$，所以原终端中不属于这十三条路径的标签理想质量仍为零。 五模式外的事件是其余八条合法旧标签的并；无需增设新投影仪器，也不按成功概率重新归一化。 近似编译的真实输出一般不严格位于 $V$ 码，所以 $p_0=3p_{25}$ 等精确编码关系 只在理想目标上严格成立。完整终端的总变差界给

$$
|p_0-3p_{25}|\le4\varepsilon_{\rm tot} .
$$

单次编译可取 $\varepsilon_{\rm tot}=\varepsilon$； 上述递归可取 $\varepsilon_{\rm tot}=\varepsilon_0+\sum_j\varepsilon_j$。 这项残差及其余逸出质量都应保留。真实门实现、输入准备和终端读取误差 需另加到完整预算，不能由编译误差一项代替。

<a id="section-9"></a>

## 9. 酉误差、归一化与递归级数的精确连接

<a id="thm:errorseries"></a>

**定理 9.1（相对误差门的绝对收敛）。**

在同一有限 Hilbert 载体上，令全部 $U_j,V_j$ 为酉算子，并满足
$\|V_j-U_j\|_{\rm op}\le\epsilon_j$。定义

$$
A_n=U_n\cdots U_1,\qquad B_n=V_n\cdots V_1,\qquad
C_n=A_n^*B_n,\qquad A_0=B_0=C_0=I.
$$

则每个 $C_n$ 仍酉，且

$$
\|B_n-A_n\|_{\rm op}\le\sum_{j=1}^n\epsilon_j,\qquad
\|C_n-C_{n-1}\|_{\rm op}\le\epsilon_n .
$$

若 $\sum_{j\ge1}\epsilon_j<\infty$，则 $C_n$ 收敛到某个酉算子 $C_\infty$，并有

$$
\boxed{\|C_\infty-C_n\|_{\rm op}\le\sum_{j>n}\epsilon_j.}
$$

此结论不要求 $A_n$ 或 $B_n$ 自身收敛。

**证明。**

酉性对乘法和取伴随闭合。直接按调用顺序相减给

$$
\Delta_n:=C_n-C_{n-1}
=A_{n-1}^*(U_n^*V_n-I)B_{n-1}.
$$

外侧酉因子不放大算符范数，故 $\|\Delta_n\|\le\epsilon_n$。 于是 $C_n=I+\sum_{j=1}^n\Delta_j$， 并且 $\|B_n-A_n\|=\|C_n-I\|$ 给首个界。 当误差可求和时，此算符级数绝对收敛，尾和给所述界。 酉算子集合在算符范数下闭合，因为取极限保留
$C_n^*C_n=C_nC_n^*=I$；所以极限也酉。

∎

这个级数保留了一个精确的“结果与误差关系”：

$$
\boxed{
C_{n-1}^*\Delta_n+\Delta_n^*C_{n-1}
+\Delta_n^*\Delta_n=0.}
$$

它由 $(C_{n-1}+\Delta_n)^*(C_{n-1}+\Delta_n)=I$ 减去旧归一化式直接得到。 因此误差增量不必自身酉；它必须与已有结果共同满足线性加二次的归一化约束。 这正是把前轮的派生误差关系提升到门序列后的版本。

若 $\epsilon_j\le c q^{j-1}$、$0<q<1$，则纸面上即有

$$
\|C_\infty-C_n\|\le \frac{c q^n}{1-q}.
$$

仅有“每一步误差很小”不足以给此尾界； 所需的是总预算可求和，或另有等效的收敛控制。 收敛的 $C_\infty$ 也不必等于 $I$：稳定偏差仍可能非零。

**推论 9.2（三轴中的相对误差闭合）。**

若所有 $U_j,V_j$ 都保留本稿指定的 $J$ 码，且 $\sum_j\epsilon_j<\infty$， 则 $C_n$ 在该码上的限制为酉门。用固定等距 $J$ 识别此码， 置 $\widehat C_n=J^*C_nJ\in U(2)$。 对每个归一 qubit 输入 $\rho$，相对框架中的状态
$\widehat C_n\rho\widehat C_n^*$ 的三轴仍在本稿的同一个 AURIC 编码球中，
并收敛到 $\widehat C_\infty\rho\widehat C_\infty^*$。 它与 $\rho$ 的三轴差及五矩差继承定理 [3.4](#thm:four) 的线性关系。 在十三维原生实现中，指定码改用 $V=LJ$，同一结论成立。

**证明。**

有限维不变码在酉算子下也是约化子空间，所以限制仍酉。 使用定理 [4.1](#thm:lift) 的码内对应及推论 [4.2](#cor:rotation) 即得球内闭合； 算符范数收敛给状态迹范数收敛。 五矩是状态的线性函数，其差因此满足同一线性等式。

∎

固定框架中的 $B_n\rho B_n^*-A_n\rho A_n^*$ 不必收敛，因为 $A_n$ 可以持续旋转； 但其迹距离等于
$D(C_n\rho C_n^*,\rho)$，会收敛到 $D(C_\infty\rho C_\infty^*,\rho)$。
有符号状态差仍不是自动归一的正概率态。 若观察到的逻辑误差为一般 CP 噪声或发生码外泄漏，须保留相应内部角色或单独计预算， 不能直接把那个约化噪声通道当作此处的酉 $V_j$。

最后，若三个读数相对于目标逻辑态 $\rho$ 的理想占据均值， 分别具有总误差界 $\delta_x,\delta_y,\delta_z$， 先按 $(u-u_0)/\nu$ 反标定，再正交投影回闭单位球，得到合法估计态 $\widehat\rho$。 闭凸球投影不会增加其到真实球内点的欧氏距离，故

$$
\boxed{D(\widehat\rho,\rho)\le
\frac{\sqrt{\delta_x^2+\delta_y^2+\delta_z^2}}{2\nu}.}
$$

这里各 $\delta_i$ 应包括编译、实际累计控制、准备、读口以及有依据的统计估计误差。 归一化与投影给出合法输出；精度由完整误差预算给出。

<a id="section-10"></a>

## 10. 最新项目增量：归一化何时足以形成共同概率律

本稿前面的态与读出概率明示采用复正态及 Born/CP 接口。 若把研究目标继续推到“这些概率规则如何从原生程序间关系取得”， 当前提交新增的续卷 II §§121–125 给出了一个更具体的条件桥。［[continuation](#ref-continuation)，[effect](#ref-effect)］ 下面保留它的供应范围，说明与本轮结论的关系。

<a id="section-10-1"></a>

### 10.1 同一旧终端覆盖任意三效果

源设原十三维输入载体为 $\mathcal H$，同族内部扩大载体为 $\mathcal K$，维数 $89$。 保留指定 ready 嵌入 $R_0:\mathcal H\to\mathcal K$、原生地址和完整旧终端。 同一终端的三个固定不交事件为
$A_0=\{b_1=1\}$、$A_1=\{b_1=0,b_2=1\}$、
$A_2=\{b_1=b_2=0\}$，其投影 $Q_0,Q_1,Q_2$ 的秩分别为 $34,21,34$。
这些秩及 $PU(89)$ 原生闭包是该来源的具体供应，并非本稿新增一个可调仪器。

**定理 10.1（源 §121 的同时三效果覆盖）。**

对任意 $E_0,E_1,E_2\succeq0$、$E_0+E_1+E_2=I_{\mathcal H}$ 和 $\varepsilon>0$，存在同一个原生正向有限字 $w$， 使三个事件及其各个并的压缩效果都以至多 $2\varepsilon$ 的算符误差逼近目标。

**证明。**

因为三个固定终端空间的秩均不少于 $13$， 可在证明中选等距 $T_k:\mathcal H\to\operatorname{ran}Q_k$。 置

$$
V_E=\sum_{k=0}^2T_k\sqrt{E_k}.
$$

正交像给 $V_E^*V_E=\sum_kE_k=I$， 且 $V_E^*Q_kV_E=E_k$。 把 $R_0$ 与 $V_E$ 的等距配对补成同一 $\mathcal K$ 上的目标酉， 再用源已供应的射影密度逼近，得
$\|K_wR_0-e^{i\gamma}V_E\|\le\varepsilon$。
对任意事件并投影 $Q_A$，两边压缩之差拆为两项， 范数至多 $2\varepsilon$。这是一次编译、一次旧终端，所有目标同时成立。

∎

$T_k,\sqrt{E_k}$ 以及目标延拓在这里是存在性证明对象，
实际调用仍是原生有限字。此结论只给效果覆盖， 不自动给那些粗事件的 Lüders 后继或任意初态源。

<a id="section-10-2"></a>

### 10.2 归一化还需要跨程序的同效果相容

给每个实际有限程序 $C$ 的完整事件律 $P_C$， 并先用其矩阵与完整终端定义概率无涉的效果签名 $E(C,A)$。 源新增的关键条件是： 当两列程序事件签名收敛到同一个效果时，它们实际事件概率的差趋于零。 这项条件把不同程序的记录接到一个共同关系对象上。

**命题 10.2（共同效果概率与 Born 表示的条件取得）。**

在源的任意目标完整程序律供应、上述跨程序匹配、同时三效果覆盖及旧 ready 校准下， 存在唯一密度矩阵 $\rho_{\mathcal H}$，使供应域内的全部事件满足

$$
P_C(A)=\operatorname{Tr}(\rho_{\mathcal H}E(C,A)).
$$

旧种子 $v$ 的 ready 校准进一步给 $\rho_{\mathcal H}=|v\rangle\langle v|$。

**证明。**

对任意效果 $0\preceq E\preceq I$，用同时覆盖选择签名趋于 $E$ 的事件列。 若概率列不为 Cauchy，则可抽出两列仍同趋 $E$ 而概率差不趋零， 与匹配条件矛盾。故其极限存在； 任意两种近似列的匹配又保证极限只依赖 $E$，定义为 $p(E)$。 常值列把每个实际有限事件连接到其 $p(E(C,A))$。

对任意 $E,F\succeq0$、$E+F\preceq I$，同时覆盖三元组
$(E,F,I-E-F)$。同一个程序中不交事件的普通概率可加性，
结合匹配极限，给

$$
p(E+F)=p(E)+p(F),\qquad p(I)=1,\qquad p(E)\ge0.
$$

这里没有要求 $E,F$ 交换。 既有 `effect_density_representation` 恰以这三个前件 给唯一正半定迹一矩阵的迹表示；本轮未执行该声明的形式应用。 最后 ready 投影 $|v\rangle\langle v|$ 的校准概率为一， 正性和迹一迫使 $\rho_{\mathcal H}$ 在其正交补上全为零， 从而 $\rho_{\mathcal H}=|v\rangle\langle v|$。

∎

该既有效果表示也可用普通有限维思路理解： 非负可加性给单调性及有理齐次性，再由有理上下夹逼给实齐次性； 把效果函数按缩放延拓到正锥，再以正负部分延拓成 Hermitian 空间上的正线性泛函。 有限维迹对偶给 $\rho$，对秩一投影非负给 $\rho\succeq0$，单位校准给 $\operatorname{Tr}\rho=1$。 本稿使用项目已有表示供应，不把这一标准表示重新宣称为新定理。

关键是“各程序各自归一”与“不同程序的同一个效果有共同概率”是两个前件。 最新源 §124 用同一个固定记录程序及终端编译列给出分离实例： 满足旧合同的非零参数响应仍能违反新增匹配。 所以新增概率关系不能从酉性、同一来源或单程序归一中省略。 源 §123 的识别范围仍是原 ready 来源及已供应的有限程序族； 任意输入、任意复合或所有 CP 仪器的实际取得不在该结论中。

<a id="section-11"></a>

## 11. 可以确立的总命题及其语义

**定理 11.1（AURIC 二元关系、酉表示与原生通用生成的连接）。**

在以下明确前件下：同一静态整体内部的复 Hilbert 关系接口； 本稿固定的五模式等距码；项目指定的黄金门、合法地址与可扩展载体； 以及使用概率时的 Born/CP 或所述共同效果接口，成立：

1. 每个非零二元正关系由尺度与三实轴完整表示，并由同一个原五模式码实现。
三轴构成原金字塔内的圆球，五矩满足同一线性关系，故已知缺项的四推一稳定成立。

2. 每个数学 $U(2)$ 具有忠实五模式提升，码内动作是球的刚性旋转。
保留完整内部记录时，合法二元仪器也有酉扩张。

3. 项目的固定黄金门在指定地址、合法编码上具有近似通用性。
本稿新的三轴编码及码内 $U(2)$ 还可在原十三维七地址模型中逐精度编译， 并可保留码上相位。

4. 带上下文的关系应使用算子值三轴；任意有限状态与门可用完整二元分块递归表示。
多个二元单元还须满足共同正性和组合相容。

5. 可求和的酉实现误差给相对误差门的绝对收敛级数、精确归一化关系与可控尾界。
有限原生字的码外误差及终端误差可以放在同一完整预算中传播。

**证明。**

依次由定理 [2.2](#thm:gram)、[3.2](#thm:encoding)、[3.4](#thm:four)、 [4.1](#thm:lift)、[5.1](#thm:record)、[7.4](#thm:manyuniversal)、 [8.2](#thm:nativeJ)、[8.3](#thm:balanced)、[6.2](#thm:operatoraxes)、 [9.1](#thm:errorseries) 及其推论得到。

∎

因此可把用户的判断精确表述为：

> AURIC 可作为二元相干正关系的完整表示单元；
> 其指定黄金门与合法组合关系可构成编码近似通用的量子门体系。
> 经典结果是整体内部记录的读出，完整酉性在保留所有相关角色的联合描述中表达。
> 更大的概念与关系通过保留上下文的二元网络连接，而误差以其自身的相容关系参与递归。

其中“任意二元概念”是指已经给出该复正关系语义的二元对象； “通用”是指定菜单上的逐目标、逐精度有限生成； “稳定”由明确的误差标尺及可求和预算承担。 这些条件给出了可检查的数学内容，也保留了继续研究整体物理来源的空间。

<a id="references"></a>

## 固定来源与证据范围

<a id="ref-head"></a>

**[head]**

[trureturing 固定提交：3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e](https://github.com/the-omega-institute/trureturing/commit/3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e)。 固定公开源码快照，2026-10-31 新加坡时间；非后续滚动分支。

<a id="ref-foundation"></a>

**[foundation]**

[AURIC FIB ATOM 金字塔基础公式与关系](https://github.com/the-omega-institute/trureturing/blob/3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)。 原五模式、三个占据读口及其经典概率关系。

<a id="ref-v28"></a>

**[v28]**

[AURIC 二元读出、完整框架相容性与黄金门桥，v28](https://github.com/the-omega-institute/trureturing/blob/3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e/docs/develop/theory/AURIC_BINARY_READOUT_FULL_FRAME_COMPATIBILITY_AND_E8_GOLDEN_GATE_BRIDGE_V28.md)。 使用范围：二阶正关系、内部仪器记录、原占据压缩的联合可测性及完整上下文边界。

<a id="ref-golden"></a>

**[golden]**

[AURIC 固定黄金门与编织相容性](https://github.com/the-omega-institute/trureturing/blob/3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e/docs/develop/theory/AURIC_FIXED_GOLDEN_GATE_AND_BRAID_COMPATIBILITY_ZH.md)，§§1–4。 矩阵与共同相位按原稿约定；早期编码桥条件由后续具体来源补足。

<a id="ref-v15"></a>

**[v15]**

[AURIC 黄金门、NAND 通用性与算术边界，v15](https://github.com/the-omega-institute/trureturing/blob/3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)。 本轮具体读取和核对 §§1–4、6–7 的相关门、编码、误差与守恒结论； 不声称审计全文后续算术证明。

<a id="ref-continuation"></a>

**[continuation]**

[AURIC FIB ATOM 与量子基本原则：相干重建续卷 II](https://github.com/the-omega-institute/trureturing/blob/3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)。 §77 的全十三维 Jones–Wenzl 对应与密度； 本轮新增 §§121–125 的同时效果覆盖、实际概率匹配及条件表示。 这些来源均为纸面论证；入库本身不构成独立认证。

<a id="ref-effect"></a>

**[effect]**

[EffectProbabilityExtension：effect\_density\_representation](https://github.com/the-omega-institute/trureturing/blob/3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e/D5/S3/Quantum/Foundation/EffectProbabilityExtension.lean)。 读取现有公开声明和相应源码；本轮未执行 Lean，也未声称新增应用已编译。

<a id="ref-flw"></a>

**[flw]**

M. H. Freedman, M. Larsen, Z. Wang, [*The two-eigenvalue problem and density of Jones representation of braid groups*](https://arxiv.org/abs/math/0103200)。 使用 Theorem 0.1 及 §2 的明确 Jones–Wenzl 表示。

<a id="ref-program"></a>

**[program]**

M. A. Nielsen, I. L. Chuang, [*Programmable quantum gate arrays*](https://arxiv.org/abs/quant-ph/9703032)。 固定等距处理器的精确程序正交性边界。

<a id="editor-notes"></a>

## 编者校核注（不属原稿）

原稿正文、证明和参考条目保持原义；“本轮”“本轮新增”“未执行”等均为作者写作轮的历史陈述。本转写的源码对应、普通纸面核对与本地页面检查，不是新的 Lean 核验，也不提供原生硬件、输入源或概率合同的实际取得证据。

定理 6.3 的一维边界按零个二元因子、空 Pauli 张量和零个自由参数解读。第 7.1 节所说“非平凡的编织相容”排除零共同因子、恒等更新及两个相同投影；这些退化情形不要求从乘积为零推出其中的二次因子为零。

FLW 原论文 Theorem 0.1 的条件是：阶数至少五且不为六或十时，线数至少三；阶数为十时，线数至少五。本文使用阶数五和至少四条线，及第 7.3 节明确给出的整个可容许表基与全部生成元对应，未借用其第 6 节非酉印刷融合矩阵来补足对应。

第 8 节的十三维、七地址编译与第 10 节的八十九维扩展须分清：后者沿用续卷 II 的指定 ready 嵌入、十一地址和完整旧终端。任意目标的有限字存在性、跨程序概率匹配、完整实际程序律供应，以及任意未知输入的取得，仍是正文分列的不同条件。

## 追加锚（本行以下为增补区）

## 12. 固定五概率表示的全部自治随机门

**定义 12.1（同一五结果上的自治更新）。** 继续使用定义 3.1 的原效果、原增益 $\nu$ 和固定顺序 $S=(0,2,3,5,25)$。对全部 qubit 密度矩阵置

$$
p(\rho)=(\operatorname{Tr}\rho E_s)_{s\in S}\in\mathbb R^5.
$$

概率写为列向量。一个自治随机更新是满足 $T_{st}\ge0$、$\sum_sT_{st}=1$ 的实 $5\times5$ 矩阵，其中 $T_{st}$ 是输入标签 $t$ 到输出标签 $s$ 的条件概率。所问的精确存在性是

$$
\exists T\quad\forall\rho\succeq0,\ \operatorname{Tr}\rho=1:
\qquad Tp(\rho)=p(U\rho U^*).
\tag{12.1}
$$

$T$ 可以依赖已指定的 $U$，但不依赖 $\rho$、制备字、制备设置、既往记录或当次抽到的输入以外的信息。行概率约定下，同一式为 $p(\rho)^{\mathsf T}T^{\mathsf T}=p(U\rho U^*)^{\mathsf T}$，更新矩阵的行和才为一。这里没有假定 $T$ 可逆，也没有要求其逆仍随机。

**定理 12.2（本编码的精确分类与全部可行核）。** 对定义 3.1 的五效果，$U\in U(2)$ 满足 (12.1) 当且仅当 $U=e^{i\gamma}I_2$。在此情形全部可行矩阵恰为

$$
T(t)=\begin{pmatrix}
1-t&0&0&0&3t\\
0&1&0&0&0\\
0&0&1&0&0\\
0&0&0&1&0\\
t&0&0&0&1-3t
\end{pmatrix},\qquad 0\le t\le\frac13.
\tag{12.2}
$$

证明。式 (12.1) 等价于逐效果等式

$$
U^*E_sU=\sum_{t\in S}T_{st}E_t\qquad(s\in S).
\tag{12.3}
$$

充分性由取迹得到。必要性中，两边之差是 Hermitian 矩阵；若其在全部纯态上的二次型为零，其谱分解即给差为零。因此不需要把输入扩充到非物理矩阵。

使用秩一 POVM 随机后处理的标准支撑事实：若非零秩一正矩阵 $F$ 是 $\sum_jc_jF_j$，其中 $c_j\ge0$、$F_j\succeq0$，则每个 $c_j>0$ 的 $F_j$ 均支撑在 $\operatorname{ran}F$ 内。事实上，对 $z\perp\operatorname{ran}F$ 有 $0=\sum_jc_j\langle z,F_jz\rangle$；各项非负，所以所用 $F_j$ 都消灭这些 $z$，正性再给所述支撑包含。这是 [Haapasalo–Pellonpää，§2 (1b) 及脚注 7](https://arxiv.org/pdf/1705.03636v1) 所述 smearing 框架中的基本正性步骤；一般框架及秩一背景不作为新增结果。

为处理本效果中的重复射线，把 $E_s=w_s(I+n_s\cdot\sigma)/2$ 的方向和迹列为

$$
\begin{array}{c|c|c}
s&n_s&w_s=\operatorname{Tr}E_s\\ \hline
0&n_A=(-1,-1,-1)/\sqrt3&3\nu\sqrt3\\
2&n_B=(3,1,1)/\sqrt{11}&\nu\sqrt{11}\\
3&n_C=(0,0,1)&2\nu\\
5&n_D=(1,3,1)/\sqrt{11}&\nu\sqrt{11}\\
25&n_A&\nu\sqrt3
\end{array}
\tag{12.4}
$$

四个方向互异。令 $R_U\in SO(3)$ 沿用推论 4.2，则 (12.3) 左侧的方向是 $R_U^{-1}n_s$。每行左侧非零，故右侧至少使用一项；支撑事实迫使其方向属于 $\{n_A,n_B,n_C,n_D\}$。这四个旋转后的方向仍互异，因而它们给这个四元集合的一个置换 $\pi$，满足 $R_U^{-1}n_g=n_{\pi(g)}$。

每一输入列只能流向这个置换指定的唯一输出方向组。将同方向的所有输出行相加并取迹，再用每列和一，得到

$$
W_g=W_{\pi(g)},\qquad
(W_A,W_B,W_C,W_D)=\nu(4\sqrt3,\sqrt{11},2,\sqrt{11}).
\tag{12.5}
$$

这里必须合并 $0,25$ 后的总迹，不能把两个重复效果误当成五条不同射线。因为 $4\sqrt3>\sqrt{11}>2$，$A,C$ 两组各自固定。于是 $R_U$ 固定两个不共线的向量 $n_A,n_C$。一个正向三维旋转还固定它们的叉积，所以 $R_U=I_3$；交换 $B,D$ 而固定 $A,C$ 的反射不属于 $SO(3)$。最后 $U$ 与全部 Pauli 矩阵交换；先与 $\sigma_z$ 交换使它对角，再与 $\sigma_x$ 交换使两个对角元相同，故 $U=e^{i\gamma}I_2$。

反向取 $T=I_5$ 即成立。若要求列出此时所有 $T$，支撑事实使 $2,3,5$ 三列各自固定，$0,25$ 两列只能在本组内流动。该 $2\times2$ 列随机块须固定权重列 $(3,1)^{\mathsf T}$。置 $T_{25,0}=t$，列归一及这项固定关系给 $T_{00}=1-t$、$T_{0,25}=3t$、$T_{25,25}=1-3t$，非负性恰为 $0\le t\le1/3$。代入 $p_0=3p_{25}$ 验证 (12.2)，包括两个端点。∎

**推论 12.3（静态完备与正随机延拓的分离）。** 令 $\mathcal C=\{p(\rho):\rho\text{ 为 qubit 密度矩阵}\}$。每个 $U$ 在 $\mathcal C$ 上都有唯一的可逆仿射更新 $F_U(p(\rho))=p(U\rho U^*)$，但它可延拓为整个五结果单纯形上的列随机矩阵，当且仅当 $U$ 是标量相位。

证明。定理 3.2 给反演

$$
\mathbf r=\nu^{-1}(p_2+p_{25}-a_\nu,\ p_5+p_{25}-a_\nu,\ p_3-\nu).
\tag{12.6}
$$

将其旋转为 $R_U\mathbf r$ 再代回定义 3.1 就给 $F_U$；逆为 $F_{U^*}$。其随机线性延拓恰是 (12.1)，由定理 12.2 分类。故这里五个精确概率没有丢失 qubit 状态信息；失败发生在要求同一个非负核作用于五个标签这一额外条件。命题 4.3 排除测量通道的 CPTP 左逆，所问对象不同；其证明不承担本分类。∎

## 13. 黄金相位门的三个已知纯目标与正误差下界

**定义 13.1（固定门和三个目标）。** 使用 §7.2 未交换逻辑基时的投影 $P=|1\rangle\langle1|$，固定

$$
U_\star=K_P=\zeta[I+(\zeta-1)P]
=\operatorname{diag}(\zeta,\zeta^2),\quad
\theta=\frac{3\pi}{5},\quad c=\cos\theta=\frac{1-\sqrt5}{4},\quad s=\sin\theta>0.
\tag{13.1}
$$

这是本卷的黄金相对相位门；整体因子 $\zeta$ 不改变密度矩阵共轭。其 Bloch 作用为绕 $z$ 轴旋转 $+\theta$。置

$$
m=R_{U_\star}^{-1}n_B
=\frac{(3c+s,c-3s,1)}{\sqrt{11}},\qquad
\rho_0=\frac{I+\sigma_z}{2},\quad
\rho_1=\frac{I-\sigma_z}{2},\quad
\rho_d=\frac{I-m\cdot\sigma}{2}.
\tag{13.2}
$$

$|m|=1$，故三者均为指定的已知纯目标；下标 $d$ 表示黄金门后效果 $2$ 的暗态。它不表示一个额外探测器。以下只用这三个输入，不假定任意未知输入的实际接入，也不增加混态准备源。

**定理 13.2（三目标的统一总变差阻碍）。** 对每个非负列归一 $5\times5$ 矩阵 $T$，记

$$
e_j(T)=\operatorname{TV}\bigl(Tp(\rho_j),p(U_\star\rho_jU_\star^*)\bigr),
\qquad j\in\{0,1,d\}.
$$

则同时有

$$
\boxed{e_0(T)+e_1(T)+4e_d(T)\ge\nu\sqrt{11}},\qquad
\boxed{\max_{j\in\{0,1,d\}}e_j(T)\ge
\delta:=\frac{\nu\sqrt{11}}6
=\frac{\sqrt{11}}{6(1+2\sqrt3+\sqrt{11})}>0.}
\tag{13.3}
$$

特别地，$\inf_T\max_je_j(T)\ge\delta$；同一个 $T$ 必须同时作用于三个输入。此常数不声称最优。

证明。由 $m=R_{U_\star}^{-1}n_B$，$U_\star^*E_2U_\star=\nu\sqrt{11}(I+m\cdot\sigma)/2$，故

$$
p_2(U_\star\rho_dU_\star^*)=0,\qquad
p_2(U_\star\rho_0U_\star^*)+p_2(U_\star\rho_1U_\star^*)
=\operatorname{Tr}E_2=\nu\sqrt{11}.
\tag{13.4}
$$

第二式也可直接用 $U_\star\rho_iU_\star^*=\rho_i$ 与 $\rho_0+\rho_1=I$ 检验。下面证明逐坐标支配

$$
p_t(\rho_d)\ge\frac14\bigl(p_t(\rho_0)+p_t(\rho_1)\bigr)\qquad(t\in S).
\tag{13.5}
$$

依 (12.4)，只需 $n_t\cdot m\le1/2$。四种内积为

$$
\begin{aligned}
n_A\cdot m&=-\frac{4c-2s+1}{\sqrt{33}},&
n_B\cdot m&=\frac{10c+1}{11},\\
n_C\cdot m&=\frac1{\sqrt{11}},&
n_D\cdot m&=\frac{6c-8s+1}{11}.
\end{aligned}
\tag{13.6}
$$

$-1/3<c<0$，因为 $1<\sqrt5<7/3$；又 $0<s<1$。因此第一项严格小于 $7/(3\sqrt{33})<1/2$，最后的不等式由 $196<297$ 给出；第二、四项严格小于 $1/11<1/2$，第三项也小于 $1/2$。由 $p_t(\rho_d)=w_t(1-n_t\cdot m)/2$ 和 $p_t(\rho_0)+p_t(\rho_1)=w_t$ 即得 (13.5)。这是对固定五效果逐项的检验，包括重复的 $0,25$，不从“信息完备”一词推测正性。

对两个归一分布，单个事件的概率差至多其 TV。非负 $T$ 保持 (13.5)，故由输出坐标 $2$ 得

$$
\begin{aligned}
e_d(T)&\ge (Tp(\rho_d))_2\\
&\ge\frac14\bigl((Tp(\rho_0))_2+(Tp(\rho_1))_2\bigr)\\
&\ge\frac14\bigl(\nu\sqrt{11}-e_0(T)-e_1(T)\bigr).
\end{aligned}
\tag{13.7}
$$

移项给第一界，再用 $e_0+e_1+4e_d\le6\max_je_j$ 给第二界。即使 (13.7) 最后一行的括号为负，移项后的不等式仍然有效。所有分母严格正且 $\nu>0$，故 $\delta>0$。证明只用三个纯态；$\rho_0+\rho_1=I$ 是纸面矩阵恒等式，不是免费执行随机混合的权限。∎

## 14. 原七地址有限正向字及完整旧终端中的稳健转送

**定义 14.1（原生来源和无条件比较律）。** 使用 §8 的同一个十站点、十三维 $\mathcal H$、七地址 $0,\ldots,6$、唯一 ready 种子 $v=e_{00100}$，以及 $V=LJ$。完整终端字母表仍为 $\Omega=\{0,1\}^{10}$，保留全部 $1024$ 个标签。五个理想支撑标签按原顺序为

$$
\begin{array}{c|ccccc}
t&0&2&3&5&25\\ \hline
\ell_t&1000000010&1010000010&1001000010&1000100010&1010100010.
\end{array}
\tag{14.1}
$$

以 $\mathsf I:\mathbb R^5\to\mathbb R^\Omega$ 表示将质量放到这五个标签、其它坐标置零的列随机嵌入。置 $p_j=p(\rho_j)$、$q_j=p(U_\star\rho_jU_\star^*)$。理想完整终端律分别为 $\mathsf I p_j,\mathsf I q_j$。不把其它标签删除后重新归一化。

对每个目标选单位向量 $\psi_j$ 使 $\rho_j=|\psi_j\rangle\langle\psi_j|$，并选数学 $B_j\in U(2)$ 使 $B_j|0\rangle=\psi_j$。定理 8.2 对任意 $\alpha>0$ 给原七地址有限正向制备字 $a_j$，满足

$$
\|K_{a_j}v-V\psi_j\|<\alpha.
\tag{14.2}
$$

定理 8.3 对 $\mathcal G_{U_\star}\in SU(13)$ 和任意 $\beta>0$ 给一个共同的有限正向门字 $g$，满足

$$
\|K_g-\mathcal G_{U_\star}\|_{\mathcal H}<\beta,\qquad
\|K_gK_{a_j}v-VU_\star\psi_j\|<\alpha+\beta.
\tag{14.3}
$$

第二界是酉性和三角不等式；实际中间态不必精确落在 $V$ 码。这里 $B_j,\mathcal G_{U_\star}$ 是编译目标，不是新增可调用控制；实际字仍只使用原地址。比较输入、输出律分别对应同一 ready 源上执行 $a_j$ 后终端读取、执行 $a_j$ 再接 $g$ 后终端读取的两种完整程序，不插入一次中途测量再继续演化。

**定理 14.2（完整标签核、有限编译和实际误差）。** 设同一概率接口下的两组完整终端律 $P_j^{\rm in},P_j^{\rm out}$ 满足

$$
\operatorname{TV}(P_j^{\rm in},\mathsf I p_j)\le a_j^{\rm err},\qquad
\operatorname{TV}(P_j^{\rm out},\mathsf I q_j)\le b_j^{\rm err}.
\tag{14.4}
$$

这里 $a_j^{\rm err},b_j^{\rm err}\ge0$ 为误差界，与制备字 $a_j$ 区别。对每一个固定的非负列归一 $\Omega\times\Omega$ 矩阵 $\mathsf K$，令

$$
r_j(\mathsf K)=\operatorname{TV}(\mathsf KP_j^{\rm in},P_j^{\rm out}),\qquad
d_j=a_j^{\rm err}+b_j^{\rm err}.
$$

则

$$
\begin{aligned}
r_0(\mathsf K)+r_1(\mathsf K)+4r_d(\mathsf K)
&\ge\nu\sqrt{11}-(d_0+d_1+4d_d),\\
\max_jr_j(\mathsf K)&\ge\delta-\max_jd_j.
\end{aligned}
\tag{14.5}
$$

所以 $\max_jd_j<\delta$ 是一个明确的严格正误差区间。核甚至可以使用全部旧终端标签，结论仍成立；它仍须不依赖三种制备设置或其档案。

证明。取任一固定确定性粗映射 $\mathsf D:\Omega\to S$，在五个 $\ell_t$ 上为其逆，在其余标签上例如全映到 $0$。这只用于证明，原记录仍完整保留。于是 $\mathsf D\mathsf I=I_5$，$T=\mathsf D\mathsf K\mathsf I$ 是定理 13.2 允许的同一个五阶列随机矩阵。随机映射收缩 TV，因为对任意实向量 $x$ 有

$$
\sum_s\left|\sum_tT_{st}x_t\right|
\le\sum_{s,t}T_{st}|x_t|=\sum_t|x_t|.
$$

三角不等式和这项收缩性给

$$
\operatorname{TV}(Tp_j,q_j)
\le a_j^{\rm err}+r_j(\mathsf K)+b_j^{\rm err}.
\tag{14.6}
$$

应用 (13.3) 的加权界及最大值界即得 (14.5)。$\mathsf D$ 不按成功条件化，故从未除以小成功概率，也没有丢弃任何泄漏或失败质量。∎

**推论 14.3（编译、执行、读出及统计的分层预算）。** 在明确采用本卷 Born/CP 接口时，精确执行 (14.2)–(14.3) 的有限字给 (14.4) 中

$$
a_j^{\rm err}\le\alpha,\qquad b_j^{\rm err}\le\alpha+\beta.
\tag{14.7}
$$

若真实准备、控制和读出使完整律相对这些精确有限字的 Born 律另有 TV 偏差界 $\eta_j^{\rm in},\eta_j^{\rm out}$，则有效预算为

$$
d_j\le2\alpha+\beta+\eta_j^{\rm in}+\eta_j^{\rm out},\qquad
\max_jr_j(\mathsf K)\ge
\delta-2\alpha-\beta-\max_j(\eta_j^{\rm in}+\eta_j^{\rm out}).
\tag{14.8}
$$

因此理想数学编译取 $\alpha<\delta/8$、$\beta<\delta/4$ 时，余量严格大于 $\delta/2$；真实偏差还须小于相应余量。有限字存在性本身不供应这些实际偏差界。

证明。归一向量 $x,y$ 的纯态距离满足 $D(|x\rangle\langle x|,|y\rangle\langle y|)\le\|x-y\|$，随后完整终端测量不增加距离。代入 (14.2)–(14.3) 得 (14.7)，再两次使用三角不等式得 (14.8)。精确原门保留 $\mathcal H$，故十三路径之外的 $1011$ 个旧标签在精确模型中质量仍为零；五模式之外还有八条合法路径，其制备后与门后总质量分别至多 $\alpha^2$、$(\alpha+\beta)^2$。这些质量全部留在完整 TV 中，不能另删后声称同一个界。真实误差若产生其它旧标签的质量，也计入 $\eta$，不得将它们作为“无效样本”删除。

原七地址来源没有中间随机仪器或可删失败分支，实际档案仍保留制备字 $a_j$、接续 $g$、调用顺序及原十位终端；这是[续卷 II 定义 77.1、83.1](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md) 的原域。字长若为 $\ell_j,m$，两种程序分别花费 $\ell_j$、$\ell_j+m$ 次原门调用，所有调用及档案保留；本推导不给字长上界或免费重置。三种已知目标可以逐精度由旧种子编译，不提供未知态、独立副本、随机混态源或新增测量。完整档案若被用来选择不同的核，便已超出同一个 $\mathsf K$ 的假设，并未被 (14.5) 排除。

有限统计认证又是另一层：若某个已供应的统计方案在同一置信事件上给六个完整经验律 $\widehat P_j^{\rm in},\widehat P_j^{\rm out}$ 及其 TV 半径 $h_j^{\rm in},h_j^{\rm out}$，则在该事件上，同时对所有 $\mathsf K$ 有

$$
\max_j\operatorname{TV}(\mathsf K\widehat P_j^{\rm in},\widehat P_j^{\rm out})
\ge\delta-\max_j(d_j+h_j^{\rm in}+h_j^{\rm out}).
\tag{14.9}
$$

这是 (14.5) 再用两次三角不等式，故也允许在同一批数据后拟合候选核。严格正认证须右侧为正，并须真实具备所声称的共同置信事件。原生单次 ready／终端合同不自动供应独立重复、平稳抽样或这些置信半径；此处不声称已实际执行或获得统计认证。∎

## 15. 本编码的决策后果、来源对应与起源边界

**命题 15.1（五概率自治状态的准确决策范围）。** 本卷完整五概率可重建全部 qubit 密度矩阵，但作为五标签概率空间上的自治状态，它不能用固定非负归一核承载任何非平凡 $U(2)$ 共轭；黄金门还受到 (13.3) 与 (14.5) 的有限正误差约束。保留相干码、引入更大的连续配置空间或保留影响更新的历史／上下文，是与这项结论相容的不同状态合同。

证明。前两句分别由推论 12.3、定理 13.2 和 14.2。定理 4.1 的 $J\rho J^*$ 与定理 8.3 的 $V\rho V^*$ 已给同一载体中的相干实现，并不需要经典随机核。另一方面，把精确 $p\in\mathcal C$ 本身作为一个连续经典配置，以 $p\mapsto F_U(p)$ 确定性更新，在纸面上完全可定义。此时状态空间是连续的 $\mathcal C$，不是从五标签中抽样的一个状态；(12.1) 没有排除这种模型，也未提供其有限精度取得或物理成本。

若扩展只是在五标签前后接固定、与输入及制备无关的随机编码 $A$、扩展核 $M$ 与随机解码 $B$，则 $BMA$ 仍是同一个五阶随机核，故不能绕开定理 12.2。若扩展改为依赖制备的隐藏分布、完整档案、相干上下文或其它未由固定 $A$ 供应的状态，这个因子分解前提不成立，不能据此排除它们。[续卷 II 命题 83.3](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md) 的矩阵群点／射线点及档案模型正属后一范围。保存旧档案的义务没有被新的五概率判据撤销。

因此下一步若要求五标签自治随机闭合，就须放弃本卷的非平凡相干门；若保留这些门，状态或更新合同就须超出该五阶随机核。这个源特定二选一增加了静态表示与相干动力学之间的约束，没有从该约束推导 Born 规则、复数标量或物理相位来源。全部概率比较仍以明确的 Born/CP 接口，或已取得同等完整律的接口为条件。§10 的跨程序同效果匹配仍是额外条件，不能由门的交换性或此处的正误差界推出。续卷 II §134 的实际历史 $7799$ 及其非匹配概率仍保持原值和原结论，本推导未给该历史安装 Born 律。∎

**定义 15.2（外部先例与仓内接口的对应边界）。** 本增补的承重增量为 `repo-derived` 的固定效果分类 (12.2)、黄金门三个明确纯目标的界 (13.3)，以及对原菜单和完整终端的 (14.5)–(14.9) 对应；不主张全球文献优先权。所复用供应如下。

| 供应 | 精确对应与保留边界 |
| --- | --- |
| E. Haapasalo、J.-P. Pellonpää，[*Optimal quantum observables*, 1705.03636v1](https://arxiv.org/pdf/1705.03636v1)，§2 (1b)、脚注 7 及 §5 | `literature-attested`：随机 smearing、秩一 POVM 与 post-processing clean 背景。其概率矩阵采用输入为行；本卷 $T$ 是该约定的转置。正组合的支撑约束用于 (12.3)，但固定方向、重复射线总权重、仅标量相位的分类及黄金门常数由本编码计算，不能归给一般 clean 性质。 |
| T. Theurer、D. Egloff、L. Zhang、M. B. Plenio，[*Quantifying Operations with an Application to Coherence*, 1806.07332v2](https://arxiv.org/pdf/1806.07332v2)，Definition 3、(7)、补充 Proposition 15、(35) | `literature-attested`：给定基底退相干 $\Delta$ 时，detection-incoherent 条件为 $\Delta\Phi=\Delta\Phi\Delta$，相应输出对角系数为输入对角的随机后处理。本卷只要求在固定二维码的全部态上满足 (12.1)，不先要求整个 $M_5$ 上的该条件，也不把它与 creation-incoherence 混同。尤其 $U_\star$ 在逻辑计算基为对角门，并不意味着它在本五效果编码中存在随机更新。 |
| V. I. Yashin、E. O. Kiktenko、A. S. Mastiukova、A. K. Fedorov，[*Minimal informationally complete measurements for probability representation of quantum dynamics*, 2006.13727v2](https://arxiv.org/pdf/2006.13727v2)，§II A、II D、(22)–(23) | `literature-attested`：信息完备概率表示中的通道一般由允许负系数的 pseudostochastic 矩阵描述。该文以 $d^2$ 个效果的 MIC 及其对偶基为前提；本卷五效果含一条重复射线，不能直接冒用其唯一 MIC 矩阵。一般“概率表示不保证随机动力学”是已有背景，本编码的全部可行酉门和三目标常数是这里处理的具体问题。 |
| 本卷 §§3–4、7–8；续卷 II §§77、83 | 已有完整 Bloch 编码、黄金相位矩阵、七地址／十三维有限正向字、唯一 ready 种子、相位平衡表示、全 $1024$ 标签和保档案经典模型。它们分别供应 (12.4)、(13.1)、(14.1)–(14.3) 及命题 15.1 的范围；未新增控制、读口或来源。 |
| [FiveModeMixedCoordinates 的静态共同律响应](../../../Blueprint/D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.scribe.cs) | 对同一给定五模式律，$\{1,x,y,z,xy\}$ 完整表示任意实响应，且明确不据此声称动态充分性。本卷采用的实际量子像还有 $p_0=3p_{25}$；静态函数完备不供应 (12.1) 的非负核。 |
| [自校准 VIII 定义 10.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VIII.md)；[RRO rooted history recovery §§15–19](RECURSIVE_RELATIONAL_OBSERVATION_ROOTED_BOUNDARY_HISTORY_RECOVERY.md) | 前者先给种子概率空间及共同律 $\mu$，后者给确定性读取、实际源像与历史恢复边界。它们均未在本七地址载体上供应未知记录概率、独立重复或 (14.9) 所需的统计置信事件，不用来填补本卷 §10 的实际律缺项。 |

## 追加锚（本行以下为增补区）
