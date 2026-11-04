**AURIC 量子关系研究续篇**

# 共同来源、原子自指 与观察者序列

**候选 C117：保留二元比较的共同细化**

**本轮的两条主线**

完整内部过程保留每一对输入的完整复比较关系，新增记录仍在整体之内。这个二元条件本身推出复线性与等距性；局部忽略记录得到 Kraus 操作。自指原子可以把显示复位为自身，但必须把输入关系转存到内部记录。随后让两位观察者的累计接口共同细化、保持已知关系，并分别覆盖每个有限问题；一致的有限状态族由此唯一重构同一个整体状态泛函。

$$
\langle Vu,Vv\rangle=\langle u,v\rangle,
 \qquad
 \omega_j\circ\iota_{ji}=\omega_i.
$$

 第一式针对完整物理振幅，第二式针对未条件化的观察接口。它们不把当前显示状态、物理条件后态与全部可读历史混成同一个对象。

**与 C116 的关系**

保留 C116 的实二元回路条件以选择三维和内部复结构；把过程的线性与完全正性接口改写为二元比较守恒及内部记录供给，并补齐共同来源与共尾观察的精确定理。这是条件明确的完整候选，不声称从“万物内生”一句话已经无条件推出所有量子公理。

**来源与证明范围**

2026 年 11 月 3 日核读公开 dev 页面、局部规律拼接反例、树上记录扩张与局部边缘盲区源码。未取得最新提交 SHA 或 AURIC 静态纤维主卷全文，故不冒称覆盖最新 HEAD。本文是自足纸笔推导，未执行 Lean 编译或向仓库写入。C117 为本轮研究稿编号。

2026 年 11 月 3 日

## 目录

- [1. 项目接点与对象类型：两位观察者看的是同一整体的什么](#section-1)
- [2. 二元关系的三维有限提升：复结构的来路](#section-2)
- [3. 完整内部过程只保留一条二元比较规则](#section-3)
- [4. 从任意输入返回原子：全局与局部是不同量词](#section-4)
- [5. 一个选择性原子分支能保证什么](#section-5)
- [6. 两个原子起点怎样保持完整比较](#section-6)
- [7. 保留来源的共同细化：从有限窗口构造同一整体态](#section-7)
- [8. 共同来源的比较空间与二元关系球](#section-8)
- [9. 两个移动窗口怎样趋于同一套关系](#section-9)
- [10. 共尾读口不等于条件态轨迹收敛](#section-10)
- [11. 三类运输与三角相位](#section-11)
- [12. 一个几何总图：来源、记录与可读窗口](#section-12)
- [13. 从这份候选恢复通常的量子公理](#section-13)
- [14. 本轮唯一完整候选 C117](#section-14)
- [15. 一段完整的白话描述](#section-15)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 项目接点与对象类型：两位观察者看的是同一整体的什么

本轮实际核读了三类现有源码。局部规律拼接反例说明，三个二元窗口分别要求 $x=y$、$y=z$、$x\ne z$，每个单坐标交叠都容许相同值，却没有共同实现 [2](#ref-repo-gluing)。树上记录扩张则在有限树、变量出现的连通性以及完整交叠投影一致条件下，把给定局部记录扩展到全部记录变量 [3](#ref-repo-tree)。局部边缘盲区给出两 qubit 的 Bell 纯态与经典关联混合态，它们两边的约化态相同，整体却不同 [4](#ref-repo-marginal)。这些是当前可读的已有源码及其声明，不据此声称它们刚刚新增。

这三项恰好限制“两个观察者都在逼近同一个整体”的论证：局部一致需要实际共同延拓；各自看全自己的部分不等于看全关联；经典记录的树上拼接结论不能不加条件地搬到量子边缘态上。

### 定义 1.1（本轮的类型约定）

$\Omega$ 表示保留对象、协议、来源与合法接续的整体。$\mathcal A_\Omega$ 是本候选选取的可观测关系代数；$\omega$ 是其上的正归一化状态泛函。有限窗口为 $\mathcal A_i$，其未条件化的状态为 $\omega_i$。具体门历史 $h$ 的条件后态则记为 $\omega_h$。它们分别属于整体、关系代数、评价和条件分支四个不同层级。

在矩阵窗口中，$\omega(X)=\operatorname{Tr}(\rho X)$；合法幅度历史 $h$ 的成功权重和条件评价为

$$
p_h=\omega(h^*h),\qquad
 \omega_h(X)=\frac{\omega(h^*Xh)}{p_h}\quad(p_h>0).
$$

显示态可能相同，完整记录不同；窗口可能扩大，条件态却仍振荡。下文把这几种情形分别定理化。

### 1.1 内容作为地址：可生成不等于唯一编码

原始协议历史可以作为内容的构造地址，记其求值为 $\operatorname{ev}_\omega(h)$。但不同词可能具有相同作用，例如 $XX=I$；相同当前态也可能保留不同来源或定义域。把内容等同于一个唯一的语法地址，需要额外选定规范编码，不能从量子态相同直接推出。

### 命题 1.2（保留合法接续的读口下降）

设 $q:\Omega\to X$，内部部分操作为 $T:A\to\Omega$。操作的可执行性与结果完全由 $q$ 决定，当且仅当

$$
q(h)=q(k)\Longrightarrow(h\in A\Longleftrightarrow k\in A),
$$

$$
h,k\in A,\ q(h)=q(k)\Longrightarrow q(Th)=q(Tk).
$$

此时 $\bar T(q(h))=q(Th)$ 唯一良定义。

**证明。**
第一式使定义域是读口纤维的并，第二式使输出在每个定义纤维内恒定，故可下降到像集。反向由操作完全由读数决定立即成立。

这延续项目的目标恢复判据及隐藏存档改变后续时间合成域的反例 [5](#ref-repo-recovery)、[6](#ref-repo-domain)。一种稳妥的“完整内容”定义，是一个地址对全部合法未来询问的响应连同这些询问的定义域；在这一层的等价才足以支持所声明的接续替换。协议名称或来源元数据若可被独立区分，应明确属于输入记录，不能宣称从一个未知非正交量子态中无代价读取其唯一名称。

**白话。**两个人可以从不同入口开始读同一个整体，也可以共享某些门或历史片段。起点不同并不迫使每一步都不同。真正需要比较的是：他们已经读到了什么、哪些来源仍保留着、下一步允许问什么。同一个画面可以有不同来路，所以当前画面本身不能冒充完整地址。

<a id="section-2"></a>

## 2. 二元关系的三维有限提升：复结构的来路

<a id="sec-c117-local"></a>

一个常值复位映射在经典概率论中也存在；一个正核在实 Hilbert 空间中同样存在。因此，观察者自指与共同来源本身尚不能选择复量子理论。本节把 C116 的局部选择条件及证明压缩重述，使本稿不必把复数、两分量振幅当作未声明的起点 [7](#ref-c116)。它属于固定球形二元类中的条件重构；一般 Jordan 代数的动力学对应和复结合结构有既有研究 [8](#ref-alfsen)，这里不把这类历史结果宣称为新发现。

### 2.1 实锥与规范对称变化

### 定义 2.1（二元比较块）

令 $W$ 为有限维实欧氏空间，$V=\mathbb R e\oplus W$、$e=(1,0)$。未归一化的正关系为

$$
C=\{(s,r):s\ge\|r\|\},\qquad
 \langle (s,r),(t,u)\rangle_E=st+r\cdot u.
$$

规范滤片是把 $e$ 送到给定严格正元 $x=(s,r)$ 的欧氏正定、自伴、双向保锥线性变换。双向保锥指变换及其逆都保持 $C$。

### 引理 2.2（规范滤片及其导数）

令 $\delta=\sqrt{s^2-\|r\|^2}>0$。唯一的规范滤片是

$$
P_x=\begin{pmatrix}
 s&r^{\mathsf T}\\
 r&\delta I+rr^{\mathsf T}/(s+\delta)
 \end{pmatrix}.
$$

其一阶响应定义对称乘法

$$
(\alpha,a)\circ(\beta,b)
 =\left.\frac{d}{dt}P_{e+t(\alpha,a)}(\beta,b)\right|_{0}
 =(\alpha\beta+a\cdot b,\alpha b+\beta a).
$$

特别地，$L_a(\beta,b)=(a\cdot b,\beta a)$。

**证明。**
写 $\eta=\operatorname{diag}(1,-I)$。保锥可逆变换 $T$ 保持锥边界，所以对所有单位 $n$，$Q(T(1,n))=0$。将 $T^{\mathsf T}\eta T$ 分块，比较 $n,-n$ 消去非对角块，再比较正交基与它们的二元和，得 $T^{\mathsf T}\eta T=c\eta$；$Te$ 在锥内部给 $c>0$。

若 $T=T^{\mathsf T}\succ0$ 且 $Te=x$，写其右下块为 $B$，便有 $c=\delta^2$、$B^2=\delta^2 I+rr^{\mathsf T}$。正定 $B$ 是右侧唯一正平方根，在 $r^\perp$ 上为 $\delta I$、在 $r$ 方向为 $s$，即显示公式。反过来，该公式的特征值为 $s\pm\|r\|$ 及 $\delta$，全为正；直接相乘验证 $P_x\eta P_x=\delta^2\eta$，且 $P_xe=x$，从而双向保锥。对 $s=1+t\alpha,r=ta$ 求导即得乘法。该乘法满足 Jordan 恒等式，因为 $L_{z^2}$ 是 $L_z$ 的线性组合；其平方锥恰为 $C$，可用互补幂等元 $p_\pm=(1,\pm n)/2$ 对正元分解并开平方验证。

这一构造仍承担球形正锥、欧氏标尺和规范滤片的定义。若赋予它物理实现，还要保留成功权重；双向保正滤片不等于确定性的可逆通道。

### 2.2 二元回路为何强制三维

### 定义 2.3（旁观方向条件）

每个实方向 $a$ 产生 $D_a\in\mathfrak{so}(W)$，$a\mapsto D_a$ 实线性，$D_a a=0$，且 $D\ne0$。要求对全部标签及其线性合成，

<a id="eq-c117-spectator"></a>

$$
\boxed{[D_a,D_b]z=0\quad(z\perp a,b).}
\tag{1}
$$

这是完整向量等式。只比较 $z\cdot[D_a,D_b]z$ 没有约束力，因为反对称算子的该自比较总是零。

### 定理 2.4（三维选择）

<a id="thm-c117-three"></a>

上述条件强制 $\dim W=3$，且存在 $\kappa>0$，使

<a id="eq-c117-loop"></a>

$$
\begin{aligned}
[D_a,D_b]&=-\kappa[L_a,L_b],
\end{aligned}
\tag{2}
$$

<a id="eq-c117-square"></a>

$$
\begin{aligned}
D_a^2x&=\kappa\bigl((a\cdot x)a-\|a\|^2x\bigr),
\end{aligned}
\tag{3}
$$

<a id="eq-c117-triple"></a>

$$
\begin{aligned}
D_aD_bx&=\kappa\bigl((a\cdot x)b-(a\cdot b)x\bigr),
\end{aligned}
\tag{4}
$$

<a id="eq-c117-bracket"></a>

$$
\begin{aligned}
D_{D_a b}&=[D_a,D_b].
\end{aligned}
\tag{5}
$$

按 $D$ 选择取向后，$D_ab=\sqrt\kappa\,a\times b$。

**证明。**
标签线性及 $D_aa=0$ 给 $D_ab=-D_ba$，故 $x\cdot D_ab$ 是交替三形式。令

$$
B(a,b)x=(b\cdot x)a-(a\cdot x)b=[L_a,L_b]x.
$$

交换子 $[D_a,D_b]$ 反对称。式 [(1)](#eq-c117-spectator) 使它在 $\operatorname{span}(a,b)^\perp$ 上为零，并保持 $\operatorname{span}(a,b)$；二维反对称算子只有一个方向，所以它是 $B(a,b)$ 的实倍数。

这个倍数不能逐对自由选。取正交基 $e_i$，写 $[D_{e_i},D_{e_j}]=\lambda_{ij}B(e_i,e_j)$。在二元合成标签

$$
a=\sum_i e_i,\qquad b=\sum_i\left(i-\frac{n+1}{2}\right)e_i
$$

上展开，其每个基对系数都是非零的 $j-i$。合成对也必须有一个共同平面比例，比较基系数便得全部 $\lambda_{ij}=\lambda$。双线性将它扩到任意 $a,b$。

将交换子等式作用于 $a$ 并使用反对称性，得

$$
\|D_ab\|^2=-\lambda\bigl(\|a\|^2\|b\|^2-(a\cdot b)^2\bigr).
$$

非平凡性排除 $\lambda=0$，故 $\lambda=-\kappa<0$，并得 [(3)](#eq-c117-square)。极化该平方式，加上交换子式，给 [(4)](#eq-c117-triple)；再由 $D_{D_ab}x=-D_xD_ab$ 得 [(5)](#eq-c117-bracket)。

取正交单位 $u,v$，令 $w=D_uv/\sqrt\kappa$。上式说明 $u,v,w$ 正交归一，且

$$
D_w=\sqrt\kappa(vu^{\mathsf T}-uv^{\mathsf T}),\qquad
 D_w^2=-\kappa(P_u+P_v).
$$

另一方面，式 [(3)](#eq-c117-square) 给 $D_w^2=\kappa(P_w-I)$。因此

$$
\boxed{I=P_u+P_v+P_w,}
$$

恰好三个方向覆盖整个 $W$。三维交替三形式只有一个尺度，范数式将其大小固定为 $\sqrt\kappa$；取向由其符号决定。

若去掉 $D\ne0$，任意维度都容许 $D=0$。若只查坐标对，模型 $W=\mathbb R^3\oplus\mathbb R$、$D_ab=(a'\times b',0)$ 会通过；但对 $a=e_1+e_4,b=e_2,z=e_1-e_4$，有 $z\perp a,b$ 而 $[D_a,D_b]z=e_2$。这说明必须检验合成标签。此规则只作用于二元球块，不能把它逐字施加到一般高维系统的全部自伴元。

### 2.3 三方向的有向体积成为内部复数

用实数对构造 $\mathbb C_J=\{s+Jt\}$，其中 $J^2=-1$。在 $\mathbb C_J\oplus\mathbb C_J^3$ 上定义

<a id="eq-c117-product"></a>

$$
(\alpha,a)(\beta,b)
 =(\alpha\beta+a\cdot b,\alpha b+\beta a+J(a\times b)).
\tag{6}
$$

这里的点积、叉积作复双线性延伸。

### 定理 2.5（内部复代数及最小振幅）

<a id="thm-c117-complex"></a>

式 [(6)](#eq-c117-product) 给出实八维结合 $*$-代数，伴随为逐分量复共轭，自伴部恰为原来的 $V$。对于正向正交基，

$$
e_ie_j+e_je_i=2\delta_{ij}1,
 \qquad J=e_1e_2e_3,
 \qquad J^2=-1.
$$

因此 $J$ 实际属于三个实方向生成的闭包；该闭包是 $\operatorname{Cl}_{3,0}\cong M_2(\mathbb C)$，最小左理想为 $H\cong\mathbb C^2$。

**证明。**
由三线性，只需在三个实向量上核对结合律。两个括号方式的标量项相同，向量差为

$$
(a\cdot b)c-(b\cdot c)a-(a\times b)\times c+a\times(b\times c)=0,
$$

这是定理 [2.4](#thm-c117-three) 的三重积恒等式。共轭将 $J$ 变号，交换向量次序也使叉积变号，故 $(xy)^*=y^*x^*$。直接计算得 $e_1e_2=Je_3$，从而 $e_1e_2e_3=J$，没有再添独立复方向。

映射

$$
\alpha1+z\cdot e\longmapsto
 \begin{pmatrix}\alpha+z_3&z_1-iz_2\\z_1+iz_2&\alpha-z_3\end{pmatrix}
$$

保持乘法与伴随，且每个复二阶矩阵唯一具有这种展开，所以是同构。由反交换关系可把全部生成词约到八个有序单项式，故此八维闭包也是相应实 Clifford 商代数。

令 $p=(1+e_3)/2,q=e_1p$。左理想 $\mathcal A p$ 由 $p,q$ 张成，且对 $x=\alpha p+\beta q,y=\gamma p+\delta q$，

$$
x^*y=(\bar\alpha\gamma+\bar\beta\delta)p.
$$

这个系数给正定复内积。矩阵表示说明它是二维且为最小左理想，代数在其上忠实作用。

自伴元 $sI+r\cdot\sigma$ 的特征值是 $s\pm\|r\|$，所以构造后的矩阵正锥恰好恢复原来的 $C$。其归一化截面是三维球，极点是球面；概率与纯态的严格对应将在第 [13](#sec-c117-full-theory) 节证明。

最初的二次式也有准确位置：

$$
a^2+xab+b^2
 =\left(1+\frac{x}{2}\right)\frac{(a+b)^2}{2}
 +\left(1-\frac{x}{2}\right)\frac{(a-b)^2}{2}.
$$

当等值为 $1$，$x=0$ 才是圆；$x=2$ 是 $(a+b)^2=1$ 的两条直线。$ab$ 为双线性项，对两个变量共同仍是二次。真正的比较解释是 $\|au+bv\|^2=a^2+b^2+2ab\,u\cdot v$：$x=2$ 表示两个单位方向重合，关系表降秩。复杂相位下的二元表将在第 [9](#sec-c117-windows) 节进入三维球。

**白话。**先规定两份方向怎样比较，再比较沿它们前后运动的小回路。回路不能暗中推动和这两个方向都垂直的完整参考；对合成方向也这样要求，两个方向就会带出第三个，而且三个已经覆盖整个二元块。把三个方向按顺序相乘，会得到一个再乘自己就反号的内部关系，它承担复数的作用。这样的复结构有了明确来路；观察者的记录守恒接下来才有可用的物理振幅空间。

<a id="section-3"></a>

## 3. 完整内部过程只保留一条二元比较规则

本节使用第 [2](#sec-c117-local) 节重述的物理复振幅空间，效果概率的自足证明见第 [13](#sec-c117-full-theory) 节。这延续 C116 的系统类型 [7](#ref-c116)，不把任意历史核的 GNS 比较空间直接认作物理振幅空间。需要重新组织的是过程接口：一个完整过程的输出包含当前读口与全部内部记录，暂时不读某些记录不等于整体已经删除它们。

### 定义 3.1（完整比较守恒）

<a id="def-c117-comparison"></a>

设 $H$ 为输入的物理振幅空间，$H_{\rm out}$ 为输出读口的振幅空间，$R$ 为内部记录空间。一个完整过程最初只规定为函数

$$
V:H\longrightarrow H_{\rm out}\otimes R,
$$

并要求对完整输入空间中的所有 $u,v$，

<a id="eq-c117-pair-law"></a>

$$
\boxed{\langle Vu,Vv\rangle=\langle u,v\rangle.}
\tag{7}
$$

内积约定对第一变量共轭线性。式中保留的是完整复比较值，不只是它的模平方。

这个条件作用于完整、未选择结果的内部过程。只看局部读口，或已经选择成功结果并重新归一化以后，一般不再保持同一内积。输入量词还必须覆盖整个声明的比较空间；有限受限菜单本身不自动供应下面证明所用的全部和与复倍数。

完整复比较使用同一个内部相位参考与相干合成接口下的幅度代表。孤立的物理射线只确定内积的模，不能独立指定这项复比较的相位；相干控制两条历史并保留参考，才使相对相位成为比较数据。改变代表时应同时改变相应坐标与编码，不把任意相位约定当作额外的可观测内容。这里的参考同样属于 $\Omega$。

### 定理 3.2（二元关系守恒自动迫出复线性）

<a id="thm-c117-linear"></a>

满足式 [(7)](#eq-c117-pair-law) 的函数 $V$ 必为复线性等距映射，故 $V^*V=I_H$。无需另行假设线性。

**证明。**
首先 $\|V0\|^2=0$，所以 $V0=0$。令 $A=V(u+v)$、$B=Vu+Vv$。比较守恒给

$$
\|A\|^2=\|B\|^2=\|u+v\|^2,
 \qquad
 \langle A,B\rangle=\langle u+v,u\rangle+\langle u+v,v\rangle=\|u+v\|^2.
$$

因此 $\|A-B\|^2=0$，即 $V(u+v)=Vu+Vv$。再令
$A=V(\lambda u)$、$B=\lambda Vu$。两者平方范数均为 $|\lambda|^2\|u\|^2$，而

$$
\langle A,B\rangle=\lambda\langle V(\lambda u),Vu\rangle
 =\lambda\langle \lambda u,u\rangle=|\lambda|^2\|u\|^2.
$$

所以 $V(\lambda u)=\lambda Vu$。复线性与保内积合起来就是 $V^*V=I_H$。

若只保留 $|\langle u,v\rangle|^2$，复共轭这类反酉映射也可以通过检验，因此不能用它替代式 [(7)](#eq-c117-pair-law) 中包含取向的比较值。

### 3.1 记录展开给出全部 Kraus 形式

### 定理 3.3（完整内部记录与量子通道）

<a id="thm-c117-record"></a>

选 $R$ 的正交基 $\{\lvert j\rangle\}$，写

$$
V\psi=\sum_jK_j\psi\otimes\lvert j\rangle.
$$

则 $\sum_jK_j^*K_j=I$，忽略记录得到

$$
\Phi(\rho)=\operatorname{Tr}_R(V\rho V^*)=\sum_jK_j\rho K_j^*.
$$

该映射在任意有限内部参考下完全正且保迹。反之，每个有限维完全正保迹映射都有这样的完整记录实现。

**证明。**
定义 $K_j=(I\otimes\langle j\rvert)V$，由记录基完备性有
$\sum_jK_j^*K_j=V^*V=I$；按该基计算部分迹便得公式。若还保留参考 $Q$，则

$$
(\Phi\otimes\operatorname{id}_Q)(X)
 =\operatorname{Tr}_R\bigl[(V\otimes I_Q)X(V^*\otimes I_Q)\bigr]\ge0
 \qquad(X\ge0).
$$

正性来自合同变换与部分迹保正；后者可逐个向量检验为
$\langle x,\operatorname{Tr}_R(Y)x\rangle=\sum_j\langle x\otimes j,Y(x\otimes j)\rangle\ge0$。迹由 $V^*V=I$ 保持。

反向可直接使用有限 Choi 构造。对输入维数 $d$，令
$\lvert \Gamma_d\rangle=\sum_i\lvert i,i\rangle$。完全正性使
$(\Phi\otimes\operatorname{id}_d)(\lvert \Gamma_d\rangle\langle \Gamma_d\rvert)$ 为正；将其谱向量按输出、输入指标重排为矩阵 $K_j$，逐个比较矩阵单位得到 $\Phi(X)=\sum_jK_jXK_j^*$。保迹给 $\sum_jK_j^*K_j=I$，故所列 $V$ 等距。

这把 C116 的任意参考正性改写成一个完整记录接口；在所述有限模型上两种描述等价，不声称数学约束因此严格变弱。若模型供应全部此类等距接口，就得到全部相应通道；一个较小菜单是否已覆盖全部通道，仍须另证，不能仅凭表示定理自动扩大。

正交记录可以按可见结果分组。若一组结果对应若干标签 $j$，该分支是相应 Kraus 项之和。一个可见结果不必只有一个 Kraus 算子：未读的细记录仍属于 $\Omega$，也仍可携带量子相干与参考关系。

### 3.2 选择性过程必须把失败分支补回

若成功分支为 $\mathcal I(\rho)=\sum_jK_j\rho K_j^*$，令
$E=\sum_jK_j^*K_j\le I$。成功概率为 $\operatorname{Tr}(\rho E)$，正概率时的条件后态为 $\mathcal I(\rho)/\operatorname{Tr}(\rho E)$。零概率时不定义这个条件化结果。

### 命题 3.4（保持类型的完整补全）

<a id="prop-c117-completion"></a>

任意上述不增迹分支都能成为完整比较守恒过程的一部分。

**证明。**
若输入输出为同一空间，可增加 $K_{\rm fail}=\sqrt{I-E}$。若两者维数不同，这个平方根的类型是 $H\to H$，不能直接当作 $H\to H_{\rm out}$ 的算子。

一般情况下，在记录中取正交直和 $R=R_{\rm succ}\oplus H$，记 $J_f:H\to R$ 为第二个分量的等距嵌入，并选输出中的一个单位向量 $a$。定义

$$
\widetilde V\psi
 =\sum_jK_j\psi\otimes\lvert {\rm succ},j\rangle
   +a\otimes J_f\sqrt{I-E}\,\psi.
$$

两类记录正交，故
$\widetilde V^*\widetilde V=E+(I-E)=I$。
在输入正交基上展开失败记录，等价于补入

$$
L_i=\lvert a\rangle\langle i\rvert\sqrt{I-E},\qquad
 \sum_iL_i^*L_i=I-E.
$$

它们具有正确的输入输出类型。失败时也保留剩余输入的记录，而非把失败定义成整体消失。

**白话。**把一次操作连同所有结果一起看，任意两份输入原有的比较关系都必须还在。这个二元条件已经迫使完整过程线性。把未读记录暂时略去，才出现通常的量子通道；只选一个成功结果，又出现条件化。它们看起来会损失信息，是因为读口的范围变小，完整内部过程并没有因此丢掉那些关系。

<a id="section-4"></a>

## 4. 从任意输入返回原子：全局与局部是不同量词

这里先把“返回自身”严格解释为返回指定的纯读口 $P_a=\lvert a\rangle\langle a\rvert$，$\|a\|=1$。一个门或程序本身属于过程类型；若还要求输出其编码，则必须另给编码接口，不能把两种类型直接写成同一个等式。

### 命题 4.1（任意完整输入不能被等距地压成同一射线）

<a id="prop-c117-global-reset"></a>

若 $\dim H>1$，不存在等距映射把每个单位输入都送到同一条固定射线。更一般地，若 $U$ 是整个封闭空间 $H_A\otimes R$ 上的满射酉算子，且 $\dim H_A>1$，则它不可能对所有全局输入都把 $A$ 因子置于同一个纯态 $a$。

**证明。**
第一种要求会把两个正交单位输入送到同一射线，输出内积的模为一，违反输入内积为零。即使允许输入相关的整体相位，矛盾仍成立。

第二种要求使 $\operatorname{Ran} U\subseteq\mathbb C a\otimes R$，因而
$(P_a\otimes I_R)U=U$。右乘 $U^*$ 得 $P_a\otimes I_R=I$，与 $\dim H_A>1$ 矛盾。此满射论证不依赖有限维。

“某个指定的物理输入”与“任意完整输入”不能互换。对单个给定单位向量 $\psi_0$，总能通过补齐正交基找到把它送到指定向量的酉算子；这不是同一个门对全部输入生效的证明，也不自动提供从未知输入构造那个门的算法。本稿的 $\omega$ 是状态泛函，可能为混态，不能直接当作这里的物理单位向量；同一系统上的酉变换保持密度矩阵的谱，不能把混态整体变为纯态。若另选纯化，还必须明确其物理空间与保留的因子。若输入已经包含全部封闭内容，就不能再把用于保存输入的另一部分默默放到它之外。

### 4.1 局部复位的精确记录定理

### 定理 4.2（局部纯复位必把完整输入移入记录）

<a id="thm-c117-reset"></a>

设 $V:H_d\to H_A\otimes R$ 等距，且每个单位输入都满足

$$
\operatorname{Tr}_R(V\lvert \psi\rangle\langle \psi\rvert V^*)=P_a.
$$

则存在一个等距映射 $W:H_d\to R$，使

<a id="eq-c117-reset-factor"></a>

$$
\boxed{V\psi=a\otimes W\psi.}
\tag{8}
$$

因此 $\dim R\ge d$，并且

<a id="eq-c117-record-gram"></a>

$$
\boxed{\langle W\psi,W\phi\rangle=\langle \psi,\phi\rangle.}
\tag{9}
$$

**证明。**
对每个单位 $\psi$，有

$$
\|((I-P_a)\otimes I_R)V\psi\|^2
 =\operatorname{Tr}[(I-P_a)P_a]=0.
$$

所以 $\operatorname{Ran} V\subseteq\mathbb C a\otimes R$。定义
$W=(\langle a\rvert\otimes I_R)V$，就有 $V=a\otimes W$，且
$W^*W=V^*V=I$。内积与维数结论直接成立。

这是 no-hiding 结构的纯输出有限维情形 [10](#ref-nohiding)。记录不是只保存“曾经有过一个输入”的经典标号；它必须保持输入的相干关系。如果输入还与参考 $Q$ 纠缠，式 [(8)](#eq-c117-reset-factor) 接上 $I_Q$ 后表明这些参考关系也完整移到 $R\otimes Q$。

### 推论 4.3（有限输入族的最小记录容量）

<a id="cor-c117-record-rank"></a>

只要求在有限输入族 $\{\psi_h\}$ 及其线性张成空间上忠实复位时，最小记录维数恰为 Gram 表

$$
K(h,k)=\langle \psi_h,\psi_k\rangle
$$

的秩。

**证明。**
式 [(9)](#eq-c117-record-gram) 要求记录向量具有同一 Gram 表，因此它们张成的维数至少为 $\operatorname{rank} K$。反向，取这个正核的最小 Gram 实现 $\{r_h\}$。映射
$\sum_hc_h\psi_h\mapsto\sum_hc_hr_h$ 良定义且保持内积，因为两边有同一零范数关系；再张量上 $a$ 即达到下界。

若要求覆盖整个 $H_d$，容量下界仍是 $d$；不能因为已测试的输入族秩较小，就把全空间所需记录缩小。一个指定纯输入 $\psi_0$ 的单元素族只有秩一，正好说明为什么单个已知纯输入与任意输入是不同命题；这一说法不把一般状态泛函 $\omega$ 默认为物理纯向量。原始来源若还有可区分的历史标签，保留其出处可能需要这个约化 Gram 表之外的记录。

### 例 4.4（达到下界的 SWAP 复位）

<a id="ex-c117-swap"></a>

取与输入同维的内部参考 $R$，预备在已知纯态 $a$。则

$$
U_{\rm swap}(\psi_A\otimes a_R)=a_A\otimes\psi_R.
$$

这实现全部输入的局部复位，记录维数恰为 $d$。但它只对已经声明的准备支持 $H_A\otimes\mathbb C a_R$ 有此性质；若参考输入为 $b$，同一 SWAP 给出 $b_A\otimes\psi_R$。因而它没有反驳全局任意输入的不可能性。

一般维数下，$V\psi=a\otimes\psi$ 同样达到最小记录下界；要把它落实为封闭酉实现，需在 $\Omega$ 内供应相应的准备资源与支持空间。这个准备条件不是由“自指”自动生成的。若连续接收 $N$ 个任意独立的 $d$ 维输入，并把它们的局部输出全部固定，则同一定理作用于 $H_d^{\otimes N}$ 给记录维数至少 $d^N$。有限记录不能无上限地吸收新的独立量子内容。

**白话。**一个读口可以从任何输入回到同一个原子。它付出的条件是：输入之间原有的区别必须完整移到内部记录里。若把那些记录也算进整个 $\Omega$，整体当然没有都变成同一个原子。原子提供相同的当前读口，记录保留不同的来路；这两个角色可以同时成立。

<a id="section-5"></a>

## 5. 一个选择性原子分支能保证什么

### 定理 5.1（恒定纯输出分支的完整分类）

<a id="thm-c117-pure-branch"></a>

设 $\mathcal I:M_d(\mathbb C)\to M_m(\mathbb C)$ 为完全正不增迹分支，且每个输出都支持在固定射线 $\mathbb C a$，允许零输出。则恰存在效果 $0\le E\le I$，使

$$
\mathcal I(\rho)=P_a\operatorname{Tr}(E\rho).
$$

其最少 Kraus 数为 $\operatorname{rank} E$。对每个归一化输入都有非零成功概率，当且仅当 $E$ 正定。

**证明。**
取 Kraus 表示 $\mathcal I(\rho)=\sum_\mu K_\mu\rho K_\mu^*$。对纯输入 $\psi$，将输出投影到 $a^\perp$，得到

$$
\sum_\mu\|(I-P_a)K_\mu\psi\|^2=0.
$$

每项非负，故全部为零，对所有 $\psi$ 成立。因此每个 $K_\mu$ 的像都包含于 $\mathbb C a$，可写为
$K_\mu=\lvert a\rangle\langle v_\mu\rvert$。令
$E=\sum_\mu\lvert v_\mu\rangle\langle v_\mu\rvert$，立即得到所述公式；不增迹给 $E\le I$。反向用 $E$ 的谱分解便得到这样的 Kraus 实现。

$E$ 是若干秩一矩阵之和，所用项数至少为 $\operatorname{rank} E$；谱分解达到这个数。成功概率为 $\operatorname{Tr}(E\rho)$。若 $E$ 有非零核，其中的纯态成功率为零；若 $E>0$，则所有成功率至少为 $\lambda_{\min}(E)>0$。

特别地，单个非零 Kraus 算子必为

$$
K=\sqrt\eta\,\lvert a\rangle\langle b\rvert,
 \qquad \|a\|=\|b\|=1,\quad0<\eta\le1,
$$

其成功概率为 $\eta\langle b,\rho b\rangle$，纯输入时为
$\eta|\langle b,\psi\rangle|^2$。当 $d>1$，它必在 $b^\perp$ 上失败。因此“一个相干分支恒定输出纯原子”不能同时保证任意输入都有非零成功率。一个可见结果若合并了多个未读记录，则不受单 Kraus 的这个限制；对全部输入成功需要 $E>0$，也就至少需要 $d$ 个 Kraus 记录方向。

若输入输出已经识别为同一空间，并进一步要求单 Kraus 门在自身目标 $a$ 上以概率一成功，则

$$
1=\eta|\langle b,a\rangle|^2\le\eta\le1.
$$

所以 $\eta=1$，$b$ 与 $a$ 同射线，$K$ 是投影 $P_a$ 的相位倍数。它保持自身，却必然拒绝正交输入。

### 5.1 固定点不等于程序已经编码了自己

在同一个输入输出系统上，确定性替换通道

$$
\mathcal R_a(\rho)=P_a\operatorname{Tr}\rho
$$

满足 $\mathcal R_a(P_a)=P_a$、$\mathcal R_a^2=\mathcal R_a$。这确实使 $a$ 成为局部固定点；完整实现则仍受定理 [4.2](#thm-c117-reset) 约束。若一个可逆过程满足 $\Phi^2=\Phi$，复合逆映射立即给 $\Phi=\operatorname{id}$，所以非平凡幂等复位不是可逆全局门。

以下几种“自身”需要不同的接口：

| 状态固定点 | $\Phi(P_a)=P_a$，只表示该状态不变。 |
|---|---|
| 过程幂等 | $\Phi^2=\Phi$，只表示重复运行不再改变该过程的结果。 |
| 程序自我编码 | 需要给出编码 $\operatorname{code}(\Phi)$、解释器及输出一致性；固定点不提供这些数据。 |
| 经典 quine | 程序输出自己的经典编码文本；它不是任意未知量子态的复制规则。 |
| 量子复制 | 要求未知 $\psi$ 产生两个同态副本，是另外一个过程命题。 |

最后一项仍由二元关系直接约束。若完整复制实现对两个输入给
$V\psi=\psi\otimes\psi\otimes r_\psi$、
$V\phi=\phi\otimes\phi\otimes r_\phi$，则

$$
\langle \psi,\phi\rangle=
 \langle \psi,\phi\rangle^2\langle r_\psi,r_\phi\rangle.
$$

当 $0<|\langle \psi,\phi\rangle|<1$ 时，取模得到
$|\langle \psi,\phi\rangle|\le|\langle \psi,\phi\rangle|^2$，矛盾。已知经典程序的正交编码可以复制，并不违背这条约束；其叠加输入一般会形成相关记录，而非两个独立同态副本。精确、确定且使用有限程序寄存器的通用量子编程也另有自己的限制 [11](#ref-programming)，不能由一个自复位固定点替代其条件。

### 5.2 一个可明确实现的有限自描述原子族

### 命题 5.2（程序运行后输出自己的码）

<a id="prop-c117-self-code"></a>

取程序空间 $H_P=\mathbb C^N$，显示与记录 $H_S,H_R\cong\mathbb C^d$，$N\le d$。用同一有限码表的正交向量 $\lvert j\rangle$ 分别标记程序和显示；内部解释规则为

$$
\operatorname{code}(\mathcal R_j)=\lvert j\rangle,
 \qquad \mathcal R_j(\rho)=\lvert j\rangle\langle j\rvert\,\operatorname{Tr}\rho.
$$

存在一个固定内部酉解释器，在记录准备为 $\lvert 0\rangle_R$ 时，使每个程序对任意局部输入运行后，在显示端输出自己的码，同时保留原输入。

**证明。**
对每个 $j$ 取已知酉矩阵 $U_j$，使 $U_j\lvert 0\rangle=\lvert j\rangle$。定义

$$
U=\sum_{j=1}^{N}\lvert j\rangle\langle j\rvert_P\otimes
 \left[\operatorname{SWAP}_{SR}(I_S\otimes U_j)\right].
$$

程序投影正交且总和为 $I_P$，各块为酉，故 $U$ 酉。直接作用得到

$$
\boxed{U(\lvert j\rangle_P\otimes\psi_S\otimes\lvert 0\rangle_R)
       =\lvert j\rangle_P\otimes\lvert j\rangle_S\otimes\psi_R.}
$$

对任意局部密度矩阵 $\rho$，输出为
$\lvert j\rangle\langle j\rvert_P\otimes\lvert j\rangle\langle j\rvert_S\otimes\rho_R$；若有参考纠缠，原有联合关系相应移到记录与参考。程序不变，显示输出该程序的码，因此实现所声明的解释规则。

这给“门输出自身”一个确切的有类型含义：输出的是该门在固定解释器中的编码，不是把过程与状态强行认作同一类型。码表与解释器都是本模型内部的对象，但不是从一个固定点凭空推导出的。如果程序是 $\sum_jc_j\lvert j\rangle$，显示与程序成为 $\sum_jc_j\lvert j,j\rangle$ 的相关态，不是两个独立的未知态副本。构造也不输出整个解释器 $U$ 的编码，不覆盖任意非正交量子程序，更不取消记录的固定准备条件。它证明一族精确自描述原子存在；项目原生的“内容即地址”解释器是否实现同一接口，仍可另行检验。

<a id="section-6"></a>

## 6. 两个原子起点怎样保持完整比较

### 定义 6.1（完整起点编码与合法支持）

<a id="def-c117-origin"></a>

设不同起点 $a,b,\ldots$ 的完整表示是同一输入比较空间上的等距映射

$$
V_a:H\to E_a,\qquad V_a^*V_a=I_H.
$$

记合法像空间的投影为 $\Pi_a=V_aV_a^*$。这里共享的是整个 $H$ 的表示接口，不只是这些映射都曾作用于一个指定输入向量 $\psi_0$。

### 定理 6.2（起点比较形成带支持的群胚）

<a id="thm-c117-origin-transport"></a>

令 $T_{ba}=V_bV_a^*$。则

$$
T_{ba}^*T_{ba}=\Pi_a,\qquad
 T_{ba}T_{ba}^*=\Pi_b,
 \qquad T_{ba}V_a=V_b.
$$

因此它在合法像空间之间等距、满射，并满足

<a id="eq-c117-cocycle"></a>

$$
\boxed{T_{ab}=T_{ba}^*,\qquad T_{aa}=\Pi_a,
 \qquad T_{cb}T_{ba}=T_{ca}.}
\tag{10}
$$

**证明。**
全部等式来自 $V_i^*V_i=I_H$。例如

$$
T_{ba}^*T_{ba}=V_aV_b^*V_bV_a^*=\Pi_a,
 \qquad
 T_{cb}T_{ba}=V_cV_b^*V_bV_a^*=V_cV_a^*.
$$

同样计算得到其余结论。对编码态还有
$T_{ba}(V_a\rho V_a^*)T_{ba}^*=V_b\rho V_b^*$。

身份算子是合法支持上的 $\Pi_a$，不是整个 $E_a$ 上的恒等。相应 CP 映射 $X\mapsto T_{ba}XT_{ba}^*$ 在支持于 $\Pi_a$ 的输入上保迹，在任意更大输入域上则一般只有不增迹性质。域与支持必须随比较接口一起保存。

对于纯复位表示 $V_a\psi=a\otimes W_a\psi$，比较具体为

$$
T_{ba}=\lvert b\rangle\langle a\rvert\otimes W_bW_a^*.
$$

若记录取最小维数，$W_a$ 满射到其记录空间；否则仍须保留其像投影，不能把未使用的记录方向也算成合法输入。

### 命题 6.3（没有记录时，完整比较无法从可见原子恢复）

<a id="prop-c117-forgotten-record"></a>

当 $\dim H>1$ 时，恒定替换通道没有恢复全部原输入的左逆。两个可见原子及其替换通道，也不唯一确定 $T_{ba}$。

**证明。**
两个不同密度矩阵经替换后相同，任何左逆作用于这个同一输出都不可能分别恢复二者。再取
$V_a\psi=a\otimes\psi$、$V_b\psi=b\otimes U\psi$，其中 $U$ 为任意酉矩阵。它们的局部替换通道都与 $U$ 无关，但完整比较是
$\lvert b\rangle\langle a\rvert\otimes U$，因此可见数据不能决定这个比较。

这不禁止在两个一维可见射线之间写出 $\lvert b\rangle\langle a\rvert$；它说明该一维映射没有保留原输入的完整内容，不能代替上面的忠实运输。若内容与地址要在项目中一并保留，地址必须包含这些来源与记录接口，而非只等于当前可见的 $a$。

### 例 6.4（未补全的选择性分支破坏接续恒等式）

<a id="ex-c117-partial-cocycle"></a>

若仅保留成功算子 $V_b$，有 $V_b^*V_b=F_b\ne I$，同一形式的比较给

$$
T_{cb}T_{ba}=V_cF_bV_a^*,
 \qquad
 T_{cb}T_{ba}-T_{ca}=V_c(F_b-I)V_a^*.
$$

这一般不为零，也不保证 $T_{ba}$ 为部分等距。把全部正交结果和失败记录补回后，完整嵌入重新满足 $V_b^*V_b=I$，才恢复定理的充分条件。

式 [(10)](#eq-c117-cocycle) 是共同表示之间的坐标相容，不是宣称任意实际物理门闭环都无几何相位。若路径或内部记录改变，完整起点标签也随之改变；同一个表面读口并不自动识别两条历史。

### 6.1 合法起点不自动具有遍历供给

若允许菜单只有 $\{\operatorname{id},\mathcal R_a\}$，每个输入都能回到 $a$，但从 $a$ 无法到达另一条纯射线。这个反例说明“共同复位终点”与“全局生成起点”是不同要求；在全供给模型中，状态可达性需要使用那个额外的供给条款证明。

同样，共同原点不能单独保证两条观察历史共尾。即使当前量子态相同，保留的来源记录也可能不同。下一节将对共同细化、实际可实现接续与共尾条件作独立处理；本节的局部等距比较没有替这些全局量词作出保证。

**白话。**不同观察者可以选择不同原子作为当前起点。只要它们各自保留完整来路，就能把一方的表示忠实换成另一方的表示，连续换几次也不会产生记账矛盾。若只剩原子的表面状态，原来的内容便无法由这个表面重新确定。给定明确的内部码表和解释器，一族程序确实能运行后输出自己的码，并把输入留在记录中；从这个起点走遍整体，还需要真正的接续与覆盖条件。

<a id="section-7"></a>

## 7. 保留来源的共同细化：从有限窗口构造同一整体态

<a id="sec-c117-common-refinement"></a>

本节讨论累计可读接口，不把它等同于当前显示态或某个成功分支的条件后态。关键问题是：两份有限读出能否进入同一个更大的合法窗口，并在其中保留原来的问题、词积与概率？先定义这种关系，再构造全局 $\omega$，而不把待求的 $\omega$ 预先放入假设。

### 7.1 观察窗口、二元比较与一致限制

### 定义 7.1（有向有限观察图）

<a id="def-c117-diagram"></a>

设 $(I,\leq)$ 为非空有向偏序集，即任意 $i,j$ 都有共同上界。每个 $i$ 对应有限维复 $C^*$ 代数 $\mathcal A_i$；当 $i\leq j$ 时，给定保单位、单射的 $*$-同态

$$
\iota_{ji}:\mathcal A_i\longrightarrow\mathcal A_j,
 \qquad
 \iota_{ii}=\operatorname{id},\qquad
 \iota_{ki}=\iota_{kj}\iota_{ji}.
$$

每个窗口还给定正归一化线性泛函 $\omega_i$，即

$$
\omega_i(1)=1,\qquad \omega_i(a^*a)\geq0.
$$

它们构成一致有限态族，是指

<a id="eq-c117-state-consistency"></a>

$$
\omega_j\circ\iota_{ji}=\omega_i
 \qquad(i\leq j).
\tag{11}
$$

在完整矩阵窗口中，$\omega_i(a)=\operatorname{Tr}(\rho_i a)$，其中 $\rho_i\geq0$、$\operatorname{Tr}\rho_i=1$；有限直和窗口采用对应的分块密度矩阵。

这里的嵌入保留加法、乘法、伴随与单位，因此保留已经指定的算符关系。共同细化还须尊重原有系统标签和独立性约定，不能为了凑出一个共同模型而把两个独立系统改认成同一个系统。有向性及一致性是候选的明确条件；存在共同语法起点，并不自动保证它们。

### 命题 7.2（核一致等价于态一致）

<a id="prop-c117-kernel-consistency"></a>

在窗口 $i$ 中定义历史比较核

$$
K_i(h,k)=\omega_i(h^*k),\qquad h,k\in\mathcal A_i.
$$

则式 [(11)](#eq-c117-state-consistency) 等价于

<a id="eq-c117-kernel-consistency"></a>

$$
K_j(\iota_{ji}h,\iota_{ji}k)=K_i(h,k)
 \qquad\text{对所有 }h,k\in\mathcal A_i.
\tag{12}
$$

每个 $K_i$ 都是正核。

**证明。**
保乘法、伴随性给出
$\iota(h)^*\iota(k)=\iota(h^*k)$，故态一致推出核一致。反向取 $h=1,k=a$，并使用 $\iota(1)=1$。任取有限组 $h_\alpha,z_\alpha$，

$$
\sum_{\alpha,\beta}\overline{z_\alpha}z_\beta
 K_i(h_\alpha,h_\beta)
 =
 \omega_i\!\left[
 \left(\sum_\alpha z_\alpha h_\alpha\right)^*
 \left(\sum_\beta z_\beta h_\beta\right)
 \right]\geq0.
$$

### 说明 7.3（概率规律不是单次样本）

<a id="rem-c117-law-sample"></a>

$\omega_i$ 是精确的统计评价，不是一回实验所得的一个结果，也不是没有误差的有限样本频率。实际数据通常只能限定一个允许态集合；完整统计评价需要重复制备、已校准的统计信息或其他明确供给。对同一个未知系统顺序测量，不能仅由一次历史得到全部不相容问题的精确概率。此外，条件化后的 $\omega_h$ 一般不满足旧窗口的式 [(11)](#eq-c117-state-consistency)；本节的一致限制针对保留完整记录的未条件化描述。

**白话。**新窗口要能重新问旧问题，得到原来的概率，并保留旧问题之间怎样相乘、怎样比较。单次看到一个结果，还不是知道了这个概率规律；选中一个分支后的画面，也不能直接冒充保留全部来源的累计窗口。

### 7.2 不预设全局态的唯一重构

### 定理 7.4（一致有限态族的全局重构）

<a id="thm-c117-global"></a>

对定义 [7.1](#def-c117-diagram) 的观察图和一致有限态族，存在由各窗口生成的 $C^*$ 归纳极限

$$
\mathcal A=\varinjlim_{i\in I}\mathcal A_i
$$

及唯一状态 $\omega:\mathcal A\to\mathbb C$，使

$$
\omega\circ\iota_i=\omega_i.
$$

若 $I$ 有可数共尾族，则 $\mathcal A$ 是可分的 AF 代数，即递增有限维 $C^*$ 代数之并的范数闭包。

**证明。**
先把两个局部元素认作同一元素，当且仅当它们在某个共同上界中的像相等。嵌入的相容性使此关系具有传递性。有向性让任意有限个元素落在同一个窗口，因此可在那里定义和、积与伴随，得到代数归纳极限 $\mathcal A_{\rm loc}$。

单射 $C^*$ 同态等距，故元素在任一代表窗口中的范数相同。以此范数完成 $\mathcal A_{\rm loc}$，得到 $\mathcal A$；各窗口经 $\iota_i$ 等距嵌入其中。以下把窗口与其像识别。

对 $a\in\mathcal A_i$ 定义 $\omega(a)=\omega_i(a)$。若有不同代表，取共同上界并用式 [(11)](#eq-c117-state-consistency)，可知赋值相同。在线性组合所属的共同窗口中计算，得到线性、$\omega(1)=1$ 及 $\omega(a^*a)\geq0$。局部状态的正性给出

$$
|\omega(a)|^2\leq\omega(a^*a)\leq\|a\|^2,
$$

所以 $\omega$ 唯一连续延拓至 $\mathcal A$。对任意 $x\geq0$，用局部元素 $b_n$ 在范数下逼近 $x^{1/2}$，则
$b_n^*b_n\to x$，从而 $\omega(x)\geq0$。单位值仍为 $1$。

另一个有相同有限限制的状态在稠密子代数 $\mathcal A_{\rm loc}$ 上与 $\omega$ 相同，由连续性便处处相同。最后，若有可数共尾族，可递归取共同上界把它改成递增共尾链；这条链的代数并仍稠密，于是得到所述 AF 表示。

### 说明 7.5（唯一性的精确范围）

<a id="rem-c117-global-scope"></a>

唯一性只针对这些窗口生成的 $\mathcal A$。若把它记为 $\mathcal A_\Omega$，便是在声明本候选的观察范围；“已经覆盖整体的全部可读关系”仍需覆盖条件，不能由记号推出。定理也不声称 $\omega$ 必为纯态。下一章中的循环向量表示不会把这一一般状态自动变成代数上的纯态。若所有窗口均为完整矩阵代数，所得是 AF 代数的特殊类；一般有限维窗口可以是矩阵代数的有限直和。

**白话。**先给每一扇有限窗口中的合法概率，再要求窗口扩大时旧答案不变，就能把这些答案接成唯一的整体评价。这里的“唯一”是所有已声明问题的唯一答案关系；没有读到的自由度，不能靠一句“整体唯一”自动消失。

### 7.3 任意有限起点、共尾路径与逐问题收敛

### 定义 7.6（共尾观察）

<a id="def-c117-cofinal"></a>

集合 $\{c_n:n\geq1\}\subset I$ 共尾，是指每个 $i\in I$ 都满足 $i\leq c_n$ 对某个 $n$ 成立。递增观察链 $(i_n)$ 共尾，是指每个有限窗口最终都包含在链上的某个窗口中。

### 定理 7.7（从任意合法有限起点延伸到共尾链）

<a id="thm-c117-cofinal"></a>

若 $I$ 有向且有可数共尾族，则任取 $i_0\in I$，存在从 $i_0$ 出发的递增共尾链。任意有限组起点也可先进入共同窗口，再沿一条共尾链细化。

**证明。**
枚举共尾族为 $c_1,c_2,\ldots$。递归利用有向性选

$$
i_{n+1}\geq i_n,c_{n+1}.
$$

任取 $i\in I$，存在 $N$ 使 $i\leq c_N$；于是 $n\geq N$ 时均有 $i\leq i_n$。有限组起点通过反复取二元共同上界得到一个共同起点，再作相同构造。

这里“合法起点”指同一个观察图中的有限对象，不指任意互相矛盾的概率赋值都能同时实现。若偏序只表示抽象嵌入，要把定理变成可执行门序列，还须供给：所选每个有限细化都有有限合法实现，并有它需要的内部记录空间。即便这些实现逐项存在，定理也不给统一的时间、内存或成本上界，更不承诺有限资源足以执行无限路径。

定理证明的是*存在*共尾路径，不是每一条实际门序列都共尾。永远重复同一窗口就可能遗漏其他问题。共同根也不够：二叉树的 $000\cdots$ 与 $111\cdots$ 共享空前缀，却在前缀序中没有后续共同上界。

### 命题 7.8（共尾观察的唯一性与弱$^*$收敛）

<a id="prop-c117-weak-convergence"></a>

两条共尾观察链若取自同一个一致观察图，它们重构的状态均为定理 [7.4](#thm-c117-global) 中的 $\omega$。进一步，若 $\sigma_n$ 是 $\mathcal A$ 上任意状态，且

$$
\sigma_n|_{\mathcal A_{i_n}}=\omega_{i_n},
$$

则 $\sigma_n(a)\to\omega(a)$ 对每个固定 $a\in\mathcal A$ 成立，即 $\sigma_n\to\omega$ 弱$^*$收敛。

**证明。**
共尾链生成相同稠密局部代数，故第一项由唯一性成立。给定 $a$ 和 $\varepsilon>0$，在某个有限窗口选 $b$ 使 $\|a-b\|<\varepsilon$。充分大的 $n$ 包含这个窗口，故 $\sigma_n(b)=\omega(b)$。状态的范数为 $1$，所以

$$
|\sigma_n(a)-\omega(a)|
 \leq|\sigma_n(a-b)|+|\omega(a-b)|
 <2\varepsilon.
$$

### 例 7.9（所有固定窗口都正确，整体范数距离仍为 $2$）

<a id="ex-c117-no-norm-convergence"></a>

取无限 qubit 链，局部代数为前 $n$ 位的 $M_2(\mathbb C)^{\otimes n}$，嵌入为添加单位。令 $\omega_0$ 是全零乘积态；令 $\sigma_n$ 仅把第 $n+1$ 位改成 $\lvert 1\rangle$，其余为 $\lvert 0\rangle$。两者在前 $n$ 位完全相同，故 $\sigma_n\to\omega_0$ 弱$^*$。然而第 $n+1$ 位的 Pauli $Z$ 算符范数为 $1$，两态对它的期望相差 $2$，所以

$$
\|\sigma_n-\omega_0\|_{\mathcal A^*}=2
 \qquad\text{对所有 }n.
$$

以上收敛针对逐个固定问题上的兼容估计，不是物理条件后态随门序列收敛。完全复位能让显示一步到达固定态，却不保证保留来源；反过来，累计记录可以越来越完整，而被观察系统仍在振荡。若整个代数本来有限维，递增子代数链的严格维数增长也只能发生有限次，不能把无限门数本身解释为无限信息增长。

**白话。**从任何合法的有限入口，都可以规划一条逐项补齐所有问题的路；但不是随便走都能走全。两条走全且相容的路会锁定同一套答案。这意味着每一个固定问题最终都能对齐，不意味着对一个无限整体的所有问题同时给出统一误差界。

### 7.4 共同交叠为什么还不够

### 例 7.10（两个 qubit 读口的正性冲突）

<a id="ex-c117-overlap"></a>

在同一个 qubit 上取
$\mathcal B_Z=\operatorname{span}_\mathbb C\{I,Z\}$、
$\mathcal B_X=\operatorname{span}_\mathbb C\{I,X\}$。
分别赋予 $\omega_Z(Z)=1$、$\omega_X(X)=1$，两者在交集 $\mathbb C I$ 上一致。但 $X+Z$ 的最大特征值是 $\sqrt2$，故

$$
\sqrt2 I-X-Z\geq0,
 \qquad
 \omega(\sqrt2 I-X-Z)=\sqrt2-2<0
$$

将违反共同态的正性。因此不存在共同 qubit 态。

### 命题 7.11（Bell 边缘的树形反例）

<a id="prop-c117-bell-tree"></a>

固定三个独立 qubit 因子 $A,B,C$，联合代数为
$M_2(\mathbb C)\otimes M_2(\mathbb C)\otimes M_2(\mathbb C)$。要求

$$
\rho_{AB}=\lvert \Phi^+\rangle\langle \Phi^+\rvert,
 \qquad
 \rho_{BC}=\lvert \Phi^+\rangle\langle \Phi^+\rvert,
 \qquad
 \lvert \Phi^+\rangle=\frac{\lvert 00\rangle+\lvert 11\rangle}{\sqrt2}.
$$

它们在共同因子 $B$ 上均给出 $I_B/2$，但不存在共同 $\rho_{ABC}$。

**证明。**
记 $P_{AB}=\lvert \Phi^+\rangle\langle \Phi^+\rvert$、$Q_{AB}=I-P_{AB}$。若联合态存在，则

$$
\operatorname{Tr}[(Q_{AB}\otimes I_C)\rho_{ABC}]=0.
$$

对正矩阵 $\rho$ 和投影 $Q$，$\operatorname{Tr}(Q\rho)=0$ 意味着
$Q\rho^{1/2}=0$，从而 $\rho$ 的支撑包含在 $\ker Q$。因此本例中
$\operatorname{supp}\rho_{ABC}\subseteq\operatorname{Ran} P_{AB}\otimes H_C$。
$P_{AB}$ 秩为一，所以必有

$$
\rho_{ABC}=P_{AB}\otimes\sigma_C,
 \qquad
 \rho_{BC}=\frac{I_B}{2}\otimes\sigma_C.
$$

后者秩至少为二，不可能等于 Bell 纯态。

两个窗口的交叠图在这里已经是一棵树。项目的经典树上记录扩张具有自己的记录及交叠条件 [3](#ref-repo-tree)；不能只凭“树”和“共同边缘相同”把结论移植到量子边缘。量子边缘相容性本身是需要检验的约束 [15](#ref-marginal)。本例固定了三个独立因子；若偷偷把 $A$ 与 $C$ 合并成同一因子，就已改变原问题。

即使存在共同态，也未必唯一。Bell 态与
$\frac12(\lvert 00\rangle\langle 00\rvert+\lvert 11\rangle\langle 11\rvert)$
都有相同单体边缘 $I/2$，但其 $X\otimes X$ 期望分别为 $1$ 和 $0$，对应项目的局部边缘盲区 [4](#ref-repo-marginal)。共同窗口须容许相关读出，不能只有各方单体答案。

同时，本节的共同对象是非交换代数上的正泛函，不是给所有不相容测量预先填写一个经典联合结果表。上下文性的经典全局截面障碍与此处量子态的存在不是同一个命题 [14](#ref-contextuality)。

**白话。**两份记录在接缝处说同一句话，仍可能在合起来之后互相冲突。甚至接缝没有绕圈，量子边缘也可能拼不上。真正的共同细化要检验合并后的正性和既有算符关系，同时保留两边的关联问题；它并不要求所有不相容测量都有一个同时确定的经典答案。

### 7.5 有限共同态的正性判据

### 定理 7.12（算符系统上的有限延拓判据）

<a id="thm-c117-positive-extension"></a>

设 $\mathcal B_1,\mathcal B_2$ 是指定的 $M_D(\mathbb C)$ 保单位子代数，状态 $f_1,f_2$ 在交集上一致。它们在算符系统
$S=\mathcal B_1+\mathcal B_2$ 上定义

$$
f(a+b)=f_1(a)+f_2(b).
$$

存在共同密度矩阵 $\rho\geq0$、$\operatorname{Tr}\rho=1$，使
$f_k(a)=\operatorname{Tr}(\rho a)$，当且仅当

<a id="eq-c117-system-positivity"></a>

$$
f(H)\geq0\qquad
 \text{对所有 }H\in S\cap M_D(\mathbb C)^+.
\tag{13}
$$

**证明。**
交集一致使 $f$ 与分解方式无关，并给出 $f(1)=1$。共同态存在显然推出式 [(13)](#eq-c117-system-positivity)。

反向，在 $S$ 的自伴实子空间取基 $I,F_1,\ldots,F_m$。所有密度矩阵的期望向量构成紧凸集

$$
C=\{(\operatorname{Tr}\rho F_1,\ldots,\operatorname{Tr}\rho F_m):
       \rho\geq0,\ \operatorname{Tr}\rho=1\}\subset\mathbb R^m.
$$

若 $p=(f(F_1),\ldots,f(F_m))\notin C$，有限维严格凸分离给出实数 $t_k$，使得对于 $H=\sum_k t_kF_k$，

$$
f(H)<\min_{\rho\geq0,\ \operatorname{Tr}\rho=1}\operatorname{Tr}(\rho H)
       =\lambda_{\min}(H).
$$

但 $H-\lambda_{\min}(H)I$ 属于 $S$ 且为正，其 $f$ 值为负，矛盾。故 $p\in C$，相应密度矩阵在整个 $S$ 上实现 $f$。

这个判据把共同细化变成有限半正定可行性问题，而不只是交集上的等式检查。若有三个以上窗口，甚至还须先确认赋值尊重它们之间的全部线性关系；两两交集一致不必自动定义其线性和上的泛函。

### 说明 7.13（尚未选出完整一致态族时）

<a id="rem-c117-finite-feasibility"></a>

也可从有限可行性开始：要求每一有限组窗口及其给定约束，均在某个共同上界中有同时满足约束的状态。取各有限窗口状态空间的紧乘积，把限制一致与闭的已知数据约束视为闭条件。任意有限组条件涉及有限多个窗口，可由所假设的共同上界状态及其限制满足，故具有有限交性质。紧致性于是给出完整一致态族，再用定理 [7.4](#thm-c117-global) 重构 $\omega$。这一前提要求每个有限问题共同可行，不能缩减成每一对交叠相同。有限样本所给的闭误差区间也可作为这里的约束，但不自动保证解存在或唯一。

**白话。**先把双方声称知道的答案放在一起，再检查：有没有一个本应非负的问题，被这些答案算成了负数？没有这种冲突，有限矩阵窗口里就确实存在共同态。实际样本只能给误差范围时，就检查这些范围是否容许共同态，不能把估计值直接宣布为唯一的整体。

### 7.6 自由正核的全部拼接，以及它的适用边界

先暂时只考虑一组已标定向量的 Gram 数据，不附加算符词积约束。共同地址的块记为 $C$，两方私有地址分别有块 $A,B$。令

$$
G_1=\begin{pmatrix}C&X\\X^*&A\end{pmatrix}\geq0,
 \qquad
 G_2=\begin{pmatrix}C&Y\\Y^*&B\end{pmatrix}\geq0.
$$

这里 $C^+$ 是 Moore–Penrose 逆，记

$$
R_1=A-X^*C^+X,\qquad R_2=B-Y^*C^+Y.
$$

### 定理 7.14（两份自由 Gram 数据的全部正完成）

<a id="thm-c117-gram-gluing"></a>

有 $R_1,R_2\geq0$，且
$\operatorname{Ran} X,\operatorname{Ran} Y\subseteq\operatorname{Ran} C$。矩阵

$$
G=\begin{pmatrix}
 C&X&Y\\X^*&A&Z\\Y^*&Z^*&B
 \end{pmatrix}
$$

半正定，当且仅当存在从第二私有坐标空间到第一私有坐标空间的收缩 $T$，使

<a id="eq-c117-gram-gluing"></a>

$$
Z=X^*C^+Y+R_1^{1/2}TR_2^{1/2},
 \qquad \|T\|\leq1.
\tag{14}
$$

奇异或零残差均包括在此公式中。

**证明。**
若 $u\in\ker C$，局部二次型在向量 $(tu,v)$ 上对所有复数 $t$ 非负，便迫使 $u^*Xv=0$；同理 $u^*Yv=0$。这给出两个值域条件。利用它们作可逆三角合同消元，得到

$$
G\geq0
 \ \Longleftrightarrow\
 C\geq0,\qquad
 \begin{pmatrix}R_1&D\\D^*&R_2\end{pmatrix}\geq0,
 \qquad D=Z-X^*C^+Y.
$$

同一消元作用于 $G_1,G_2$，给出 $R_1,R_2\geq0$。

残差块若为正，用相同零空间检验得到
$\operatorname{Ran} D\subseteq\operatorname{Ran} R_1$、
$\operatorname{Ran} D^*\subseteq\operatorname{Ran} R_2$。在两支撑子空间上令
$T=R_1^{+1/2}DR_2^{+1/2}$，其中 $R^{+1/2}:=(R^+)^{1/2}$；归一化合同把正性化为

$$
\begin{pmatrix}I&T\\T^*&I\end{pmatrix}\geq0.
$$

其二次型为
$\|x+Ty\|^2+\langle y,(I-T^*T)y\rangle$，
故等价于 $\|T\|\leq1$。把 $T$ 在支撑的正交补上补零，便得
$D=R_1^{1/2}TR_2^{1/2}$。反向，任意收缩给出上述正块，再乘以残差平方根作合同，即得所需完成。

取 $T=0$ 总给出一种完成：共同部分之外、尚未解释的两组残差互相正交。它是一项选择，不是交叠一致所强迫的结论。多份已指定的交叉块还可能构成循环冲突：三个对角值为 $1$、两两内积均为 $-1$ 的 $2\times2$ 块分别为正，但完整 $3\times3$ 矩阵有特征值 $-1$，因此不能共同实现。这与项目的局部规律循环拼接障碍相呼应 [2](#ref-repo-gluing)。

定理 [7.14](#thm-c117-gram-gluing) 不推翻 Bell 树反例。实际算符历史还须满足
$K(h,k)=\omega(h^*k)$、单位关系及全部已指定词积；独立系统还带有固定的张量与交换关系。一个自由 Gram 完成可能违反这些关系。只有同时遵守它们的完成，才是合法量子共同窗口。

**白话。**共同历史先确定两份记录中已经对齐的部分；剩下的部分可以怎样相互倾斜，由一个收缩参数描述。仅看向量比较时总能选一种接法，但若这些向量还代表有乘法、有独立性约定的操作，就必须继续检查这些约定，不能把随便接上的正矩阵当成物理共同态。

### 7.7 从保来源等距过程到保单位窗口

全过程等距与本节的保单位嵌入之间还有一个不能省略的类型差别。设
$V:H_{\rm in}\to H_{\rm out}\otimes H_R$ 满足 $V^*V=I$。则

$$
a\longmapsto VaV^*
$$

是到角代数的单射 $*$-同态，但单位映为 $VV^*$，一般不是整个输出空间的单位；反向压缩 $b\mapsto V^*bV$ 一般不保乘法。因此不能把任意等距压缩直接当作定义 [7.1](#def-c117-diagram) 的保单位细化。

### 命题 7.15（带内部空白记录的保单位实现）

<a id="prop-c117-unital-bridge"></a>

在允许的更大内部窗口中补足有限维数，使输出空间 $\mathcal H'$ 的维数为 $\dim H_{\rm in}$ 的整数倍，并把 $V$ 视为到 $\mathcal H'$ 的等距映射。存在有限维记录空间 $H_B$、固定单位向量 $\lvert 0\rangle_B$ 和酉映射

$$
U:H_{\rm in}\otimes H_B\longrightarrow\mathcal H',
 \qquad
 U(\psi\otimes\lvert 0\rangle_B)=V\psi.
$$

由此得到保单位嵌入

<a id="eq-c117-unital-bridge"></a>

$$
\iota(a)=U(a\otimes I_B)U^*.
\tag{15}
$$

对联合态 $\rho'=U(\rho\otimes\lvert 0\rangle\langle 0\rvert_B)U^*$，有
$\operatorname{Tr}[\rho'\iota(a)]=\operatorname{Tr}(\rho a)$。

**证明。**
选输入正交基。$\psi\mapsto V\psi$ 把子空间
$H_{\rm in}\otimes\lvert 0\rangle_B$ 的正交基映成输出中的正交组。两端维数相等，在各自正交补上补齐正交基即可得到 $U$。式 [(15)](#eq-c117-unital-bridge) 显然保乘法、伴随和单位；迹等式由酉不变性及 $\operatorname{Tr}\lvert 0\rangle\langle 0\rvert_B=1$ 得到。

空白记录和扩大窗口均须在 $\Omega$ 的合法操作供给内，不能隐去这项资源条件，也不声称有限整体能无穷提供新记录。固定初始化同样重要：若输入与将被忽略的记录任意预相关，仅凭输入边缘态一般不能定义一个输入无关的固定约化通道。沿酉实现保留完整记录，则旧读口通过式 [(15)](#eq-c117-unital-bridge) 搬到新窗口，旧概率按式 [(11)](#eq-c117-state-consistency) 保持；忽略或选择记录后得到的局部操作属于另一种映射类型。

**白话。**完整过程可以把来源搬进内部记录，让显示重新开始；扩大观察窗口时，就沿着这个完整搬运把旧问题一起带过去。只看显示或丢掉记录，是另一个操作。把这两层分清，才能同时说明为什么局部会复位、为什么来源没有消失，以及两位观察者后来怎样重新对齐。

<a id="section-8"></a>

## 8. 共同来源的比较空间与二元关系球

<a id="sec-c117-comparison"></a>

本节沿用 C116 给出的复系统类型。物理振幅空间用于表示制备、门和全记录等距；
本节构造的 GNS 空间则用于比较同一来源下的历史。两者有联系，却不能不经说明就认作同一操作空间。
正核的 Hilbert 实现属于已有的核理论与 GNS 路线 [12](#ref-aronszajn)；
以下将所需结论按本稿的历史记号直接证明。

### 定义 8.1（共同来源与历史核）

$\Omega$ 保留原始历史、协议和记录；$\mathcal A$ 是其选定接口的含幺复 $C^*$-代数，
$\omega$ 是该接口上的正归一泛函。有限层次可直接取矩阵代数；
若使用无限层次，本节明确使用相应的范数及 Hilbert 完备化。
历史的算子表示记为 $h\in\mathcal A$，未来门 $a$ 接在左侧成为 $ah$。
定义

$$
K(h,k)=\omega(h^*k),\qquad
 \|h\|_\omega^2=\omega(h^*h),\qquad
 N_\omega=\{h:\|h\|_\omega=0\}.
$$

历史标签本身仍留在 $\Omega$ 中；不同标签可以具有相同算子表示。

### 命题 8.2（共同核的 Hilbert 实现及接续方向）

<a id="prop-c117-gns"></a>

$K$ 的每个有限 Gram 表半正定。
商空间 $\mathcal A/N_\omega$ 具有内积
$\langle [h],[k]\rangle=\omega(h^*k)$，其完备化记为 $\mathcal H_\omega$。
令 $\xi=[1]$，则

$$
\pi(a)[h]=[ah],\qquad
 \|\pi(a)\|\le\|a\|,\qquad
 \omega(a)=\langle \xi,\pi(a)\xi\rangle.
$$

零空间等价允许共同的未来左接续，一般不允许任意右接续。

**证明。**
对任意有限系数 $z_i$，

$$
\sum_{i,j}\bar z_i z_jK(h_i,h_j)
 =\omega\!\left[
 \left(\sum_i z_ih_i\right)^*
 \left(\sum_j z_jh_j\right)\right]\ge0.
$$

二阶正性给出
$|K(h,k)|^2\le K(h,h)K(k,k)$。
因此零范数对象与所有对象正交，零空间为线性子空间，
上述商内积良定义且正定。
由 $a^*a\le\|a\|^2I$，

$$
\|ah\|_\omega^2
 =\omega(h^*a^*ah)\le\|a\|^2\omega(h^*h).
$$

所以 $N_\omega$ 是左理想，左乘在商上良定义且有界，
从而延伸到完备化。乘法及伴随关系直接由内积验证，
而 $\|\xi\|^2=\omega(I)=1$，得到最后的读出式。

右接续的反例可在 $M_2(\mathbb C)$ 中取
$\omega(a)=\langle 0\rvert a\lvert 0\rangle$、$h=P_1=\lvert 1\rangle\langle 1\rvert$、
$X=\lvert 0\rangle\langle 1\rvert+\lvert 1\rangle\langle 0\rvert$。
此时 $[h]=0$，但 $hX\lvert 0\rangle=\lvert 1\rangle$，故 $[hX]\ne0$。

因此，零空间商只是当前接口的比较压缩，不删除来源记录，
也不允许把当前不可区分的历史任意重新接线。

### 8.1 两条历史的三维关系坐标

写 $v_h=\pi(h)\xi$、$v_k=\pi(k)\xi$，并令

$$
p=\|v_h\|^2,\quad q=\|v_k\|^2,\quad c=\langle v_h,v_k\rangle,\qquad
 G=\begin{pmatrix}p&c\\\bar c&q\end{pmatrix}.
$$

正性给出 $p,q\ge0$、$|c|^2\le pq$。
当 $t=p+q>0$，有

<a id="eq-c117-pair-ball"></a>

$$
\frac Gt=\frac12(I+r\cdot\sigma),\qquad
 r=\frac{(2\operatorname{Re} c,-2\operatorname{Im} c,p-q)}t,\qquad
 |r|^2=1-\frac{4(pq-|c|^2)}{t^2}.
\tag{16}
$$

这是将矩阵四个实分量除以迹后的直接恒等式。
$G$ 秩一当且仅当两个比较向量线性相关；其归一化点在球面上。
两向量独立时，点在球内。若 $p=0$，正性迫使 $c=0$，
但不能为历史 $h$ 定义条件归一态。
若 $p=q=0$，整块为零，连归一化关系球也未定义。

当 $p,q>0$，两个 GNS 射线之间的距离为

$$
d_{\mathrm{FS}}([v_h],[v_k])
 =\arccos\frac{|c|}{\sqrt{pq}}.
$$

它是比较空间的射影距离。
把 $|c|^2/(pq)$ 解释成可实现的秩一转移概率，
还需相应投影属于允许的物理读口；
一般的 $\pi_\omega(\mathcal A)$ 未必包含
$\mathcal H_\omega$ 上的全部秩一投影。

### 例 8.3（关系表的纯度不等于条件物理纯度）

取 $\omega(a)=\operatorname{Tr}(a)/2$。有限 GNS 表示可写成
$v_h=h/\sqrt2$，内积为 Hilbert–Schmidt 内积。
若 $h=k=I$，则 $G/t$ 秩一，但两条历史的条件物理态都是混态 $I/2$。
若 $h=I,k=\sigma_z$，则 $p=q=1,c=0$，
两个比较向量正交，条件物理态却仍同为 $I/2$。
因此条件态相同也不等于比较射线相同。

记录还涉及一个必须固定的转置约定。
在矩阵接口 $\omega(a)=\operatorname{Tr}(\rho a)$ 中，相干控制两条历史，
并保留路径记录，得到的未归一记录块为

$$
\frac12
 \begin{pmatrix}
  \operatorname{Tr}(h\rho h^*)&\operatorname{Tr}(h\rho k^*)\\
  \operatorname{Tr}(k\rho h^*)&\operatorname{Tr}(k\rho k^*)
 \end{pmatrix}
 =\frac12\begin{pmatrix}p&\bar c\\c&q\end{pmatrix}.
$$

这里可先共同缩放 $h,k$，使控制操作成为合法分支；
共同尺度不改变下述归一化。
成功后记录态是 $G^{\mathsf T}/t$，其第二个 Bloch 坐标为
$+2\operatorname{Im} c/t$，而 [(16)](#eq-c117-pair-ball) 的 Gram 表取负号。
两者的谱、秩和纯度相同，不能因此忽略相位符号。
直接比较相干历史还可验证

$$
\|v_h+e^{i\phi}v_k\|^2
 =p+q+2\operatorname{Re}(e^{i\phi}c).
$$

**白话。**同一个来源下，两条历史各有多少权重、彼此怎样相合，可以组成一张三维关系球。这张球描述的是两条历史的比较，不自动等于某个观察者的物理状态。概率为零的分支不能再归一化；已经记下的历史也不会因为当前读口看不出差别就被删掉。

<a id="section-9"></a>

## 9. 两个移动窗口怎样趋于同一套关系

<a id="sec-c117-windows"></a>

令观察者 $o$ 的读口代数递增：

$$
\mathcal A_{o,0}\subseteq\mathcal A_{o,1}\subseteq\cdots
 \subseteq\mathcal A,\qquad I\in\mathcal A_{o,n}.
$$

它们读取同一 $\omega$ 的限制，而非每步另选一个条件后态。
在共同比较空间内定义

$$
H_{o,n}
 =\overline{\operatorname{span}\{\pi(a)\xi:a\in\mathcal A_{o,n}\}},
 \qquad P_{o,n}:\mathcal H_\omega\to H_{o,n}.
$$

这里 $P_{o,n}$ 是正交比较投影。
因为单位元已在每个读口中，

<a id="eq-c117-unit-already-present"></a>

$$
\boxed{P_{o,n}\xi=\xi\quad\text{对每个 }n.}
\tag{17}
$$

所以不能把 $P_{o,n}\xi$ 描述成逐步逼近整体态的向量。
真正需要逼近的是固定历史或问题的向量 $v_h=\pi(h)\xi$。

### 定理 9.1（窗口残余与共同关系极限）

<a id="thm-c117-window"></a>

省略观察者下标，设 $H_n$ 递增，$P_n$ 为其正交投影，并令

$$
H_\infty=\overline{\bigcup_nH_n},\qquad
 E_n(v)=\|(I-P_n)v\|^2.
$$

则 $P_n$ 强收敛到 $P_\infty$，并且

$$
E_n(v)\downarrow\|(I-P_\infty)v\|^2.
$$

令 $\Delta_n=P_{n+1}-P_n$，则 $\Delta_n$ 为两两正交的投影，
且

<a id="eq-c117-residual-budget"></a>

$$
E_n(v)-E_{n+1}(v)=\|\Delta_nv\|^2,\qquad
 E_0(v)=\|(I-P_\infty)v\|^2+
             \sum_{n\ge0}\|\Delta_nv\|^2.
\tag{18}
$$

若 $H_\infty=\mathcal H_\omega$，每个固定问题的残余趋于零。

**证明。**
嵌套性给 $P_nP_m=P_mP_n=P_{\min(n,m)}$。
由此直接相乘可知 $\Delta_n^2=\Delta_n=\Delta_n^*$，
不同增量乘积为零。正交分解

$$
(I-P_n)v=\Delta_nv+(I-P_{n+1})v
$$

给出第一项残余恒等式。
若 $v\in H_\infty$，对任意 $\epsilon>0$，
可取 $u\in H_N$ 使 $\|v-u\|<\epsilon$。
当 $n\ge N$，最佳近似性给
$\|(I-P_n)v\|\le\|v-u\|<\epsilon$。
若 $v\perp H_\infty$，则所有 $P_nv=0$。
把一般 $v$ 分解到这两个正交部分，得到强收敛。
将残余差从 $0$ 到 $N-1$ 求和，再令 $N\to\infty$，
得到 [(18)](#eq-c117-residual-budget)。

对历史写 $E_n(h)=E_n(v_h)$，定义可读关系核

$$
K_n(h,k)=\langle P_nv_h,P_nv_k\rangle.
$$

正交分解给出

<a id="eq-c117-residual-kernel"></a>

$$
K(h,k)=K_n(h,k)+
 \langle (I-P_n)v_h,(I-P_n)v_k\rangle.
\tag{19}
$$

所以 $K_n$ 与残余核 $K-K_n$ 都半正定；
相邻增量也是 Gram 核

$$
K_{n+1}(h,k)-K_n(h,k)
 =\langle \Delta_nv_h,\Delta_nv_k\rangle.
$$

特别有可核算的误差界

<a id="eq-c117-kernel-error"></a>

$$
|K(h,k)-K_n(h,k)|
 \le\sqrt{E_n(h)E_n(k)}.
\tag{20}
$$

两个观察者的窗口投影 $P_n,Q_m$ 满足

$$
\|P_nv-Q_mv\|
 \le\sqrt{E_n(v)}+\sqrt{F_m(v)}.
$$

若两窗口并集都稠密于共同比较空间，右侧在 $n,m$ 独立增长时趋于零；
由 [(20)](#eq-c117-kernel-error)，固定历史对的核读数也趋于相同。
若两读口链互相共尾，即每一方的任一阶段都包含于另一方的某个后续阶段，
则它们具有同一可达闭包。但共尾本身不保证这个闭包就是全部
$\mathcal H_\omega$：若覆盖不足，极限应为共同的 $P_\infty$，而不是 $I$。

### 9.1 残余是精确定义，不是自动可计算的完成度

在 $v\ne0$ 时，可定义相对残余 $E_n(v)/\|v\|^2$；
零向量没有这项归一比值。残余是最佳近似误差，
并不保证观察者已经握有计算它所需的数据。
若有限窗口有已知正交基 $w_1,\ldots,w_r$，则

$$
E_n(h)=K(h,h)-\sum_{\ell=1}^r|\langle w_\ell,v_h\rangle|^2.
$$

只有所需范数和交叉数据都可得时，这才成为实际计算式。
例如窗口仅为 $\mathbb C e_0$，尚未读取目标的交叉关系；
即使知道 $\|v_h\|=1$，现有窗口内数据仍可兼容
$v_h=e_0$ 或 $v_h=e_1$，残余分别为 $0$ 或 $1$。
数学上存在一个真实残余，不等于有限读口已能认证它的值。

强收敛也不意味着对所有问题一致收敛。
在 $\ell^2$ 中取 $H_n=\operatorname{span}\{e_0,\ldots,e_n\}$、$\xi=e_0$。
每个固定向量都被逐步逼近，但

$$
\|I-P_n\|=1,\qquad E_n(e_{n+1})=1
$$

始终成立。不断改变目标，可以一直追着尚未读到的方向走。

### 例 9.2（比较投影不是自动的物理条件期望）

取 $\mathcal A=M_2(\mathbb C)$、
$\rho=(I+r\sigma_x)/2$、$0<r<1$，
并令读口为对角代数 $\mathcal D=\operatorname{span}\{P_0,P_1\}$。
这是忠实状态。GNS 投影到 $\mathcal D\xi$ 的算子代表
$\mathsf E_\omega(a)=b_0P_0+b_1P_1$ 满足正交条件

$$
b_i=\frac{\omega(P_ia)}{\omega(P_i)}.
$$

代入 $a=\sigma_y$，有
$\omega(P_0\sigma_y)=-ir/2$、
$\omega(P_1\sigma_y)=ir/2$，故

$$
\mathsf E_\omega(\sigma_y)=-ir\sigma_z.
$$

它连自伴性都不保持，因而不是物理 CP 条件期望。
窗口投影定理仍然成立，因为它说的是比较空间的最佳近似。
若需要物理条件期望，必须另加相应的存在及兼容条件。

**白话。**整体态的代表向量已经在每个含单位的窗口里；增长的不是这个向量，而是观察者能分解哪些问题。对一个固定问题，未解决部分与每次新读出的部分正交，平方权重可以逐次记账。两个充分覆盖的观察者最终会对这个固定问题一致，但这既不提供统一速度，也不保证他们已经能从有限记录算出剩余多少。

<a id="section-10"></a>

## 10. 共尾读口不等于条件态轨迹收敛

<a id="sec-c117-two-limits"></a>

读口扩张和结果条件化有不同的数学对象。
若 $\bigcup_n\mathcal A_n$ 在 $\mathcal A$ 中范数稠密，
且 $\widetilde\omega_n$ 是整个 $\mathcal A$ 上的状态，
其限制与 $\omega$ 在 $\mathcal A_n$ 上一致，
则对每个固定 $a\in\mathcal A$，有 $\widetilde\omega_n(a)\to\omega(a)$。
证明是：取某个 $b\in\mathcal A_N$ 逼近 $a$，
对 $n\ge N$，

$$
|\widetilde\omega_n(a)-\omega(a)|\le2\|a-b\|.
$$

这里比较的是同一来源的兼容读数。

一条成功历史 $h$ 的条件态则是

$$
\omega_h(a)=
 \frac{\omega(h^*ah)}{\omega(h^*h)}
 \qquad\bigl(\omega(h^*h)>0\bigr).
$$

分母为零时不定义条件态。
即使读口已经完整，条件态也可以不收敛：
取 $\mathcal A_n=\mathcal B_n=M_2(\mathbb C)$、
$\omega(a)=\langle 0\rvert a\lvert 0\rangle$，并取历史

$$
h_n=\sigma_x^n,\qquad k_n=I.
$$

两方都已访问完整代数，所有历史成功概率也都是一；
第一方的条件态却在 $\lvert 0\rangle,\lvert 1\rangle$ 之间交替，第二方保持 $\lvert 0\rangle$。
再取 $h_n=(-1)^nI$，所有条件态与射线都相同，
归一化比较向量仍不收敛。

共尾链应共享单位，并使用未经重新条件化的状态限制。
角代数 $p\mathcal Ap$ 的单位是 $p$；
若 $\omega(p)<1$，再除以 $\omega(p)$ 已经改变归一接口，
不能把它悄然混进同一限制链。

**白话。**两个观察者逐渐拥有同一套读口，说明他们对固定问题的比较会一致；这不表示他们选中的结果分支必须走向同一个状态。读口增长、条件态演化以及向量代表的相位变化，是三件分别需要检验的事。

<a id="section-11"></a>

## 11. 三类运输与三角相位

<a id="sec-c117-transport"></a>

前章的全记录支持群胚已经证明：
同一来源的等距编码 $\iota_a,\iota_b$ 之间，
$T_{ba}=\iota_b\iota_a^*$ 是可达支持之间的部分等距，
并满足严格接续关系。这里不重复该定理。
它不同于同一 $\mathcal H_\omega$ 内两个可读窗口的重叠。

取正交标架 $V_a:\mathbb C^r\to H_a\subseteq\mathcal H_\omega$、
$V_b:\mathbb C^s\to H_b\subseteq\mathcal H_\omega$。
矩阵 $V_b^*V_a$ 的范数不超过一，但一般不是部分等距：
两条夹角为 $\theta$ 的射线已经给出标量 $\cos\theta$，
在 $0<\theta<\pi/2$ 时既非零也非单位模。
其极分解才给出部分等距因子，并伴随不能丢掉的正衰减因子。

若两标架表示同一个窗口，则 $U_{ba}=V_b^*V_a$ 为酉矩阵。
对同窗第三标架，

$$
U_{cb}U_{ba}=V_c^*P_{H_a}V_a=V_c^*V_a=U_{ca}.
$$

因此纯换坐标的闭环为恒等。
非零相位来自移动射线或窗口上的指定运输，而非这条坐标恒等式失效。
把几何相位表述为线丛运输属于已有的 holonomy 观点 [13](#ref-simon)；
以下只需秩一矩阵相乘即可验证。

### 定理 11.1（三条移动射线的相位与成功权重）

<a id="thm-c117-triangle-phase"></a>

令 $\psi_1,\psi_2,\psi_3$ 为单位比较向量，

$$
c_{ij}=\langle \psi_i,\psi_j\rangle,\qquad
 P_i=\lvert \psi_i\rangle\langle \psi_i\rvert,\qquad
 B=c_{12}c_{23}c_{31}.
$$

若三个相邻重叠都非零，定义极运输

$$
U_{ji}=\frac{P_jP_i}{|c_{ij}|}.
$$

它是从第 $i$ 条射线到第 $j$ 条射线的部分等距，且

<a id="eq-c117-triangle-holonomy"></a>

$$
U_{13}U_{32}U_{21}
 =\frac{\bar B}{|B|}P_1.
\tag{21}
$$

实际投影环 $P_2,P_3,P_1$ 对初态 $\psi_1$ 的成功概率为 $|B|^2$。

**证明。**
有

$$
P_jP_i=\bar c_{ij}\lvert \psi_j\rangle\langle \psi_i\rvert,
$$

故 $U_{ji}^*U_{ji}=P_i$、$U_{ji}U_{ji}^*=P_j$。
三个归一因子相乘后，分子为

$$
P_1P_3P_2P_1=\bar B P_1,
$$

立即得到 [(21)](#eq-c117-triangle-holonomy)。
不除以归一因子时，成功振幅为 $\bar B\psi_1$，
其平方范数就是 $|B|^2$。
在 $\psi_i\mapsto e^{i\chi_i}\psi_i$ 下，
各重叠取得相邻相位差，乘积 $B$ 不变。

若任一相邻重叠为零，投影环成功概率为零，
相应极运输及 $\arg B$ 未定义，不能补成零相位。
上式作为 GNS 几何总是成立；
要实现这些投影，仍需相应物理读口可用。
闭环后的密度状态看不见整体相位，
保留可相干比较的参考分支后，才可把该相位读成干涉差异。

例如在物理二元纯态空间中取

$$
\psi_1=(1,0)^{\mathsf T},\quad
 \psi_2=(1,1)^{\mathsf T}/\sqrt2,\quad
 \psi_3=(1,i)^{\mathsf T}/\sqrt2.
$$

此时 $B=(1+i)/4$，运输相位为 $e^{-i\pi/4}$，
投影环成功概率为 $1/8$。
三对距离还受到整体正性的约束：
归一化三阶 Gram 表的行列式为

<a id="eq-c117-triple-gram"></a>

$$
1-|c_{12}|^2-|c_{23}|^2-|c_{31}|^2
 +2\operatorname{Re}(c_{12}c_{23}c_{31})\ge0.
\tag{22}
$$

该式由行列式直接展开，在零重叠时仍成立。
因此三对距离与三点相位不能任意独立指定；
这正是一项可检验的“关系的关系”。

### 11.1 共同比较空间不保证共同经典结果表

两个窗口总能放入共同闭线性张成空间，
但任意两个量子测量未必具有同时保留两边结果的经典细化。
例如，假设 $\sigma_z,\sigma_x$ 的锐测量有共同效果
$G_{ij}\ge0$，其边缘分别为 $P_i^z,P_j^x$。
于是

$$
G_{ij}\le P_i^z,\qquad G_{ij}\le P_j^x.
$$

若 $0\le G\le P$，对 $v\in\ker P$ 有
$\langle v,Gv\rangle=0$，正性遂迫使 $Gv=0$，
故 $\operatorname{Ran} G\subseteq\operatorname{Ran} P$。
这里两条不同秩一射线的交集为零，所以所有 $G_{ij}=0$，
与 $\sum_{ij}G_{ij}=I$ 矛盾。
记录保真必须针对同一已执行流程的细化，
或包括协议选择记录的共同表示；
它不能为不相容上下文同时预赋结果。

**白话。**同一份完整记录换一种编码，可以无损对照；两个观察者只拿出各自窗口时，对照一般会损失一部分内容。窗口沿不同路径移动，还可以留下三角相位，这不是坐标记号自相矛盾。共同来源让这些关系能放在一起比较，却不强迫所有不相容读口同时拥有一张经典结果表。复数与物理操作类型仍承接 C116，本节新增的是共同来源中的记录保真、窗口增长和残余控制。

<a id="section-12"></a>

## 12. 一个几何总图：来源、记录与可读窗口

```latex
\begin{tikzpicture}[>=Latex,font=\small]
\node[draw,rounded corners,fill=teal!6,minimum width=2.5cm,minimum height=1.25cm,align=center] (src) at (0,0) {共同来源\\$\psi\in H$};
\node[draw,rounded corners,fill=teal!6,minimum width=5.5cm,minimum height=1.25cm,align=center] (a) at (7.1,1.5) {原子 $a$ 的完整表示\\$a\otimes W_a\psi$};
\node[draw,rounded corners,fill=blue!5,minimum width=5.5cm,minimum height=1.25cm,align=center] (b) at (7.1,-1.5) {原子 $b$ 的完整表示\\$b\otimes W_b\psi$};
\draw[->,thick,teal!70!black] (src.north east) -- node[above,sloped] {$V_a$ 保二元比较} (a.west);
\draw[->,thick,blue!70!black] (src.south east) -- node[below,sloped] {$V_b$ 保二元比较} (b.west);
\draw[<->,thick] (a.south) -- node[right,align=left] {$T_{ba}=V_bV_a^*$\\仅在合法支持上互逆} (b.north);
\node[align=center,text width=12.8cm] at (4,-3.25) {显示端可各自固定；来源的全部比较保存在 $W_a\psi,W_b\psi$ 中。\\抹去记录后，两个显示状态不再决定这个运输。};
\end{tikzpicture}
```

**图 1。**完整记录的几何：两个入口是同一来源的两种等距编码。图中箭头不是“整个 $\Omega$ 复位为一个原子”。

```latex
\begin{tikzpicture}[>=Latex,font=\small]
\begin{scope}[shift={(-3.3,0)}]
\draw[fill=teal!4,draw=teal!70!black] (0,0) circle (1.65);
\draw[teal!50!black] (-1.65,0) arc[start angle=180,end angle=360,x radius=1.65,y radius=.45];
\draw[dashed,teal!50!black] (1.65,0) arc[start angle=0,end angle=180,x radius=1.65,y radius=.45];
\draw[->] (-2,0)--(2,0) node[right] {$r_x$};
\draw[->] (0,-1.9)--(0,2.05) node[above] {$r_z$};
\draw[->] (-.8,-.8)--(.95,.95) node[right] {$r_y$};
\draw[->,very thick,teal!80!black] (0,0)--(.75,.65);
\fill[teal!80!black] (.75,.65) circle (.045);
\node[align=center,text width=5.9cm] at (0,-2.7) {两条历史的 Gram 球\\$r=(2\Re c,-2\Im c,p-q)/(p+q)$\\球面：两比较向量线性相关};
\end{scope}
\begin{scope}[shift={(3.7,0)}]
\coordinate (v1) at (-1.35,-.8);
\coordinate (v2) at (1.3,-.7);
\coordinate (v3) at (0,1.45);
\draw[->,thick,teal!70!black] (v1)--node[below] {$c_{12}$}(v2);
\draw[->,thick,teal!70!black] (v2)--node[right] {$c_{23}$}(v3);
\draw[->,thick,teal!70!black] (v3)--node[left] {$c_{31}$}(v1);
\foreach \v/\lab in {v1/1,v2/2,v3/3}{\fill (\v) circle (.05);}
\node[below left] at (v1) {$[\psi_1]$};
\node[below right] at (v2) {$[\psi_2]$};
\node[above] at (v3) {$[\psi_3]$};
\node[align=center,text width=5.9cm] at (0,-2.7) {三条射线的关系环：$B=c_{12}c_{23}c_{31}$\\运输相位 $\bar B/|B|$，成功率 $|B|^2$\\距离与相位共同受 Gram 正性约束};
\end{scope}
\end{tikzpicture}
```

**图 2。**二元比较提升成三维球，三条比较再形成有相位的环。右图表示关联次序，不表示射影空间中的欧氏三角距离；零重叠时该运输不定义。

整体比较空间 $\mathcal H_\omega$ 通常远大于一个三维球；三维球属于一个二元关系块。观察者的几何对象是递增窗口 $H_{o,n}$。共同单位向量 $\xi$ 从一开始就在每个窗口里，逐步减少的是固定问题向量的残余 $\|(I-P_{o,n})v_h\|^2$。因此图中的三维结构、全记录等距和窗口正交投影各有自己的类型，不能互相代换。

<a id="section-13"></a>

## 13. 从这份候选恢复通常的量子公理

<a id="sec-c117-full-theory"></a>

共同细化负责说明多个观察者怎样属于同一个统计整体。它不能替代局部量子结构、效果概率及复合规则。本节将仍然需要的接口逐项写出，并补足有限维的状态、测量、复合和运动理论。所有后果只在明确生成的系统类内成立。

### 13.1 效果的二元拆并推出 Born 规则

### 定义 13.1（一致的效果概率）

在 $M_d(\mathbb C)$ 中，效果为 $0\le E\le I$。状态最初是函数 $w:[0,I]\to[0,1]$，对同一效果跨测量分解使用同一数值，并满足

$$
w(I)=1,\qquad w(E+F)=w(E)+w(F)
 \quad(E,F\ge0,\ E+F\le I).
$$

全部合法有限测量为 $\sum_kE_k=I$ 的分解。模型采用全部满足此条件的评价，而非先指定一组密度矩阵。

这个二元合并包含三结果上下文 $\{E,F,I-E-F\}$，不只是要求每个二结果实验分别归一化。它是广义效果版 Gleason 路线的有限维输入 [9](#ref-busch)。

### 定理 13.2（密度矩阵与平方律）

<a id="thm-c117-born"></a>

上述评价恰为

$$
\boxed{w(E)=\operatorname{Tr}(\rho E),\qquad \rho\ge0,\quad\operatorname{Tr}\rho=1.}
$$

状态集合的极点恰为秩一投影，纯态对纯锐效果的概率为 $|\langle \phi,\psi\rangle|^2$。

**证明。**
可加性给 $w(0)=0$ 及单调性；将 $E$ 均分为 $n$ 份得到有理数齐次性，再用上下有理数夹逼得到 $w(tE)=tw(E)$，$0\le t\le1$，不必另加连续性。

对任意正矩阵 $A$，取 $u\ge\|A\|$、$u>0$，定义 $W(A)=u\,w(A/u)$。齐次性说明此值不依赖 $u$；选共同上界可证 $W(A+B)=W(A)+W(B)$。对自伴元 $X=A-B$ 定义 $L(X)=W(A)-W(B)$：若 $A-B=C-D$，则 $A+D=C+B$，加性保证定义良好。因此 $L$ 是正实线性泛函，且 $L(I)=1$。

自伴矩阵上的非退化配对 $\operatorname{Tr}(XY)$ 给唯一自伴 $\rho$，使 $L(X)=\operatorname{Tr}(\rho X)$。对所有秩一效果的非负评价给 $\rho\ge0$，归一化给 $\operatorname{Tr}\rho=1$。反向显然。

秩至少二的密度矩阵可在两个正特征值上作相反微扰，故不极端。若秩一 $P_\psi=t\rho_1+(1-t)\rho_2$，正性使两项都支持于 $\mathbb C\psi$，归一化迫使两者均等于 $P_\psi$。最后 $\operatorname{Tr}(P_\psi P_\phi)=|\langle \phi,\psi\rangle|^2$。

若删去拆并条件，二阶效果 $E=\alpha I+b\cdot\sigma$ 上的
$\widetilde w(E)=\alpha+4b_z^3$ 仍给 $[0,1]$ 内的概率并满足互补归一化；但 $\widetilde w(P_z)=1$，而 $2\widetilde w(P_z/2)=5/8$。因此 Born 规则没有从“存在观察者”或“能复位”中自动出来。

自伴可观测量 $A=\sum_j a_jP_j$ 的锐测量由这些谱投影给出，期望为 $\operatorname{Tr}(\rho A)$。一般效果分解给 POVM。随机制备混合对应密度矩阵凸组合，且相同密度重心恰好对全部效果不可区分。

**白话。**把同一个结果拆成两格，再把两格合起来，概率不能变。这个二元记账要求一旦用于全部效果，就迫使概率线性。前面构造的复振幅表示随后把线性评价写成迹；对两个纯方向，它恰好成为内积的模平方。

### 13.2 独立系统必须对齐同一个内部复中心

### 定义 13.3（有限复合闭包）

联合表示是非零含幺实结合 $*$-代数。局部矩阵代数以保单位单射 $*$-同态嵌入，像两两交换，共享同一个内部中心 $J$，并生成联合代数。还允许任意非零投影支持上的角代数作为受限系统。模型供应这些系统的全部状态和效果。

### 定理 13.4（复张量积与任意有限维系统）

<a id="thm-c117-tensor"></a>

两个满足上述条件的矩阵系统的联合代数恰为 $M_d(\mathbb C)\otimes_\mathbb C M_m(\mathbb C)\cong M_{dm}(\mathbb C)$。从二元原子及非零角代数生成全部 $M_d(\mathbb C)$。

**证明。**
共享 $J$ 使乘法映射 $a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 对复标量平衡，交换性使它为 $*$-同态，生成性使它满射。源矩阵代数为单代数：任意非零理想可经左右乘矩阵单位取得所有矩阵单位。因此保单位同态的核只能为零，映射同构。

$N$ 个二元原子给 $M_{2^N}(\mathbb C)$。对任意 $d\le2^N$，取秩 $d$ 的投影 $p$，其角代数 $pM_{2^N}(\mathbb C)p$ 同构于 $M_d(\mathbb C)$，单位是 $p$。这种系统闭包不等于观察者窗口间的保单位嵌入；后者必须另行使用共同的窗口单位。

中心对齐确有内容。若只作实张量积，

$$
M_2(\mathbb C)\otimes_\mathbb R M_2(\mathbb C)\cong M_4(\mathbb C)\oplus M_4(\mathbb C),
$$

显式映射为 $a\otimes b\mapsto(a\otimes_\mathbb C b,a\otimes_\mathbb C\bar b)$。令 $Z=-J_AJ_B$，其像是 $(I,-I)$；$(I\pm Z)/2$ 分开两个扇区，维数相等证明映射同构。要求 $J_A=J_B$ 正好选择 $Z=1$ 的扇区。两个扇区的归一化迹在所有局部自伴乘积上相同，却在 $Z$ 上分别给 $1,-1$，所以局部量子球本身并不排除额外整体扇区。

联合态的局部状态唯一由 $\operatorname{Tr}_B\rho_{AB}$ 表示，因为

$$
\operatorname{Tr}[\rho_{AB}(E\otimes I)]=\operatorname{Tr}[(\operatorname{Tr}_B\rho_{AB})E]
$$

对全部效果成立。Bell 向量 $(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$ 是非乘积纯态，两边约化态均为 $I/2$，故给出纠缠。保留全部结果时，局部保迹通道不改变另一侧边缘：代入 $\sum_jK_j^*K_j=I$ 计算即可；选择某个结果后的条件边缘可以改变，但其选择记录不能被省略。

### 13.3 从完整序列到一般仪器

第 [3.3](#thm-c117-record) 定理已经由完整比较守恒推出 Kraus 形式及任意内部参考下的正性。若连续完整步骤为 $V_1,\ldots,V_n$，每一步在此前记录上作用为恒等，则

$$
V_{1:n}=(V_n\otimes I_{R_{<n}})\cdots(V_2\otimes I_{R_1})V_1
$$

仍满足 $V_{1:n}^*V_{1:n}=I$。逐个展开记录，序列分支的 Kraus 算子是按执行顺序的乘积；完整分支总和保持概率。对任意同类型历史 $h,k$，还有

<a id="eq-c117-history-conserve"></a>

$$
\boxed{\omega(h^*k)=\sum_j\omega(h^*K_j^*K_jk).}
\tag{23}
$$

所以守恒的是整个二元关系，不仅是 $h=k$ 时的单个成功权重。

两个观察者的完整序列若都是同一源空间上的等距编码，就可把 $V_a,V_b$ 换成 $V_{a,1:n},V_{b,1:m}$，直接使用定理 [6.2](#thm-c117-origin-transport)。若比较的只是尚未覆盖全部来源的窗口，应使用第 [9](#sec-c117-windows) 节的窗口收缩，而不能误用可逆坐标运输。

### 13.4 理想测后态需要一个明确的选择定义

同一效果 $E$ 允许 $\sqrt E\rho\sqrt E$，也允许 $U\sqrt E\rho\sqrt E U^*$；概率相同，后态可不同。定义有限纯态组 $P_s$、正权重 $w_s$ 满足

$$
\sum_sw_sP_s\otimes P_s=\frac{I+F}{d(d+1)},\qquad\sum_sw_s=1,
$$

其中 $F$ 交换两因子。对固定输入输出系统和效果 $E$，把最大化

$$
R(T)=\sum_sw_s\operatorname{Tr}[P_sT(P_s)],\qquad
 T(X)=\sum_aK_aXK_a^*,\quad\sum_aK_a^*K_a=E
$$

的分支定义为理想实现。

所需有限比较组确实存在：标准基总权重取 $1/(d+1)$，全部向量 $(z_1,\ldots,z_d)/\sqrt d$、$z_i\in\{1,i,-1,-i\}$ 总权重取 $d/(d+1)$，各组内均匀。记 $D_0=\sum_i\lvert ii\rangle\langle ii\rvert$，两组二阶矩分别为 $D_0/d$ 与 $(I+F-D_0)/d^2$，所列权重恰好消掉 $D_0$。

### 定理 13.5（平方根及 Lüders 更新）

<a id="thm-c117-luders"></a>

理想实现唯一为 $T_E(X)=\sqrt E X\sqrt E$，最大值为

$$
\frac{\operatorname{Tr} E+(\operatorname{Tr}\sqrt E)^2}{d(d+1)}.
$$

对投影 $P$，正成功概率下的条件态为 $P\rho P/\operatorname{Tr}(\rho P)$。

**证明。**
二阶矩给 $R(T)=[\operatorname{Tr} E+\sum_a|\operatorname{Tr} K_a|^2]/[d(d+1)]$。令 $L=\sqrt E$，在其正支持的特征基上写 $L\lvert i\rangle=\lambda_i\lvert i\rangle$，$\lambda_i>0$。所有 $K_a$ 在 $\ker E$ 上为零，可写为 $K_a=A_aL$、$\sum_aA_a^*A_a=P_{\operatorname{Ran} E}$。向量 $v_i=(\langle i\rvert A_a\lvert i\rangle)_a$ 满足 $\|v_i\|\le1$，故

$$
\sum_a|\operatorname{Tr} K_a|^2
 =\left\|\sum_i\lambda_iv_i\right\|^2
 \le\left(\sum_i\lambda_i\right)^2.
$$

$K=L$ 达到此界。等号迫使所有 $v_i$ 为同一个单位向量 $(c_a)_a$，且每个 $A_a\lvert i\rangle=c_a\lvert i\rangle$，从而 $K_a=c_aL$、$\sum_a|c_a|^2=1$，给同一个映射 $X\mapsto LXL$。$E=0$ 时所有 Kraus 算子均为零，结论仍成立。

**白话。**一个结果亮起来时，内部可能还多转了一圈。概率只说明它亮起的份量，不能把这一圈排除。用一组有限而均衡的纯方向比较，在固定成功效果下保留最多原方向，才唯一选出平方根更新。这是理想实现的定义条件，不能装进概率公式后再称其已经被概率推出。

### 13.5 双向完整运动与连续时间

### 定理 13.6（酉运动及 Hamiltonian 形式）

<a id="thm-c117-dynamics"></a>

在同一个 $M_d(\mathbb C)$ 上，一个确定过程及其逆都具有完整记录实现，当且仅当它为酉共轭 $\Phi(X)=UXU^*$。若这些确定过程另组成连续单参数群 $\Phi_{t+s}=\Phi_t\Phi_s$，则存在自伴 $H$，使

$$
\Phi_t(X)=e^{-itH/\hbar}Xe^{itH/\hbar},\quad
 \dot\rho=-\frac{i}{\hbar}[H,\rho].
$$

相容的纯态代表满足 $i\hbar\dot\psi=H\psi$。

**证明。**
设过程与逆的 Kraus 算子分别为 $K_a,L_j$。恒等通道的 Choi 矩阵秩一，故其每个 Kraus 向量共线，亦即 $L_jK_a=c_{ja}I$。至少一个 $c_{j_0a_0}\ne0$，所以同维方阵 $L_{j_0},K_{a_0}$ 可逆；固定 $j_0$ 后，全部 $K_a$ 互相成比例，合成单 Kraus $A$。保迹给 $A^*A=I$，同维使 $A$ 酉。逆向直接成立。

有限维连续单参数线性群可在单位附近取矩阵对数，再由群律延伸为 $\Phi_t=e^{t\mathcal L}$。每个 $\Phi_t$ 保乘法及伴随，求导使 $\mathcal L$ 为 $*$-导子。用矩阵单位，取 $A=\sum_i\mathcal L(E_{i1})E_{1i}$，对 $E_{kl}E_{i1}=\delta_{li}E_{k1}$ 求导并求和，得到 $\mathcal L(E_{kl})=AE_{kl}-E_{kl}A$。伴随相容迫使 $A+A^*$ 为实标量矩阵；去掉一半该标量得到反自伴 $A_0$。令 $H=i\hbar A_0$ 即得公式。

这里的 $\hbar>0$ 是时间与生成元的单位换算；证明不决定其经验数值或具体 $H$。连续时间也不由一条离散观察序列自动生成。即使物理序列存在，能否高效实现某次细化仍是资源问题。

### 13.6 量子理论的可核后果

对自伴 $A,B$，在正状态给出的内积中取 $A-\omega(A)I$、$B-\omega(B)I$，Cauchy–Schwarz 直接给

$$
\operatorname{Var}_\omega(A)\operatorname{Var}_\omega(B)
 \ge\left|\omega\bigl[(A-\omega(A)I)(B-\omega(B)I)\bigr]\right|^2
 \ge\frac14|\omega([A,B])|^2.
$$

若两边的自伴二值算子满足 $A_i^2=B_j^2=I$，CHSH 算子

$$
S=A_0\otimes(B_0+B_1)+A_1\otimes(B_0-B_1)
$$

有 $S^2=4I-[A_0,A_1]\otimes[B_0,B_1]$，故 $\|S\|\le2\sqrt2$。取 Bell 态、$A_0=Z,A_1=X$、$B_{0,1}=(Z\pm X)/\sqrt2$ 达到此界。它们是已构造代数与正性的推论，不是另外塞入的公理。

有限构造至此覆盖 Hilbert 空间、密度态、Born 概率、POVM、量子仪器、复张量积、纠缠、酉运动和指定理想准则下的 Lüders 更新。无限观察窗口的归纳极限已经由共同细化章节给出；它允许无限系统的状态泛函，但没有自动提供所有无限维量子场论所需的局部结构或未界算符动力学。

<a id="section-14"></a>

## 14. 本轮唯一完整候选 C117

<a id="sec-c117-candidate"></a>

### 定义 14.1（C117：保留二元比较的共同细化）

模型中的内容、门、记录、参考与读口均属于 $\Omega$。核心要求是：*改变完整表示或扩大累计接口时，保留任意两份既有内容的完整比较及其合法接续；未读差异进入内部记录；同源的有限接口能够在保持这些关系的更大接口中共同细化。*

以下六项给这个要求的类型、供给与概率含义，合起来是一份完整候选，而非六个备选理论。

1. **Q1.** **局部二元类。** 原始读口满足定义域饱和及纤维内输出一致。非平凡原子具有第 [2](#sec-c117-local) 节的实 Lorentz 锥、欧氏比较、规范滤片和标签线性有向生成元；对所有标签及合成标签要求 $D_aa=0$、$D\ne0$、$D_a\in\mathfrak{so}(W)$ 及式 [(1)](#eq-c117-spectator) 的旁观条件。相应完整接续由所构造的结合表示承载。

2. **Q2.** **读出拆并。** 在生成代数的全部效果上，同一效果跨分解同读；合法的二元结果合并满足概率可加，单位效果取值为一。模型取全部这样的评价。

3. **Q3.** **有限整体闭包。** 独立原子进入非零含幺实结合 $*$-代数，嵌入保单位且彼此交换，共享同一个内部 $J$，并生成联合代数。允许非零角代数作为受限系统，也允许有限经典记录直和；所用内部参考和准备支持明确属于供给域。

4. **Q4.** **完整过程保比较。** 完整过程起初仅为物理振幅空间间的函数 $V$，含全部输出记录，满足


   $$
   \langle Vu,Vv\rangle=\langle u,v\rangle\qquad\text{对整个输入空间中的 }u,v.
   $$


   局部操作由选取或忽略正交记录获得，所有失败分支可补回。模型允许全部这类有限接口及其顺序接续；实际装置若只具有限制菜单，不自动拥有全部模型操作。记录必须在 $\Omega$ 内提供，固定空白记录的初始化是资源条件。

5. **Q5.** **观察关系可共同细化。** 同一个一致域的有限累计窗口形成有向保单位 $*$-嵌入图；图保留固定系统标签、乘法与独立性。局部读出满足


   $$
   K_j(\iota_{ji}h,\iota_{ji}k)=K_i(h,k),
    \qquad K_i(h,k)=\omega_i(h^*k).
   $$


   选择有可数共尾族的观察范围，每个被使用的有限细化有合法有限实现。称覆盖这一族的路径为完整观察路径。只要求这种路径从每个有限起点存在，不把所有实际路径都定义成完整。

6. **Q6.** **理想与时间的命名。** 理想效果分支按第 [13.5](#thm-c117-luders) 定理的有限均衡比较最大保留量定义；双向合法的确定过程称为可逆运动。若讨论连续时间动力学，再指定连续单参数群及时间单位，不从离散门序列自动添加这一结构。

两个核心式分别作用于完整物理过程与未条件化累计接口。它们具有同一个意思：*旧的二元关系在完整新表示中仍可被找回。* 但它们不是同一个映射类型：前者推出等距过程，后者要求保乘法的窗口嵌入。式 [(15)](#eq-c117-unital-bridge) 给出在内部准备资源允许时连接两者的构造。

### 定理 14.2（C117 的量子与观察者重构）

<a id="thm-c117-full"></a>

满足 C117 的生成系统具有下列完整表示。

1. 二元原子的实方向为三维，内部复闭包为 $M_2(\mathbb C)$，振幅空间为 $\mathbb C^2$。有限复合与角代数生成任意 $M_d(\mathbb C)$。

2. 状态、效果、概率及复合分别为密度矩阵、正效果、Born 迹规则及复张量积。全部局部过程是量子仪器，完整确定过程为 CPTP 通道，理想分支为平方根或投影 Lüders 更新；连续可逆群具有 Hamiltonian 形式。

3. 每个局部纯复位原子具有 $V_a\psi=a\otimes W_a\psi$ 的完整实现，$W_a$ 等距；有限正交程序码可由内部受控酉解释器实现自描述输出。任意两种同源完整编码通过 $T_{ba}=V_bV_a^*$ 在可达支持上相互转换，且满足严格接续式 [(10)](#eq-c117-cocycle)。

4. 一致有限窗口唯一生成 $\mathcal A$ 上的状态 $\omega$。从任意合法有限起点存在共尾观察路径；任意两条这样的路径对每个固定可读问题重构同一评价。对应 GNS 窗口的残余满足式 [(18)](#eq-c117-residual-budget) 与 [(20)](#eq-c117-kernel-error)。

反过来，通常有限维复量子系统以及它们的一致可数有限窗口族，在明确供应上述内部记录、效果、细化和理想选择后，满足这些条件。

**证明。**
第 1 项由定理 [2.4](#thm-c117-three)、[2.5](#thm-c117-complex) 和 [13.4](#thm-c117-tensor) 得到。第 2 项由效果定理 [13.2](#thm-c117-born)、过程定理 [3.2](#thm-c117-linear)、[3.3](#thm-c117-record)、理想定理 [13.5](#thm-c117-luders) 与动力学定理 [13.6](#thm-c117-dynamics) 得到。第 3 项是定理 [4.2](#thm-c117-reset)、命题 [5.2](#prop-c117-self-code) 与定理 [6.2](#thm-c117-origin-transport)。第 4 项由定理 [7.4](#thm-c117-global)、[7.7](#thm-c117-cofinal) 及 [9.1](#thm-c117-window) 给出；共尾代数并的范数稠密性保证相应循环子空间并稠密。

反向，在标准 qubit 中取球形自伴部、规范正滤片及 $D_ab=\sqrt\kappa\,a\times b$，即满足局部条件。迹评价满足拆并，复张量积满足共享中心；每个有限 Kraus 仪器均由已证明的完整记录构造实现。按声明的供给取一致窗口图，则核保持和共同细化逐条成立。理想最大值及连续群形式已在对应定理中双向验证。

这个结果是条件重构，不是证明全部条件逻辑独立或绝对最少。特别地，Q4 在有限复系统上与线性等距的记录实现等价；它删去了一个单列的线性假设，提供了更直接的二元解释，却没有凭改写取消它的数学内容。Q5 的正性、有向性和覆盖也没有从“内容等于地址”自动推出。

### 14.1 通常量子公理的来源表

| 标准表述 | 本候选中的实际推导及承重条件 |
|---|---|
| 复 Hilbert 空间 | 实二元旁观回路推出三维；三方向乘积给中心 $J^2=-1$；最小左理想给 $\mathbb C^2$，复合与角闭包给 $\mathbb C^d$。 |
| 叠加及过程线性 | 振幅空间来自局部代数表示；完整二元比较守恒用范数恒等式推出 $V(u+v)=Vu+Vv$ 与复齐次性。 |
| 状态与 Born 规则 | 全效果上的跨分解一致和二元可加给正线性泛函；有限矩阵表示将其写成 $\operatorname{Tr}(\rho E)$。 |
| 复合与纠缠 | 共享中心、交换独立嵌入和生成性给复张量积；全部联合正态中包含非乘积纯态。 |
| 一般量子操作 | 在内部正交记录上展开完整等距；忽略或选择记录给全部 Kraus 仪器，任意参考下保正自动成立。 |
| 理想测后态 | 概率不唯一确定后态；有限均衡比较的最大保留准则唯一给 $\sqrt E\rho\sqrt E$，投影时给 Lüders 更新。 |
| 酉运动及 Schrödinger 方程 | 同维确定过程及逆均合法则为酉；另给连续时间群后，导子为自伴生成元的交换子。 |
| 多观察者的共同来源 | 有向保单位细化、一致正评价和覆盖给唯一归纳极限态；共尾使每个固定问题最终得到同一评价。 |

### 14.2 反着推：不遵守时具体失去什么

| 放松的要求 | 已给出的显式后果 |
|---|---|
| 完整复比较只剩模平方 | 反酉共轭也保转移概率，不能由该条件推出复线性。 |
| 纯复位时不保留记录 | 两个正交输入被压成同一射线，完整内积无法保持。 |
| 把整个封闭输入都算进复位量词 | 满射酉不能把全空间送进一个真子空间；必须声明准备支持。 |
| 把单一成功幅度当成万能原子 | $K=\sqrt\eta\lvert a\rangle\langle b\rvert$ 在 $b^\perp$ 上成功率为零。 |
| 抹去失败记录再比较序列 | 中间的 $V_b^*V_b$ 不再为 $I$，两步转换出现 $V_c(V_b^*V_b-I)V_a^*$ 的缺口。 |
| 只比较重叠而不检验共同正性 | $X=1,Z=1$ 的局部评价交集一致，却把 $\sqrt2I-X-Z$ 这个正元赋成负数。 |
| 把经典树拼接当成量子树拼接 | $AB$ 与 $BC$ 都是 Bell 纯边缘，公共 $B$ 相同，却无固定独立 $ABC$ 的联合态。 |
| 只知各方边缘，没有相关窗口 | Bell 态和经典关联态可给同一单体边缘，整体态仍不唯一。 |
| 合法门但没有共尾覆盖 | 永远重复一个门或一个窗口，可一直遗漏固定问题。 |
| 把累计读口等同条件后态 | $X^n\lvert 0\rangle$ 的条件态交替振荡，即便每一步已拥有完整 $M_2$ 读口。 |
| 把最佳比较投影当作物理仪器 | 对角窗口的 GNS 投影可把 $Y$ 送成 $-irZ$，连自伴性都不保。 |
| 把逐问题极限当统一全局误差 | 无限 qubit 中移动的一位翻转给逐问题正确，却始终范数距离 $2$。 |

### 14.3 内生性的精确定义与仍需验证的项目接点

本稿把“公理内生”解释为：所有参量、读口、参考、操作及检验对象都来自同一 $\Omega$，条件只描述它们之间的关系；通过成立或失败的内部比较来决定哪些对象属于这个模型。没有一个站在 $\Omega$ 外面的观察者被用来补足测量或记录。

这不把定义与事实混同。定义可以规定什么叫“保比较的过程”或“完整观察路径”，但仍要证明项目原生门及其语义满足该定义、这样的对象存在、可在所需资源内实现，并覆盖所声明的内容。C117 的开放前端依然是：从项目原生协议中构造球形正锥、有向标签及旁观条件；给原子自指提供明确编码和解释器；把完整记录及保单位细化实现为实际合法接续。只有这些桥梁都通过，才可说本候选已经被项目原生系统实现。

**本轮已完成的理论范围。** 有限复量子系统及仪器的重构；局部自复位的记录分类；全记录观察者转换；可数有限窗口的共同状态构造；固定问题的残余收敛；二元球与三角相位的兼容几何。

**没有被这些定理自动选择的内容。** 一个特定宇宙态是否纯、具体 Hamiltonian、作用常数、粒子种类、物理时空维数，以及实际有限样本或有限资源下的收敛速度。$\mathcal H_\omega$ 上有一个循环向量，不等于 $\omega$ 在其可观测代数上是纯态，更不等于已经构造唯一的物理宇宙波函数。三维二元关系球也不等于现实空间的三维性。

<a id="section-15"></a>

## 15. 一段完整的白话描述

整体里有内容，也有内容怎样接续、从哪里来的记录。观察者可以从任意合法的有限原子入口开始；这个原子每次都可以把自己的显示重新变回自身，但输入没有因此消失，它原有的区别和相干关系必须完整移到整体内部的记录里。于是不同起点可以显示不同的原子、运行不同的门，却仍在保存同一来源的两种表示；带着完整记录，它们之间可以无损对照，连续换几次也不矛盾。随后每开一扇新窗口，都要能找回旧窗口的问题和答案，并保留问题彼此怎样比较、怎样接续。两条路径只要最终都覆盖每一个有限问题，就会对同一套整体关系达成一致；这个整体状态不必先从外面摆进来，它由全部相容的有限关系唯一接成。对每一对历史，把两边的权重和它们的复交叉关系放在一起，会得到一个三维球；第三条历史再加入时，三对关系绕成一个环，距离与相位必须互相容得下。球来自二元回路的相容，概率来自同一结果拆合不变，量子门来自完整比较不丢失，而两个观察者的共同极限来自窗口的相容与覆盖。整个过程中，公理成为内部对象必须共同满足的约束；它们有可见的失败后果，也有清楚的适用范围。

<a id="references"></a>

## 参考文献

<a id="ref-repo"></a>

### [1]

 the-omega-institute. *trureturing*. Public `dev` repository consulted 2026-11-03. [https://github.com/the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing). Latest HEAD SHA and the full AURIC static-fiber volume were not obtained; this manuscript does not claim complete latest-commit coverage.

<a id="ref-repo-gluing"></a>

### [2]

 the-omega-institute. *LocalLawGluingObstruction.lean*. Source inspected 2026-11-03, including `compatible_local_laws_can_lack_global_state`. [Repository source](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction.lean).

<a id="ref-repo-tree"></a>

### [3]

 the-omega-institute. *RunningIntersectionRecords.lean*. Source inspected 2026-11-03, including `extend_record_at_neighbor` and `local_row_extends_raw_join`. The latter asserts extension existence, not unique extension. [Repository source](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.lean).

<a id="ref-repo-marginal"></a>

### [4]

 the-omega-institute. *LocalMarginalCorrelationBlindSpot.lean*. Source inspected 2026-11-03. [Repository source](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.lean). No fresh Lean build was run for these source inspections.

<a id="ref-repo-recovery"></a>

### [5]

 the-omega-institute. *TargetRecoveryCriterion.lean*. [Repository source](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean), consulted 2026-11-03.

<a id="ref-repo-domain"></a>

### [6]

 the-omega-institute. *HiddenArchiveTemporalDomain.lean*. [Repository source](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.lean), consulted 2026-11-03.

<a id="ref-c116"></a>

### [7]

 AURIC C116. *二元回路相容与内部量子几何*. Previously delivered research manuscript, 2026-11-03. Local reconstruction and all required finite quantum-interface proofs are restated in this manuscript. C117 is a continuation number, not a repository release tag.

<a id="ref-alfsen"></a>

### [8]

 E. M. Alfsen and F. W. Shultz. Orientation in operator algebras. *PNAS* 95 (1998), 6596–6601. [https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/).

<a id="ref-busch"></a>

### [9]

 P. Busch. Quantum states and generalized observables: a simple proof of Gleason's theorem. *Physical Review Letters* 91 (2003), 120403. [https://arxiv.org/abs/quant-ph/9909073](https://arxiv.org/abs/quant-ph/9909073).

<a id="ref-nohiding"></a>

### [10]

 S. L. Braunstein and A. K. Pati. Quantum information cannot be completely hidden in correlations: implications for the black-hole information paradox. *Physical Review Letters* 98 (2007), 080502. [https://arxiv.org/abs/gr-qc/0603046](https://arxiv.org/abs/gr-qc/0603046). The pure-output finite-dimensional case is proved directly here.

<a id="ref-programming"></a>

### [11]

 M. A. Nielsen and I. L. Chuang. Programmable quantum gate arrays. *Physical Review Letters* 79 (1997), 321–324. [https://arxiv.org/abs/quant-ph/9703032](https://arxiv.org/abs/quant-ph/9703032). The restriction concerns exact deterministic finite program architectures, not approximate universal circuit computation.

<a id="ref-aronszajn"></a>

### [12]

 N. Aronszajn. Theory of reproducing kernels. *Transactions of the American Mathematical Society* 68 (1950), 337–404. [https://pages.stat.wisc.edu/~wahba/stat860public/pdf2/aronszajn.pdf](https://pages.stat.wisc.edu/~wahba/stat860public/pdf2/aronszajn.pdf). Historical source for positive-kernel Hilbert realizations; the representation used here is proved explicitly.

<a id="ref-simon"></a>

### [13]

 B. Simon. Holonomy, the quantum adiabatic theorem, and Berry's phase. *Physical Review Letters* 51 (1983), 2167–2170. [https://doi.org/10.1103/PhysRevLett.51.2167](https://doi.org/10.1103/PhysRevLett.51.2167). The discrete three-ray formula in this manuscript is proved by matrix multiplication.

<a id="ref-contextuality"></a>

### [14]

 S. Abramsky and A. Brandenburger. The sheaf-theoretic structure of non-locality and contextuality. *New Journal of Physics* 13 (2011), 113036. [https://arxiv.org/abs/1102.0264](https://arxiv.org/abs/1102.0264).

<a id="ref-marginal"></a>

### [15]

 A. Klyachko. Quantum marginal problem and representations of the symmetric group. 2004. [https://arxiv.org/abs/quant-ph/0409113](https://arxiv.org/abs/quant-ph/0409113).
## 16. 受控终端字行到局部 Lorentz 预测锥的桥

### 定义 16.1（同源受控终端域与全部合法未来）

固定唯一来源 $\Omega$ 及其状态 $\omega$。前缀 $a$、后缀 $f$ 均指这个来源内实际允许的有限门词，按先 $a$ 后 $f$ 的调用顺序书写。一般实际域为

$$
\mathcal D=\{(a,f):a\in\mathsf A,\ f\in\mathsf F(a)\},\qquad
p(a;f,w)=\omega[af\text{ 后的完整终端标签为 }w],\quad w\in\Gamma.
\tag{16.1}
$$

$\Gamma$ 是所选窗口的全部终端标签，含失败标签，且在本节有限。语义概率满足

$$
p(a;f,w)\ge0,\qquad \sum_{w\in\Gamma}p(a;f,w)=1.
\tag{16.2}
$$

它不是采样频率或删除失败后的条件概率。对明确事件 $E\subseteq\Gamma$ 才定义 $p(a;f,E)=\sum_{w\in E}p(a;f,w)$ 及 $m=2p-1$；完整标签事件与 bit-read 事件不互换。

以下分类限定在一个**共同续接域**：实际前缀为含空字的串接闭子菜单 $\mathsf L$；$\mathsf F$ 是这个域中每个前缀后全部合法的终端未来，$\epsilon\in\mathsf F$，且 $g f\in\mathsf F$ 对每个 $g\in\mathsf L,f\in\mathsf F$ 成立。因此 $\mathsf L\times\mathsf F\subseteq\mathcal D$，并有同一完整程序的续接恒等式

$$
p(ag;f,w)=p(a;gf,w).
\tag{16.3}
$$

“全部未来”在这个指定域内全称量化，不是选几个方便读数；若不同前缀的合法未来不同，或者新增档案、记录读口，必须重新核对共同域及下述容量，不能沿用旧预测等价。选择局部窗口不宣称已经覆盖整个 $\Omega$。这里的串接合同不添加任意准备、中间测量、外部 ready/reset、独立副本或随机选词。

### 定义 16.2（由行本身构造的实预测容量）

将当前预测行定义为所有合法未来上的函数

$$
x_a(f,w)=p(a;f,w),\qquad
V=\operatorname{span}_{\mathbb R}\{x_a:a\in\mathsf L\}.
\tag{16.4}
$$

相同的 $x_a$ 表示在全部这些未来上不可区分。假设实预测容量恰为 $\dim_{\mathbb R}V=4$。这是一个明确前提，不从标签数、有限域的三维向量空间、现成矩阵维数或三次读数推出。令 $e_{f,w}$ 为坐标评价，则

$$
e_{f,w}(x_a)=p(a;f,w),\qquad
\sum_{w\in\Gamma}e_{f,w}=u,\qquad u(x_a)=1,
\qquad W=\ker u,\quad\dim_{\mathbb R}W=3.
\tag{16.5}
$$

式 (16.2) 保证各 $f$ 定义的是同一个 $u$：在行的任意线性关系中，系数和必为零。所有评价函数分离 $V$；有限维性保证其中有有限个已声明评价张成 $V^*$。状态差张成 $W$，因为 $x_a$ 张成 $V$ 且均在 $u=1$。这些是构造的结果，没有添加不可观测坐标。

式 (16.3) 使 $T_gx_a=x_{ag}$ 良定义并线性：若 $\sum_i t_i x_{a_i}=0$，则对每个 $f,w$，$\sum_i t_i x_{a_i g}(f,w)=\sum_i t_i x_{a_i}(gf,w)=0$。于是

$$
u T_g=u,\qquad T_hT_g=T_{gh},\qquad e_{gf,w}=e_{f,w}T_g.
\tag{16.6}
$$

$T_{gh}$ 的下标仍按调用先后书写。这一证明消费全部未来的线性关系，不能用有限读数上的拟合代替。由 $\epsilon\in\mathsf F$ 及 $g\mathsf F\subseteq\mathsf F$ 可知 $\mathsf L\subseteq\mathsf F$，但不要求反向包含。式 (16.6) 只给出每个固定未来效果在可逆前缀下的轨道 $\{e_{f,w}T_g:g\in\mathsf L\}$；它不保证不同 $f$ 的效果属于同一轨道。一般 $f\in\mathsf F\setminus\mathsf L$ 也未被赋予 $V$ 上的变换 $T_f$。

### 假设 16.3（统计逆、无限不可约作用与兼容正锥）

对每个 $g\in\mathsf L$，另有一个**同一菜单中已经供应的正向有限字** $\bar g\in\mathsf L$，满足

$$
x_{a g\bar g}=x_a=x_{a\bar g g}
\quad\text{对每个 }a\in\mathsf L,
\text{ 即在每个 }f\in\mathsf F,w\in\Gamma\text{ 上相等}.
\tag{16.7}
$$

这只是统计逆条件；字面逆调用不是新原语。由 (16.6)–(16.7)，$T_{\bar g}=T_g^{-1}$，故 $\mathcal G=\{T_g:g\in\mathsf L\}$ 是一个线性群。要求其在 $W$ 上的像无限，并且没有非零真不变实子空间。无限指**不同预测变换的数目**，不是给同一变换添加无限多个词名。不可约性也须相对于全部指定未来的预测商核判断。

称 $K\subset V$ 为兼容正锥，若它是闭凸锥，包含全部 $x_a$，满足 $T_gK\subseteq K$，且每个完整终端效果 $e_{f,w}$ 在 $K$ 上非负。有限和给出的事件效果亦须保留。凸性、闭性和正齐次性是数学有序完成的定义，不表示实际已经供应混合、极限准备或任意正向滤片。

这些假设没有正定不变度量、球面轨道、复标量、Born 概率律或 Hilbert 正锥前提。四维实容量、共同未来域、准确统计逆以及无限不可约预测作用仍是须从原生关系取得的额外内容。

### 定理 16.4（从源相对统计条件导出旋转闭包与 Lorentz 有序几何）

在定义 16.1–16.2 及假设 16.3 下，存在唯一的共同固定中心 $c\in V$、$u(c)=1$，以及 $W$ 上的正定内积 $\langle\ ,\ \rangle$，使

$$
V=\mathbb R c\oplus W,\qquad
T_g(tc+w)=tc+A_gw,\qquad A_g\in O(W).
\tag{16.8}
$$

令 $x_\epsilon=c+v$、$r=\|v\|$。则 $r>0$，并且

$$
SO(W)\subseteq\overline{\{A_g\}}\subseteq O(W),\qquad
\overline{\{x_a:a\in\mathsf L\}}
 =c+\{w:\|w\|=r\}.
\tag{16.9}
$$

这里的球面和稠密性是结论，不是纯态供应前提。特别地，定义同一个数学对象

$$
S_{\min}=\overline{\operatorname{conv}}\{x_a:a\in\mathsf L\},\qquad
C_{\min}=\overline{\operatorname{cone}}\{x_a:a\in\mathsf L\},
\tag{16.10}
$$

其中 $\operatorname{cone}$ 指所有**有限非负线性组合**，而非仅单条射线的并，便有

$$
S_{\min}=\{c+w:\|w\|\le r\},\qquad
C_{\min}=K_r,\qquad
K_R=\{tc+w:t\ge0,\ \|w\|\le Rt\}.
\tag{16.11}
$$

每个兼容正锥恰为某个 $K_R$，其半径的全部约束由命题 16.5 给出。它们均与四维未来 Lorentz 锥有序线性同构，但不因抽象同构而成为固定预测坐标中的同一个锥。

**证明。** 先从统计行取得紧性。取四个评价组成 $V$ 的线性坐标。由 (16.2)，实际行在这些坐标中均有界，故其闭凸包 $S_{\min}$ 紧；它在仿射超平面 $u=1$ 中满维。由统计逆，$T_g$ 将实际行集合双射到自身，因而 $T_gS_{\min}=S_{\min}$。取四个实际行作 $V$ 的基，则每个 $T_g$ 的基像都在同一紧集内，所以所有 $T_g$ 的算符范数统一有界；逆变换也在这个群中，逆范数同样统一有界。若 $T_{g_n}\to T$，由 $\|T_{g_n}z\|\ge M^{-1}\|z\|$ 得 $T$ 仍可逆。因此 $H=\overline{\mathcal G}$ 是 $GL(V)$ 中的紧群，并保持 $S_{\min}$ 和 $u$。本步所选参考范数仅用于有限维有界性，没有预设保持概率的欧氏几何。

用紧群的归一 Haar 测度取

$$
c=\int_H h x_\epsilon\,dh,\qquad
\langle w,z\rangle=\int_H (h w,h z)_0\,dh,
\tag{16.12}
$$

其中 $(\ ,\ )_0$ 是任意参考内积。紧性、可逆性使后一式正定，Haar 不变性使它被 $H$ 保持。前一式在紧凸集 $S_{\min}$ 内，满足 $u(c)=1$ 且被 $H$ 固定，得到 (16.8)。两个共同固定中心的差是 $W$ 中固定向量；不可约性和 $\dim W=3$ 排除非零固定向量，故 $c$ 唯一。$h$ 在 $c$ 和 $W$ 上的作用决定整个 $h$，因此 $H$ 在 $W$ 上的像 $H_W$ 是紧正交群，且仍无限、不可约。

为完整说明三维群步骤，取 $H_W^+=H_W\cap SO(W)$。它指数至多二，所以无限。无限紧群中有不同于恒等而趋于恒等的序列：取聚点附近两个不同元素之商即可。写这个序列为绕单位轴 $n_j$、角度 $0<\theta_j\to0$ 的旋转，取子列 $n_j\to n$。对任意实角 $\theta$，选整数 $k_j$ 使 $k_j\theta_j\to\theta$，便有 $R_{n_j}(\theta_j)^{k_j}\to R_n(\theta)$。闭性保证绕 $n$ 的整圆旋转均在 $H_W^+$ 中。

若所有 $h\in H_W$ 保持直线 $\mathbb R n$，就违反不可约性。故存在 $h$ 使 $n'=hn$ 不平行于 $n$，共轭给绕 $n'$ 的整圆旋转。再取 $n''=R_n(\pi/2)n'$；三轴线性独立，绕 $n''$ 的整圆也由共轭得到。映射

$$
(s,t,q)\longmapsto R_n(s)R_{n'}(t)R_{n''}(q)
$$

在零点的导数由三条独立轴的反对称矩阵组成，是 $\mathbb R^3\to\mathfrak{so}(W)$ 的同构。逆函数定理给出包含于 $H_W^+$ 的恒等邻域；$SO(3)$ 的连通性遂给 $H_W^+=SO(W)$。这只使用紧群平均、初等旋转与局部坐标的成熟步骤，没有把连续旋转作为实际门供应。

全部 $x_a=T_a x_\epsilon$，所以其中心化轨道为 $A_av$。若 $v=0$，全部行相同，与容量四矛盾；故 $r>0$。正交性给轨道位于半径 $r$ 球面，刚证出的旋转闭包在球面上传递，给出 (16.9)。球面的闭凸包是闭球，得到 $S_{\min}$。其非负有限组合是该截面的齐次凸包；紧性保证当 $t\to0$ 时空间分量也趋零，故闭包恰为 (16.11) 的 $K_r$。这里确实做了凸化，没有以“射线闭包”代替凸包。

最后取任意兼容 $K$。因 $\sum_w e_{f,w}=u$，在 $K$ 上有 $u\ge0$。若 $u(z)=0$，所有 $e_{f,w}(z)$ 均为零，评价分离 $V$ 便迫使 $z=0$。在截面 $S_K=K\cap\{u=1\}$ 上，每个评价在 $[0,1]$，有限组评价坐标保证 $S_K$ 有界；闭性保证它紧。统计逆将 $T_gK\subseteq K$ 提升为等号，再由闭性延至 $H$。$S_K$ 包含 $S_{\min}$，关于 $c$ 平移后的截面是紧凸、旋转不变集，必为某个半径 $R\ge r$ 的闭球：取最大范数点，旋转给整球面，凸性给其球内；最大性排除球外。由 $u$ 严格正性，每个非零 $K$ 元素均由此截面正缩放得到，故 $K=K_R$。对其效果约束的充要性见下命题。取 $w'=w/R$ 给标准 Lorentz 形式 $t\ge\|w'\|$，所以有序同构成立。∎

### 命题 16.5（固定预测坐标中的全部锥族与准确饱和）

固定定理 16.4 得到的一套预测坐标、中心 $c$ 和内积，后文不同时改写状态与效果。对一个已声明二值事件的某个效果 $e$，写

$$
e(tc+w)=\alpha t+\langle b,w\rangle,\qquad
\lambda=\|b\|>0,\qquad m=\min(\alpha,1-\alpha).
\tag{16.13}
$$

单事件特例另要求：完整终端标签恰为 $\Gamma=\{+,-\}$，取 $e=e_{\epsilon,+}$，并且每个已声明未来的效果满足下列**轨道覆盖前件**：

$$
\forall f\in\mathsf F\quad\exists g\in\mathsf L:\qquad
 e_{f,+}=eT_g\quad\text{或}\quad e_{f,+}=(u-e)T_g.
\tag{16.13a}
$$

等式均指 $V^*$ 中的相等，等价于在全部实际行 $x_a$ 上相等。结合 (16.6) 及 $\mathsf L\subseteq\mathsf F$，这恰说明全部完整标签效果的集合为 $\{eT_g,(u-e)T_g:g\in\mathsf L\}$。$\mathsf F=\mathsf L$ 是保证此覆盖的一个充分情形；一般共同域不添加这一限制。只有两个标签、续接闭性及全未来统计逆均不自动给出 (16.13a)，也不排除其他未来改变效果的偏置或对比。

在上述单事件前件下，兼容锥的**全部固定坐标族**恰为

$$
K_R=\{tc+w:t\ge0,\|w\|\le Rt\},\qquad
r\le R\le\frac{m}{\lambda}.
\tag{16.14}
$$

在同一轨道覆盖前件下，这个区间退化为唯一半径，当且仅当

$$
\lambda r=m.
\tag{16.15}
$$

对一般共同未来域及完整终端菜单，无须 (16.13a)：令 $j$ 遍历每个 $e_{f,w}$ 及其互补事件，或等价地遍历包含它们的全部已声明事件，分别记 $\alpha_j,\lambda_j,m_j$。则准确的一般式为

$$
r\le R\le R_{\max},\qquad
R_{\max}=\inf_{j:\lambda_j>0}\frac{m_j}{\lambda_j}.
\tag{16.16}
$$

$\lambda_j=0$ 的效果只要求 $0\le\alpha_j\le1$；它不标定半径。评价的分离性保证存在非零 $\lambda_j$，行的非负性保证 $r\le R_{\max}<\infty$。完整菜单的唯一性当且仅当 $R_{\max}=r$。任一事件满足 (16.15) 对一般菜单的唯一性仍足够；缺少 (16.13a) 时，不能反称唯一性要求所选基事件满足 (16.15)，因为其他未来效果可给出更紧的界。若事件族无限且下确界不取到，也不能反称唯一性必有某个单事件达到饱和。已有的每个未来效果和新增效果都必须进入 (16.16)，不能把单探测器区间冒充完整菜单区间。

对 $\lambda>0$ 的事件，准确区分下列标定条件：

1. **确定端点。** 若某个实际字的概率恰为零或一，则 (16.15) 成立；反向只保证轨道闭包上有确定端点，不保证某个有限字准确到达。
2. **平衡。** $e(c)=\alpha=1/2$。它没有规定 $\lambda r$ 的值。此时 $m=1/2$，只有再有 $\lambda r=1/2$，才同时得到闭包上的零、一两端。
3. **固定偏置下最大对比。** 实际轨道闭包上的最大值减最小值为 $2\lambda r$，非负互补效果允许的上限是 $2m$。达到这个上限等价于 (16.15)；偏置不平衡时可只有一端确定。
4. **全二值对比。** 对比幅度为一，等价于 $\alpha=1/2$ 且 $\lambda r=1/2$。这同时要求平衡及饱和，不能只由归一化或“projective read”的名称取得。

**证明。** $e$ 在 $u=1$ 的半径 $R$ 球上的最小值、最大值分别为 $\alpha-\lambda R$、$\alpha+\lambda R$。因此 $e\ge0$ 且 $u-e\ge0$ 的充要条件为 $\lambda R\le\min(\alpha,1-\alpha)$。对 $g\in\mathsf L$，由 (16.8) 有

$$
(eT_g)(tc+w)=\alpha t+\langle A_g^{-1}b,w\rangle.
$$

因此可逆前缀作用保持 $\alpha,\lambda$；取互补效果把 $\alpha$ 改为 $1-\alpha$、$b$ 改为 $-b$，仍保持 $m,\lambda$。在 (16.13a) 下，这些计算覆盖每个已声明效果，且没有额外效果遗漏。定理 16.4 给状态下界 $R\ge r$；各 $K_R$ 自动闭凸、含全部实际行并被 $T_g$ 保持，故 (16.14) 完整，(16.15) 正是此特例区间退化的条件。

一般 $\mathsf F$ 中的其他效果不由上述可逆轨道计算代替。直接对每个 $j$ 应用球上极值公式，全部效果非负的充要条件就是 $\lambda_jR\le m_j$；与 $R\ge r$ 联立即得 (16.16)。这一论证无须 $T_f$ 存在或不同未来同轨。非负性延至闭包球面，故每个比值至少为 $r$；至少一个有限比值来自非恒定评价。

在实际轨道上若 $e(x_a)=0$，则 $\alpha\le\lambda r\le m\le\alpha$，所以 $\lambda r=m=\alpha$；若 $e(x_a)=1$，同理 $\lambda r=m=1-\alpha$。反向极点 $w=\pm r b/\lambda$ 在轨道闭包内，故饱和给出对应的闭包端点。平衡与两种对比结论来自同一极值公式。比如 $\alpha=1/3,\lambda r=1/3$ 时范围为 $[0,2/3]$，有确定端点并锁定半径，却没有全二值对比。取 $\alpha=1/2,\lambda r=1/4$ 则平衡但仅凭该效果不能锁定半径；在 (16.13a) 下确有锥歧义，一般菜单还须看其他效果。∎

**定义 16.5a（固定坐标歧义与共同尺度规范的区别）。** 同时变换 $w\mapsto s w$、$r\mapsto sr$、$R\mapsto sR$、$b\mapsto b/s$，$s>0$，使所有配对保持不变，是同一预测表示的坐标规范。它不等于在 (16.14) 的轨道覆盖前件下，或一般式 (16.16) 的许可区间内，保持 $x_a,e_{f,w},T_g,c$ 及内积全部不变而改变 $R$。后者改变哪些未实际取得的预测向量被判为正。固定全部实际行的线性变换必须在它们的线性张成 $V$ 上为恒等，故不能将两个不同 $K_R$ 作为同一固定预测实现识别掉。无论由单事件饱和 (16.15) 还是完整菜单条件 $R_{\max}=r$ 选定固定坐标中的唯一锥，都没有选定一个脱离坐标的绝对长度或物理时间单位。

### 命题 16.6（满足模型、真实锥歧义与删除条件反模型）

以下均为同一抽象来源内的完整两标签终端律；所写门和逆字是各模型声明的菜单，不移植为原生十三维来源的新资源。

取 $W=\mathbb R^3$，选 $\theta/\pi$ 为无理数，声明绕 $z$、$x$ 轴的角 $\pm\theta$ 四个实际控制，所有有限字合法，反向次序的负角词供应统计逆。令 $A_a$ 是按先后调用得到的旋转，$x_a=c+A_ae_z$，且对全部未来 $f$ 定义

$$
p(a;f,+)=\frac12+\frac14\langle e_z,A_fA_ae_z\rangle,
\qquad p(a;f,-)=1-p(a;f,+).
\tag{16.17}
$$

所有概率在 $[1/4,3/4]$ 内。这个**固定响应律**、固定行及固定效果同时兼容 $K_1$ 和 $K_2$，并且恰兼容全部 $1\le R\le2$；没有同时缩放状态和效果。若将 (16.17) 的 $1/4$ 改为 $1/2$，仍为满足模型，此时空字的 $+$ 概率为一，兼容半径唯一为 $R=1$。

删去“像无限”，可取有限的全部坐标置换和符号翻转群，令 $x_a=c+A_a(1,1,1)$，$p(a;f,+)=1/2+(A_fA_a(1,1,1))_3/4$，并保留互补标签。这满足四维实预测容量、统计逆和不可约性，但 $S_{\min}-c=[-1,1]^3$，其锥是立方锥，不是 Lorentz 锥。

删去“不可约”，可取上述绕 $z$ 的无理角旋转及其逆，并加入 $z$ 方向符号翻转。令 $x_a=c+A_a(1,0,1)$，效果为

$$
e(tc+w)=\frac t2+\frac{w_1+w_3}{8},\qquad p(a;f,+)=e(T_fx_a).
\tag{16.18}
$$

它的无限可逆作用保持直线 $\mathbb R e_z$；行容量仍为四，但

$$
S_{\min}-c=\{(w_1,w_2,w_3):w_1^2+w_2^2\le1,\ |w_3|\le1\}.
\tag{16.19}
$$

这是圆柱而不是球，故所得正锥不是 Lorentz 锥。

**证明。** 第一模型的两个无理角幂分别稠密于两轴旋转圆，闭包遂包含 $SO(3)$；两轴的标准表示没有共同非零真不变子空间。状态球面和旋转效果分别仿射张成三维、线性分离三维，所以行容量恰为四。其基效果有 $r=1,\alpha=1/2,\lambda=1/4$；这里 $\mathsf F=\mathsf L$ 为全部有限字，且 $e_{f,+}=eT_f$，故满足 (16.13a)，(16.14) 精确给 $[1,2]$。两个锥不同，例如 $c+\tfrac32e_z$ 仅属于较大者；此向量不是新增实际准备。将系数改为 $1/2$ 给 $\lambda r=m$，证明饱和模型。

有限群模型的轨道恰为立方体八个顶点。它的标准表示不可约：对任意不变子空间，利用单坐标符号翻转之差抽出一个非零坐标轴，再用置换得到全部三轴。三个坐标效果及状态差均满秩，概率为 $1/4$ 或 $3/4$，逆均在菜单内。凸包是立方体，有线段边界，不可能仿射同构于严格凸球。

圆柱模型的轨道闭包是高度 $\pm1$ 的两个单位圆，凸包恰为 (16.19)。各轨道坐标满足 $|w_1+w_3|\le2$，所以两标签概率均合法。旋转效果的平面分量张成 $xy$ 平面，翻转使 $z$ 分量亦被分离；轨道差张成三维，故容量仍为四。圆柱也有非平凡边界线段，排除 Lorentz 截面的严格凸性。三个模型都按同一串接规律定义全部未来，故没有只检查单门而忽略混合词。∎

### 命题 16.6a（相同二标签不蕴含未来效果同轨）

存在满足定义 16.1–16.2 及假设 16.3 的两标签共同域，其中 $\mathsf L\subsetneq\mathsf F$，空未来效果未饱和，但完整菜单的兼容锥唯一；因而不能删除 (16.14)–(16.15) 的轨道覆盖前件。

**证明。** 沿用命题 16.6 的四个旋转字母及无理角，取 $\mathsf L$ 为全部偶长度字，$\mathsf F$ 为全部有限字，$\Gamma=\{+,-\}$。对完整程序 $s$ 定义

$$
p(s,+)=\frac12+\kappa_{|s|}\langle e_z,A_s e_z\rangle,
\qquad
\kappa_n=\begin{cases}1/4,&n\text{ 为偶数},\\1/2,&n\text{ 为奇数},\end{cases}
\qquad p(s,-)=1-p(s,+),
$$

并令 $p(a;f,\pm)=p(af,\pm)$。这给合法概率、共同域及串接恒等式；它只是同一来源的字响应律，没有添加准备、复位、副本或新标签。负角逆字保持偶长度，矩阵乘积恢复恒等，故对每个 $f\in\mathsf F$ 恢复预测行，满足全未来统计逆。偶长度菜单包含绕两轴的 $\pm2\theta$，闭包包含 $SO(3)$，作用无限且不可约。

在固定坐标 $x_a=c+A_a e_z$ 中，各效果为

$$
e_{f,+}(tc+w)=\frac t2+\kappa_{|f|}\langle A_f^{-1}e_z,w\rangle,
\qquad e_{f,-}=u-e_{f,+}.
$$

偶长度状态轨道的仿射张成是三维，偶长度未来的评价已经分离三维空间分量；加上 $u$，这些坐标与实际预测行空间线性同构。因此实预测容量恰为四，$r=1$，并非另添隐藏坐标。空未来效果的参数为 $\alpha=1/2,\lambda=1/4$，其可逆轨道及互补效果的 $\lambda$ 均为 $1/4$。单字未来 $f=R_z(\theta)$ 已合法，却有 $\lambda_f=1/2$，故不满足 (16.13a)。仅约束空未来轨道会留下 $1\le R\le2$，完整式 (16.16) 则给 $R_{\max}=1$，唯一兼容锥为 $K_1$。例如

$$
e_{R_z(\theta),+}(c-2e_z)=-\frac12,
\qquad c-2e_z\in K_2.
$$

所以 $K_2$ 确被一个已有未来效果排除；这里的测试向量不是实际准备。该模型保留主定理的整个共同未来域，展示的只是单轨道特例与一般全效果判据的区别。∎

### 命题 16.7（同一原生菜单的局部角与四字完整回返障碍）

固定[相干重建续卷 II](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md) 定义 77.1 的来源：站点为 $b_{-1},b_0,\ldots,b_8$，$H=V_8^{\mathbf1}$ 为整个十三维扇区，$e_\beta=|10\,\beta\,010\rangle$，$\beta=(b_1,\ldots,b_5)$ 无相邻占据。唯一 ready 为 $v=e_{00100}$，完整标签为 $\Gamma=\{0,1\}^{10}$。取

$$
x=\varphi^{-1},\quad y=\sqrt x,\quad x+x^2=1,\quad
\zeta=e^{3\pi i/5},\quad
Q=\begin{pmatrix}x&xy\\xy&x^2\end{pmatrix},
\quad K_j=\zeta[I+(\zeta-1)\mathcal P_j],
\tag{16.20}
$$

其中 $\mathcal P_j=n_{j-1}n_{j+1}+(1-n_{j-1})(1-n_{j+1})Q_j$ 是同一三站点投影。仍按

$$
K_{j_1\cdots j_\ell}=K_{j_\ell}\cdots K_{j_1},\qquad K_\epsilon=I
\tag{16.21}
$$

书写调用顺序。本命题**使用已给的矩阵/Born 模型作为反模型**，$q_v(\psi)=|\langle v,\psi\rangle|^2$；它不是从未知终端响应律推出 Born 规则。

首先，局部子空间 $L=\operatorname{span}\{e_{00100},e_{00101}\}$ 在地址 $4,5$ 下不变。在此顺序的基中有字面对应

$$
K_4|_L=\zeta[I+(\zeta-1)P],\quad P=\operatorname{diag}(0,1),\qquad
K_5|_L=\zeta[I+(\zeta-1)Q].
\tag{16.22}
$$

因此这两个地址在已给模型中有一个真正的两分量角；这个对应不能替换为另一九位编码的 ready 或地址。

但对同一来源全部七地址，取四个合法前缀

$$
u_0=\epsilon,\qquad u_1=1,\qquad u_2=5,\qquad u_3=15.
\tag{16.23}
$$

每门满足 $K_j^{10}=I$，故 $j^9$ 是已允许的九次正向调用，供应 $K_j^{-1}$。取 $u_0^{-1}=\epsilon,u_1^{-1}=1^9,u_2^{-1}=5^9,u_3^{-1}=5^9 1^9$，其中最后一个字按先九次 $5$、后九次 $1$ 调用。对**完整标签** $w_v=1000100010$ 及其单标签事件 $E_v=\{w_v\}$，全部十六个受控程序给

$$
r_{ij}=p(u_j;u_i^{-1},w_v)
      =q_v(K_{u_i}^{-1}K_{u_j}v),\qquad 0\le i,j\le3.
\tag{16.24}
$$

令 $a=x^2$，则准确表为

$$
r=\begin{pmatrix}
1&a&a&a^2\\
a&1&a^2&a\\
a&a^2&1&a\\
a^2&a&a&1
\end{pmatrix}
=\begin{pmatrix}1&a\\a&1\end{pmatrix}\otimes
 \begin{pmatrix}1&a\\a&1\end{pmatrix}.
\tag{16.25}
$$

其中心化矩阵 $B=2r-\mathbf1_4\mathbf1_4^{\mathsf T}$ 不正半定，因为

$$
\begin{aligned}
\mathbf1_4^{\mathsf T}B\mathbf1_4
 &=8(1+a)^2-16\\
 &=40x^2-16=24-40x<0.
\end{aligned}
\tag{16.26}
$$

所以不存在任何实内积空间中的单位向量 $n_0,\ldots,n_3$ 使 $r_{ij}=(1+\langle n_i,n_j\rangle)/2$。尤其不可能把这个完整回返表解释成四个同标签纯 qubit 的相互重叠。障碍直接是共同 centered Gram 正性，不需要同时存在四个 $\pm1$ 隐藏变量的假设。

**证明。** 对 (16.22)，两条路径都有 $b_3=1,b_4=0,b_6=0$。地址 $4$ 的左右邻为 $1,b_5$，只施加投影值 $b_5$ 的相位，不翻转中心 $b_4$；地址 $5$ 的邻位均零，按中心位顺序 $b_5=0,1$ 施加 $Q$。两门因而保持 $L$ 并给所列矩阵。这里没有改变 $H$、基序或 ready。

地址 $1$ 的三站点支撑是 $(b_0,b_1,b_2)$，地址 $5$ 的支撑是 $(b_4,b_5,b_6)$，二者不交，所以它们在整个站点空间上交换，限制到 $H$ 后仍交换。由 $Q^2=Q$，$\mathcal P_j$ 也是投影，$K_j$ 的本征值为 $\zeta,\zeta^2$，两者十次方均为一，故上述逆字保持共同标量，且

$$
K_{5^9 1^9}=K_1^9K_5^9=(K_5K_1)^{-1}.
\tag{16.27}
$$

这四个前缀及其相对词保持四维矩形

$$
M=\operatorname{span}\{e_{00100},e_{10100},e_{00101},e_{10101}\}
 =\operatorname{span}\{e_{i010j}:i,j\in\{0,1\}\}.
\tag{16.28}
$$

在 $M$ 上 $b_2=b_4=0$，两外邻 $b_0=b_6=0$；故 $K_1$ 只在 $i$ 位施加 $U=\zeta[I+(\zeta-1)Q]$，$K_5$ 只在 $j$ 位施加同一个 $U$。四条路径都合法，$b_3=1$ 始终不动。ready 对应 $(i,j)=(0,0)$，并非把整个十三维扇区替换成四维来源。

从中心输入零返回零的振幅是 $A=\zeta[1+(\zeta-1)x]=\zeta(x^2+x\zeta)$。由 $\zeta+\bar\zeta=-x$ 有

$$
|A|^2=x^4+x^2+x^3(\zeta+\bar\zeta)=x^2=a.
\tag{16.29}
$$

逆门的对应对角元为共轭，故同样给 $a$。两个前缀坐标相同时相对算子为恒等，给返回概率一；不同时为 $U$ 或 $U^{-1}$，给 $a$。两独立矩阵因子的返回振幅相乘，因此差一位给 $a$、差两位给 $a^2$，证明 (16.25)。这是所给矩阵的因子化计算，不供应独立准备或外部副本。

每行和为 $(1+a)^2$，所以 $\sum_{i,j}r_{ij}=4(1+a)^2$，$\sum_{i,j}B_{ij}=8(1+a)^2-16$。又 $(1+x^2)^2=(2-x)^2=5x^2$，得到 (16.26)。$x=(\sqrt5-1)/2>3/5$ 保证严格负号。若有所述单位向量，则 $B_{ij}=\langle n_i,n_j\rangle$，全一二次型等于 $\|\sum_i n_i\|^2\ge0$，矛盾。在复二分量纯态中，Pauli 展开给 $\operatorname{Tr}(\rho_i\rho_j)=(1+n_i\cdot n_j)/2$，所以这个受限解释确被排除。原十三维 Born 模型仍完全一致；本命题没有排除高维纯态重叠、不同准备与不同读口的一般配对、非纯局部描述或未中心化的正核。

每个条目读取原 $1024$ 标签行中的 $w_v$，其余标签保留且总和仍为一；没有改成某一位成功事件，也没有后选择。故这是实际有限合法门词上的障碍，不依赖密度极限、额外相位参考或任意准备。∎

### 定义 16.8（有序前端与量子公理的分层接口）

本节推导的对象是所声明局部域的**实有序预测载体**。与 C115、C117 及通常量子公理的关系按以下合同分开：

| 结构 | 本节条件及其结论 | 尚需供应的量子接口 |
|---|---|---|
| 预测充分性 | 全部合法终端未来的行商核，实秩四及三维差空间 | 四维容量和共同未来域在所选原生菜单上成立；加入记录后重新核对 |
| 正几何 | 统计逆、无限不可约作用导出不变正定内积、旋转闭包、球形最小凸截面及全部兼容 Lorentz 锥族 | 不把闭包元素或凸组合当成实际准备；更大域的锥另证 |
| 二值评价 | 全标签正归一行给有限事件的实线性效果；单事件饱和 (16.15) 足够，完整菜单唯一性的充要条件为 (16.16) 中 $R_{\max}=r$；单事件必要性另需 (16.13a) | Born 的全部效果拆并及读口对应，不由已供应效果的线性扩展自动取得 |
| 局部二元结构 | $w/R$ 归一后给三维球的有序几何，可接 C115 的欧氏比较空间 | 另需有向双线性变化、同一两分量表示及结合闭合；不是任意更大结合包络 |
| 复振幅与相位 | 本节未选复标量；$SO(3)$ 是数学预测闭包 | C115 定义 2.2 的有向闭合迫出中央 $J^2=-1$；相干复值关系核及共同内部相位参考另供 |
| 可逆门与过程 | $T_g$ 为局部锥的有序自同构，允许的反射仍可能存在 | 取向、复线性、完整输入比较与记录；有序可逆不独自推出量子幺正性 |
| 测量后继与记录 | $p(a;f,w)$ 是完整终端读出，未规定读后态 | C117 Q4 的完整过程、正交记录、失败分支、初始化资源及合法忽略记录 |
| 复合与共同中心 | 本节不添加独立系统或张量积 | C115 共同复中心、交换嵌入及生成性，C117 Q3 的内部准备支持 |
| 观察细化与时间 | 只量化已有有限字，不添加连续时间 | C117 Q5 的共同细化与覆盖，以及 Q6 另供的连续一参数群、物理时间对应 |

式 (16.12) 的 $c$ 是预测群的数学固定中心，不是中央复数 $J$、外部参考态或可实际重置到的 ready。球面是最小预测凸包的极点集合，不证明整个 $\omega$ 纯，也不证明在更大兼容锥中的实际行纯。有限域三维不具有这里使用的实概率凸性、紧性及连续旋转，因此不能同名替换成 Bloch 球。

若进一步供应 C115 的对称双线性比较 $S$ 和有向变化 $D$，且 $S+jD$ 在同一个两分量空间内表示、闭合并结合，才可消费其定理 2.3、命题 2.5 的结论：有向常数与 $j^2$ 相锁定，中央归一元平方为负，代数同构于 $M_2(\mathbb C)$。这条乘法前件没有由 (16.9) 的旋转轨道取得。进一步供应 C117 Q3–Q6，才可消费复合、记录、细化、理想更新及另供连续时间的相应结论。

在已经给出复振幅解释时，普通门 $U$ 与 $-U$ 对未带相干分支路由的全部门序列终端概率有相同作用：每个完整确定门词至多改变整体标量。相干受控路由 $I\oplus U$ 与 $I\oplus(-U)$ 则相差可干涉的分支相对号，不能据普通行等价将它们认作同一操作。比较它们需要实际保相干的路由、共同内部相位关系及记录合同；数学自旋提升或正向逆字不供应这些资源。这里也不将一个 GNS 循环向量误认成纯宇宙态。

### 定义 16.9（承重综合、来源对应与剩余起源命题）

本节的 `repo-derived` 综合是将同源、共同合法未来的准确行等价接到统计逆与实容量，导出局部有序完成，再在**固定预测实现**中分清最小锥、效果约束和饱和唯一性，并用原七地址的有限完整回返表阻止把局部二元中心化提升至全部菜单。紧群、三维旋转、凸锥与 qubit 几何的成熟步骤不是新的量子原理。引用和版本的条件对应如下；不主张穷尽文献或原创优先权。

| 来源 | 实际消费的条件与工具 | 不由该来源或本节取得的内容 |
|---|---|---|
| [C115](AURIC_BINARY_SQUARE_TWO_COMPONENT_COMPOSITION_AND_INTERNAL_COMPLEX_STRUCTURE_C115.md) §§2、4–6；本卷 §§2–3、7–9、14 | 已有二元有序几何、同空间有向结合闭合及条件性的共同中心、记录、GNS 接口 | 不重证为新成果；本节未替这些接口取得原生前件 |
| [相干重建续卷 II](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md) 定义 77.1、定理 77.2；v15 (3.1)–(3.2) | (16.20)–(16.29) 的同一十站点、七地址、十三路径、ready、完整标签、正向逆字和矩阵比较模型 | 未知响应律的 Born 性、全菜单实秩四、额外实际资源 |
| Monras–Winter, *Quantum learning of classical stochastic processes: The completely-positive realization problem*, [arXiv:1412.3634v1](https://arxiv.org/html/1412.3634v1)，Lemma 3、4、7 及 §4 | `literature-attested`：稳定锥、群逆将稳定提升为不变、最小商实现；本节取 $D\leftrightarrow T_g,\tau\leftrightarrow x_\epsilon,\pi\leftrightarrow e_{f,w}$ 的源相对类比 | 原文是 stationary output process；本节是每个受控字后归一的终端行，不能挪用其随机过程假设或 CP 实现 |
| Fanizza–Lumbreras–Winter, *Quantum theory in finite dimension cannot explain every general process with finite memory*, [arXiv:2209.11225v2](https://arxiv.org/html/2209.11225v2)，§2.1 (5)–(7)、§2.2 (8) | `literature-attested`：$C_{\min}\subseteq K\subseteq C_{\max}$ 的锥夹层及 SDR 必要条件背景；这里 $C_{\max}$ 改为所有合法终端效果非负的集合 | 不把其 stationary Hankel 域当成本节共同控制域；一个 Lorentz 锥不足以提供 CP 矩阵层次 |
| Freedman–Larsen–Wang, *The two-eigenvalue problem and density of Jones representation of braid groups*, [math/0103200v1](https://arxiv.org/html/math/0103200v1)，§2、Theorem 0.1 | `literature-attested`：原卷 77.2 已对 $r=5,n=8,\lambda=[4,4]$ 的全十三维逐基逐门对应后使用的密度供应 | (16.25)–(16.29) 本身只用有限矩阵，不调用密度或将闭包门认作实际调用 |
| Barnum–Hilgert, *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*, [arXiv:1904.03753](https://arxiv.org/html/1904.03753)，Theorem 1.1 | `literature-attested`：spectral 与 strongly symmetric 的有限维紧凸集分类，用于区分另一条更强的状态空间路线 | 本节未假设或取得其完整 frame/spectral 供应，也不从名称调用该全分类 |
| Araújo et al., *Quantum circuits cannot control unknown operations*, [arXiv:1309.7976](https://arxiv.org/html/1309.7976)，式 (1) 前后的相位论证 | `literature-attested`：普通未知 $U$ 的整体相位与受控相对相位不同，子空间实现可有额外信息 | 不把其电路禁定理当作所有物理控制的不可能性，亦不增添本源相干控制 |
| [C118 §§140–149，固定版本](https://github.com/the-omega-institute/trureturing/blob/e54a4512cdaf8733f5e522d0ece9a826ec1dfebe/docs/develop/theory/AURIC_COMPOSITE_COMPARISON_REFERENCE_FREE_FILTER_RELATIONS_V96_CONTINUATION.md) | 两个固定生成词与二十四项校正目录；条件仍含有限复载体、全称实际细记录 F、实际支持逆、准备读回与准确有限校准包 | 不供应本节原生容量与锥、复中心、物理资源或时间；有限目录不等于整个无界菜单的一份有限证书 |
| [C113 §§20–22，固定版本](https://github.com/the-omega-institute/trureturing/blob/5ccf20964da0a6695170f80f89e8383c92913a6c/docs/develop/theory/AURIC_INTERNAL_BALANCED_CALIBRATION_AND_FILTER_COMPOSITION_GEOMETRY_C113.md) | 同一正复线性分支、正确效果、指定 $J$、实际准确有限二阶设计与完整读回下的近饱和界，含奇异效果及矩形输出 | 不从任意小正缺陷推出准确 CP；不取得设计、读口漂移协议、原生前端或共同资源 |

剩余起源命题是：在同一个 $\Omega$ 的原生实际域中构造满足定义 16.1–16.3 的局部菜单，取得完整效果族的准确饱和或说明其锥歧义，再取得 C115 的有向两分量结合闭合、共同相干相位以及 C117 的实际记录、共同中心、复合和时间合同。四维容量、全未来统计逆及无限不可约性在这里都是条件；有限门词或有限采样不能独自认证它们的无限量词。命题 16.7 又表明不能把正确的局部角直接扩成原七地址的共同 centered 单位向量核。上述缺口仍为 open，本节的局部条件推导不构成整个量子起源的完成。

## 追加锚（本行以下为增补区）

## 17. 实三维比较与原生四时关系：先导出全未来容量，再接 qubit

本节补的是 §16 的一个前件，而不是重述其四维假设：在明确供应的实三维比较空间上，方向标签本身允许任意连续非线性响应；额外要求原有黄金四时关系在同一实际局部域的所有前后文、完整标签与原始概率上成立，才排除高阶响应模态，导出非退化时的共同实预测容量四。这里不先给复射线、复矩阵、Born 律、CP 或有限预测维数。实三维、共同未来充分性、连续性、旋转供应和准确四时关系都是建模前提，不能以“量子起源”为名隐去。

### 定义 17.1（实际局部输入、前缀、完整未来与原始行）

固定同一个 $\Omega$、同一个 $\omega$、一个原生局部输入类型及其唯一指定初始条件。令 $\mathcal L$ 为实际可调用的确定性控制正有限字幺半群，$\epsilon$ 为不调用控制；$\mathcal A=\mathcal L$ 为本节的前缀域。不对中间测量结果后选择，不另取 ready、外部 reset、独立副本或相位参考。字的调用顺序沿用 (16.21)。实际字、控制器和器件仍保留各自身份：两个字即使在下面的比较空间上作用相同，也不是同一物理程序的定义。

令 $\mathcal F$ 为这个共同输入类型上**全部原有合法有限终端请求**，包含原有的控制延续、读口、器件身份、事件和一切合法可问的旧记录；$q\in\mathcal F$ 带原来的完整有限标签集 $\Gamma_q$。请求可以任意长，$\mathcal F$ 不要求有限。每个 $\mathcal A\times\mathcal F$ 配对合法；若原菜单没有这个共同类型，就不能直接适用本节。对 $b\in\mathcal L$，先调用 $b$ 再执行 $q$ 是同一未来域中的请求 $bq$。数据为

$$
p(a;q,w)\ge0,\qquad
\sum_{w\in\Gamma_q}p(a;q,w)=1,\qquad
p(ab;q,w)=p(a;bq,w).
\tag{17.1}
$$

完整标签包括原有成功、失败、零标签、端口及记录值，不合并原来可区分的标签。事件 $E\subseteq\Gamma_q$ 的质量为 $\sum_{w\in E}p(a;q,w)$；有正分母时才能条件化，零质量分支不产生归一后继态。若一个前缀本来有非单位制备成功质量，不能只用成功条件分布冒充 (17.1)；须将该质量及失败记录纳入同一实际合同，或明确它不属于这里的确定性前缀域。

定义完整行、准确全未来等价及其共同实线性容量：

$$
x_a=(p(a;q,w))_{(q,w)\in\mathcal I},\quad
\mathcal I=\{(q,w):q\in\mathcal F,\ w\in\Gamma_q\},\quad
a\sim a'\ \Longleftrightarrow\ x_a=x_{a'},\quad
d_{\rm loc}=\dim_{\mathbb R}\operatorname{span}\{x_a:a\in\mathcal A\}.
\tag{17.2}
$$

这是局部、指定共同类型的终端预测维数，不是整个 $\omega$ 的维数。$\mathcal F$ 包含一个分支程序，不意味着该程序的每个读后分支又成为 $\mathcal A$ 中的合法准备；这种分支前缀闭合另需供应。合法请求若会离开局部角，也不能因此从 $\mathcal F$ 删掉。

### 定义 17.2（实方向模型：充分性不是仿射性）

供应一个正定实内积空间 $W$，$\dim_{\mathbb R}W=3$，一个单位向量 $n_\epsilon$，以及实际控制的旋转 $A_b\in SO(W)$，满足

$$
n_a=A_a n_\epsilon,\qquad
n_{ab}=A_b n_a,\qquad
A_{bc}=A_cA_b,\qquad
\overline{\{A_b:b\in\mathcal L\}}=SO(W).
\tag{17.3}
$$

所用比较逆作用须由实际允许的正有限字供应，不能由群闭包制造实际逆门；是否在完整行上互逆仍由 (17.4) 的全未来合同承担，不主张两个器件程序字面相同。闭包及任意实凸组合在本节只是数学工具，均不增加实际可用的准备、控制或复制操作。

对**每个**原请求及完整标签，另供应一个连续函数

$$
F_{q,w}:S(W)\longrightarrow[0,1],\qquad
p(a;q,w)=F_{q,w}(n_a)\quad(a\in\mathcal A).
\tag{17.4}
$$

式 (17.4) 是全未来方向充分性及其连续延拓：相同方向不能被任何保留的旧记录问题区分。它不是“只看选定成功口”，也不是在已完成层析后删去其余读口。由 (17.1)、稠密轨道和连续性，

$$
F_{bq,w}(n)=F_{q,w}(A_bn),\qquad
\sum_wF_{q,w}(n)=1\quad(n\in S(W)).
\tag{17.5}
$$

特别地，全未来等价对右接实际控制不变。定义并未要求 $F$ 线性、仿射、多项式或有限调和展开；如 $F(n)=(1+(e\cdot n)^3)/2$ 仍符合方向充分性。三维**输入标签**不等于四维**响应行空间**，后者须由下面的选择关系推出。

### 定义 17.3（原生黄金四时选择关系）

令 $x=(\sqrt5-1)/2$，供应一个实际字 $t\in\mathcal L$，$A_t$ 是绕某单位轴旋转 $\theta=\pm3\pi/5$。要求对所有 $a,b\in\mathcal L$、$q\in\mathcal F$、$w\in\Gamma_q$，在相同输入资源和原始质量下有

$$
p(at^3b;q,w)+x^2p(atb;q,w)
=p(ab;q,w)+x^2p(at^2b;q,w).
\tag{17.6}
$$

这是 [V24 引理 7.2](AURIC_TWO_BASIS_STATES_THREE_CHANNELS_PHASE_CHIRALITY_AND_RECURSIVE_SQUARE_LAW_V24.md) 和[相干重建续卷 II §85](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md) 的同一准确四时系数关系。新前端不消费它们的已给复射线、有限复载体或 Born 实现，而将 (17.6) 作为未知原生响应的独立前件。它不是近似校准，也不是只有有限个已测上下文的等式。

其简洁比较几何是同一旋转轨道上的加权四边形闭合：

$$
A_t^3+x^2A_t=I+x^2A_t^2.
\tag{17.7}
$$

式 (17.7) 由 $A_t$ 的轴向特征值 $1$ 和平面旋转角给出；它是**方向**的关系，不能自行推出未知 $F$ 保持这个关系。式 (17.6) 额外要求每个原生响应保持这个特定四点平衡，且对所有共同实际前后文成立。系数相等不供应实验性混合装置或四条同时存在的样本。

### 定理 17.4（全未来仿射化、非退化容量四与准确识别）

在定义 17.1–17.3 下，存在唯一的 $\alpha_{q,w}\in\mathbb R$、$\beta_{q,w}\in W$，使

$$
F_{q,w}(n)=\alpha_{q,w}+\langle\beta_{q,w},n\rangle,\qquad
\|\beta_{q,w}\|\le\min\{\alpha_{q,w},1-\alpha_{q,w}\},
\quad
\sum_w\alpha_{q,w}=1,\quad\sum_w\beta_{q,w}=0.
\tag{17.8}
$$

反过来，(17.8) 的每个仿射响应都满足 (17.6)。若全部 $\beta_{q,w}=0$，则 $d_{\rm loc}=1$，所有实际前缀全未来等价。否则

$$
d_{\rm loc}=4,\qquad
a\sim a'\ \Longleftrightarrow\ n_a=n_{a'}.
\tag{17.9}
$$

更准确地，非退化时

$$
J:\mathbb R\oplus W\longrightarrow
\mathbb R^{\mathcal I},\qquad
J(s,r)_{q,w}=\alpha_{q,w}s+\langle\beta_{q,w},r\rangle
\tag{17.10}
$$

是到完整行张成空间的线性同构，$x_a=J(1,n_a)$。实际可逆控制的预测作用满足 $T_bJ(s,r)=J(s,A_br)$。最小闭凸归一完成为 $J(1,\overline B_W)$，其最小闭锥是

$$
J\{(s,r):s\ge\|r\|\}.
\tag{17.11}
$$

这是最小预测完成，不断言球内每一点都是实际准备，也不排除 §16 的更大兼容锥歧义。

**证明。** 记 $A=A_t$，$U_Bh(n)=h(Bn)$，并在连续函数的复化空间上置

$$
R(z)=z^3-x^2z^2+x^2z-1
=(z-1)(z-\zeta)(z-\bar\zeta),\qquad
\zeta=e^{3\pi i/5}.
\tag{17.12}
$$

因 $\zeta+\bar\zeta=-x$ 且 $1-x=x^2$，因式分解准确成立，$\zeta$ 的阶为十。对任一固定 $F=F_{q,w}$，(17.6) 先在所有 $n_a$ 上给 $R(U_A)U_{A_b}F=0$。式 (17.3) 的轨道稠密及连续性把它延拓到整球面；实际 $A_b$ 在 $SO(W)$ 稠密，又给

$$
R(U_A)U_BF=0\qquad(B\in SO(W)).
\tag{17.13}
$$

这里没有声称极限 $B$ 是可实际调用的门。

令 $N$ 为满足 (17.13) 的连续复函数闭子空间。它在一致范数下闭且对所有旋转不变：虽然 $U_BU_C=U_{CB}$，右侧仍遍历全部旋转。消费球面调和的成熟结论：$L^2(S^2)$ 分解为互不等价的不可约 $SO(3)$ 模 $\mathcal H_\ell$，$\ell=0,1,\ldots$；中心特征标积分 $P_\ell h=(2\ell+1)\int_{SO(3)}\overline{\chi_\ell(B)}U_Bh\,dB$ 给每个 $\mathcal H_\ell$ 的有界投影，其中 Haar 测度归一，$\chi_\ell$ 为该不可约表示的特征标。该积分由连续函数中的有限和一致逼近，故 $F\in N$ 的投影仍在 $N$。若其 $\ell$ 分量非零，不可约性迫使整个 $\mathcal H_\ell\subseteq N$。这是使用既有表示论工具，不是另立一条 trine 或射影刚性定理。

若 $\ell\ge2$，则 $\mathcal H_\ell$ 有绕 $A$ 的轴的非零权 $m=2$ 分量；在复基中其 $U_A$ 特征值为 $\zeta^2$ 或 $\bar\zeta^2$。两者均不是 (17.12) 的三个根，故这个分量不可能满足 $R(U_A)h=0$，矛盾。因此所有 $\ell\ge2$ 分量为零。该论证使用每个高阶不可约模都含权二，而不是只检查最高权；例如权十一能模十伪装成权一，不能据此放过整个高阶模。由 $L^2$ 完备性，$F$ 几乎处处等于 $\mathcal H_0\oplus\mathcal H_1$ 中的函数；两侧连续且球面测度满支撑，等式处处成立。这也处理了没有预先有限展开的任意连续 $F$。

常数与一次球面调和恰为 $\alpha+\langle\beta,n\rangle$。它在球面上的极值是 $\alpha\pm\|\beta\|$，给 (17.8) 的正性界；(17.5) 和系数唯一性给两条归一式。(17.7) 则直接证明逆向。至此没有假设任何有限行秩。

若有 $\beta_{q,w}\ne0$，后接控制的效果满足

$$
\alpha_{bq,w}=\alpha_{q,w},\qquad
\beta_{bq,w}=A_b^{-1}\beta_{q,w}.
\tag{17.14}
$$

它们的实张成包含 $W$：实际轨道稠密于整个非零球面，有限维线性子空间是闭的。若 $J(s,r)=0$，对一个请求求全标签和先给 $s=0$，再由 (17.14) 给 $r=0$，所以 $J$ 单射。另一方面 $\{(1,n_a)\}$ 张成 $\mathbb R\oplus W$，因为稠密球面不在任何真仿射超平面中。故所有行的张成恰为 $J(\mathbb R\oplus W)$，维数四，且准确等价正是方向相同。右接控制的作用、最小闭凸包及锥由相同稠密性得到。若全部 $\beta=0$，各行是同一个非零归一行，其张成为一维。∎

### 推论 17.5（导出容量后的忠实局部 qubit 表示）

在定理 17.4 的非退化情形，选择 $W$ 的一个正向正交基。到这一步才使用 Pauli 矩阵，置

$$
\rho_a=\frac{I+n_a\cdot\sigma}{2},\qquad
E_{q,w}=\alpha_{q,w}I+\beta_{q,w}\cdot\sigma.
\tag{17.15}
$$

由 (17.8)，$0\le E_{q,w}\le I$，$\sum_wE_{q,w}=I$，并且

$$
p(a;q,w)=\operatorname{Tr}(\rho_aE_{q,w}).
\tag{17.16}
$$

这消费 [V48 §7.5](AURIC_ISOTROPY_CHIRALITY_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V48.md) 已有的仿射球—密度矩阵—效果接口，不把 Pauli 表示列为输入，也不重复声称 Born 分类。$n_a\mapsto\rho_a$ 对完整行忠实；最小闭凸完成对应 qubit 密度球，已供应请求对应其中实际效果的有限 POVM 子菜单，不供应所有 POVM。一个原标签若在全部前缀上概率零，其效果就是零；标签仍保留。成功/失败的原始质量和每个事件的有限加和原样保留，不重归一化成二标签实验。

由 V48 定理 6.3 的 $SU(2)\to SO(3)$ 双覆盖，每个实际可逆控制有数学幺正代表，其共轭作用实现 $A_b$。给生成控制选取提升后按实际字相乘即可；相同旋转的不同字可能相差中央号，其量子通道作用相同。忠实性指预测行及旋转作用，不是对不同硬件字身份的单射。也没有据此提供相干受控门、原有仪器的读后更新或相对整体相位的实际检测。

## 18. 对 (16.22) 的原生挂接：局部旋转密度与待供应的响应

### 命题 18.1（两个原地址的实比较作用稠密）

保留 (16.20)–(16.22) 的同一来源、地址 $4,5$、角 $L$ 和 ready。在候选实比较模型中取

$$
e_z=(0,0,1),\qquad
u=(2x\sqrt x,0,2x-1),\qquad
\theta=3\pi/5,\qquad
A_4=R_{e_z}(\theta),\quad A_5=R_u(-\theta).
\tag{18.1}
$$

这里 $4x^3+(2x-1)^2=1$，所以 $u$ 为单位轴，且不与 $e_z$ 共线。这两个旋转生成的闭包是 $SO(3)$；两者阶均为十，$4^9,5^9$ 分别供应它们的正字逆作用。

**证明。** 使用实三维旋转的标准单位实四元数提升，令 $c=\cos(\theta/2)$、$s=\sin(\theta/2)$。$A_4$、$A_5$ 的提升可取 $c+se_z$、$c-su$，其中向量视为纯虚实四元数。实际正字 $45^9$ 的作用是 $A_5^{-1}A_4$，其提升的标量部为

$$
c^2-s^2(e_z\cdot u)
=\frac{2-x}{4}-\frac{2+x}{4}(2x-1)
=\frac{x^2}{2}.
\tag{18.2}
$$

若该旋转有限阶，提升的两个复特征值必为互逆单位根，故其迹 $x^2=(3-\sqrt5)/2$ 是单位根与其逆的和。这样的代数数每个共轭都在 $[-2,2]$；然而 $x^2$ 的不可约多项式是 $z^2-3z+1$，另一共轭 $(3+\sqrt5)/2>2$，矛盾。因此生成群无限。这里用复数检查实四元数的有限阶，只是成熟旋转工具，不是对未知概率假设复量子载体。

旋转角既非零亦非 $\pi$，每个生成元唯一的不变实直线是其轴。两轴不同，故生成群没有共同不变直线；在正交三维空间中，不变平面也给不变正交直线。因此作用不可约。现在只消费 §16 定理 16.4 证明中的**紧实三维群步骤**：无限不可约闭子群的单位分量不能是平凡群或轴旋转群，故含整个 $SO(3)$。此步骤不使用该定理的容量四前件；没有循环调用其整体结论。∎

在已经给定的 (16.22) 矩阵比较模型中，$P=(I-\sigma_z)/2$、$Q=(I+u\cdot\sigma)/2$；其普通共轭作用恰为 (18.1)。这个逐地址对应说明挂接位置确是原来的局部二元角。它不证明未知原生概率必须按共轭作用或 Born 律产生。全十三维 $PU(13)$ 的密度也未被用来替代此局部 $SO(3)$ 证明。

### 定义 18.2（同源挂接的剩余供应合同）

要在原生数据上消费定理 17.4，须明确提供下列内容，而不是将矩阵比较模型的解释复制为未知响应的证明：

1. 同一 ready 在比较空间的方向为 $n_\epsilon=e_z$，地址 $4,5$ 的原生可逆确定性字满足 (18.1) 的实比较模型。命题 18.1 随后提供旋转密度，不再另假设全局复射影密度。
2. 这些前缀有同一实际合法终端未来类型；保留原来的 $\Gamma=\{0,1\}^{10}$ 全部 $1024$ 标签及所有原来可问的旧记录、器件、端口和合法延续。其余五个地址可以不作为局部可逆前缀，但其合法终端延续不能以“离开 $L$”为由删除。
3. 所有这些完整原始响应满足 (17.4) 的方向充分性与连续性，以及以 $t=4$ 代入的 (17.6) 的全部 $a,b,q,w$ 等式。这是新的实质原生供应义务，不是一个有限回返表或一个成功口的结论。
4. 资源、初始化概率、原有失败和零分支均与 (16.20) 的来源一致；正向逆字的操作存在也不能充当重置、复制、未供应的制备或共同内部相位参考。

特别地，若存在一个合法旧记录问题区分 $\epsilon$ 与 $4^{10}$ 的程序档案，两者虽有相同方向，(17.4) 就失败；必须报告失败，不能抹掉档案。一般地，任何 $n_a=n_{a'}$ 而保留记录概率不同的实际对，都直接否证这个全未来挂接。此边界消费[相干重建续卷 II §§83.1–83.3](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md) 已有的“条件索引终端未来”与“可访问程序档案”区别。

已给矩阵/Born 模型在 $L$ 上提供这类响应的一个一致性比较实例：任意原终端效应限制到 $L$ 后仍为正效果，故有 (17.8) 的形式；所有完整标签的四时关系随之成立。这个实例不确立未知原生响应的 (17.4)、(17.6)，也不许删去原模型外额外保留的记录。命题 16.7 的七地址四前缀反例则仍然阻止把这个局部结论提升为全部原历史的共同 centered qubit 核。

## 19. 选择关系的作用：兼容模型、删除模型与高阶响应

### 命题 19.1（同一实方向与控制上的四种精确区别）

下列模型都是解析的条件模型，不声称它们分别已由原始硬件供应。前两项固定命题 18.1 的控制、$n_\epsilon=e_z$ 和单次确定性门词，无外部逐次自由制备；$\mathcal F$ 包括任意实际后接字 $f$ 和终端标签。若用原 $\Gamma$，选择两个不同完整标签 $w_+,w_-$，其余标签保留且概率零；原本若赋予这些标签特殊物理含义，还须另行匹配，不能据这个抽象模型改写原源。

**(a) 兼容非退化模型。** 对任意 $0<\eta\le1/2$，取

$$
p(a;f,w_\pm)=\frac12\pm\eta\,e_z\cdot A_fn_a .
\tag{19.1}
$$

它保留原始正归一质量、逆字和共同未来，满足全部 (17.6)，且有至少一个非零方向效果。因此其完整共同实容量为四。无锐度 $\eta=1/2$ 的额外要求；此例既不供应全效果菜单，也不通过理想测量更新获得结论。

**(b) 删除四时关系，保留三维方向和满旋转。** 采用 V48 命题 7.4 与 V24 §6 已有的立方响应，而将其接到这里的同一完整有限字域：

$$
p(a;f,w_\pm)=\frac{1\pm(e_z\cdot A_fn_a)^3}{2}.
\tag{19.2}
$$

这不是新的立方反例或新的 trine 刚性成果。其本节用途是准确计算共同全未来容量并检验选择关系。写 $z^3=(3/5)z+(2/5)P_3(z)$；一次和三次球面调和分量都非零。在稠密旋转下，后接效果张成 $\mathcal H_1\oplus\mathcal H_3$，因为它们是互不等价不可约模；完整标签求和再给常数。稠密前缀球面上的评价不消灭任何非零连续函数，故共同响应行秩准确为

$$
1+\dim\mathcal H_1+\dim\mathcal H_3=1+3+7=11.
\tag{19.3}
$$

于是三维方向充分性、正归一、满旋转、可逆性乃至 $e_z\cdot n=\pm1$ 的端点标定均不够。由定理 17.4 的证明或三次分量的权二，必存在**实际有限** $a,b,f$ 及某完整标签使 (17.6) 不成立；若每个实际有限上下文都成立，其连续稠密延拓就会迫使三次分量消失。这里不把 11 说成原源容量，只是所声明反模型的准确全未来容量。

**(c) 删除方向充分性，保留完整四时关系和一项可见记录。** 为使区别具体，另取这个反模型的初始条件 $(n_0,c_0)=(u,0)$，不将它冒充原来源的 ready；$c\in\{0,1\}$ 是原样可读取的记录。控制作用为

$$
4:(n,c)\mapsto(A_4n,c),\qquad
5:(n,c)\mapsto(A_5n,c\mathbin{\oplus}1).
\tag{19.4}
$$

请求 $f$ 的完整标签为 $(\sigma,d)$，$\sigma\in\{+1,-1\}$、$d\in\{0,1\}$，概率为

$$
p((n,c);f,\sigma,d)
=\mathbf1_{\{d=c\oplus\chi(f)\}}\,
 \frac{1+\sigma\,e_z\cdot A_fn}{2},
\tag{19.5}
$$

其中 $\chi(f)$ 为字中地址 $5$ 次数的奇偶。其余标签可作为零标签保留。$4^9,5^9$ 仍是真正的正字逆：后者九次翻转记录一次，再与原调用配对恢复记录。插入 $t=4$ 不改变任何记录值，四项中的记录因子完全相同，方向部分满足 (17.7)，故每个完整标签都满足 (17.6)。

但是 $\epsilon$ 与 $5$ 在此初始条件有相同方向 $u$，记录分别为零、一；读取 $d$ 就区分它们。因此 (17.4) 失败，不能只把 $d$ 求和后宣布其为全未来 qubit。这个模型的完整容量实际上是八：控制旋转的偶 $5$ 子群在生成群中指数至多二；其闭包是连通 $SO(3)$ 的指数至多二闭子群，故仍为 $SO(3)$，奇陪集也稠密。两种记录扇区各有稠密球面，完整后接效果分别张成一个常数加三个方向坐标，给两个四维直和。此证明也说明为何“全标签四时关系”不能替代“全未来方向充分性”。

**(d) 只保留单轴检查的混叠。** 若只有绕 $e_z$ 的 $t$ 及其幂，连续函数

$$
F(n)=\frac12+\varepsilon\operatorname{Re}(n_x+in_y)^{11},
\qquad 0<\varepsilon\le\frac12
\tag{19.6}
$$

及其补事件处处正归一、非仿射，却通过这一单轴的全部四时检查：权 $\pm11$ 在十阶旋转下与权 $\pm1$ 有相同特征值。此项删除的是满旋转前后文供应，不声称满足 (17.3)，也不声称单轴实际轨道有 11 维容量。它只表明为何要在整个不可约模中检查权二，不能用一个轴的频率别名推出全球面仿射性。∎

三个删除方向相互独立地指出需要保留的东西：实三维不消灭非线性高阶响应；四时关系不消灭可见的额外记录；单轴四时关系不排除旋转混叠。因而 (17.6) 不是把“容量四”换名，而是在保留其余明示几何与全未来前件后，具有可被精确反模型区分的选择内容。

## 20. 来源对应、量子接口与未解的原生起源

### 定义 20.1（已覆盖步骤与本节的源相对增量）

本节不新增 trine、Gleason、紧群或 qubit 分类定理。文献中间工具与仓内已有结论的参数对应如下；“未覆盖”仅指这里列明的既有正文接口，不主张研究史原创或穷尽检索。

| 来源与定位 | 已有且本节直接消费的内容 | 本节区别及未借入的前件 |
|---|---|---|
| Caves–Fuchs–Manne–Renes, *Gleason-Type Derivations of the Quantum Probability Rule for Generalized Measurements*, [quant-ph/0306179v1](https://arxiv.org/html/quant-ph/0306179v1)，§IV.1 式 (11)–(20)、§IV.2.1 式 (22) | 连续球面函数的调和分解、$SO(3)$ 不可约模及旋转正交性；原文 trine 权重条件已导出一次仿射性 | 本节把其 $\ell,m$ 模工具用于实际四时多项式 $R$，不是重证 trine 规则，也不假设原生菜单能任取 trine 测量 |
| [DLMF §14.30](https://dlmf.nist.gov/14.30)，式 14.30.1、14.30.8 | $Y_{\ell m}$ 的方位因子 $e^{im\phi}$ 及正交性；这里每个 $\ell\ge2$ 取 $m=2$ | 不由一次轴旋转的最高权得出全模结论；连续函数的无限展开由有界投影处理 |
| [V24](AURIC_TWO_BASIS_STATES_THREE_CHANNELS_PHASE_CHIRALITY_AND_RECURSIVE_SQUARE_LAW_V24.md) §6.4、引理 7.2、定理 7.3；[相干重建续卷 II](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md) §§85–86 | 已有 trine 刚性、黄金四时系数、多项式筛选及十三维复射影条件 Born 结论 | 原定理先给 $\mathbb P(\mathbb C^{13})$、门矩阵及相应射影作用；本节先给实 $S(W)$ 与可能非线性响应，从实际全未来关系导出共同实容量，没有再发表一个复射影筛选结论 |
| [V48](AURIC_ISOTROPY_CHIRALITY_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V48.md) 定理 6.3、§7.3、命题 7.4、§7.5 | $SU(2)/SO(3)$、仿射球的校准、立方反例、Pauli 状态/效果接口 | 只在定理 17.4 已经导出仿射性后使用 qubit 表示；(19.3) 是此反例接到实际全未来控制域的秩计算 |
| 本卷 §16，特别是定理 16.4、命题 16.7、定义 16.8–16.9 | 四维载体给定后的有序几何、紧三维群步骤、原局部角与七地址反例、锥饱和及相位边界 | (17.9) 补其容量输入；(18.1)–(18.2) 验证局部旋转密度，未用全局密度顶替局部证明 |
| [C113](AURIC_INTERNAL_BALANCED_CALIBRATION_AND_FILTER_COMPOSITION_GEOMETRY_C113.md) §§32–35 | 任意小校准缺陷下选定有限表的五维下界 | 不是准确全未来维数五或有限精度证书；它阻止用近似关系冒充 (17.6) 及准确容量四 |
| Galley–Masanes, *Classification of all alternatives to the Born rule in terms of informational properties*, [1610.04859v3](https://arxiv.org/html/1610.04859v3)，Result 2、附录 A.2 | 对给定复纯态及有限表示的替代概率理论分类背景 | 本节不借入其复射线或有限预测表示前件；非有限展开在 (17.13) 后才被排除 |
| Freedman–Larsen–Wang, *The two-eigenvalue problem and density of Jones representation of braid groups*, [math/0103200v1](https://arxiv.org/html/math/0103200v1)，Theorem 0.1、§2 | 已有原十三维全局密度的文献工具，归续卷 II 的既有使用 | 不推出原局部两门的实 $SO(3)$ 密度；本节以原地址实旋转及无限阶字单独验证该项 |

本节的源相对综合是：在不先有复射影载体的局部实方向模型中，把**原标签、原质量、原未来**的黄金四时关系通过旋转模筛选接到完整行空间，先推出其容量，再接已有仿射球量子接口；并在原地址上定位该模型所需的真实旋转供应及不能隐藏的记录检验。先验实三维具有实质限制，但它没有预先限制响应的调和阶数或行秩；命题 19.1(b) 的 11 维模型使这一点可检查。该综合标为 repo-derived 条件应用，未取得文献原创优先权。

### 定义 20.2（所导出的量子公理接口与仍未供应的内容）

| 项目 | 在明示前件下导出的内容 | 仍未供应 |
|---|---|---|
| 状态与概率 | 局部完整行的共同 $\mathbb R\oplus W$ 表示；非退化容量四；最小预测完成为球；(17.15)–(17.16) 的精确 qubit 表示 | 原源全部未来的 (17.4)、(17.6)；球内任意实际准备、全效果菜单及更大兼容锥的唯一性 |
| 事件和分支质量 | 每个原标签的正效果、原事件加和、原失败/零质量均保持 | 实际后选择装置、零分支的归一态；不可将原始质量抛弃 |
| 可逆操作 | 已有局部确定性控制的旋转及数学幺正共轭代表，实际正字逆按原资源保留 | 由闭包产生的新实际门；任意幺正控制、反射的原生合法性 |
| 更新与过程 | 给定前缀后全部原终端请求的概率，无末端信息损失 | 每个读后分支成为本地合法前缀的闭合、Markov 后继、Lüders/平方根更新、原仪器的 CP 性及所有扩张输入上的完全正性 |
| 复合与相位 | 一份局部复二分量数学表示；整体号的通道等价 | 独立准备、张量复合、局部层析、共同复中心、可控相干路由及内部相对相位参考；数学自旋提升不供应这些资源 |
| 时间与谱 | 原有限门词及其离散旋转谱可在表示中讨论 | 物理连续时间、Hamiltonian、能量、$\hbar$，以及预测/信息谱与物理能谱的共同实现对应 |

(17.6) 不设读后态，因此无法只凭这些终端恒等式把每个原测量仪器认成 qubit CP 仪器。即使某份数学量子仪器能产生相同终端概率，其存在也不等于已识别原来每条分支的实际更新与合法继续。要扩域，须重新证明扩域的共同未来充分性与每个资源前件，不能将这里的局部四维提升到所有历史或全局 $\omega$。

[C123–C127 所在卷](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md) §§35–40 的界限保持原义：改变另名 $D$ 的同过程反模型阻止仅从过程识别那个 $D$，不阻止量子过程实现的存在；全签名重构须准确保留原来指定的 $D$。本节不增加辅助 $D$ 唯一性的完成要求，也不从局部旋转自动补出 C115 的有向结合乘法。存在量子预测实现、识别原生量及保留另名关系是三个须按各自前件处理的目标。

“所有量都是预测的量”“关系也可能不确定”“信息守恒”及两种谱的直觉仍是研究输入。这里的实际定义只确定终端预测行及其控制作用，未指定一个已验证的守恒信息泛函，也未识别两种谱。若关系本身含不确定性，必须说明其共同历史、联合律、可问事件及与 (17.1) 的连接；只加一个随机关系名称不会供应定理前件。明确这些接口并取得实际原生挂接、更新、复合、相干相位及时间，仍是完整量子起源任务的未解部分；本节只完成所声明的条件桥。

## 追加锚（本行以下为增补区）
