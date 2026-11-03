# 相对锚、交换原子与关系场论

从二元各向同性到整体圆、局部椭圆与闭环曲率

**AURIC v87：一个完整候选及其理论接续**

项目连续研究稿

2026 年 11 月 2 日

## 摘要

本轮承接 v86，将 $\Omega$ 的参考角色与整体本身分开：任何可用内部态都可被选作锚，但单个锚态不自动给出完整坐标框、理想时钟或无限可复用的量子程序。同一过程的被动换表示保持关系读数；真正更换相互作用伙伴或参照协议，则可以改变相对运动。

只新增一个候选 $C_{87}$：两个同类完整量子端口的最简二元作用，在没有额外方向背景时，与二者的任意共同酉改向相容。在继承的完整自伴生成元接口上，这恰好等价于 $K=aI+b\mathsf S$，其中 $\mathsf S$ 是交换算子。给出有限代数证明及删去条件后的反例，不将这一经典交换子分类宣称为新数学发现。

未知锚作为真实量子输入保留后，部分交换使两端同时变化并产生纠缠。对纯产品初态，完整联合射线在一个二复维子空间的 Bloch 球上绕圆；单端约化态的 Bloch 向量则精确走椭圆，半轴由两态重叠决定。圆的周期、局部混合和椭圆由同一个二元原子推出。三态闭环不变量、两关系的不相容及不确定性，又统一为一个 Gram 行列式恒等式。

将实际延续与内部参照延续写成两条连接，它们的差给出无外部静止锚的相对生成元；内部展开后的整条轨迹在换锚时只差常量酉变换。不同延续次序的剩余作用给曲率，变化子空间的补向比较给诱导曲率。最后构造有限交换网络，逐项接回既有量子规则，并明确哪些条件还不足以选择引力或标准模型。

全部数学论证为解析证明；未运行数学程序、数值实验或候选枚举。

## 目录

- [1. 版本位置与本轮真正的增量](#section-1)
- [2. 定义：相对锚、完整参照与各向同性](#section-2)
- [3. 唯一新候选 C87：完整二元作用的共同各向同性](#section-3)
- [4. 定理：整体圆与局部椭圆来自同一个交换原子](#section-4)
- [5. 固定锚场怎样出现：一阶响应、资源与项目接口](#section-5)
- [6. 反着推：删去哪个条件，会留下什么模型](#section-6)
- [7. 关系也有关系：不确定性与二元正核的三维提升](#section-7)
- [8. 三态闭环：相位、不相容与 Gram 行列式是同一约束](#section-8)
- [9. 无外部方向的关系不相容：三个端口的解析例子](#section-9)
- [10. 移动锚：两条内部延续的差就是相对生成元](#section-10)
- [11. 定理：同一参照历史换锚后，整条轨迹性质保持](#section-11)
- [12. 关系场：输运、闭环与补向曲率](#section-12)
- [13. 一个完整有限模型：内部交换网络与守恒](#section-13)
- [14. 怎样接回现有量子力学：依赖、定义与证明](#section-14)
- [15. 统一场论的确切进度：已闭合什么，还须锁定什么](#section-15)
- [来源与版本关系](#references)

<a id="section-1"></a>

## 1. 版本位置与本轮真正的增量

本轮记为 v87，承接已交付 v86 的共同场定理，以及 v84 的完整相干执行、v85 的内部能量闭合。项目核验使用固定提交

`c63ab162315fddd0801cbe9f47dbf3eda6e13360`。

本轮有界实时读取未取得当前 HEAD，因此不认证该基线之后的仓库变更。核读范围为本地已有 16 份该基线 Markdown 中的相关章节；不作全仓库唯一性或文献优先权声明。

V74 已给出共同 Gram 框到酉族、水平相位、曲率及移动内部参照的生成元；$\Omega$ 静态纤维稿已保留非平凡闭环和路径记忆。这些结果是本轮的起点 [1](#ref-v74)–[2](#ref-static)。v86 的关键式是：同一完整纯态方向表满足

$$
\operatorname{tr}\bigl(X(P)R+PX(R)\bigr)=0\quad\text{对全部秩一 }P,R,
$$

则必存在共同自伴 $H$，使 $X(P)=-i[H,P]/\hbar$，唯一到标量。本轮继续问：**把伙伴本身也保留为量子输入，再排除未声明的绝对方向，最简二体作用是什么？**

本文沿用共同复正核、效果概率标定、独立准备的积核、内部记录和原生执行合同。新的 $C_{87}$ 不重新假装这些已讨论结构都由“相对”一词单独推出。其结论是一个可自足计算的**有限关系量子模型**与规范几何框架。从该框架进一步选择电磁、弱、强和引力的实际动力学，仍需明确而可检验的关系条件。

**白话图景。**这次的推进是把“谁是锚”也放进过程：锚是整体里参与比较的内容，不是最后一个绝对态。两边一起换朝向，最简单的作用不应暗中认得某根外部轴。把这句话写成精确约束后，能推出一种完整的二元作用，并同时解释整体的圆和局部的椭圆。

<a id="section-2"></a>

## 2. 定义：相对锚、完整参照与各向同性

约定内积第二变量线性。当前有限比较载体为 $\mathcal H\simeq\mathbb C^d$；整体关系对象记为 $\mathfrak R$，选定内部锚的记号为 $\Omega_a$。这仅区分两个角色，不增添整体之外的对象，也不要求 $\mathfrak R$ 有限维。

### 定义 2.1（锚与参照协议）

锚态 $a$ 指定一次比较的起点。完整参照协议还指定可比较的方向、相干相位、内部时钟及跨事件的延续规则。只有这些数据足以支撑实际读出时，才称为一个完整参考框。

### 命题 2.2（纯锚无特权，但不唯一地给出整框）

同一有限载体上任意两个归一纯态 $a,b$ 都存在酉 $g$ 使 $ga=b$。该选择一般不唯一：固定向量 $a$ 的稳定子含 $U(d-1)$，固定射线的稳定子为 $U(1)\times U(d-1)$。

**证明。**将 $a,b$ 分别补成正交基，记相应酉矩阵为 $A,B$，则 $g=BA^\dagger$。在 $a^\perp$ 上任取酉变换仍固定 $a$；若只固定射线，还可独立改变 $a$ 的相位。

混态也可用作物理参照，但不同谱的混态不由酉变换互达。例如纯态和 $I/d$ 的 $\operatorname{tr}\rho^2$ 不同。因此“任何态可被选为锚”不等于“任何锚拥有相同的参照资源”。在单个纯锚图上，

$$
z=\frac{(I-P_a)\psi}{\langle a,\psi\rangle}
$$

仅对 $\langle a,\psi\rangle\ne0$ 定义；遇到正交超平面须换图，而非宣布物理态消失。

### 定义 2.3（三种不同的关系要求）

被动协变是同一过程全部数据共同改写后，读数保持；物理各向同性是在指定作用没有额外方向背景时，共同主动改向仍使用同一种作用；更换实际伙伴或参照协议，则是另一个关系配置。

例如

$$
\operatorname{tr}(\rho E)=\operatorname{tr}(g\rho g^\dagger\,gEg^\dagger)
$$

是被动表示一致性。任意给定 Hamiltonian 都可以如此改写，因此它单独不限制 Hamiltonian 的形式。$C_{87}$ 将进一步限制最简同类二元作用。这里的群是内部 $U(d)$，不自动等于物理空间的 $SO(3)$；量子比特的共同酉作用才有熟悉的 Bloch 球转动图像。

### 定理 2.4（单态无背景场只能为零）

设 $X(P)$ 为纯态投影切向，即 $X=X^\dagger$、$PX+XP=X$。若

$$
X(gPg^\dagger)=gX(P)g^\dagger
\quad\text{对全部 }g\in U(d)
$$

成立，则 $X(P)=0$。

**证明。**取 $J=2P-I$。它固定 $P$，而切向仅有 $P$ 与 $I-P$ 之间的交叉块，所以 $JX(P)J=-X(P)$。协变又要求 $JX(P)J=X(P)$，故为零。

**白话图景。**一个点若没有伙伴、没有历史方向，又要求所有方向一样，就没有理由向任何一边走。运动方向可以来自另一个内部态，或来自内部保存的历史和控制。大家一起改写坐标时关系保持；真的换了伙伴，关系本身就可能改变。

<a id="section-3"></a>

## 3. 唯一新候选 C87：完整二元作用的共同各向同性

本节的两个端口可区分，但载体同型，均为 $\mathcal H$。“同类”并不要求其未知输入态相同，也不要求能克隆一个未知态。完整载体为 $\mathcal H\otimes\mathcal H$，不是先取系统边际再假定锚不动。继承 v86 的共同场与相干提升，完整自治原子已有自伴生成元 $K$。

### 定义 3.1（候选 C87）

若一个完整二端口原子只比较两个同类端口，没有未声明的第三个方向背景，则共同酉改向与该原子可交换：

$$
\boxed{[K,g\otimes g]=0\qquad\forall g\in U(d).}
\tag{$C_{87}$}
$$

等价地，其完整门 $U_t=e^{-itK/\hbar}$ 对所有 $t$ 都与 $g\otimes g$ 对易。若原子强度随同一个内部钟变化，可逐时应用此条件。

这是本轮唯一新增的模型选择条件。它强于被动协变。其“原子”指这里声明的最简二端口作用类型，并不声称存在不可分割的最短时间或最小门角。量词中的 $g$ 比较的是同一个固定二体作用下两端的共同改向；这是结构对称性要求，不授予执行任意 $g$ 门的权限。额外能量结构、背景张量或第三伙伴存在时，应进入完整接口，不能暗藏在“仅两个端口”的定义里。

### 定理 3.2（完整二元原子的分类）

当 $d\ge2$ 时，$C_{87}$ 当且仅当

$$
\boxed{K=aI+b\mathsf S,qquad a,b\in\mathbb R,qquad
\mathsf S(u\otimes v)=v\otimes u.}
$$

两个实系数唯一。$d=1$ 时 $\mathsf S=I$，仅剩标量，系数分解不唯一。

**证明。**固定正交基 $e_1,\ldots,e_d$，将 $e_i\otimes e_j$ 写为 $\ket{ij}$。

第一步，令 $g$ 为任意对角相位矩阵。$\ket{ij}$ 的共同相位权重是 $e^{i(\theta_i+\theta_j)}$。对所有独立 $\theta_i$ 比较，$K$ 只能保持每个 $\operatorname{Span}\{\ket{ii}\}$ 和每个 $\operatorname{Span}\{\ket{ij},\ket{ji}\}$（$i\ne j$）。

第二步，共同基置换使所有单维块为同一实数 $a_0$，所有不同指标对的二维块相同。再用交换 $i,j$ 的置换及自伴性，二维块必须是

$$
\begin{pmatrix}b_0&c_0\\c_0&b_0\end{pmatrix},qquad b_0,c_0\in\mathbb R.
$$

第三步，取酉矩阵将 $e_i$ 送到 $e_+=(e_i+e_j)/\sqrt2$。$K\ket{ii}=a_0\ket{ii}$ 与共同改向相容，故 $K(e_+\otimes e_+)=a_0(e_+\otimes e_+)$。比较其中 $\ket{ij}+\ket{ji}$ 的系数，得到 $a_0=b_0+c_0$。因此 $K=b_0I+c_0\mathsf S$。

反向由交换定义直接有 $\mathsf S(g\otimes g)=(g\otimes g)\mathsf S$。当 $d\ge2$，$I,\mathsf S$ 线性无关，系数唯一。

这属于二重张量的 Schur–Weyl 交换子结构；上述证明自足。项目增量是将它与内部未知锚、实际完整门及后续读出相接，而非数学首创。$C_{87}$ 允许 $b=0$，也不决定 $b$ 的符号、数值、$\hbar$ 或物理时长。共同标量 $a$ 在射线层不可见，在完整相干路径比较中仍须保留。

对 qubit，直接在四条积基上核对得

$$
\mathsf S=\frac12\left(I+\sigma_x\otimes\sigma_x+
\sigma_y\otimes\sigma_y+\sigma_z\otimes\sigma_z\right).
$$

故该原子是各向同性自旋交换的熟悉形式。若把两个端口限制在一个全对称子空间，$\mathsf S=I$；只保留那个子空间时仅剩共同相位，无非平凡射影运动。

**白话图景。**两个同类端口之间，最简单的作用不能记住外部的“上、下、左、右”。它能够区分的，是两份内容保持原位，还是互换位置。连续作用把这两种可能相干地接起来，于是得到部分交换；锚与当前态都在作用里面。

<a id="section-4"></a>

## 4. 定理：整体圆与局部椭圆来自同一个交换原子

令 $\theta=bt/\hbar$、$c=\cos\theta$、$s=\sin\theta$。由 $\mathsf S^2=I$，

$$
U_t=e^{-iat/\hbar}(cI-is\mathsf S).
$$

本节计算密度矩阵和射线时共同相位抵消；并未抹去实际相干门的这个因子。部分交换与两端约化公式在量子同质化研究中已有明确原型 [5](#ref-ziman)。

### 定理 4.1（完整演化与两端反作用）

对明确供应的初始产品态 $\rho\otimes R$，其中两者为任意密度矩阵，

$$
\begin{aligned}
\rho_1(t)&=c^2\rho+s^2R-ics[R,\rho],\\
\rho_2(t)&=s^2\rho+c^2R+ics[R,\rho].
\end{aligned}
$$

特别地，$\rho_1(t)+\rho_2(t)=\rho+R$。

**证明。**展开 $(cI-is\mathsf S)(\rho\otimes R)(cI+is\mathsf S)$。由交换定义，$\mathsf S(A\otimes B)\mathsf S=B\otimes A$，并有

$$
\operatorname{tr}_2[(A\otimes B)\mathsf S]=AB,
\qquad
\operatorname{tr}_2[\mathsf S(A\otimes B)]=BA.
$$

分别对两端取迹即得。完整联合输入若原已相关，仍用完整酉式，不能沿用产品态简式。

### 定理 4.2（纯产品轨迹的有限三维圆）

设 $P=\ket\psi\bra\psi$、$R=\ket r\bra r$，令 $p=\operatorname{tr}(PR)=|\langle\psi,r\rangle|^2$。当 $p<1$ 时，完整轨迹位于一个二复维子空间。在该子空间的标准 Bloch 表示中，

$$
\boxed{
 n(t)=\left(\sqrt{1-p^2}\cos2\theta,
\sqrt{1-p^2}\sin2\theta,
 p\right).
}
$$

**证明。**记 $u=\psi\otimes r$、$v=r\otimes\psi$，则 $\langle u,v\rangle=p$。因此

$$
e_+=\frac{u+v}{\sqrt{2(1+p)}},
\qquad
e_- =\frac{u-v}{\sqrt{2(1-p)}}
$$

为正交归一的交换特征向量，特征值分别为 $+1,-1$。且

$$
u=\sqrt{\frac{1+p}{2}}e_++\sqrt{\frac{1-p}{2}}e_-.
$$

演化将两系数分别乘 $e^{-i\theta}$、$e^{i\theta}$。写二阶密度矩阵为 $(I+n\cdot\sigma)/2$，即得所列轨迹。

若 $b\ne0$ 且 $p<1$，射线周期为 $\pi\hbar/|b|$。仅 $p=0$ 时该圆是大圆，即此 $\mathbb CP^1$ 的测地线；$0<p<1$ 是纬圈。$p=1$ 时初始联合态为交换本征态，射线不动。在 $d\ge2$ 的完整二端口载体上，相干门返回恒等还须同时满足

$$
(a+b)T/\hbar\in2\pi\mathbb Z,
\qquad
(a-b)T/\hbar\in2\pi\mathbb Z,
$$

不能从射线周期推断原生十调用闭环或全部幅度周期。

### 定理 4.3（qubit 的单端椭圆）

令纯态 $P,R$ 的 Bloch 单位向量分别为 $r,s$，于是 $p=(1+r\cdot s)/2$。第一端的精确 Bloch 轨迹为

$$
\boxed{
 r_1(t)=\frac{r+s}{2}+\frac{r-s}{2}\cos2\theta
+\frac{s\times r}{2}\sin2\theta.
}
$$

当 $0<p<1$ 且 $b\ne0$ 时它为椭圆，两半轴分别为

$$
\boxed{A=\sqrt{1-p},\qquad B=\sqrt{p(1-p)}.}
$$

因此 $B/A=\sqrt p$：形状由同一二元重叠决定，没有另加独立形状参数。$p=0$ 时退化为线段；$p=1$ 或 $b=0$ 时实际轨迹为点。若只执行有限角度区间，得到相应椭圆弧。

**证明。**Pauli 乘法给 $[R,P]=(i/2)(s\times r)\cdot\sigma$。将其代入定理 4.1，使用 $c^2=(1+\cos2\theta)/2$、$cs=\sin2\theta/2$，即得轨迹式。两个轴向量 $(r-s)/2$ 与 $(s\times r)/2$ 正交，长度为所列 $A,B$。椭圆中心 $(r+s)/2$ 与两轴都正交。进一步直接平方得

$$
|r_1(t)|^2=1-(1-p)^2\sin^2 2\theta.
$$

所以除两端纯态触点外，非退化椭圆位于 Bloch 球内部。

对任意 $d$ 的纯产品输入，局部约化态始终支持在 $\operatorname{Span}_\mathbb C\{\psi,r\}$ 中；在该有效二复维片内，上述椭圆公式同样成立。同一计算给

$$
\boxed{\operatorname{tr}\rho_1(t)^2=1-2c^2s^2(1-p)^2.}
$$

这可由该二阶 Bloch 范数与 $\operatorname{tr}\rho^2=(1+|r|^2)/2$ 证明；$p=1$ 单独为纯态。当纯度小于一时，完整联合纯态已纠缠。所以完整圆到局部椭圆的原因是内部约化及反作用。不同 Hamiltonian 的一般高维轨迹并不都为圆；本节的圆来自两点谱 $a\pm b$。

```text
完整联合射线：球上纬圆          单端约化态：平面椭圆
        n3                                  B
        ↑                                   ↑
      --o--  高度 p                       --o--
    /       \                           /       \
   圆半径 √(1-p²)                      A       A
```

**白话图景。**把两个态连同锚一起看，它们以固定的相对节奏交换内容，完整关系绕一个圆。只看其中一边，另一边仍保存着部分内容和相干关系，于是这一边在球里面走椭圆。这里没有把信息扔到整体外面；局部看不见的部分保存在两边的关联中。周期来自同一个相位差反复走满一圈，具体转多快还要内部时钟与耦合来标定。

<a id="section-5"></a>

## 5. 固定锚场怎样出现：一阶响应、资源与项目接口

式（4.1）在 $t=0$ 给

$$
\boxed{\dot\rho_1(0)=-\frac{ib}{\hbar}[R,\rho].}
$$

当前态与伙伴态的对易关系给出初始切向；伙伴并不因此永远固定。若 $P\perp R$，则初始切向为零，但

$$
\rho_1(t)=P+\sin^2(bt/\hbar)(R-P),
\qquad
\ddot\rho_1(0)=2(b/\hbar)^2(R-P).
$$

因此单端的一根切向不足以确定完整过程，更不能把它当作闭合系统的全部历史。

### 命题 5.1（已校准纯伙伴场的分类，作为附属接口）

另考虑已由 v86 认证的全输入场族 $X_R(P)=-i[H_R,P]/\hbar$，其中 $R$ 为秩一投影。若接口只有 $(P,R)$，并且该场族联合协变，则唯一无迹代表为

$$
H_R=\lambda(R-I/d),
\qquad \lambda\in\mathbb R\text{ 对所有纯 }R\text{ 相同}.
$$

**证明。**联合协变使 $H_{gRg^\dagger}-gH_Rg^\dagger$ 与全部纯投影对易，故为标量；无迹消去标量。固定 $R$ 的 $U(1)\times U(d-1)$ 稳定子使交叉块为零、补块为标量，故 $H_R=\alpha R+\beta(I-R)$。无迹与纯投影轨道的传递性即给结论。

这个附属命题说明已校准方向场的形式；它不是本轮第二条新公理，也不是用一份未知量子态无扰动地实现任意 $e^{-i\theta R}$ 的保证。例如若同一处理器对全部 $\psi$ 满足

$$
W(\psi\otimes r)=U_r\psi\otimes r,
$$

对非正交 $r,s$ 比较完整内积便得 $U_r^\dagger U_s=I$。不同非正交程序一般不能在这种精确无扰动合同下调用不同门。更一般的完整程序边界沿用 v86。

### 命题 5.2（新准备伙伴的连续弱作用极限）

若确实供应 $n$ 份独立准备的相同纯态 $R$，每份新伙伴在接入前都与当前完整历史独立，每次使用一份新伙伴，以角度 $\theta/n$ 做部分交换，则系统通道在 $n\to\infty$ 时趋于

$$
\rho\longmapsto e^{-i\theta R}\rho e^{i\theta R}.
$$

**证明。**令 $Q=I-R$、$c_n=\cos(\theta/n)$。逐次应用式（4.1）给

$$
Q\rho Q\longmapsto c_n^{2n}Q\rho Q,
\qquad
R\rho Q\longmapsto c_n^ne^{-i\theta}R\rho Q.
$$

$Q$ 块损失的迹进入一维 $R$ 块；另一个交叉块取伴随。由 $\log\cos x=-x^2/2+O(x^4)$，有 $c_n^{2n},c_n^n\to1$，极限正是所列投影相位门。

这与密度矩阵指数化的多副本思想相接 [6](#ref-lloyd)。新伙伴、独立准备及可调弱脉冲都是资源条件；不从一份未知锚免费复制，也不自动属于项目原生菜单。

项目 FIB 续卷 V 定义 1.1 的固定脉冲数学内部演化为

$$
U_j(t)=e^{i\alpha t}\bigl[I+(e^{i\alpha t}-1)\mathcal P_j\bigr],
\qquad\alpha=3\pi/5,quad0\le t\le1.
$$

完整 $\mathcal P_j$ 一般高秩，局部 $Q$ 才为秩一投影。固定秩 $r$ 的同一稳定子论证给 $H_R=\lambda_r(R-rI/d)$，不同秩轨道不强迫同一 $\lambda_r$。因此项目门与已校准投影场有相同函数形式；其具体相位、整体因子、十调用恒等与允许的调用菜单仍来自原生定义。原文只允许完整正向单位脉冲，数学上的分数时刻不能改写成执行权限。

**白话图景。**“绕锚转”可以是完整交换过程的一阶图像，也可以在不断接入新准备伙伴的极限中成为有效门。这两种说法都能精确写清，但资源不同。一份未知锚不能既不断供给方向、又永远不变；把它的反作用和准备历史记回整体，理论才真正内生。

<a id="section-6"></a>

## 6. 反着推：删去哪个条件，会留下什么模型

| 删除或改写的条件 | 具体模型 | 后果 |
| --- | --- | --- |
| 只保留被动协变 | 任意 $K_0$ 随框架共轭改写 | 合法量子动力学仍成立，不能选出交换原子 |
| 只允许实正交共同改向 | $\ket\Phi=d^{-1/2}\sum_i\ket{ii}$，$K=\ket\Phi\bra\Phi$ | 对 $O(d)$ 不变，但一般不属于 $\operatorname{span}\{I,\mathsf S\}$ |
| 隐含第三个方向数据 | $K=Z\otimes Z$，只共同旋转输入不旋转 $Z$ | 强度与方向依赖未报告的背景 |
| 改为两端独立任意改向 | 与全部 $g\otimes h$ 对易 | 只剩标量，无非平凡相互作用 |
| 只保留单端初始切向 | $P\perp R$ 的部分交换 | 初始切向为零，二阶仍变化 |
| 将边际当完整纯态 | 式（4.5）的任一般时刻 | 漏掉混合、纠缠和伙伴反作用 |
| 把不变解释成处处不确定 | 取读口的本征态 | 该关系可以有严格零方差 |

第二行的证明是 $(O\otimes O)\Phi=\Phi$，而对一般复对角酉不成立。$\ket\Phi\bra\Phi$ 在维数至少三的对称子空间中仅为秩一，$aI+b\mathsf S$ 在整个对称子空间上是标量，二者不可能相同。这明确显示：$U(d)$ 的选择使用继承的共同复结构，不能由“看起来无方向”含糊替代。

第四行可分两步证明：与全部 $g\otimes I$ 对易先迫 $K=I\otimes B$，再与全部 $I\otimes h$ 对易迫 $B$ 为标量。二元关系允许相对方向存在；它排除共同绝对方向，不抹去两个端口之间的差别。

$C_{87}$ 也不因 $b=0$ 成为矛盾；零耦合是合法极限。用候选排除某模型，准确意思是它不属于所定义的最简同类二元作用，并非宣称所有不满足它的量子过程都不合法。

**白话图景。**反推的价值是找出条件真正管了什么。只说换坐标，几乎什么作用都能通过；把两端的相对方向也抹掉，又会把运动全部抹成零。有用的中间位置是：共同改向不改变作用，而两份内容之间的关系可以改变。

<a id="section-7"></a>

## 7. 关系也有关系：不确定性与二元正核的三维提升

对同一准备态 $\rho$ 上的自伴读口 $A,B$，记

$$
\delta A=A-\operatorname{tr}(\rho A)I,
\qquad
\delta B=B-\operatorname{tr}(\rho B)I.
$$

在 Hilbert–Schmidt 空间取 $u=\delta A\sqrt\rho$、$v=\delta B\sqrt\rho$，并写

$$
\Gamma=\begin{pmatrix}a&c\\\bar c&b\end{pmatrix},
$$

其中 $a=\operatorname{Var}_\rho(A)$、$b=\operatorname{Var}_\rho(B)$、$c=\operatorname{tr}(\rho\delta A\delta B)$。$\Gamma$ 就是这两个变化的共同 Gram 矩阵。

### 定理 7.1（关系读口的 Robertson–Schrödinger 约束）

$$
\boxed{
 ab\ge |c|^2
=\left(\frac12\langle\{\delta A,\delta B\}\rangle\right)^2
+\left(\frac1{2i}\langle[A,B]\rangle\right)^2.
}
$$

**证明。**任意 $z_1,z_2\in\mathbb C$ 有 $z^\dagger\Gamma z=\lVert z_1u+z_2v\rVert_{\rm HS}^2\ge0$，故 $ab-|c|^2\ge0$。$c$ 的实部为对称协方差，虚部为交换子均值，分解模方即得。

若两个读口已按声明单位无量纲化，且 $q=a+b>0$，则

$$
\frac\Gamma q=\frac{I+r_\Gamma\cdot\sigma}{2},
\qquad
r_\Gamma=\frac{(2\operatorname{Re}c,-2\operatorname{Im}c,a-b)}{a+b},
$$

$$
\boxed{|r_\Gamma|^2=1-\frac{4(ab-|c|^2)}{(a+b)^2}\le1.}
$$

这是二元读出关系的有限三维提升。$q=0$ 时两个方差与交叉项均为零，不作归一化。尺度 $q$ 与单位仍需保留；一张归一图并没有保存全部原始信息。更高维整体也不因此变成三维。

任意有限维 Hermitian 锐读口都有零方差本征态。所以“关系也测不准”的准确结论是：**不相容关系的共同锐化受到态依赖的约束**。$[A,B]\ne0$ 不保证每个态的乘积下界严格正；任取 $A$ 的本征态即可令方差乘积为零。这里是准备态上的读数方差，不直接等于仪器误差或测量扰动。有限维也不能满足 $[A,B]=i\hbar I$，因为两边取迹矛盾；归一三维图不推出最小绝对面积。

**白话图景。**关系不是没有误差的外部尺子，它本身也是一个读口。两个读口若使用同一部分内容，却要求不同的对齐方式，它们的波动就不能随意各自指定。这个限制来自同一个二元正核；某个关系仍可以完全确定，不必把一切都宣布成模糊。

<a id="section-8"></a>

## 8. 三态闭环：相位、不相容与 Gram 行列式是同一约束

令归一 $a,b,c$ 已位于同一比较载体；若原先处于不同事件，应先声明内部输运。定义

$$
x=|\langle a,b\rangle|^2,quad y=|\langle a,c\rangle|^2,quad z=|\langle b,c\rangle|^2,
\qquad \mathcal B=\langle a,b\rangle\langle b,c\rangle\langle c,a\rangle=\operatorname{tr}(P_aP_bP_c).
$$

$\mathcal B$ 是三次二元比较接成闭环的量；任意共同酉变换和各向量的独立相位选择都抵消。三态 Gram 矩阵 $G_3=(\langle a_i,a_j\rangle)$ 满足

$$
\boxed{\det G_3=1-x-y-z+2\operatorname{Re}\mathcal B\ge0.}
$$

若 $xyz>0$，令 $\mathcal B=\sqrt{xyz}e^{i\phi}$，便得

$$
\cos\phi\ge\frac{x+y+z-1}{2\sqrt{xyz}}.
$$

若 $\mathcal B=0$，相位不定义。

### 定理 8.1（闭环关系与不确定性的精确接合）

在态 $a$ 上取读口 $P_b,P_c$，则

$$
\begin{aligned}
\operatorname{Var}(P_b)&=x(1-x),&\operatorname{Var}(P_c)&=y(1-y),\\
\langle\delta P_b\delta P_c\rangle&=\mathcal B-xy,&
\frac1{2i}\langle[P_b,P_c]\rangle&=\operatorname{Im}\mathcal B.
\end{aligned}
$$

并有

$$
\boxed{\operatorname{Var}(P_b)\operatorname{Var}(P_c)-|\mathcal B-xy|^2=xy\det G_3\ge0.}
$$

**证明。**投影平方等于自身，故方差和交叉矩式直接成立。又 $|\mathcal B|^2=xyz$，展开左端得

$$
xy(1-x-y+xy)-xyz+2xy\operatorname{Re}\mathcal B-x^2y^2
=xy(1-x-y-z+2\operatorname{Re}\mathcal B).
$$

结合 Gram 行列式即得；含零重叠时同样成立。

对 qubit，Pauli 乘法还给

$$
\mathcal B=\frac{1+r_a\cdot r_b+r_b\cdot r_c+r_c\cdot r_a
+i\,r_a\cdot(r_b\times r_c)}4.
$$

取 $a=\ket0$、$b=(\ket0+\ket1)/\sqrt2$、$c=(\ket0+i\ket1)/\sqrt2$，则 $x=y=z=1/2$、$\mathcal B=(1+i)/4$。把三态一起复共轭，所有二元转移概率保持，$\operatorname{Im}\mathcal B$ 反号。因此只保留两两概率会漏掉闭环定向；共同酉各向同性不等于把反酉时间反演也当同一取向。

闭环量还可有完全内部的直接读口。令三个端口的循环排列为 $C\ket{x,y,z}=\ket{y,z,x}$，则

$$
\langle a,b,c|C|a,b,c\rangle=\mathcal B.
$$

$C$ 与共同 $g^{\otimes3}$ 对易；$(C+C^\dagger)/2$ 与 $(C-C^\dagger)/(2i)$ 分别读取实部和虚部。两者是同一正规算子的函数，彼此对易；不应把它们误写成互相不确定的读口。实际调用仍须供应相应排列及记录测量。

**白话图景。**两两比较告诉我们彼此有多接近；把三个比较连成环，还能知道绕行的方向和相位。这份闭环信息恰好也控制两个关系能否同时变得很锐利。因此“关系的关系”不是再添加一个神秘对象，而是已存在二元比较接合后留下的可读内容。

<a id="section-9"></a>

## 9. 无外部方向的关系不相容：三个端口的解析例子

取三个 qubit，定义完全内部的关系读口

$$
A=\mathsf S_{12},qquad B=\mathsf S_{23}.
$$

二者与任何共同 $g^{\otimes3}$ 对易，但一般彼此不对易。令 $\omega=e^{2\pi i/3}$，取

$$
\ket\Psi=\frac{\ket{100}+\omega\ket{010}+\omega^2\ket{001}}{\sqrt3}.
$$

在单激发三维空间中，$A$ 交换前两条基向量，$B$ 交换后两条。直接作用得

$$
AB\ket\Psi=\omega^2\ket\Psi,
\qquad
\langle A\rangle=\langle B\rangle=(1+\omega+\omega^2)/3=0.
$$

因 $A^2=B^2=I$，有

$$
\operatorname{Var}(A)=\operatorname{Var}(B)=1,
\quad\langle AB\rangle=-\frac12-\frac{i\sqrt3}{2},
\quad\langle[A,B]\rangle=-i\sqrt3.
$$

式（7.1）精确饱和为

$$
1=\left(-\frac12\right)^2+\left(-\frac{\sqrt3}{2}\right)^2.
$$

若定义三自旋手性 $\chi=\sigma_1\cdot(\sigma_2\times\sigma_3)$，由 Pauli 对易关系可得 $[A,B]=-i\chi/2$，故此态 $\langle\chi\rangle=2\sqrt3$。这份定向来自三个内部关系的顺序，并不选择外部空间轴。另一方面，在完全对称子空间内 $A=B=I$，两个关系可同时有零方差。

**白话图景。**先交换第一、第二份内容，再交换第二、第三份内容，与反过来做并不一样。这个差别只靠三个内部端口就能读出，没有借用外部方向。整体可以各向同性，内部关系仍然有顺序、手性和不相容。

<a id="section-10"></a>

## 10. 移动锚：两条内部延续的差就是相对生成元

以下是既有完整相干表示的几何接续，不增加第二条候选。在声明的内部比较参数域上，设同一个 Hermitian 丛有两条连接

$$
D^A=d+A,
\qquad D^B=d+B,
\qquad A^\dagger=-A,
\quad B^\dagger=-B.
$$

$A$ 描述实际延续，$B$ 描述内部参照怎样延续。基底参数可以是内部控制、记录和时钟；本节没有先将它认作物理时空。对共同局部换框 $\psi'=g\psi$，要求 $D'\psi'=gD\psi$，乘积法则唯一给

$$
A'=gAg^\dagger-dg\,g^\dagger,
\qquad
B'=gBg^\dagger-dg\,g^\dagger.
$$

这类时变参照修正与量子参考系文献的 Hamiltonian 变换相接 [7](#ref-qrf)；该文献也区分一般协变与保持具体动力学形式的对称性。

### 定理 10.1（相对生成元无须外部静止框）

设实际态满足 $D^A_t\psi=0$。令

$$
\boxed{C=A-B,qquad H_{A|B}=-i\hbar C_t.}
$$

则 $H_{A|B}$ 自伴，且

$$
\boxed{i\hbar D^B_t\psi=H_{A|B}\psi,qquad
H_{A|B}'=gH_{A|B}g^\dagger.}
$$

**证明。**两条连接变换式相减，非齐次项抵消，故 $C'=gCg^\dagger$。$C_t$ 反 Hermitian，所以 $-i\hbar C_t$ 自伴。$D^A_t\psi=0$ 给 $D^B_t\psi=-C_t\psi$，乘 $i\hbar$ 即得。

令 $P=\ket\psi\bra\psi$、$Q=I-P$。相对水平切向和速度为

$$
QD^B_t\psi=-\frac i\hbar(H_{A|B}-\langle H_{A|B}\rangle I)\psi,
\qquad
v_{\rm FS}=\frac{\Delta H_{A|B}}\hbar.
$$

该速度使用 $\lVert QD\psi\rVert$ 的 Fubini–Study 归一约定。共同换框时不变；真正把 $B$ 换成另一份物理参照协议时则可改变。特别地 $B=A$ 给零相对速度，表示参照与过程一起走，不代表所有内部关系都静止。

普通坐标导数不能替代协变导数。例如 $\psi(t)=e^{-it\sigma_y}\ket0$，选 $g(t)=e^{it\sigma_y}$ 可令 $\psi'=\ket0$。但原来静止的参照连接 $B=0$ 变成 $B'=-dg\,g^\dagger$，相对运动仍被记录。普通 Hamiltonian 的变换相应为

$$
H'=gHg^\dagger+i\hbar\dot g g^\dagger.
$$

$C_{87}$ 限制共同参照下的相互作用生成元；不能在时变坐标里漏掉参考项再照搬。

**白话图景。**当前过程有一套“接下来怎样走”，内部参照也有一套。两套规则相减，才得到相对于该参照的生成元。换表示时两边出现同一个修正，它们自动抵消，所以不需要再假设一根绝对静止的锚。

<a id="section-11"></a>

## 11. 定理：同一参照历史换锚后，整条轨迹性质保持

令 $T_B(t,s)$ 是沿同一内部路径的参照平行输运，满足

$$
\partial_tT_B(t,s)=-B_tT_B(t,s),
\qquad T_B(s,s)=I.
$$

定义将当前态拉回初始锚载体的内部展开

$$
\eta_0(t)=T_B(t,0)^\dagger\psi(t).
$$

### 定理 11.1（轨迹的锚不变性）

在同一物理参照协议 $B$ 下，任意共同局部换框给

$$
\boxed{\eta_0'(t)=g(0)\eta_0(t).}
$$

若仅把同一参照历史上的起点从 $0$ 改为 $s$，则

$$
\boxed{\eta_s(t)=T_B(s,0)\eta_0(t).}
$$

两个变换都与 $t$ 无关。因此整条射影曲线的 Fubini–Study 长度、在相应量有定义的正则光滑段上的内在曲率与测地性质，以及相同读口约定下的关系预测保持。

**证明。**输运方程的唯一性与连接变换式给

$$
T_B'(t,0)=g(t)T_B(t,0)g(0)^\dagger,
$$

代入展开式即得第一式。沿同一路径的合成给 $T_B(t,0)=T_B(t,s)T_B(s,0)$，即得第二式。常量酉变换保持内积及其诱导的射影度量，故整条曲线的相应内在几何保持。

此外直接微分得

$$
i\hbar\dot\eta_0=
\bigl(T_B(t,0)^\dagger H_{A|B}T_B(t,0)\bigr)\eta_0.
$$

这把相对 Schrödinger 形式写进一个完全内部选定的初始载体。任意非线性坐标投影的平面外观不在不变性结论之列；圆或椭圆的具体绘图形状须说明采用哪个等距表示或哪个约化读出。不同路径把锚接到一起时，可能留下闭环作用；下一节保留这份内容。

**白话图景。**沿同一套内部比较规则，把起点换到别处，等于把整条轨迹一起转一下，不会改掉它走了多远、怎样弯曲。如果改用另一套真实运动的参照，比较对象已经变了，相对速度就可能不同。前者是换锚的表示自由，后者是新的关系。

<a id="section-12"></a>

## 12. 关系场：输运、闭环与补向曲率

### 12.1 路径之间的关系

路径 $\gamma:x\to y$ 的完整输运 $T_\gamma$ 在换框后满足

$$
T_\gamma'=g_yT_\gamma g_x^\dagger.
$$

这也可由全部二元相干比较

$$
\langle g_yu,T_\gamma'g_xv\rangle=\langle u,T_\gamma v\rangle
$$

唯一恢复。对同端点路径 $\gamma,\zeta$，定义

$$
W_{\gamma,\zeta}=T_\gamma^\dagger T_\zeta,
\qquad W'=g_xWg_x^\dagger.
$$

回路共轭类及 $\operatorname{tr}(\rho W)$ 等相干读数不变。给定确实可执行的相干路径控制，干涉概率可为

$$
p_+=\frac12\left[1+\operatorname{Re}\left(e^{i\chi}
\langle\psi,T_\gamma^\dagger T_\zeta\psi\rangle\right)\right].
$$

因此一个对单态射线不可见的共同相位，也可能由两条实际路径的比较读出。

### 定义 12.2（关系曲率）

对 $D=d+A$ 定义

$$
\boxed{F_A=dA+A\wedge A,
\qquad (F_A)_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu+[A_\mu,A_\nu].}
$$

由 $[D_\mu,D_\nu]\psi=(F_A)_{\mu\nu}\psi$，曲率正是两种延续次序的差。共同换框给 $F_A'=gF_Ag^\dagger$。

按 $+\mu,+\nu,-\mu,-\nu$ 顺序走边长 $\epsilon,\delta$ 的小矩形，

$$
T_\square=I-\epsilon\delta(F_A)_{\mu\nu}
+O\bigl(\epsilon\delta(|\epsilon|+|\delta|)\bigr).
$$

符号由约定 $\dot T=-A_tT$ 固定；常系数情形的乘积为

$$
e^{\delta A_\nu}e^{\epsilon A_\mu}e^{-\delta A_\nu}e^{-\epsilon A_\mu}.
$$

有限非阿贝尔回路需要路径排序，不能直接替换成未排序的曲率积分指数。

相对连接差 $C=A-B$ 满足

$$
\boxed{F_A-F_B=D_BC+C\wedge C,
\qquad D_BC=dC+B\wedge C+C\wedge B.}
$$

这里两个交叉项都是加号。$C$ 按张量方式变换，不是独立连接。再由协变导数 Jacobi 恒等式得到 $D_AF_A=0$，即 Bianchi 恒等式。它是比较的相容恒等式，尚不是场的动力学方程。

### 定理 12.3（变化子空间的补向曲率）

先取环境连接为平坦的 $d$。令 $V(x)$ 为正交归一列框，$V^\dagger V=I_r$、$P=VV^\dagger$、$Q=I-P$。其诱导连接为 $A_V=V^\dagger dV$，则

$$
\boxed{F_V=dV^\dagger\,Q\wedge dV.}
$$

**证明。**$dA_V=dV^\dagger\wedge dV$。对 $V^\dagger V=I$ 微分给 $dV^\dagger V=-V^\dagger dV=-A_V$。因此 $dV^\dagger P\wedge dV=-A_V\wedge A_V$。把 $I=P+Q$ 插入即得。

在一般环境连接 $D^B=d+B$ 中，诱导连接为 $V^\dagger D^BV$，同一展开给

$$
F_V=V^\dagger F_BV+(D^BV)^\dagger Q\wedge D^BV.
$$

环境本身的曲率与保留子空间的补向贡献都在；不能在已有曲率背景中漏掉第一项。

回到平坦环境 $d$，秩一时 $V=\psi$，有

$$
(F_V)_{\mu\nu}=2i\operatorname{Im}\langle Q\partial_\mu\psi,Q\partial_\nu\psi\rangle.
$$

这将 v86 的补向切线与本轮“变化次序的剩余”直接接合。沿回路取周期归一框（或显式计入图间转移），写 $A_V=i\alpha$、$\alpha=-i\langle\psi,d\psi\rangle$，平行回路相位为 $e^{-i\oint\alpha}$；沿正向相邻态的重叠乘积，在细分极限中的相位为 $+\oint\alpha$（模 $2\pi$），两者方向约定相反。绝热非简并本征线上的这一几何结构与 Berry–Simon 相位相接 [8](#ref-simon)。

若完整框 $U$ 单值且 $A=U^\dagger dU$，则微分 $U^\dagger U=I$ 给 $dA=-A\wedge A$，所以 $F=0$。纯粹换坐标不制造曲率。完整平坦框中的变化子空间仍可有上述非零诱导曲率；那是保留子空间的比较规则发生了变化。局部 $F=0$ 也不排除非单连通域的全局 holonomy。

对 qubit 的无迹部分写 $A_\mu=-i\,a_\mu\cdot\sigma/2$，则

$$
(F_A)_{\mu\nu}=-\frac i2
\left(\partial_\mu a_\nu-\partial_\nu a_\mu+a_\mu\times a_\nu\right)\cdot\sigma.
$$

这是每个二态 $\mathfrak{su}(2)$ 片上的三个实分量；整体 $U(1)$ 相位另保留，任意高维 $U(d)$ 的全部关系场不能压成同一张三维图。

**白话图景。**场是一套把邻近比较接起来的规则。先沿一条关系走，再沿另一条走，若与反过来不一样，绕小圈后就留下一个可测的剩余作用，这就是曲率。在平坦环境中，变化子空间的这个剩余完全来自两根补向切线的共同关系；环境已有曲率时，还要把环境的那份作用一起保留。所以“补、动、动的变化”可以在同一结构中精确接合。

<a id="section-13"></a>

## 13. 一个完整有限模型：内部交换网络与守恒

为了使“关系场论”具有明确状态、演化和预测，定义如下有限模型，而不将网络结构本身伪装为已推出。给定内部端口集合 $V$、允许的二元边集合 $E$、同型载体 $\mathcal H$，以及实耦合记录 $b_{ij}$。这些是模型供应的内部结构数据；其具体来源与选择须由项目实际合同认证。令

$$
\boxed{\mathcal K=\mathcal H^{\otimes |V|},
\qquad
K_E=aI+\sum_{\{i,j\}\in E}b_{ij}\mathsf S_{ij}.}
$$

初态是 $\rho_0\ge0$、$\operatorname{tr}\rho_0=1$，可以含任意内部关联。完整自治演化为 $\rho(t)=e^{-itK_E/\hbar}\rho_0e^{itK_E/\hbar}$。内部记录的效果与条件更新采用继承的仪器接口，任一读数为 $p_e(t)=\operatorname{tr}(\rho(t)E_e)$。

### 定理 13.1（网络的封闭性与共同荷守恒）

模型保持正性、迹、完整纯度及共同 $U(d)$ 对称性。任意同类单端口自伴读口 $h$ 的总和

$$
G_h=\sum_i h_i
$$

与 $K_E$ 对易。重叠边的交换一般不对易，不相交边的交换对易。

**证明。**每个 $\mathsf S_{ij}$ 自伴，故 $K_E$ 自伴；酉共轭保持所列状态性质。共同 $g^{\otimes|V|}$ 与每个交换对易。交换 $i,j$ 仅将 $h_i+h_j$ 两项互换，不影响其他项，故总和守恒。不相交边作用于不同因子因而对易；$\mathsf S_{12}\mathsf S_{23}$ 与 $\mathsf S_{23}\mathsf S_{12}$ 在 $\ket{100}$ 上给不同结果，故重叠边一般不对易。

若 $h$ 是相同标定的局部物理能量，则可以取完整自治 Hamiltonian $H_{\rm tot}=G_h+K_E$。两项对易；相互作用绘景恰由 $K_E$ 生成。这保留相互作用能量，并接回 v85 的完整守恒。固定的非标量 $h$ 是额外内部结构；$H_{\rm tot}$ 不再具有固定 $h$ 下的全部共同 $U(d)$ 主动对称。总能量 $G_h$ 保持；其他加性读口是否保持，还须与这一自由项相容。

同维端口不自动意味着其真实能谱相同；对两端不同 $h_1,h_2$，

$$
[\mathsf S,h_1\otimes I+I\otimes h_2]=0
\quad\Longleftrightarrow\quad h_1-h_2\text{ 为标量}.
$$

证明是交换前后相减给 $D\otimes I=I\otimes D$，对一端取迹即迫 $D$ 标量。

对两个产品输入，定理 4.1 还给精确交换量。记 $E_\rho=\operatorname{tr}(h\rho)$、$E_R=\operatorname{tr}(hR)$、$C_h=-i\operatorname{tr}(h[R,\rho])\in\mathbb R$，则

$$
\Delta E_1=s^2(E_R-E_\rho)+csC_h,
\qquad
\Delta E_2=-\Delta E_1.
$$

一般网络上

$$
\frac{d}{dt}\langle h_i\rangle
=\frac{i}{\hbar}\sum_jb_{ij}\langle[\mathsf S_{ij},h_i]\rangle,
$$

相邻端口收到相反的边贡献；这是一条内部交换的连续方程。全局共轭各向同性不使局部能量总是相同，也不把计算程序本身等同于能量流入。

本模型给出明确的状态、完整门、局部约化、内部读口、守恒量和顺序效应。将多端口生成元写成两体项之和，是这里选定的组合模型，并非 $C_{87}$ 排除了所有更高体作用。例如 $i[\mathsf S_{12},\mathsf S_{23}]$ 也是自伴且共同 $U(d)$ 不变的三体生成元。它并未把任意门列为可执行：具体可用边、脉冲、程序和记录要由原生菜单供应。交换网络有很强的共同对称性；它本身也不自动成为任意整体量子门的通用控制集合。

### 13.1 逐端口换锚：边比较将交换原子接成关系场

现在允许每个端口使用自己的载体坐标 $\mathcal H_i$，并明确供应内部酉比较 $T_{ij}:\mathcal H_j\to\mathcal H_i$，反边为其伴随。边上的交换定义为

$$
\boxed{\mathsf S_{ij}(T)(u_i\otimes v_j)=T_{ij}v_j\otimes T_{ij}^\dagger u_i.}
$$

它先按内部比较将对方的内容送到本端口，再交换；$T_{ij}=I$ 时就是前面的原子。

### 命题 13.2（局域框架下的同一个交换关系）

$\mathsf S_{ij}(T)$ 自伴且平方为 $I$。若每端独立作不随内部时间改变的被动换框 $g_i$，并将同一边比较写成 $T_{ij}'=g_iT_{ij}g_j^\dagger$，则

$$
\mathsf S_{ij}(T')=(g_i\otimes g_j)\mathsf S_{ij}(T)(g_i\otimes g_j)^\dagger.
$$

因此 $\sum b_{ij}\mathsf S_{ij}(T)$ 与全部内部读口共同改写后，所有预测保持。

**证明。**式中映射作用两次即为恒等；它是酉映射，故自伴。在产品向量上代入 $T_{ij}'$ 并消去 $g_i^\dagger g_i$、$g_j^\dagger g_j$，即得变换式。产品向量张成联合载体，故为完整算子恒等式。

纯产品输入的重叠改写为 $p=\operatorname{tr}(P_iT_{ij}R_jT_{ij}^\dagger)$，它在这些独立换框下保持；圆、椭圆及纯度公式仍由同一 $p$ 决定。时变局域换框则使用前述参照连接与协变导数，保留移动框架项。

例如闭环 $W_1=T_{12}T_{23}T_{31}$ 从端口 1 出发并返回，满足 $W_1'=g_1W_1g_1^\dagger$。边上换锚的自由与闭环可读剩余因而同时保留。此处是带 $T$ 数据的被动局域协变，不是固定所有 $T$ 后对两端独立主动改向仍不变。$T$ 的来源、回路和动态都须声明，$C_{87}$ 没有自动供应任意边输运。若希望相应局部读口 $h_i$ 的总和守恒，一个充分的边相容条件为 $h_iT_{ij}=T_{ij}h_j$；一般有曲率的比较网络不能无条件继承所有同类加性荷守恒。

**白话图景。**可以把整体看作一张内部关系网：每条边只处理两端的交换，许多边共享端口。共享端口使作用次序有意义，也使局部内容能流动、纠缠并保存历史。若各端用同一能量尺度，流出一端的量进入另一端；改变轨道要追踪真实相互作用与资源。

<a id="section-14"></a>

## 14. 怎样接回现有量子力学：依赖、定义与证明

本节明确整条理论链。旧轮次已经讨论的共同复正核、概率标定和组合结构继续使用；$C_{87}$ 填的是**最简同类二体相互作用的选择**，不是用一个交换子方程替代全部旧前件。

| 现有规则 | 内部关系前件 | 结论 |
| --- | --- | --- |
| 复 Hilbert 态空间 | 共同复正核、零范数商、声明张成 | 态为共同关系实现中的向量或射线 |
| 共同酉运动 | 完整相干可逆性；v86 二态切向相容 | $X(P)=-i[H,P]/\hbar$ |
| Schrödinger 方程 | 共同自伴场、相干相位提升、内部钟 | $i\hbar\dot\psi=H\psi$ |
| 复合与纠缠 | 独立准备的积核、产品参照张成 | 张量积；一般态不必为产品 |
| 密度算子与 Born 效果 | 正、归一、可加的效果读数；既有强度标定 | $p(E)=\operatorname{tr}(\rho E)$ |
| 仪器与一般通道 | 完整门及显化记录，选择或忽略记录 | Kraus 形式与完全正性 |
| 理想投影更新 | 投影效果、范围内每个纯态不扰动 | 未归一 $P\rho P$ |
| 不确定性 | 同一正核上的两个偏差向量 | Robertson–Schrödinger 约束 |
| 关系相互作用 | 本轮唯一 $C_{87}$ | $K=aI+b\mathsf S$ 及内部反作用 |
| 相对生成元与曲率 | 内部输运、共同换框、路径合成 | 两连接差、闭环与诱导曲率 |

### 共同核如何给态空间

对内部准备标签 $x$ 的归一复核 $k(x,y)$，若每个有限 Gram 块正半定，则在形式和上定义

$$
\left\langle\sum_i c_i[x_i],\sum_jd_j[y_j]\right\rangle
=\sum_{ij}\bar c_i d_jk(x_i,y_j).
$$

正性使零范数向量与全部向量正交；商掉它们，有限秩切口便得有限维 Hilbert 空间。这使用共同复结构和全块正性。只知道两根正交向量，或每个二阶块单独能画进球内，并不足够。

### 共同场如何给时间演化

v86 由二态一阶相容推出共同自伴 $H$ 到标量。既有相干比较固定实际相位提升后，解 $\dot U=-iHU/\hbar$，由 $d(U^\dagger U)/dt=0$ 及 $U(0)=I$ 得 $U$ 酉。固定生成元给指数，时变内部控制给相应传播子。射影运动不能单独固定共同标量或时间尺度；这些由相位读口与内部钟标定。本轮 $C_{87}$ 进一步把最简二端口的 $H$ 限制成定理 3.2。

### 组合如何给张量积

若独立准备的积关系为

$$
k_{12}((x,y),(x',y'))=k_1(x,x')k_2(y,y'),
$$

映射 $[x,y]\mapsto[x]\otimes[y]$ 保全部 Gram，故延拓为等距。产品准备张成所声明复合载体时，该等距为酉同构。产品准备条件不等于所有联合态都可分；部分交换已提供明确纠缠态。

### 记录如何给效果、Born 形式与通道

对完整酉 $W$ 和内部记录初态 $\ket0$，取正交记录基 $\ket e$，令

$$
M_e=(I\otimes\bra e)W(I\otimes\ket0),
\qquad \sum_eM_e^\dagger M_e=I.
$$

由已建立的分支强度概率标定，

$$
p_e(\psi)=\lVert M_e\psi\rVert^2
=\langle\psi,E_e\psi\rangle,
\qquad E_e=M_e^\dagger M_e.
$$

忽略记录给 $\Phi(\rho)=\sum_eM_e\rho M_e^\dagger$。对任意辅助载体及任意 $X\ge0$，

$$
(\Phi\otimes I)(X)=\sum_e(M_e\otimes I)X(M_e^\dagger\otimes I)\ge0,
$$

故完全正；完备关系给保迹。结果条件态按相应分支归一；零概率分支不定义归一条件态。这明确使用既有概率语义，$C_{87}$ 本身没有额外推出随机读数解释。

### 效果读数如何给密度矩阵

若 $f$ 在全部效果 $0\le E\le I$ 上正、归一，且 $E+F\le I$ 时可加，则由单调性与有理分割先得实齐次性。对正算子 $A$，选正整数 $n\ge\lVert A\rVert$ 定义 $F(A)=nf(A/n)$，可加性保证与 $n$ 无关。延拓到 Hermitian 空间后，有限维迹配对给唯一 $\rho$，使 $F(A)=\operatorname{tr}(\rho A)$。正性和归一分别给 $\rho\ge0$、$\operatorname{tr}\rho=1$。

### 理想投影如何给 Lüders 更新

某结果效果为 $P$，其 Kraus 族满足 $\sum_\alpha A_\alpha^\dagger A_\alpha=P$。对 $\ker P$ 求范数和得 $A_\alpha=A_\alpha P$。若该结果固定 $\operatorname{ran}P$ 中每个纯态，则每个 $A_\alpha\psi$ 与 $\psi$ 共线；对两态及其叠加应用线性性，得 $A_\alpha=c_\alpha P$。$P\ne0$ 时有 $\sum|c_\alpha|^2=1$；$P=0$ 时全部 Kraus 算子为零。两种情形的未归一更新都为 $P\rho P$。只给投影效果、不要求范围内不扰动时，并不唯一决定这一更新。

**白话图景。**量子的现有规则能接成一条关系链：共同关系造出态空间，共同变化造出酉运动，独立组合给出复合载体，内部记录给出测量与局部混合。本轮再把最简内部伙伴作用锁成交换，并把换锚、相对运动与曲率放回同一条链。每个环节都写明前件，才知道哪些是定义、哪些是已经证明的必然后果。

<a id="section-15"></a>

## 15. 统一场论的确切进度：已闭合什么，还须锁定什么

本轮已经闭合的理论部分包括：同类二体原子的分类、未知锚的反作用、整体圆与局部椭圆、完全内部的关系不相容、移动锚下的轨迹等距、路径曲率及补向诱导曲率，以及一个完整有限交换网络。这些结果使用同一关系语法，不需要在整体之外放置观察者。

它们尚不唯一选定现实的统一场论。理由可以严格反推：同样的共同各向同性允许任意 $b$ 甚至零；同样的规范协变允许不同的基底、联络、度量和作用量。即使另给定一个度量，

$$
\int\lVert F\rVert^2\,d\mu
\quad\text{与}\quad
\int(\lVert F\rVert^2+\lambda\lVert F\rVert^4)\,d\mu
$$

都可规范不变，却给不同动力学。因此“全部关系在整体内部”以及“换锚读数保持”不够排除这些不同模型。

| 还需选择的结构 | 本轮已有约束 | 尚不能声称的结论 |
| --- | --- | --- |
| 时空、局域性与度量 | 内部参数域与输运可定义 | 已推出三维空间、Lorentz 结构或等效原理 |
| 规范群与物质表示 | 二态片及完整有限 $U(d)$ 表示 | 已选择标准模型的群、粒子谱和耦合常数 |
| 场方程与源 | 曲率、Bianchi 恒等式与有限网络动力学 | Bianchi 恒等式自动等于 Yang–Mills 或 Einstein 方程 |
| 尺度及物理检验 | 内部时钟、能量和读口可标定 | 从几何图像单独得到 $\hbar,c,G$ 等数值 |
| 原生可实现性 | 已给完整条件与资源接口 | 任意数学门、读口或极限已由当前菜单供应 |

“公理内生”在这里具有可操作的含义：候选只量化内部端口、比较、操作和记录，并且能通过删去条件构造反例。把这样的模型族命名为一种关系结构，可将候选写成其定义间的约束；数学定理描述该结构的必然后果。现实为何属于这类结构，则仍须已有实验事实、项目实际来源或新的可检验选择条件。单纯改名不能将经验选择变成逻辑同义反复。

**白话图景。**可以把整幅图景这样说：整体没有最后一颗特权状态，任何可用部分都能成为比较的起点。态与锚一起作用，最简单的无绝对方向关系使两份内容相干地交换；完整看是圆，局部看可以是椭圆。许多二元关系共享内容，作用次序于是留下闭环相位、手性与不确定性。把这些局部比较沿内部历史接起来，就得到关系场；绕路不能完全抵消的剩余是曲率。换一套表示，整条关系轨迹仍然对得上；换了真实伙伴或参照，新的相对运动也能由同一理论计算。这已经是一套有明确定义、定理和预测的有限关系量子理论。要把它落实为现实四种相互作用的统一，还须继续用内部关系约束锁定时空、源和具体动力学。

> **本轮候选的最短白话。**两个同类量子端口之间，最简单的完整作用只认它们彼此的关系。大家一起换朝向，作用不变；锚也属于被作用的内容。在已经认证的共同量子结构中，这迫使完整原子成为“保持与交换”的相干组合。

<a id="references"></a>

## 来源与版本关系

<a id="ref-v86"></a>

1. 本对话已交付 v86，*补向相容、共同量子场与内部学习*，2026-11-02。承接其共同场定理、实际相位提升、程序与能量接口。

<a id="ref-v74"></a>

2. trureturing，[V74：光滑量子历史、余切动力学与内生运动](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)，固定提交；本轮核读 §§8、10，结合此前已读 §§3–7。

<a id="ref-static"></a>

3. trureturing，[Ω 静态相容纤维理论](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，固定提交；相关 §§3、5、9、31、55。路径独立性、闭环与已有交换用途均有条件。

<a id="ref-fib"></a>

4. trureturing，[FIB 量子原则与相干重建续卷 V](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_V.md)，定义 1.1、§§8.1、8.6、9.2。仅作已核验原生接口对应。

<a id="ref-ziman"></a>

5. M. Ziman et al., *Quantum homogenization*, [arXiv:quant-ph/0110164](https://arxiv.org/abs/quant-ph/0110164)，§II，式 (2.3)–(2.7)。该稿使用 $+i\sin\eta\,\mathsf S$；本文选 $-i\sin\theta\,\mathsf S$，交换子符号相应改变。

<a id="ref-lloyd"></a>

6. S. Lloyd, M. Mohseni, P. Rebentrost, *Quantum principal component analysis*, [arXiv:1307.0401](https://arxiv.org/abs/1307.0401)，关于多份状态与短部分交换的论证。本文有限时间式由完整酉直接推导，保留 $\sin\theta\cos\theta$ 系数。

<a id="ref-qrf"></a>

7. F. Giacomini, E. Castro-Ruiz, Č. Brukner, *Quantum mechanics and the covariance of physical laws in quantum reference frames*, [doi:10.1038/s41467-018-08155-0](https://doi.org/10.1038/s41467-018-08155-0)；[arXiv:1712.07207](https://arxiv.org/abs/1712.07207)，§I.B 式 (3)–(6)。该文从已有量子运动出发，不能引用为零前提量子起源证明。

<a id="ref-simon"></a>

8. B. Simon, *Holonomy, the Quantum Adiabatic Theorem, and Berry's Phase*, Physical Review Letters 51, 2167 (1983)， [doi:10.1103/PhysRevLett.51.2167](https://doi.org/10.1103/PhysRevLett.51.2167)。此处仅对应绝热本征线上的几何相位与 holonomy；不据此宣称已统一所有相互作用。
