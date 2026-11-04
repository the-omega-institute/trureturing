# 单轴夹持

> 参考输入：AI 撰写的工作稿，由用户提供于本会话（2026-11-04，Asia/Singapore）。Lean 是仓库的数学真源；本文仅为参考文稿，未作形式化认证。

QUANTUM ORIGINS / $\Omega Q$-009

一种作用只停一根轴；前后夹住其它作用，只剩一条线

**本轮唯一候选。**

令 $e$ 为同一完整原预测窗口的中心化来源，$W=\operatorname{span}(Ge)$，$\mathfrak g=\operatorname{Lie}(G)$。要求

$$
\boxed{\exists A\in\mathfrak g:\qquad
\ker A=\mathbb R e,\qquad
\operatorname{rank}\bigl(\mathcal C_A:\mathfrak g\to\operatorname{End}(W),\ K\mapsto AKA\bigr)=1.}
\tag{Q9}
$$

后一个条件自动排除 $A=0$。它只要求全部夹持结果互为倍数，未预先指定输出沿着 $A$。

白话：**有一种转向，只让原内容这一根轴不动；把任意原转向夹在它的两次作用之间，所有结果都只剩同一种作用的不同强弱。**

主定理仅用紧作用给出的正比较、矩阵块分解、来源循环性和原 Lie 括号闭合，推出

$$
\dim W=\dim\mathfrak g=3,\qquad\mathfrak g=\mathfrak{so}(W).
$$

随后，夹持留下的系数成为比较尺；三次重复作用约回一次；原内容与原交换子直接给地址。由比较和交换子构造四个实振幅，再由原来源的稳定相位恢复复二维 Hilbert 空间及 Born 律。

 日期：2026-11-04，新加坡。

固定源码：`dev@d9880e9f2c329bb3db982f33791419d5d90126b9`。

提交时间：2026-11-04 19:01:29 +0800。

承接：$\Omega Q$-008，固定版本 `8e15c484...`。

本稿为普通数学定义、定理、证明与反模型；未声明 Lean 认证或文献首创。

本轮压缩了候选的表达、输入对象及刚性证明；完整原方向、记录与实现条件继续保留。

<a id="section-1"></a>

## 1. 最新项目接点与本轮的压缩

本轮实际读取的 `dev` 已更新为 `d9880e9f...`。相对上一轮，完整树差异为 178 个路径、6540 行新增和 792 行删除。理论正文只有三份变化：C117 追加 §§25–29；新增 Fourpath Continuation IV；新增 Giacomelli 无限 log-concavity 锥收缩。C127 本轮未改。HEAD 的 C113 标题对应已有正文的接入，本文不把它重复算作新增数学。 [1](#ref-commit)、[2](#ref-compare)

**C117 新增边界。**

若整个原未来图确有固定有限原标签的准确非负合法控制展开，定理 25.2 给兼容常数与统一 $\kappa>0$，共同正修复满足

$$
d_{\mathcal D}(F)\le\frac{\delta}{\kappa+\delta},\qquad \delta=5\varepsilon.
$$

但命题 25.4 同时证明：*两个种子也可以产生无限维完整预测张成*。命题 27.2 又在同一固定二、三标签共享记录图上构造

$$
\varepsilon_N\to0,\qquad
d_{\mathcal D_3}(F^{(N)})
=\frac{1-1/\sqrt2}{2}>0.
$$

这些是明确模型与假设下的结果，不是未知原生响应已经仿射或正的证明。§29 保留的原生全未来共同正性义务也未闭合。 [3](#ref-c117)

因此本轮的简化发生在*准确关系*本身；有限种子、小残差、少数标签不能替代完整 $W$。下面还给出与之呼应的新反例：夹持可以任意接近秩一，完整内容却一直五维。

**Fourpath 新增边界。**

新定理 49.1 在既定 $\operatorname{Dens}_2\times U(4)$ 域中证明，选定正几何支行列式恰有一个临界零点

$$
59/25<\xi_*<61/25,\qquad D'_{\mathrm{sel}}(\xi_*)<0,
$$

完整效果消去与稳定方向松弛后的四次系数 $C_{\mathrm{eff}}>28/25$。其严格局部极小与分支结论限于所述原 level 的 phase-feedback 部分。稳定方向不能省略，例如

$$
F(b,z)=\tfrac12z^2+2zb^2+b^4,\qquad
F(b,0)=b^4,\quad \min_zF(b,z)=-b^4.
$$

本文保留全部原作用方向，同样避免先固定看不见的方向再宣称稳定。该 Fourpath 定理已经在量子矩阵域中工作，不用作量子结构起源的前件。 [4](#ref-fourpath)

**本轮的实质简化。**

上一轮用完整一阶关系 $Kx+Ay=0$ 的两个商空间相互唯一，再借辛球面论证得到三维。本轮只用原来源 $e$ 和一个算子 $A$：一个核、一条夹持像。三维主证明全为矩阵代数；无须预输入维数、复数、叉积、内容地址或单频律。

<a id="section-2"></a>

## 2. 定义：完整原窗口、来源与二元夹持

### 定义 2.1（完整原预测前端）

固定 $\Omega$ 内的原归一准备。原总可逆控制含空词、接续封闭，并有同菜单内准确统计逆。共同未来域保留全部合法请求、完整标签、失败、可读旧记录及相关可用性区别。写

$$
x_a(f,w)=p(a;f,w),\quad p\ge0,\quad\sum_wp(a;f,w)=1.
$$

定义

$$
V=\operatorname{span}_\mathbb R\{x_a\},\qquad u(x_a)=1,\qquad
W=\ker u=\operatorname{span}_\mathbb R\{x_a-x_b\}.
$$

要求 $V$ 有限维且 $W\ne0$。这定义一个有限预测窗口，不宣称整个 $\Omega$ 有限，也不由有限门数推出有限维数。

### 引理 2.2（紧作用与循环来源）

<a id="lem-front"></a>

接续 $T_gx_a=x_{ag}$ 在 $V$ 上良定义，其矩阵闭包 $H$ 是紧群。置

$$
c=\int_Hhx_\epsilon\,dh,\qquad e=x_\epsilon-c,\qquad
G=H|_W,\qquad\mathfrak g=\operatorname{Lie}(G)\subseteq\operatorname{End}_\mathbb R(W).
$$

则 $V=\mathbb R c\oplus W$，$G$ 紧且有效，$e\ne0$，并有

$$
\boxed{W=\operatorname{span}(Ge).}
$$

**证明。**
原行的线性关系在全部未来成立，故在以 $g$ 开头的未来也成立，使接续良定义。选有限实际行基与有限分离评价坐标；接续后这些坐标仍在 $[0,1]$，所以所有矩阵一致有界。准确统计逆使逆也一致有界，闭包无奇异矩阵，故为紧群。

平均 $c$ 固定且 $u(c)=1$。固定 $c$ 并在 $W$ 恒等的作用在 $V$ 恒等，因此限制有效。各 $x_a-c=T_ae$，它们张成 $W$，得到循环性。若 $e=0$，全部轨道不动，与 $W\ne0$ 矛盾。

原程序身份和日志并未因预测表示而被删除。$A\in\mathfrak g$ 首先是原作用闭包的无穷小生成元，不自动是实际菜单中已供应的精确连续器件。数学闭包也不会新增可调用的复合、读口或随机准备。

### 定义 2.3（停轴与夹持）

对 $A\in\mathfrak g$，停住内容为 $\ker A=\{x:Ax=0\}$。定义

$$
\mathcal C_A:\mathfrak g\longrightarrow\operatorname{End}(W),\qquad
\mathcal C_A(K)=AKA.
$$

乘法是完整 $W$ 上的算子顺序合成。两个元是 $A,K$；同一个 $A$ 在两侧重复，不另引第三个独立元。

**候选 $\Omega Q$-009：单轴夹持。**

$$
\boxed{\exists A\in\mathfrak g:\quad
\ker A=\mathbb R e,\qquad \dim\mathcal C_A(\mathfrak g)=1.}
\tag{Q9}
$$

第一项只留原来源轴；第二项只留一条夹持响应线。公理没有预定那条像线等于 $\mathbb R A$，也没有预定 $A$ 在其余方向上只有一个频率。

这里比较的是*整个算子*。只在 $e$ 上比较毫无辨识力，因为 $Ae=0$ 已使全部 $AKAe=0$。$\operatorname{rank}\mathcal C_A=1$ 也不是 $\operatorname{rank} A=1$；后者最后会被证明为二。

若写成参数响应，$AKA$ 是

$$
\left.\partial_s\partial_t\partial_r
\bigl(e^{sA}e^{tK}e^{rA}\bigr)\right|_{s=t=r=0}.
$$

它不是有限门的共轭 $UKU^{-1}$，也不是三次物理测量。后者的实际供应须另外证明。本轮不声称实验响应阶数比上一轮更低。

<a id="section-3"></a>

## 3. 反着推：条件缺失时，各有什么后果

### 反例 3.1（停轴不唯一：原记录可留在额外方向）

取 $W=\mathbb R^3\oplus\mathbb R$、$G=SO(3)\times\{\pm1\}$，来源 $e=(e_3,1)$。它循环且群平均为零。令 $R_{e_3}z=e_3\times z$、$A=R_{e_3}\oplus0$。则 $\dim(A\mathfrak g A)=1$，但
$\ker A=\mathbb R e_3\oplus\mathbb R$ 为二维，完整 $W$ 为四维。

这说明只看夹持线会漏掉真实可区分的静止方向；不能先把那个方向删去再宣布候选成立。

### 反例 3.2（夹持不唯一：横向可保留多个独立转向）

取 $W=\mathbb R^5,G=SO(5),e=e_5$，令

$$
A=J_{12}+J_{34},
$$

其中 $J_{ij}e_i=e_j,J_{ij}e_j=-e_i$。有 $\ker A=\mathbb R e$。但在 $e^\perp$ 上 $A$ 可逆，$K\mapsto AKA$ 的像同构于 $\mathfrak{so}(4)$，故其维数为六。

### 反例 3.3（没有原顺序闭合：五维裸算子族也会通过）

在上一反例中，令 $E=e^\perp$，对 $v\in E$ 定义

$$
X_v(te+z)=tv-\langle v,z\rangle e.
$$

裸线性族 $\mathcal L=\mathbb R A+\{X_v:v\in E\}$ 满足
$\ker A=\mathbb R e,\ \dim(A\mathcal L A)=1$，因为 $AX_vA=0$。
但 $[X_{e_1},X_{e_2}]$ 给一个只转 $12$ 平面的算子，不在 $\mathcal L$。完整 Lie 闭包增添横向转向后，夹持像不再一维。

### 反例 3.4（没有来源循环：可以藏入从未由原来源到达的方向）

仍取 $W=\mathbb R^5,e=e_5,A=J_{12}+J_{34}$，但取 $G=\{e^{tA}\}$、$\mathfrak g=\mathbb R A$。两条候选条件都成立，然而 $Ge=\{e\}$ 不张成 $W$。引理 [2.2](#lem-front) 已排除这种伪窗口。

### 反例 3.5（没有紧性：二维反例）

令 $W=\mathfrak{aff}(1)=\operatorname{span}(h,z)$，$[h,z]=z$，取忠实伴随作用、循环来源 $e=h$、$A=\operatorname{ad}_h$。则

$$
\ker A=\mathbb R h,\qquad A^2=A,\qquad A\mathfrak g A=\mathbb R A,
$$

但 $\dim W=2$。其作用非紧，不能来自上述完整有界可逆概率前端。

<a id="section-4"></a>

## 4. 主定理：一条夹持像直接迫出三维

<a id="sec-main"></a>

### 定理 4.1（单轴夹持刚性）

在引理 [2.2](#lem-front) 的同一前端，$Q9$ 等价于

$$
\boxed{\dim W=3,\qquad
\mathfrak g=\mathfrak{so}(W,B),\qquad G^\circ=SO(W,B).}
$$

完整 $G$ 为 $SO(3)$ 或 $O(3)$。这里 $B$ 是唯一满足 $B(e,e)=1$ 的 $G$-不变正内积。

**证明。**
**一、只用紧性选证明用比较。**
对任意正内积作 Haar 平均，并缩放使 $B_0(e,e)=1$。于是所有 $K\in\mathfrak g$ 斜对称。写

$$
W=\mathbb R e\oplus E,\quad E=e^\perp,\qquad
A=\begin{pmatrix}0&0\\0&D\end{pmatrix}.
$$

$\ker A=\mathbb R e$ 使 $D:E\to E$ 可逆。斜对称非零算子不能有 $A^3=0$，所以夹持像一维首先给

$$
A\mathfrak g A=\mathbb R A^3.
\tag{4.1}
$$

此时尚未将它说成 $\mathbb R A$。

**二、夹持唯一迫使全部横向块同向。**
任一 $K\in\mathfrak g$ 有块式

$$
K=\begin{pmatrix}0&-v^\flat\\v&S\end{pmatrix},
\qquad v=Ke,\quad S^*=-S.
$$

由 $AKA=tA^3$ 得

$$
DSD=tD^3.
$$

两侧消去可逆 $D$，得到 $S=tD$。所以

$$
\boxed{K=tA+X_v,\qquad
X_v(se+z)=sv-B_0(v,z)e.}
\tag{4.2}
$$

特别地，

$$
\mathfrak g_e=\{K:Ke=0\}=\mathbb R A.
\tag{4.3}
$$

停住原来源的转向唯一，已成为结论。

**三、原来源循环性保证轴确实能被搬动。**
若每个 $v=Ke$ 都为零，则 $\mathfrak g=\mathbb R A$。每个 $g\in G$ 正规化自己的 Lie 代数线，因此
$gAg^{-1}$ 是 $A$ 的非零倍数。它随即保持 $\ker A=\mathbb R e$，故 $Ge\subseteq\mathbb R e$。
循环性使 $W=\mathbb R e$，与 $A\ne0$ 矛盾。此论证也覆盖不连通 $G$。

因此可取 $v\ne0$ 使 $X_v\in\mathfrak g$。Lie 闭合给

$$
[A,X_v]=X_{Dv}\in\mathfrak g.
$$

$D$ 可逆斜对称，所以 $Dv\ne0$、$B_0(v,Dv)=0$。

**四、两次偏转的顺序差，只能是原停轴转向。**
再取交换子

$$
T=[X_v,X_{Dv}]\in\mathfrak g.
$$

它固定 $e$。对 $z\in E$，直接计算

$$
Tz=B_0(v,z)Dv-B_0(Dv,z)v.
\tag{4.4}
$$

所以它只在 $\operatorname{span}(v,Dv)$ 上非零，且秩恰为二。由 (4.3)，$T=cA$。在 $v$ 上比较还得到 $c=B_0(v,v)>0$，即
$[X_v,X_{Av}]=B_0(v,v)A$。于是

$$
\operatorname{rank} A=2,\qquad \dim W=\dim\ker A+\operatorname{rank} A=3.
$$

这一步就是三维有限提升：$\{e,v,Av\}$ 已覆盖完整原窗口。

**五、恢复全部三维转向。**
此时 $E$ 二维，$v,Dv$ 为其基。因此 $\mathfrak g$ 包含三个独立算子

$$
A,\quad X_v,\quad X_{Dv},
$$

而 $\mathfrak{so}(W,B_0)$ 只有三维，故两者相等。于是 $G^\circ=SO(3)$，且 $G\subseteq O(3)$，完整群只有所列两种。

反向，在标准三维旋转作用中，对原来源 $e\ne0$ 取任一非零轴转向 $A$。它的核是 $\mathbb R e$。写 $W=\mathbb R e\oplus e^\perp$，横向二维的斜对称算子空间一维，所以任意 $K$ 的横向块均为 $A$ 的倍数，因而夹持像一维。

全部旋转的不变正比较只差比例，条件 $B(e,e)=1$ 固定该比例。证毕。

**与 $\Omega Q$-008 的准确关系。**

三维标准作用满足上一轮全部一阶互补偿；上一轮也已证明一阶互补偿只选中该作用。因此两轮在同一前端等价。本稿的主定理独立于上一轮证明：不使用射影切空间、KKS 辛形式、球面上同调或表示分类。简化发生在所需对象、表达与证明，未声称模型类严格扩大。

<a id="section-5"></a>

## 5. 夹持读数成为比较，原交换子直接成为地址

### 5.1 由夹持留下的系数定义比较

### 定理 5.1（全局夹持律与内生比较）

<a id="thm-sandwich"></a>

$Q9$ 成立后，对所有 $B,K\in\mathfrak g$，

$$
\boxed{BKB=-\kappa(B,K)B,\qquad
\kappa(B,K)=-\tfrac12\operatorname{Tr}_W(BK).}
\tag{5.1}
$$

所以对 $B\ne0$，可以先把 $\kappa(B,K)$ 定义为夹持后沿 $B$ 剩下的负系数，再由右式证明它对称、双线性且正定。

**证明。**
主定理后选证明用正交取向，将斜对称算子写成 $Bz=b\times z,Kz=k\times z$。向量三重积给

$$
BK=k b^\flat-B_0(b,k)I,\qquad
BKB=-B_0(b,k)B.
$$

取迹有 $-\frac12\operatorname{Tr}(BK)=B_0(b,k)$。此等式对相反取向也相同；迹的坐标不变性与原斜对称性给全部所列性质。

这份比较来自同一原作用的返回系数；选择证明用取向没有进入最终定义。极化 (5.1) 得到更完整的关系：

$$
BKC+CKB=-\kappa(B,K)C-\kappa(C,K)B,
\tag{5.2}
$$

$$
[B,[K,C]]
=\kappa(B,C)K-\kappa(B,K)C.
\tag{5.3}
$$

第二式由第一式交换 $K,C$ 后相减得到。因此

$$
\|[B,K]\|_\kappa^2
=\kappa(B,B)\kappa(K,K)-\kappa(B,K)^2.
\tag{5.4}
$$

证明可将 (5.3) 与迹配对的不变性相结合。正交、面积和三重关系均由同一个二元夹持读数恢复。

### 推论 5.2（自归一夹持就是实转向投影）

对 $B\ne0$，定义

$$
\mathcal P_B(K)=-\frac{BKB}{\kappa(B,B)}
=\frac{\kappa(B,K)}{\kappa(B,B)}B.
$$

则 $\mathcal P_B^2=\mathcal P_B$，它是 $(\mathfrak g,\kappa)$ 到 $\mathbb R B$ 的正交投影，且 $B$ 的非零重标不改变它。

这是转向空间里的实轴投影。它的轴无向，因而不等同于后面的量子纯态投影；后者保留相反内容的区别。

### 5.2 原内容加切向变化，给出原地址加交换子变化

### 定理 5.3（不用外给体积形式的地址构造）

任何 $w\in W$ 唯一写成

$$
w=t e+K e,
$$

其中 $t$ 唯一、$K$ 只差一个 $A$ 的倍数。定义

$$
\boxed{\Phi(te+Ke)=tA+[K,A].}
\tag{5.5}
$$

则 $\Phi:W\to\mathfrak g$ 为实线性同构，$\Phi(e)=A$，且
$\ker\Phi(w)=\mathbb R w$ 对 $w\ne0$ 成立。

**证明。**
主定理给 $\mathfrak g e=e^\perp$ 与 $\mathfrak g_e=\mathbb R A$，因此表示及独立性成立。若 $K$ 改成 $K+sA$，交换子不变，所以定义良定。

写 $v=Ke,K=sA+X_v$，则 $[K,A]=-X_{Dv}$。于是

$$
(tA-X_{Dv})(te+v)
=tDv-tDv+B_0(Dv,v)e=0.
$$

这同时说明 $\Phi(w)w=0$。若 $\Phi(w)=0$，其对角与非对角块分别给 $t=0,Dv=0$，所以 $w=0$。维数给同构；三维非零斜对称算子的核一维，故核恰为 $\mathbb R w$。

所有保持该核线的线性同构只差非零常数：两份之比保持每条直线，看基向量及其两两之和便知它是标量。条件 $\Phi(e)=A$ 因而固定唯一标定。

### 推论 5.4（原内容的归一比较与转向）

定义

$$
\boxed{
B(w,z)=\frac{\kappa(\Phi(w),\Phi(z))}{\kappa(A,A)},
\qquad R_w=\frac{\Phi(w)}{\sqrt{\kappa(A,A)}}.}
\tag{5.6}
$$

则 $B$ 是唯一满足 $B(e,e)=1$ 的原不变正比较，并有

$$
\kappa(R_w,R_z)=B(w,z),\quad
[R_w,R_z]=R_{R_wz},\quad
R_wR_zv=B(w,v)z-B(w,z)v.
$$

**证明。**
在主证明的 $B_0(e,e)=1$ 标定中，$A=\lambda(e\times\cdot)$；(5.5) 给 $\Phi(w)=\lambda(w\times\cdot)$。所以 (5.6) 恰为 $B_0$，并给两种归一取向之一的叉积恒等式。换原见证或取向不改变 $B$。

若完整 $G=O(3)$，有向提升满足
$\operatorname{Ad}_gR_w=\det(g)R_{gw}$；它不是对反射无扭曲协变的映射。原相反内容、相反转向及原速率均继续保留。

<a id="section-6"></a>

## 6. 三项闭合、圆与两个读出的椭圆

### 定理 6.1（单频与幂递推成为结论）

对任意非零 $B\in\mathfrak g$，置 $\lambda=\sqrt{\kappa(B,B)}>0$，则

$$
\boxed{B^3=-\lambda^2B,\qquad B^{r+2}=-\lambda^2B^r\quad(r\ge1).}
\tag{6.1}
$$

因此

$$
e^{tB}=I+\frac{\sin(\lambda t)}{\lambda}B
+\frac{1-\cos(\lambda t)}{\lambda^2}B^2.
\tag{6.2}
$$

**证明。**
在 (5.1) 取 $K=B$ 得第一式，乘幂给递推，按奇偶幂对指数级数求和得到 (6.2)。

令

$$
P_\parallel=I+B^2/\lambda^2,\qquad
P_\perp=-B^2/\lambda^2.
$$

由 (6.1) 可核对它们是互补正交投影，秩分别为一、二。置 $w_\parallel=P_\parallel w(0)$、$w_\perp=P_\perp w(0)$，任意内容的轨迹为

$$
w(t)=w_\parallel+
\cos(\lambda t)w_\perp+
\sin(\lambda t)\frac{Bw_\perp}{\lambda}.
\tag{6.3}
$$

横向两向量正交且等长。因而原三维轨迹是平面圆或静止点；在单位球上一般为小圆，$w_\parallel=0$ 时才是大圆。重复关系的幂在 $\{I,B,B^2\}$ 内停止增添新方向，并未由此离散化原转速。

### 定理 6.2（两线性读出的椭圆）

对两份固定仿射读出 $r=(f_1,f_2)$，沿 (6.3) 有

$$
r(t)=r_c+p\cos(\lambda t)+q\sin(\lambda t).
$$

令 $M=[p\ q]$。若 $\operatorname{rank} M=2$，其轨迹满足

$$
\boxed{(r-r_c)^T(MM^T)^{-1}(r-r_c)=1.}
\tag{6.4}
$$

它为圆当且仅当 $MM^T$ 是正标量矩阵；秩一时退化为线段，秩零时为点。

**证明。**
仿射读出施加于 (6.3) 即得前式。可逆 $M$ 把单位圆的两坐标映到读出平面，左乘 $M^{-1}$ 并取平方范数得到 (6.4)。奇异值相等恰为圆；其余秩的结论直接成立。

这给“两个读出加一条归一关系”一份准确模型。椭圆形状由读口映射决定；当原生成元随历史改变，候选不强迫任意路径都是椭圆。初始切线也不唯一决定整条后续历史。

```latex
\begin{tikzpicture}[>=Latex,scale=.84]
\draw[->,ink!65] (-2.4,0)--(2.4,0);
\draw[->,ink!65] (0,-1.6)--(0,1.7);
\draw[very thick,accent] (0,0) circle(1.3);
\node at (0,-2.05){原转动平面：两正交、等长分量};
\draw[->,thick,ink] (2.8,.15)--(4.3,.15) node[midway,above]{两份读出};
\begin{scope}[shift={(7,0)},rotate=25]
\draw[very thick,warm] (0,0) ellipse(2.1 and .85);
\draw[->,ink!45] (-2.45,0)--(2.45,0);
\draw[->,ink!45] (0,-1.2)--(0,1.25);
\end{scope}
\node at (7,-2.05){读出平面：\(M(S^1)\)};
\end{tikzpicture}
```

**图 1。**固定生成元给圆；两线性读出一般给椭圆。图示的是准确投影关系，不把任意历史强制为椭圆。

<a id="section-7"></a>

## 7. 更短的振幅构造：四个实分量，内生复二维

### 7.1 由比较和交换子定义四元数代数

### 定义 7.1（四实维振幅代数）

在实空间 $\mathcal Q=\mathbb R1\oplus\mathfrak g$ 上定义

$$
(a,B)\star(b,K)
=\bigl(ab-\kappa(B,K),\,aK+bB+[B,K]\bigr),
\qquad (a,B)^*=(a,-B).
\tag{7.1}
$$

### 定理 7.2（结合性、正范数与四元数）

$\mathcal Q$ 是含幺结合实代数，满足

$$
q^*\star q=\|q\|^2\,1,\qquad
\|(a,B)\|^2=a^2+\kappa(B,B),\qquad
\|q\star r\|=\|q\|\|r\|.
$$

每个非零元可逆，且 $\mathcal Q\cong\mathbb H$。

**证明。**
只需验证三个纯转向的结合律。由 (5.3) 与迹配对不变性，$(B\star K)\star C$ 与 $B\star(K\star C)$ 的标量部分同为
$-\kappa([B,K],C)=-\kappa(B,[K,C])$，向量部分同为

$$
-\kappa(B,K)C-\kappa(K,C)B+\kappa(B,C)K.
$$

所以结合。直接代入得 $q^*q=\|q\|^2$，且 $(qr)^*=r^*q^*$；结合性于是给范数乘法。逆为 $q^*/\|q\|^2$。

取 $\kappa$-正交单位 $u,v$，令 $w=[u,v]$。式 (5.3)–(5.4) 给

$$
u^2=v^2=w^2=-1,\quad uv=w,\quad vu=-w
$$

及循环关系。这正是 Hamilton 四元数乘法表。 [6](#ref-baez)

从此本节省略 $\star$，但保留类型：$\mathcal Q$ 的乘法由比较和括号新定义。原 $W$ 上的算子顺序乘法仍在 $\operatorname{End}(W)$ 中；原三维斜对称生成元生成的结合代数是 $M_3(\mathbb R)$，不是 $\mathcal Q$ 或 $M_2(\mathbb C)$。具体地，正交单位轴生成元满足 $R_iR_j=E_{ji}$（$i\ne j$）、$R_i^2+I=E_{ii}$，故给全部实矩阵单位。这几种表示通过明确构造相连，不能相互冒名。

### 7.2 原来源挑出相位子代数，得到复二维 Hilbert 空间

取

$$
u=R_e=\frac{A}{\sqrt{\kappa(A,A)}},\qquad u^2=-1.
$$

定义原来源的相位子代数

$$
\mathbb C_u=\{a+bu:a,b\in\mathbb R\}.
$$

它在 $\mathcal Q$ 内已经存在。为固定通常复符号的取向，取

$$
j:\mathbb C\to\mathbb C_u,\qquad j(a+ib)=a-bu.
$$

将同一个四实维空间 $\mathcal Q$ 看成右复向量空间

$$
q\cdot z=q\,j(z).
$$

定义

$$
\pi_u(q)=\tfrac12(q-uqu),\qquad
\langle q,r\rangle=j^{-1}\!\left(\pi_u(q^*r)\right).
\tag{7.2}
$$

对 $q=a+K$，还有直接连接原候选的等式

$$
\boxed{\pi_u(a+K)=a+\kappa(u,K)u
=a-(uKu)_{\operatorname{End}(W)}.}
$$

最后一项用的是原算子夹持，中间和左侧在 $\mathcal Q$ 中。相位平面正是“原夹持留下的那根轴，加上单位方向”；两种乘法的类型保持明确。

### 定理 7.3（复二维振幅）

该空间是复二维 Hilbert 空间 $\mathcal H\cong\mathbb C^2$。若 $v\perp u$ 为单位纯转向，则

$$
\mathcal Q=\mathbb C_u\oplus v\mathbb C_u
$$

是两份正交实二维平面；写 $q=j(z_1)+v j(z_2)$，便有

$$
\|q\|^2=|z_1|^2+|z_2|^2.
$$

**证明。**
$\pi_u$ 保留 $1,u$ 分量并消去垂直纯转向，故值在 $\mathbb C_u$。对 $c,d\in\mathbb C_u$，因它们与 $u$ 交换，
$\pi_u(csd)=c\pi_u(s)d$。这给内积的共轭线性、线性与共轭对称；$q^*q=\|q\|^2$ 给正定。四元数正交基 $1,u,v,uv$ 给所列直和、复维数二与范数式。有限维保证完备。

$\mathbb C_u$ 不是四元数的中心。它的单位范数元素构成保持原来源读出不变的右相位圈；复线性算子代数 $\operatorname{End}_\mathbb C(\mathcal H)$ 的标量中心才是通常的 $\mathbb C I$。这里明确区分两者。

### 7.3 同一内容的全部振幅代表，恰好只差相位

### 定义 7.4（内容读出）

对单位振幅 $q\in\mathcal Q$，定义

$$
X(q)=q u q^*\in\mathfrak g,\qquad n(q)=R^{-1}(X(q))\in W.
\tag{7.3}
$$

### 定理 7.5（Hopf 读出与复射线）

$X(q)$ 为单位纯转向，读出覆盖整个 $S(W)$。两份单位振幅读出相同，当且仅当

$$
r=q\,j(e^{i\theta})
$$

对某个 $\theta$ 成立。因此

$$
\boxed{S^1\longrightarrow S^3\longrightarrow S^2,\qquad
\mathbb C P^1\cong S^2.}
$$

**证明。**
共轭保持纯转向与范数。对任一单位 $X\ne-u$，取

$$
q=\frac{1-Xu}{\sqrt{2(1+\kappa(X,u))}}.
$$

它范数一，且 $qu=Xq$，因此 $quq^*=X$。对 $X=-u$，取单位 $v\perp u$ 即可。

若 $quq^*=rur^*$，则 $q^*r$ 与 $u$ 交换。纯转向部分与 $u$ 的交换子为零，按 (5.4) 必平行于 $u$，所以 $q^*r\in\mathbb C_u$。它范数一，恰为所列相位。反向直接成立。

因此保留内容的连续相位圈由原来源的稳定关系决定。把全部单位四元数都当成无差别标量，会把不同内容一起合并，违背同一读出。三维 $W$ 是内容嵌入空间；其纯态球面二维，单位振幅球面三维，去掉一个相位维后恰好二维。

### 7.4 Born 平方律的直接四元数证明

### 定理 7.6（半角平方）

对单位振幅 $q,r$，

$$
\boxed{
|\langle q,r\rangle|^2
=\frac{1+\kappa(X(q),X(r))}{2}
=\frac{1+B(n(q),n(r))}{2}.}
\tag{7.4}
$$

**证明。**
写单位 $p=q^*r=a+bu+cv+d\,uv$。则

$$
|\pi_u(p)|^2=a^2+b^2,\qquad
a^2+b^2+c^2+d^2=1.
$$

由四元数乘法直接算得

$$
\kappa(u,pup^*)=a^2+b^2-c^2-d^2.
$$

共轭保持 $\kappa$，所以该量就是
$\kappa(quq^*,rur^*)$。联立两式得到 (7.4)。

若两份有向内容夹角为 $\theta$，则 (7.4) 为 $\cos^2(\theta/2)$。第 5 节的实转向轴投影给的是 $\cos^2\theta$；这里加回了有向内容、归一化与相位纤维，两个投影的类型不同。相反内容 $n,-n$ 对应正交纯态。

### 7.5 自伴算子与原概率的准确保持

对 $X\in\mathfrak g$，定义复线性算子

$$
\widehat X(r)=-Xru.
$$

记左、右乘为 $L_X,R_u$，则复结构 $i=-R_u$，有
$\widehat X=L_Xi$。

### 定理 7.7（Pauli 关系与原 Born 配对）

上述算子自伴，并满足

$$
\widehat X\widehat Y
=\kappa(X,Y)I+i\widehat{[X,Y]},\qquad
\operatorname{Tr}\widehat X=0,\quad
\operatorname{Tr}(\widehat X\widehat Y)=2\kappa(X,Y).
\tag{7.5}
$$

对单位 $X=X(q)$，

$$
P_X=\tfrac12(I+\widehat X)
$$

恰为振幅 $q$ 的复秩一正交投影。

**证明。**
左乘纯转向和右乘 $u$ 都反自伴且彼此交换，故它们的负乘积自伴。四元数乘法给 (7.5) 的乘法式。取单位 $Y\perp X$，$\widehat Y\widehat X\widehat Y=-\widehat X$，所以迹为零，再由乘法式得迹配对。

对任意 $r$，有

$$
P_{X(q)}r
=\tfrac12(r-quq^*ru)
=q\,\pi_u(q^*r)
=q\cdot\langle q,r\rangle.
$$

这正是复秩一正交投影公式。

$I,\widehat{\mathfrak g}$ 张成全部自伴 $2\times2$ 复算子，因为它们四实维且线性独立。因此
$\operatorname{End}_\mathbb C(\mathcal H)\cong M_2(\mathbb C)$。它也满足上一轮的 Clifford 生成关系，所以复振幅路线与 Clifford 路线准确相容；本轮无需先建八实维 Clifford 代数再取最小理想。

原轨道闭包为 $c+S(W)$，最小闭凸完成为 $c+\overline B(W)$。任一原事件唯一写成

$$
f(tc+w)=\alpha t+B(b,w).
$$

原概率界给 $\|b\|\le\min(\alpha,1-\alpha)$。对 $\|w\|_B\le1$，令

$$
\rho_w=\tfrac12(I+\widehat{R_w}),\qquad
E_f=\alpha I+\widehat{R_b}.
$$

则 $\rho_w\ge0,\operatorname{Tr}\rho_w=1,0\le E_f\le I$，由 (7.5) 得

$$
\boxed{f(c+w)=\operatorname{Tr}(\rho_wE_f).}
\tag{7.6}
$$

原完整标签归一化给 $\sum_kE_k=I$，失败标签继续保留。数学闭凸完成及全部锐效果的存在，不自动供应原随机准备、读口或原分支过程。

<a id="section-8"></a>

## 8. 更大几何：锥、旋转、相位与路径

自伴矩阵 $aI+\widehat{R_w}$ 的本征值是 $a\pm\|w\|$，正锥为

$$
C=\{(a,w):a\ge\|w\|\},\qquad
\det(aI+\widehat{R_w})=a^2-B(w,w).
$$

其归一截面是三维球。定义

$$
L_w(t,z)=(B(w,z),tw),\qquad
\mathcal R_w(t,z)=(0,R_wz).
$$

由 (5.6) 逐项计算，

$$
[\mathcal R_w,\mathcal R_z]=\mathcal R_{R_wz},\quad
[\mathcal R_w,L_z]=L_{R_wz},\quad
[L_w,L_z]=-\mathcal R_{R_wz}.
$$

六个方向保持 $t^2-B(z,z)$，线性独立，故为 $\mathfrak{so}(1,3)$。其复矩阵实现是

$$
\mathcal R_w\mapsto-\tfrac i2\widehat{R_w},\qquad
L_w\mapsto\tfrac12\widehat{R_w}.
$$

这说明三维内容、四实维振幅和四维正锥属于同一组比较关系。这里未将响应总量 $t$ 认作物理时间。

### 命题 8.1（旋转的半角提升）

给定原生成元 $M=R_a$，单位振幅满足

$$
\dot q=\tfrac12M q
\quad\Longrightarrow\quad
\dot X=[M,X],\qquad
i\hbar\dot q=\tfrac\hbar2\widehat M q.
$$

因此内容转一圈时，振幅可得到负号；两圈才在该提升中返回。

**证明。**
微分 $X=quq^*$，四元数纯转向的乘法交换子是 $2[M,X]$，所以得到第一式。由 $\widehat M=L_Mi$ 得 $L_M=-i\widehat M$，给第二式。取单位轴 $v$，振幅 $q(t)=\cos(t/2)+v\sin(t/2)$ 直接显示 $2\pi$ 与 $4\pi$ 的区别。

这给指定参数后的数学表示；实际连续控制、原速率及 $\hbar$ 的数值仍由原接口承担。

### 命题 8.2（历史搬运与相位曲率）

沿给定单位内容路径 $n(t)$，令 $A(t)=\lambda(t)R_{n(t)}\ne0$。则

$$
M_{\rm hor}
=\frac{[A,\dot A]}{\kappa(A,A)}
=R_{n\times\dot n},\qquad
M_{\rm hor}n=\dot n.
$$

全部搬运为 $M_{\rm hor}+\alpha R_n$，其中水平者唯一最小化瞬时 $\kappa$-范数。

**证明。**
$[A,\dot A]=\lambda^2R_{n\times\dot n}$、$\kappa(A,A)=\lambda^2$，故公式成立。两份搬运之差固定 $n$，所以属于 $\mathbb R R_n$。两项正交，范数平方为 $\|\dot n\|^2+\alpha^2$。

若 $X(q)=R_n$ 且 $\dot q=\frac12M_{\rm hor}q$，则

$$
\langle q,\dot q\rangle
=\tfrac12j^{-1}\pi_u(q^*M_{\rm hor}q)
=-\tfrac i2\kappa(M_{\rm hor},R_n)=0.
$$

所以这份最小原搬运，确实提升为复振幅的水平连接。

在复二维坐标取局部单位代表

$$
\psi(\theta,\phi)=
\begin{pmatrix}\cos(\theta/2)\\e^{i\phi}\sin(\theta/2)\end{pmatrix}.
$$

直接微分给

$$
a=i\psi^\dagger d\psi=-\tfrac12(1-\cos\theta)d\phi,\qquad
da=-\tfrac12\sin\theta\,d\theta\wedge d\phi.
$$

水平提升 $\Psi=e^{i\chi}\psi$ 满足 $\Psi^\dagger d\Psi=0$，等价于 $d\chi=a$。因此闭路的几何相位为

$$
\boxed{\gamma=-\Omega_{\rm solid}/2\pmod{2\pi}.}
$$

跨图时加入过渡相位；两份跨面相差整球，曲率积分为 $-2\pi$，所以该相位模 $2\pi$ 良定。该积分也由 Stokes 定理排除全球光滑单位振幅截面。Hopf 几何恢复熟知的半立体角相位；Berry 原文讨论相应绝热量子相位。 [7](#ref-berry) 实际干涉实现仍需原相干参考。给定路径与起始单位振幅后，水平提升唯一；终点内容却不包含全部路径相位。

<a id="section-9"></a>

## 9. 完整有限量子理论：定义、定理与接口

<a id="sec-quantum"></a>

本节把基本块发展为完整的有限数学理论，并列出它与原整体实际对象对应所需的关系。$Q9$ 只选择基本窗口，不重复施加于全部复合内容。

### 9.1 复合与任意有限维系统

### 定理 9.1（复张量的唯一性）

若 $M_m(\mathbb C)$、$M_n(\mathbb C)$ 以同一复中心含幺 $*$-嵌入联合代数，两个像交换，且乘积复线性张成联合代数，则联合代数同构于 $M_{mn}(\mathbb C)$。

**证明。**
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 为满射含幺 $*$-同态。源 $M_m\otimes_\mathbb C M_n\cong M_{mn}$ 单，核为零或全体；含幺排除全体，故为同构。

量子位张量幂给 $M_{2^N}$，秩 $d\le2^N$ 的数学投影角给 $M_d$，再取有限直和，得到

$$
\mathcal A=\bigoplus_sM_{d_s}(\mathbb C).
$$

这给全部有限复矩阵代数的数学完成；实际支持角、实际复合与共用复中心仍须原接口供应。完整 C127 的某些满足族只有 $3^k$ 大小的块，并无实际 $M_2$ 对象；本文不能把数学角冒充原对象。 [5](#ref-c127)

### 9.2 状态、效果与观测量

### 定理 9.2（密度与迹配对）

标准正锥上的归一正线性泛函恰为

$$
\omega(a)=\sum_s\operatorname{Tr}(\rho_sa_s),\qquad
\rho_s\ge0,\quad\sum_s\operatorname{Tr}\rho_s=1.
$$

效果是 $0\le E\le I$，完整 POVM 满足 $\sum_kE_k=I$。自伴量 $H=\sum_kh_kP_k$ 的谱概率与均值分别为 $\operatorname{Tr}(\rho P_k)$、$\operatorname{Tr}(\rho H)$。

**证明。**
非退化迹配对给唯一自伴 $\rho_s$。在全部秩一正投影上非负等价于 $\rho_s\ge0$，单位评价给总迹一。反向直接成立。自伴谱分解给观测量结论。

### 9.3 完整参考推出 CP 与一般仪器

### 定理 9.3（参考保正与 Kraus 表示）

设同一原分支在自伴部分实线性，作唯一复线性延拓 $\mathcal E:M_d\to M_n$。若有实际完整矩阵参考 $M_r$、$r\ge d$，使 $\mathcal E\otimes\operatorname{id}_r$ 在完整联合标准正锥上保正，则

$$
\mathcal E(\rho)=\sum_\mu K_\mu\rho K_\mu^*.
$$

在全部归一态上迹不增，等价于 $\sum_\mu K_\mu^*K_\mu\le I$。完整仪器归一，等价于

$$
\sum_{k,\mu}K_{k\mu}^*K_{k\mu}=I.
$$

**证明。**
在参考中取 $d$ 维子空间，并取 $\lvert\Gamma\rangle =\sum_i\lverti\rangle \otimes\lverti\rangle$。联合保正使 Choi 矩阵
$C_{\mathcal E}=(\mathcal E\otimes\operatorname{id})(\lvert\Gamma\rangle \langle\Gamma\rvert )$
为正。将其谱分解向量重排为矩阵 $K_\mu$，比较矩阵单位即得表示。反向的共轭和在任意参考上保正。迹配对给所列不等式与等式。

这是标准有限维 Choi–Kraus 等价关系，参见 Watrous 定理 2.22。原参考条件必须覆盖全部联合正锥，单有经典参考、乘积态或线性分离不足。原标签 $k$ 与数学 Kraus 索引 $\mu$ 也不能自动合并为可访问的细记录。 [8](#ref-watrous)

### 推论 9.4（排除反射作为可附接的量子过程）

如果原反射也满足完整量子参考条件，就产生矛盾。

**证明。**
Bloch 的一个反射由转置代表。对 Bell 态的一半转置得到 $\tfrac12\operatorname{Swap}$，有特征值 $-1/2$。任意其它反射只相差旋转，结论不变。

这排除某类实际可附接过程，不选择一种绝对坐标手性。若原菜单真的有反射，则该原实例不满足后续完整参考接口，不能通过删去原门声称已经重建。

### 命题 9.5（仪器的有限酉扩张）

任一完整 Kraus 仪器都有一个数学等距扩张

$$
V\psi=\sum_{k,\mu}K_{k\mu}\psi\otimes\lvertk,\mu\rangle ,
\qquad V^*V=I.
$$

在环境读出投影 $Q_k=\sum_\mu\lvertk,\mu\rangle \langlek,\mu\rvert$ 后取偏迹，得到原分支
$\mathcal E_k(\rho)=\sum_\mu K_{k\mu}\rho K_{k\mu}^*$。

**证明。**
由完整性，
$V^*V=\sum_{k,\mu}K_{k\mu}^*K_{k\mu}=I$。
展开 $V\rho V^*$，投影 $Q_k$ 并对环境取迹即得分支。将输入、输出嵌入足够大的同维空间，补齐正交基，可将该等距映射延拓为一个酉算子。反向，任何这种酉扩张和环境读出都给 Kraus 仪器。

任一数学 POVM 也有实现：取 $K_k=\sqrt{E_k}$，便有 $\sum K_k^*K_k=I$。实际原设备是否供应该环境、耦合与读出，是同一原过程接口的实现问题。数学环境索引 $\mu$ 不因此成为实际可读标签。

### 9.4 Lüders 更新的准确前提

### 定理 9.6（理想投影更新）

CP 分支的效果为投影 $P$，并且不扰动每个支撑于 $P$ 的态，则

$$
\mathcal E(\rho)=P\rho P.
$$

**证明。**
$\sum_\mu K_\mu^*K_\mu=P$ 给 $K_\mu=K_\mu P$。对 $\psi\in P\mathcal H$，秩一正和
$\sum_\mu\lvertK_\mu\psi\rangle \langleK_\mu\psi\rvert =\lvert\psi\rangle \langle\psi\rvert$
迫使每项的向量与 $\psi$ 共线。对独立向量及其和用线性，得到 $K_\mu=c_\mu P$、$\sum_\mu|c_\mu|^2=1$。零投影和秩一情形直接包含。

成功概率非零时，条件态为 $P\rho P/\operatorname{Tr}(\rho P)$。只可重复、或仅保持某组基态，不足以推出此定理：支撑内退相干提供反例。

### 9.5 连续可逆过程与 Schrödinger 形式

### 定理 9.7（连续幺正演化）

同一简单块上的连续 CPTP 单参数群，若逆也 CP，则存在自伴 $H$，使

$$
\mathcal E_t(\rho)=U_t\rho U_t^*,\quad
U_t=e^{-itH/\hbar},\quad
i\hbar\dot\psi=H\psi.
$$

相应密度方程为 $\dot\rho=-i[H,\rho]/\hbar$。

**证明。**
令 $F$ 为 Heisenberg 对偶，$S=F^{-1}$。两者都保单位且 CP，故

$$
F(a)^*F(a)\le F(a^*a),\qquad
a^*a\le S(F(a)^*F(a)).
$$

把第一式施加 $S$，与第二式合并，迫使两式取等。$S$ 单射，故
$F(a)^*F(a)=F(a^*a)$。对 $a+b$ 与 $a+ib$ 极化，得到
$F(a)^*F(b)=F(a^*b)$，所以 $F$ 为 $*$-自同构。

有限维连续单参数矩阵群可写成指数，生成元 $\delta$ 是保持 $*$ 的导子。它必为内导子：对矩阵单位，置

$$
B=\sum_i\delta(E_{i1})E_{1i}.
$$

微分恒等式 $E_{kl}E_{i1}=\delta_{li}E_{k1}$，右乘 $E_{1i}$ 并求和，得到
$[B,E_{kl}]=\delta(E_{kl})$。故 $\delta(a)=[B,a]$。
保持 $*$ 又给 $[B+B^*,a]=0$，所以减去一个中心标量后可取 $B^*=-B$。写 $B=iH/\hbar$，即得 Heisenberg 指数式及其 Schrödinger 对偶。直和的有限中心不能被连续群非平凡置换，逐块论证。

该结论给定连续参数后的结构形式，不计算实际时钟、原生成元的速度、具体 $H$ 或 $\hbar$。

### 9.6 两个可检验的理论后果

完整局部 CPTP 操作并遗忘全部结果时，

$$
\operatorname{Tr}_B[(\operatorname{id}\otimes\mathcal E_B)(\rho_{AB})]=\operatorname{Tr}_B\rho_{AB},
$$

由 $\sum K_\mu^*K_\mu=I$ 直接推出无信号性。后选择不属于该命题。

正半内积 $\langle X,Y\rangle_\rho=\operatorname{Tr}(\rho X^*Y)$ 的 Cauchy–Schwarz 不等式给

$$
\operatorname{Var}_\rho(H)\operatorname{Var}_\rho(K)
\ge\left|\frac1{2i}\operatorname{Tr}(\rho[H,K])\right|^2.
$$

不确定性来自同一正比较与非交换乘法，不需要另立一条概率公理。

### 9.7 复合的实质后果：纠缠与 Bell 相关

在两个基本块的标准联合完成中，定义

$$
\lvert\Psi^-\rangle =\frac{\lvert01\rangle -\lvert10\rangle }{\sqrt2}.
$$

它的两个约化态都是 $I/2$，而联合态是秩一投影，不能是乘积态；也不能是乘积态的凸组合，因为秩一正和中的每项必须支撑在同一条射线上。

Pauli 矩阵直接给

$$
\langle\Psi^-|(a\cdot\sigma)\otimes(b\cdot\sigma)|\Psi^-\rangle=-B(a,b).
$$

取 $A_0=\sigma_z,A_1=\sigma_x$，
$B_0=(\sigma_z+\sigma_x)/\sqrt2$、
$B_1=(\sigma_z-\sigma_x)/\sqrt2$，得到

$$
\langle A_0B_0\rangle+\langle A_0B_1\rangle+
\langle A_1B_0\rangle-\langle A_1B_1\rangle=-2\sqrt2.
$$

对共同概率空间中预先给定的 $a_0,a_1,b_0,b_1\in\{\pm1\}$，相同组合
$a_0(b_0+b_1)+a_1(b_0-b_1)$ 的绝对值恒为二，平均后仍不超过二。因此标准联合完成包含超过该共同赋值模型的相关；同时上节已证明完整局部操作不发信号。

这是复合接口与联合正锥的结果，不是单个三维球或 $Q9$ 单独保证原环境中已经存在 Bell 实验。

<a id="section-10"></a>

## 10. 准确证书、近似反例与理论范围

### 10.1 有限矩阵证书并不缩掉原未来

选完整 $\mathfrak g$ 的基 $K_1,\ldots,K_m$，将各 $AK_jA$ 展平成列，得到夹持矩阵 $S_A$。对完整 $n=\dim W$，$Q9$ 等价于存在 $A\in\mathfrak g$ 使

$$
Ae=0,\qquad\operatorname{rank} A=n-1,\qquad\operatorname{rank} S_A=1.
$$

因此可以用非零最大子式与全部二阶子式消失作准确有限证书。其有限性以完整原 $W,\mathfrak g$ 已识别为前提，不能从当前采样足够反推未知未来没有其它方向。

### 定理 10.1（任意近似秩一也不保证完整内容三维）

在 $W=\mathbb R^5,G=SO(5),e=e_5$ 中，取

$$
A_\varepsilon=J_{12}+\varepsilon J_{34},\qquad0<\varepsilon<1.
$$

则 $\ker A_\varepsilon=\mathbb R e$。本例可将夹持视为
$\mathcal C_{A_\varepsilon}:\mathfrak{so}(5)\to\mathfrak{so}(5)$，两边均用 $\kappa=-\frac12\operatorname{Tr}$；其奇异值为

$$
\operatorname{sv}(\mathcal C_{A_\varepsilon})
=\{1,\varepsilon,\varepsilon,\varepsilon,\varepsilon,\varepsilon^2,0,0,0,0\}.
$$

所以 $\sigma_2/\sigma_1=\varepsilon\to0$，但夹持准确秩始终为六，完整 $W$ 始终五维。

**证明。**
$J_{12}$ 方向的夹持系数绝对值为一，$J_{34}$ 方向为 $\varepsilon^2$。连接 $12$ 与 $34$ 两平面的四个斜对称基方向，在夹持下互相置换并各乘 $\pm\varepsilon$。连接 $e_5$ 的四个方向全被消去，得到所列奇异值。

这个模型可由原响应

$$
p(\pm\mid n,m)=\tfrac12(1\pm n\cdot m),
\quad n,m\in S^4,
$$

及全 $SO(5)$ 原可逆控制实现；完整 $V$ 六维、$W$ 五维，来源循环。极限 $A_0$ 的核升为三维，故没有反驳准确 $Q9$。

直观上，第二个转动平面变慢，不等于那两个内容方向消失。这个反例说明任何定量刚性延伸至少要排除这种谱退化；它不证明单独添加谱隙就已充分。该结论与新 C117 对小残差和准确容量的区分一致。

### 10.2 标准量子公理的依赖关系

| 通常的表述 | 本轮中的来源 | 原实例的额外实现关系 |
|---|---|---|
| 复 Hilbert 空间 | 夹持比较与交换子给四实维 $\mathcal Q$；原来源稳定相位给 $\mathbb C_u$，右模为 $\mathbb C^2$ | 原实例是否实现全部完成元素 |
| 纯态射线与相位 | 同一 Hopf 内容的全部振幅恰差 $\mathbb C_u$ 单位相位 | 原相干参考与路径供应 |
| 密度与 Born 律 | 原完整仿射评价由 $\operatorname{Tr}(\rho E)$ 保持；四元数计算给半角平方 | 全部数学混合态、锐效果不自动供应 |
| 复合张量积 | 共同复中心、交换嵌入及乘积张成 | 同一实际联合对象与完整联合正锥 |
| 一般 CP 仪器 | 完整矩阵参考保正、全部分支归一 | 参考和原标签身份须保持 |
| 投影更新 | CP、投影效果、全部支撑态不扰动 | 仅可重复或保一组基态不够 |
| 薛定谔形式 | 连续 CPTP 群与 CP 逆迫出内导子 | 实际时钟、具体 $H$、能标 |

本轮完整建立的是有限维数学理论。$Q9$ 选择最小量子位窗口，不要求每个高维系统都满足它；标准 qutrit 可不含实际 qubit 对象。C127 的原 $D$、原中心、参考和全部对象继续保留，不能用新 $\Phi,R$ 替换它们。 [5](#ref-c127)

无限维、连续位置与动量、无界算子定义域及场论仍需拓扑极限和连续性条件。有限矩阵不能满足 $[Q,P]=i\hbar I$，因为左右取迹不等。本轮没有把有限完成扩写成未证明的无限理论。

### 10.3 内生的准确含义

原响应定义 $W$，原接续定义 $G,\mathfrak g$，原准备定义 $e$，同一作用的顺序合成定义 $\mathcal C_A$。候选只约束这些定义之间的核与像：

$$
\ker A=\mathbb R e,\qquad \dim\mathcal C_A(\mathfrak g)=1.
$$

度量、地址、单频、叉积、相位圈和振幅均在其后出现。但“约束的对象全在 $\Omega$ 内”不证明任意原实例都满足约束。前述反模型同样能在一个整体中定义。

所以这一轮的可证明推进是：把关系输入压缩成一根停轴与一条夹持像；以纯代数得到三维；从夹持系数与交换子构造全部有限量子完成；将该完成与实际原对象连接所需的条件继续写明。这里的新意定位是本系列的回溯表述与证明组合，标准四元数、Hopf 与有限量子定理不被声称为新发现。

<a id="section-11"></a>

## 11. 一段完整白话

在整体里找一种转向，它只让原来那份内容的一根轴不动。再拿任意另一种转向，前后各经过这同一种作用；如果不论中间放什么，最后都只剩同一种作用的不同强弱，那么横向世界就不能藏着第二套独立转法。原来的变换按先后接起来，两份偏转的顺序差会逼出一个真实转动平面；加上那根停住轴，完整窗口正好三维。夹持后剩下多少，给出两份转向的比较；原内容怎样偏，原转向的交换子就怎样给它地址。重复转向到第三次便能约回第一次，所以任意多次重复都只在三项里循环，两份线性读出呈现圆或椭圆。把这套比较和顺序关系合在一起，就得到四个实振幅；原内容不变时允许的转动恰是一圈相位，于是四个实分量自然成为两个复分量。两份振幅相互比较的平方，准确等于原内容的 Born 概率。把这些窗口按共同相位、完整联合结构和参考连接起来，就得到有限量子理论。入口仍只是同一整体内的二元关系：一种作用从两边夹住另一种作用，究竟还会留下多少独立变化。

<a id="references"></a>

## 参考文献

<a id="ref-commit"></a>

### [1]

 trureturing，
[本轮固定提交](https://github.com/the-omega-institute/trureturing/commit/d9880e9f2c329bb3db982f33791419d5d90126b9)，2026-11-04 19:01:29 +0800。

<a id="ref-compare"></a>

### [2]

 trureturing，
[从 $\Omega Q$-008 至本轮的固定比较](https://github.com/the-omega-institute/trureturing/compare/8e15c484cf5786fe69fef0627fd84a63cfeb5942...d9880e9f2c329bb3db982f33791419d5d90126b9)。

<a id="ref-c117"></a>

### [3]

 trureturing，
[C117 固定正文](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)，本轮新增 §§25–29，尤其定理 25.2、命题 25.4 与 27.2。

<a id="ref-fourpath"></a>

### [4]

 trureturing，
[Fourpath Continuation IV](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/docs/develop/theory/QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_IV.md)，定理 49.1、稳定方向松弛及其准确范围。

<a id="ref-c127"></a>

### [5]

 trureturing，
[C123–C127 固定正文](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)，尤其 §§35–40。

<a id="ref-baez"></a>

### [6]

 J. C. Baez，*The Octonions*，
Bull. Amer. Math. Soc. 39 (2002)，145–205，
[作者正文 §2.1](https://math.ucr.edu/home/baez/octonions/node4.html)；四元数乘法表是成熟数学，本文另给所需结合律与表示证明。

<a id="ref-berry"></a>

### [7]

 M. V. Berry，*Quantal phase factors accompanying adiabatic changes*，
Proc. R. Soc. Lond. A 392 (1984)，45–57，
[作者提供的原论文](https://michaelberryphysics.wordpress.com/wp-content/uploads/2013/07/berry120.pdf)。

<a id="ref-watrous"></a>

### [8]

 J. Watrous，*The Theory of Quantum Information*，
[第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，尤其定理 2.22，CP、Choi 与 Kraus 的有限维等价。
