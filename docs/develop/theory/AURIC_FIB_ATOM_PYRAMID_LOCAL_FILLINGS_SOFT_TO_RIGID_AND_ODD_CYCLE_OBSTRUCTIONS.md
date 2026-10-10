# AURIC FIB ATOM 金字塔：从局部填充、软到刚，到全局环路障碍

**Reference input: open.** 本卷完整保存用户供文，包括陈述、证明、表格、例子、代码来源与拟议形式化接口。供文中的“定理”“严格证明”“正式冻结”等语言属于开放参考输入；本卷未新增 Lean、Blueprint、Reg 或 Frozen 声明，不认证物理实现或算法优势。Lean 声明、证明项及其内核核验的公理闭包是本库形式系统内的数学真源。

**来源。** Author kind: mixed user-supplied material; original author and model unknown. Receipt date: 2026-10-10. 来源标识为本会话供文 auric-fib-atom-local-fillings-soft-to-rigid-and-odd-cycle-obstructions。接收原文 SHA-256 为 `5d33d12203c037526ff87e7e82600f24670de86e0690c8edd16f8e807f1c19cc`，原始字节数为 29016。全部原句与公式内容保留，数学分隔符和标题层级作结构规范化，声明地址仅供本文定位。按用户指定，本卷只添加理论正文，不运行消化；没有 atom 或形式化覆盖状态的新增主张。

**历史归属与复用。** 供文对 dev、README 和 PR 的“当前”判断归属其引用的 b40c4b1cddd454c51ede5862bd91c2fac3537b42 等历史快照，不认证交付时移动分支的状态。静态纤维沿用 [Foundational Formulas and Relations](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)、[Boundary Calculus](AURIC_FIB_ATOM_PYRAMID_BOUNDARY_CALCULUS.md) 和 [Output-Resolved Instrument Closure](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)。独立集多面体、全酉模性、树上概率缝合、支持函数及 Steiner 面积公式是既有数学方法；本卷不将其应用或改写宣称为原创定理。

## 编者限定与开放义务

以下限定与供文原句分开，不替代或认证原文陈述。

- **Q1（§§2–5、10）：** 软占用向量是合法刚性状态概率混合的一阶均值；单个金字塔点不是某次填充样本。窗口坐标 X_i、Y_i、Z_i 在概率缝合处应读成对应二值位置的期望，不能与实现样本的 0/1 值互换。纤维宽度可以为零；“唯一隐藏方向”指完整五态仿射映射的核，不表示每个约束后纤维都有可变参数。
- **Q2（§4、接口 B）：** 矩阵 Q 的条目是事件 m=0 上的未归一化联合质量；当 r=1-Z>0 时，条件概率矩阵为 Q/r，条件协方差公式与条件独立等价式在该域使用。r=0 时通常条件律未定义，不能由 Delta=0 推出该事件上的条件独立。Delta 作为“曲率坐标”是命名或类比，没有给出微分几何曲率。
- **Q3（§6）：** 形状模型要求有限整数 k>=3、以同一内心为原点的凸正多边形、非负且固定的尺度 gamma，以及 0<=tau<=1。面积一阶项消失指在 tau=0 展开的线性系数为零；一般 tau>0 时面积导数不为零。单位直径圆的 k=0 代码分支不使用正多边形半径公式。面积二阶响应与概率联合坐标的相似不构成两种参数、操作或资源代价之间的已证同构。
- **Q4（§§7–8、接口 E）：** 冲突图适配器是在固定有限候选姿态宇宙上的抽象模型。必须指定边界容许接触、重叠判定、相同姿态是否属于同一带标号物体，以及每个物体的选择限制。独立集只保证所选姿态两两不冲突；固定物体数、每个物体恰选一个姿态等约束不能从 STAB 自动得到。连续搜索产生的姿态覆盖全部几何可行解仍需另证。
- **Q5（§7）：** 顶点集随参数改变时，STAB 的包含关系在共同宇宙 R^Omega 中将禁用姿态坐标补零后比较。姿态的中心、方向、尺度、形状族和容器坐标系保持对应；仅改变 tau 或嵌套容器尺度。分数占用的“软填充”与几何形状的软化是不同定义，二者的双向箭头需要实际适配器与对应证据，不能仅靠同名软/刚推出。
- **Q6（§8）：** Q(G)=STAB(G) 的模型域为有限简单二分图；TU 论证使用带符号的关联矩阵（或其转置）及整数上下界。保持边界的凸分解要求可行的 0/1 边界面，保留的是均值与该边界；它不保持任意高阶联合律，也不给出几何硬化轨迹、最优装箱值或算法预算优势。
- **Q7（§§9、12–13）：** 奇环半填充证明的是局部边约束不充分。所列奇环不等式是必要约束，不能未经证明宣称它们描述任意图的完整独立集多面体。C5 中 Delta=0 的条件端点律是退化的确定性律；这与全局不可实现不矛盾。Z2 相位描述限于该交替边界支持，不是任意循环的完整 holonomy 判据或物理曲率。
- **Q8（§10、接口 C）：** 路径缝合要求各 q_i 是同一带标号有限路径上的归一化非负局部概率律、合法支持和逐公共二元组的一致边缘。零概率公共状态的任意条件转移只在不可达状态上使用。推广到树状局部节需明确无环的窗口/因子组织及 running-intersection 性质；原冲突图是树不自动证明任意窗口族满足该组织条件。
- **Q9（§§5、11）：** 生成函数与矩阵计数针对带标号位置、有限整数长度和指定边界。周期迹公式在 L>=3 的简单环域使用；它不是按旋转或反射取商后的图案数。FIB 数值权重、位置独立集数量和几何面积仍是不同读数。
- **Q10（§§6–7、14–16）：** 所引 soft-to-rigid 固定提交的形状定义和 README 的比较范围可以用于源级对应；它们不认证本卷拟议有限冲突图适配器、数值接触判定或新装箱证书。程序的搜索经验与几何可行集的数学嵌套必须分别使用。供文的形式化接口是候选工作，物理、生命和黎曼猜想等外推没有因此完成。

## 完整供文

我先给出核心结论：

> AURIC FIB ATOM 金字塔不是五个孤立图案的集合，而是路径图 $P_3$ 的独立集凸包。它的三维坐标只记录三个原子的一阶占用率；同一个金字塔点通常对应一条一维的“隐藏填充纤维”，由 $\kappa$ 参数化。  
>   
> 对路径或更一般的二分冲突图，所有满足局部冲突不等式的软填充都可以分解为刚性填充的概率混合；但一旦出现奇环，局部一致可能无法闭合成全局刚性对象。  
>   
> `soft-to-rigid` 的几何过程可以严格映射到这一结构，但映射发生在“姿态冲突图—独立集凸包”这一层，而不是说圆、正多边形与 FIB 数字本身是同一个物理对象。

因此，最有力的统一框架是：

$$
\text{FIB ATOM 局部状态}
\longrightarrow
\text{独立集}
\longrightarrow
\text{金字塔凸包}
\longrightarrow
\text{边界缝合}
\longrightarrow
\text{全局路径或环路}
\longrightarrow
\text{软到刚的可实现性}.
$$

---

## 1. 先固定记号：指数、数值和物理位置分开

按照你指定的绑定：

$$
F[\mathrm{null}]=\mathrm{null},
\qquad
F[1]=[2],
\qquad
F[2]=[3],
\qquad
F[3]=[5],
\qquad
F[1,3]=[2,5].
$$

这里的 $1,2,3$ 是位置索引，$2,3,5$ 是对应的 FIB 数值。不能把二者混用。

令：

- $u$：位置 $1$，即数值 $2$ 的原子；
- $m$：位置 $2$，即数值 $3$ 的原子；
- $v$：位置 $3$，即数值 $5$ 的原子。

由于相邻位置不能同时被占用，合法二进制填充为：

$$
um=0,
\qquad
mv=0.
$$

因此合法状态只有五个：

| 状态 | 物理位序 $(u,m,v)$ | 金字塔坐标 $(X,Y,Z)=(u,v,m)$ | FIB 值 |
|---|---:|---:|---:|
| $F[\mathrm{null}]$ | $000$ | $(0,0,0)$ | $0$ |
| $F[1]$ | $100$ | $(1,0,0)$ | $2$ |
| $F[2]$ | $010$ | $(0,0,1)$ | $3$ |
| $F[3]$ | $001$ | $(0,1,0)$ | $5$ |
| $F[1,3]$ | $101$ | $(1,1,0)$ | $7=2+5$ |

这里把 $(X,Y,Z)$ 定义成：

$$
X=u,\qquad Y=v,\qquad Z=m.
$$

所以物理位序是：

$$
(u,m,v)=(X,Z,Y).
$$

合法状态的冲突图是三点路径：

$$
1\;-\;2\;-\;3,
$$

也就是位置 $1$ 与 $3$ 可以同时占用，但 $1$ 与 $2$、$2$ 与 $3$ 不能同时占用。

---

## 2. AURIC 金字塔的严格定义

令五个顶点为：

$$
\nu_0=(0,0,0),
$$

$$
\nu_1=(1,0,0),
$$

$$
\nu_2=(0,0,1),
$$

$$
\nu_3=(0,1,0),
$$

$$
\nu_{13}=(1,1,0).
$$

定义 AURIC FIB ATOM 金字塔：

$$
\mathcal P=
\operatorname{conv}
\{\nu_0,\nu_1,\nu_2,\nu_3,\nu_{13}\}.
$$

### theorem 2.1: 定理 1：金字塔的半空间表达

$$
\boxed{
\mathcal P=
\left\{
(X,Y,Z)\in\mathbb R^3:
X\ge 0,\;
Y\ge 0,\;
Z\ge 0,\;
X+Z\le 1,\;
Y+Z\le 1
\right\}.
}
$$

#### 证明

五个顶点都满足：

$$
X\ge0,\qquad Y\ge0,\qquad Z\ge0,
$$

以及：

$$
X+Z\le1,
\qquad
Y+Z\le1.
$$

因此凸包包含在右侧集合中。

反过来，取任意满足这些不等式的点。

如果 $Z=1$，由于：

$$
X+Z\le1,\qquad Y+Z\le1,
$$

必有：

$$
X=Y=0.
$$

此时点就是顶点 $\nu_2$。

现在假设 $0\le Z<1$。令：

$$
u=\frac{X}{1-Z},
\qquad
v=\frac{Y}{1-Z}.
$$

由 $X+Z\le1$ 与 $Y+Z\le1$，得：

$$
0\le u\le1,\qquad 0\le v\le1.
$$

在底面 $Z=0$ 上，有：

$$
(u,v,0)=
(1-u)(1-v)\nu_0
+
u(1-v)\nu_1
+
(1-u)v\nu_3
+
uv\nu_{13}.
$$

于是：

$$
(X,Y,Z)=
(1-Z)(u,v,0)+Z\nu_2.
$$

所以该点属于五个顶点的凸包。

因此两者相等。证毕。

---

### 2.1 横截面结构

固定 $Z=z$，则：

$$
0\le X\le1-z,
\qquad
0\le Y\le1-z.
$$

所以横截面是正方形：

$$
\mathcal P_z=[0,1-z]^2.
$$

底面 $Z=0$ 是由四个端点填充构成的正方形：

$$
\nu_0,\quad \nu_1,\quad \nu_3,\quad \nu_{13}.
$$

顶点 $\nu_2$ 是中间原子 $F[2]=[3]$ 独占时的状态。

因此它确实是一个方形底面的方锥，而不是任意三维多面体。

它的体积为：

$$
\operatorname{Vol}(\mathcal P)=
\int_0^1(1-z)^2\,dz=
\frac13.
$$

这个体积不是主要的组合不变量，但它说明一个事实：中间原子的占用率 $Z$ 越高，两个端点能够同时变化的自由度按平方缩小。

---

## 3. 隐藏填充纤维：为什么一个点不等于一个填充

设五个合法状态的概率分别为：

$$
p_0,p_1,p_2,p_3,p_{13},
$$

对应：

$$
F[\mathrm{null}],F[1],F[2],F[3],F[1,3].
$$

它们满足：

$$
p_0+p_1+p_2+p_3+p_{13}=1.
$$

金字塔坐标是概率的第一阶投影：

$$
X=p_1+p_{13},
$$

$$
Y=p_3+p_{13},
$$

$$
Z=p_2.
$$

定义隐藏变量：

$$
\kappa:=p_{13}.
$$

则概率可以反解为：

$$
p_{13}=\kappa,
$$

$$
p_1=X-\kappa,
$$

$$
p_3=Y-\kappa,
$$

$$
p_2=Z,
$$

$$
p_0=1-X-Y-Z+\kappa.
$$

令：

$$
r:=1-Z.
$$

非负性给出：

$$
\kappa\ge0,
$$

$$
\kappa\le X,
$$

$$
\kappa\le Y,
$$

$$
\kappa\ge X+Y+Z-1.
$$

因此：

### theorem 3.1: 定理 2：隐藏纤维的 Fréchet 区间

固定金字塔点 $(X,Y,Z)$ 后，所有实现它的概率填充恰好由：

$$
\boxed{
\max(0,X+Y+Z-1)
\le
\kappa
\le
\min(X,Y)
}
$$

给出。

等价地：

$$
\boxed{
\kappa_-=
\max(0,X+Y-r),
\qquad
\kappa_+=
\min(X,Y).
}
$$

#### 证明

由：

$$
p_{13}=\kappa\ge0,
$$

得到下界 $0$。

由：

$$
p_1=X-\kappa\ge0,
\qquad
p_3=Y-\kappa\ge0,
$$

得到：

$$
\kappa\le X,
\qquad
\kappa\le Y.
$$

由：

$$
p_0=r-X-Y+\kappa\ge0,
$$

得到：

$$
\kappa\ge X+Y-r.
$$

将所有上下界合并即可。证毕。

---

### 3.1 隐藏纤维的宽度

纤维长度为：

$$
w_\kappa=
\kappa_+-\kappa_-.
$$

可以写成对称形式：

$$
\boxed{
w_\kappa=
\min\{X,Y,r-X,r-Y\}.
}
$$

因此纤维宽度在以下四个边界面上消失：

$$
X=0,
$$

$$
Y=0,
$$

$$
X+Z=1,
$$

$$
Y+Z=1.
$$

这些面就是“填充关系唯一化”的地方。

而在底面内部，例如：

$$
(X,Y,Z)=\left(\frac12,\frac12,0\right),
$$

有：

$$
0\le\kappa\le\frac12.
$$

同一个金字塔点至少有两种完全不同的填充解释：

$$
\frac12\delta_{\mathrm{null}}
+
\frac12\delta_{13},
$$

对应：

$$
\kappa=\frac12,
$$

以及：

$$
\frac12\delta_1
+
\frac12\delta_3,
$$

对应：

$$
\kappa=0.
$$

两者具有相同的一阶坐标：

$$
X=Y=\frac12,\qquad Z=0,
$$

但一个强调“端点共同出现”，另一个强调“两个端点互斥地分开出现”。

---

### 3.2 仿射回路：最根本的隐藏关系

五个顶点之间存在唯一的仿射回路：

$$
\boxed{
\nu_0+\nu_{13}=
\nu_1+\nu_3.
}
$$

展开即：

$$
(0,0,0)+(1,1,0)=
(1,0,0)+(0,1,0).
$$

这正是上面的两个混合分解相同的原因。

在概率空间中，对概率向量施加：

$$
(p_0,p_1,p_2,p_3,p_{13})
\mapsto
(p_0,p_1,p_2,p_3,p_{13})
+
t(1,-1,0,-1,1)
$$

不会改变：

$$
X,\qquad Y,\qquad Z.
$$

因此隐藏纤维的方向是：

$$
\boxed{
(1,-1,0,-1,1).
}
$$

这个方向改变的是二阶联合结构，而不是三个原子的单点占用率。

数值上还有一个对应关系：

$$
0+7=2+5.
$$

但要区分两件事：

- 向量关系 $\nu_0+\nu_{13}=\nu_1+\nu_3$ 是几何仿射关系；
- 数值关系 $0+7=2+5$ 是 FIB 权重关系。

二者相互映照，但不是同一个定理。

---

## 4. $\Delta$：隐藏填充的二阶相关量

把端点占用变量记为 $u,v$。在中间原子未被占用，即 $m=0$ 的条件下，端点联合分布可以写成：

$$
Q=
\begin{pmatrix}
p_0 & p_3\\
p_1 & p_{13}
\end{pmatrix}.
$$

定义：

$$
\boxed{
\Delta:=\det Q=
p_0p_{13}-p_1p_3.
}
$$

代入上面的参数化，得到：

$$
\boxed{
\Delta=
(1-Z)\kappa-XY=
r\kappa-XY.
}
$$

当 $r>0$ 时：

$$
\operatorname{Cov}(u,v\mid m=0)=
\frac{\Delta}{r^2}.
$$

因此：

$$
\Delta=0
$$

当且仅当端点在条件 $m=0$ 下条件独立。

如果：

$$
\Delta>0,
$$

说明 $F[1,3]$ 的联合出现概率高于独立模型的预测。

如果：

$$
\Delta<0,
$$

说明两个端点在软分布中呈现额外的排斥关系。

---

### 4.1 任意局部观测量只通过 $\kappa$ 感受到隐藏关系

设任意函数 $f$ 定义在五个合法状态上：

$$
f_0=f(F[\mathrm{null}]),
\quad
f_1=f(F[1]),
\quad
f_2=f(F[2]),
\quad
f_3=f(F[3]),
\quad
f_{13}=f(F[1,3]).
$$

定义四点差分：

$$
J_f=
f_{13}-f_1-f_3+f_0.
$$

则：

$$
\boxed{
\begin{aligned}
\mathbb E[f]
={}&
f_0
+(f_1-f_0)X
+(f_3-f_0)Y\\
&+(f_2-f_0)Z
+J_f\kappa.
\end{aligned}
}
$$

所以：

- $X,Y,Z$ 控制所有一阶信息；
- $\kappa$ 是唯一的隐藏二阶自由度；
- 只有满足 $J_f\neq0$ 的观测量，才能探测 $\kappa$。

当 $Z<1$ 时，条件独立的规范选择为：

$$
\boxed{
\kappa_0=\frac{XY}{1-Z}.
}
$$

此时：

$$
\Delta=0.
$$

所有其他局部填充都可以写成：

$$
\kappa=\kappa_0+t,
$$

并且：

$$
\Delta=(1-Z)t.
$$

因此，$\Delta$ 是仿射回路方向上的曲率坐标。

---

## 5. FIB 权重与路径独立集生成函数

给三个位置赋权：

$$
w_1=2,\qquad w_2=3,\qquad w_3=5.
$$

一个合法填充的总权重为：

$$
W=2u+3m+5v.
$$

于是五个状态的权重是：

$$
0,\quad2,\quad3,\quad5,\quad7.
$$

加权独立集生成函数为：

$$
\boxed{
Z_{P_3}(q)=
1+q^2+q^3+q^5+q^7.
}
$$

这里：

$$
q^7=q^2q^5
$$

对应联合端点状态 $F[1,3]$。

对一般路径 $P_n$，若第 $i$ 个位置的权重为 $a_i$，则加权生成函数满足：

$$
\boxed{
Z_n(q)=
Z_{n-1}(q)
+
q^{a_n}Z_{n-2}(q).
}
$$

原因是最后一个位置有两种互斥情况：

1. 不选最后一个位置，贡献 $Z_{n-1}$；
2. 选最后一个位置，则倒数第二个位置不能选，贡献 $q^{a_n}Z_{n-2}$。

如果忽略权重，只统计合法二进制词，长度为 $n$ 的路径填充数量为：

$$
\boxed{
F_{n+2},
}
$$

其中：

$$
F_0=0,\qquad F_1=1.
$$

因此，FIB 结构不是因为五个状态“看起来像”斐波那契，而是因为路径上的局部排斥递推直接产生了 Fibonacci 递推。

---

## 6. `soft-to-rigid` 的几何参数化

`soft-to-rigid` 的核心形状可写成如下形式。对一个单位边长的正 $k$ 边形 $P_k$，其内切圆半径为：

$$
\rho_k=
\frac{1}{2\tan(\pi/k)}.
$$

令 $D$ 为单位圆盘，定义软化形状：

$$
\boxed{
S_{\gamma,\tau}=
\gamma\left[(1-\tau)P_k\oplus\tau\rho_kD\right],
\qquad
0\le\tau\le1.
}
$$

其中：

- $\tau=0$：刚性正多边形；
- $\tau=1$：内切圆盘；
- $\gamma$：整体尺度；
- $\oplus$：Minkowski 和。

源代码中的具体实现见 [`engine2d.js`](https://github.com/yoheinakajima/soft-to-rigid/blob/07e3cbd3c4855e5e19344885fbf672c3d7a0f039/engine/engine2d.js)，项目说明见 [`soft-to-rigid README`](https://github.com/yoheinakajima/soft-to-rigid/blob/07e3cbd3c4855e5e19344885fbf672c3d7a0f039/README.md)。

---

### theorem 6.1: 定理 3：软到刚的集合嵌套

若：

$$
0\le\tau_2\le\tau_1\le1,
$$

则：

$$
\boxed{
S_{\gamma,\tau_1}
\subseteq
S_{\gamma,\tau_2}.
}
$$

#### 证明

对单位方向 $n$，支持函数为：

$$
h_{S_{\gamma,\tau}}(n)=
\gamma\left[(1-\tau)h_{P_k}(n)+\tau\rho_k\right].
$$

由于内切圆盘包含于正多边形：

$$
h_{P_k}(n)\ge\rho_k.
$$

因此：

$$
\frac{\partial}{\partial\tau}
h_{S_{\gamma,\tau}}(n)=
\gamma\left(\rho_k-h_{P_k}(n)\right)
\le0.
$$

支持函数随 $\tau$ 增大而减小，所以 $\tau$ 越大，形状越小；也就是：

$$
\tau_1\ge\tau_2
\quad\Longrightarrow\quad
S_{\gamma,\tau_1}\subseteq S_{\gamma,\tau_2}.
$$

证毕。

---

### 6.1 面积变化是严格二次的

设正 $k$ 边形面积为：

$$
A_{P_k}=\frac{k\rho_k}{2}.
$$

令：

$$
\alpha=\gamma(1-\tau),
\qquad
r=\gamma\tau\rho_k.
$$

Steiner 公式给出：

$$
\operatorname{Area}(S_{\gamma,\tau})=
\alpha^2 A_{P_k}
+
\alpha r\,p_{P_k}
+
\pi r^2.
$$

因为：

$$
p_{P_k}=k=\frac{2A_{P_k}}{\rho_k},
$$

代入后，中间的一次项完全抵消，得到：

$$
\boxed{
\operatorname{Area}(S_{\gamma,\tau})=
\gamma^2
\left[
A_{P_k}
+
\left(\pi\rho_k^2-A_{P_k}\right)\tau^2
\right].
}
$$

当 $\gamma=1$ 时：

$$
\boxed{
\frac{\operatorname{Area}(S_{1,\tau})}{A_{P_k}}=
1-\eta_k\tau^2,
}
$$

其中：

$$
\eta_k=
1-\frac{\pi\rho_k^2}{A_{P_k}}.
$$

典型数值为：

| 形状 | $k$ | $\eta_k$ |
|---|---:|---:|
| 三角形 | $3$ | $0.3954002119$ |
| 正方形 | $4$ | $0.2146018366$ |
| 五边形 | $5$ | $0.1351937340$ |
| 六边形 | $6$ | $0.0931003179$ |
| 八边形 | $8$ | $0.0519405510$ |

这里出现了一个与 AURIC $\kappa$ 很有启发性的结构：

- 几何软化的面积投影在一阶上看不到 $\tau$，首个变化项是 $\tau^2$；
- AURIC 金字塔的一阶坐标 $(X,Y,Z)$ 看不到端点的联合关系，必须引入 $\kappa$ 或 $\Delta$ 才能恢复二阶信息。

这不是说 $\tau=\kappa$，也不是说两套理论数值等价；它们的共同结构是：

> 一个更高维对象经过一阶投影后，存在一个隐藏方向，其影响要到二阶或联合观测层面才显现。

---

## 7. 冲突图是两个项目之间的严格桥梁

固定一个有限的姿态集合 $\Omega$。每个姿态 $a\in\Omega$ 表示一个物体中心、方向和形状参数。

对给定 $(\tau,L)$，定义冲突图：

$$
G_{\tau,L}=(V_{\tau,L},E_{\tau,L}),
$$

其中：

- $a\in V_{\tau,L}$：姿态 $a$ 的形状满足容器边界；
- $\{a,b\}\in E_{\tau,L}$：两个姿态对应的形状发生重叠。

一个刚性合法填充就是一个独立集：

$$
I\subseteq V_{\tau,L}.
$$

它的占用向量是：

$$
\chi^I_a=
\begin{cases}
1,&a\in I,\\
0,&a\notin I.
\end{cases}
$$

而软填充是一个分数向量：

$$
x\in[0,1]^{V_{\tau,L}},
$$

满足：

$$
x_a+x_b\le1
\qquad
(\{a,b\}\in E_{\tau,L}).
$$

因此，`soft-to-rigid` 与 AURIC 的对应关系是：

$$
\boxed{
\text{软几何填充}
\longleftrightarrow
\text{冲突图上的分数填充}
}
$$

以及：

$$
\boxed{
\text{刚性几何填充}
\longleftrightarrow
\text{冲突图独立集的指示向量}.
}
$$

---

### theorem 7.1: 定理 4：固定姿态宇宙中的软到刚单调性

若 $\tau_1\ge\tau_2$，并且容器坐标系与姿态集合固定，则：

$$
V_{\tau_2,L}\subseteq V_{\tau_1,L},
$$

并且在共同顶点上：

$$
E_{\tau_1,L}\subseteq E_{\tau_2,L}.
$$

因此：

$$
\boxed{
\operatorname{STAB}(G_{\tau_2,L})
\subseteq
\operatorname{STAB}(G_{\tau_1,L}),
}
$$

其中：

$$
\operatorname{STAB}(G)=
\operatorname{conv}
\{\chi^I:I\text{ 是 }G\text{ 的独立集}\}.
$$

### 解释

从软圆盘逐渐硬化到刚性多边形时：

- 物体变大；
- 原来贴墙合法的姿态可能变成非法；
- 原来不重叠的姿态可能发生重叠；
- 合法独立集的集合只能缩小。

如果容器尺度 $L$ 同时减小，并且容器是嵌套的，那么可行集合也继续缩小。

但必须区分两个命题：

1. **固定候选姿态宇宙下的可行集嵌套**：这是严格定理；
2. **数值搜索程序最后找到哪个局部最优**：这不具有一般单调性。

搜索中的随机扰动、姿态生成、局部下降和重启会改变搜索轨迹。因此，`soft-to-rigid` README 中的实验比较是算法经验，而不是“硬化必然优于刚性直接搜索”的数学定理。该项目 README 报告了多组形状与容器实验，并明确把 hardening 作为一种不同的搜索路径，而不是普遍支配的默认算法；源代码中的目标函数也将重叠、墙面越界和容器尺度分别作为残差或代价处理。

---

## 8. 二分冲突图上的严格刚化定理

定义图 $G=(V,E)$ 的分数填充多面体：

$$
Q(G)=
\left\{
x\in\mathbb R^V:
0\le x_v\le1,\;
x_u+x_v\le1
\;\text{for every }uv\in E
\right\}.
$$

定义独立集凸包：

$$
\operatorname{STAB}(G)=
\operatorname{conv}
\{\mathbf 1_I:I\subseteq V,\ I\text{ independent}\}.
$$

### theorem 8.1: 定理 5：二分图软填充可以概率刚化

若 $G$ 是二分图，则：

$$
\boxed{
Q(G)=\operatorname{STAB}(G).
}
$$

换句话说，每个满足局部冲突不等式的软填充，都可以表示为刚性独立集填充的凸组合：

$$
x=
\sum_I\lambda_I\mathbf 1_I,
\qquad
\lambda_I\ge0,
\qquad
\sum_I\lambda_I=1.
$$

#### 证明

把图的顶点分成二分：

$$
V=A\sqcup B.
$$

对 $B$ 中顶点对应的变量列乘以 $-1$。每条边约束：

$$
x_u+x_v\le1
$$

被转换为一个有向关联矩阵中的差分行。二分图的有向关联矩阵是全酉模的；加入上下界对应的 $\pm I$ 后，约束矩阵仍然全酉模。

因此，当右端项为整数时，$Q(G)$ 的所有极点都是整数点。由于：

$$
0\le x_v\le1,
$$

整数点只能是 $0$ 或 $1$。而边约束又保证这些 $1$ 的位置构成独立集。

所以 $Q(G)$ 的极点恰好是独立集指示向量，得到：

$$
Q(G)=\operatorname{STAB}(G).
$$

证毕。

---

### 8.1 边界保持版本

设 $B\subseteq V$ 是边界顶点，并固定：

$$
x_b=b_b\in\{0,1\},
\qquad b\in B.
$$

如果这个边界赋值本身可以延伸为独立集，那么：

$$
Q(G)\cap\{x_b=b_b:b\in B\}
$$

仍然是可延伸独立集指示向量的凸包。

这意味着：

> 对路径或树上的 AURIC 局部填充，只要边界数据是整数且相容，软填充可以在保持边界的同时随机刚化。

这里的“刚化”是概率意义的：

- 若要求保持每个点的精确占用率，通常需要随机选择一个刚性填充；
- 若要求单次样本就完全相同，则只有原始 $x$ 本身已经是 $0/1$ 向量时才可能。

---

## 9. 奇环是软到刚的真正障碍

二分性不是技术细节，而是刚化定理的边界。

考虑奇环：

$$
C_{2k+1}.
$$

令每个顶点：

$$
x_v=\frac12.
$$

则每条边都满足：

$$
x_u+x_v=1.
$$

所以它满足所有局部边约束，即：

$$
x\in Q(C_{2k+1}).
$$

但是，$C_{2k+1}$ 的任意独立集最多包含 $k$ 个顶点。因此所有刚性独立集的凸组合都满足：

$$
\sum_{v\in C_{2k+1}}x_v\le k.
$$

而半填充点满足：

$$
\sum_{v\in C_{2k+1}}x_v=
\frac{2k+1}{2}=
k+\frac12.
$$

矛盾。

因此：

$$
\boxed{
\frac12\mathbf 1
\in Q(C_{2k+1})
\quad\text{但}\quad
\frac12\mathbf 1
\notin \operatorname{STAB}(C_{2k+1}).
}
$$

必须加入奇环不等式：

$$
\boxed{
\sum_{v\in C_{2k+1}}x_v\le k.
}
$$

这就是“局部填充合法，但全局不能刚化”的最小反例。

---

## 10. 从局部 AURIC 三元组到全局路径

设第 $i$ 个窗口覆盖三个连续位置：

$$
(x_i,x_{i+1},x_{i+2}).
$$

令：

$$
q_i(a,b,c)
$$

为合法三元组 $(a,b,c)\in\{000,100,010,001,101\}$ 上的概率分布。

两个相邻窗口的公共部分是一个二元组：

$$
(b,c).
$$

定义左窗口的右边界边缘：

$$
\mu_i(b,c)=
\sum_a q_i(a,b,c),
$$

以及右窗口的左边界边缘：

$$
\mu_i'(b,c)=
\sum_d q_{i+1}(b,c,d).
$$

### theorem 10.1: 定理 6：路径上的局部缝合定理

一组局部分布 $q_1,\ldots,q_L$ 可以来自某个全局独立二进制词的三元组边缘，当且仅当：

$$
\boxed{
\sum_a q_i(a,b,c)=
\sum_d q_{i+1}(b,c,d)
}
$$

对每一个相邻窗口和每一个合法公共二元组 $(b,c)$ 成立。

#### 充分性证明

先从 $q_1$ 采样第一个三元组。

当已经处于公共状态 $(b,c)$ 时，定义转移概率：

$$
K_i(d\mid b,c)=
\frac{q_{i+1}(b,c,d)}{\mu_i(b,c)}
$$

当 $\mu_i(b,c)>0$ 时成立；当 $\mu_i(b,c)=0$ 时，转移值任意，因为该状态不会被访问。

由此逐步生成：

$$
x_1,x_2,\ldots,x_{L+2}.
$$

由于每个局部三元组都属于：

$$
\{000,100,010,001,101\},
$$

不会出现相邻的 $11$，所以生成的是合法独立词。

重叠边缘相等保证每一步生成的三元组边缘仍然是对应的 $q_i$。证毕。

---

### 10.1 在 AURIC 坐标中的缝合条件

窗口 $i$ 的金字塔坐标记为：

$$
(X_i,Y_i,Z_i),
$$

其中：

$$
X_i=x_i,
\qquad
Y_i=x_{i+2},
\qquad
Z_i=x_{i+1}.
$$

窗口 $i+1$ 的坐标为：

$$
X_{i+1}=x_{i+1},
\qquad
Y_{i+1}=x_{i+3},
\qquad
Z_{i+1}=x_{i+2}.
$$

所以公共边界的匹配条件为：

$$
\boxed{
Z_i=X_{i+1},
\qquad
Y_i=Z_{i+1}.
}
$$

这说明：

- $Z_i$ 与下一个窗口的 $X_{i+1}$ 相接；
- $Y_i$ 与下一个窗口的 $Z_{i+1}$ 相接；
- 局部隐藏变量 $\kappa_i$ 不直接出现在相邻窗口的公共二元边缘中。

因此，$\kappa_i$ 可以在一定范围内改变，而不破坏一阶边界缝合；真正限制它的是非负性、全局周期条件和更高阶相关约束。

---

## 11. 转移矩阵、Fibonacci 增长和周期闭合

按状态顺序：

$$
[\mathrm{null},1,2,3,13],
$$

定义从窗口状态 $s=(a,b,c)$ 到：

$$
t=(b,c,d)
$$

的转移矩阵：

$$
M=
\begin{pmatrix}
1&0&0&1&0\\
1&0&0&1&0\\
0&1&0&0&1\\
0&0&1&0&0\\
0&0&1&0&0
\end{pmatrix}.
$$

开放的 $L$ 个三元窗口覆盖长度 $L+2$ 的独立词，因此：

$$
\boxed{
\mathbf 1^\top M^{L-1}\mathbf 1=
F_{L+4}.
}
$$

这给出了 AURIC 局部状态到 Fibonacci 增长的直接线性代数表达。

如果要求周期闭合，则使用迹：

$$
\boxed{
\operatorname{tr}(M^L)=
F_{L-1}+F_{L+1}
}
$$

对于 $L\ge3$，右侧是 Lucas 数，也是长度为 $L$ 的环上独立集数量。

---

## 12. C5 的局部一致、全局失败示例

对五个周期窗口，令每一个局部分布都相同：

$$
q_i=
\frac12\delta_{101}
+
\frac12\delta_{010}.
$$

每个窗口都局部合法。

其公共边缘在两个状态之间均匀分布：

$$
10\longleftrightarrow01.
$$

因此相邻窗口边缘完全一致，所有局部缝合条件都成立。

但它不能来自一个全局 $C_5$ 的独立集概率分布。

原因是每个顶点的占用率都是：

$$
\frac12.
$$

所以全局期望占用数为：

$$
5\cdot\frac12=\frac52.
$$

然而 $C_5$ 的任何独立集最多只能占用两个顶点：

$$
|I|\le2.
$$

因此不可能存在这样的全局刚性分布。

这个例子有一个更细的性质：每个局部窗口的 AURIC 坐标为：

$$
(X,Y,Z)=\left(\frac12,\frac12,\frac12\right),
$$

并且：

$$
\kappa=\frac12.
$$

于是：

$$
\Delta=
(1-Z)\kappa-XY=
\frac12\cdot\frac12-\frac12\cdot\frac12=
0.
$$

也就是说：

> 局部的 $\Delta$ 可以完全为零，局部端点甚至条件独立，但全局仍然可能因为奇环相位而无法闭合。

这里有两个独立层次：

1. $\Delta$：局部隐藏相关；
2. 环路奇偶性：全局 holonomy 障碍。

在这个 C5 例子中，局部转移把边界相位：

$$
10\leftrightarrow01
$$

交换一次。绕奇环五次后，相位翻转，不能回到初始状态。绕两圈才闭合，这就是一个 $\mathbb Z_2$ 型的相位障碍。

---

## 13. “填充关系”的完整层级

现在可以把 AURIC FIB ATOM 的结构分成五层。

## 第一层：原子层

三个位置：

$$
1,\;2,\;3
$$

对应三个数值：

$$
2,\;3,\;5.
$$

局部禁止相邻占用：

$$
um=0,\qquad mv=0.
$$

## 第二层：合法状态层

五个状态：

$$
\mathrm{null},\;1,\;2,\;3,\;13.
$$

它们是路径 $P_3$ 的全部独立集。

## 第三层：金字塔层

五个状态的凸包是：

$$
\mathcal P=
\{X,Y,Z\ge0,\;X+Z\le1,\;Y+Z\le1\}.
$$

它记录的是平均占用率，而不是完整概率律。

## 第四层：隐藏纤维层

同一个 $(X,Y,Z)$ 对应：

$$
\kappa\in[\kappa_-,\kappa_+].
$$

仿射回路：

$$
\nu_0+\nu_{13}=\nu_1+\nu_3
$$

产生唯一隐藏方向。

## 第五层：全局缝合层

相邻窗口必须满足：

$$
Z_i=X_{i+1},
\qquad
Y_i=Z_{i+1}.
$$

路径上这些条件足以构造全局分布；周期环上还需要额外的 holonomy 闭合条件。

这解释了为什么“局部合法”与“全局可实现”不是同一个概念。

---

## 14. 与 trureturing 当前进展的对应

我按 `trureturing` 当前 `dev` 分支检查到的头部提交是：

- [`b40c4b1`](https://github.com/the-omega-institute/trureturing/commit/b40c4b1cddd454c51ede5862bd91c2fac3537b42)，时间为 2026-10-10；
- 相关理论文档包括 [`AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md`](https://github.com/the-omega-institute/trureturing/blob/b40c4b1cddd454c51ede5862bd91c2fac3537b42/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)、边界演算、局部重构、相关与原生延拓、内蕴分类和隐藏关系统计等文件。

最近几批提交可以这样理解：

| 当前方向 | 对 AURIC 金字塔的意义 |
|---|---|
| [FIB 白盒卷 66.17/66.19 与 dyadic 前缀尾工具](https://github.com/the-omega-institute/trureturing/commit/0916b99b4223dc2177bf422a50a95f4f4c18d54d) | 把局部相位、有限前缀和尾部边界变成可计算对象 |
| [return compatibility stability](https://github.com/the-omega-institute/trureturing/commit/a8e0ab756490c6e7dc9822b40f4070a223d25242) | 研究边界变化如何稳定地传播到返回值与预测纤维 |
| [Hance 24-cell preparation-noncontextuality threshold](https://github.com/the-omega-institute/trureturing/commit/72c1606a3669ac10e5e21ee0cac1115a99145511) | 将局部非语境性、阈值和全局一致性的边界推进到更复杂的有限结构 |
| 当前头部的 weighted sign theorem / Robin tail gap 合并 | 复用已证明的加权符号定理，同时保留真实剩余缺口，而不是用形式化重写掩盖它 |

GitHub 的当前 PR 列表也显示，项目正在把 AURIC FIB 金字塔连接到 escape dynamics、prediction fibers、typed bridge 和 thermodynamic action 等更高层接口。[GitHub](https://github.com/the-omega-institute/trureturing/pulls?utm_source=chatgpt.com)

项目 README 的方法论与这里的推导完全一致：它强调逻辑依赖、区分、观察者恢复和可检查证明；同时明确提醒，局部一致不保证全局一致，有限树上的延拓定理与有环结构必须分开处理，并把 Lean 源和证明项视为权威对象。[GitHub](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com)

因此，最自然的下一步不是再增加一层比喻，而是把上面的对象正式冻结为可检查接口。

---

## 15. 建议正式冻结的定理接口

## 接口 A：局部金字塔

正式证明：

$$
\mathcal P=
\{X,Y,Z\ge0,\;X+Z\le1,\;Y+Z\le1\}.
$$

并导出：

$$
\kappa_-=
\max(0,X+Y+Z-1),
\qquad
\kappa_+=
\min(X,Y).
$$

## 接口 B：隐藏相关

定义：

$$
\Delta=(1-Z)\kappa-XY.
$$

证明：

$$
\Delta=0
\iff
u\perp v\mid(m=0).
$$

同时记录仿射回路方向：

$$
(1,-1,0,-1,1).
$$

## 接口 C：路径刚化

对任意路径或树上的局部概率节，若公共边缘一致，则存在全局概率节；并且可以通过有限流分解算法提取刚性样本。

## 接口 D：奇环证书

对 $C_{2k+1}$，输出证书：

$$
x_v=\frac12,
$$

满足全部边约束，却违反：

$$
\sum_vx_v\le k.
$$

这提供一个最小的“局部通过、全局失败”反例。

## 接口 E：几何冲突图适配器

对 `soft-to-rigid` 的候选姿态集合，定义：

$$
(\tau,L)
\mapsto
G_{\tau,L}.
$$

证明：

$$
\tau_1\ge\tau_2
\Longrightarrow
\operatorname{STAB}(G_{\tau_2,L})
\subseteq
\operatorname{STAB}(G_{\tau_1,L})
$$

在固定姿态宇宙和嵌套容器假设下成立。

这一步把几何数值实验变成可以接入 AURIC 组合核的有限图证书。

---

## 16. 可以明确说出的结论与暂时不能说出的结论

已经可以严格证明的部分是：

1. AURIC 五状态正是路径 $P_3$ 的独立集；
2. 它们的凸包是一个方锥；
3. 每个金字塔点的隐藏填充由 $\kappa$ 的 Fréchet 区间给出；
4. $\Delta$ 是唯一的局部二阶端点相关量；
5. 路径和树上的局部一致可以延拓为全局概率填充；
6. 奇环会产生局部到全局的刚化障碍；
7. `soft-to-rigid` 的几何硬化在固定冲突图宇宙中对应可行独立集族的单调收缩；
8. 几何面积的软化响应是严格二次的，而 AURIC 的隐藏纤维是一阶投影丢失的联合自由度。

仍然不能直接推出的部分是：

- 不能把 $\tau$ 直接等同于 $Z$ 或 $\kappa$；
- 不能从局部 AURIC 金字塔直接推出一个几何装箱最优值；
- 不能把 C5 的组合 holonomy 自动解释成物理时空中的真实曲率；
- 不能把项目中的逻辑结构直接宣传成黎曼猜想证明或物理理论完成。

更准确的统一说法是：

> `soft-to-rigid` 提供了从连续几何到冲突图的外层机制；AURIC FIB ATOM 金字塔提供了每个局部冲突单元的精确概率几何；路径定理说明无环边界可以缝合，奇环定理说明全局闭合需要额外的相位证书；$\kappa$ 和 $\Delta$ 则刻画一阶投影隐藏的局部联合信息。

这使“填充关系”不再只是图案之间的视觉类比，而成为一条可证明的结构链：

$$
\boxed{
\text{原子排斥}
\Rightarrow
\text{独立集}
\Rightarrow
\text{金字塔}
\Rightarrow
\text{隐藏纤维}
\Rightarrow
\text{边界缝合}
\Rightarrow
\text{树上刚化}
\Rightarrow
\text{奇环障碍}
\Rightarrow
\text{几何软到刚冲突图}.
}
$$

## 追加锚（本行以下为增补区）
