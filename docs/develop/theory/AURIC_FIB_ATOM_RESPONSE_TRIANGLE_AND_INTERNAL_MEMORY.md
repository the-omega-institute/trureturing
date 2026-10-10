# Auric FIB-ATOM：三角关系的生成、边界几何与内部记忆

**来源与范围。** 本卷固定读取快照 `05b2af2`，把 FIB 五模式动作图、正权二次响应、边界消元和明确加入的内部松弛状态放在同一模型链中。Kron 消元是外部经典工具；新增内容是将它具体接到当前五模式来源与后续可区分性。所有松弛质量、时间常数和能量方程都是额外模型数据，不是原生 FIB 语法自动供应的物理定律。本文是参考输入，Lean 才是仓库数学真值来源；本文不声称 Lean 已验证。

## 1. 五模式的动作边、混合棱与响应边

记

$$
O=\mathsf F[\varnothing],\quad L=\mathsf F[1],\quad T=\mathsf F[2],\quad R=\mathsf F[3],\quad J=\mathsf F[1,3].
$$

占位规则为 $xz=yz=0$。若额外规定一步只翻转一个占位且结果合法，则动作图的边是

$$
\boxed{O-L,\quad L-J,\quad J-R,\quad R-O,\quad O-T.}
$$

这是正方形加一条支边。它不同于金字塔凸包的八条几何棱，也不同于原生高到低读者的窗口输入。

### theorem 1.1: 三种边具有不同语义

**Claim status: open.** 概率混合的棱、允许动作的边和后续响应中的有效耦合是三个不同关系对象。特别地，消去动作图节点所得的有效边不自动成为原生 FIB 动作。

**说明。** 本卷的响应边只服务于声明的二次模型；它们不能反向改写五模式合法性。

## 2. 相对读数的二次响应

### 定义 2.1：加权边差能量

在有限连通无向图上，每条边赋正权 $c_{ij}>0$，节点读数为 $u_i\in\mathbb R$。定义

$$
\mathcal E(u)=\frac12\sum_{\{i,j\}}c_{ij}(u_i-u_j)^2.
$$

图 Laplacian 为 $L$ 时，$\mathcal E(u)=u^{\mathsf T}Lu/2$，响应为 $j=Lu$。因此 $\sum_i j_i=0$，而

$$
\mathcal E(u+\lambda\mathbf1)=\mathcal E(u).
$$

### theorem 2.2: 读数反号只改变响应方向

**Claim status: open.** $u\mapsto-u$ 给出 $j\mapsto-j$ 且 $\mathcal E\mapsto\mathcal E$。

**证明。** Laplacian 响应是一次式，边差能量是二次式。证毕。

本节的“反”是读数差的方向反转，不是五模式取补，也不是凸区域变凹区域。

## 3. 消去一个共同节点会生成完整三角耦合

### 定义 3.1：正权星形

一个内部变量 $y$ 连接 $m$ 个边界变量 $u_1,\ldots,u_m$，权重为 $c_i>0$：

$$
\mathcal E(u,y)=\frac12\sum_{i=1}^mc_i(u_i-y)^2.
$$

边界能量定义为 $\mathcal E_\partial(u)=\min_y\mathcal E(u,y)$。

### theorem 3.2: 星形消元公式

**Claim status: open.** 令 $C=\sum_i c_i$。则唯一内部极小点为

$$
\boxed{y_* = \frac{\sum_i c_i u_i}{C}}
$$

且

$$
\boxed{
\mathcal E_\partial(u)=\frac1{2C}\sum_{i<j}c_ic_j(u_i-u_j)^2.
}
$$

有效边权为 $g_{ij}=c_ic_j/C$。

**证明。** 对 $y$ 求导得到 $Cy-\sum_i c_iu_i=0$。代入并使用加权平方差恒等式

$$
\sum_i c_i u_i^2-\frac{(\sum_i c_i u_i)^2}{C}
=\frac1C\sum_{i<j}c_ic_j(u_i-u_j)^2
$$

即可。证毕。

所以两个边界端点生成一条有效边，三个端点生成三角耦合，四个端点生成六条两两耦合。后者的六项仍只由四个内部臂权生成。

## 4. 三角耦合的共同节点反演

### theorem 4.1: 正三角耦合唯一反演为三臂星形

**Claim status: open.** 给定 $g_{12},g_{13},g_{23}>0$，存在唯一的 $c_1,c_2,c_3>0$ 使

$$
g_{ij}=\frac{c_ic_j}{c_1+c_2+c_3}.
$$

具体为

$$
\boxed{c_1=g_{12}+g_{13}+\frac{g_{12}g_{13}}{g_{23}}},
$$
$$
\boxed{c_2=g_{12}+g_{23}+\frac{g_{12}g_{23}}{g_{13}}},
\qquad
\boxed{c_3=g_{13}+g_{23}+\frac{g_{13}g_{23}}{g_{12}}}.
$$

**证明。** 令 $a_1=\sqrt{g_{12}g_{13}/g_{23}}$，并循环定义 $a_2,a_3$。则 $g_{ij}=a_ia_j$。取 $c_i=a_i(a_1+a_2+a_3)$，得到所需权；反向由三个两两乘积唯一决定正的 $a_i$。证毕。

同一个三角边界二次响应可以来自直接三角图或仅含一个共同内部点的树。静态边界实验无法从这份响应函数中恢复内部拓扑。

## 5. 四个边界的共同来源约束

### theorem 5.1: 四边界星形的乘积检验

**Claim status: open.** 六个严格正的耦合来自一个正权共同节点（且没有另加直接边）当且仅当

$$
\boxed{g_{12}g_{34}=g_{13}g_{24}=g_{14}g_{23}.}
$$

**证明。** 必要性由 $g_{ij}=c_ic_j/C$ 直接得到。反向先由前三个耦合恢复 $a_1,a_2,a_3$，令 $a_4=g_{14}/a_1$；两项乘积条件保证 $g_{24}=a_2a_4$ 与 $g_{34}=a_3a_4$，再取 $c_i=a_i\sum_j a_j$。证毕。

一般 $m$ 个边界端点时，$m$ 个臂权生成 $m(m-1)/2$ 个耦合，局部独立相容约束数为

$$
\boxed{\frac{m(m-3)}2}.
$$

三边界是参数临界情形，四边界开始有共同来源的可检验约束。

## 6. 响应距离产生锐角与单纯形体积

### 定义 6.1：边界响应距离

在端点 $i$ 注入单位响应、在 $j$ 提取单位响应、其余端点净响应为零，定义

$$
R_{ij}=u_i-u_j,\qquad d_{ij}=\sqrt{R_{ij}}.
$$

### theorem 6.2: 星形响应必为锐角度量

**Claim status: open.** 令 $r_i=1/c_i$。则

$$
\boxed{R_{ij}=r_i+r_j.}
$$

三端点在端点 $i$ 的余弦分子为

$$
\boxed{\frac{d_{ij}^2+d_{ik}^2-d_{jk}^2}{2}=r_i>0,}
$$

故响应三角形三个角均锐。

**证明。** 无净响应的其他端点与内部节点等电位；单位响应的总差是 $1/c_i+1/c_j$。再用内积余弦公式。证毕。

反过来，任意非退化锐角三角形给出正的 $r_i$，从而唯一恢复这份星形响应。钝角需要某个 $r_i<0$，因此不属于正权模型。

### theorem 6.3: 响应面积与一般单纯形体积

**Claim status: open.** 三端点面积满足

$$
\boxed{4A^2=r_1r_2+r_1r_3+r_2r_3.}
$$

一般 $m$ 端点的 $(m-1)$ 维单纯形体积为

$$
\boxed{
V_{m-1}^2=
\frac{(\prod_{i=1}^m r_i)(\sum_{i=1}^m r_i^{-1})}{((m-1)!)^2}.
}
$$

**证明。** 以第 $m$ 点为参考，差向量 Gram 矩阵为 $G_{ij}=\delta_{ij}r_i+r_m$。矩阵行列式引理给出

$$
\det G=(\prod_i r_i)(\sum_i r_i^{-1}),
$$

再除以 $((m-1)!)^2$。三点情形是同一公式的 $m=3$ 特例。证毕。

## 7. 五模式动作图的空节点消元

回到动作图 $O-L-J-R-O$ 与支边 $O-T$。保留边界 $B=(L,R,J,T)$，将 $O$ 作为内部变量，并把五条原边权均取一。

### theorem 7.1: FIB 空模式生成边界三角耦合

**Claim status: open.** 内部极小点为

$$
\boxed{u_O=(u_L+u_R+u_T)/3.}
$$

消去 $O$ 后，$L,R,T$ 之间出现三条权重 $1/3$ 的有效边，$L-J$ 与 $R-J$ 两条单位边保留。按 $(L,R,J,T)$ 排列，边界 Laplacian 为

$$
\boxed{
\Lambda=\frac13
\begin{pmatrix}
5&-1&-3&-1\\
-1&5&-3&-1\\
-3&-3&6&0\\
-1&-1&0&2
\end{pmatrix}.
}
$$

**证明。** 对 $O$ 的三条单位连接应用 theorem 3.2，再加上原有 $L-J,R-J$ 两条边。证毕。

消元前后静态边界响应完全相同；图的独立闭环数可以改变，因此静态边界实验不必恢复内部拓扑。

### theorem 7.2: 响应四面体不等于占位金字塔

**Claim status: open.** 该边界的有效电阻矩阵为

$$
R_{ij}=\begin{pmatrix}
0&1&3/4&7/4\\
1&0&3/4&7/4\\
3/4&3/4&0&2\\
7/4&7/4&2&0
\end{pmatrix}.
$$

以 $J$ 为参考，三条差向量 Gram 矩阵为

$$
G=\begin{pmatrix}3/4&1/4&1/2\\1/4&3/4&1/2\\1/2&1/2&2\end{pmatrix},
$$

所以 $\det G=3/4$，响应四面体体积平方为

$$
\boxed{V_{\mathrm{resp}}^2=\frac1{48}.}
$$

占位均值金字塔的坐标体积仍为 $1/3$。两个数来自不同读口，不代表同一个物理空间。

## 8. Schur 补是完整的静态边界

### theorem 8.1: 二次响应的顺序无关消元

**Claim status: open.** 对内部、边界分块

$$
L=\begin{pmatrix}L_{BB}&L_{BI}\\L_{IB}&L_{II}\end{pmatrix},
$$

若每个内部连通分量连接边界，则

$$
\boxed{\Lambda=L_{BB}-L_{BI}L_{II}^{-1}L_{IB}}
$$

且

$$
\boxed{\min_{u_I}\mathcal E(u_B,u_I)=\tfrac12u_B^{\mathsf T}\Lambda u_B.}
$$

**证明。** 固定边界后内部二次型严格凸，驻点满足 $L_{II}u_I+L_{IB}u_B=0$；解出并代回。对多个内部块，逐次最小化与联合最小化相同。证毕。

前提是没有复制仍需共同满足的接缝变量，也没有删掉后续仍会读取的关系。最小化加法与概率求和不是同一种数值语义，不能只因都能写成矩阵就互换。

## 9. 动态内部状态留下记忆核

静态边界等价并不保证动态等价。现在明确加入质量 $m>0$ 与松弛方程

$$
m\dot y=\sum_i c_i u_i-Cy,
\qquad
j_i=c_i(u_i-y),
\qquad C=\sum_i c_i.
$$

### theorem 9.1: 消去动态内部变量得到卷积记忆

**Claim status: open.** 令 $\tau=m/C$，则

$$
\boxed{y(t)=e^{-t/\tau}y(0)+\frac1m\int_0^t e^{-(t-s)/\tau}\sum_i c_i u_i(s)\,ds}
$$

并且

$$
\boxed{j_i(t)=c_i u_i(t)-c_i e^{-t/\tau}y(0)-\frac{c_i}{m}\int_0^t e^{-(t-s)/\tau}\sum_jc_j u_j(s)\,ds.}
$$

**证明。** 对一阶线性微分方程使用积分因子，再代入 $j_i=c_i(u_i-y)$。证毕。

同一个当前边界输入，因不同 $y(t)$ 可产生不同响应。取三条单位连接、$y(0)=0$、$u=(1,0,0)$，则

$$
y(t)=\frac13(1-e^{-3t/m}),
$$

初始响应为 $(1,0,0)$，长期响应为 $(2/3,-1/3,-1/3)$。静态三角等效只能给长期关系，不能免费重现暂态。

### theorem 9.2: 一个内部状态产生共同极点与秩一修正

**Claim status: open.** 对零初始条件的 Laplace 变换，记 $c=(c_1,\ldots,c_m)^{\mathsf T}$，则

$$
\boxed{\Lambda(s)=\operatorname{diag}(c_i)-\frac{cc^{\mathsf T}}{C+ms}}
$$

以及

$$
\boxed{\Lambda(s)-\Lambda(0)=\frac{ms}{C(C+ms)}cc^{\mathsf T}.}
$$

**证明。** 变换后 $(C+ms)y(s)=c^{\mathsf T}u(s)$，代回边界响应。证毕。

所以所有频率响应共享同一松弛时间 $m/C$ 和同一秩一方向 $cc^{\mathsf T}$；不满足者不能由一个这样的内部节点解释。

暂态守恒为

$$
\boxed{\sum_i j_i=m\dot y,}
$$

平衡时才恢复静态的零和。并且

$$
\boxed{\frac{d\mathcal E}{dt}=\sum_i j_i\dot u_i-\frac1m\left(Cy-\sum_i c_i u_i\right)^2.}
$$

耗散来自新声明的松弛方程，不是静态几何自动证明的时间箭头。

## 10. 同一二次递归中的 Fibonacci 与黄金比例

定义串并联递归

$$
R_0=1,
\qquad
R_{n+1}=1+\frac{R_n}{1+R_n}=\frac{2R_n+1}{R_n+1}.
$$

### theorem 10.1: 单位串并联递归产生隔项 Fibonacci 比值

**Claim status: open.** 有

$$
\boxed{R_n=\frac{F_{2n+2}}{F_{2n+1}}},
\qquad
R_n\to\varphi.
$$

**证明。** 代入归纳假设并使用 Fibonacci 递推：

$$
R_{n+1}=\frac{2F_{2n+2}+F_{2n+1}}{F_{2n+2}+F_{2n+1}}=\frac{F_{2n+4}}{F_{2n+3}}.
$$

正固定点满足 $R=1+R/(1+R)$，即 $R^2=R+1$。分式更新矩阵为

$$
\begin{pmatrix}2&1\\1&1\end{pmatrix}=\begin{pmatrix}1&1\\1&0\end{pmatrix}^{2}.
$$

这说明共享的是代数递归，不是串并联过程已经成为原生 $\rho$ 操作。若单位串联与并联参数改为 $a,b$，固定点变为

$$
\boxed{R_*=(a+\sqrt{a^2+4ab})/2,}
$$

所以黄金比例依赖于该明确组合规则。

## 11. 边界化的限制与共同来源纪律

近期几何卷关于特定树、近单位边长和平面接地合同的不可实现性，只针对其明确假设，不推出一般树图都不可平面绘制。本卷同样只推出声明模型内的结论：

$$
\boxed{\text{静态边界等价}\not\Rightarrow\text{内部几何等价}\not\Rightarrow\text{动态来源等价}.}
$$

若内部状态还会参与未来作用，就不能在边界化时替换成“无记忆的新副本”。量子共同环境的连续两次作用也遵守这一共同来源纪律，但实值松弛方程不等同于量子动力学。

## 追加锚（本行以下为增补区）
