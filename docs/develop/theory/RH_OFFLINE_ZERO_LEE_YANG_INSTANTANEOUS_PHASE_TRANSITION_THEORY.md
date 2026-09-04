# RH 离线零点时刻的 Lee–Yang 横向谱相变理论

## 摘要

本文研究一个严格的条件问题：假设 completed Riemann 型函数存在离开临界线的零点，那么沿谱高度扫描时，第一次遇到离线零点的那个高度究竟发生了什么。

本文不证明黎曼猜想，也不假定离线零点存在。本文建立的是一个纯数学理论：把“离线零点的那个时刻像相变”分解为反射相分裂、横向能隙闭合、Lee–Yang 径向缺陷、Mahler 自由能跳跃、局部相位涡旋以及标量层对关系层失去强制性的统一结构。

核心结论是：若

$$
\rho_*=\frac12+\delta_*+it_*,
\qquad \delta_*\ne0,
$$

是一个离线零点，则在同一高度 $t_*$ 必有反射零点

$$
\rho_*^\sharp=\frac12-\delta_*+it_*.
$$

在 Cayley–Lee–Yang 坐标中，这两个零点位于同一辐角、互为倒数的两条半径上。若该高度的中心点不是零点，则横向零能相从反射固定点分裂为一对 $\mathbb Z_2$ 对称的离轴相。若该零点是单零点，则可见能量在该处按二次律闭合，复相位发生 $\pi$ 翻转，有限分辨率观察者看到一对短暂出现的 near-zero phase bubbles。

更强地，若黎曼猜想为假，则第一离线高度 $T_{\mathrm{off}}$ 存在。三个累积序参量在该高度第一次变为正：最大横向位移、离线零点计数和 Cayley 根族的对数 Mahler 测度。与此同时，一个有限 prime-frequency 关系层仍具有严格正的双曲横向能量

$$
\sinh^2\!\left(\delta_*\log\frac qp\right)>0.
$$

因此，离线零点时刻可以严格描述为：标量零能闭合，而二体关系层仍保留非零横向信息。真正尚未闭合的 RH 承重桥，是把这一 prime-side 关系能量无条件运输到 zero-side 离线奇能量，并证明 completed prime–Gamma 系统禁止该关系信息在标量完成中永久逃逸。

---

# 1. completed 反射系统

## 1.1 基本函数类

固定一个非零整函数

$$
\Xi:\mathbb C\to\mathbb C
$$

满足两条对称律：

$$
\boxed{\Xi(s)=\Xi(1-s),}
\tag{1.1}
$$

$$
\boxed{\Xi(\overline s)=\overline{\Xi(s)}.}
\tag{1.2}
$$

Riemann completed xi 函数属于这一类。令中心化变量

$$
u=s-\frac12,
$$

并定义

$$
F(u):=\Xi\!\left(\frac12+u\right).
$$

则

$$
F(-u)=F(u),
\qquad
F(\overline u)=\overline{F(u)}.
\tag{1.3}
$$

第一条是关于中心的偶对称，第二条是实结构。

## 1.2 横向谱切片

对 $t,\delta\in\mathbb R$，定义

$$
\boxed{
X(t,\delta)
:=
\Xi\!\left(\frac12+\delta+it\right)
=F(\delta+it).
}
\tag{1.4}
$$

这里：

- $t$ 是沿临界线方向的谱高度；
- $\delta=\Re s-\tfrac12$ 是垂直于临界线的横向坐标。

定义非负可见能量

$$
\boxed{
V(t,\delta):=|X(t,\delta)|^2.
}
\tag{1.5}
$$

### 定理 1.1　同高度反射共轭律

对任意 $t,\delta\in\mathbb R$，

$$
\boxed{
X(t,-\delta)=\overline{X(t,\delta)}.
}
\tag{1.6}
$$

从而

$$
\boxed{
V(t,-\delta)=V(t,\delta).
}
\tag{1.7}
$$

#### 证明

由实结构，

$$
\overline{F(\delta+it)}=F(\delta-it).
$$

再由偶对称，

$$
F(\delta-it)=F(-\delta+it).
$$

故得式 (1.6)，取模平方即得式 (1.7)。

---

# 2. 离线零点时刻作为反射相分裂

## 2.1 横向零相纤维

定义高度 $t$ 上的横向零相集合

$$
\mathcal P_t
:=
\left\{
\delta\in\left(-\frac12,\frac12\right):
X(t,\delta)=0
\right\}.
\tag{2.1}
$$

由定理 1.1，

$$
\boxed{
\delta\in\mathcal P_t
\Longleftrightarrow
-\delta\in\mathcal P_t.
}
\tag{2.2}
$$

所以每一条横向零相纤维都是 $\mathbb Z_2$ 对称的。

## 2.2 离线事件

称

$$
(t_*,\delta_*),
\qquad
\delta_*\ne0,
\qquad
X(t_*,\delta_*)=0,
\tag{2.3}
$$

为一个正高度离线谱事件。

### 定理 2.1　同高度反射零点对

若 $(t_*,\delta_*)$ 是离线谱事件，则

$$
\boxed{
X(t_*,\delta_*)
=
X(t_*,-\delta_*)
=0.
}
\tag{2.4}
$$

因此同一谱高度上至少出现两个互异横向零相。

#### 证明

由定理 1.1，

$$
X(t_*,-\delta_*)
=
\overline{X(t_*,\delta_*)}
=0.
$$

又因 $\delta_*\ne0$，两点互异。

## 2.3 中心分离

若进一步满足

$$
X(t_*,0)\ne0,
\tag{2.5}
$$

则

$$
V(t_*,0)>0,
$$

而

$$
V(t_*,\pm\delta_*)=0.
$$

### 定理 2.2　反射固定相的离轴分裂

在式 (2.3) 与式 (2.5) 下，$V(t_*,\cdot)$ 至少具有两个互异的零能全局极小点

$$
\delta=\pm\delta_*;
$$

反射固定点 $\delta=0$ 不是零能相。

因此该事件构成一个严格的

$$
\boxed{
\mathbb Z_2\text{-reflected ground-phase split}.
}
\tag{2.6}
$$

这里“至少”不可删除：仅凭当前前件不能排除同一高度存在其他零点。

## 2.4 序参量

在反射商空间

$$
\mathbb R/(\delta\sim-\delta)
$$

上，自然序参量是

$$
\boxed{m=|\delta|.}
\tag{2.7}
$$

临界线相对应 $m=0$，离线相对应 $m>0$。离线零点不是简单地把一个零点平移；它在反射商中引入了一个非零序参量。

---

# 3. 第一离线高度与真正的“那个时刻”

## 3.1 第一离线高度的存在

定义正高度离线零点集

$$
\mathcal Z_{\mathrm{off}}^+
=
\left\{
(t,\delta):
 t>0,
\ 0<|\delta|<\frac12,
\ X(t,\delta)=0
\right\}.
\tag{3.1}
$$

### 定理 3.1　若 RH 为假，则第一离线高度存在

若 $\mathcal Z_{\mathrm{off}}^+\ne\varnothing$，则集合

$$
\left\{
t>0:\exists\delta,\ (t,\delta)\in\mathcal Z_{\mathrm{off}}^+
\right\}
$$

具有最小元。记为

$$
\boxed{T_{\mathrm{off}}.}
\tag{3.2}
$$

#### 证明

取任一离线零点高度 $t_0$。由于 $F$ 是非零整函数，其零点在紧矩形

$$
\left\{
|\Re u|\le\frac12,
\ 0\le\Im u\le t_0
\right\}
$$

中只有有限多个。该有限集合中的正高度离线零点纵坐标具有最小值。若存在一列正高度离线零点趋向 $0$，紧性给出有限平面内的聚点，与非零整函数零点离散性矛盾。

这一定理把“第一个离线零点”从直觉对象变为严格条件对象。

## 3.2 累积最大位移

对 $T\ge0$，定义

$$
\boxed{
M(T)
=
\max\left(
\left\{
|\delta|:
0<t\le T,
\ X(t,\delta)=0,
\ 0<|\delta|<\frac12
\right\}
\cup\{0\}
\right).
}
\tag{3.3}
$$

有界矩形中的零点局部有限，所以最大值存在。

### 定理 3.2　第一离线高度处的序参量跃迁

若 $T_{\mathrm{off}}$ 存在，则

$$
M(T)=0
\qquad
(0\le T<T_{\mathrm{off}}),
\tag{3.4}
$$

而

$$
M(T_{\mathrm{off}})>0.
\tag{3.5}
$$

所以 $M$ 在 $T_{\mathrm{off}}$ 处发生正跳跃。

这给出第一种严格相变读法：当“谱体积”由高度截断 $T$ 控制时，第一个离线零点使横向序参量从严格零突然变为非零。

## 3.3 离线计数

令 $N_{\mathrm{off}}(T)$ 为 $0<t\le T$ 内离线零点按重数计数的总数。由于同高度反射成对，

$$
\boxed{N_{\mathrm{off}}(T)\in2\mathbb N.}
\tag{3.6}
$$

在第一离线高度，

$$
N_{\mathrm{off}}(T_{\mathrm{off}})
-
\lim_{T\uparrow T_{\mathrm{off}}}N_{\mathrm{off}}(T)
\ge2.
\tag{3.7}
$$

若同时计入负高度共轭零点，则完整轨道按四点出现。

---

# 4. 单个离线零点的局部临界正常形

## 4.1 任意重数

设

$$
u_*=\delta_*+it_*
$$

是 $F$ 的一个 $m$ 重零点。则存在 $c\ne0$，使

$$
F(u)
=
c(u-u_*)^m
+
O(|u-u_*|^{m+1}).
\tag{4.1}
$$

令

$$
\epsilon=\delta-\delta_*,
\qquad
\tau=t-t_*.
$$

则

$$
\boxed{
X(t_*+\tau,\delta_*+\epsilon)
=
c(\epsilon+i\tau)^m
+
O\!\left((\epsilon^2+\tau^2)^{(m+1)/2}\right).
}
\tag{4.2}
$$

因此

$$
\boxed{
V(t_*+\tau,\delta_*+\epsilon)
=
|c|^2(\epsilon^2+\tau^2)^m
+
O\!\left((\epsilon^2+\tau^2)^{m+1/2}\right).
}
\tag{4.3}
$$

### 推论 4.1　能隙闭合指数

沿固定横向坐标 $\delta=\delta_*$，

$$
V(t,\delta_*)
=
|c|^2|t-t_*|^{2m}
+
o(|t-t_*|^{2m}).
\tag{4.4}
$$

所以零点重数 $m$ 直接给出可见能隙闭合指数 $2m$。

## 4.2 对数奇异势

定义零点检测势

$$
\Phi(t,\delta)
:=-\log V(t,\delta).
\tag{4.5}
$$

它不是未经构造的物理自由能，而是由零点能量直接定义的解析势。

由式 (4.3)，

$$
\boxed{
\Phi(t_*+\tau,\delta_*+\epsilon)
=
-2m\log\sqrt{\epsilon^2+\tau^2}
-
\log|c|^2
+
o(1).
}
\tag{4.6}
$$

因此零点对应一个对数奇点。

## 4.3 相位绕数

在围绕 $(t_*,\delta_*)$ 的正向小圆上，$X$ 的相位绕行数为 $m$：

$$
\boxed{
\frac1{2\pi}\Delta\arg X=m.
}
\tag{4.7}
$$

所以一个 $m$ 重零点是拓扑荷为 $m$ 的相位涡旋。

沿 $\delta=\delta_*$ 穿过 $t_*$，两侧主项分别为

$$
c(i|\tau|)^m,
\qquad
c(-i|\tau|)^m.
$$

故两侧相位差为

$$
\boxed{m\pi\pmod{2\pi}.}
\tag{4.8}
$$

当 $m$ 为奇数时，两侧归一化相位互为负值；当 $m=1$ 时发生严格的 $\pi$ 翻转。

## 4.4 单零点

若 $m=1$，则 $c=\Xi'(\rho_*)$，且

$$
V
=
|\Xi'(\rho_*)|^2
\left[(\delta-\delta_*)^2+(t-t_*)^2\right]
+
o\!\left((\delta-\delta_*)^2+(t-t_*)^2\right).
\tag{4.9}
$$

在该点，$V$ 的 Hessian 主部是

$$
2|\Xi'(\rho_*)|^2 I_2.
\tag{4.10}
$$

因此简单离线零点具有各向同性二次锥、对数奇点、单位相位绕数和 $\pi$ 穿越四个同时出现的局部临界特征。

## 4.5 反射涡旋对

反射零点 $-\delta_*+it_*$ 与原零点具有相同重数。反射变换在源空间反转横向方向，复共轭在目标空间反转相位方向；两次反转抵消，因此两个涡旋具有相同正拓扑荷。

所以离线轨道在正高度切片上不是一对相消涡旋，而是一对由反射共轭锁定、同荷出现的相位缺陷。

---

# 5. 有限分辨率观察者与 phase bubble

## 5.1 near-zero 可见相

有限观察者不能判定精确等式 $X=0$，只能读取阈值事件

$$
|X(t,\delta)|\le\varepsilon.
\tag{5.1}
$$

定义

$$
\mathcal B_\varepsilon(t)
=
\left\{
\delta:
|X(t,\delta)|\le\varepsilon
\right\}.
\tag{5.2}
$$

在 $m$ 重零点附近，存在正常数 $c_-,c_+$，使充分小时

$$
c_-r^m
\le
|X|
\le
c_+r^m,
\qquad
r=\sqrt{(\delta-\delta_*)^2+(t-t_*)^2}.
\tag{5.3}
$$

因此 near-zero 区域被两个圆盘夹住，其尺度为

$$
\boxed{r_\varepsilon\asymp\varepsilon^{1/m}.}
\tag{5.4}
$$

### 推论 5.1　可见时间宽度

固定 $\delta=\delta_*$，observer 看见该 near-zero 相的时间宽度满足

$$
|t-t_*|\asymp\varepsilon^{1/m}.
\tag{5.5}
$$

简单零点时，

$$
|t-t_*|\approx
\frac{\varepsilon}{|\Xi'(\rho_*)|}.
\tag{5.6}
$$

## 5.2 双 phase bubble

反射零点产生两个同时居中的 near-zero bubble：

$$
(\delta,t)
\approx
(\delta_*,t_*),
\qquad
(-\delta_*,t_*).
$$

当 $r_\varepsilon<|\delta_*|/2$ 时，两个 bubble 互不相交，也不接触中心轴。有限观察者看到的过程是：

$$
\boxed{
\text{出现}
\longrightarrow
\text{扩张}
\longrightarrow
\text{在 }t_*\text{ 达最大}
\longrightarrow
\text{收缩}
\longrightarrow
\text{消失}.
}
\tag{5.7}
$$

因此“瞬时”与“有限持续时间”并不矛盾：前者属于精确零点几何，后者属于有限分辨率观察。

---

# 6. Cayley–Lee–Yang 圆坐标

## 6.1 临界线到单位圆

固定

$$
a>\frac12,
$$

定义 Cayley 坐标

$$
\boxed{
w=C_a(u)=\frac{a+u}{a-u},
\qquad
u=s-\frac12.
}
\tag{6.1}
$$

若 $u=\delta+it$，则

$$
\boxed{
|w|^2
=
\frac{(a+\delta)^2+t^2}
     {(a-\delta)^2+t^2}.
}
\tag{6.2}
$$

故

$$
\boxed{
\delta=0
\Longleftrightarrow
|w|=1.
}
\tag{6.3}
$$

临界线被精确送到 Lee–Yang 单位圆。

## 6.2 同角 reciprocal split

同高度反射伙伴对应

$$
u^\sharp=-\overline u=-\delta+it.
$$

直接计算得

$$
\boxed{
C_a(u^\sharp)
=
\frac1{\overline{C_a(u)}}.
}
\tag{6.4}
$$

若

$$
C_a(u)=re^{i\theta},
$$

则

$$
C_a(u^\sharp)=r^{-1}e^{i\theta}.
\tag{6.5}
$$

因此离线零点对在 Cayley 平面中：

- 辐角完全相同；
- 一个在单位圆外；
- 一个在单位圆内；
- 两个半径互为倒数。

这使“同一个时刻发生径向相分裂”成为精确几何事实，而不是类比。

## 6.3 径向序参量

定义

$$
\boxed{
\eta_a(t,\delta)
:=
\log|C_a(\delta+it)|.
}
\tag{6.6}
$$

则

$$
\eta_a(t,-\delta)
=-\eta_a(t,\delta),
\tag{6.7}
$$

且

$$
\eta_a(t,\delta)=0
\Longleftrightarrow
\delta=0.
\tag{6.8}
$$

其显式表达为

$$
\eta_a(t,\delta)
=
\frac12
\log
\frac{(a+\delta)^2+t^2}
     {(a-\delta)^2+t^2}.
\tag{6.9}
$$

临界线附近，

$$
\boxed{
\eta_a(t,\delta)
=
\frac{2a}{a^2+t^2}\,\delta
+O(\delta^3).
}
\tag{6.10}
$$

所以 $\eta_a$ 是 $\delta$ 的 Lee–Yang 径向正规坐标。

---

# 7. 有限谱体积多项式与 Mahler 自由能

## 7.1 正高度截断根族

令 $\mathcal Z_T^+$ 为 $0<\Im\rho\le T$ 的非平凡零点多重集。定义 Cayley 根

$$
w_\rho=C_a\!\left(\rho-\frac12\right)
$$

以及有限谱多项式

$$
\boxed{
P_{a,T}(w)
=
\prod_{\rho\in\mathcal Z_T^+}(w-w_\rho).
}
\tag{7.1}
$$

正高度零点集在

$$
\rho\longmapsto1-\overline\rho
$$

下封闭，因此根多重集在

$$
w\longmapsto\frac1{\overline w}
$$

下封闭。

### 定理 7.1　Vieta 径向荷恒为零

对每个反射根对

$$
w=re^{i\theta},
\qquad
w^\sharp=r^{-1}e^{i\theta},
$$

有

$$
|ww^\sharp|=1,
\qquad
\log|w|+\log|w^\sharp|=0.
\tag{7.2}
$$

因此整个反射完备截断满足

$$
\boxed{
\sum_{\rho\in\mathcal Z_T^+}\log|w_\rho|=0.
}
\tag{7.3}
$$

等价地，首项系数与常数项的模长比不能检测 reciprocal 离圆分裂。

这是一条决定性的信息逃逸定理：反射对称强迫一阶有符号径向荷完全冲销，即使每个单根都已经离开单位圆。

## 7.2 对数 Mahler 缺陷

对 monic 多项式，Mahler 测度满足

$$
\log M(P_{a,T})
=
\sum_{\rho\in\mathcal Z_T^+}
\log^+|w_\rho|.
\tag{7.4}
$$

由于根按 $\eta,-\eta$ 成对，

$$
\boxed{
\log M(P_{a,T})
=
\frac12
\sum_{\rho\in\mathcal Z_T^+}
\left|\log|w_\rho|\right|.
}
\tag{7.5}
$$

定义累积 Lee–Yang–Mahler 缺陷自由能

$$
\boxed{
\mathcal F_a(T)
:=
\log M(P_{a,T}).
}
\tag{7.6}
$$

它满足：

$$
\mathcal F_a(T)\ge0,
$$

且

$$
\boxed{
\mathcal F_a(T)=0
\Longleftrightarrow
0<\Im\rho\le T\text{ 的全部零点均在线}.
}
\tag{7.7}
$$

### 定理 7.2　第一离线高度处的 Mahler 跳跃

若 $T_{\mathrm{off}}$ 存在，则

$$
\mathcal F_a(T)=0
\qquad
(T<T_{\mathrm{off}}),
\tag{7.8}
$$

而

$$
\boxed{
\mathcal F_a(T_{\mathrm{off}})>0.
}
\tag{7.9}
$$

若该高度只有一个重数为 $m$ 的反射零点对，且外侧根模长为 $r_*>1$，则跳跃量为

$$
\boxed{
\Delta\mathcal F_a(T_{\mathrm{off}})
=m\log r_*.
}
\tag{7.10}
$$

这给出第二种严格相变读法：在线零点增加多项式次数，却不改变 Mahler 自由能；第一对离圆根则使自由能第一次产生正跳跃。

## 7.3 Lee–Yang 缺陷原子测度

定义正测度

$$
\boxed{
\mu_a^{\mathrm{LY}}
=
\frac12
\sum_{\substack{\rho:\Im\rho>0}}
 m_\rho
\left|\log|w_\rho|\right|
\delta_{\Im\rho}.
}
\tag{7.11}
$$

则

$$
\mathcal F_a(T)
=
\mu_a^{\mathrm{LY}}((0,T]).
\tag{7.12}
$$

因此：

$$
\boxed{
\mathrm{RH}
\Longleftrightarrow
\mu_a^{\mathrm{LY}}=0
\Longleftrightarrow
\mathcal F_a(T)=0\quad\forall T>0.
}
\tag{7.13}
$$

若 RH 为假，$T_{\mathrm{off}}$ 正是该正原子测度的第一个支撑点。

有限分辨率观察者对 $\mu_a^{\mathrm{LY}}$ 作时间卷积，原子脉冲便被展宽为第 5 节的 phase bubble。这把“离线的那个时刻”写成了一个精确的正测度原子。

---

# 8. 一个最小信息逃逸模型

## 8.1 在线相与离线相单元

固定辐角 $\theta$ 与 $r>1$。考虑两个二根状态：

$$
A_\theta
=
\{e^{i\theta},e^{i\theta}\},
\tag{8.1}
$$

$$
B_{r,\theta}
=
\{re^{i\theta},r^{-1}e^{i\theta}\}.
\tag{8.2}
$$

$A_\theta$ 是单位圆上的双根相，$B_{r,\theta}$ 是同角 reciprocal 离圆相。

定义一阶乘积读出

$$
c_{\mathrm{prod}}(\{w_1,w_2\})=w_1w_2,
\tag{8.3}
$$

以及径向关系读出

$$
c_{\mathrm{rad}}(\{w_1,w_2\})
=
(\log|w_1|)^2+(\log|w_2|)^2.
\tag{8.4}
$$

则

$$
c_{\mathrm{prod}}(A_\theta)
=
c_{\mathrm{prod}}(B_{r,\theta})
=e^{2i\theta},
\tag{8.5}
$$

而

$$
c_{\mathrm{rad}}(A_\theta)=0,
\qquad
c_{\mathrm{rad}}(B_{r,\theta})=2(\log r)^2>0.
\tag{8.6}
$$

### 定理 8.1　一阶 Vieta 读出必然遗失离圆信息

在线双根相与 reciprocal 离圆相具有完全相同的根乘积，但具有不同的径向二阶能量。因此 self-reciprocity、常数项与首项系数模长相等、总径向荷为零，都不能推出单位圆根定位。

第一非平凡定位信息至少需要进入：

$$
\boxed{
\text{绝对径向变差、二阶能量或逐根位置关系层}.
}
\tag{8.7}
$$

## 8.2 有限信息逃逸率

令有限状态空间

$$
\Omega=\{A_\theta,B_{r,\theta}\}.
$$

对任意观察族 $S$，定义联合不可区分核

$$
K_S
=
\{(x,y)\in\Omega^2:
\text{族 }S\text{ 的全部读出在 }x,y\text{ 上相同}\},
\tag{8.8}
$$

非对角逃逸集合

$$
E_S=K_S\setminus\Delta_\Omega,
\tag{8.9}
$$

以及均匀有序非对角 pair 的信息逃逸率

$$
\boxed{
\varepsilon(S)
=
\frac{|E_S|}{|\Omega|(|\Omega|-1)}.
}
\tag{8.10}
$$

只保留乘积读出时，两个状态不可区分，所以

$$
\varepsilon(\{c_{\mathrm{prod}}\})=1.
\tag{8.11}
$$

加入径向关系读出后，两个状态被完全分离，所以

$$
\varepsilon(\{c_{\mathrm{prod}},c_{\mathrm{rad}}\})=0.
\tag{8.12}
$$

故径向关系读出的留一信息增益为

$$
\boxed{
\delta_{\mathrm{rad}}
=
1.
}
\tag{8.13}
$$

这不是人工评分，而是由两个观察 kernel 的严格包含精确计算所得。

该二状态单元揭示了本理论的信息逃逸核心：

$$
\boxed{
\text{反射对称保存总乘积，
却允许等量反向的径向信息从一阶标量层逃逸。}
}
\tag{8.14}
$$

---

# 9. prime-frequency 复关系层

## 9.1 复化二槽核

令两个不同素数频率为

$$
\omega_p=\log p,
\qquad
\omega_q=\log q,
$$

并取反射观察点

$$
s_1=\sigma+\delta+it_1,
\qquad
s_2=\sigma-\delta+it_2.
$$

定义交替二槽核

$$
\boxed{
\mathcal K_{p,q}
=
p^{-s_1}q^{-s_2}
-
q^{-s_1}p^{-s_2}.
}
\tag{9.1}
$$

记

$$
\tau=t_1-t_2,
\qquad
\Delta_{p,q}=\log\frac qp.
$$

则有精确恒等式

$$
\boxed{
\frac{(pq)^{2\sigma}}4
|\mathcal K_{p,q}|^2
=
\sinh^2(\delta\Delta_{p,q})
+
\sin^2\!\left(\frac{\tau\Delta_{p,q}}2\right).
}
\tag{9.2}
$$

圆周方向的时间分辨与双曲方向的横向分裂，是同一个复关系核的两个正交分量。

## 9.2 法向关系能量

定义

$$
\boxed{
R_{p,q}(\delta)
:=
\sinh^2\!\left(\delta\log\frac qp\right).
}
\tag{9.3}
$$

### 定理 9.1　严格横向可分离性

若 $p\ne q$，则

$$
R_{p,q}(\delta)=0
\Longleftrightarrow
\delta=0.
\tag{9.4}
$$

特别地，任何离线位移 $\delta_*\ne0$ 都给出

$$
\boxed{R_{p,q}(\delta_*)>0.}
\tag{9.5}
$$

### 定理 9.2　全局严格凸性

若 $p\ne q$，则

$$
R_{p,q}''(\delta)
=
2\log^2\frac qp
\cosh\!\left(2\delta\log\frac qp\right)>0.
\tag{9.6}
$$

所以 $R_{p,q}$ 以 $\delta=0$ 为唯一全局极小点。

### 推论 9.1　横向刚度下界

由 $|\sinh x|\ge|x|$，

$$
\boxed{
R_{p,q}(\delta)
\ge
\delta^2\log^2\frac qp.
}
\tag{9.7}
$$

临界线附近，

$$
R_{p,q}(\delta)
=
\delta^2\log^2\frac qp
+
\frac13\delta^4\log^4\frac qp
+
O(\delta^6).
\tag{9.8}
$$

因此 prime pair 自身提供的是恢复临界线的正刚度，不是把零点推出临界线的负质量。

## 9.3 零核条件

由式 (9.2)，当 $p\ne q$ 时，

$$
\mathcal K_{p,q}=0
$$

当且仅当

$$
\delta=0,
\qquad
\tau\log(q/p)\in2\pi\mathbb Z.
\tag{9.9}
$$

所以单个 prime pair 已经满足一个最小的 Lee–Yang 型定位律：交替关系核若完全闭合，则法向坐标必须回到临界线。

困难不在二体核，而在无穷 prime–Gamma 完成是否保留这种关系层强制性。

---

# 10. prime cluster 的横向外积能量

## 10.1 有限加权簇

取有限不同 prime-frequency 集合

$$
\mathcal C=\{p_1,\ldots,p_m\}
$$

及非负权重 $W_{ij}\ge0$。定义

$$
\boxed{
R_{\mathcal C}(\delta)
=
\sum_{i<j}
W_{ij}
\sinh^2\!\left(
\delta(\log p_j-\log p_i)
\right).
}
\tag{10.1}
$$

若至少一个连接不同频率的权重严格为正，则

$$
R_{\mathcal C}(\delta)=0
\Longleftrightarrow
\delta=0,
\tag{10.2}
$$

且 $R_{\mathcal C}$ 严格凸。

其临界线二次刚度为

$$
\boxed{
\mathfrak m_{\mathcal C}^2
=
\sum_{i<j}
W_{ij}(\log p_j-\log p_i)^2.
}
\tag{10.3}
$$

并有

$$
R_{\mathcal C}(\delta)
\ge
\mathfrak m_{\mathcal C}^2\delta^2.
\tag{10.4}
$$

## 10.2 等权完全图与 log-prime 方差

在等权完全图下，

$$
\sum_{i<j}(x_i-x_j)^2
=
m\sum_i(x_i-\bar x)^2.
$$

令 $x_i=\log p_i$，得

$$
\boxed{
R_{\mathcal C}(\delta)
\ge
\delta^2m
\sum_{i=1}^m
\left(\log p_i-\overline{\log p}\right)^2.
}
\tag{10.5}
$$

因此有限 prime cluster 的横向刚度由整个 log-frequency 方差控制，而不是只由最小加法 gap 控制。

## 10.3 短 gaps 是软模

若 $q=p+g$ 且 $g\ll p$，则

$$
\log\frac qp
=
\frac gp
+O\!\left(\frac{g^2}{p^2}\right),
$$

从而

$$
R_{p,q}(\delta)
=
\delta^2\frac{g^2}{p^2}
+
O\!\left(
\delta^2\frac{g^3}{p^3}
+
\delta^4\frac{g^4}{p^4}
\right).
\tag{10.6}
$$

所以短 prime gap 不增强单 pair 的离线信号，而是降低其横向刚度并延长相干时间。

其理论身份是：

$$
\boxed{
\text{near-degenerate soft relation mode}.
}
\tag{10.7}
$$

单个 soft mode 不是相变。只有跨大量尺度相容嵌套的 soft clusters，才可能使全局最小 coercivity 逼近零。这正是 PrimeGap sticky tower 应承担的理论角色。

---

# 11. Lee–Yang 径向度量与 prime 双曲度量的局部等价

## 11.1 共同零集

对固定 $a>1/2$、有限非平凡 prime cluster $\mathcal C$，有

$$
\eta_a(t,\delta)=0
\Longleftrightarrow
\delta=0
\Longleftrightarrow
R_{\mathcal C}(\delta)=0.
\tag{11.1}
$$

因此 Cayley 径向缺陷与 prime 双曲关系能量具有完全相同的相边界。

## 11.2 紧窗可比性

固定有限高度 $0\le t\le T$ 和闭横向窗

$$
|\delta|\le\frac12-\eta_0,
\qquad
\eta_0>0.
$$

由于

$$
\partial_\delta\eta_a(t,0)
=
\frac{2a}{a^2+t^2}>0
$$

且

$$
R_{\mathcal C}(\delta)
=
\mathfrak m_{\mathcal C}^2\delta^2+O(\delta^4),
$$

比值

$$
\frac{R_{\mathcal C}(\delta)}{\eta_a(t,\delta)^2}
$$

在 $\delta=0$ 处具有严格正的连续延拓。紧性给出常数

$$
0<c_{a,\mathcal C,T,\eta_0}
\le
C_{a,\mathcal C,T,\eta_0}<\infty
$$

使

$$
\boxed{
c_{a,\mathcal C,T,\eta_0}
\eta_a(t,\delta)^2
\le
R_{\mathcal C}(\delta)
\le
C_{a,\mathcal C,T,\eta_0}
\eta_a(t,\delta)^2.
}
\tag{11.2}
$$

所以在任何有限谱窗内，prime 双曲关系能量都是 Lee–Yang 径向偏移的一个等价二次度量。

这是一条纯坐标—度量定理。它不声称 prime side 已经生成或控制 zeta 零点，但它证明两种候选序参量确实测量同一个法向自由度。

---

# 12. 横向 coercivity gap 的闭合

## 12.1 固定高度 coercivity

在避开中心的闭环带

$$
A_{\varepsilon,\eta}
=
\left\{
\delta:
\varepsilon\le|\delta|\le\frac12-\eta
\right\},
$$

其中 $\varepsilon,\eta>0$ 且该集合非空，定义

$$
\boxed{
\mathfrak c_{\mathcal C}(t;\varepsilon,\eta)
=
\min_{\delta\in A_{\varepsilon,\eta}}
\frac{V(t,\delta)}{R_{\mathcal C}(\delta)}.
}
\tag{12.1}
$$

分母在该环带上严格为正。

### 定理 12.1　有限横向零点与 coercivity 等价

$$
\boxed{
\mathfrak c_{\mathcal C}(t;\varepsilon,\eta)>0
}
$$

当且仅当高度 $t$ 在该横向环带内没有零点。

#### 证明

比值是紧集上的连续非负函数。若无零点，分子处处严格正，故最小值严格正；若存在零点，最小值为零。

因此离线零点 $(t_*,\delta_*)$ 一旦落入环带，就强迫

$$
\boxed{
\mathfrak c_{\mathcal C}(t_*;\varepsilon,\eta)=0.
}
\tag{12.2}
$$

这给出第三种严格相变读法：在该时刻，标量可见能量对关系层横向能量的最佳强制常数闭合。

## 12.2 累积 coercivity

定义

$$
\boxed{
\mathfrak C_{\mathcal C}(T;\varepsilon,\eta)
=
\min_{0\le t\le T}
\mathfrak c_{\mathcal C}(t;\varepsilon,\eta).
}
\tag{12.3}
$$

则 $\mathfrak C_{\mathcal C}$ 关于 $T$ 单调不增，并且

$$
\mathfrak C_{\mathcal C}(T;\varepsilon,\eta)>0
$$

当且仅当矩形

$$
0\le t\le T,
\qquad
\varepsilon\le|\delta|\le\frac12-\eta
$$

中没有离线零点。

于是 RH 等价于：对任意有限 $T$ 和任意有理 $\varepsilon,\eta>0$，所有这些有限窗 coercivity 常数都严格为正。

这只是等价重述，不是证明；但它把 RH 精确改写为一族有限紧窗强制性命题。

## 12.3 第一离线时刻的连续 gap closing

设 $(T_{\mathrm{off}},\delta_*)$ 是第一离线事件，并选择环带包含 $\delta_*$。则对 $T<T_{\mathrm{off}}$，

$$
\mathfrak C_{\mathcal C}(T;\varepsilon,\eta)>0,
$$

而

$$
\mathfrak C_{\mathcal C}(T_{\mathrm{off}};\varepsilon,\eta)=0.
$$

与最大位移 $M(T)$ 的正跳跃不同，coercivity gap 通常从左侧连续趋于零。若第一离线零点是孤立的 $m$ 重零点，则沿固定 $\delta_*$ 有上界

$$
\mathfrak C_{\mathcal C}(T;\varepsilon,\eta)
\le
\frac{|c|^2}{R_{\mathcal C}(\delta_*)}
(T_{\mathrm{off}}-T)^{2m}
+
o((T_{\mathrm{off}}-T)^{2m}).
\tag{12.4}
$$

在唯一局部最小分支与全局分离条件下，该式提升为同阶渐近。

因此同一事件同时表现为：

$$
\boxed{
\text{序参量跳起，coercivity gap 闭合。}
}
\tag{12.5}
$$

这正是相变语言中“新相出现”与“旧相稳定性消失”的双重读法。

---

# 13. prime 加权的离线缺陷测度

定义有限 cluster 对一个零点 $\rho=\tfrac12+\delta_\rho+i\gamma_\rho$ 的关系权

$$
\mathcal R_{\mathcal C}(\rho)
:=
R_{\mathcal C}(\delta_\rho).
\tag{13.1}
$$

并定义正原子测度

$$
\boxed{
\nu_{\mathcal C}
=
\frac12
\sum_{\substack{\rho:\Im\rho>0}}
 m_\rho
R_{\mathcal C}(\delta_\rho)
\delta_{\Im\rho}.
}
\tag{13.2}
$$

由于

$$
R_{\mathcal C}(\delta)=0
\Longleftrightarrow
\delta=0,
$$

有

$$
\boxed{
\mathrm{RH}
\Longleftrightarrow
\nu_{\mathcal C}=0.
}
\tag{13.3}
$$

并且若第一离线高度存在，则它也是 $\nu_{\mathcal C}$ 的第一个支撑点。

$\mu_a^{\mathrm{LY}}$ 用 Cayley 径向长度加权，$\nu_{\mathcal C}$ 用 prime-frequency 双曲关系能量加权。第 11 节说明两者在有限谱窗内测量同一法向缺陷，但一个来自圆坐标，一个来自 prime 关系度量。

真正开放的问题不是定义 $\nu_{\mathcal C}$，而是：能否不读取零点坐标，仅从 completed prime–Gamma side 构造或控制同一个正测度。

---

# 14. zero-side 奇通道与相变字典

对一个 supplied 离线四点轨道，现有 zero-side 理论把卷积平方贡献分解为

$$
\boxed{
Q_{\operatorname{orb}(\rho)}(g)
=
E_\rho^{\mathrm{even}}(g)
-
E_\rho^{\mathrm{odd}}(g),
}
\tag{14.1}
$$

其中

$$
E_\rho^{\mathrm{even}}(g)\ge0,
\qquad
E_\rho^{\mathrm{odd}}(g)\ge0.
\tag{14.2}
$$

离线轨道的全部符号风险集中于 odd channel。

本理论给出下列精确字典：

| Lee–Yang／横向几何 | zero-side | prime relation side |
|---|---|---|
| $\delta=0$ | 在线固定相 | $R_{\mathcal C}=0$ |
| $\delta\ne0$ | 离线反射相 | $R_{\mathcal C}>0$ |
| reciprocal radial pair | 四点轨道的正高度半轨道 | 双曲二槽分裂 |
| Mahler 缺陷 | 离线轨道存在 | prime 加权缺陷测度 |
| 径向二阶能量 | odd spectral energy | exterior relation energy |
| coercivity gap 闭合 | Weil 符号风险出现 | scalar completion 不再控制 relation layer |

但“字典”不是“输运定理”。当前仍不能从

$$
R_{\mathcal C}(\delta_*)>0
$$

直接推出一个具体 Weil odd energy 的定量下界，也不能反向从 prime cluster 能量排除所有离线轨道。

---

# 15. 两种相变必须区分

## 15.1 谱扫描相变

本文的 $t$ 是复平面中的谱坐标。固定 $\Xi$ 不变，观察者沿高度扫描。第一离线高度的事件是：

- 累积横向序参量首次变正；
- 离线计数首次跳跃；
- Mahler 缺陷首次产生正原子；
- 有限窗 coercivity 首次闭合。

这是一个

$$
\boxed{\text{spectral-volume / observer-scan transition}.}
\tag{15.1}
$$

零点不是在物理时间中临时生成，而是扫描切片第一次穿过一个已有的二维复零点缺陷。

## 15.2 变形参数相变

若另有连续函数族 $\Xi_\lambda$，使零点随控制参数 $\lambda$ 运动，那么在线零点碰撞后分裂成离线共轭对，才是动力学意义上的 root-bifurcation transition。

在一般二重零点临界条件下，Weierstrass 正规形具有候选形状

$$
\Xi_\lambda
\sim
U(\lambda,u)
\left[(u-u_c)^2-A(\lambda-\lambda_c)\right],
\tag{15.2}
$$

从而横向序参量满足平方根律

$$
|\delta|\asymp|\lambda-\lambda_c|^{1/2}.
\tag{15.3}
$$

这与 fixed-$\Xi$ 的高度扫描不是同一参数，但二者在临界点共享同一个反射 radial split 几何。

因此“离线的那个时刻”可以有两种严格含义：

1. 固定函数中第一次扫描到离线缺陷的高度；
2. 变形流中零点真正离开临界线的控制参数。

本文主要建立第一种，并保留第二种作为连续相变扩展。

---

# 16. 纯理论的信息逃逸纪律

本理论的每一层必须区分原始前件、推出结论与开放桥。

## 16.1 最小前件族

记：

- $A_1$：$\Xi$ 是非零整函数；
- $A_2$：反射律 $\Xi(s)=\Xi(1-s)$；
- $A_3$：实结构 $\Xi(\bar s)=\overline{\Xi(s)}$；
- $A_4$：存在离线零点 $(t_*,\delta_*)$；
- $A_5$：中心分离 $X(t_*,0)\ne0$；
- $A_6(m)$：该零点重数为 $m$；
- $A_7$：有限 prime relation graph 至少含一条连接不同频率的正权边；
- $A_8$：存在一个在线零点状态，用于有限信息逃逸比较；
- $A_9$：prime–Gamma side 到 zero-side odd energy 的忠实输运。

其中 $A_9$ 是开放桥，不进入任何已经证明结论的前件伪装层。

## 16.2 最小依赖表

| 结论 | 最小依赖 |
|---|---|
| 同高度反射共轭律 | $A_2,A_3$ |
| 离线零点反射成对 | $A_2,A_3,A_4$ |
| 中心固定相被排除 | 再加 $A_5$ |
| 第一离线高度存在 | $A_1,A_4$ 与临界条带有界性 |
| 最大位移跳跃 | 第一离线高度 |
| 局部 $2m$ 次 gap closing | $A_1,A_6(m)$ |
| 奇重数相位 antipodal crossing | $A_6(m)$ 且 $m$ 奇 |
| Cayley reciprocal radial split | $A_2,A_3$ 与坐标定义 |
| Mahler 缺陷正跳跃 | 第一离线高度与 Cayley 坐标 |
| prime relation energy 严格为正 | $A_4,A_7$ |
| 有限窗 coercivity 闭合 | $A_4,A_7$ |
| 二状态信息逃逸率由 $1$ 降为 $0$ | Vieta 与径向读出定义 |
| 从 prime side 排除离线 odd channel | 必须使用开放的 $A_9$ |
| RH | 不能由前述有限与条件结论单独推出 |

该表的作用是阻止下列偷运：

- 把反射伙伴直接放入离线零点定义；
- 把“中心非零”隐藏在“phase split”名称中；
- 把单零点性质默认给所有零点；
- 把 $p\ne q$ 从严格正性条件中删除；
- 把 zero-defined prime 权重测度误写成 prime-side 已构造对象；
- 把同一零集或同一坐标依赖误写成因果支配；
- 把等价重述误写成 RH 证明。

## 16.3 理论不可约性

在最小二状态 radial split 单元中，乘积读出与径向读出具有严格不同的不可区分核。删除径向读出，信息逃逸率严格上升。因此径向二阶信息不是乘积对称性的同义重复，而是一个不可约的新概念坐标。

相反，反射伙伴不是独立输入；它可以由 $A_2,A_3$ 推出。若把它另列为原始前件，就会把本可导出的信息重复记账，降低理论的内生信息增益。

这给出本理论的无逃逸原则：

$$
\boxed{
\text{可推出者不得作为输入；
不可由低阶标量恢复者必须保留为独立关系读出。}
}
\tag{16.1}
$$

---

# 17. RH 的 Lee–Yang–Mahler 等价族

固定任意 $a>1/2$。下列命题等价：

1. 所有非平凡零点满足 $\Re\rho=1/2$；
2. 对所有 $T>0$，$M(T)=0$；
3. 对所有 $T>0$，$N_{\mathrm{off}}(T)=0$；
4. 对所有 $T>0$，$P_{a,T}$ 的全部根位于单位圆；
5. 对所有 $T>0$，$\mathcal F_a(T)=0$；
6. Lee–Yang 缺陷测度 $\mu_a^{\mathrm{LY}}$ 为零；
7. 对任意非平凡有限 prime cluster，$\nu_{\mathcal C}=0$；
8. 对任意有限 $T$ 与任意避轴横向环带，有限窗 coercivity 常数严格为正。

这些是 RH 的一组严格等价重述。它们的价值在于把同一命题分别投影为：

- 零点定位；
- 序参量消失；
- 缺陷计数消失；
- Lee–Yang 圆稳定；
- Mahler 自由能为零；
- 正原子缺陷测度为空；
- prime 关系度量下的离线能量为空；
- 所有有限窗保持正 coercivity。

但等价族本身不提供其中任何一个命题的无条件证明。

---

# 18. 唯一承重开放桥

## 18.1 已经得到的两端对象

zero side 已有离线奇能量：

$$
E_{\mathrm{off}}^{\mathrm{odd}}(g)\ge0.
$$

prime relation side 现在有自然横向能量：

$$
\mathcal E_{\mathrm{prime}}^\perp(\delta;g)
=
\sum_{p<q}
W_{p,q}[g]
\sinh^2\!\left(
\delta\log\frac qp
\right).
\tag{18.1}
$$

## 18.2 忠实输运猜想

真正的承重命题应具有形式

$$
\boxed{
E_{\mathrm{off}}^{\mathrm{odd}}(g)
\le
C\,
\mathcal E_{\mathrm{prime}}^\perp(\delta;g)
+
\varepsilon(g),
}
\tag{18.2}
$$

并在 canonical completion 极限中满足

$$
\varepsilon(g)\to0.
$$

还需独立证明 completed reflection-flatness 强迫

$$
\mathcal E_{\mathrm{prime}}^\perp\to0.
\tag{18.3}
$$

再加测试族对每个离线轨道的分离性，才可能推出

$$
E_{\mathrm{off}}^{\mathrm{odd}}=0
$$

并最终排除离线零点。

## 18.3 为什么这是唯一心脏

前述全部有限结论只说明：

- 离线时刻具有严格的 radial split；
- 一阶 reciprocal scalar 会遗失该 split；
- Mahler／二阶关系读出能够恢复该信息；
- prime pair 对所有 $\delta\ne0$ 提供严格正法向度量；
- 离线零点使 scalar-to-relation coercivity 常数闭合。

它们没有说明 completed zeta scalar 必须支配 prime relation layer。只有式 (18.2)–(18.3) 能把“相变诊断”升级为“相变不可能发生”的定理。

因此，任何把 `canonical`、`positive`、`stable`、`converges` 或 `completion` 直接写入输入数据并由此推出 RH 的做法，都会把唯一承重桥从证明体逃逸到命名或前件中。

---

# 19. 最终理论收束

若第一离线零点存在，则它不是一个普通的函数值对消。

在谱高度

$$
T_{\mathrm{off}}
$$

处同时发生：

$$
\boxed{
\begin{aligned}
&\text{横向零相由反射固定轴分裂为 }\pm\delta_*;\\
&\text{Cayley 根在同一辐角上分裂为 }r_*\text{ 与 }r_*^{-1};\\
&\text{累积最大位移从 }0\text{ 跳为正};\\
&\text{离线计数至少增加 }2;\\
&\text{Mahler 缺陷自由能第一次产生正跳跃};\\
&\text{Lee–Yang 缺陷测度出现第一个正原子};\\
&\text{有限窗 scalar-to-relation coercivity 闭合};\\
&\text{若零点简单，能量二次闭合且相位翻转 }\pi;\\
&\text{有限 observer 看见一对短暂 phase bubbles};\\
&\text{任一非平凡 prime relation metric 仍读取到严格正法向能量}.
\end{aligned}
}
\tag{19.1}
$$

所以用户直觉的最精确数学版本是：

$$
\boxed{
\textbf{第一离线零点高度是一个 Lee–Yang–Mahler 型瞬时横向谱相变点。}
}
\tag{19.2}
$$

它同时具有两种相变特征：

- 序参量、计数与 Mahler 自由能在累积谱体积中发生正跳跃；
- scalar-to-relation coercivity gap 在该高度闭合。

更深一层，离线相的 signed radial charge 仍为零：

$$
\eta+(-\eta)=0.
$$

所以一阶标量完成可以完全看不见它；只有

$$
|\eta|,
\qquad
\eta^2,
\qquad
\sinh^2(\delta\Delta\log p),
\qquad
E_{\mathrm{odd}}
$$

这样的绝对值、二阶关系量或奇通道能量才能恢复该信息。这就是离线零点“像相变”的本体原因：

$$
\boxed{
\text{旧的反射平衡仍保持总账为零，
但内部已经分裂出一对非零、互相抵销的关系相。}
}
\tag{19.3}
$$

RH 在这套理论中的最终含义不是“从未发生数值对消”，而是：

$$
\boxed{
\textbf{完整 prime–Gamma completion 永远不允许
这种被一阶反射总账隐藏的径向关系相成为真实零点。}
}
\tag{19.4}
$$

本文已经把“那个时刻”的几何、局部分析、序参量、Mahler 自由能、信息逃逸和 prime 关系度量统一为一个纯理论对象；尚未解决、也不得被命名替代的，只剩 prime-side 横向关系能量到 zero-side 离线奇能量的忠实输运。