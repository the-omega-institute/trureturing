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

---

# 增订一　Zeckendorf 能量、黄金传递与 Lee–Yang 横向相变

> 本增订直接续接本卷。以下编号在增订内部独立使用；全部内容仍属于同一个纯理论文件，不另立 SPEC 或实现文档。

## 摘要

本增订研究：为什么 Zeckendorf 表示、黄金比例、PrimeGaps、跳跃能量、Hankel 最小记忆、Lee–Yang 零点与假想的 zeta 离线零点反复出现在同一理论邻域中。

结论不是“黄金比例直接证明 RH”，也不是“把整数写成 Zeckendorf 表示便会改变 zeta”。恰恰相反，首先有一个否定性结论：Zeckendorf 表示对整数指数的编码是无损双射，因此凡是只通过整数指数取值的标量 Euler 配分函数，在 Zeckendorf 重编码下完全不变。Zeckendorf 本身不会制造任何新零点。

它真正增加的是一个此前被标量指数压扁的关系层：

$$
\boxed{
\text{整数指数}
\quad\longmapsto\quad
\text{唯一的无相邻占据历史}.
}
$$

在这一提升中，同一个有限状态空间自然携带五种不能混同的能量：

1. Fibonacci 指数值能量；
2. 占据数能量；
3. 黄金共轭稳定影子；
4. successor／translation 跳跃能量；
5. prime-frequency 横向关系能量。

第一种能量完整区分状态，却遗忘状态之间的局部关系；第二至第五种能量逐层恢复 hard-core memory、稳定通道、动态转移和 cross-prime 外积结构。项目中已经机器闭合的 `FiniteZeckendorfEulerIdentity`、`GoldenEulerBetaZeckendorf`、`PrimeJumpDecomposition`、`HankelRankMinimality`、`GoldenScalarDihedralBlindness`、`OrderedPrimeHolonomyCasimir` 和 `OffLineOrbitParityDecomposition` 正好落在这条分层链的不同位置。

本增订得到四个新的有限理论核心。

第一，有限 Zeckendorf 指数配分函数严格退化为几何级数，其全部非平凡根位于局部 Euler fugacity 单位圆；而 hard-core 占据配分函数由二阶 transfer matrix 控制，其两个本征通道为

$$
\lambda_\pm(z)=\frac{1\pm\sqrt{1+4z}}2,
$$

在 $z=1$ 时恰为

$$
\lambda_+(1)=\varphi,
\qquad
\lambda_-(1)=-\varphi^{-1}.
$$

因此 $\varphi$ 是最小一位记忆系统的 Perron 增长率，$-\varphi^{-1}$ 是精确性所必需、却在大尺度上指数衰减的稳定影子通道。

第二，项目的黄金指数账户具有一个精确的两级创新场。若 $b(v)$ 表示该账户，则

$$
\Delta b_v=b(v+1)-b(v)\in\{\varphi^2,\varphi\},
$$

并且扣除平均漂移 $\sqrt5$ 后，创新只取

$$
\varphi^{-2},\qquad-\varphi^{-1}.
$$

它的累积和始终有界，而长期均方能量恰为 $\varphi^{-3}$。这说明黄金稳定通道不是额外随机噪声，而是一条确定性的、零平均、有限预算的校正流。

第三，Zeckendorf 分解把一个 prime-power translation 精确分解成 Fibonacci 尺度 translation 的乘积，并给出跳跃能量的多尺度上界。它把项目已有的 arithmetic jump Laplacian 与黄金 shell 连接起来，但不提供反向 coercivity；不同 shell 仍可能在标量 translation 中发生抵消。

第四，在有限 Zeckendorf 状态与有限 prime cluster 的联合模型中，横向 susceptibility 的二阶系数严格分解为

$$
\boxed{
\text{Zeckendorf exponent second moment}
\times
\text{prime log-frequency relation energy}.
}
$$

若状态均匀分布，前者随黄金深度约按 $\varphi^{2Q}$ 增长；若使用真实单素数 Euler Gibbs 权，前者却保持有限。因此 combinatorial state count 本身不会产生 zeta 相变；真正的全局临界性必须来自 prime–Gamma 完成对跨尺度状态权的重新组织。

最终得到的统一判断是：

$$
\boxed{
\begin{aligned}
\text{Zeckendorf}
&=\text{标量整数指数的无损关系提升},\\
\varphi
&=\text{最小 hard-core memory 的扩张通道},\\
-\varphi^{-1}
&=\text{被标量大尺度压低的稳定影子},\\
\text{jump / holonomy / odd energy}
&=\text{被反射或交换压掉的一阶信息的二阶显影},\\
\text{假想离线零点}
&=\text{标量完成为零而关系层仍可能带正横向能量的时刻}.
\end{aligned}
}
$$

最后一行仍是条件性的。要把它提升为 RH 证明，必须构造 canonical prime–Zeckendorf–Gamma transfer，并证明其关系能量无条件支配 zero-side 离线奇能量。本文不把该桥藏入“能量”“黄金”“相变”或“Zeckendorf”这些名称中。

---

# 增订一·0　理论地位与真源边界

本增订是纯数学理论，不是工程规范，也不新增 Lean 声明。

下列事实已经由仓库 Lean 真源承担：

1. `D5/S0/Tower/GoldenNames`：长度 $Q$ 的合法黄金名字与初始 Fibonacci 区间双射，基数为 $F_{Q+2}$，并具有实值注入读出；
2. `D5/S3/Observer/GoldenCoding/FiniteZeckendorfEulerIdentity`：Zeckendorf Fibonacci 和给出初始整数区间，并把有限 Euler 和精确运输为几何级数；
3. `D5/S3/Analytic/GoldenEulerBetaZeckendorf`：黄金指数账户的闭式、最小 Zeckendorf 指标奇偶读出和 $\varphi/\varphi^2$ 跳跃律；
4. `D5/S1/Deficit/ZeckendorfDisplacementReading`：Fibonacci 指标上移之和等于黄金 Beatty 读数；
5. `D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition`：有限 prime-power 项等于 coherent mass 减去非负 arithmetic jump energy；
6. `D5/S3/Observer/Hankel/HankelRankMinimality` 与 `HankelMinimalStateDimension`：稳定 Hankel rank 计算可见可达维数，并等于同一行为的最小实现维数；
7. `D5/S3/Observer/AgencyHolonomy/GoldenScalarDihedralBlindness`：完整标量黄金世界不能恢复有序 prime-word dihedral holonomy；
8. `D5/S3/Observer/AgencyHolonomy/OrderedPrimeHolonomyCasimir`：一阶有序响应消失，负二阶响应成为平方 winding 的非负加权和；
9. `D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition`：一个 supplied 离线轨道的 Weil 贡献分解成偶能量减奇能量，且两种能量分别非负。

本增订从这些真源出发作有限代数、组合、谱和能量推导。以下内容明确不作为既有 Lean 定理冒充：

- canonical prime–Zeckendorf–Gamma transfer 已经存在；
- Zeckendorf 稳定影子已经等于 zeta zero odd channel；
- prime-side 横向能量已经支配 zero-side 奇能量；
- 黄金比例已经从 Riemann completed function 中被无条件抽取；
- RH 已被证明。

---

# 增订一·1　状态、能量、关系与测度必须分开

## 1.1 四元对象

一个有限统计—谱系统不只是一组状态。其完整数据至少应写成

$$
\boxed{
\mathfrak S=(\Omega,H,\mathcal R,\mu),
}
\tag{A1.1}
$$

其中：

- $\Omega$ 是微观状态空间；
- $H:\Omega\to\mathbb R$ 是能量或指数读出；
- $\mathcal R$ 是状态之间的局部约束、转移、顺序或关系结构；
- $\mu$ 是状态权或所选 ensemble。

相应配分函数为

$$
Z_{\mathfrak S}(\beta)
=
\sum_{\eta\in\Omega}
\mu(\eta)e^{-\beta H(\eta)}.
\tag{A1.2}
$$

仅知道 $Z_{\mathfrak S}$，一般不能恢复 $\mathcal R$。甚至当 $H$ 对状态是单射时，$Z$ 仍只读取能级及其权重，不读取这些能级是通过何种局部记忆、carry 或 holonomy 连接起来的。

这正是本文所有“看似相关”对象的共同位置：

$$
\boxed{
\text{Zeckendorf 给出 }\Omega\text{ 与 }\mathcal R,
\quad
\text{Euler 给出 }H\text{ 与 }\mu,
\quad
\text{Lee–Yang 读取 }Z\text{ 的复零点},
\quad
\text{信息逃逸检测 }\mathfrak S\mapsto Z\text{ 遗忘了什么}.
}
\tag{A1.3}
$$

## 1.2 五类能量

对后文的黄金—素数系统，必须区分：

### （一）指数值能量

$$
E_Q(\eta)=\sum_k\eta_kF_k.
\tag{A1.4}
$$

它回答“这个历史代表哪个整数”。

### （二）占据能量

$$
N_Q(\eta)=\sum_k\eta_k.
\tag{A1.5}
$$

它回答“这个历史使用了多少个 Fibonacci 原子”。

### （三）稳定影子

$$
S_Q(\eta)=\sum_k\eta_k\psi^k,
\qquad
\psi=-\varphi^{-1}.
\tag{A1.6}
$$

它记录主 Fibonacci 值读出中被整数投影压掉的 Galois 共轭校正。

### （四）跳跃／carry 能量

$$
\mathcal D(f)
=
\sum_{\eta\to\eta'}
\left|f(\eta')-f(\eta)\right|^2.
\tag{A1.7}
$$

它读取状态之间的变化，而不是单个状态的值。

### （五）横向关系能量

$$
\mathcal E_{p,q}^{\perp}(\delta)
=
\sinh^2\!\left(
\delta\log\frac qp
\right).
\tag{A1.8}
$$

它读取两个 prime frequencies 在反射横向偏移下是否仍然不可区分。

五者的输出空间、零集和可加性不同，不能以“都是 energy”为理由直接相等或相加。本增订所建立的是它们之间的精确分解、共同二次结构和仍待构造的输运箭头。

---

# 增订一·2　Zeckendorf 是整数指数的无损 hard-core 提升

## 2.1 有限合法词空间

固定 $Q\ge0$，定义

$$
\Omega_Q
=
\left\{
(\eta_2,\ldots,\eta_{Q+1})\in\{0,1\}^{Q}:
\eta_k\eta_{k+1}=0
\right\}.
\tag{A2.1}
$$

约束 $\eta_k\eta_{k+1}=0$ 是一步 hard-core memory：一位被占据以后，下一位不得被占据。

定义 Fibonacci 指数能量

$$
\boxed{
E_Q(\eta)
=
\sum_{k=2}^{Q+1}\eta_kF_k.
}
\tag{A2.2}
$$

记

$$
M_Q=F_{Q+2}.
\tag{A2.3}
$$

### 定理 A2.1　有限 Zeckendorf 能量双射

映射

$$
E_Q:\Omega_Q\longrightarrow
\{0,1,\ldots,M_Q-1\}
\tag{A2.4}
$$

是双射。

#### 证明

这是仓库 `GoldenNames.goldenNameEquiv` 与 `FiniteZeckendorfEulerIdentity` 的数学内容：合法无相邻 Fibonacci 数位恰好唯一表示初始区间中的每一个整数。

### 推论 A2.2　状态数与黄金熵

$$
|\Omega_Q|=M_Q=F_{Q+2}.
\tag{A2.5}
$$

因此

$$
\log|\Omega_Q|
=Q\log\varphi+O(1).
\tag{A2.6}
$$

$\log\varphi$ 不是人为插入的常数，而是最小一步记忆二进制系统的状态熵率。

## 2.2 无损与无记忆不是同一件事

因为 $E_Q$ 是双射，所以若 observer 能读取完整整数值 $E_Q(\eta)$，则任意两个不同状态都可区分：

$$
E_Q(\eta)=E_Q(\xi)
\Longrightarrow
\eta=\xi.
\tag{A2.7}
$$

所以在微观状态层，Zeckendorf energy 没有信息逃逸。

但双射并不意味着它保存了关系结构。若只保留能量列表

$$
0,1,\ldots,M_Q-1,
$$

则“这些整数来自无相邻数位”“successor 如何 carry”“哪些状态共享最小数位奇偶”“状态图的 Hankel rank 为何”等信息全部不在能量列表中。

因此必须区分：

$$
\boxed{
\text{状态可识别性}
\neq
\text{结构可恢复性}.
}
\tag{A2.8}
$$

---

# 增订一·3　凡经由整数指数因子的标量量都不产生新信息

## 3.1 Factor-through-energy 不变性

### 定理 A3.1　任意指数函数的 Zeckendorf 重标不变

对任意交换加法目标中的函数 $a$，

$$
\boxed{
\sum_{\eta\in\Omega_Q}a(E_Q(\eta))
=
\sum_{v=0}^{M_Q-1}a(v).
}
\tag{A3.1}
$$

#### 证明

由定理 A2.1 对有限和重标即可。

这条定理比某个特定配分函数更重要。它说明：任何完全因子化为

$$
\Omega_Q\xrightarrow{E_Q}\{0,\ldots,M_Q-1\}\xrightarrow{a}A
$$

的读出，都只看见整数能量，不看见 Zeckendorf locality。

## 3.2 有限 Zeckendorf–Euler 多项式

取 $a(v)=x^v$，定义

$$
Z_Q^{\mathrm{exp}}(x)
=
\sum_{\eta\in\Omega_Q}x^{E_Q(\eta)}.
\tag{A3.2}
$$

则

$$
\boxed{
Z_Q^{\mathrm{exp}}(x)
=
1+x+\cdots+x^{M_Q-1}
=
\frac{1-x^{M_Q}}{1-x}.
}
\tag{A3.3}
$$

### 定理 A3.2　有限局部 fugacity 圆定位

若 $Q\ge1$，则

$$
Z_Q^{\mathrm{exp}}(x)=0
\Longleftrightarrow
x^{M_Q}=1
\text{ 且 }x\ne1.
\tag{A3.4}
$$

从而全部根满足

$$
\boxed{|x|=1.}
\tag{A3.5}
$$

这是一条真正的有限圆定位定理，但它来自能量双射和几何级数，不是 Riemann Hypothesis。

## 3.3 无限局部 Euler 因子

令 $\Omega_\infty$ 为有限支撑的无限合法 Zeckendorf 数位。Zeckendorf 定理给出

$$
\Omega_\infty\simeq\mathbb N.
\tag{A3.6}
$$

因此当 $|x|<1$ 时，

$$
\boxed{
\sum_{\eta\in\Omega_\infty}x^{E(\eta)}
=
\sum_{v\ge0}x^v
=
\frac1{1-x}.
}
\tag{A3.7}
$$

取 $x=p^{-s}$，在 $\Re s>0$ 的单局部收敛域中，

$$
\sum_{\eta\in\Omega_\infty}
p^{-sE(\eta)}
=
(1-p^{-s})^{-1}.
\tag{A3.8}
$$

### 否定性结论 A3.3　Zeckendorf 重编码不会改变 Euler scalar

Zeckendorf lift 对单个 Euler 因子是无损坐标变化。只要 Hamiltonian 仍然只是 $E(\eta)$ 的函数，它既不改变局部因子，也不改变由这些因子在绝对收敛域内形成的标量乘积。

因此：

$$
\boxed{
\text{Zeckendorf 本身不是新 zeta，也不是离线零点的来源。}
}
\tag{A3.9}
$$

新内容只能来自不因子化经过 $E$ 的 readout，例如 occupancy、carry、ordered holonomy、exterior energy 或 Gamma-coupled completion。

---

# 增订一·4　两个“单位圆”必须严格区分

## 4.1 局部 Euler fugacity 圆

在式 (A3.3) 中，变量是

$$
x=p^{-s}.
\tag{A4.1}
$$

所以

$$
|x|=1
\Longleftrightarrow
\Re s=0.
\tag{A4.2}
$$

有限几何级数的单位圆根对应局部 Euler 坐标中的虚轴。

## 4.2 completed Cayley–Lee–Yang 圆

对 completed function 的中心变量

$$
u=s-\frac12,
$$

取 $a>1/2$，定义

$$
w=C_a(u)=\frac{a+u}{a-u}.
\tag{A4.3}
$$

则

$$
|w|=1
\Longleftrightarrow
\Re s=\frac12.
\tag{A4.4}
$$

这是本卷前文使用的 RH 临界圆。

### 定理 A4.1　两圆非同一

局部变量 $x=p^{-s}$ 的圆与 completed Cayley 变量 $w=C_a(s-1/2)$ 的圆不是同一坐标集合：前者对应 $\Re s=0$，后者对应 $\Re s=1/2$。

所以从式 (A3.5) 不能推出 RH。

把两只圆识别起来所需的不是代数换名，而是一个真正承载全部素数、Gamma 因子、函数方程、解析延拓与零点输运的 prime–Gamma completion。

这条非同一性是信息逃逸审计中的硬边界：

$$
\boxed{
\text{局部 fugacity circle}
\not\equiv
\text{completed critical circle}.
}
\tag{A4.5}
$$

---

# 增订一·5　同一个 Zeckendorf 状态空间的 hard-core 配分函数

## 5.1 占据多项式

定义占据数

$$
N_Q(\eta)=\sum_{k=2}^{Q+1}\eta_k
\tag{A5.1}
$$

以及 hard-core occupation polynomial

$$
H_Q(z)
=
\sum_{\eta\in\Omega_Q}z^{N_Q(\eta)}.
\tag{A5.2}
$$

按最高数位是否占据分类，得到

$$
\boxed{
H_Q(z)=H_{Q-1}(z)+zH_{Q-2}(z),
}
\tag{A5.3}
$$

初值为

$$
H_0(z)=1,
\qquad
H_1(z)=1+z.
\tag{A5.4}
$$

## 5.2 二态 transfer matrix

令

$$
T(z)=
\begin{pmatrix}
1&z\\
1&0
\end{pmatrix}.
\tag{A5.5}
$$

其特征值为

$$
\boxed{
\lambda_\pm(z)
=
\frac{1\pm\sqrt{1+4z}}2.
}
\tag{A5.6}
$$

并有闭式

$$
H_Q(z)
=
\frac{
\lambda_+(z)^{Q+2}-
\lambda_-(z)^{Q+2}
}{
\lambda_+(z)-\lambda_-(z)
}.
\tag{A5.7}
$$

在 $z=1$：

$$
\boxed{
\lambda_+(1)=\varphi,
\qquad
\lambda_-(1)=1-\varphi=-\varphi^{-1}.
}
\tag{A5.8}
$$

因此

$$
H_Q(1)=F_{Q+2}
=
\frac{\varphi^{Q+2}-(-\varphi^{-1})^{Q+2}}{\sqrt5}.
\tag{A5.9}
$$

$\varphi$ 是扩张通道，$-\varphi^{-1}$ 是稳定通道。后者在相对尺度上指数衰减，却承担精确整数值、边界条件和奇偶振荡。

## 5.3 Hankel 最小记忆维数

序列

$$
a_Q=H_Q(1)=F_{Q+2}
\tag{A5.10}
$$

满足二阶递推，故其稳定 Hankel rank 不超过 $2$。另一方面，

$$
\det
\begin{pmatrix}
a_0&a_1\\
a_1&a_2
\end{pmatrix}
=
\det
\begin{pmatrix}
1&2\\
2&3
\end{pmatrix}
=-1\ne0.
\tag{A5.11}
$$

所以 Hankel rank 恰为 $2$。

结合仓库的 Hankel 最小实现定理，完整 Fibonacci 计数行为的最小有限状态实现维数正是两维。两维可取为：

- 上一位未占据；
- 上一位已占据。

于是：

$$
\boxed{
\varphi\text{ 不是“神秘常数”，而是最小一步记忆自动机的主本征值。}
}
\tag{A5.12}
$$

同时：

$$
\boxed{
-\varphi^{-1}\text{ 是标量大尺度近似最容易遗漏、但精确系统不能删除的第二状态方向。}
}
\tag{A5.13}
$$

## 5.4 hard-core 零点与 equimodular locus

由式 (A5.7)，若 $H_Q(z)=0$ 且 $z\ne-1/4$，则

$$
\left(
\frac{\lambda_+(z)}{\lambda_-(z)}
\right)^{Q+2}=1.
\tag{A5.14}
$$

因此必有

$$
|\lambda_+(z)|=|\lambda_-(z)|.
\tag{A5.15}
$$

全部根可写为

$$
\boxed{
z_j
=-\frac1{4\cos^2\!\left(\frac{j\pi}{Q+2}\right)},
\qquad
1\le j\le\left\lfloor\frac{Q+1}{2}\right\rfloor.
}
\tag{A5.16}
$$

它们全在负实轴，并在 $Q\to\infty$ 时向边缘

$$
z_c=-\frac14
\tag{A5.17}
$$

聚积。在 $z_c$，两个 transfer eigenvalues 合并。

这给出一个严格的有限 Lee–Yang／Fisher 型原型：

$$
\boxed{
\text{零点}
=
\text{两个 transfer channels 等模并满足相位量子化}.
}
\tag{A5.18}
$$

它是 Zeckendorf hard-core system 的定理，不是 zeta 的定理。

---

# 增订一·6　二变量 Zeckendorf 配分函数同时保留值与记忆

## 6.1 联合配分函数

定义

$$
\boxed{
\mathcal Z_Q(x,z)
=
\sum_{\eta\in\Omega_Q}
 x^{E_Q(\eta)}z^{N_Q(\eta)}.
}
\tag{A6.1}
$$

按最高数位分类得到非齐次 Fibonacci transfer：

$$
\boxed{
\mathcal Z_Q(x,z)
=
\mathcal Z_{Q-1}(x,z)
+z x^{F_{Q+1}}
\mathcal Z_{Q-2}(x,z),
}
\tag{A6.2}
$$

其中

$$
\mathcal Z_0=1,
\qquad
\mathcal Z_1=1+zx.
\tag{A6.3}
$$

两个截面分别为

$$
\mathcal Z_Q(x,1)=Z_Q^{\mathrm{exp}}(x),
\tag{A6.4}
$$

$$
\mathcal Z_Q(1,z)=H_Q(z).
\tag{A6.5}
$$

因此同一个状态空间在两个 observer 下呈现完全不同的零点几何：

- 指数 observer 看见单位圆几何级数；
- occupancy observer 看见负实轴 hard-core edge；
- 联合 observer 看见一个二维复零簇。

这证明“零点属于哪一种相变”不能只由状态空间决定，还取决于选择了哪一个 Hamiltonian 和哪一种 ensemble。

## 6.2 反射完成不等于圆定位

令 $z\in\mathbb R$，定义关于 $x$ 的 reciprocal completion

$$
\boxed{
\mathcal C_Q(x,z)
=
\mathcal Z_Q(x,z)\,
 x^{M_Q-1}\mathcal Z_Q(x^{-1},z).
}
\tag{A6.6}
$$

则

$$
x^{2(M_Q-1)}
\mathcal C_Q(x^{-1},z)
=
\mathcal C_Q(x,z).
\tag{A6.7}
$$

所以根自动以 reciprocal pairs 出现。但这不保证每个根在单位圆上。

最小情形 $Q=1$：

$$
\mathcal Z_1(x,z)=1+zx,
\tag{A6.8}
$$

$$
\mathcal C_1(x,z)
=(1+zx)(x+z).
\tag{A6.9}
$$

其根为

$$
x_+=-z,
\qquad
x_-=-z^{-1}.
\tag{A6.10}
$$

若令 $z=e^h>0$，则

$$
|x_+|=e^h,
\qquad
|x_-|=e^{-h}.
\tag{A6.11}
$$

在 $h=0$，两根在 $-1$ 合并；在 $h\ne0$，它们同角、互为倒数、离开单位圆。

然而始终有一阶有符号径向荷抵消：

$$
\log|x_+|+\log|x_-|=0.
\tag{A6.12}
$$

而二阶径向能量为

$$
\boxed{
(\log|x_+|)^2+(\log|x_-|)^2
=2h^2.
}
\tag{A6.13}
$$

这个最小模型精确说明：

$$
\boxed{
\text{反射函数方程只产生 reciprocal pairing；
正性或稳定性才负责 circle localization。}
}
\tag{A6.14}
$$

它与 completed zeta 的函数方程／RH 分工同型，但不是二者的数值同一。

---

# 增订一·7　Zeckendorf 的扩张通道与稳定影子

## 7.1 Minkowski 双通道

令

$$
\psi=1-\varphi=-\varphi^{-1}.
\tag{A7.1}
$$

对合法词 $\eta$，定义

$$
U(\eta)=\sum_k\eta_k\varphi^k,
\qquad
S(\eta)=\sum_k\eta_k\psi^k.
\tag{A7.2}
$$

由 Binet 公式，

$$
\boxed{
E(\eta)
=
\frac{U(\eta)-S(\eta)}{\sqrt5}.
}
\tag{A7.3}
$$

若把每个 Fibonacci 指标上移一位，定义

$$
E^+(\eta)=\sum_k\eta_kF_{k+1},
\tag{A7.4}
$$

则

$$
\boxed{
E^+(\eta)=\varphi E(\eta)+S(\eta).
}
\tag{A7.5}
$$

仓库的 Zeckendorf displacement reading 正是这一关系的整数闭式版本。

对 canonical Zeckendorf 数位，稳定影子满足统一界

$$
\boxed{
-\varphi^{-2}<S(\eta)<\varphi^{-1}.
}
\tag{A7.6}
$$

其符号由最小被占据指标的奇偶控制。

所以：

- $U$ 随深度指数增长；
- $S$ 始终在固定有界窗内；
- 但 $S$ 决定上移值落在哪一个相邻整数以及下一次跳跃取哪一支。

这是“稳定通道小但不可删除”的第一个精确实例。

## 7.2 黄金指数账户的两级跳跃

记项目中的黄金指数账户为

$$
b(v)=\operatorname{o5Beta}(v).
\tag{A7.7}
$$

仓库已证闭式

$$
\boxed{
 b(v)
=\left\lfloor\frac{v+1}{\varphi}\right\rfloor
+v\varphi
=\sqrt5\,v+\varphi^{-1}
-\operatorname{fract}((v+1)\varphi).
}
\tag{A7.8}
$$

定义增量

$$
\Delta b_v=b(v+1)-b(v).
\tag{A7.9}
$$

则

$$
\boxed{
\Delta b_v\in\{\varphi^2,\varphi\}.
}
\tag{A7.10}
$$

具体分支由 $v+1$ 的 canonical Zeckendorf 最小指标奇偶决定。

## 7.3 精确创新场

扣除平均漂移，定义

$$
\boxed{
\xi_v=\Delta b_v-\sqrt5.
}
\tag{A7.11}
$$

由

$$
\varphi^2-\sqrt5=\varphi^{-2},
\qquad
\varphi-\sqrt5=-\varphi^{-1},
\tag{A7.12}
$$

得到

$$
\boxed{
\xi_v\in\{\varphi^{-2},-\varphi^{-1}\}.
}
\tag{A7.13}
$$

### 定理 A7.1　高跳跃的精确计数

令

$$
A_N=\#\{0\le v<N:\Delta b_v=\varphi^2\}.
\tag{A7.14}
$$

则

$$
\boxed{
A_N=\left\lfloor\frac{N+1}{\varphi}\right\rfloor.
}
\tag{A7.15}
$$

#### 证明

因为 $b(0)=0$，且每个高跳跃比低跳跃多 $1$，故

$$
b(N)=N\varphi+A_N.
$$

与式 (A7.8) 比较即得。

因此高跳跃频率与低跳跃频率分别为

$$
\lim_{N\to\infty}\frac{A_N}{N}
=\varphi^{-1},
\tag{A7.16}
$$

$$
\lim_{N\to\infty}\frac{N-A_N}{N}
=\varphi^{-2}.
\tag{A7.17}
$$

### 定理 A7.2　创新累计严格有界

$$
\boxed{
\sum_{v=0}^{N-1}\xi_v
=b(N)-N\sqrt5
=\varphi^{-1}-\operatorname{fract}((N+1)\varphi).
}
\tag{A7.18}
$$

从而

$$
-\varphi^{-2}
<
\sum_{v=0}^{N-1}\xi_v
\le
\varphi^{-1}.
\tag{A7.19}
$$

所以创新场的积分不会随时间增长。

### 定理 A7.3　创新均方能量

$$
\boxed{
\lim_{N\to\infty}
\frac1N\sum_{v=0}^{N-1}\xi_v^2
=\varphi^{-3}.
}
\tag{A7.20}
$$

#### 证明

由两种取值和频率，

$$
\varphi^{-1}\varphi^{-4}
+\varphi^{-2}\varphi^{-2}
=
\varphi^{-5}+\varphi^{-4}
=\varphi^{-3}.
$$

这给出一条精确的“漂移—创新”分解：

$$
\boxed{
\Delta b_v
=\sqrt5+\xi_v,
\qquad
\text{累计创新有界，均方创新为 }\varphi^{-3}.
}
\tag{A7.21}
$$

它不是热随机过程，而是 balanced Sturmian／Zeckendorf memory 产生的确定性有限预算流。

---

# 增订一·8　arithmetic jump energy 的 Zeckendorf shell 分解

## 8.1 已有 prime jump decomposition

项目已经构造

$$
\operatorname{PrimeTerm}
=
2W_L\|f\|_2^2
-
E_{\mathrm{jump},L}(f),
\tag{A8.1}
$$

其中

$$
E_{\mathrm{jump},L}(f)
=
\sum_{n\in\mathcal P_L}
\frac{\Lambda(n)}{\sqrt n}
\left\|f-\mathsf T_{\log n}f\right\|_2^2
\ge0.
\tag{A8.2}
$$

这里

$$
(\mathsf T_a f)(y)=f(y-a)
\tag{A8.3}
$$

是 unitary translation。

## 8.2 prime power 的 Fibonacci shell factorization

取

$$
n=p^v,
\qquad
v=\sum_{k\in Z(v)}F_k
\tag{A8.4}
$$

为 $v$ 的 canonical Zeckendorf 分解。因为 translations 构成交换群，

$$
\boxed{
\mathsf T_{v\log p}
=
\prod_{k\in Z(v)}
\mathsf T_{F_k\log p}.
}
\tag{A8.5}
$$

这不是近似，而是精确因子分解。

## 8.3 跳跃能量的多尺度上界

设 $Z(v)=\{k_1,\ldots,k_r\}$。恒等式

$$
I-U_1\cdots U_r
=
\sum_{j=1}^{r}
U_1\cdots U_{j-1}(I-U_j)
\tag{A8.6}
$$

与 unitary invariance 给出

$$
\left\|
(I-\mathsf T_{v\log p})f
\right\|_2
\le
\sum_{k\in Z(v)}
\left\|
(I-\mathsf T_{F_k\log p})f
\right\|_2.
\tag{A8.7}
$$

再由 Cauchy–Schwarz：

$$
\boxed{
\left\|
(I-\mathsf T_{v\log p})f
\right\|_2^2
\le
r(v)
\sum_{k\in Z(v)}
\left\|
(I-\mathsf T_{F_k\log p})f
\right\|_2^2,
}
\tag{A8.8}
$$

其中 $r(v)=|Z(v)|$。

因为 Zeckendorf 指标不相邻，

$$
r(v)=O(\log v).
\tag{A8.9}
$$

所以任意 prime-power jump 可以被一个稀疏 Fibonacci shell family 上界。

## 8.4 为什么没有自动反向界

式 (A8.8) 只有一个方向。多个 shell displacement 可能在总 translation 中相互抵消，因此一般不能由

$$
\|(I-\mathsf T_{v\log p})f\|_2
$$

恢复所有

$$
\|(I-\mathsf T_{F_k\log p})f\|_2.
$$

这又是一次结构信息逃逸：总位移只看见 Fibonacci 原子之和，而 shell energy 读取分解历史。

Zeckendorf normal form 通过“无相邻指标”消除了

$$
F_k+F_{k+1}=F_{k+2}
\tag{A8.10}
$$

造成的局部命名冗余，但标量 translation 仍不保留原子分解。

真正的 reverse coercivity 必须加入至少一种额外结构：shell orthogonality、disjoint frequency support、positive Gram completion、ordered carry cocycle 或 prime–Gamma 全局约束。

---

# 增订一·9　Zeckendorf 与 prime 横向能量的有限联合定理

## 9.1 prime cluster relation energy

固定有限 prime cluster

$$
\mathcal C=\{p_1,\ldots,p_m\}
\tag{A9.1}
$$

和非负 pair weights $W_{ij}$。记

$$
\Delta\omega_{ij}
=
\log p_j-\log p_i.
\tag{A9.2}
$$

定义 cluster log-frequency 二阶量

$$
\boxed{
\mathcal V_{\mathcal C}
=
\sum_{i<j}W_{ij}(\Delta\omega_{ij})^2.
}
\tag{A9.3}
$$

若至少一个不同 prime pair 具有正权重，则

$$
\mathcal V_{\mathcal C}>0.
\tag{A9.4}
$$

## 9.2 Zeckendorf 平均横向能量

定义

$$
\boxed{
\mathscr E_{Q,\mathcal C}^{\perp}(\delta)
=
\frac1{M_Q}
\sum_{\eta\in\Omega_Q}
\sum_{i<j}W_{ij}
\sinh^2\!\left(
\delta E_Q(\eta)\Delta\omega_{ij}
\right).
}
\tag{A9.5}
$$

由能量双射，也可写为

$$
\mathscr E_{Q,\mathcal C}^{\perp}(\delta)
=
\frac1{M_Q}
\sum_{v=0}^{M_Q-1}
\sum_{i<j}W_{ij}
\sinh^2(\delta v\Delta\omega_{ij}).
\tag{A9.6}
$$

### 定理 A9.1　严格正性与唯一零相

若 $Q\ge1$ 且 $\mathcal V_{\mathcal C}>0$，则

$$
\mathscr E_{Q,\mathcal C}^{\perp}(\delta)\ge0,
\tag{A9.7}
$$

并且

$$
\boxed{
\mathscr E_{Q,\mathcal C}^{\perp}(\delta)=0
\Longleftrightarrow
\delta=0.
}
\tag{A9.8}
$$

#### 证明

每一项非负。若 $\delta\ne0$，取 $v=1$ 和一个 $W_{ij}>0$、$p_i\ne p_j$ 的 pair，则对应 $\sinh^2$ 严格为正。

### 定理 A9.2　Zeckendorf–prime susceptibility factorization

在 $\delta=0$：

$$
\boxed{
\left.
\frac{d^2}{d\delta^2}
\mathscr E_{Q,\mathcal C}^{\perp}(\delta)
\right|_{\delta=0}
=
\frac{(M_Q-1)(2M_Q-1)}3
\mathcal V_{\mathcal C}.
}
\tag{A9.9}
$$

#### 证明

因为

$$
\left.
\frac{d^2}{d\delta^2}
\sinh^2(a\delta)
\right|_{\delta=0}
=2a^2,
$$

而

$$
\frac1{M_Q}
\sum_{v=0}^{M_Q-1}v^2
=
\frac{(M_Q-1)(2M_Q-1)}6.
$$

故得结论。

### 推论 A9.3　黄金深度放大律

因为 $M_Q=F_{Q+2}\asymp\varphi^Q$，

$$
\boxed{
\mathscr E_{Q,\mathcal C}^{\perp\prime\prime}(0)
\asymp
\varphi^{2Q}\mathcal V_{\mathcal C}.
}
\tag{A9.10}
$$

所以在均匀有限状态 ensemble 中：Zeckendorf depth 提供指数增长的二阶放大，prime cluster 提供 log-frequency 方向方差，二者在最低阶严格乘法分离。

这就是 Zeckendorf 与 PrimeGaps 在能量层真正相遇的位置。

---

# 增订一·10　Fibonacci–Lorentz shell tower

## 10.1 同一个复参数的圆周与双曲分量

对不同 primes $p,q$，令

$$
\Delta\omega=\log(q/p),
\qquad
z=\delta+i\frac\tau2.
\tag{A10.1}
$$

项目已有复交替核给出

$$
\left|\sinh(z\Delta\omega)\right|^2
=
\sinh^2(\delta\Delta\omega)
+
\sin^2\!\left(\frac\tau2\Delta\omega\right).
\tag{A10.2}
$$

在 Fibonacci shell $F_k$ 上定义

$$
a_k=zF_k\Delta\omega.
\tag{A10.3}
$$

由于

$$
F_{k+1}=F_k+F_{k-1},
$$

有

$$
\boxed{
a_{k+1}=a_k+a_{k-1}.}
\tag{A10.4}
$$

若令

$$
R_k=e^{a_k},
\tag{A10.5}
$$

则

$$
\boxed{R_{k+1}=R_kR_{k-1}.}
\tag{A10.6}
$$

这是一条精确的 multiplicative Fibonacci rapidity recurrence。

- 当 $\delta=0$ 时，$|R_k|=1$，得到圆周 phase tower；
- 当 $\delta\ne0$ 时，$|R_k|=e^{\delta F_k\Delta\omega}$，得到 hyperbolic radial tower。

因此：

$$
\boxed{
\text{时间相位与离线横向分裂，是同一 Fibonacci 复 rapidity 的虚部和实部。}
}
\tag{A10.7}
$$

## 10.2 shell 横向能量

定义归一化 shell detector

$$
\mathcal E_k^{\perp}(\delta;p,q)
=
\sinh^2\!\left(
\delta F_k\log\frac qp
\right).
\tag{A10.8}
$$

其零集为

$$
\mathcal E_k^{\perp}=0
\Longleftrightarrow
\delta=0
\tag{A10.9}
$$

只要 $F_k>0$ 且 $p\ne q$。

## 10.3 临界 Zeckendorf 深度

令

$$
x=|\delta|\left|\log\frac qp\right|.
\tag{A10.10}
$$

定义首次达到非微扰尺度的 shell：

$$
k_*(x)=\min\{k:F_kx\ge1\}.
\tag{A10.11}
$$

由 Binet 渐近，

$$
\boxed{
 k_*(x)
=
\log_\varphi\frac{\sqrt5}{x}+O(1)
\qquad(x\downarrow0).
}
\tag{A10.12}
$$

相应合法状态数满足

$$
\boxed{
M_{k_*}\asymp\frac1x
=
\frac1{|\delta|\,|\log(q/p)|}.
}
\tag{A10.13}
$$

而所需信息熵为

$$
\boxed{
\log M_{k_*}
=
\log\frac1{|\delta|\,|\log(q/p)|}+O(1).
}
\tag{A10.14}
$$

这给出一个精确 observer-resolution law：横向偏移越小，需要越深的黄金 memory；prime log-gap 越小，需要越深的黄金 memory；深度只对分辨率的对数增长，但状态数按其倒数增长。

若 $q=p+g$ 且 $g\ll p$，则

$$
\log(q/p)=\frac gp+O(g^2/p^2),
\tag{A10.15}
$$

所以

$$
\boxed{
 k_*
=
\log_\varphi\frac{p}{|\delta|g}+O(1).
}
\tag{A10.16}
$$

这正是 short-gap sticky grain 与 Zeckendorf depth 的定量接点。

---

# 增订一·11　均匀状态 ensemble 与真实 Euler Gibbs ensemble 的分叉

式 (A9.10) 容易诱发一个错误结论：因为状态数按 $\varphi^Q$ 增长，横向 susceptibility 按 $\varphi^{2Q}$ 增长，所以黄金递归自动产生相变。

该结论不成立，因为 susceptibility 还依赖状态测度。

## 11.1 均匀 ensemble

在式 (A9.5) 中，每个 exponent $v\in[0,M_Q-1]$ 权重相同，因此

$$
\mathbb E_Q[v^2]
=
\frac{(M_Q-1)(2M_Q-1)}6
\asymp M_Q^2.
\tag{A11.1}
$$

这确实产生黄金深度放大。

## 11.2 单 Euler 因子的 Gibbs ensemble

固定 $0<x<1$，对 $v\ge0$ 使用几何权

$$
\mu_x(v)=(1-x)x^v.
\tag{A11.2}
$$

则

$$
\mathbb E_x[v^2]
=
\boxed{
\frac{x(1+x)}{(1-x)^2}
}<\infty.
\tag{A11.3}
$$

取 $x=p^{-\sigma}$，对任一固定 prime 和 $\sigma>0$，该二阶矩有限。

所以在真实局部 Euler 权下，增加 Zeckendorf depth 并不会让单个 prime factor 的横向二阶响应发散。

### 定理 A11.1　单局部因子无黄金深度相变

对固定 $p$ 与 $\sigma>0$，Zeckendorf exponent tower 在 Euler Gibbs 权下的二阶 exponent moment 随 $Q\to\infty$ 收敛到式 (A11.3)，不按 $\varphi^{2Q}$ 发散。

因此：

$$
\boxed{
\text{组合状态数增长}
\not\Rightarrow
\text{Euler 加权能量增长}.
}
\tag{A11.4}
$$

真正的临界现象若存在，必须来自 primes 数量随尺度增长、prime phases 的 collective alignment、Gamma／pole completion、analytic continuation，或 zero-side 与 prime-side 之间的非局部谱输运。

---

# 增订一·12　黄金 renormalization 可以稳定几何，却不能自动稳定质量

## 12.1 log-gap 与 Fibonacci shell 的互补缩放

固定 $P_0>0$ 和 additive gap $g>0$，令

$$
P_Q=P_0\varphi^Q.
\tag{A12.1}
$$

则

$$
\boxed{
\lim_{Q\to\infty}
F_Q\log\left(1+\frac g{P_Q}\right)
=
\frac g{\sqrt5P_0}.
}
\tag{A12.2}
$$

#### 证明

使用

$$
F_Q\varphi^{-Q}\to\frac1{\sqrt5}
$$

与

$$
\log(1+g/P_Q)\sim g/P_Q.
$$

因此若 prime scale 约乘 $\varphi$，同时 Zeckendorf shell 深度增加一层，则

$$
F_Q\Delta\log p
$$

可以保持非退化。

于是归一化横向能量具有有限极限：

$$
\sinh^2\!\left(
\delta F_Q\log(1+g/P_Q)
\right)
\longrightarrow
\sinh^2\!\left(
\frac{\delta g}{\sqrt5P_0}
\right).
\tag{A12.3}
$$

这给出一个真正的 golden tangent fixed scale：

$$
\boxed{
\text{Fibonacci shell 增长 }\varphi^Q
\quad\text{抵消}\quad
\text{固定 additive gap 的 log-frequency 收缩 }\varphi^{-Q}.
}
\tag{A12.4}
$$

## 12.2 但 Euler 质量超指数衰减

若同一个 $F_Q$ 被解释成 prime-power exponent，则对应 scalar Euler weight 包含

$$
P_Q^{-\sigma F_Q}
=
\exp\!\left(-\sigma F_Q\log P_Q\right).
\tag{A12.5}
$$

由于

$$
F_Q\asymp\varphi^Q,
\qquad
\log P_Q\asymp Q,
$$

该权重按

$$
\exp(-cQ\varphi^Q)
\tag{A12.6}
$$

超指数衰减。

所以：

$$
\boxed{
\text{归一化几何可以处在 fixed scale，
实际 Euler mass 却可以趋于零。}
}
\tag{A12.7}
$$

这说明 Zeckendorf–PrimeGap renormalization 目前只建立了几何／observer 分辨结构，尚未建立 zeta 配分权下的非消失贡献。

要形成真正的 multiscale sticky tower，必须另外证明 completion measure 对这些 shell 提供足够质量。该质量不能由状态数或归一化 kernel 自动生成。

---

# 增订一·13　一阶信息消失、二阶能量显影的统一原理

## 13.1 抽象二次显影定理

设 $d$ 是一个在 involution 下变号的缺陷：

$$
d\longmapsto-d.
\tag{A13.1}
$$

若标量 observable $A$ 对该 involution 不变，

$$
A(d)=A(-d),
\tag{A13.2}
$$

且 $A$ 在 $0$ 可微，则

$$
\boxed{A'(0)=0.}
\tag{A13.3}
$$

若 $A$ 解析，则其 Taylor 展开只含偶次项：

$$
A(d)=A(0)+a_2d^2+a_4d^4+\cdots.
\tag{A13.4}
$$

所以被反射压掉的一阶有符号信息，第一种可由 invariant scalar 稳定读取的量通常是平方能量。

## 13.2 项目中的六个实例

1. reciprocal roots：$\log r+\log r^{-1}=0$，但 $(\log r)^2+(\log r^{-1})^2>0$；
2. ordered holonomy：一阶 observer response 为零，负二阶 response 是平方 winding 的非负加权和；
3. prime jump：共同 translation 模式被消去以后，剩余量为 $\|f-\mathsf T_af\|_2^2\ge0$；
4. prime transverse split：$\sinh^2(\delta\Delta\omega)=\delta^2\Delta\omega^2+O(\delta^4)$；
5. off-line zero odd channel：$E_{\mathrm{odd}}=4m_\rho|A_{\mathrm{odd}}|^2\ge0$；
6. golden innovation：$\sum\xi_v=O(1)$，而 $N^{-1}\sum\xi_v^2\to\varphi^{-3}>0$。

这六个对象并不相等，但它们共享同一结构法则：

$$
\boxed{
\text{有符号／有序／反射信息在一阶 scalar 中冲销，
在二阶正能量中重新显影。}
}
\tag{A13.5}
$$

这就是 Zeckendorf、jump energy、holonomy Casimir、Lee–Yang radial defect 和 off-line odd energy 真正相关的原因。

---

# 增订一·14　假想离线零点的联合能量图景

设

$$
\rho_*
=
\frac12+\delta_*+it_*,
\qquad
\delta_*\ne0
\tag{A14.1}
$$

是一个假想离线零点。

本卷前文已经得到：同高度存在反射零点；Cayley 坐标中出现同角 reciprocal radial pair；scalar visible energy 满足 $V(t_*,\delta_*)=0$；若中心非零则发生 $\mathbb Z_2$ reflected phase split；若零点简单则发生二次 gap closing、相位翻转和局部涡旋。

另一方面，对任意不同 primes $p,q$：

$$
\sinh^2\!\left(
\delta_*\log\frac qp
\right)>0.
\tag{A14.2}
$$

对任意非平凡有限 Zeckendorf depth 与 prime cluster：

$$
\mathscr E_{Q,\mathcal C}^{\perp}(\delta_*)>0.
\tag{A14.3}
$$

于是形成一个严格的并置事实：

$$
\boxed{
\text{zero-side scalar value}=0,
\qquad
\text{independently defined finite relation detector}>0.
}
\tag{A14.4}
$$

但“并置”不是“矛盾”。式 (A14.4) 中两边目前没有 canonical identity 或 domination theorem 相连。

因此严谨表述只能是：

$$
\boxed{
\text{离线零点是一个 candidate scalar/relation coercivity-gap closing event。}
}
\tag{A14.5}
$$

要把 candidate 变成 theorem，必须证明 relation detector 是 completed explicit formula 中 odd channel 的真实下界或等价范数。

---

# 增订一·15　信息逃逸究竟发生在哪一层

## 15.1 不发生在 Zeckendorf state decode

因为 $E_Q$ 是双射，

$$
\ker(E_Q)=\Delta_{\Omega_Q}.
\tag{A15.1}
$$

所以精确指数能量没有微观状态碰撞。

## 15.2 发生在结构到标量配分的投影

考虑带关系的模型类

$$
\mathfrak M=(\Omega_Q,E_Q,\mathcal R).
\tag{A15.2}
$$

定义 scalar readout

$$
\Pi_{\mathrm{sc}}(\mathfrak M)
=
\sum_{\eta\in\Omega_Q}x^{E_Q(\eta)}.
\tag{A15.3}
$$

它与 $\mathcal R$ 无关。于是任意两个不同关系结构 $\mathcal R_1\ne\mathcal R_2$，只要共享同一个能量标号，就满足

$$
\Pi_{\mathrm{sc}}(\Omega_Q,E_Q,\mathcal R_1)
=
\Pi_{\mathrm{sc}}(\Omega_Q,E_Q,\mathcal R_2).
\tag{A15.4}
$$

这就是一个非平凡 model-level kernel。

若模型空间只含这两个模型，则 scalar readout 对唯一非对角有序 pair 全部碰撞，信息逃逸率为 $1$。若再加入一个能区分 $\mathcal R_1,\mathcal R_2$ 的 Laplacian、Hankel、carry 或 holonomy readout，联合 kernel 退化为对角线，逃逸率降为 $0$。

因此：

$$
\boxed{
\text{Zeckendorf 的信息价值不在重新命名整数，
而在把被 scalar partition 遗忘的 CUT/FLOW 关系重新对象化。}
}
\tag{A15.5}
$$

## 15.3 结构读出层级

可以把当前项目中的 readouts 排成：

$$
\begin{aligned}
\mathcal O_0&=\text{整数 exponent / scalar Euler factor},\\
\mathcal O_1&=\text{occupation polynomial / hard-core transfer},\\
\mathcal O_2&=\text{stable shadow / least-index parity},\\
\mathcal O_3&=\text{successor and arithmetic jump Dirichlet form},\\
\mathcal O_4&=\text{ordered holonomy / exterior pair energy},\\
\mathcal O_5&=\text{zero-side off-line odd spectral energy}.
\end{aligned}
\tag{A15.6}
$$

它们不是简单的数值精度递增，而是在逐步恢复不同类型的关系：值、一步记忆、Galois 稳定修正、动态创新、cross-prime 顺序与二体关系，以及 zero orbit 的反对称谱风险。

低信息逃逸的最终对象不应选择其中一个替代其余，而应证明哪些层通过 canonical morphism 可以互相恢复。

---

# 增订一·16　两个等价风格的最终开放桥

## 16.1 能量支配形式

需要构造 canonical 权重和完成映射，使

$$
\boxed{
E_{\mathrm{off}}^{\mathrm{odd}}(g)
\le
C\Bigl(
E_{\mathrm{jump}}^{\mathrm{Zeck}}(g)
+
E_{\mathrm{hol}}^{\mathrm{gold}}(g)
+
E_{\mathrm{prime}}^{\perp}(g)
\Bigr)
+\varepsilon(g).
}
\tag{A16.1}
$$

并在受控极限中证明

$$
\varepsilon(g)\to0.
\tag{A16.2}
$$

式 (A16.1) 目前是目标，不是定理。三种 prime-side energy 也不能在未给出共同 Hilbert space 和嵌入以前直接相加；严格版本必须先把它们运输到同一有限 Galerkin 空间。

## 16.2 transfer equimodular confinement 形式

另一种表达是构造 canonical completed prime–Zeckendorf transfer cocycle，其两个主通道具有 Lyapunov exponents

$$
L_+(s),\qquad L_-(s).
\tag{A16.3}
$$

Zeckendorf hard-core 原型说明，有限配分零点发生在两个 transfer channels 等模并满足相位量子化的位置。

### 猜想 A16.1　Arithmetic equimodular confinement

对 canonical completed cocycle，

$$
\boxed{
L_+(s)=L_-(s)
\Longrightarrow
\Re s=\frac12.
}
\tag{A16.4}
$$

并且 completed determinant 的零点只能出现在该等模集合上。若两部分均建立，则推出 RH。

这条猜想把三种语言统一：

$$
\boxed{
\begin{aligned}
\text{Weil 语言}&:\text{odd energy 不产生负性},\\
\text{Lee–Yang 语言}&:\text{根不离临界圆},\\
\text{transfer 语言}&:\text{等模集合被限制在反射固定轴}.
\end{aligned}
}
\tag{A16.5}
$$

## 16.3 为什么 Zeckendorf 是候选而非答案

Zeckendorf 提供了唯一 hard-core normal form、最小二态记忆、扩张／稳定 Galois 通道、稀疏 Fibonacci shell factorization、精确 balanced innovation，以及与 prime log-gap 互补的尺度增长。

但它尚未提供 canonical zeta transfer operator、Gamma completion channel、prime-pair energy 的真实全局权、zero-side odd energy 的无条件支配、极限紧性和测试族分离性。

所以最准确的判断是：

$$
\boxed{
\text{Zeckendorf 给出了 RH 相变问题可能需要的最小 memory geometry，
但没有自动给出该 geometry 在 completed }\Xi\text{ 中的动力学权。}
}
\tag{A16.6}
$$

---

# 增订一·17　黄金隐藏通道临界性

前述结构可压缩为：

$$
\boxed{
\begin{array}{ccccc}
\text{integer exponent}
&\xrightarrow{\text{Zeckendorf}}
&\text{hard-core history}
&\xrightarrow{\text{Galois split}}
&(\varphi\text{-expanding},\psi\text{-stable})
\\[2mm]
&&\downarrow\text{successor / carry}
&&\downarrow\text{quadratic reveal}
\\[2mm]
\text{scalar Euler}
&\xleftarrow{\text{forget relation}}
&\text{jump energy}
&\longrightarrow
&\text{prime exterior energy}
\\[2mm]
&&&&\downarrow\text{missing transport}
\\[2mm]
&&&&\text{off-line odd energy}.
\end{array}
}
\tag{A17.1}
$$

这里最深的结构不是“所有对象数值相等”，而是：标量读出反复删除有符号关系信息；被删除的信息在稳定／反对称通道中保留；对称性使一阶读出归零；第一忠实读出成为正的二阶能量；相变发生在 scalar gap 闭合而二阶 relation mode 仍存活的位置。

据此，可以把假想第一离线高度重新表述为：

$$
\boxed{
T_{\mathrm{off}}
=
\text{completed scalar channel 首次允许零值，
同时一个尚未被证明可输运的稳定 relation channel 仍可能携带正能量的高度}.
}
\tag{A17.2}
$$

而 RH 的黄金隐藏通道版本是：

$$
\boxed{
\text{completed prime–Gamma dynamics 不允许任何 Zeckendorf／holonomy 稳定影子
在反射固定轴外与主通道达到可产生零点的等模状态}.
}
\tag{A17.3}
$$

式 (A17.3) 是研究纲领，不是已证等价；其成为严格 RH 等价的前提，是完成第 A16 节的 canonical transfer/determinant 构造。

---

# 增订一·18　结论地位总表

| 结论 | 地位 |
|---|---|
| 合法 Zeckendorf words 与 $[0,F_{Q+2})$ 双射 | 仓库机器闭合 |
| 有限 Zeckendorf exponent partition 是几何级数 | 仓库机器闭合 |
| 其非平凡根在局部 fugacity 单位圆 | 直接推论 |
| 该圆等于 RH Cayley 临界圆 | 不成立 |
| Zeckendorf 重编码改变单 Euler factor | 不成立 |
| hard-core occupation partition 满足二阶递推 | 纯有限定理 |
| $z=1$ 的 transfer eigenvalues 为 $\varphi,-\varphi^{-1}$ | 纯有限定理 |
| hard-core zeros 位于负实轴并趋向 $-1/4$ | 纯有限定理 |
| Fibonacci count sequence 的最小 realization dimension 为 $2$ | 有限证明 + 仓库 Hankel 定理 |
| 黄金指数增量取 $\varphi^2$ 或 $\varphi$ | 仓库机器闭合 |
| 扣除 $\sqrt5$ 后创新均方为 $\varphi^{-3}$ | 本增订直接推论 |
| prime-power translation 有 Zeckendorf shell 精确因子分解 | 本增订有限定理 |
| 总 jump energy 自动下界每个 shell energy | 不成立；只有上界 |
| Zeckendorf–prime susceptibility 二阶乘法分离 | 本增订有限定理 |
| 均匀状态 susceptibility 按 $\varphi^{2Q}$ 增长 | 本增订直接推论 |
| 单 Euler Gibbs ensemble 同样发散 | 不成立；二阶矩有限 |
| Fibonacci shell 可补偿 short log-gap 的几何收缩 | 本增订条件极限定理 |
| 该补偿自动克服 Euler mass 衰减 | 不成立 |
| scalar first-order cancellation 与 quadratic energy reveal 是共同机制 | 抽象定理 + 多个仓库实例 |
| prime transverse energy 已支配 off-line odd energy | 尚未建立 |
| canonical transfer 的等模集合只在临界线 | 新核心猜想 |
| 本增订证明 RH | 不成立 |

---

# 增订一·19　最终收束

Zeckendorf、黄金比例、能量、Lee–Yang 和离线零点确实属于同一张结构图，但它们的关系不是：

$$
\text{出现 }\varphi
\Longrightarrow
\mathrm{RH}.
$$

真正的关系是：

$$
\boxed{
\begin{aligned}
\text{Zeckendorf 唯一性}
&\Longrightarrow
\text{整数指数可无损提升为 hard-core history},\\
\text{hard-core history}
&\Longrightarrow
\text{最小二态 transfer 与 }(\varphi,-\varphi^{-1})\text{ 双通道},\\
\text{稳定影子}
&\Longrightarrow
\text{有界一阶校正与正二阶创新能量},\\
\text{prime log-gap}
&\Longrightarrow
\text{同一复核中的时间相位与横向 }\sinh^2\text{ 能量},\\
\text{Zeckendorf depth}\times\text{prime variance}
&\Longrightarrow
\text{有限横向 susceptibility},\\
\text{scalar completion}
&\Longrightarrow
\text{这些关系量可能被压缩或冲销},\\
\text{off-line zero}
&\Longrightarrow
\text{若存在，则 scalar zero 与正 relation detector 在同一高度并置}.
\end{aligned}
}
\tag{A19.1}
$$

最后一步还不是矛盾，因为 canonical transport 尚未建立。

因此本增订的最终命题是：

$$
\boxed{
\textbf{RH 的潜在黄金机制，不是 Fibonacci 数值神秘地控制零点，
而是最小 hard-core memory 的稳定影子能否在 prime–Gamma 完成后
被一个正二阶能量完全审计。}
}
\tag{A19.2}
$$

若审计完成，则所有反射轴外的 odd relation mode 都必须付出正能量，而 completed scalar zero 无法在该能量仍为正时发生。若审计不能完成，则 Zeckendorf 仍只是一个优美、无损、但与 RH 承重桥分离的坐标系统。

这把下一步研究压缩成唯一问题：

$$
\boxed{
\text{能否从 canonical Zeckendorf carry / golden holonomy / prime jump energy
构造一个由显式公式识别的正算子，
其零空间恰好等于 critical-line phase，
其正空间恰好包含全部 off-line odd modes？}
}
\tag{A19.3}
$$

在这条算子桥闭合以前，所有“黄金比例解释 RH”的表述都只能是结构候选；在它闭合以后，Zeckendorf 才会从命名坐标真正升级为 completed zeta 的动力学内核。
