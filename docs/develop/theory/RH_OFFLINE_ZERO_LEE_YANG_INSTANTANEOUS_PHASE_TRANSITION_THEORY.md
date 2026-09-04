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

---

# 增订二　黄金判别式谱覆盖、Lorentz 二通道与算术等模禁闭

> 本增订继续压缩前两部分的共同结构。以下公式使用 `B` 前缀独立编号。本文仍为纯数学理论：已由仓库 Lean 真源承担的有限结论、本文直接推导的有限结论、条件性 completed 模型与 RH 承重猜想严格分层。

## 摘要

增订一已经表明，Zeckendorf 的意义不在于改变整数指数或 Euler 标量，而在于把整数提升为带一步 hard-core memory 的唯一历史；黄金比例则是该最小二态系统的扩张本征值，负共轭 $-\varphi^{-1}$ 是精确性不可删除的稳定影子。

本增订进一步发现：这些结构并非若干彼此相似的公式，而是同一条二次谱覆盖的不同纤维。

定义加权 hard-core transfer

$$
T(z)=
\begin{pmatrix}
1&z\\
1&0
\end{pmatrix}.
$$

其特征方程为

$$
\lambda^2-\lambda-z=0,
$$

判别式为

$$
D(z)=1+4z.
$$

于是：

- 热力学边缘 $z=-\tfrac14$ 是 $D(z)=0$ 的解析分歧点；
- 黄金无权纤维 $z=1$ 给出 $D(1)=5$，本征值恰为 $\varphi$ 与 $-\varphi^{-1}$；
- 将该纤维模素数约化时，两个通道是否在本地分裂，恰由 $5$ 的二次剩余性控制；
- 对非分歧素数，Frobenius 对两个通道的作用正是恒等或交换，而项目的模 $5$ 黄金二次特征正记录这一 Weyl 符号；
- 围绕解析分歧点的 monodromy 与惰性素数的 Frobenius 都执行同一个 deck involution：交换两条谱支。

这给出本轮最重要的精确结论：

$$
\boxed{
\text{Zeckendorf 的黄金双通道、模 }5\text{ 的 split/inert 素数、}
\text{以及 Lee--Yang 等模分支，来自同一二次谱覆盖的解析与算术作用。}
}
\tag{B0.1}
$$

本增订还建立一条此前隐藏的有限恒等式。令 $J_N$ 为长度 $N$、零边界的最近邻平均算子，则

$$
\boxed{
\det(I_N+4zJ_N^2)=H_{N-1}(z)^2,
}
\tag{B0.2}
$$

其中 $H_{N-1}$ 是 Zeckendorf hard-core occupation polynomial。项目已经机器证明，参考系交换通道的 entanglement fidelity 正是 $\|J_Nc\|_2^2$，其最优值为

$$
F_N^*=\cos^2\frac{\pi}{N+1}.
$$

而当 $N\ge2$ 时，hard-core 配分函数离临界边缘最近的零点精确满足

$$
\boxed{
z_{N-1}^{\mathrm{near}}=-\frac1{4F_N^*}.}
\tag{B0.3}
$$

因此有限参考系的最优 fidelity tax 与有限配分零点离热力学边缘的距离，是同一条 path spectrum 的两个精确读出，而不是数值巧合。

最后，本增订把 prime-pair 横向能量提升为三种等价的有限局部几何：

$$
\boxed{
\text{外积 Gram 能量}
\quad\Longleftrightarrow\quad
\text{最小奇异值打开}
\quad\Longleftrightarrow\quad
\text{反射通道 fidelity 损失}.
}
\tag{B0.4}
$$

这三者在临界线附近都由 weighted variance of $\log p$ 控制。于是 RH 的承重问题可以进一步收紧为：能否从 completed prime--Zeckendorf--Gamma cocycle 构造一个保持边界横截性、在临界线外具有 dominated splitting、并与 zero-side odd channel 互 intertwine 的正算子。

---

# 增订二·0　理论地位与真源边界

本增订使用下列仓库真源，但不把它们扩大解释为 RH 证明：

1. `GoldenNames` 与 `FiniteZeckendorfEulerIdentity`：Zeckendorf 合法词、Fibonacci 初始区间与有限 Euler 和；
2. `GoldenEulerBetaZeckendorf`：黄金指数账户与最小指标奇偶控制；
3. `GoldenCharacterQuotient`：非分歧素数的模 $5$ 二次特征给出 $\{\pm1\}$ 商，乘积等于惰性字母数的奇偶；
4. `GoldenScalarDihedralBlindness`：完整标量黄金世界不能恢复有序 prime-word dihedral holonomy；
5. `OrderedPrimeHolonomyCasimir`：一阶有序响应消失，负二阶响应为平方 winding 的非负和；
6. `ChannelFidelityBridge`：有限 excitation-exchange channel 的 entanglement fidelity 等于最近邻二次型并等于 path averaging 范数平方；
7. `TopEigenspace`：$J_N^2$ 的顶本征空间由正负边缘 sine modes 配对生成，最优二次值为 $\cos^2(\pi/(N+1))$；
8. `LocalPositiveSquareCompletion`：正对角完成的 determinant 零点位于负实轴；
9. `PrimitiveBundle`：有限角色标记原语族的联合不可区分核等于各原语 kernel 的交；
10. `OffLineOrbitParityDecomposition`：supplied 离线四点轨道的 Weil 贡献等于 even energy 减 odd energy，两者分别非负。

本文新推导的有限恒等式包括：判别式五的谱覆盖解释、Lorentz 共形关系、Frobenius--monodromy 同一 deck action、path-fidelity determinant 恒等式、fidelity tax 与最近零点的精确换算、hard-core 平稳链协方差、prime reflected Gramian 与 fidelity 的精确关系、以及共同 Galerkin 张量微分。

以下命题仍明确保持开放：

- Riemann completed $\Xi$ 已经等于本文某个有限 transfer determinant 的极限；
- Gamma 因子已经被黄金 hard-core transfer 无条件恢复；
- 模 $5$ 黄金特征决定全部 zeta zeros；
- prime reflected fidelity 已经等于 zero-side odd energy；
- completed cocycle 在临界线外已经证明 dominated splitting；
- 边界向量对主通道的耦合已经证明不消失；
- RH 已被证明。

---

# 增订二·1　通用 hard-core transfer 与二次谱覆盖

## B1.1 加权一步记忆系统

令

$$
T(z)=
\begin{pmatrix}
1&z\\
1&0
\end{pmatrix},
\qquad z\in\mathbb C.
\tag{B1.1}
$$

若状态向量的两个分量分别表示“末位未占据”和“末位已占据”，则一次长度增长由 $T(z)$ 完成。其特征多项式为

$$
\boxed{
\chi_z(\lambda)
=\det(\lambda I-T(z))
=\lambda^2-\lambda-z.
}
\tag{B1.2}
$$

定义判别式

$$
\boxed{D(z)=1+4z.}
\tag{B1.3}
$$

在选择平方根以后，两条谱支为

$$
\boxed{
\lambda_\pm(z)
=\frac{1\pm\sqrt{D(z)}}2.
}
\tag{B1.4}
$$

并满足

$$
\lambda_++\lambda_-=1,
\qquad
\lambda_+\lambda_-=-z.
\tag{B1.5}
$$

## B1.2 谱曲线

定义二次谱覆盖

$$
\boxed{
\Sigma
=
\{(z,y)\in\mathbb C^2:y^2=1+4z\}.
}
\tag{B1.6}
$$

在 $\Sigma$ 上，

$$
\lambda_\pm=\frac{1\pm y}{2}.
\tag{B1.7}
$$

覆盖的 deck involution 为

$$
\boxed{
\iota(z,y)=(z,-y),
}
\tag{B1.8}
$$

它精确交换

$$
\lambda_+\longleftrightarrow\lambda_-.
\tag{B1.9}
$$

因此“二通道”不是人为把一个标量复制两次，而是单值化平方根所必需的最小谱覆盖。

## B1.3 三个决定性纤维

### 零活动纤维

当 $z=0$：

$$
D(0)=1,
\qquad
(\lambda_+,\lambda_-)=(1,0).
\tag{B1.10}
$$

一条通道完全消失，系统退化为无占据背景。

### 分歧纤维

当

$$
z_c=-\frac14,
\tag{B1.11}
$$

有

$$
D(z_c)=0,
\qquad
\lambda_+=\lambda_-=\frac12.
\tag{B1.12}
$$

这是二次覆盖的唯一有限分歧点，也是 hard-core 零点的热力学边缘。

### 黄金纤维

当 $z=1$：

$$
D(1)=5,
\tag{B1.13}
$$

从而

$$
\boxed{
\lambda_+(1)=\frac{1+\sqrt5}{2}=\varphi,
\qquad
\lambda_-(1)=\frac{1-\sqrt5}{2}=-\varphi^{-1}.
}
\tag{B1.14}
$$

因此判别式五不是后来附加给 Fibonacci 递推的神秘常数，而是通用 hard-core 谱覆盖在物理无权活动 $z=1$ 上的纤维值：

$$
\boxed{5=D(1).}
\tag{B1.15}
$$

---

# 增订二·2　解析 monodromy 与算术 Frobenius 是同一通道交换

## B2.1 围绕分歧点的解析 monodromy

令 $z$ 沿一个小闭环绕 $-1/4$ 一周。平方根

$$
\sqrt{1+4z}
$$

改变符号，因此解析延拓执行

$$
\lambda_+\longleftrightarrow\lambda_-.
\tag{B2.1}
$$

这正是 deck involution $\iota$。

## B2.2 黄金纤维的模素数约化

在 $z=1$，特征多项式为

$$
\boxed{
\chi_1(\lambda)=\lambda^2-\lambda-1,
}
\tag{B2.2}
$$

判别式为 $5$。

令 $p$ 为奇素数且 $p\ne5$。在 $\mathbb F_p$ 上：

- 若 $5$ 是平方，则 $\chi_1$ 分解为两个不同线性因子；
- 若 $5$ 不是平方，则 $\chi_1$ 在 $\mathbb F_p$ 上不可约，并只在 $\mathbb F_{p^2}$ 上分裂。

因此：

$$
\boxed{
\chi_1\text{ 在 }\mathbb F_p\text{ 上分裂}
\Longleftrightarrow
\left(\frac5p\right)=+1.
}
\tag{B2.3}
$$

而

$$
\boxed{
\chi_1\text{ 在 }\mathbb F_p\text{ 上惰性}
\Longleftrightarrow
\left(\frac5p\right)=-1.
}
\tag{B2.4}
$$

由于 $5\equiv1\pmod4$，二次互反律给出

$$
\boxed{
\left(\frac5p\right)
=
\left(\frac p5\right).
}
\tag{B2.5}
$$

右侧正是项目 `GoldenCharacterQuotient` 使用的黄金二次特征。

## B2.3 Frobenius 的通道作用

在 $\mathbb F_{p^2}$ 中取

$$
y^2=5.
$$

Euler 判别给出

$$
y^p
=5^{(p-1)/2}y
=\left(\frac5p\right)y.
\tag{B2.6}
$$

故 Frobenius 作用为

$$
\boxed{
\operatorname{Frob}_p(y)
=\chi_5(p)y,
\qquad
\chi_5(p)=\left(\frac p5\right).
}
\tag{B2.7}
$$

于是：

- $\chi_5(p)=+1$ 时，Frobenius 固定两条本征线；
- $\chi_5(p)=-1$ 时，Frobenius 交换两条本征线。

换言之：

$$
\boxed{
\text{黄金二次特征就是 Frobenius 在二通道谱覆盖上的 Weyl 符号。}
}
\tag{B2.8}
$$

## B2.4 分歧素数与素数二

当 $p=5$，判别式消失，$\chi_1$ 具有重根；这是算术分歧纤维，而不是 split 或 inert 纤维。

当 $p=2$，

$$
\chi_1(\lambda)
\equiv
\lambda^2+\lambda+1
\pmod2
\tag{B2.9}
$$

在 $\mathbb F_2$ 上不可约，所以素数 $2$ 单独属于惰性类型。该边界必须单列，不能把只对奇素数定义的普通 Legendre 公式未经说明地套到 $2$ 上。

## B2.5 Frobenius--monodromy 同一性

解析侧绕分歧点一次执行

$$
y\mapsto-y.
$$

算术侧每个惰性素数的 Frobenius 也执行

$$
y\mapsto-y.
$$

因此：

$$
\boxed{
\text{解析 monodromy 与惰性 Frobenius 是同一二次谱覆盖的同一个非平凡 deck action。}
}
\tag{B2.10}
$$

这条同一性是严格的有限代数事实。它并不意味着 zeta 的解析延拓由模 $5$ 字符单独决定；它说明项目中的黄金字符、二态 transfer 和分支交换确实共享一个真实的谱几何母体。

---

# 增订二·3　Lorentz 二次型与相型签名

## B3.1 与 transfer 相容的二次型

定义

$$
\boxed{
q_z(X,Y)
=-X^2+XY+zY^2,
}
\tag{B3.1}
$$

其对称矩阵为

$$
J_z=
\begin{pmatrix}
-1&\tfrac12\\
\tfrac12&z
\end{pmatrix}.
\tag{B3.2}
$$

直接计算得

$$
\boxed{
T(z)^\mathsf TJ_zT(z)
=-zJ_z.
}
\tag{B3.3}
$$

所以 $T(z)$ 不是任意二阶递推矩阵，而是 $q_z$ 的共形 Lorentz 变换；共形因子为 $-z$。

## B3.2 null directions 就是 transfer channels

对斜率向量 $(\lambda,1)$：

$$
q_z(\lambda,1)
=-\lambda^2+\lambda+z.
\tag{B3.4}
$$

因此

$$
\boxed{
q_z(\lambda,1)=0
\Longleftrightarrow
\lambda^2-\lambda-z=0.
}
\tag{B3.5}
$$

也就是说，两条 transfer 本征通道正是关系二次型的两条 null directions。

## B3.3 判别式就是 metric determinant

有

$$
\boxed{
\det J_z
=-\frac{1+4z}{4}
=-\frac{D(z)}4.
}
\tag{B3.6}
$$

所以谱判别式和关系 metric 的非退化判别式完全相同。

对实 $z$：

### 双曲相

若

$$
z>-\frac14,
$$

则 $D(z)>0$、$\det J_z<0$，故 $q_z$ 不定并具有两条实 null rays。两条 transfer channels 可在实数上区分。

### 抛物临界相

若

$$
z=-\frac14,
$$

则 $J_z$ 退化，两条 null rays 合并。这是 transfer collision 与 metric degeneration 的同一点。

### 椭圆相

若

$$
z<-\frac14,
$$

则 $D(z)<0$。此时 $q_z$ 为负定，实 null directions 消失，而两条本征值成为等模复共轭对。

因此：

$$
\boxed{
\text{hard-core edge 不只是根的聚点；它是关系 metric 从双曲型经退化转为椭圆型的签名相变。}
}
\tag{B3.7}
$$

## B3.4 黄金 norm form

在 $z=1$，

$$
q_1(X,Y)=-X^2+XY+Y^2.
\tag{B3.8}
$$

令 $K=\mathbb Q(\sqrt5)$，则

$$
\operatorname{Norm}_{K/\mathbb Q}(X-Y\varphi)
=X^2-XY-Y^2.
\tag{B3.9}
$$

故

$$
\boxed{
q_1(X,Y)
=-\operatorname{Norm}_{K/\mathbb Q}(X-Y\varphi).
}
\tag{B3.10}
$$

黄金 Lorentz metric 正是实二次域 $\mathbb Q(\sqrt5)$ 的 norm form，差一个整体符号和基选择。

---

# 增订二·4　黄金单位、Lorentz boost 与二面体 normalizer

## B4.1 一步 transfer 是 norm $-1$ 单位作用

记

$$
A=T(1)=
\begin{pmatrix}
1&1\\
1&0
\end{pmatrix}.
\tag{B4.1}
$$

其 determinant 为

$$
\det A=-1,
\tag{B4.2}
$$

且

$$
A^\mathsf TJ_1A=-J_1.
\tag{B4.3}
$$

这对应黄金单位

$$
\operatorname{Norm}(\varphi)=-1.
\tag{B4.4}
$$

所以一次 Fibonacci transfer 是 orientation-reversing 的 Lorentz unit；其平方才进入 proper boost 分量。

## B4.2 两步 transfer 是 proper boost

有

$$
A^2=
\begin{pmatrix}
2&1\\
1&1
\end{pmatrix},
\qquad
(A^2)^\mathsf TJ_1A^2=J_1.
\tag{B4.5}
$$

其本征值为

$$
\varphi^2,
\qquad
\varphi^{-2}.
\tag{B4.6}
$$

令标准 boost

$$
B(u)=
\begin{pmatrix}
\cosh u&\sinh u\\
\sinh u&\cosh u
\end{pmatrix}.
\tag{B4.7}
$$

则 $A^2$ 在一个实正交坐标变换后等价于

$$
\boxed{B(2\log\varphi).}
\tag{B4.8}
$$

因此黄金递推深度的两步增长，是离散 rapidity

$$
2\log\varphi
\tag{B4.9}
$$

的 Lorentz boost。

## B4.3 三种 rapidity 是同型坐标而非相同数值

本理论中出现三类 reciprocal pairs：

1. Cayley 零点对：$e^{\pm\eta_a(t,\delta)}$；
2. prime reflected pair：$e^{\pm\delta\Delta\omega_{p,q}}$；
3. golden transfer 两步通道：$e^{\pm2\log\varphi}$。

去掉共同复相位以后，它们都属于同一个 split Cartan 形式

$$
\operatorname{diag}(e^u,e^{-u}).
\tag{B4.10}
$$

所以：

$$
\boxed{
\eta_a(t,\delta),
\quad
\delta\log(q/p),
\quad
2\log\varphi
}
\tag{B4.11}
$$

是同一种 rank-one Lorentz 坐标的三个实例，但没有任何理由把它们数值相等。

## B4.4 Weyl reflection 与有序乘法

令 $W$ 满足

$$
W^2=I,
\qquad
WB(u)W=B(-u).
\tag{B4.12}
$$

则 boost torus 与 $W$ 生成无限二面体型 normalizer。

把一个局部因子写成

$$
g_j=B(u_j)W^{e_j},
\qquad e_j\in\{0,1\},
\tag{B4.13}
$$

并记

$$
\epsilon_j=(-1)^{e_j}.
\tag{B4.14}
$$

则有序乘积的总 rapidity 为

$$
\boxed{
U_n
=u_1+
\epsilon_1u_2+
\epsilon_1\epsilon_2u_3+
\cdots+
\left(\prod_{j=1}^{n-1}\epsilon_j\right)u_n.
}
\tag{B4.15}
$$

而最终 Weyl parity 仅为

$$
\epsilon_{\mathrm{tot}}
=
\prod_{j=1}^n\epsilon_j.
\tag{B4.16}
$$

所以模 $5$ 黄金 character quotient 只记录最终通道交换奇偶；它一般不能恢复有序 rapidity $U_n$。这正解释了为什么 permutation-invariant character 与 ordered dihedral holonomy 必须分层。

## B4.5 标量 trace 的盲性

proper boost 的 trace 为

$$
\operatorname{tr}B(u)=2\cosh u,
\tag{B4.17}
$$

满足

$$
\operatorname{tr}B(u)
=
\operatorname{tr}B(-u).
\tag{B4.18}
$$

因此 scalar trace 删除 rapidity 的符号。其一阶导数在 $u=0$ 消失，而二阶导数为正：

$$
\left.\frac d{du}2\cosh u\right|_{u=0}=0,
\qquad
\left.\frac{d^2}{du^2}2\cosh u\right|_{u=0}=2.
\tag{B4.19}
$$

这给出 ordered holonomy Casimir、reciprocal radial energy 与 prime transverse energy 的共同 rank-one group 原型。

---

# 增订二·5　hard-core 等模边缘与精确有限尺寸律

## B5.1 occupation polynomial

仍令

$$
H_Q(z)=H_{Q-1}(z)+zH_{Q-2}(z),
\quad
H_0=1,
\quad
H_1=1+z.
\tag{B5.1}
$$

在 $D(z)\ne0$ 时，

$$
\boxed{
H_Q(z)
=
\frac{\lambda_+(z)^{Q+2}-\lambda_-(z)^{Q+2}}
{\lambda_+(z)-\lambda_-(z)}.
}
\tag{B5.2}
$$

## B5.2 完整等模集合

若

$$
|\lambda_+(z)|=|\lambda_-(z)|,
\tag{B5.3}
$$

则由 $\lambda_++\lambda_-=1$ 可知二者必为复共轭，除非和为零；后者与和为 $1$ 矛盾。因此 $z=-\lambda_+\lambda_-$ 必为负实数，并有 $D(z)\le0$。

反之，当 $z\le-1/4$ 为实数时，两根互为复共轭或重合，故等模。

所以：

$$
\boxed{
|\lambda_+(z)|=|\lambda_-(z)|
\Longleftrightarrow
z\in(-\infty,-1/4].
}
\tag{B5.4}
$$

hard-core 的等模 locus 是一条完整负实割线，而不只是端点。

## B5.3 有限零点量子化

有限零点满足

$$
\left(\frac{\lambda_+}{\lambda_-}\right)^{Q+2}=1.
\tag{B5.5}
$$

从而

$$
\boxed{
z_{Q,j}
=-\frac1{4\cos^2\left(\frac{j\pi}{Q+2}\right)},
\qquad
1\le j\le\left\lfloor\frac{Q+1}{2}\right\rfloor.}
\tag{B5.6}
$$

所有根位于等模割线上，但不会等于分歧点本身。

## B5.4 分歧点上的有限配分函数不为零

在 $z=-1/4$，两根合并为 $1/2$。取式 (B5.2) 的极限得

$$
\boxed{
H_Q(-1/4)
=\frac{Q+2}{2^{Q+1}}>0.
}
\tag{B5.7}
$$

所以相变边缘不是任一有限体积配分函数的零点；它是零点在 $Q\to\infty$ 时的聚积端点。

## B5.5 最近零点的精确距离

最接近 $-1/4$ 的根为

$$
z_Q^{\mathrm{near}}
=-\frac1{4\cos^2(\pi/(Q+2))}.
\tag{B5.8}
$$

因此

$$
\boxed{
-\frac14-z_Q^{\mathrm{near}}
=\frac14\tan^2\frac{\pi}{Q+2}.
}
\tag{B5.9}
$$

并有渐近

$$
\boxed{
-\frac14-z_Q^{\mathrm{near}}
\sim
\frac{\pi^2}{4(Q+2)^2}.}
\tag{B5.10}
$$

这是一条精确的 $Q^{-2}$ zero-pinching law。

## B5.6 双曲侧的通道 gap

对 $-1/4<z<0$，两根均为正，定义 modulus gap

$$
\Gamma(z)
=
\log\frac{\lambda_+(z)}{\lambda_-(z)}.
\tag{B5.11}
$$

令 $y=\sqrt{1+4z}$，则

$$
\boxed{
\Gamma(z)
=2\operatorname{artanh}y.
}
\tag{B5.12}
$$

当 $z\downarrow-1/4$：

$$
\boxed{
\Gamma(z)
=2\sqrt{1+4z}
+O((1+4z)^{3/2}).}
\tag{B5.13}
$$

相应 correlation length

$$
\ell(z)=\Gamma(z)^{-1}
\tag{B5.14}
$$

满足

$$
\boxed{
\ell(z)
\sim
\frac1{2\sqrt{1+4z}}.}
\tag{B5.15}
$$

因此 $Q^{-2}$ zero pinching 与平方根 gap closing 是同一个分歧指数的两个有限尺寸表现。

## B5.7 极限自由能与零点密度

在主通道占优的区域，单位长度自由能为

$$
f(z)=\log\lambda_+(z).
\tag{B5.16}
$$

它在 $z=-1/4$ 具有平方根分支奇点。若以每一长度 $Q$ 归一化零点计数，则极限零点测度支撑于 $(-\infty,-1/4]$；写 $x=-z\ge1/4$，密度为

$$
\boxed{
\frac{d\nu}{dx}
=
\frac1{2\pi x\sqrt{4x-1}}.
}
\tag{B5.17}
$$

其总质量为 $1/2$，对应 $\deg H_Q/Q\to1/2$。边缘处的反平方根发散正是两通道相位量子化在 thermodynamic limit 中形成的 pinching density。

---

# 增订二·6　path averaging、reference fidelity 与 hard-core determinant 的精确恒等式

## B6.1 path averaging spectrum

令 $J_N$ 为 $\mathbb R^N$ 上的零边界最近邻平均：

$$
(J_Nc)_j
=\frac{c_{j-1}+c_{j+1}}2,
\tag{B6.1}
$$

其中边界外分量取零。其 sine modes 的本征值为

$$
\boxed{
\mu_k
=\cos\frac{k\pi}{N+1},
\qquad
1\le k\le N.}
\tag{B6.2}
$$

并且

$$
\mu_{N+1-k}=-\mu_k.
\tag{B6.3}
$$

所以平方以后，正负边缘 mode 成对退化。

## B6.2 determinant square identity

考虑正算子

$$
K_N=4J_N^2.
\tag{B6.4}
$$

其谱为

$$
4\cos^2\frac{k\pi}{N+1}.
\tag{B6.5}
$$

于是

$$
\det(I_N+zK_N)
=
\prod_{k=1}^N
\left(1+4z\cos^2\frac{k\pi}{N+1}\right).
\tag{B6.6}
$$

利用 $k\leftrightarrow N+1-k$ 配对，并注意奇数 $N$ 时中央 mode 的平方本征值为零，得到：

### 定理 B6.1　path--Zeckendorf determinant identity

$$
\boxed{
\det(I_N+4zJ_N^2)
=H_{N-1}(z)^2.}
\tag{B6.7}
$$

因此 Zeckendorf hard-core polynomial 是一个有限正 path determinant 的规范谱平方根。

## B6.3 fidelity edge

项目的有限 channel-to-fidelity bridge 给出，对归一化参考向量 $c$：

$$
F_e(c)=\|J_Nc\|_2^2.
\tag{B6.8}
$$

当 $N\ge2$ 时，其最大值为

$$
\boxed{
F_N^*
=\cos^2\frac{\pi}{N+1}.}
\tag{B6.9}
$$

该最大值的完整 eigenspace 是由 $k=1$ 与 $k=N$ 两个反射配对 mode 张成的二维空间。

## B6.4 最优 fidelity 与最近配分零点

令 $N\ge2$ 且 $Q=N-1$。由式 (B5.8) 与式 (B6.9)：

$$
\boxed{
z_{N-1}^{\mathrm{near}}
=-\frac1{4F_N^*}.}
\tag{B6.10}
$$

定义最优 reference-frame tax

$$
\tau_N=1-F_N^*.
\tag{B6.11}
$$

则最近零点到热力学边缘的距离精确为

$$
\boxed{
-\frac14-z_{N-1}^{\mathrm{near}}
=
\frac{\tau_N}{4(1-\tau_N)}.}
\tag{B6.12}
$$

因为

$$
\tau_N
=\sin^2\frac{\pi}{N+1},
\tag{B6.13}
$$

所以

$$
\tau_N
\sim\frac{\pi^2}{(N+1)^2},
\tag{B6.14}
$$

且

$$
-\frac14-z_{N-1}^{\mathrm{near}}
\sim\frac{\pi^2}{4(N+1)^2}.
\tag{B6.15}
$$

这给出精确字典：

$$
\boxed{
\text{有限 reference fidelity 的缺口}
\quad\longleftrightarrow\quad
\text{有限 hard-core 零点尚未压到临界边缘的距离}.}
\tag{B6.16}
$$

该字典来自同一个 path spectrum，不是把两个独立渐近式强行比较。

## B6.5 与离线 phase bubble 的尺度区别

若一个简单零点附近

$$
V\asymp r^2,
\tag{B6.17}
$$

并把有限参考系 tax $\tau_N$ 用作能量分辨阈值，则可见半径满足

$$
r_N\asymp\sqrt{\tau_N}\asymp N^{-1}.
\tag{B6.18}
$$

而 hard-core fugacity edge 的 zero pinching 是 $N^{-2}$。二者不是冲突：前者是二次能量到坐标距离的开方，后者是二次分支相位量子化后的参数距离。

---

# 增订二·7　正 determinant 完成与根定位

## B7.1 hard-core polynomial 的正谱因子化

由式 (B5.6)，

$$
\boxed{
H_Q(z)
=
\prod_{j=1}^{\lfloor(Q+1)/2\rfloor}
\left(
1+4z\cos^2\frac{j\pi}{Q+2}
\right).}
\tag{B7.1}
$$

定义正对角算子

$$
\mathsf K_Q
=
\operatorname{diag}
\left(
4\cos^2\frac{j\pi}{Q+2}
\right)_j.
\tag{B7.2}
$$

则

$$
\boxed{H_Q(z)=\det(I+z\mathsf K_Q).}
\tag{B7.3}
$$

且 $\mathsf K_Q$ 的所有 eigenvalues 严格为正。

因此任何零点必须是某个正 eigenvalue 的负倒数：

$$
H_Q(z)=0
\Longrightarrow
z\in(-\infty,0).
\tag{B7.4}
$$

## B7.2 与 LocalPositiveSquareCompletion 的共同机制

项目 `LocalPositiveSquareCompletion` 证明：有限实谱外的 inverse-square weights 形成正对角矩阵，而 $\det(I+wA)$ 的全部零点位于负实轴。

式 (B7.3) 表明 Zeckendorf hard-core roots 由完全同型的有限正 determinant 机制定位。

共同原理为：

$$
\boxed{
A>0
\quad\Longrightarrow\quad
\det(I+zA)=0
\Rightarrow z<0.}
\tag{B7.5}
$$

但这仍不是 RH，因为 completed Cayley 变量的目标域是单位圆，而这里的变量是 hard-core activity。要获得 RH，需要先构造一个 canonical completed self-adjoint／unitary operator，使其 characteristic variable 与 Cayley $w$ 真正对应。

## B7.3 self-adjoint 到 unitary 的候选路线

若 $H=H^*$，则其 Cayley transform

$$
U=(H-iI)(H+iI)^{-1}
\tag{B7.6}
$$

为 unitary。有限特征多项式

$$
\det(wI-U)
\tag{B7.7}
$$

的根全部位于单位圆。

因此存在另一条严格目标路线：从 prime--Zeckendorf--Gamma 数据构造 self-adjoint $H_T$，证明其 Cayley determinant 在有限窗内收敛到 transformed $\Xi$。困难全部集中在“canonical construction”和“convergence to $\Xi$”，不能由 unitary 这个名称代替。

---

# 增订二·8　黄金 hard-core 平稳链的隐藏能量常数

## B8.1 Perron 归一化 Markov 链

在 $z=1$，取 Perron 右向量 $(\varphi,1)$。对 transfer $A$ 作 Doob--Perron 归一化，得到 Markov 矩阵

$$
\boxed{
P=
\begin{pmatrix}
\varphi^{-1}&\varphi^{-2}\\
1&0
\end{pmatrix}.}
\tag{B8.1}
$$

其本征值为

$$
1,
\qquad
-\varphi^{-2}.
\tag{B8.2}
$$

第二本征值正是稳定／反交错 memory mode。

## B8.2 平稳占据密度

令状态 $1$ 表示当前位置被占据，则平稳占据概率为

$$
\boxed{
\rho
=\frac1{\varphi+2}.}
\tag{B8.3}
$$

其单点方差为

$$
\boxed{
\operatorname{Var}(\eta_0)
=\rho(1-\rho)
=\frac15.}
\tag{B8.4}
$$

## B8.3 精确交错协方差

二态链的非平凡谱只有 $-\varphi^{-2}$，所以

$$
\boxed{
\operatorname{Cov}(\eta_0,\eta_n)
=
\frac15(-\varphi^{-2})^n.}
\tag{B8.5}
$$

这说明 hard-core memory 不是单调衰减，而是带奇偶翻转的指数衰减。

## B8.4 积分 susceptibility

定义双边积分协方差

$$
\chi_{\rm hc}
=
\sum_{n\in\mathbb Z}
\operatorname{Cov}(\eta_0,\eta_n).
\tag{B8.6}
$$

由几何级数：

$$
\boxed{
\chi_{\rm hc}
=
\frac15
\frac{1-\varphi^{-2}}{1+\varphi^{-2}}
=
\frac1{5\sqrt5}.}
\tag{B8.7}
$$

更一般地，若 activity 为 $z>0$，单位长度 pressure 的 log-activity 二阶导数为

$$
\boxed{
\chi_{\rm hc}(z)
=
\frac{z}{(1+4z)^{3/2}}.}
\tag{B8.8}
$$

在 $z=1$ 恰得到 $1/(5\sqrt5)$。

## B8.5 五种黄金尺度不可混同

当前理论中至少出现：

$$
\begin{aligned}
&\text{stable/dominant ratio magnitude}:&&\varphi^{-2},\\
&\text{one-site variance}:&&1/5,\\
&\text{integrated hard-core susceptibility}:&&1/(5\sqrt5),\\
&\text{golden innovation mean square}:&&\varphi^{-3},\\
&\text{two-channel modulus gap}:&&2\log\varphi.
\end{aligned}
\tag{B8.9}
$$

这些常数来自不同 readouts，不能因为都与黄金系统有关就彼此替换。它们分别测量衰减率、局部涨落、累计响应、确定性创新能量和 Lyapunov separation。

---

# 增订二·9　prime reflected Gramian、最小奇异值与 fidelity

## B9.1 反射行向量

固定有限 prime cluster

$$
\mathcal C=\{p_1,\ldots,p_m\},
\qquad
\omega_j=\log p_j,
\tag{B9.1}
$$

以及正权 $w_j>0$。定义

$$
r_+(\delta)_j
=\sqrt{w_j}e^{\delta\omega_j},
\qquad
r_-(\delta)_j
=\sqrt{w_j}e^{-\delta\omega_j}.
\tag{B9.2}
$$

组成矩阵

$$
A(\delta)=
\begin{pmatrix}
r_+(\delta)\\
r_-(\delta)
\end{pmatrix}.
\tag{B9.3}
$$

令

$$
G(\delta)=A(\delta)A(\delta)^\mathsf T.
\tag{B9.4}
$$

## B9.2 exterior determinant

记

$$
W=\sum_jw_j.
\tag{B9.5}
$$

则

$$
G(\delta)=
\begin{pmatrix}
\sum_jw_je^{2\delta\omega_j}&W\\
W&\sum_jw_je^{-2\delta\omega_j}
\end{pmatrix}.
\tag{B9.6}
$$

直接展开得到

$$
\boxed{
\det G(\delta)
=4\sum_{i<j}
w_iw_j
\sinh^2(\delta(\omega_i-\omega_j)).}
\tag{B9.7}
$$

这正是 finite prime exterior energy。

## B9.3 最小奇异值作为观察能隙

在 $\delta=0$：

$$
G(0)=
\begin{pmatrix}W&W\\W&W\end{pmatrix},
\tag{B9.8}
$$

其 eigenvalues 为

$$
2W,
\qquad0.
\tag{B9.9}
$$

临界线上的两行完全重合，反对称观察方向不可见。

令

$$
\nu_j=\frac{w_j}{W},
\qquad
\operatorname{Var}_\nu(\omega)
=
\sum_j\nu_j(\omega_j-\bar\omega)^2.
\tag{B9.10}
$$

则

$$
\sum_{i<j}w_iw_j(\omega_i-\omega_j)^2
=W^2\operatorname{Var}_\nu(\omega).
\tag{B9.11}
$$

所以 $G$ 的最小 eigenvalue 满足

$$
\boxed{
\lambda_{\min}(G(\delta))
=2W\operatorname{Var}_\nu(\omega)\delta^2
+O(\delta^4).}
\tag{B9.12}
$$

即离轴后新出现的第二个可见方向，其 observation gap 以 $\delta^2$ 打开。

## B9.4 反射通道 fidelity

把 $r_\pm$ 归一化，定义 squared fidelity

$$
\boxed{
\mathcal F_{\mathcal C}(\delta)
=
\frac{W^2}
{\left(\sum_jw_je^{2\delta\omega_j}\right)
 \left(\sum_jw_je^{-2\delta\omega_j}\right)}.}
\tag{B9.13}
$$

临界线上

$$
\mathcal F_{\mathcal C}(0)=1.
\tag{B9.14}
$$

若 cluster 含不同频率，则 $\delta\ne0$ 时严格小于 $1$。

由式 (B9.6)--(B9.7)，有精确恒等式

$$
\boxed{
\frac1{\mathcal F_{\mathcal C}(\delta)}-1
=
\frac{4}{W^2}
\sum_{i<j}w_iw_j
\sinh^2(\delta(\omega_i-\omega_j)).}
\tag{B9.15}
$$

因此 exterior energy 与 fidelity loss 不是仅在二阶近似下相关，而由一个精确单调换算相连。

## B9.5 fidelity 的局部信息度量

取负对数：

$$
\boxed{
-\log\mathcal F_{\mathcal C}(\delta)
=4\operatorname{Var}_\nu(\omega)\delta^2
+O(\delta^4).}
\tag{B9.16}
$$

结合式 (B9.12)：

$$
\boxed{
-\log\mathcal F_{\mathcal C}(\delta)
=
\frac2W\lambda_{\min}(G(\delta))
+O(\delta^4).}
\tag{B9.17}
$$

所以临界线附近的三个量具有同一局部二次 metric：

$$
\boxed{
\begin{aligned}
&\text{prime exterior }\sinh^2\text{ energy},\\
&\text{reflected Gramian 的最小 eigenvalue},\\
&\text{反射通道的 negative log fidelity}.
\end{aligned}}
\tag{B9.18}
$$

共同系数正是 weighted variance of $\log p$。

## B9.6 short gaps 的 fidelity 解释

若 cluster 位于 $[P,P+D]$ 且 $D\ll P$，则

$$
\operatorname{Var}(\log p)
=O(D^2/P^2).
\tag{B9.19}
$$

从而固定 $\delta$ 下：

$$
1-\mathcal F_{\mathcal C}(\delta)
=O(\delta^2D^2/P^2).
\tag{B9.20}
$$

所以 short-gap cluster 是高 fidelity 的反射通道：代数上已经秩二，有限精度下却几乎仍像同一状态。这与 sticky grain 的解释完全一致。

---

# 增订二·10　二通道配分零点的精确平衡定理

## B10.1 一般二通道振幅

考虑

$$
\boxed{
Z_N(s)
=a_+(s)\lambda_+(s)^N
+a_-(s)\lambda_-(s)^N,}
\tag{B10.1}
$$

其中在所讨论点两系数与两通道均非零。

若 $Z_N(s)=0$，取模得到：

$$
|a_+||\lambda_+|^N
=|a_-||\lambda_-|^N.
\tag{B10.2}
$$

因此：

### 定理 B10.1　zero-balance identity

$$
\boxed{
N\log\frac{|\lambda_+|}{|\lambda_-|}
=
\log\frac{|a_-|}{|a_+|}.}
\tag{B10.3}
$$

零点要求 bulk Lyapunov imbalance 恰好由 boundary coefficient imbalance 抵消。

## B10.2 有界边界耦合迫使近等模

若在一个区域中存在

$$
0<m\le|a_\pm(s)|\le M<\infty,
\tag{B10.4}
$$

则任何零点满足

$$
\boxed{
\left|
\log\frac{|\lambda_+|}{|\lambda_-|}
\right|
\le
\frac1N\log\frac Mm.}
\tag{B10.5}
$$

所以长度趋于无穷时，零点只能逼近 equimodular locus。

若边界系数恰好等模，

$$
|a_+|=|a_-|,
\tag{B10.6}
$$

则任何零点必须严格满足

$$
|\lambda_+|=|\lambda_-|.
\tag{B10.7}
$$

## B10.3 dominated splitting 排除零点

若紧集 $K$ 上有统一 gap

$$
\left|
\log\frac{|\lambda_+|}{|\lambda_-|}
\right|
\ge\gamma>0,
\tag{B10.8}
$$

而 boundary coefficient ratio 仅次指数增长：

$$
\sup_{s\in K}
\frac1N
\left|
\log\frac{|a_-|}{|a_+|}
\right|
\longrightarrow0,
\tag{B10.9}
$$

则充分大 $N$ 时 $K$ 内无零点。

这给出严格的 transfer confinement 机制：

$$
\boxed{
\text{bulk dominated splitting}
+
\text{boundary transversality}
\Longrightarrow
\text{zero-free region}.}
\tag{B10.10}
$$

## B10.4 边界横截性不能省略

即使 $|\lambda_+|>|\lambda_-|$，若 $a_+$ 恰为零或指数级微小，dominant channel 也可能从 matrix coefficient 中消失。因此仅证明 cocycle 有 Lyapunov gap 不足以排除零点。

必须分开证明：

1. bulk channel gap；
2. boundary vectors 对 dominant line 的非消失耦合；
3. coefficient ratio 的次指数控制。

将“canonical boundary”写入结构字段而不证明这三点，会把承重信息从 theorem body 逃逸到命名中。

## B10.5 两种有限尺寸指数

hard-core edge 上，通道相位差在分歧参数附近按平方根变化；相位量子化 $\Delta\theta\asymp N^{-1}$ 因而给出参数距离 $N^{-2}$。

prime reflected channels 的 modulus gap 为

$$
\Gamma_{p,q}(\delta)
=2|\delta|\,|\log(q/p)|.
\tag{B10.11}
$$

若有限 completed coefficient imbalance 为 $O(1)$，式 (B10.5) 只允许

$$
|\delta|
=O\!\left(
\frac1{N|\log(q/p)|}
\right).
\tag{B10.12}
$$

相应横向能量为

$$
\sinh^2(\delta\log(q/p))=O(N^{-2}).
\tag{B10.13}
$$

所以 $N^{-2}$ 可以来自两种不同机制：分歧相位的平方根量子化，或线性 modulus gap 的二次能量。二者必须通过控制参数和坐标区分。

---

# 增订二·11　transfer 长度与 Fibonacci shell 深度必须分离

当前理论同时使用两个容易混淆的尺度。

## B11.1 transfer length

$$
N=\text{局部约束链或 cocycle 的因子数}.
\tag{B11.1}
$$

它控制：

- 两通道振幅的 $N$ 次幂；
- 相位量子化间距 $O(N^{-1})$；
- hard-core edge 的 $O(N^{-2})$ zero pinching；
- boundary coefficient 相对 bulk gap 的权重。

## B11.2 Fibonacci shell index

$$
k=\text{Zeckendorf 原子 }F_k\text{ 的指标},
\tag{B11.2}
$$

且

$$
F_k\asymp\varphi^k.
\tag{B11.3}
$$

它控制：

- prime rapidity 的放大 $F_k\delta\Delta\omega$；
- 分辨小 $|\delta\Delta\omega|$ 所需的黄金 memory depth；
- prime-power exponent 的稀疏 shell factorization。

因此：

$$
\boxed{N\ne k,
\qquad
N\ne F_k.}
\tag{B11.4}
$$

把 $N^{-2}$ finite-size law 与 $\varphi^{-2k}$ shell decay 未经映射地识别，会产生错误的尺度结论。只有在另行定义 renormalization relation $N=N(k)$ 后才能比较。

---

# 增订二·12　共同 Galerkin 空间中的 Zeckendorf--prime 微分

## B12.1 两个有限 Hilbert 空间

取有限 exponent 空间

$$
\mathcal H_Z
=\ell^2(\{0,\ldots,M_Q-1\},\mu),
\tag{B12.1}
$$

其中 $\mu(v)>0$ 且总质量归一化为 $1$。

取有限 prime graph $\mathcal C$ 的 vertex space

$$
\mathcal H_P=\ell^2(V_{\mathcal C},\nu),
\tag{B12.2}
$$

以及 edge space $\mathcal H_E$。

## B12.2 exponent multiplication 与 prime gradient

定义 exponent multiplication operator

$$
(\mathsf Nf)(v)=vf(v).
\tag{B12.3}
$$

对 edge $i<j$，定义 weighted gradient

$$
(d_{\mathcal C}h)_{ij}
=\sqrt{W_{ij}}(h_j-h_i).
\tag{B12.4}
$$

特别地，对 frequency vector

$$
\omega_i=\log p_i,
\tag{B12.5}
$$

有

$$
\|d_{\mathcal C}\omega\|^2
=
\sum_{i<j}W_{ij}(\log p_j-\log p_i)^2.
\tag{B12.6}
$$

## B12.3 张量横向微分

定义

$$
\boxed{
D_{Q,\mathcal C}
=\mathsf N\otimes d_{\mathcal C}:
\mathcal H_Z\otimes\mathcal H_P
\longrightarrow
\mathcal H_Z\otimes\mathcal H_E.}
\tag{B12.7}
$$

对常 exponent amplitude $\mathbf1_Z$ 与 frequency vector $\omega$：

$$
\boxed{
\|D_{Q,\mathcal C}(\mathbf1_Z\otimes\omega)\|^2
=
\mathbb E_\mu[v^2]
\sum_{i<j}W_{ij}(\Delta\log p_{ij})^2.}
\tag{B12.8}
$$

而增订一的横向 susceptibility 满足

$$
\boxed{
\left.\frac{d^2}{d\delta^2}
\mathscr E_{Q,\mathcal C}^{\perp}(\delta)
\right|_{\delta=0}
=2\|D_{Q,\mathcal C}(\mathbf1_Z\otimes\omega)\|^2.}
\tag{B12.9}
$$

这第一次把“Zeckendorf second moment 乘 prime variance”实现为同一有限 Hilbert space 中一个真正 operator norm，而不是两个标量事后相乘。

## B12.4 kernel 分解

在有限维中，

$$
\ker(\mathsf N\otimes d_{\mathcal C})
=
(\ker\mathsf N\otimes\mathcal H_P)
+
(\mathcal H_Z\otimes\ker d_{\mathcal C}).
\tag{B12.10}
$$

若 prime graph 连通，则

$$
\ker d_{\mathcal C}
=\operatorname{span}\{\mathbf1_P\}.
\tag{B12.11}
$$

而

$$
\ker\mathsf N
=\operatorname{span}\{\delta_0\}.
\tag{B12.12}
$$

所以 joint transverse energy 看不见且只看不见：

1. exponent 为零的真空状态；
2. 所有 prime frequencies 同时作共同平移的 coherent mode。

这正是预期的 gauge kernel，而不是任意人为指定的零空间。

## B12.5 Poincare coercivity

在上述 kernel 的正交补上，若

$$
\lambda_Z^+
=\min_{v>0}v^2=1
\tag{B12.13}
$$

且 $\lambda_P^+>0$ 是 prime graph Laplacian 的第一正 eigenvalue，则

$$
\boxed{
\|D_{Q,\mathcal C}F\|^2
\ge
\lambda_P^+\|F\|^2}
\tag{B12.14}
$$

对所有避开真空与共同 prime mode 的 $F$ 成立，适当理解张量权重。

short-gap sticky clusters 的问题，正是 $\lambda_P^+$ 在跨尺度极限中可能变小；黄金 shell 只能改变 exponent factor，不能自动阻止 prime graph spectral gap collapse。

---

# 增订二·13　从局部能量到 zero-side odd energy 的最小 intertwining 定理

## B13.1 两侧有限空间

设：

- $\mathcal H_{P,L}$ 为尺度 $L$ 的 prime relation Galerkin 空间；
- $\mathcal H_{Z,L}^{\mathrm{odd}}$ 为对应 zero-orbit odd 空间；
- $D_{P,L}$ 为 prime/Zeckendorf relation differential；
- $D_{Z,L}$ 为 zero-side odd differential；
- $U_L:\mathcal H_{P,L}\to\mathcal H_{Z,L}^{\mathrm{odd}}$ 为候选 explicit-formula analysis map。

## B13.2 intertwining-with-error

假设存在有界算子 $B_L$ 与误差 $R_L$，使

$$
\boxed{
D_{Z,L}U_L
=B_LD_{P,L}+R_L.}
\tag{B13.1}
$$

则对任意 $f$：

$$
\begin{aligned}
\|D_{Z,L}U_Lf\|^2
&\le
\left(\|B_LD_{P,L}f\|+\|R_Lf\|\right)^2\\
&\le
2\|B_L\|^2\|D_{P,L}f\|^2
+2\|R_Lf\|^2.
\end{aligned}
\tag{B13.2}
$$

因此：

### 定理 B13.1　有限能量输运准则

$$
\boxed{
E_{Z,L}^{\mathrm{odd}}(U_Lf)
\le
2\|B_L\|^2E_{P,L}^{\mathrm{rel}}(f)
+2\|R_Lf\|^2.}
\tag{B13.3}
$$

这就是此前开放 domination 式的最小 operator-theoretic 来源。

## B13.3 排除离线 mode 还需要什么

式 (B13.3) 本身仍不足以排除离线 mode。还必须有：

1. **覆盖性**：每个候选 zero odd mode 位于 $U_L$ 的像或受其 frame 控制；
2. **prime reflection flatness**：目标 preimage 上 $E_{P,L}^{\mathrm{rel}}\to0$；
3. **误差相对 gap 消失**：$\|R_L\|^2=o(\gamma_{Z,L})$；
4. **zero odd coercivity**：真实离线 mode 满足 $E_{Z,L}^{\mathrm{odd}}\ge\gamma_{Z,L}\|h\|^2$；
5. **极限紧性**：有限 Galerkin 结论不在 $L\to\infty$ 时失去质量。

缺少任一项，都可能出现能量估计成立但离线 mode 逃到 kernel、像空间之外或极限无穷远的情形。

## B13.4 square-late principle

局部正能量不能在完成以前盲目相加，因为

$$
\left|\sum_j a_j\right|^2
\ne
\sum_j|a_j|^2
\tag{B13.4}
$$

且差异正是 cross-phase terms。

因此正确顺序是：

$$
\boxed{
\text{先把 amplitude / carry / holonomy 输运到同一空间，
再取 exterior norm 或 odd square。}}
\tag{B13.5}
$$

若过早把每个 local channel 平方，顺序、相位和 destructive interference 会永久丢失。正能量是最终证书，不一定是可直接逐局部组合的原始状态。

---

# 增订二·14　CIRPT 原语分层与联合 kernel

增订一指出，Zeckendorf 的信息价值在关系层。当前项目的 `PrimitiveBundle` 已经把有限原语族的联合观察 kernel 定义为各 atom kernel 的交。因此本理论可以用四类原语重新表达。

## B14.1 ADMIT

Zeckendorf hard-core 条件

$$
\eta_k\eta_{k+1}=0
\tag{B14.1}
$$

决定哪些数位历史合法。它删除局部 carry 冗余。

## B14.2 ANCHOR

整数 exponent

$$
E_Q(\eta)=\sum_k\eta_kF_k
\tag{B14.2}
$$

把合法历史锚定到唯一整数值。它在 state level 是单射，但不保存关系图。

## B14.3 FLOW

successor/carry、prime word 顺序和 transfer cocycle 决定状态如何演化。ordered rapidity $U_n$ 属于 FLOW，而不是最终 character parity。

## B14.4 CUT

反射通道

$$
\delta\longleftrightarrow-\delta
\tag{B14.3}
$$

以及 split/inert Frobenius

$$
y\longmapsto\pm y
\tag{B14.4}
$$

决定二通道如何被固定或交换。

## B14.5 二次 observer

Gram determinant、smallest singular value、negative log fidelity 与 odd energy 读取 CUT/FLOW 差异的平方大小。

四类角色原语自身先形成

$$
\boxed{
K_{\rm primitive}
=K_{\rm ADMIT}
\cap K_{\rm ANCHOR}
\cap K_{\rm FLOW}
\cap K_{\rm CUT}.}
\tag{B14.5}
$$

若二次 observer 已由这些原语构造，并且它的 collision relation 被登记为一个 packed observer atom，则记其 kernel 为 $K_{\rm quad}$。它必须按其数学来源归入既有的 `CUT`、`FLOW`、`ADMIT` 或 `ANCHOR` 角色之一；`ENERGY` 不是第五种 CIRPT role。加入该 observer 后的联合观察 kernel 为

$$
\boxed{
K_{\rm observed}
=K_{\rm primitive}\cap K_{\rm quad}.}
\tag{B14.6}
$$

只有在证明严格包含

$$
K_{\rm observed}\subsetneq K_{\rm primitive}
\tag{B14.7}
$$

或给出相应 leave-one-out witness 以后，才能声称二次 observer 具有严格正的信息增益。删除一个层通常只保证 kernel 不缩小；是否严格扩大必须单独证明，不能由层名推出。

## B14.6 能量足以定位，但不足以重构顺序

RH 只询问

$$
|\delta|=0\text{ 还是 }|\delta|>0,
\tag{B14.8}
$$

故一个忠实的平方 radial energy 在 zero side 足以作定位证书。

但 prime amplitudes 在到达 zero side 以前会发生有序乘法和相位抵消；仅保留平方能量一般不能重构其 FLOW。因此：

$$
\boxed{
\text{定位目标可以只需 magnitude，
证明该 magnitude 的来源却可能必须保留 orientation 与 order。}}
\tag{B14.9}
$$

这解释了为什么 holonomy 和 Casimir 都需要：前者保持组合信息，后者给出最终正证书。

---

# 增订二·15　算术黄金判别式禁闭猜想

## B15.1 completed two-channel cocycle

设存在由 prime、prime powers、Zeckendorf carry 与 Gamma block 规范构造的矩阵 cocycle

$$
\mathcal M_L(s)
=G_\Gamma(s;L)
\prod_{p\le P(L)}^{\longrightarrow}
G_p(s),
\tag{B15.1}
$$

乘积保留规定的有序或可证明的顺序无关结构。

要求每个非分歧 local block 位于黄金 split torus 的 normalizer，并且其 Weyl projection 满足

$$
\boxed{
\operatorname{Weyl}(G_p)
=\chi_5(p).}
\tag{B15.2}
$$

这把 `GoldenCharacterQuotient` 从独立二值标签提升为 local channel Frobenius 的投影；但式 (B15.1) 的具体 block 仍待构造。

## B15.2 singular-value Lyapunov gap

定义

$$
\Gamma_L(s)
=
\frac1{N_L}
\log\frac{\sigma_1(\mathcal M_L(s))}
{\sigma_2(\mathcal M_L(s))}
\ge0.
\tag{B15.3}
$$

反射对称应给出

$$
\Gamma_L(1-\bar s)=\Gamma_L(s).
\tag{B15.4}
$$

而目标禁闭性质是：对任意避开临界线的紧集 $K$，

$$
\boxed{
\liminf_{L\to\infty}
\inf_{s\in K}
\Gamma_L(s)>0.}
\tag{B15.5}
$$

这就是 completed dominated splitting。

## B15.3 boundary transversality

若 transformed determinant 或 matrix coefficient 写成

$$
Z_L(s)=
\langle \ell_L(s),
\mathcal M_L(s)r_L(s)\rangle,
\tag{B15.6}
$$

还必须证明 $\ell_L,r_L$ 对 dominant singular directions 的耦合不以指数速度消失。

可写成：存在次指数 $c_L>0$，使

$$
|\langle \ell_L,u_{1,L}\rangle|
\,|\langle v_{1,L},r_L\rangle|
\ge c_L,
\qquad
\frac1{N_L}\log c_L\to0.
\tag{B15.7}
$$

## B15.4 completed determinant fidelity

最后需要局部一致收敛

$$
\boxed{
Z_L(s)\longrightarrow C(s)\Xi(s),}
\tag{B15.8}
$$

其中 $C(s)$ 在临界条带内无零。

只有式 (B15.5)、(B15.7)、(B15.8) 同时成立，二通道 zero-balance theorem 才能排除临界线外零点。

### 猜想 B15.1　Arithmetic golden-discriminant confinement

存在满足上述条件的 canonical completed cocycle，并且其等模集合在极限中被限制为

$$
\boxed{
\Gamma(s)=0
\Longrightarrow
\Re s=\frac12.}
\tag{B15.9}
$$

若再有式 (B15.8)，则 RH 成立。

该猜想比“存在一个 Hilbert--Polya 算子”更具分解性，因为它明确列出：

- local quadratic cover；
- mod-$5$ Weyl/Frobenius projection；
- ordered normalizer product；
- Gamma completion；
- bulk dominated splitting；
- boundary transversality；
- determinant convergence。

任何一个环节都不能由其名称自动提供。

---

# 增订二·16　与离线零点相变的最终接合

设假想离线零点为

$$
\rho_*
=\frac12+\delta_*+it_*.
\tag{B16.1}
$$

前两部分已经给出：

- 同高度出现 $\pm\delta_*$ 反射零相；
- Cayley 坐标中出现 $e^{\pm\eta_*}$ reciprocal pair；
- scalar visible energy 在 $(t_*,\delta_*)$ 闭合；
- prime pair relation energy对每个不同频率对严格为正；
- zero orbit 的符号风险集中在 nonnegative odd energy。

本增订增加以下解释。

## B16.1 离线零点是 bulk--boundary 精确平衡事件

任何精确的 two-channel representation 中，一个零点首先满足 zero-balance identity：bulk modulus gap 与 boundary coefficient imbalance 必须精确抵消。对有限 $N$，即使两条边界系数都非零且保持横截，一个有限的 coefficient imbalance 也可以把零点从严格等模集合移动 $O(N^{-1})$；因此不能把每个有限离轴零点直接归结为“bulk gap closing”或“boundary coefficient 等于零”。

真正可用于 completed 极限的结论是：若 $N_L\to\infty$ 时仍有零点停留在一个与等模集合正距离分离的紧集内，那么至少有下列一项失效：

1. bulk singular-value gap 没有保持统一正下界；
2. boundary coefficient ratio 不是次指数的，或 dominant coupling 以指数速度消失；
3. two-channel 近似、determinant 表示或 completion error 在该极限中不可忽略。

所以：

$$
\boxed{
\begin{aligned}
\text{persistent off-axis zero}
\Longrightarrow{}&
\text{bulk dominated-splitting failure}\\
&\lor\ \text{boundary subexponentiality/transversality failure}\\
&\lor\ \text{two-channel completion-error failure}.
\end{aligned}}
\tag{B16.2}
$$

前一理论只讨论了 scalar-to-relation coercivity closing；本式说明 completed transfer 证明必须分别审计 bulk、boundary 与 representation error，不能把三者压成一个未分解的“相变”字段。

## B16.2 离线 radial pair 是 Lorentz boost mode

Cayley pair

$$
w_*=e^{i\theta_*}e^{\eta_*},
\qquad
w_*^\sharp=e^{i\theta_*}e^{-\eta_*}
\tag{B16.3}
$$

去掉共同相位后，正是 rapidity $\eta_*$ 的 split-torus pair。其第一反射不变量为

$$
\sinh^2\eta_*.
\tag{B16.4}
$$

prime pair 的对应 invariant 为

$$
\sinh^2(\delta_*\Delta\log p).
\tag{B16.5}
$$

两者属于同一种 Lorentz energy，但仍缺 canonical map 把所有 local rapidities 胶合成 $\eta_*$。

## B16.3 相变不等于通道生成

在固定 $\Xi$ 中，离线零点不是两条通道在物理时间 $t_*$ 被创造；它是 observer slice 首次穿过一个已存在的 radial defect。

在变形族 $\Xi_\lambda$ 中，若 two-channel discriminant 真正穿过零并使等模 locus 改变，才是 root-bifurcation。hard-core $D(z)=0$ 为这种分歧相变提供了最小正规形。

## B16.4 RH 的加强型能量表述

RH 不仅可读为“所有 zero radial energies 为零”，还可提出更强的 completed statement：

$$
\boxed{
\begin{aligned}
&\text{临界线外，completed cocycle 保持正 singular-value gap；}\\
&\text{boundary vectors 对 dominant channel 保持横截；}\\
&\text{prime relation differential 的 joint kernel 只含 gauge modes；}\\
&\text{zero-side odd energy 由该 relation differential 的像控制。}
\end{aligned}}
\tag{B16.6}
$$

若四项成立，则离线 scalar zero 无法通过隐藏 relation mode 或边界失耦产生。

---

# 增订二·17　信息逃逸与不可替代结论表

| 命题 | 地位 |
|---|---|
| $T(z)$ 的谱覆盖为 $y^2=1+4z$ | 直接有限代数 |
| $z=-1/4$ 是解析分歧／metric 退化点 | 直接有限代数 |
| $z=1$ 的判别式为 $5$，通道为 $\varphi,-\varphi^{-1}$ | 直接有限代数 |
| 奇素数 $p\ne5$ 的 split/inert 由 $(p/5)$ 控制 | 直接有限域代数 |
| 惰性 Frobenius 与解析 monodromy 执行同一 deck swap | 直接推论 |
| 项目 golden character 等于 local channel Weyl sign | 与仓库定义相容的精确识别 |
| character parity 恢复完整 ordered holonomy | 不成立 |
| $T(z)^TJ_zT(z)=-zJ_z$ | 直接矩阵恒等式 |
| hard-core edge 是 Lorentz signature transition | 直接分类推论 |
| $\det(I+4zJ_N^2)=H_{N-1}(z)^2$ | 本增订有限定理 |
| 最近 hard-core zero 为 $-1/(4F_N^*)$ | 本增订直接推论 |
| reference fidelity tax 精确决定 edge zero displacement | 本增订直接推论 |
| 正 determinant 机制定位 hard-core roots 到负实轴 | 有限谱推论 |
| 该负实轴定位等于 RH 单位圆定位 | 不成立 |
| hard-core 协方差为 $\frac15(-\varphi^{-2})^n$ | 本增订有限 Markov 推论 |
| hard-core susceptibility 为 $1/(5\sqrt5)$ | 本增订直接推论 |
| exterior energy 与 reflected fidelity 有精确换算 | 本增订有限定理 |
| exterior energy、最小 singular gap、$-\log$ fidelity 同阶 | 本增订局部定理 |
| dominated splitting 单独排除 matrix-coefficient zeros | 不成立；还需 boundary transversality |
| Zeckendorf--prime tangent energy 是张量 differential norm | 本增订有限 operator identity |
| prime relation differential 已与 zero odd differential intertwine | 尚未建立 |
| canonical completed golden-discriminant cocycle 已存在 | 尚未建立 |
| 本增订证明 RH | 不成立 |

---

# 增订二·18　最终收束

本增订将前两部分的“黄金隐藏通道”进一步压缩成一个单一母结构：

$$
\boxed{
\Sigma:
\quad y^2=1+4z.}
\tag{B18.1}
$$

在该谱覆盖中：

$$
\boxed{
\begin{aligned}
\text{branch point }D=0
&\Longleftrightarrow
\text{两通道碰撞与 hard-core edge},\\
D(1)=5
&\Longleftrightarrow
(\varphi,-\varphi^{-1})\text{ 黄金通道},\\
\chi_5(p)=+1
&\Longleftrightarrow
\text{Frobenius 固定两通道},\\
\chi_5(p)=-1
&\Longleftrightarrow
\text{Frobenius 交换两通道},\\
q_z\text{ 的签名}
&\Longleftrightarrow
\text{双曲、退化、椭圆相型},\\
|\lambda_+|=|\lambda_-|
&\Longleftrightarrow
\text{finite zeros 的必要 bulk 条件},\\
\sinh^2 u
&\Longleftrightarrow
\text{反射隐藏 rapidity 的首个正 invariant}.
\end{aligned}}
\tag{B18.2}
$$

最深的新结论不是“数字 $5$ 神秘地出现在 RH 周围”，而是：

$$
\boxed{
\textbf{数字 }5\textbf{ 是最小一步 hard-core transfer 在 }z=1\textbf{ 纤维的谱判别式；}
}
\tag{B18.3}
$$

因此项目中的 Zeckendorf memory、黄金数域、模 $5$ prime character 和 dihedral channel swap 确实拥有一个共同的有限代数来源。

与此同时，path operator 给出第二条精确闭环：

$$
\boxed{
\text{reference-frame fidelity spectrum}
\longleftrightarrow
\text{positive path determinant}
\longleftrightarrow
\text{hard-core zero pinching}.}
\tag{B18.4}
$$

prime cluster 则给出第三条精确闭环：

$$
\boxed{
\text{log-prime exterior energy}
\longleftrightarrow
\text{second singular direction}
\longleftrightarrow
\text{reflected-channel fidelity loss}.}
\tag{B18.5}
$$

三条闭环仍未自动汇合到 $\Xi$。真正缺少的不是更多相似公式，而是一个保持全部结构的 completed functor：

$$
\boxed{
\begin{array}{ccc}
\text{prime--Zeckendorf normalizer cocycle}
&\xrightarrow{\quad U_L\quad}&
\text{zero-orbit odd space}\\
D_{P,L}\downarrow&&\downarrow D_{Z,L}\\
\text{prime relation energy}
&\xrightarrow{\quad B_L\quad}&
\text{zero odd energy},
\end{array}}
\tag{B18.6}
$$

满足

$$
D_{Z,L}U_L=B_LD_{P,L}+R_L,
\qquad
\|R_L\|\to0,
\tag{B18.7}
$$

并同时保持 bulk dominated splitting、boundary transversality、Gamma completion 与 determinant convergence。

因此本轮把 RH 承重问题收紧为：

$$
\boxed{
\textbf{能否构造一个 completed arithmetic two-channel functor，
使黄金判别式的 local Frobenius/holonomy 数据在极限中形成临界线外的 dominated splitting，
并使其正 relation energy 忠实覆盖全部 off-line odd modes？}}
\tag{B18.8}
$$

若答案为是，则 Lee--Yang 圆定位、Weil odd-energy 正性、transfer equimodular confinement 与 Hilbert--Polya unitary localization 将成为同一结构的四种坐标表达。若答案为否，则已经建立的黄金、Zeckendorf、path fidelity 与 prime-gap 恒等式仍是彼此严格关联的有限理论，但不能被提升为 RH 的动力学解释。

---

# 增订三　复幂 Solenoid 荷—相位分解、深度—宽度忠实性与 Rouché 有理证书

> 本增订继续追加于同一纯理论主卷。公式编号使用 `C` 前缀，与主卷、增订一和增订二相互独立。本文不新增 Lean 声明，不把条件证书写成 RH 证明。

## 摘要

增订二已经把假想离线零点收紧为一个 visible–hidden Schur margin 的饱和事件，并区分了 holomorphic transfer 与 Hermitian energy。本增订进一步接入项目最新闭合的三个真源：

1. `D5/S1/Solenoid/ComplexPowerSolenoidDecomposition`：任意非零 compatible complex power thread 构造性地分解为一个实对数荷与一个 universal-solenoid phase thread；
2. `D5/S3/Weil/ZetaAnalytic/RoucheZeroCount`：矩形边界上的严格扰动不等式保持解析零点计数；
3. `D5/S3/Zeros/RationalNegativeCountCertificate`：一旦负径向计数区域非空且开放，必存在有理参数证书。

同时使用：

- `D5/S3/ConceptDynamics/InformationEscape/EscapePairs`；
- `D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty`；
- `D5/S3/Observer/Hankel/HankelRankMinimality`；
- 本卷已有 prime-pair 复核、Zeckendorf 二态 transfer 与 Schur 临界理论。

本增订得到六个新的理论核心。

第一，对每个素数 $p$ 和中心化谱参数

$$
u=\delta+it,
$$

存在 canonical complex power thread

$$
Z_{p,u}(m)
=
\exp\!\left(
-\frac{u\log p}{m}
\right).
$$

其守恒对数荷与相位分别为

$$
Q_p(u)=-\delta\log p,
\qquad
\theta_{p,t}(m)
=
-\frac{t\log p}{2\pi m}
\pmod 1.
$$

所以临界线并不是“相位消失”的地方，而是全部 centered prime threads 的非紧对数荷同时归零的切片；$t$ 仍完整存在于 solenoid phase 中。

第二，本卷的 prime-pair 横向项具有精确荷梯度解释：

$$
\boxed{
\sinh^2\!\left(
\delta\log\frac qp
\right)
=
\sinh^2\!\left(
Q_p(u)-Q_q(u)
\right).
}
$$

时间项则是同一对 threads 的 compact phase difference。由此，原有的

$$
\sinh^2+\sin^2
$$

不是两个相似的能量，而是

$$
\mathbb R_{\rm charge}\times\mathcal S_{\rm phase}
$$

上非紧方向与紧方向的两个关系读出。

第三，phase faithfulness 存在一条此前未显化的深度—宽度对偶：

- 一个固定素数的全部 power levels 可以无歧义恢复 $t$；
- 任意有限 levels 只在有限高度窗内忠实，并在全轴上保留周期 alias；
- 两个带标签的不同素数在 level one 已足以全局恢复 $t$，因为 $\log p/\log q$ 不可能为有理数。

所以 observer 可以用“沿一个素数向深层取根”换取 phase faithfulness，也可以用“在同一层横向保留两个乘法独立的素数标签”换取 phase faithfulness。标量 Euler 完成之所以危险，不是局部信息不足，而是它把这些标签与关系重新压入交换标量。

第四，对 universal solenoid 的有限 level observer family，可以给出精确的 structural novelty 判据。设 $S$ 是已观察 levels，$m$ 是候选新 level，令

$$
N=\operatorname{lcm}(S\cup\{m\}),
\qquad
d_S=\gcd_{s\in S}\frac Ns.
$$

则 level-$m$ phase readout 可由 $S$ 中 readouts 恢复，当且仅当

$$
d_S\mid\frac Nm.
$$

否则存在一个显式 solenoid phase thread，在全部 $S$-levels 上与零 thread 相同，却在 level $m$ 上不同。由项目的 exact escape/structural novelty 语言，这正是一个 leave-one-out unique-capture witness。

第五，假如存在离线零点，则 Cayley 圆外对应零点的内侧径向邻域必出现严格负的 scale-weighted radial log derivative。该区域自动开放，因此项目的 rational negative-count theorem 的两个抽象前提，在这一具体 profile 上可由离线零点局部解析正常形条件性地提供。于是 RH 失败不仅有一个不可见的复零点，还必有：

$$
\boxed{
q,r\in\mathbb Q,\quad
r>0,\quad
\mathscr Q(q,r)>0,\quad
r\partial_r\log\mathscr Q(q,r)<0
}
$$

这样的有理径向先兆证书。

第六，Rouché 稳定性把 RH 转化为一族有限有理矩形证书。若 canonical analytic approximant

$$
D_N(s)=U_N(s)\det T_N(s)
$$

在某个离轴有理矩形上无零，并满足严格边界误差小于 determinant floor，则 $\Xi$ 在该矩形中也无零。若 Hermitianization

$$
E_N=T_N^*T_N
$$

具有正 hidden block 和正 Schur margin，则可以显式推出 singular-value floor、determinant floor 与 Rouché 预算。该预算含有维数因子

$$
\mu_N^{d_N/2}.
$$

所以 Zeckendorf/Hankel 的真正证明论价值进一步显现：不是把 $F_{Q+2}$ 个历史全部展开，而是把它们压缩到最小二态 transfer，从而避免 determinant certificate 的维数指数税。

最终，RH 的候选有限证书架构不再是“完整重构全部 solenoid phase”，而是：

$$
\boxed{
\text{有限高度窗的 phase faithfulness}
+
\text{grounded charge coercivity}
+
\text{Schur determinant floor}
+
\text{Rouché strict boundary stability}.
}
$$

这条架构仍缺 canonical prime–Zeckendorf–Gamma transfer、其与 $\Xi$ 的 locally uniform determinant approximation，以及所有离轴有理矩形上的 uniform certificate。本文只把缺口压缩到这些明确位置。

---

# 增订三·0　理论地位与信息逃逸边界

## C0.1 已闭合真源

本增订使用下列仓库定理作为已闭合输入。

### （一）complex power thread 的荷—相位分解

项目已经机器证明：

$$
m\log\|z_m\|=Q(z),
\tag{C0.1}
$$

并构造等价：

$$
\boxed{
\operatorname{ComplexPowerThread}
\simeq
\mathbb R\times\mathcal S,
}
\tag{C0.2}
$$

其中 $\mathcal S$ 是项目已有的 universal solenoid。项目还证明：

$$
Q(z)=0
\Longleftrightarrow
\|z_m\|=1\quad\forall m.
\tag{C0.3}
$$

该真源明确删除了原来源中未由 power-thread 数据支持的 RH、Gamma、maximal compact、zero-thread 与 trivial-zero 子句。因此本增订也不恢复这些已被审计删除的陈述。

### （二）矩形 Rouché 零点计数

项目已经机器证明：若 $f,g$ 在闭矩形邻域解析，并且边界上

$$
|f-g|<|g|,
\tag{C0.4}
$$

则二者在矩形中的零点数按解析重数相同。严格不等式不可弱化为非严格不等式。

### （三）有理负径向证书

项目已经机器证明：若某个二参数 profile 的 negative-count region 开放，并且 $\neg\mathrm{RH}$ 使该区域非空，则存在正有理半径和有理角参数落在该区域中。

该定理本身不证明区域开放，也不证明 RH 失败产生真实点。本增订只对 Cayley 拉回的局部零点 profile 条件性地补出这两个解析前件。

### （四）exact information escape 与 structural novelty

项目已经机器化：

- finite escape pairs；
- leave-one-out unique capture pairs；
- exact escape rate；
- 结构 kernel 严格缩小；
- semantic closure；
- “降低逃逸率”等价于 canonical quotient CUT 的严格 kernel novelty。

所以本增订不把“加入一个 readout 看起来更丰富”当作信息增益。只有给出 kernel 严格缩小或 unique-capture witness，才能声称该 readout 是结构新信息。

### （五）Hankel visible rank

项目已经机器证明，有限维线性系统在足够大 horizon 上的 Hankel rank 等于 reachable dimension 减去 reachable-unobservable dimension。结合项目已有最小实现结果，Hankel rank 是可见行为所需的最小记忆维数，而不是任意 chosen state-space dimension。

## C0.2 本增订新推导的地位

以下是本增订中的纯数学推导，但尚未作为新的 Lean 真源登记：

- centered prime power thread 的显式构造；
- prime transverse energy 的 charge-gradient 恒等式；
- finite level phase aliasing 周期；
- finite solenoid level structural novelty 的 $\gcd/\operatorname{lcm}$ 判据；
- one-prime depth / two-prime width faithfulness；
- charge graph 加 anchor 后的有限 coercivity；
- off-circle zero 产生 open negative radial precursor；
- rational rectangle RH 等价族；
- Schur margin 到 determinant floor 的显式下界；
- determinant dimension tax；
- countable Rouché certificate reformulation。

以下仍是开放承重桥：

- canonical prime–Zeckendorf–Gamma analytic transfer；
- 其 determinant 与 completed $\Xi$ 只差无零 analytic unit；
- locally uniform、带显式误差界的 approximation；
- Gamma/pole block 对 ambient common charge mode 的 canonical anchor；
- finite phase/charge observables 到 zero-side odd orbit energy 的 faithful intertwining；
- 所有离轴有理矩形上的统一证书。

---

# 增订三·1　centered prime complex power thread

## C1.1 定义

固定素数 $p$，令

$$
u=\delta+it\in\mathbb C.
\tag{C1.1}
$$

对每个正整数 $m$，定义：

$$
\boxed{
Z_{p,u}(m)
=
\exp\!\left(
-\frac{u\log p}{m}
\right).
}
\tag{C1.2}
$$

所有坐标均非零。

### 定理 C1.1　power-thread compatibility

对任意正整数 $m,n$：

$$
\boxed{
Z_{p,u}(mn)^n
=
Z_{p,u}(m).
}
\tag{C1.3}
$$

#### 证明

直接计算：

$$
Z_{p,u}(mn)^n
=
\exp\!\left(
-\frac{nu\log p}{mn}
\right)
=
\exp\!\left(
-\frac{u\log p}{m}
\right).
$$

所以 $Z_{p,u}$ 是项目 `ComplexPowerThread` 的一个 canonical 元素。

## C1.2 守恒对数荷

由定义：

$$
\|Z_{p,u}(m)\|
=
\exp\!\left(
-\frac{\delta\log p}{m}
\right).
\tag{C1.4}
$$

因此：

$$
m\log\|Z_{p,u}(m)\|
=
-\delta\log p.
\tag{C1.5}
$$

### 定义 C1.2　prime logarithmic charge

$$
\boxed{
Q_p(u)
:=
Q(Z_{p,u})
=
-\delta\log p.
}
\tag{C1.6}
$$

这个量与 power level $m$ 无关，正是项目 charge-conservation theorem 在 canonical prime thread 上的实例。

## C1.3 solenoid phase

归一化坐标为：

$$
\frac{Z_{p,u}(m)}{\|Z_{p,u}(m)\|}
=
\exp\!\left(
-\frac{it\log p}{m}
\right).
\tag{C1.7}
$$

在 additive circle 坐标中定义：

$$
\boxed{
\theta_{p,t}(m)
=
-\frac{t\log p}{2\pi m}
\pmod 1.
}
\tag{C1.8}
$$

它满足：

$$
n\theta_{p,t}(mn)
=
\theta_{p,t}(m),
\tag{C1.9}
$$

所以确实给出一个 universal-solenoid phase thread。

于是 canonical prime thread 的荷—相位分解是：

$$
\boxed{
Z_{p,u}
\longleftrightarrow
\left(
-\delta\log p,\,
\theta_{p,t}
\right).
}
\tag{C1.10}
$$

## C1.4 局部信息完整性

对固定素数 $p$：

- 任一单个 level 的 norm 已经恢复 $\delta$：

$$
\boxed{
\delta
=
-\frac{m\log\|Z_{p,u}(m)\|}{\log p};
}
\tag{C1.11}
$$

- 全部 phase levels 恢复 $t$，见增订三·5；
- 所以完整的一个 prime thread 已经忠实编码中心化谱参数 $u$。

因此 zeta 困难不来自单个 prime thread 缺少 $\delta$ 或 $t$；困难来自 scalar multiplication、symmetrization、completion 与 analytic continuation 如何压缩这些局部关系数据。

---

# 增订三·2　反射、临界线与零荷切片

## C2.1 同高度反射

中心化变量的同高度反射为：

$$
u^\sharp=-\overline u=-\delta+it.
\tag{C2.1}
$$

对应 thread 满足：

$$
\boxed{
Z_{p,u^\sharp}(m)
=
\frac1{\overline{Z_{p,u}(m)}}.
}
\tag{C2.2}
$$

所以：

$$
Q_p(u^\sharp)=-Q_p(u),
\tag{C2.3}
$$

而：

$$
\theta_{p,t}^{\sharp}(m)
=
\theta_{p,t}(m).
\tag{C2.4}
$$

反射只翻转非紧 charge，不改变同高度 compact phase。

## C2.2 临界线的精确 thread 表述

由项目的 zero-charge/unit-norm theorem：

$$
Q_p(u)=0
\Longleftrightarrow
\|Z_{p,u}(m)\|=1\quad\forall m.
\tag{C2.5}
$$

而 $Q_p(u)=-\delta\log p$，故对任意素数 $p$：

$$
\boxed{
\Re s=\frac12
\Longleftrightarrow
\delta=0
\Longleftrightarrow
Q_p(u)=0
\Longleftrightarrow
\|Z_{p,u}(m)\|=1\quad\forall m.
}
\tag{C2.6}
$$

所以 RH 的 thread 几何不是：

$$
\text{all phases are trivial}.
$$

在线零点一般仍具有非平凡 $t$，所以其 solenoid phase 非平凡。正确命题是：

$$
\boxed{
\text{所有零点所对应的 centered prime threads 都落在 zero-charge phase locus。}
}
\tag{C2.7}
$$

## C2.3 Cayley radial coordinate 与 prime charge

本卷前文定义：

$$
\eta_a(t,\delta)
=
\log\left|
\frac{a+\delta+it}{a-\delta-it}
\right|.
\tag{C2.8}
$$

它满足：

$$
\eta_a(t,\delta)=0
\Longleftrightarrow
\delta=0
\Longleftrightarrow
Q_p(u)=0.
\tag{C2.9}
$$

临界线附近：

$$
\eta_a(t,\delta)
=
\frac{2a}{a^2+t^2}\delta
+
O(\delta^3).
\tag{C2.10}
$$

代入 $\delta=-Q_p/\log p$：

$$
\boxed{
\eta_a(t,\delta)
=
-\frac{2a}{(a^2+t^2)\log p}
Q_p(u)
+
O(Q_p(u)^3).
}
\tag{C2.11}
$$

所以 Lee–Yang 径向序参量与 complex-power logarithmic charge 在每个有限高度窗内局部线性等价。

---

# 增订三·3　prime-pair 复核是 charge–phase 关系度量

## C3.1 charge gradient

对不同素数 $p,q$：

$$
Q_p(u)-Q_q(u)
=
-\delta\log p+\delta\log q
=
\delta\log\frac qp.
\tag{C3.1}
$$

因此本卷已有横向关系能量可重写为：

$$
\boxed{
\sinh^2\!\left(
\delta\log\frac qp
\right)
=
\sinh^2\!\left(
Q_p(u)-Q_q(u)
\right).
}
\tag{C3.2}
$$

它不是一个附加比喻，而是 complex-power thread 的 real-charge gradient energy。

## C3.2 compact phase gradient

记：

$$
\tau=t_1-t_2,
\qquad
\Phi_{p,q}(\tau)
=
\frac{\tau}{2\pi}
\log\frac qp.
\tag{C3.3}
$$

则：

$$
\sin^2\!\left(
\frac{\tau}{2}\log\frac qp
\right)
=
\sin^2\!\left(
\pi\Phi_{p,q}(\tau)
\right).
\tag{C3.4}
$$

$\Phi_{p,q}$ 是两个 labelled prime phase flows 的相对 compact coordinate。

## C3.3 荷—相位统一式

本卷 prime-pair identity 因而成为：

$$
\boxed{
\frac{(pq)^{2\sigma}}4
|\mathcal K_{p,q}|^2
=
\sinh^2(Q_p-Q_q)
+
\sin^2(\pi\Phi_{p,q}).
}
\tag{C3.5}
$$

所以：

- $\sinh^2$ 读取 $\mathbb R$-charge difference；
- $\sin^2$ 读取 circle/solenoid phase difference；
- 两者来自同一个 complex determinant；
- 前者在 $\delta\ne0$ 时提供与 phase 无关的正底；
- 后者可以因 compact recurrence 反复归零。

这给出一个新的概念压缩：

$$
\boxed{
\text{PrimeGaps 的复核是 }
\mathbb R_{\rm charge}\times\mathcal S_{\rm phase}
\text{ 上的二槽关系 observer。}
}
\tag{C3.6}
$$

## C3.4 不可错误归一化

canonical charges 满足：

$$
\frac{Q_p(u)}{\log p}
=
-\delta
\qquad
\forall p.
\tag{C3.7}
$$

因此若错误地定义“归一化一致性能量”：

$$
\sum_{p<q}
W_{p,q}
\left(
\frac{Q_p}{\log p}
-
\frac{Q_q}{\log q}
\right)^2,
\tag{C3.8}
$$

它对所有 $\delta$ 都恒为零，完全删除离线信号。

真正的横向能量必须保留 raw logarithmic weights：

$$
Q_p-Q_q
=
\delta(\log q-\log p).
\tag{C3.9}
$$

所以 prime labels 与 $\log p$ 不是可约掉的单位选择，而是横向几何本身。

---

# 增订三·4　一个素数的有限 level phase aliasing

## C4.1 有限 level family

固定素数 $p$，取非空有限正整数集合 $S$。令：

$$
L_S=\operatorname{lcm}\{m:m\in S\}.
\tag{C4.1}
$$

只观察：

$$
\left(
\theta_{p,t}(m)
\right)_{m\in S}.
\tag{C4.2}
$$

### 定理 C4.1　有限 level aliasing 周期

两个实参数 $t,t'$ 在全部 $S$-levels 上不可区分，当且仅当：

$$
\boxed{
t-t'
\in
\frac{2\pi L_S}{\log p}\mathbb Z.
}
\tag{C4.3}
$$

#### 证明

令：

$$
x=\frac{(t-t')\log p}{2\pi}.
$$

在 level $m$ 上 phase 相等，当且仅当 $x/m\in\mathbb Z$，即 $x\in m\mathbb Z$。对所有 $m\in S$ 同时成立，当且仅当：

$$
x\in\bigcap_{m\in S}m\mathbb Z
=
L_S\mathbb Z.
$$

## C4.2 finite-window faithfulness

设观察高度区间 $I$ 的长度为 $T$。若：

$$
\frac{2\pi L_S}{\log p}>T,
\tag{C4.4}
$$

则有限 phase readout 在 $I$ 上单射。

特别地，只取一个 level $m$，只要：

$$
\boxed{
m>\frac{T\log p}{2\pi},
}
\tag{C4.5}
$$

level-$m$ phase observer 就足以在长度 $T$ 的任意高度窗中消除时间 alias。

所以：

$$
\boxed{
\text{无限 solenoid depth 只对无界高度轴必需；
每个有限谱窗都只需有限 level。}
}
\tag{C4.6}
$$

## C4.3 Fibonacci shell 深度

若选择 Fibonacci level $F_n$，条件成为：

$$
F_n>\frac{T\log p}{2\pi}.
\tag{C4.7}
$$

由 Binet 渐近：

$$
\boxed{
n_{\rm phase}(T,p)
=
\log_\varphi
\left(
\frac{\sqrt5\,T\log p}{2\pi}
\right)
+
O(1).
}
\tag{C4.8}
$$

这是一条不同于横向分辨深度的定律：

- 横向分辨深度由 $|\delta|\log(q/p)$ 控制；
- 纵向 phase de-aliasing 深度由 $T\log p$ 控制。

二者共同决定一个有限 RH observer 所需的 Zeckendorf depth。

---

# 增订三·5　完整 single-prime thread 与 phase inverse limit

## C5.1 全 level phase faithfulness

### 定理 C5.1　完整 one-prime phase thread 恢复 $t$

若：

$$
\theta_{p,t}(m)
=
\theta_{p,t'}(m)
\qquad
\forall m\ge1,
\tag{C5.1}
$$

则：

$$
\boxed{t=t'.}
\tag{C5.2}
$$

#### 证明

令：

$$
x=\frac{(t-t')\log p}{2\pi}.
$$

前件意味着 $x/m\in\mathbb Z$ 对所有正整数 $m$。取 $m>|x|$，则 $|x/m|<1$。它又是整数，只能为零，所以 $x=0$，继而 $t=t'$。

结合 norm charge：

### 推论 C5.2　一个完整 prime thread 忠实编码 $u$

$$
\boxed{
Z_{p,u}=Z_{p,v}
\Longrightarrow
u=v.
}
\tag{C5.3}
$$

## C5.2 charge 与 phase 的观察非对称

charge 具有 finite-coordinate recovery：

$$
Q_p(u)
=
m\log\|Z_{p,u}(m)\|
\tag{C5.4}
$$

对任意一个 $m$ 成立。

phase 则是 inverse-limit data：任意有限 levels 在全实轴上都保留非平凡 alias period。

所以 complex-power equivalence：

$$
\operatorname{ComplexPowerThread}
\simeq
\mathbb R\times\mathcal S
\tag{C5.5}
$$

在观察论上是不对称的：

$$
\boxed{
\mathbb R\text{-charge 是有限层可见的，}
\qquad
\mathcal S\text{-phase 的全局忠实性需要逆极限。}
}
\tag{C5.6}
$$

这解释了为什么 off-line displacement 产生 phase-independent hyperbolic floor，而 tangential time phase 可以具有任意深的 recurrence。

---

# 增订三·6　有限 solenoid observer 的 structural novelty 判据

## C6.1 问题设置

令 $\mathcal S$ 为 universal solenoid。对每个正整数 $m$，定义 coordinate observer：

$$
\pi_m:\mathcal S\to\mathbb R/\mathbb Z,
\qquad
\pi_m(\theta)=\theta_m.
\tag{C6.1}
$$

给定非空有限已观察集合 $S$ 与候选新 level $m$，令：

$$
N=\operatorname{lcm}(S\cup\{m\}),
\tag{C6.2}
$$

$$
a_s=\frac Ns
\qquad(s\in S),
\tag{C6.3}
$$

$$
b=\frac Nm,
\tag{C6.4}
$$

$$
d_S=\gcd\{a_s:s\in S\}.
\tag{C6.5}
$$

由 compatibility：

$$
\theta_s=a_s\theta_N,
\qquad
\theta_m=b\theta_N.
\tag{C6.6}
$$

### 定理 C6.1　finite-level semantic closure criterion

$$
\boxed{
\pi_m
\text{ 可由 }
\{\pi_s:s\in S\}
\text{ 恢复}
\Longleftrightarrow
d_S\mid b.
}
\tag{C6.7}
$$

#### 证明：充分性

若 $d_S\mid b$，由 Bézout 存在整数 $k_s$ 使：

$$
d_S=\sum_{s\in S}k_sa_s.
$$

写 $b=hd_S$，则：

$$
\theta_m
=
b\theta_N
=
\sum_{s\in S}hk_sa_s\theta_N
=
\sum_{s\in S}hk_s\theta_s.
\tag{C6.8}
$$

所以新 coordinate 是已有 coordinates 的整数线性组合。

#### 证明：必要性与显式 witness

若 $d_S\nmid b$，令：

$$
T=\frac N{d_S},
\tag{C6.9}
$$

并取 real-generated solenoid thread：

$$
\vartheta^{(T)}_r
=
\frac Tr
\pmod1.
\tag{C6.10}
$$

对任意 $s\in S$：

$$
\vartheta_s^{(T)}
=
\frac{N/s}{d_S}
=
\frac{a_s}{d_S}
=0\pmod1.
\tag{C6.11}
$$

但：

$$
\vartheta_m^{(T)}
=
\frac b{d_S}
\ne0\pmod1
\tag{C6.12}
$$

因为 $d_S\nmid b$。

所以零 phase thread 与 $\vartheta^{(T)}$ 在全部旧 observers 上碰撞，却被 $\pi_m$ 分离。

## C6.2 信息逃逸解释

项目的 structural novelty 语言因而给出：

$$
\boxed{
d_S\nmid\frac Nm
\Longleftrightarrow
\pi_m
\text{ 对 finite level catalog 具有严格 kernel novelty。}
}
\tag{C6.13}
$$

这比“更深 level 一定更有信息”精确得多。

一个 numerically 更大的 level 可能已经在旧 coordinates 的 semantic closure 中；一个较小但 divisibility-independent 的 level 也可能提供 unique capture。

因此 solenoid phase 的信息层级不是线性深度序，而是：

$$
\boxed{
\text{由 divisibility lattice、gcd 与 lcm 控制的部分序。}
}
\tag{C6.14}
$$

---

# 增订三·7　phase faithfulness 的深度—宽度对偶

## C7.1 两个 labelled primes 在 level one 已全局忠实

取不同素数 $p\ne q$，定义：

$$
\iota_{p,q}(u)
=
\left(
p^{-u},
q^{-u}
\right).
\tag{C7.1}
$$

### 定理 C7.1　two-prime level-one embedding

$$
\boxed{
\iota_{p,q}(u)=\iota_{p,q}(v)
\Longrightarrow
u=v.
}
\tag{C7.2}
$$

#### 证明

取模长，从：

$$
|p^{-u}|=|p^{-v}|
$$

得到 $\Re u=\Re v$。

令 $\tau=\Im u-\Im v$。相位相等给出整数 $k,\ell$：

$$
\tau\log p=2\pi k,
\qquad
\tau\log q=2\pi\ell.
\tag{C7.3}
$$

若 $\tau\ne0$，则：

$$
\frac{\log p}{\log q}
=
\frac{k}{\ell}
\in\mathbb Q.
\tag{C7.4}
$$

于是存在非零整数关系：

$$
p^{\ell}=q^{k},
$$

与不同素数的唯一分解矛盾。故 $\tau=0$。

## C7.2 深度—宽度对偶

于是有两种完全不同的 phase 完备方式：

$$
\boxed{
\begin{aligned}
\text{one prime + all power levels}
&\Longrightarrow
\text{phase faithful},\\
\text{two distinct labelled primes + level one}
&\Longrightarrow
\text{phase faithful}.
\end{aligned}
}
\tag{C7.5}
$$

前者使用 vertical root depth，后者使用 horizontal prime width。

这说明：

$$
\boxed{
\text{Zeckendorf/power depth 与 prime-pair relation width
是两种可互补的 observer resource。}
}
\tag{C7.6}
$$

## C7.3 scalar product 重新制造 alias

若只保留 scalar product：

$$
p^{-u}q^{-u}
=
(pq)^{-u},
\tag{C7.7}
$$

则虚部只按周期：

$$
\frac{2\pi}{\log(pq)}
\tag{C7.8}
$$

可见。

所以 labelled pair 是单射，而 commutative product 不是单射。

这是一个最小关系信息逃逸模型：

$$
\boxed{
\text{两个 prime labels 已足以恢复 }t,
\quad
\text{但把它们乘成一个 scalar 会再次遗失 }t.
}
\tag{C7.9}
$$

prime-pair alternating determinant、ratio、exterior square 或 ordered holonomy 的作用，正是阻止这一横向标签被 scalarization 删除。

---

# 增订三·8　charge graph、共同模与 anchor

## C8.1 非线性 charge graph energy

取连通有限 prime graph $G=(V,E)$，正边权 $W_e>0$。对任意 real charge vector：

$$
q=(q_v)_{v\in V},
$$

定义：

$$
\boxed{
\mathcal E_G^{\rm ch}(q)
=
\sum_{\{i,j\}\in E}
W_{ij}\sinh^2(q_i-q_j).
}
\tag{C8.1}
$$

则：

$$
\mathcal E_G^{\rm ch}(q)=0
\Longleftrightarrow
q_i=q_j\quad\forall i,j,
\tag{C8.2}
$$

即：

$$
\boxed{
\ker\mathcal E_G^{\rm ch}
=
\operatorname{span}\{\mathbf1\}.
}
\tag{C8.3}
$$

在小 charge 区：

$$
\mathcal E_G^{\rm ch}(q)
=
q^TL_Gq
+
O(\|B^Tq\|^4),
\tag{C8.4}
$$

其中 $L_G$ 是加权 graph Laplacian。

## C8.2 physical spectral charge ray

对 canonical prime threads：

$$
q_p=Q_p(u)=-\delta\log p.
\tag{C8.5}
$$

令：

$$
\ell=(\log p)_{p\in V}.
$$

则：

$$
q=-\delta\ell.
\tag{C8.6}
$$

只要 graph 至少连接两个不同素数，$\ell$ 不是常向量，因此：

$$
\mathcal E_G^{\rm ch}(-\delta\ell)=0
\Longleftrightarrow
\delta=0.
\tag{C8.7}
$$

所以在 canonical 一维 spectral manifold 上，pair charge differences 已足以定位临界线。

## C8.3 ambient charge space 仍有共同模

若为了 Schur elimination 把 charge 扩张到一般 ambient state space，则 constant charge mode 不再被 edge energy 看见。

因此必须区分：

$$
\boxed{
\text{restricted physical charge ray 上的 faithful detection}
}
\tag{C8.8}
$$

与：

$$
\boxed{
\text{ambient charge Hilbert space 上的 full coercivity}.
}
\tag{C8.9}
$$

前者不需要额外 anchor；后者必须控制共同模。

## C8.4 grounded Laplacian

定义平均 charge：

$$
\bar q=\frac1{|V|}\sum_{v\in V}q_v.
\tag{C8.10}
$$

对 $\kappa>0$，定义：

$$
\boxed{
\mathcal E_{G,\kappa}^{\rm grounded}(q)
=
q^TL_Gq
+
\kappa|V|\,|\bar q|^2.
}
\tag{C8.11}
$$

把：

$$
q=\bar q\,\mathbf1+q_\perp,
\qquad
q_\perp\perp\mathbf1,
\tag{C8.12}
$$

并令 $\lambda_2(L_G)>0$ 为第一非零 Laplacian eigenvalue，则：

$$
\boxed{
\mathcal E_{G,\kappa}^{\rm grounded}(q)
\ge
\min\{\lambda_2(L_G),\kappa\}\|q\|^2.
}
\tag{C8.13}
$$

这给出 full ambient coercivity。

Gamma/pole completion 是否 canonical 地提供式 (C8.11) 中的共同模 anchor，目前仍是开放桥；不能因为 completed function 具有 Gamma factor 就直接认定该项已经存在。

---

# 增订三·9　荷—相位乘积 arena 的 exact escape rate

## C9.1 finite product arena

取有限 charge set $C$，$|C|=c$，有限 phase set $P$，$|P|=p$。状态空间为：

$$
\Omega=C\times P.
\tag{C9.1}
$$

假设 charge observer 完全区分 $C$。某个有限 phase observer family 将 $P$ 分成等价类：

$$
P=P_1\sqcup\cdots\sqcup P_r,
\qquad
|P_j|=n_j.
\tag{C9.2}
$$

联合 observers 下，两个状态不可区分，当且仅当：

- charge 相同；
- phase 落在同一个 $P_j$。

所以有序非对角 escape pair 数为：

$$
\boxed{
|\operatorname{EscapePairs}|
=
c\sum_{j=1}^{r}n_j(n_j-1).
}
\tag{C9.3}
$$

总有序非对角 pair 数为：

$$
cp(cp-1).
\tag{C9.4}
$$

因此 exact escape rate 为：

$$
\boxed{
\varepsilon
=
\frac{
\sum_jn_j(n_j-1)
}{
p(cp-1)
}.
}
\tag{C9.5}
$$

## C9.2 两个极端

只观察 charge、不观察 phase 时，只有一个 phase class $n_1=p$：

$$
\boxed{
\varepsilon_{\rm charge}
=
\frac{p-1}{cp-1}.
}
\tag{C9.6}
$$

phase 也被完全分离时，所有 $n_j=1$：

$$
\boxed{
\varepsilon_{\rm charge+phase}=0.
}
\tag{C9.7}
$$

## C9.3 structural novelty 等价于严格降率

加入一个新 phase coordinate 后：

- 若它在已有 semantic closure 中，partition 不变，escape rate 不变；
- 若它分裂至少一个旧 class，则：

$$
\sum_jn_j(n_j-1)
$$

严格下降，因而 exact escape rate 严格下降。

结合定理 C6.1：

$$
\boxed{
d_S\nmid\frac Nm
\Longrightarrow
\pi_m
\text{ 具有显式 unique-capture pair，并严格降低有限 arena 的逃逸率。}
}
\tag{C9.8}
$$

这把 abstract structural novelty 与 universal-solenoid divisibility geometry 接成一个可计算判据。

---

# 增订三·10　离圆零点必产生负径向先兆区域

## C10.1 Cayley 拉回

固定 $a>1/2$。令：

$$
u=C_a^{-1}(w)
=
a\frac{w-1}{w+1},
\tag{C10.1}
$$

并定义：

$$
G_a(w)
=
\Xi\!\left(
\frac12+C_a^{-1}(w)
\right),
\qquad
w\ne-1.
\tag{C10.2}
$$

若 $\rho_*$ 是离线零点，则其 Cayley 像 $w_*$ 满足：

$$
G_a(w_*)=0,
\qquad
|w_*|\ne1.
\tag{C10.3}
$$

利用 reciprocal reflection，可选择圆外伙伴：

$$
w_*=r_*e^{iq_*},
\qquad
r_*>1.
\tag{C10.4}
$$

## C10.2 radial counting profile

定义：

$$
\boxed{
\mathscr Q_a(q,r)
=
|G_a(re^{iq})|^2.
}
\tag{C10.5}
$$

在 $\mathscr Q_a>0$ 的位置定义 scale-weighted radial log derivative：

$$
\boxed{
\mathscr R_a(q,r)
=
r\partial_r\log\mathscr Q_a(q,r).
}
\tag{C10.6}
$$

## C10.3 局部正常形

设 $w_*$ 是 $m$ 重零点。局部有：

$$
G_a(w)
=
(w-w_*)^mH(w),
\qquad
H(w_*)\ne0.
\tag{C10.7}
$$

沿同一径向射线 $q=q_*$：

$$
\mathscr Q_a(q_*,r)
=
|r-r_*|^{2m}|H(re^{iq_*})|^2.
\tag{C10.8}
$$

因此：

$$
\boxed{
\mathscr R_a(q_*,r)
=
\frac{2mr}{r-r_*}
+
r\partial_r
\log|H(re^{iq_*})|^2.
}
\tag{C10.9}
$$

当 $r\uparrow r_*$ 且 $r<r_*$ 时，第一项趋向 $-\infty$，第二项保持有界。

### 定理 C10.1　off-circle zero forces a negative radial precursor

存在 $r_0<r_*$，使：

$$
r_0<r<r_*
\Longrightarrow
\mathscr Q_a(q_*,r)>0,
\qquad
\mathscr R_a(q_*,r)<0.
\tag{C10.10}
$$

由于 $\mathscr Q_a$ 与 $\mathscr R_a$ 在避开零点的局部区域连续，存在一个非空开集：

$$
\boxed{
\mathcal N_a
=
\left\{
(q,r):
r>0,\,
\mathscr Q_a(q,r)>0,\,
\mathscr R_a(q,r)<0
\right\}
}
\tag{C10.11}
$$

包含这些内侧点。

这正好为项目 `RationalNegativeCountCertificate` 的“开放”和“RH 失败时非空”两个前件提供一个具体条件性来源。

---

# 增订三·11　有理 radial precursor certificate

由 $\mathbb Q^2$ 在 $\mathbb R^2$ 中稠密以及定理 C10.1：

### 定理 C11.1　离线零点蕴含有理负径向先兆

若 completed $\Xi$ 存在离线零点，则对任意固定 $a>1/2$，存在：

$$
q\in\mathbb Q,
\qquad
r\in\mathbb Q_{>0},
\tag{C11.1}
$$

使：

$$
\boxed{
\mathscr Q_a(q,r)>0,
\qquad
r\partial_r\log\mathscr Q_a(q,r)<0.
}
\tag{C11.2}
$$

这里的 $q$ 是角度的一个实代表，不要求是 $\pi$ 的有理倍数。

## C11.2 证书边界

式 (C11.2) 是有限参数 witness，但它还不是完全离散的 machine certificate。要验证它，仍需要：

- 对 $G_a$ 在有理点的可认证求值或区间界；
- 对 radial derivative 的可认证严格负上界；
- 对 branch、Cayley inverse 与远离 $w=-1$ 的域控制。

所以该定理证明的是：

$$
\boxed{
\neg\mathrm{RH}
\Longrightarrow
\text{存在有限有理参数的严格不等式先兆}.
}
\tag{C11.3}
$$

它没有证明该先兆在当前工程中已经可执行枚举。

---

# 增订三·12　有理矩形是全部离线零点的可数观察基

## C12.1 离轴有理矩形

令 $\mathfrak R_{\mathbb Q}^{\rm off}$ 为所有闭矩形：

$$
R=[x_0,x_1]+i[y_0,y_1],
\tag{C12.1}
$$

其中：

$$
x_0,x_1,y_0,y_1\in\mathbb Q,
\qquad
x_0<x_1,
\qquad
y_0<y_1,
\tag{C12.2}
$$

且整个矩形位于 critical strip 内并与临界线保持正距离：

$$
\overline R
\subset
\left\{
s:
0<\Re s<1,\,
\Re s\ne\frac12
\right\}.
\tag{C12.3}
$$

该 family 可数。

## C12.2 RH 的 rational rectangle 等价

记 $N_\Xi(R)$ 为 $\Xi$ 在 $R$ 内按解析重数的零点数，边界零点通过选择更小矩形避开。

### 定理 C12.1　countable off-axis zero-count criterion

$$
\boxed{
\mathrm{RH}
\Longleftrightarrow
N_\Xi(R)=0
\quad
\forall R\in\mathfrak R_{\mathbb Q}^{\rm off}.
}
\tag{C12.4}
$$

#### 证明

若 RH 成立，离轴矩形中显然没有零点。

反之，若存在离线零点 $\rho_*$，由零点离散性与 $\rho_*$ 到临界线的正距离，可以选择一个足够小的开邻域，只包含有限零点且边界无零。再由有理数稠密性，在该邻域中选择一个有理矩形包含 $\rho_*$、边界不经过零点且仍完全离轴，于是：

$$
N_\Xi(R)>0.
$$

## C12.3 真与假的证书非对称

因此：

$$
\boxed{
\neg\mathrm{RH}
\Longrightarrow
\exists R\in\mathfrak R_{\mathbb Q}^{\rm off},
\quad
N_\Xi(R)>0.
}
\tag{C12.5}
$$

RH 失败有一个有限几何窗口 witness。

但 RH 本身是：

$$
\forall R\in\mathfrak R_{\mathbb Q}^{\rm off},
\quad
N_\Xi(R)=0,
\tag{C12.6}
$$

仍是一个可数全称命题。

所以“把无限 RH 改成有限问题”的严格版本不是单个有限问题，而是：

$$
\boxed{
\text{失败由一个有限窗口见证；
成立需要一族可数有限窗口证书或一个统一全局 coercivity theorem。}
}
\tag{C12.7}
$$

---

# 增订三·13　Rouché 将 analytic approximation 变成零点证书

## C13.1 边界误差与 determinant floor

对 $R\in\mathfrak R_{\mathbb Q}^{\rm off}$，设 $D_N$ 在 $R$ 的邻域解析。定义：

$$
\operatorname{Err}_N(R)
=
\sup_{s\in\partial R}
|\Xi(s)-D_N(s)|,
\tag{C13.1}
$$

$$
\operatorname{Floor}_N(R)
=
\inf_{s\in\partial R}
|D_N(s)|.
\tag{C13.2}
$$

若：

$$
\boxed{
\operatorname{Err}_N(R)
<
\operatorname{Floor}_N(R),
}
\tag{C13.3}
$$

则项目的 Rouché theorem 给出：

$$
\boxed{
N_\Xi(R)=N_{D_N}(R).
}
\tag{C13.4}
$$

## C13.2 两种 finite certificate

### 排除证书

若：

$$
N_{D_N}(R)=0
\tag{C13.5}
$$

且式 (C13.3) 成立，则：

$$
N_\Xi(R)=0.
\tag{C13.6}
$$

### 反例证书

若：

$$
N_{D_N}(R)>0
\tag{C13.7}
$$

且式 (C13.3) 成立，则：

$$
N_\Xi(R)>0,
\tag{C13.8}
$$

从而 RH 失败。

## C13.3 locally uniform convergence 的固定窗口稳定性

假设：

$$
D_N\longrightarrow\Xi
\tag{C13.9}
$$

在 compact sets 上局部一致收敛。

若 $\partial R$ 无 $\Xi$ 零点，则：

$$
m_R
=
\inf_{\partial R}|\Xi|>0.
\tag{C13.10}
$$

对充分大 $N$：

$$
\sup_{\partial R}|D_N-\Xi|<\frac{m_R}{3}.
\tag{C13.11}
$$

于是：

$$
|D_N|
\ge
|\Xi|-|D_N-\Xi|
>
\frac{2m_R}{3},
\tag{C13.12}
$$

所以：

$$
|D_N-\Xi|<|D_N|
\tag{C13.13}
$$

并得到 zero-count stability。

因此每个固定有理矩形的零点计数最终稳定。

但 $N$ 可以依赖 $R$；局部一致收敛本身不提供一个覆盖全部高度的统一有限 $N$。

---

# 增订三·14　Schur margin 到 determinant floor 的定量桥

## C14.1 analytic transfer 与 Hermitianization

设：

$$
T_N(s)\in M_{d_N}(\mathbb C)
\tag{C14.1}
$$

在矩形邻域逐项 holomorphic。定义：

$$
E_N(s)
=
T_N(s)^*T_N(s)
\succeq0.
\tag{C14.2}
$$

$E_N$ 不 holomorphic，但：

$$
\ker E_N(s)=\ker T_N(s),
\tag{C14.3}
$$

并且：

$$
|\det T_N(s)|^2
=
\det E_N(s).
\tag{C14.4}
$$

## C14.2 hidden block 与 Schur complement

把：

$$
E_N
=
\begin{pmatrix}
A&B\\
B^*&D
\end{pmatrix},
\tag{C14.5}
$$

并假设在某个集合上：

$$
D\succeq dI,
\qquad
d>0,
\tag{C14.6}
$$

$$
S
:=
A-BD^{-1}B^*
\succeq\kappa I,
\qquad
\kappa>0,
\tag{C14.7}
$$

$$
\|B\|\le b.
\tag{C14.8}
$$

令：

$$
C=D^{-1}B^*.
\tag{C14.9}
$$

完成平方给出：

$$
\langle E_N(x,y),(x,y)\rangle
=
\langle Sx,x\rangle
+
\langle D(y+Cx),y+Cx\rangle.
\tag{C14.10}
$$

定义 triangular map：

$$
L(x,y)=(x,y+Cx).
\tag{C14.11}
$$

则：

$$
E_N
=
L^*
\begin{pmatrix}
S&0\\
0&D
\end{pmatrix}
L.
\tag{C14.12}
$$

又有：

$$
\|L^{-1}\|
\le
1+\|C\|
\le
1+\frac bd.
\tag{C14.13}
$$

### 定理 C14.1　Schur-to-singular-value floor

$$
\boxed{
E_N
\succeq
\mu I,
\qquad
\mu
=
\frac{
\min\{\kappa,d\}
}{
(1+b/d)^2
}.
}
\tag{C14.14}
$$

#### 证明

由式 (C14.12)：

$$
\langle E_Nv,v\rangle
\ge
\min\{\kappa,d\}\|Lv\|^2.
$$

而：

$$
\|Lv\|
\ge
\frac{\|v\|}{\|L^{-1}\|}.
$$

代入式 (C14.13) 即得。

所以：

$$
\sigma_{\min}(T_N)
\ge
\sqrt\mu.
\tag{C14.15}
$$

## C14.3 determinant floor

所有 singular values 都不小于 $\sqrt\mu$，所以：

$$
\boxed{
|\det T_N|
\ge
\mu^{d_N/2}.
}
\tag{C14.16}
$$

若：

$$
D_N(s)
=
U_N(s)\det T_N(s),
\tag{C14.17}
$$

且边界上：

$$
|U_N(s)|\ge u_N>0,
\tag{C14.18}
$$

则：

$$
\boxed{
\operatorname{Floor}_N(R)
\ge
u_N\mu_N^{d_N/2}.
}
\tag{C14.19}
$$

因此一个足够的 Rouché 条件是：

$$
\boxed{
\operatorname{Err}_N(R)
<
u_N\mu_N^{d_N/2}.
}
\tag{C14.20}
$$

这就是 Schur margin 到 analytic zero-count stability 的定量桥。

---

# 增订三·15　determinant entropy tax 与 Hankel 最小记忆

## C15.1 证书精度预算

由式 (C14.20)，所需误差精度至少满足：

$$
-\log\operatorname{Err}_N(R)
>
-\log u_N
+
\frac{d_N}{2}\log\frac1{\mu_N}.
\tag{C15.1}
$$

定义：

$$
\boxed{
\mathfrak B_N(R)
=
-\log u_N
+
\frac{d_N}{2}\log\frac1{\mu_N}.
}
\tag{C15.2}
$$

它是由 unit floor、operator gap 与 realization dimension 共同决定的 determinant certificate budget。

即使 $\mu_N$ 保持正，只要：

$$
0<\mu_N<1
$$

且 $d_N\to\infty$，determinant floor 仍可能指数趋零。

所以：

$$
\boxed{
\text{positive-definite}
\not\Longrightarrow
\text{Rouché-certifiable with a useful uniform margin}.
}
\tag{C15.3}
$$

## C15.2 naive state enumeration 的代价

Zeckendorf 深度 $Q$ 的合法历史数为：

$$
M_Q=F_{Q+2}\asymp\varphi^Q.
\tag{C15.4}
$$

若把每个历史当作独立 matrix state，则 generic determinant floor 的维数项可能具有尺度：

$$
\mu^{M_Q/2}
=
\exp\!\left(
-\Theta(\varphi^Q)
\right).
\tag{C15.5}
$$

相应误差预算关于 $Q$ 指数增长。

## C15.3 minimal transfer 的代价

同一 hard-core count behavior 具有二阶递推和 $2\times2$ transfer。其 Hankel rank 恰为 $2$，所以可见行为只需二态记忆。

若 analytic determinant representation 可以在不改变目标 scalar 零集的前提下压缩到 minimal realization rank $r_N$，则维数税从：

$$
\frac{d_N}{2}\log\frac1\mu
$$

降为：

$$
\frac{r_N}{2}\log\frac1\mu.
\tag{C15.6}
$$

在 Zeckendorf hard-core 原型中：

$$
r_N=2.
\tag{C15.7}
$$

于是本轮得到一个新的解释：

$$
\boxed{
\text{Zeckendorf/Hankel 的证明论价值，
不是制造指数多状态，
而是把指数多历史压缩成最小二态 memory，
从而降低 determinant zero certificate 的维数税。}
}
\tag{C15.8}
$$

这里仍需保留一个前件：state-space 压缩必须保持 analytic determinant，至多乘以无零 unit。Hankel 行为等价本身不自动保证任意 chosen determinant 不变。

---

# 增订三·16　有限高度 observer 的双重深度预算

## C16.1 phase budget

由式 (C4.8)，覆盖高度窗 $|t|\le T$ 的 single-prime Fibonacci phase depth 为：

$$
n_{\rm phase}
=
\log_\varphi(T\log p)+O(1).
\tag{C16.1}
$$

## C16.2 transverse budget

由增订一的 Fibonacci–Lorentz scaling，分辨 prime pair $(p,q)$ 上横向位移 $\delta$ 需要：

$$
n_{\perp}
=
\log_\varphi
\frac1{
|\delta|\,|\log(q/p)|
}
+
O(1).
\tag{C16.2}
$$

## C16.3 joint observer depth

所以一个同时在有限高度窗中解除 phase alias、又能分辨给定 transverse scale 的 observer，可取：

$$
\boxed{
n_{\rm obs}
=
\max\left\{
n_{\rm phase},
n_{\perp}
\right\}.
}
\tag{C16.3}
$$

对假想第一离线零点：

$$
\rho_*
=
\frac12+\delta_*+it_*,
\tag{C16.4}
$$

存在有限 $n$，使：

- level $F_n$ 在 $[0,t_*]$ 中对 single-prime phase 无 alias；
- pair shell $F_n$ 对 $\delta_*$ 达到非微扰横向尺度；
- 一个围绕 $\rho_*$ 的有理矩形可由有限 phase/charge coordinates 区分。

所以：

$$
\boxed{
\neg\mathrm{RH}
\text{ 的第一个离线缺陷在 observer geometry 上具有有限深度 witness。}
}
\tag{C16.5}
$$

这仍不意味着当前工程已能从 prime side 算出该 witness；它只说明一旦缺陷存在，不需要无限深度才能在它所在的有限高度窗中分辨它。

---

# 增订三·17　四类不同的信息逃逸及其唯一修复

当前理论至少出现四种不可混同的 kernel enlargement。

## C17.1 label scalarization escape

两个 labelled primes：

$$
(p^{-u},q^{-u})
$$

忠实，但乘积：

$$
(pq)^{-u}
$$

重新产生 phase alias。

修复对象是：

$$
\boxed{
\text{pair / ratio / exterior / ordered holonomy readout}.
}
\tag{C17.1}
$$

## C17.2 common-charge escape

edge differences 看不见：

$$
q\mapsto q+c\mathbf1.
$$

修复对象是：

$$
\boxed{
\text{one independent charge ANCHOR}.
}
\tag{C17.2}
$$

## C17.3 finite-root-depth escape

有限 solenoid coordinates 看不见某些 deeper root choices。其 novelty 由定理 C6.1 的 divisibility criterion 决定。

修复对象是：

$$
\boxed{
\text{structurally novel deeper level
或 multiplicatively independent prime width}.
}
\tag{C17.3}
$$

## C17.4 determinant-boundary escape

pointwise positive Schur margin 若没有 uniform lower floor，可能不足以压过 analytic approximation error；高维 determinant 还会把 singular floor 乘成极小量。

修复对象是：

$$
\boxed{
\text{Hankel-minimal realization
+
uniform Schur floor
+
strict Rouché inequality}.
}
\tag{C17.4}
$$

## C17.5 不可互换性

四种修复分别作用于不同 kernel：

- pair observer 不能 grounding common charge；
- anchor 不能恢复 deep phase；
- deep phase 不能提供 determinant boundary floor；
- positive determinant floor 不能重构 prime ordering。

所以最终低逃逸理论必须是它们的 joint kernel，而不是用一个“能量”概念替代全部层。

---

# 增订三·18　Rouché–Schur rational certificate stack

## C18.1 单矩形证书

对每个离轴有理矩形 $R$，一个完整 finite certificate 可由下列数据组成：

1. 一个有限维 holomorphic transfer $T_N(s)$；
2. 一个无零 analytic unit $U_N(s)$；
3. scalar approximant：

$$
D_N(s)=U_N(s)\det T_N(s);
\tag{C18.1}
$$

4. $E_N=T_N^*T_N$ 的 visible–hidden block decomposition；
5. 整个 $\overline R$ 上：

$$
D\succeq dI,
\qquad
S\succeq\kappa I,
\qquad
\|B\|\le b;
\tag{C18.2}
$$

6. unit floor：

$$
|U_N|\ge u>0;
\tag{C18.3}
$$

7. certified analytic error：

$$
\sup_{\partial R}|\Xi-D_N|
<
u
\left(
\frac{\min\{\kappa,d\}}{(1+b/d)^2}
\right)^{d_N/2}.
\tag{C18.4}
$$

由式 (C18.2)，$T_N$ 在整个矩形内可逆，所以：

$$
N_{D_N}(R)=0.
\tag{C18.5}
$$

由式 (C18.4) 和 Rouché：

$$
N_\Xi(R)=0.
\tag{C18.6}
$$

### 条件定理 C18.1　countable rational certificate criterion implies RH

若每个：

$$
R\in\mathfrak R_{\mathbb Q}^{\rm off}
$$

都具有上述某个 finite certificate，则：

$$
\boxed{\mathrm{RH}.}
\tag{C18.7}
$$

#### 证明

每个离轴有理矩形都无零，再用定理 C12.1。

## C18.2 failure taxonomy

反过来，若存在离线零点，则包含它的某个有理矩形必使 certificate stack 的至少一层失败：

$$
\boxed{
\begin{aligned}
&\text{不存在 canonical finite transfer；或}\\
&\det T_N\text{ 与 }\Xi\text{ 的 unit relation 不忠实；或}\\
&\text{hidden block 失去正 gap；或}\\
&\text{Schur margin 在矩形内闭合；或}\\
&\text{unit amplitude 消失；或}\\
&\text{approximation error 不足以跨过 determinant floor；或}\\
&\text{dimension growth 使 floor 比误差更快坍缩。}
\end{aligned}
}
\tag{C18.8}
$$

这把“离线相变原因”从单一比喻改写成一组互斥程度未定、但逐项可验证的 failure modes。

---

# 增订三·19　从 prime–zero 输运到 finite certificate 的新研究顺序

此前路线直接追求：

$$
E_{\rm prime}^{\perp}
\longrightarrow
E_{\rm off}^{\rm odd}.
\tag{C19.1}
$$

本增订表明，可以把该桥拆成更细的七层。

## 第一层：canonical prime threads

构造并闭合：

$$
Z_{p,u}(m)
=
e^{-u\log p/m},
\qquad
Q_p=-\delta\log p.
\tag{C19.2}
$$

## 第二层：labelled relation geometry

证明：

$$
\sinh^2(\delta\log(q/p))
=
\sinh^2(Q_p-Q_q),
\tag{C19.3}
$$

并保留 compact phase difference。

## 第三层：finite structural novelty

用 $\gcd/\operatorname{lcm}$ 判据识别哪些 solenoid level readouts 真正缩小 kernel；用 two-prime embedding识别横向 prime width 的 phase faithfulness。

## 第四层：grounded relation coercivity

在 ambient charge/phase Galerkin space 上加入最小 ANCHOR，使 graph differential 没有共同模 escape。

## 第五层：analytic transfer

构造：

$$
T_N(s),
\qquad
D_N(s)=U_N(s)\det T_N(s),
\tag{C19.4}
$$

并证明 $D_N\to\Xi$ locally uniformly，带可计算误差。

## 第六层：Hermitian Schur certificate

对：

$$
E_N=T_N^*T_N
$$

证明 hidden block、cycle block、charge anchor 与 visible block 的 uniform Schur lower bounds。

## 第七层：Rouché exhaustion

在所有离轴有理矩形上证明：

$$
\operatorname{Err}_N(R)
<
\operatorname{Floor}_N(R).
\tag{C19.5}
$$

这七层中，前四层主要是有限关系几何；第五层是 prime–Gamma analytic heart；第六层是 positive completion heart；第七层是从 finite approximation 到 global zero exclusion 的 limit heart。

---

# 增订三·20　建议形式化节点

以下是本增订自然产生的节点名称。它们是理论分解，不表示已经创建文件。

```text
D5/S3/Observer/PrimePowerThread/
  CenteredPrimePowerThread.lean
  PrimeThreadCompatibility.lean
  PrimeThreadLogarithmicCharge.lean
  PrimeThreadSolenoidPhase.lean
  ReflectedPrimeThreadInverseConjugate.lean
  CriticalLineIffZeroPrimeCharge.lean

D5/S3/Observer/PrimeThreadRelation/
  PrimePairChargeGradient.lean
  PrimePairKernelChargePhaseIdentity.lean
  RawChargeWeightCannotNormalizeAway.lean
  TwoPrimeLevelOneEmbedding.lean
  ScalarPrimeProductPhaseAliasing.lean

D5/S3/Observer/SolenoidInformationEscape/
  FiniteLevelAliasingPeriod.lean
  FiniteWindowSingleLevelFaithfulness.lean
  FullThreadPhaseFaithfulness.lean
  FiniteLevelSemanticClosureCriterion.lean
  LevelObserverUniqueCaptureWitness.lean
  SolenoidLevelStructuralNovelty.lean

D5/S3/Observer/ChargeGraph/
  NonlinearChargeGraphEnergy.lean
  ChargeGraphConstantKernel.lean
  PhysicalPrimeChargeRayFaithful.lean
  GroundedChargeLaplacian.lean
  GroundedChargeCoercivity.lean
  PrimeGammaCommonChargeAnchorTarget.lean

D5/S3/Zeros/CayleyRadialCertificate/
  CayleyPulledBackZeroProfile.lean
  OffCircleZeroRadialLogDerivative.lean
  OffCircleZeroNegativeRegionOpen.lean
  OffLineZeroRationalRadialPrecursor.lean

D5/S3/Weil/ZetaAnalytic/RationalRectangleCertificate/
  OffAxisRationalRectangleBasis.lean
  RhIffAllRationalRectangleCountsZero.lean
  LocallyUniformZeroCountStability.lean
  RoucheZeroFreeApproximantCertificate.lean

D5/S3/Weil/ZetaLinear/SchurRoucheBridge/
  BlockEnergyTriangularFactorization.lean
  SchurMarginSingularValueFloor.lean
  SingularValueDeterminantFloor.lean
  SchurMarginRoucheBoundaryFloor.lean
  DeterminantDimensionTax.lean
  HankelMinimalCertificateDimensionTarget.lean

D5/S3/Weil/PrimeGammaCertificate/
  CanonicalPrimeZeckendorfGammaTransferTarget.lean
  TransferDeterminantXiUnitTarget.lean
  LocallyUniformTransferApproximationTarget.lean
  RationalRectangleCertificateExhaustionTarget.lean
  RationalCertificateStackImpliesRhTarget.lean
```

其中以下节点可以纯有限地闭合：

- prime thread compatibility；
- charge formula；
- reflection formula；
- finite aliasing period；
- full thread faithfulness；
- two-prime embedding；
- solenoid $\gcd/\operatorname{lcm}$ novelty criterion；
- graph constant kernel；
- grounded Laplacian coercivity；
- local radial precursor；
- Schur-to-singular floor；
- singular-to-determinant floor；
- rational rectangle count equivalence。

所有带 `Target` 的节点都不得通过把结论写入 structure field 来伪闭合。

---

# 增订三·21　结论地位总表

| 结论 | 地位 |
|---|---|
| complex power thread 分解为 $\mathbb R\times\mathcal S$ | 仓库机器闭合 |
| zero charge 当且仅当全部 levels unit norm | 仓库机器闭合 |
| centered prime thread $Z_{p,u}(m)=e^{-u\log p/m}$ compatible | 本增订直接有限推论 |
| prime charge 为 $-\delta\log p$ | 本增订直接计算 |
| 同高度反射翻转 charge、保持 phase | 本增订直接计算 |
| 临界线等价于任意 prime thread 的 zero-charge locus | 本增订直接推论 |
| prime transverse $\sinh^2$ 等于 raw charge-gradient energy | 本增订精确恒等式 |
| finite single-prime levels 在全轴 phase faithful | 不成立；存在 lcm alias |
| finite single-prime level 在充分短高度窗 faithful | 本增订有限定理 |
| full single-prime thread phase faithful | 本增订有限论证 |
| two distinct labelled primes 的 level-one readout faithful | 本增订有限定理 |
| scalar product 保持该 faithfulness | 不成立 |
| 任意更深 solenoid level 都 structurally novel | 不成立 |
| level novelty 由 gcd/lcm divisibility 判据决定 | 本增订有限定理 |
| charge graph edge energy 在 ambient space 正定 | 不成立；常向量是 kernel |
| restricted canonical prime charge ray 上 pair energy faithful | 本增订有限定理 |
| mean anchor + connected graph 给出 full coercivity | 本增订有限定理 |
| Gamma completion 已提供该 anchor | 尚未建立 |
| 离圆零点产生 open negative radial precursor | 本增订条件解析定理 |
| RH 失败产生有理 radial precursor | 本增订 + 仓库 rational-certificate theorem |
| RH 等价于全部离轴有理矩形零点计数为零 | 本增订精确等价 |
| strict Rouché boundary inequality 保持矩形零点数 | 仓库机器闭合 |
| pointwise Schur 正性自动给出统一 Rouché floor | 不成立 |
| uniform hidden/Schur bounds 给出显式 determinant floor | 本增订有限算子定理 |
| determinant floor 支付 $d_N/2$ 的维数税 | 本增订直接推论 |
| Zeckendorf raw state count 是最佳 transfer dimension | 不成立 |
| Hankel-minimal two-state memory 可降低 local certificate dimension | 条件于 determinant-preserving realization |
| 每个有理离轴矩形都有 certificate stack 蕴含 RH | 本增订条件定理 |
| canonical prime–Gamma transfer 已完成该 stack | 尚未建立 |
| 本增订证明 RH | 不成立 |

---

# 增订三·22　最终收束

本增订把项目中此前分散的四种对象接成一条严格链：

$$
\boxed{
\begin{aligned}
\text{complex power thread}
&\simeq
\text{logarithmic charge}
\times
\text{solenoid phase},\\
\text{critical line}
&=
\text{zero-charge slice},\\
\text{prime-pair complex kernel}
&=
\text{charge-gradient hyperbolic energy}
+
\text{phase-gradient circular energy},\\
\text{Zeckendorf depth}
&=
\text{finite-height phase de-aliasing resource},\\
\text{prime width}
&=
\text{multiplicatively independent phase de-aliasing resource},\\
\text{Hankel minimal rank}
&=
\text{determinant certificate 的最小记忆维数},\\
\text{Schur margin}
&=
\text{finite transfer 的 singular-value floor},\\
\text{Rouché strictness}
&=
\text{finite certificate 到真实零点计数的 analytic transport}.
\end{aligned}
}
\tag{C22.1}
$$

所以假想离线零点的最新精确含义是：

$$
\boxed{
\textbf{completed analytic transfer 在一个非零 logarithmic-charge 点产生 kernel，
而任何试图排除它的 finite Schur–Rouché certificate
必在 charge anchor、phase faithfulness、Schur floor、boundary unit、
approximation error 或 dimension budget 中至少一处失效。}
}
\tag{C22.2}
$$

这也进一步校正“信息逃逸”的位置。

信息并不从 canonical prime thread 中逃逸：

- charge 在任一 level 可见；
- phase 可由完整 root tower 或两个 labelled primes 恢复。

信息真正逃逸于：

$$
\boxed{
\text{labelled thread family}
\longrightarrow
\text{commutative scalar completion}
}
\tag{C22.3}
$$

以及：

$$
\boxed{
\text{finite positive operator}
\longrightarrow
\text{没有统一 boundary floor 的无限极限}.
}
\tag{C22.4}
$$

因此下一承重点不应继续增加新的“黄金能量”名称，而应建立以下两个 canonical 对象：

$$
\boxed{
T_N(s)
=
\text{保留 prime labels、power-thread charge、solenoid phase、
Zeckendorf carry 与 Gamma anchor 的 holomorphic finite transfer},
}
\tag{C22.5}
$$

以及：

$$
\boxed{
\mathfrak C_N(R)
=
\frac{
\operatorname{Err}_N(R)
}{
u_N(R)\mu_N(R)^{d_N/2}
}.
}
\tag{C22.6}
$$

其中 $\mathfrak C_N(R)$ 是 dimension-aware Rouché certificate ratio。

最终目标可写成：

$$
\boxed{
\forall R\in\mathfrak R_{\mathbb Q}^{\rm off},
\quad
\exists N,
\quad
\mathfrak C_N(R)<1.
}
\tag{C22.7}
$$

一旦式 (C22.7) 由 canonical prime–Gamma construction 无条件建立，定理 C18.1 便推出 RH。

所以本轮最深的一句话是：

$$
\boxed{
\textbf{RH 可以被重写为：completed prime-thread system 的所有非零 charge 窗口，
都能被某个 Hankel-minimal、Schur-coercive、Rouché-stable 的有限 observer certificate 排除。}
}
\tag{C22.8}
$$

它仍不是证明，但已把“离线相变不可能发生”压缩成一个可数、有限窗口化、带精确误差—维数预算的单一证书纲领。
