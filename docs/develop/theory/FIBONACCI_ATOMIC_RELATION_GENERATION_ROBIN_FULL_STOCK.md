# FIB ATOM：Robin 完整库存与文献接口续卷

**定义 441.0（前置与编号）。** 本卷承接 [FIB ATOM 主卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的全部记号；条目 441–459 的引用在本卷内解释。主卷的价格层、严格库存、自匹配根及黄金组成观察仍为前置。其余同主题续卷的条目以卷名区分，不能仅凭相同编号合并。

## 441. 固定秩 FIB 仿射族不能成为 Musin 高阶接触层

这一节只检验一个容易被“共同几何切面”掩盖的来源条件。令

$$
\mathcal F_r=\{N_{r,g}=1+F_rg:g\ge1\},
$$

其中 $F_r$ 是第 $r$ 个 Fibonacci 数。对 $r\ge3$，有 $F_r>1$，并且

$$
N_{r,g}\equiv1\pmod{F_r},
\qquad \gcd(N_{r,g},F_r)=1.
\tag{441.1}
$$

另一方面，Musin 预印本的 Corollary 3.8 对其固定横坐标的高阶算术族给出：对每个固定正整数 $d$，存在 $k_0(d)$，使得所有阶数 $k\ge k_0(d)$ 的成员都被 $d$ 整除。这里的量词是“该层的每一个成员”，不是只对首个接触点成立；其来源与适用条件见 [Musin 文献卡](../../../Library/Analytic/musin2026higherorder.md)。

### 命题 441.1（固定秩的模障碍）

设 $\mathcal C_k$ 是 Musin Corollary 3.8 所适用的任一固定横坐标高阶算术族。对每个固定 $r\ge3$，存在 $k_0(F_r)$，使得

$$
\boxed{
\mathcal C_k\cap\mathcal F_r=\varnothing
\qquad(k\ge k_0(F_r)).
}\tag{441.2}
$$

**证明。** 取 Corollary 3.8 中的固定整数 $d=F_r$。当 $k\ge k_0(F_r)$ 时，每个 $n\in\mathcal C_k$ 满足 $F_r\mid n$。若同时 $n\in\mathcal F_r$，则式（441.1）给出 $n\equiv1\pmod{F_r}$，与 $F_r\mid n$ 矛盾。故交集为空。证毕。

这个结论排除了一个具体的来源误认：固定 $r$ 的 $1+F_rg$ 仿射窗口，不能在高阶上直接等同于 Musin 的上述接触层，也不能把 Musin 的层级 Robin 保持定理通过“同一个递归几何”这一名称自动运输过来。它没有处理 Musin 的另一类保留全部全局最大值的构造，也没有排除让 $r=r(k)$ 随阶数变化的路线；后者需要一个对变化模数 $F_{r(k)}$ 统一的接触定理，而 Corollary 3.8 的固定 $d$ 量词不提供该 uniformity。

因此，若要把高阶接触方法接回 FIB，必须明确选择以下接口之一：改变 FIB 的同余来源，使其能够承载高阶接触所强制的固定因子；证明随 $r$ 变化的接触族及其统一增长/凹性条件；或放弃接触层识别，直接在同一 $N_{r,g}$ 上建立完整的约数和或有符号显式公式估计。单独复述支撑线、接触嵌套或五窗仿射递归不能填补这个模障碍。本节是 Musin 的已声明整除结论与 FIB 同余恒等式的直接组合，不宣称 RH 或 Robin 全称不等式。
## 442. 变化秩接触路线的固定因子逃逸条件

上一节只取固定的 $r$。变化秩并不能任意绕过同一个模障碍。设

$$
N_k=1+F_{r_k}g_k,\qquad r_k\ge3,\quad g_k\ge1,
$$

并假设 $N_k$ 属于同一个固定横坐标的 Musin 高阶算术族 $\mathcal C_k$，其中
$k\to\infty$。沿用 Corollary 3.8：对每个固定正整数 $d$，存在 $k_0(d)$，使得

$$
d\mid n\qquad(n\in\mathcal C_k,\ k\ge k_0(d)).
$$

### 命题 442.1（变化秩的固定因子逃逸）

对每个固定正整数 $d$，都有

$$
\boxed{
\gcd(d,F_{r_k})=1
\qquad(k\ge k_0(d)).
}
\tag{442.1}
$$

因而，对每个固定素数 $p$，最终有 $p\nmid F_{r_k}$。等价地，若 $z(p)$ 是
$p$ 的 Fibonacci 入口秩，则

$$
z(p)\nmid r_k
$$

对充分大的 $k$ 成立。

**证明。** 固定 $d$，取 $k\ge k_0(d)$。由 $N_k\in\mathcal C_k$，有 $d\mid N_k$。若
$h=\gcd(d,F_{r_k})>1$，则 $h\mid d$ 给出 $h\mid N_k$；另一方面

$$
N_k=1+F_{r_k}g_k\equiv1\pmod h,
$$

矛盾。因此 $h=1$，得到（442.1）。取 $d=p$ 即得素数版本。最后使用 Fibonacci
入口秩的定义与强整除律：$p\mid F_{r_k}$ 当且仅当 $z(p)\mid r_k$。证毕。

### 推论 442.2（秩必须逃离固定值与固定因子）

若上述交点对无穷多个 $k$ 存在，则

$$
\boxed{r_k\longrightarrow\infty,}
\tag{442.2}
$$

并且对每个固定 $s\ge3$，

$$
\boxed{
\gcd(s,r_k)\in\{1,2\}
\qquad\text{最终成立}.
}
\tag{442.3}
$$

特别地，最终 $s\nmid r_k$ 对每个固定 $s\ge3$ 成立；例如秩不能在无穷后段持续含有任何固定的奇因子，也不能持续被 $4$ 整除。

更强地，若 $P^-(m)$ 表示 $m>1$ 的最小素因子，则

$$
\boxed{
P^-(F_{r_k})\longrightarrow\infty.
}
\tag{442.4}
$$

**证明。** 若 $r_k$ 不趋于无穷，则某个固定 $r\ge3$ 在无穷子列上重复；命题 441.1 对该固定 $r$ 给出最终空交，与假设矛盾。对固定 $s\ge3$，将（442.1）取为 $d=F_s$，再用

$$
\gcd(F_s,F_{r_k})=F_{\gcd(s,r_k)}
$$

以及 $F_1=F_2=1$，得到（442.3）。若存在固定 $B$ 使无穷多个 $k$ 满足
$P^-(F_{r_k})\le B$，取不超过 $B$ 的所有素数之积为 $d$，则这些 $k$ 上
$\gcd(d,F_{r_k})>1$，与（442.1）在充分大 $k$ 时矛盾。故（442.4）成立。证毕。

这给变化秩路线一个必要的“素因子逃逸”条件，但它仍不是充分条件：它只保证固定整除障碍最终消失，未保证 $N_k$ 是同一 CA/SA 极值源，也未提供 Musin 所需的接触参数、增长凹性或 Robin 点值传递。允许的候选秩可以是例如没有固定因子重复的变化序列；如何把这类序列与高阶接触的相邻比值和完整约数响应联合起来，仍是未解决接口。不能把（442.1）反向解释成存在这样的接触族，更不能由它推出 RH。

### 推论 442.3（接触成员的不同素因子数发散）

令

$$
P(y)=\prod_{p\le y}p
$$

为实数 $y\ge2$ 的 primorial。对每个固定 $y$，将 Corollary 3.8 的固定整数取为
$d=P(y)$，便有

$$
P(y)\mid N_k
\qquad\text{对充分大的 }k.
$$

于是

$$
\boxed{
\omega(N_k)\ge\pi(y)\quad\text{最终成立，对每个固定 }y,
}
\tag{442.5}
$$

从而 $\omega(N_k)\to\infty$。结合（442.1），充分大时这些固定小素数与
$F_{r_k}$ 互素；它们来自接触层的整除要求，而不是来自 FIB 模数。这个结论没有给出
$\omega(N_k)$ 相对于 $k$ 或 $\log N_k$ 的增长速率，因此只能排除固定
$\omega$ 的筛选路线，不能替代高阶接触所需的 Robin 点值估计。

### 推论 442.4（固定素数方向的 profinite 逃逸）

对任意固定素数 $p$ 和任意固定整数 $A\ge1$，将 Corollary 3.8 的固定整数取为
$d=p^A$，得到

$$
p^A\mid N_k
\qquad\text{对充分大的 }k.
$$

因此

$$
\boxed{
v_p(N_k)\longrightarrow\infty
\qquad\text{对每个固定素数 }p.
}
\tag{442.6}
$$

更一般地，$N_k\to0$ 按有限模数坐标收敛：每个固定 $Q\ge1$ 最终整除
$N_k$。结合（442.1），对每个固定 $Q$ 还同时有

$$
\gcd(Q,F_{r_k})=1
\qquad\text{最终成立},
$$

所以接触族的固定整除要求与 FIB 同余只能通过逐阶变化、且最终互素的
Chinese-remainder 接口共同实现。这个结论没有给出 $v_p(N_k)$ 的增长速率；
它只说明任何固定的 $p$-进安全界（例如固定的 $v_2$ 截断）至多排除有限个接触阶，
不能单独完成 Robin 的全称估计。

## 443. 接触链对变化秩的相邻模约束

现在再加入 Musin Corollary 3.10 在其凹性假设下给出的首接触整除链。设

$$
m_k=N_k=1+F_{r_k}g_k,\qquad
m_k\mid m_{k+1},
$$

并置

$$
R_k=\frac{m_{k+1}}{m_k},
\qquad
h_k=\gcd(r_k,r_{k+1}).
$$

### 命题 443.1（相邻接触比值的 Fibonacci 同余）

在上述条件下，

$$
\boxed{
F_{h_k}\mid R_k-1.
}
\tag{443.1}
$$

**证明。** 强整除律给

$$
F_{h_k}=\gcd(F_{r_k},F_{r_{k+1}}).
$$

由两个仿射表示，

$$
m_k\equiv1\pmod{F_{h_k}},
\qquad
m_{k+1}\equiv1\pmod{F_{h_k}}.
$$

另一方面 $m_{k+1}=R_km_k$，而 $m_k\equiv1$，所以

$$
1\equiv m_{k+1}=R_km_k\equiv R_k\pmod{F_{h_k}},
$$

即得（443.1）。证毕。

### 推论 443.2（非平凡相邻模只能来自变化的公共秩）

若 $h_k\ge3$，则

$$
R_k\ge F_{h_k}+1.
$$

在命题 442.1 的接触假设下，每个固定 $s\ge3$ 只能有有限多个 $k$ 满足
$h_k=s$，因为 $h_k=s$ 会使 $s\mid r_k$。因此，若想从（443.1）得到无穷多个非平凡的固定 Fibonacci 模约束，公共秩 $h_k$ 必须本身无界变化；若 $(h_k)$ 有界，则最终 $h_k\in\{1,2\}$，而 $F_{h_k}=1$，式（443.1）退化为无信息的整除式。

这个结果提供了一个可检验的接口：Musin 的相邻比值增长结论与 FIB 来源若要共同实现，必须同时满足（442.1）的固定因子逃逸和（443.1）的相邻模约束。它没有给出 $R_k$ 的上界，也没有把 Musin 的 $\omega(R_k)$ 增长转化成 Robin 点值估计；因此仍不能推出接触族存在、Robin 不等式或 RH。

## 444. Musin 相邻商的指数素因子增长排除有界复杂度 FIB 链

上一节只使用了整除链的模约束。Musin 预印本 Theorem 3.12 对其
$0<\alpha\le1$ 的固定横坐标接触族还给出更强的相邻商读数。令
$m_k$ 为该族第 $k$ 层的首接触，$R_k=m_{k+1}/m_k$，并令
$\omega$ 表示不同素因子的个数。其结论是

$$
\limsup_{k\to\infty}\frac{\log(1+\omega(R_k))}{k}=\frac1\alpha.
\tag{444.1}
$$

这里沿用文献卡的量词和接触族；该结论属于 Musin 的来源，不是本节重新证明的
FIB 定理。

### 推论 444.1（同一 FIB 链上的指数级对数商下界）

假设 Musin 的首接触链同时具有上一节的 FIB 形式

$$
m_k=1+F_{r_k}g_k,\qquad g_k\ge1,
$$

以及 $m_k\mid m_{k+1}$。对任意 $0<\varepsilon<1/\alpha$，存在无穷多个
$k$ 使得

$$
\omega(R_k)\ge
\exp\!\bigl((1/\alpha-\varepsilon)k\bigr)-1,
$$

从而

$$
\boxed{
\log R_k\ge(\log2)\left[
\exp\!\bigl((1/\alpha-\varepsilon)k\bigr)-1
\right].
}
\tag{444.2}
$$

**证明。** 由（444.1）的上极限定义，在无穷多个 $k$ 上有
$$
\log(1+\omega(R_k))\ge(1/\alpha-\varepsilon)k.
$$
因此得到第一式。若 $R_k$ 有 $t$ 个不同素因子，则每个素因子的指数至少为
$1$，故 $R_k\ge2^t$；取对数即得（444.2）。证毕。

这给出一个此前未写出的 FIB 兼容性检验。任何额外满足

$$
\log(m_{k+1}/m_k)=O(k)
\tag{444.3}
$$

的候选递归链，都不可能是这个 Musin 接触族的同一实际来源：式（444.2）在同一
无穷子列上是指数级的，而（444.3）只有线性级；等价地，$R_k$ 本身在该子列上至少是
双指数级。更一般地，任何给出
$\log R_k=\exp(o(k))$ 的有界复杂度模型也会被排除。这个结论只使用 Musin 的
相邻商定理和整数的基本素因子界，没有把 FIB 地址误当成接触坐标。

### 推论 444.2（秩模约束的量化二择一）

若再令 $h_k=\gcd(r_k,r_{k+1})$，则上一节给出

$$
F_{h_k}\mid R_k-1.
$$

于是 $h_k\ge3$ 时，$F_{h_k}\le R_k-1$，并由
$F_h\ge\varphi^{h-2}$（$h\ge2$）得到

$$
\boxed{
h_k\le2+\log_\varphi R_k.
}
\tag{444.4}
$$

因此一个声称的 FIB—接触实现必须落入两种情形之一：

1. $h_k\in\{1,2\}$ 在无穷后段成立，此时（443.1）退化为模 $1$，FIB
   结构对相邻商没有提供非平凡约束；或
2. $h_k\ge3$ 在无穷子列出现，此时相邻商必须同时满足
   $R_k\equiv1\pmod{F_{h_k}}$ 和（444.2）的指数级对数下界。

式（444.4）是上界而不是反向下界；不能从 Musin 的大
$\omega(R_k)$ 直接推出 $h_k\to\infty$。因此本节排除的是有界复杂度的 FIB 接触模型，
不是变化秩接触族本身。它也没有提供 Robin 点值的有符号估计、同一 CA/SA 极值源的
识别、接触族存在性或 RH 证明。

## 445. 严格 Euler 库存与 Fibonacci 索引的条件相容性

上一节的接触链与 Euler 库存是两条不同的来源假设。
[严格库存前向窗口](../../../Blueprint/D5/S3/Arith/Robin/EulerLayerPhaseSeparation.md)
给出正整数 $U$ 的分层整除结论，而 Fibonacci 入口秩性质给出

$$
q\mid F_m\quad\Longleftrightarrow\quad z(q)\mid m,
$$

其中 $q$ 为素数、$z(q)$ 是它的最小正 Fibonacci 零指标。把两者放在同一个
$U=F_m$ 假设下，可以得到一个新的接口，但不能把它误读成无条件的 FIB 来源定理。

### 命题 445.1（高阶库存给出 Fibonacci rank 分整除）

令 $t\ge243$，$B=t+t^{4/5}$，并假设 $U=F_m>0$ 满足严格库存律。若 $q$ 为素数、
$k\ge2$ 且

$$
t<q^k\le B,
$$

则

$$
q^k\mid U,
\qquad q\mid F_m,
\qquad z(q)\mid m.
\tag{445.1}
$$

若 $q$ 为素数且

$$
t<q\le B,
$$

则

$$
q\nmid F_m,
\qquad z(q)\nmid m.
\tag{445.2}
$$

**证明。** 第一组结论直接取严格库存定理的高阶分支；由 $q^k\mid U=F_m$
得到 $q\mid F_m$，再用 Fibonacci 入口等价得到 $z(q)\mid m$。第二组由库存定理的
首层分支给 $U$ 在 $q$ 处的赋值为零，因此 $q\nmid U=F_m$，再用同一入口等价的逆向得到
$z(q)\nmid m$。这里的论证只运输同一个 $U$；没有把不同候选整数的局部极值拼在一起。
$\square$

### 命题 445.2（两个窗口严格分离）

在命题 445.1 的范围内，高阶素幂窗口与首层素数窗口不会使用同一个素数。事实上，

$$
t<q^k\le B, k\ge2
\quad\Longrightarrow\quad
q\le\sqrt B\le\sqrt{4t/3}<t,
\tag{445.3}
$$

而 $t<q$ 时

$$
q^k\ge q^2>t^2>B.
\tag{445.4}
$$

因此（445.1）与（445.2）并不构成同一个 $q$ 的“既占用又缺失”矛盾；Euler
分离定理正是把它们安排在两个不同的素数尺度上。

对高阶窗口中的全部素数置

$$
\mathcal Q_t=\{q:\ q\text{ prime},\ \exists k\ge2,\ t<q^k\le B\},
$$

则在 $U=F_m$ 的附加假设下还有整除账本

$$
\operatorname{lcm}_{q\in\mathcal Q_t}z(q)\mid m.
\tag{445.5}
$$

这份账本是一个可检验的 FIB—Robin 接口：它把 Euler 的实际库存转成 Fibonacci
索引的共同约束，同时保留首层窗口的非整除约束。当前没有已支付的统一下界说明
（445.5）会超过候选索引 $m$，也没有证明严格库存整数 $U$ 必须是 Fibonacci 数。
所以它不能识别 CA/SA 来源，也不能给出 Robin 点值符号或 RH；真正未解决的是把
实际候选的来源条件 $U=F_m$（或其仿射替代）与完整约数响应放到同一个可估计的联合
模型中。

本节是对两个既有接口的条件性组合，不重述其 Euler 价格估计、库存证明或
Fibonacci 强整除证明；若删除任一来源假设，445.1--445.5 不再成立。

## 446. 高阶库存对 Fibonacci 指数的 Wall--Sun--Sun 二择一

§445 只使用了高阶库存的素因子结论 $q\mid F_m$。但在平方层上，库存给出
$q^2\mid F_m$，所以还可以调用已有的 Fibonacci $q$-进赋值公式。这个接口
把严格 Euler 库存的短区间约束，转成 Fibonacci 索引本身的乘法约束；它仍然是
在附加 $U=F_m$ 假设下的条件结论。

固定

$$
 B=t+t^{4/5},\qquad
 \mathcal I_t=\{q:\ q\text{ 为素数},\ t<q^2\le B\}.
$$

当 $t\ge243$ 时，$\mathcal I_t$ 中的素数都大于 $5$。对每个这样的 $q$，
记 $z(q)$ 为首次 Fibonacci 零指标，并记

$$
 e_q=v_q(F_{z(q)}).
$$

定义高首次深度集合

$$
 \mathcal W_t=\{q\in\mathcal I_t:e_q\ge2\},\qquad
 P_t=\prod_{q\in\mathcal I_t\setminus\mathcal W_t}q,
$$

空积取 $1$。

### 命题 446.1（平方库存的指数二择一）

令 $U=F_m>0$ 满足命题 445.1 的严格库存律。则

$$
 \boxed{P_t\mid m.}
 \tag{446.1}
$$

从而有精确的对数账本

$$
 \boxed{
 \log m\ge
 \sum_{q\in\mathcal I_t\setminus\mathcal W_t}\log q
 =\theta(\sqrt B)-\theta(\sqrt t)
  -\sum_{q\in\mathcal W_t}\log q .
 }
 \tag{446.2}
$$

这里 $\theta(x)=\sum_{q\le x}\log q$；端点可取任一与
$t<q^2\le B$ 一致的整数约定。

**证明。** 对 $q\in\mathcal I_t$，取 $k=2$ 应用严格库存，得到

$$
 q^2\mid U=F_m.
$$

特别地 $q\mid F_m$，由 Fibonacci 入口判据得 $z(q)\mid m$。已有的
Fibonacci 赋值提升公式给出

$$
 v_q(F_m)=e_q+v_q\!\left(m/z(q)\right)
 \qquad(z(q)\mid m).
$$

又有秩界 $z(q)\mid q-(5/q)$ 或 $z(q)\mid q+(5/q)$，故
$q\nmid z(q)$。若 $q\notin\mathcal W_t$，则 $e_q=1$；而
$q^2\mid F_m$ 要求右端至少为 $2$，于是
$q\mid m/z(q)$，进而 $q\mid m$。不同 $q$ 互异，故其乘积 $P_t\mid m$。

最后，$\mathcal I_t$ 正好是素数区间
$(\sqrt t,\sqrt B]$，对数求和给出（446.2）。$\square$

### 推论 446.2（短区间的 WSS 质量或指数膨胀）

由素数定理，沿 $t\to\infty$，

$$
 \theta(\sqrt B)-\theta(\sqrt t)
 =\left(\frac12+o(1)\right)t^{3/10}.
 \tag{446.3}
$$

因此命题 446.1 给出以下互补结论：

$$
 \boxed{
 \log m=o(t^{3/10})\ \Longrightarrow\
 \sum_{q\in\mathcal W_t}\log q
 \ge\left(\frac12-o(1)\right)t^{3/10}.
 }
 \tag{446.4}
$$

以及

$$
 \boxed{
 \sum_{q\in\mathcal W_t}\log q=o(t^{3/10})\ \Longrightarrow\
 m\ge\exp\!\left(\left(\frac12-o(1)\right)t^{3/10}\right).
 }
 \tag{446.5}
$$

特别地，若该短区间没有 $e_q\ge2$ 的素数，便直接得到（446.5）。这里
$e_q\ge2$ 正是 Fibonacci 版本的高首次赋值（通常称为
Wall--Sun--Sun 型）条件；其开放背景和赋值约定见
[Fibonacci 非 Wieferich 素数条目](../../../Library/ArithUnits/li2026nonwieferich.md)；
本节不假设这类素数不存在，也不把该开放问题改写成已知定理。

**证明。** 将（446.3）代入（446.2）即可得到（446.4）；移项并取指数得到
（446.5）。$\square$

这个二择一比（445.5）的秩最小公倍数账本更强：它使用了平方库存的第二层，
直接迫使非高首次深度的素数进入同一个索引 $m$。但它仍不能单独完成
Robin 估计。要把它接回实际来源，至少还需二者之一：

1. 从严格库存或来源最大性证明一个索引尺度，例如
   $m\le t^A$（固定 $A$），使（446.4）迫使短区间承载几乎全部
   $t^{3/10}/2$ 的高首次深度素数质量；或
2. 在这些平方层上取得 $\mathcal W_t$ 的独立上界，足以使（446.5) 与来源
   给出的 $m$ 尺度冲突。

下面的命题 446.3 在同一个附加 $U=F_m$ 假设下给出所需索引尺度；
定理 447.2 随后排除充分大时的这一精确来源。这里的条件性赋值二择一不推出
一般仿射来源的 Robin 不等式或 RH。

### 命题 446.3（严格库存自身给出多项式索引尺度）

在命题 446.1 的附加假设 $U=F_m$ 下，严格库存还会自动限制 $m$ 的增长。
存在绝对常数 $C>0$，使所有充分大的 $t$ 都有

$$
 \boxed{m\le C\,t\log t.}
 \tag{446.6}
$$

所以沿任意 $t\to\infty$ 的此类 FIB 库存序列，

$$
 \log m=o(t^{3/10}),
$$

命题 446.1 的二择一必然退化为

$$
 \boxed{
 \sum_{q\in\mathcal W_t}\log q
 \ge\left(\frac12-o(1)\right)t^{3/10}.
 }
 \tag{446.7}
$$

**证明。** 严格库存中每个实际选取的层 $(q,k)$ 都满足

$$
 \frac{\log(1+1/(q+\cdots+q^k))}{\log q}
 >\frac1{t\log t}.
$$

因 $q+\cdots+q^k\ge q^k$ 且 $\log(1+u)<u$，得到

$$
 q^k\log q<t\log t.
 \tag{446.8}
$$

置 $X_t=t\log t/\log2$。把 $U$ 的每一层赋值写成其实际素数幂层的
不重复求和，式（446.8）给

$$
 \log U
 =\sum_{\text{实际选取的 }(q,k)}\log q
 \le\sum_{q^k\le X_t}\log q
 =\psi(X_t).
 \tag{446.9}
$$

Chebyshev 的标准上界 $\psi(x)\le C_\psi x$ 给
$\log U\le(C_\psi/\log2)t\log t$。对 $m\ge2$，
$F_m\ge\varphi^{m-2}$；而 $m=1$ 时 $F_m=1$，不可能承载
$q^2\mid U$ 的窗口层。因此 $m\le2+C t\log t$，吸收常数后得（446.6）。
再将 $\log m=O(\log t)$ 代入（446.4)，得到（446.7）。$\square$

命题 446.3 把缺口定位得更窄：若希望把严格 Euler 库存的核心无条件识别为
Fibonacci 数，必须解释一个长度约 $t^{3/10}$ 的平方层短区间中，几乎全部
素数的首次 Fibonacci 赋值为何同时至少为二；或者证明该识别在高 $t$ 时根本
不可能。Wall--Sun--Sun 的逐素数赋值条件
没有给出这里所需的短区间加权上界。因此（446.7）仍是条件性来源障碍，不是
Robin/RH 的反例，也不是对 WSS 开放问题的解决。

### 命题 446.4（全部库存层的 Fibonacci 索引影子）

把严格库存的实际层数记为

$$
 a_q(t)=v_q(U)
 =\#\left\{k\ge1:r_{q,k}>\frac1{t\log t}\right\}.
$$

若 $U=F_m>0$，则对每个素数 $q\ge7$ 都有以下精确三分：

$$
 \boxed{
 \begin{array}{ll}
 a_q(t)=0 &\Longrightarrow\ q\nmid F_m,\ z(q)\nmid m,\\[2mm]
 a_q(t)>0,\ e_q>a_q(t)&\Longrightarrow\ \text{不存在这样的 }U=F_m,\\[2mm]
 a_q(t)>0,\ e_q\le a_q(t)&\Longrightarrow\
 v_q(m)=a_q(t)-e_q.
 \end{array}
 }
 \tag{446.10}
$$

特别地，定义

$$
 M_{\rm sh}(t)=
 \prod_{\substack{q\ge7\\a_q(t)>0}}
 q^{\,a_q(t)-e_q}
 \quad\text{（仅在所有指数非负时定义）},
$$

则任何满足条件的 Fibonacci 库存都满足

$$
 \boxed{M_{\rm sh}(t)\mid m.}
 \tag{446.11}
$$

**证明。** 若 $a_q(t)=0$，严格库存给 $q\nmid U=F_m$，再用入口秩判据
得到 $z(q)\nmid m$。若 $a_q(t)>0$，则 $q\mid F_m$，所以 $z(q)\mid m$。
对 $q\ge7$，已有赋值提升公式给

$$
 v_q(F_m)=e_q+v_q\!\left(m/z(q)\right).
$$

秩界 $z(q)\mid q\pm1$ 保证 $q\nmid z(q)$，故
$v_q(m/z(q))=v_q(m)$。但严格库存又给
$v_q(F_m)=a_q(t)$。若 $e_q>a_q(t)$，两式矛盾；否则相减得到
$v_q(m)=a_q(t)-e_q$。对所有 $q\ge7$ 取乘积即得（446.11）。$\square$

命题 446.4 把 §445 的“秩整除账本”升级为逐素数赋值账本。它同时记录：

$$
\text{首层缺失}\ \Longleftrightarrow\ z(q)\nmid m,
\qquad
\text{已占用层}\ \Longleftrightarrow\
v_q(m)=a_q(t)-e_q.
$$

因此，未来若能从 Fibonacci 赋值理论或独立的 WSS 结果给出
$e_q$ 的上界，便可直接估计 $M_{\rm sh}(t)$，无需重新分析 Euler
约数和。当前没有这样的统一上界；命题 446.4 仍是联合必要条件，不改变
Robin/RH 的开放状态。

## 447. 严格 Euler 库存最终不可能恰为 Fibonacci 数

§445--§446 都把 $U=F_m$ 作为附加来源假设。本节给出一个更早的排除：
在高尺度上，严格 Euler 库存的素数支撑已经被 Euler 边际价格截在
$t$ 以下，而 Fibonacci 数的本原素因子会把支撑推到其指标附近。因此，
该附加假设不可能沿无穷高的 $t$ 序列成立。这个结论不使用 WSS 密度，
也不改变严格库存本身的 Robin 估计。

沿用 §111.2 的严格库存

$$
N^-(t)=\prod_p p^{a_p(t)},\qquad
a_p(t)=\#\{k\ge1:r_{p,k}>\lambda(t)\},\qquad
\lambda(t)=\frac1{t\log t},
$$

并令 $P^+(n)$ 表示正整数 $n>1$ 的最大素因子。

### 命题 447.1（支撑截止）

对 $t\ge243$，$N^-(t)$ 的每个素因子都严格小于 $t$；若
$N^-(t)>1$，则

$$
\boxed{P^+(N^-(t))<t.}
\tag{447.1}
$$

**证明。** 对每个素数 $p$，首层边际价格满足

$$
r_{p,1}
=\frac{\log(1+1/p)}{\log p}
<\frac1{p\log p}.
$$

当 $p\ge t$ 时，$x\mapsto x\log x$ 在 $[243,\infty)$ 上严格递增，故

$$
r_{p,1}<\frac1{p\log p}
\le\frac1{t\log t}=\lambda(t).
$$

同一素数的后续边际价格严格小于首层价格，所以 $a_p(t)=0$。因此
$N^-(t)$ 不含任何 $p\ge t$，得到命题及（447.1）。$\square$

### 定理 447.2（Fibonacci 来源的最终排除）

存在 $T\ge243$，使得对所有 $t\ge T$，严格库存都不可能是 Fibonacci 数：

$$
\boxed{
\forall t\ge T\ \forall m\ge1,\qquad N^-(t)\ne F_m.
}
\tag{447.2}
$$

**证明。** 反设存在趋于无穷的 $t$ 以及 $m$ 使
$N^-(t)=F_m$。§111.2 已给出的尺度式为

$$
\log N^-(t)
=\psi(t)+(\sqrt2-1)\sqrt t+o(\sqrt t)
=t+o(t).
\tag{447.3}
$$

另一方面，Binet 公式给出

$$
\log F_m=m\log\varphi-\tfrac12\log5+o(1),
\qquad
\frac mt\longrightarrow\frac1{\log\varphi}>1.
\tag{447.4}
$$

故充分大时 $m>t+1$，且特别有 $m>12$。Carmichael 的 Fibonacci
本原素因子定理（Yabuta, *Fibonacci Quarterly* 39(5),
Theorem 3）给出一个素数 $p\mid F_m$，它不整除任何较早的正 Fibonacci
项。于是其首次零秩满足 $z(p)=m$。该 $p$ 不可能是 $2,3,5$，因为这三个
素数已经分别出现在更早的 $F_3,F_4,F_5$ 中；所以可以使用经典 Fibonacci 秩界

$$
z(p)\mid p-\left(\frac5p\right),
$$

其中 Legendre 符号为 $\pm1$。因此 $m=z(p)\le p+1$，从而

$$
p\ge m-1>t.
$$

但 $p\mid F_m=N^-(t)$ 与命题 447.1 冲突，因为（447.1）要求每个库存素因子
严格小于 $t$。矛盾证明（447.2）。$\square$

这个排除只针对精确来源 $U=F_m$。它不排除仿射或乘积型来源，例如
$U=1+F_r g$，也不说明这些来源满足 Robin 不等式。它的作用是把 §445--§446
的下一步从“继续加强 $U=F_m$ 的必要条件”移到真正尚未覆盖的来源保持问题：
需要给出一个仍保留完整素数幂赋值、同时能与 FIB 地址相容的仿射或乘积构造，
再对其 $Z(U)=\sigma(U)/U$ 作统一估计。因而（447.2）是来源识别的反例，
不是 Robin 不等式或 RH 的证明，也不重复 §445 的秩账本或 §446 的 WSS 二择一。

## 448. 严格 Euler 库存也不可能属于有限 Fibonacci 最小公倍数族

§447 排除了精确单项来源 $N^-(t)=F_m$。本节把排除扩大到
§365 定义的完整有限 Fibonacci 最小公倍数族

$$
\mathcal M=\left\{\operatorname{lcm}_{s\in S}F_s:
S\subseteq\mathbb N_{>0}\text{ 有限}\right\}.
$$

新增的约束来自同一个严格库存的二进赋值，而不是重新使用平方层 WSS
账本。

### 引理 448.1（二进库存赋值的增长）

存在 $T_0\ge243$，使得对所有 $t\ge T_0$，若
$a_2(t)=v_2(N^-(t))$，则

$$
\boxed{
3\cdot2^{a_2(t)-2}>t+1.
}
\tag{448.1}
$$

**证明。** 对 $k\ge1$，置
$G_2(k)=\sum_{j=0}^{k}2^{-j}$。因为 $G_2(k-1)<2$，有

$$
\frac{G_2(k)}{G_2(k-1)}
=1+\frac{2^{-k}}{G_2(k-1)}
>1+2^{-k-1}.
$$

对 $0<x\le1/4$，$\log(1+x)\ge x/(1+x)>x/2$，故

$$
r_{2,k}
=\frac{\log(G_2(k)/G_2(k-1))}{\log2}
>\frac{2^{-k-2}}{\log2}.
\tag{448.2}
$$

令
\[
L_t=\log_2\!\left(\frac{t\log t}{\log2}\right),
\qquad
k_t=\lfloor L_t\rfloor-2.
\]
充分大时 $k_t\ge1$，并且
$2^{k_t+2}\le t\log t/\log2$。由（448.2），
$r_{2,k_t}>\lambda(t)$；边际价格随 $k$ 严格下降，所以
$a_2(t)\ge k_t$。于是

$$
3\cdot2^{a_2(t)-2}
\ge3\cdot2^{\lfloor L_t\rfloor-4}
>\frac{3t\log t}{32\log2}.
$$

最后取 $T_0$ 足够大，使右侧大于 $t+1$，即得（448.1）。$\square$

### 定理 448.2（Fibonacci lcm 来源的最终排除）

存在 $T\ge T_0$，使得对所有 $t\ge T$，

$$
\boxed{
N^-(t)\notin\mathcal M.
}
\tag{448.3}
$$

**证明。** 反设 $N^-(t)=M(S)$ 且 $t\ge T$，其中 $S$ 为有限正指标集合。
由引理 448.1，$a_2(t)>2$。最小公倍数的赋值取最大值，所以存在
$s\in S$ 满足

$$
v_2(F_s)=v_2(M(S))=a_2(t).
$$

主卷 §95 的精确 Fibonacci 二进赋值公式为

$$
v_2(F_s)=
\begin{cases}
0,&3\nmid s,\\
1,&s\equiv3\pmod6,\\
v_2(s)+2,&6\mid s.
\end{cases}
\tag{448.4}
$$

因此 $6\mid s$，且 $s\ge3\cdot2^{a_2(t)-2}>t+1$。

再取 Carmichael 本原素因子定理给出的素数 $p\mid F_s$。
因为 $s>12$，可取 $p$ 不整除任何更早的 Fibonacci 项；于是
$z(p)=s$。该素数不属于 $2,3,5$，并满足经典 Fibonacci 秩界

$$
s=z(p)\mid p-\left(\frac5p\right),
$$

故 $p\ge s-1>t$。但 $p\mid F_s\mid M(S)=N^-(t)$，这与命题
447.1 的库存支撑截止矛盾。故（448.3）成立。$\square$

这个结论把严格 Euler 库存同时排除在单项 Fibonacci 来源和有限 Fibonacci
lcm 来源之外。它仍不排除一般仿射来源 $1+F_rg$、乘积来源或其它保留完整
素数幂赋值的 FIB 构造；也不提供这些来源的 Robin 点值上界。因此，下一条真正
未覆盖的桥仍是把仿射/乘积 FIB 地址与同一 CA/SA 价格源连接起来，而不是继续
加强已经被（447.2）和（448.3）排除的 Fibonacci lcm 识别。

## 450. 严格库存对一般仿射秩的素因子下界

对于一般仿射来源 $N_g=1+F_rg$，严格库存的全部首层赋值限制 $F_r$ 本身。它不重复（447.1）的库存支撑上界：
（447.1）说库存中不能出现 $p\ge t$，本节反过来说明库存必然包含所有
$p\le t-1$；当 $t$ 为整数时，这就是所有 $p<t$。

### 命题 450.1（库存与仿射模数的粗糙性）

令 $t\ge4$，并沿用

$$
\lambda(t)=\frac1{t\log t},\qquad
N^-(t)=\prod_p p^{a_p(t)},\qquad
a_p(t)=\#\{k\ge1:r_{p,k}>\lambda(t)\}.
$$

若 $r\ge3$、$g\ge1$，且

$$
N^-(t)=1+F_rg,
$$

则

$$
\boxed{P^-(F_r)>t-1.}
\tag{450.1}
$$

其中 $P^-(m)$ 表示 $m>1$ 的最小素因子。

**证明。** 对任意素数 $p\le t-1$，有

$$
\log(1+1/p)>\frac1{p+1}.
$$

又因 $t\ge3$，

$$
(p+1)\log p
\le t\log p
<t\log t.
$$

所以

$$
r_{p,1}
=\frac{\log(1+1/p)}{\log p}
>\frac1{(p+1)\log p}
>\frac1{t\log t}=\lambda(t),
$$

从而 $a_p(t)\ge1$，即 $p\mid N^-(t)$。另一方面，仿射表示给出

$$
N^-(t)\equiv1\pmod{F_r},
$$

故 $\gcd(N^-(t),F_r)=1$。因此 $F_r$ 不可能含有任何 $p\le t-1$，
得到（450.1）。
$\square$

### 推论 450.2（固定秩仿射来源只有有限库存高度）

在命题 450.1 的条件下，对固定 $r\ge3$，有

$$
\boxed{
t<P^-(F_r)+1\le F_r+1.
}
\tag{450.2}
$$

因此固定 $r$ 的族 $1+F_rg$ 不可能在严格 Euler 库存中出现于无界的
$t$ 高度。由于 $N^-(x)$ 随 $x$ 按整除序单调不减，更精确地，若
$N^-(t)=1+F_rg$，则

$$
g=\frac{N^-(t)-1}{F_r}
\le\frac{N^-(P^-(F_r)+1)-1}{F_r}.
\tag{450.3}
$$

**证明。** 由（450.1）立即得（450.2）。若 $x\le y$，则
$\lambda(x)\ge\lambda(y)$，所以严格有益层在 $x$ 时是 $y$ 时的子集，
从而 $N^-(x)\mid N^-(y)$ 且 $N^-(x)\le N^-(y)$。将
$t<P^-(F_r)+1$ 代入此单调性，再用 $N^-(t)=1+F_rg$，得到（450.3）。
$\square$

### 推论 450.3（变化秩路线的必要条件）

若存在 $t_j\to\infty$、$r_j\ge3$、$g_j\ge1$ 使

$$
N^-(t_j)=1+F_{r_j}g_j,
$$

则

$$
\boxed{
 P^-(F_{r_j})>t_j-1\longrightarrow\infty,
}
\tag{450.4}
$$

并且 $r_j\to\infty$。所以一般仿射来源若要承载无界严格库存，必须使用
最小素因子同时逃逸的变化 Fibonacci 秩；固定秩和仅仅增大乘子 $g$ 的路线
已经被（450.2）排除。

这个结论仍不是 Robin 不等式：它只约束来源的可实现性，没有识别
$N^-(t)$ 为 CA/SA，也没有控制 $Z(N_g)=\sigma(N_g)/N_g$ 的点值尾项。
它把下一步压缩为一个明确的联合问题：是否存在满足（450.4）的变化秩，
同时保留 FIB 接缝、完整库存赋值和同一 CA 价格源。


### 推论 450.4（变化秩的强整除粗糙性）

定义

$$
D(t)=\max\{d\ge3:F_d\le t-1\}.
$$

则命题 450.1 的条件还蕴含

$$
\boxed{
d\mid r,\quad 3\le d\le D(t)
\quad\Longrightarrow\quad\text{矛盾}.
}
\tag{450.5}
$$

特别地，对 $t\ge4$，有

$$
\boxed{
4\nmid r,\qquad
q\mid r,\ q\text{ 为奇素数}
\quad\Longrightarrow\quad
q>D(t).
}
\tag{450.6}
$$

并且由 Binet 公式

$$
D(t)=\log_\varphi t+O(1).
\tag{450.7}
$$

**证明。** 若 $d\mid r$，强整除律给 $F_d\mid F_r$。当
$3\le d\le D(t)$ 时，$F_d\le t-1$，故 $F_d$ 的任一素因子
$p$ 满足 $p\le t-1$；但 $p\mid F_r$ 与（450.1）矛盾。这证明（450.5）。
取 $d=4$ 得 $4\nmid r$；取 $d=q$ 得（450.6）。最后由
$F_d=\varphi^d/\sqrt5+O(\varphi^{-d})$ 得（450.7）。$\square$

这把无界仿射来源的秩压到
$r=2^\varepsilon m$（$\varepsilon\in\{0,1\}$）且 $m$ 的所有奇素因子
大于 $D(t)$ 的候选集合。候选集合仍然无穷，因而（450.5）--（450.7）
不能单独推出 Robin 不等式；它们提供的是把完整库存赋值继续反推到 FIB
地址的联合筛选。

### 推论 450.5（仿射秩的库存尺度上界）

在命题 450.1 的条件下，存在绝对常数 $C>0$，使充分大的 $t$ 满足

$$
\boxed{
r\le C\,t\log t.
}
\tag{450.8}
$$

因此变化秩路线同时受到

$$
r>D(t)=\log_\varphi t+O(1),
\qquad r\le C\,t\log t,
$$

以及（450.6）的素因子粗糙性约束。

**证明。** 沿用命题 446.3 的库存层计数。若 $a_p(t)$ 的第 $k$ 层被选中，
则

$$
\frac{\log(1+1/(p+\cdots+p^k))}{\log p}>\frac1{t\log t}
$$

与 $\log(1+u)<u$ 给出

$$
p^k\log p<t\log t.
$$

置 $X=t\log t/\log2$。把库存的每个实际素数幂层按其素数计重，得到

$$
\log N^-(t)\le\sum_{p^k\le X}\log p=\psi(X)\le C_0t\log t,
$$

其中最后一步是 Chebyshev 上界。由 $g\ge1$ 及
$N^-(t)=1+F_rg$，有 $F_r<N^-(t)$；又
$F_r\ge\varphi^{r-2}$（$r\ge2$），故

$$
(r-2)\log\varphi\le C_0t\log t.
$$

增大常数即得（450.8）。下界由 $D(t)$ 的定义及
$D(t)=\log_\varphi t+O(1)$ 给出。$\square$

这个上界只限制地址秩的规模；它没有把仿射族识别为 CA/SA，也没有给出
$Z(1+F_rg)$ 相对于 Robin 预算的有符号尾项。因此它是对（450.5）--（450.7）
候选筛的尺度补充，不是 Robin 不等式或 RH 的证明。

### 推论 450.6（严格自匹配根上的线性秩界）

再假设 $t$ 是第 111 节的严格自匹配根，即

$$
\log N^-(t)=t,
\qquad N^-(t)=1+F_rg.
$$

则

$$
\boxed{
D(t)<r<2+\frac{t}{\log\varphi},
\qquad
g<\frac{e^t}{\varphi^{r-2}}.
}
\tag{450.9}
$$

**证明。** 左侧仍由（450.5）及 $r\ge3$ 给出：若 $r\le D(t)$，取
$d=r$ 即矛盾。右侧使用

$$
\varphi^{r-2}\le F_r<N^-(t)=e^t,
$$

其中最后一个严格不等式来自 $g\ge1$ 与
$N^-(t)=1+F_rg$。这给出
$r<2+t/\log\varphi$。再由
$g=(e^t-1)/F_r$ 和 $F_r\ge\varphi^{r-2}$ 得第二个不等式。
$\square$

所以若仿射来源真的落在 Robin 裕量的严格自匹配谷底，它的秩只能位于

$$
D(t)<r<2+t/\log\varphi,
\qquad D(t)=\log_\varphi t+O(1),
$$

同时满足（450.6）的素因子粗糙性。这个临界根特化仍没有证明
$\gamma+\log\log N^-(t)-\log Z(N^-(t))>0$；缺失的仍是同一配置上的有符号价格尾项。

### 命题 450.7（秩筛本身的非完备性）

对充分大的整数 $t$，存在素数秩 $r$ 同时满足

$$
\boxed{
\frac t2<r<t,
\qquad
P^-(F_r)>t-1,
\qquad
r>D(t),
\qquad
r<2+\frac t{\log\varphi}.
}
\tag{450.10}
$$

因此（450.1）、（450.5）--（450.9）的秩与素因子必要条件，单独不能排除
无穷多个潜在仿射临界秩；它们必须与完整库存同余或 Robin 价格信息联合使用。

**证明。** 对充分大的 $t$，由 Bertrand 定理可取素数
$t/2<r<t$，并且 $r>5$。若 $p\mid F_r$，则入口秩满足
$z(p)\mid r$。因为 $r$ 是素数、$z(p)\ge3$，只能有
$z(p)=r$；素数 $2,5$ 的入口秩分别为 $3,5$，也不出现在
$F_r$ 中。经典秩界

$$
r\mid p-\left(\frac5p\right)
$$

再结合 $p$ 与 $r$ 的奇性，给出 $p\ge2r-1\ge t$，故
$P^-(F_r)>t-1$。由于 $D(t)=\log_\varphi t+O(1)$，最终有
$r>D(t)$；而 $r<t<2+t/\log\varphi$ 给出最后一个不等式。$\square$

命题 450.7 不声称这些秩确实满足
$N^-(t)=1+F_rg$；它只证明当前必要条件在无穷候选上仍可同时成立。
所以真正未覆盖的桥已经具体化为：证明严格库存的余数
$N^-(t)\bmod F_r$ 不等于一，或从该余数条件直接建立 Robin 的有符号余量。

## 451. 严格库存对仿射乘子的二进余类锁定

上一节的秩筛只检查了 $F_r$ 的素因子；严格库存本身还给出一个独立的
二进接口。它不能排除剩余的素数秩，但能把仿射乘子 $g$ 限制到一个随库存
高度增长的逆元余类中。这一条件与 §258.7 中固定的外部 26-free 筛不同：这里
模数是实际库存的 $2$-进赋值 $a_2(t)$，不依赖外部 Robin 证书。

### 命题 451.1（二进仿射余类）

令 $t$ 足够大，并假设

$$
N^-(t)=1+F_rg,\qquad r\ge3,\quad g\ge1.
$$

记 $a_2(t)=v_2(N^-(t))$。则

$$
\boxed{
3\nmid r,
\qquad
g\equiv -F_r^{-1}\pmod {2^{a_2(t)}}.
}
\tag{451.1}
$$

其中逆元存在于 $\mathbb Z/2^{a_2(t)}\mathbb Z$。并且由引理 448.1，

$$
\boxed{
2^{a_2(t)}>\frac43(t+1).
}
\tag{451.2}
$$

另一方面，若第 $k$ 个二进边际层被计入库存，则
$G_2(k-1)\ge1$ 与 $\log(1+u)\le u$ 给出

$$
\frac1{t\log t}<r_{2,k}
\le\frac{2^{-k}}{\log2}.
$$

所以

$$
\boxed{
2^{a_2(t)}<\frac{t\log t}{\log2}.
}
\tag{451.3}
$$

因此，在任意长度小于 $\frac43(t+1)$ 的候选 $g$-区间内，至多有一个整数
满足（451.1）。

**证明。** 当 $t$ 足够大时，$2\mid N^-(t)$，因为
$r_{2,1}=\log(3/2)/\log2>1/(t\log t)$。若 $3\mid r$，则
$2\mid F_r$，从而 $1+F_rg$ 为奇数，与 $2\mid N^-(t)$ 矛盾；故
$3\nmid r$，并且 $F_r$ 为奇数。由

$$
2^{a_2(t)}\mid N^-(t)=1+F_rg
$$

得到 $F_rg\equiv-1\pmod {2^{a_2(t)}}$。由于 $F_r$ 奇，乘以其模
$2^{a_2(t)}$ 的逆元即得（451.1）。式（451.2）正是引理 448.1
的等价改写。若两个候选 $g_1,g_2$ 都落在长度小于该模数的区间且满足（451.1），
则模数整除 $g_1-g_2$，只能有 $g_1=g_2$。$\square$

### 边界 451.2（这条余类尚未支付 Robin 缺口）

命题 451.1 的模数介于线性下界（451.2）与 $O(t\log t)$ 上界（451.3）之间，
而潜在仿射临界秩的乘子满足 $\log g\asymp t$；所以在当前
$r\in(t/2,t)$ 的候选窗口中，单个二进余类仍留下指数级长度的候选范围，
不能单独排除仿射来源。它提供的是一个可与
完整库存余数、素数幂层和 Robin 有符号价格尾项联合使用的精确接口，而不是
$N^-(t)\bmod F_r\ne1$ 的证明。

## 452. 平方层窗口给出的仿射 CRT 余类

二进层只是一个素数方向。严格库存的前向窗口还同时提供一批不同的平方层，
它们把同一个仿射乘子锁到更大的共同模数。令

$$
B_t=t+t^{4/5},\qquad
\mathcal I_t=\{q:\ q\text{ 为素数},\ t<q^2\le B_t\},
$$

并置

$$
Q_t=\prod_{q\in\mathcal I_t}q^2.
$$

### 命题 452.1（平方库存的共同仿射余类）

令 $t\ge243$，并假设

$$
N^-(t)=1+F_rg,\qquad r\ge3,\quad g\ge1.
$$

则

$$
\boxed{
 g\equiv -F_r^{-1}\pmod {Q_t}.
}
\tag{452.1}
$$

这里的逆元存在；并且命题 446.2 的短区间素数估计给出

$$
\boxed{
\log Q_t
=2\bigl(\vartheta(\sqrt {B_t})-\vartheta(\sqrt t)\bigr)
=\bigl(1+o(1)\bigr)t^{3/10}.
}
\tag{452.2}
$$

**证明。** 对每个 $q\in\mathcal I_t$，严格库存前向窗口定理取 $k=2$
给出 $q^2\mid N^-(t)$。由于 $q^2\mid N^-(t)=1+F_rg$，若 $q\mid F_r$，
则右边模 $q$ 等于 $1$，矛盾。因此每个 $q$ 与 $F_r$ 互素。约去
各个 $q^2$ 后得到

$$
F_rg\equiv-1\pmod {q^2}
\qquad(q\in\mathcal I_t).
$$

不同 $q^2$ 两两互素，CRT 给出（452.1）。式（452.2）是命题 446.2
中
$\vartheta(\sqrt {B_t})-\vartheta(\sqrt t)
=(\tfrac12+o(1))t^{3/10}$ 的两倍。$\square$

### 边界 452.2（CRT 仍没有支付完整乘子尺度）

由（452.2），平方层共同模数满足
$Q_t=\exp((1+o(1))t^{3/10})$。另一方面，在临界自匹配尺度且
$r\in(t/2,t)$ 时，已有库存渐近与 Binet 估计给
$\log g\asymp t$。所以（452.1）在该窗口内仍留下指数级长度的候选
余类代表；它比单独的二进约束强，但仍不能推出
$N^-(t)\bmod F_r\ne1$，也没有给出 Robin 的有符号余量。

## 453. 全部重复素幂的仿射模数

平方层窗口只使用了很短的一段素数区间。事实上，严格库存的所有重复素幂可以
一次性压缩成一个更大的、仍与 $F_r$ 互素的模数。对实数 $t\ge243$，令
$P(t)$ 为 $N^-(t)$ 的最大支撑素数，定义

$$
R_t=\prod_{p\le P(t)}p,\qquad H_t=\frac{N^-(t)}{R_t}.
$$

这里 $R_t$ 是严格库存的素支撑，$H_t$ 保留每个素数的额外幂次。
这与 §207 的任意仿射整数小素数核心不同：这里的支撑和指数都由同一个严格
Euler 库存强制给出，而不是为一个候选 $N_g$ 选取截断参数。

### 命题 453.1（高阶库存核心的仿射余类）

若

$$
N^-(t)=1+F_rg,\qquad r\ge3,\quad g\ge1,
$$

则

$$
\boxed{
g\equiv -F_r^{-1}\pmod {H_t}.
}
\tag{453.1}
$$

并且

$$
\boxed{
\log H_t=\sqrt2\,\sqrt t+o(\sqrt t).
}
\tag{453.2}
$$

**证明。** 首层边际价格随素数严格递减，故实际支撑为全部 $p\le P(t)$，
$H_t$ 是整数并整除 $N^-(t)$。仿射来源直接给
$\gcd(F_r,N^-(t))=1$，故 $\gcd(F_r,H_t)=1$。由
$H_t\mid N^-(t)=1+F_rg$，

$$
F_rg\equiv-1\pmod {H_t},
$$

乘以 $F_r$ 的逆元即得（453.1）。

再用命题 111.2 的已有尺度式

$$
\log N^-(t)=\psi(t)+(\sqrt2-1)\sqrt t+o(\sqrt t)
$$

以及素数定理，

$$
\psi(t)-\vartheta(t)
=\vartheta(\sqrt t)+O(t^{1/3}\log t)
=\sqrt t+o(\sqrt t).
$$

命题 450.1 的首层比较保证全部 $p\le t-1$ 均在支撑中，而命题 447.1
排除 $p\ge t$。因此 $0\le\vartheta(t)-\log R_t\le\log t$，
包括非整数时钟的可能边界素数。相减得到

$$
\log H_t
=\log N^-(t)-\log R_t
=\sqrt2\,\sqrt t+o(\sqrt t),
$$

证明（453.2）。$\square$

### 边界 453.2（重复素幂核心仍小于仿射乘子尺度）

在严格自匹配根上，若 $r\in(t/2,t)$，则已有库存渐近与 Binet 公式给出
$\log g\asymp t$，而（453.2）只有
$\log H_t\asymp\sqrt t$。因此（453.1）把乘子压到一个
$\exp(\Theta(\sqrt t))$ 模数的单一余类，却仍留下
$\exp(\Theta(t))$ 个候选尺度；它没有排除仿射来源，也没有支付 Robin 的
有符号余量。它说明下一步若要关闭余数缺口，必须使用素支撑的乘积结构与
$H_t$ 的重复幂结构之间的联合信息，而不能只增加一个固定的局部模数。

## 454. 一个有限的严格库存仿射实现

命题 450.7 的必要筛不排除有限的实际仿射库存；下面的命题给出一个严格实现。

### 命题 454.1（$F_{11}$ 的严格库存命中）

令

$$
\begin{aligned}
N_*={}&2^7 3^4 5^3 7^2
\cdot11\cdot13\cdot17\cdot19\cdot23\cdot29\cdot31\\
&\cdot37\cdot41\cdot43\cdot47\cdot53\cdot59\cdot61\cdot67\\
={}&2376356437046672757697836816000.
\end{aligned}
$$

则

$$
F_{11}=89,\qquad
g_*=\frac{N_*-1}{89}
=26700634124119918625818391191,
$$

并且对每个实数

$$
t\in[68,71]
$$

都有

$$
\boxed{N^-(t)=N_*=1+F_{11}g_* .}
\tag{454.1}
$$

**证明。** 使用 $h_p(k)=\log(1+1/(p+\cdots+p^k))$，有

$$
\frac1{p+\cdots+p^k+1}<h_p(k)<\frac1{p+\cdots+p^k}.
$$

标准对数级数给出有理数界

$$
\frac23<\log2<1,\quad1<\log3<2,\quad
1<\log5<\frac53,\quad1<\log7<2,\quad\log11>\frac73,
$$

$$
\log67<\frac{841}{200},\quad
\log68>\frac{421}{100},\quad
\frac{213}{50}<\log71<\frac{427}{100}.
$$

这些界可统一取经典展开 $z=(u-1)/(u+1)$ 的前 256 项：

$$
\log u=2\sum_{j=0}^{255}\frac{z^{2j+1}}{2j+1}+R,
\qquad 0<R\le\frac{2z^{513}}{513(1-z^2)}\quad(u>1).
$$

于是整个 $[68,71]$ 上均有

$$
\frac1{304}<\lambda(t)<\frac1{286}.
$$

四个小素数的已采用末层 $r_{2,7},r_{3,4},r_{5,3},r_{7,2}$
分别大于 $1/255,1/242,1/260,1/114$，均大于 $1/286$；
下一层 $r_{2,8},r_{3,5},r_{5,4},r_{7,3}$ 分别小于
$1/340,1/363,1/780,1/399$，均小于 $1/304$。
对 $11\le p\le67$，首层价格随 $p$ 递减，并且

$$
r_{67,1}>\frac{200}{68\cdot841}>\frac1{286},\qquad
r_{p,2}\le r_{11,2}<\frac1{308}<\frac1{304}.
$$

对所有 $p\ge71$，由 $\log(1+u)<u-u^2/2+u^3/3$ 得

$$
r_{p,1}\le r_{71,1}
<\frac{1/71-1/(2\cdot71^2)+1/(3\cdot71^3)}{213/50}
<\frac1{304}.
$$

严格前缀条件因此在整个实区间上确定相同的库存指数

$$
\begin{array}{c|rrrrrrrrrrrrrrrrrrr}
p&2&3&5&7&11&13&17&19&23&29&31&37&41&43&47&53&59&61&67\\
\hline
a_p&7&4&3&2&1&1&1&1&1&1&1&1&1&1&1&1&1&1&1 .
\end{array}
$$

有限乘积与整数除法遂给出（454.1）以及 $N_*$、$g_*$ 的所列精确值。

这个整数并不违反 Robin：其有限约数和比值为

$$
Z(N_*)=
\frac{193593307677327360}{26134262392224331}
\approx7.4076438344,
$$

同一对数级数在素因子上求和给出 $68<\log N_*<71$。再复用主卷 §84
已有的 $e^\gamma>89/50$，有严格比较

$$
Z(N_*)<\frac{149}{20}<\frac{37469}{5000}
<e^\gamma\log\log N_*.
$$

所以该命中只证明“严格库存仿射余数可以在有限尺度上实现”，不提供 Robin
反例，也不削弱 450.7 对无穷候选必要筛不完备性的诊断。它说明后续证明必须
处理实际库存余数的渐近结构，不能先验地把所有 $N^-(t)\equiv1\pmod{F_r}$
排除。

此外，

$$
\log N_*=69.943121195662589\ldots\in(68,71).
$$

由于该区间内库存指数没有变化，这个例子还给出一个严格稳定的自匹配根
$t_*=\log N_*$，满足 $N^-(t_*)=N_*$。因此，仿射 Fibonacci 命中并非只
发生在与自匹配无关的普通库存点；它可以落在 Robin 临界切片本身。该点的正裕度由上面的有理数比较给出；自匹配与仿射命中本身不确定其他根的裕度。

## 455. 严格自匹配库存是同一价格源上的 CA 子列

本节只做一个来源识别，不把任意仿射整数都标成极大丰数。对 $\lambda>0$，
令

$$
\mathcal P_\lambda(n)
=\log\frac{\sigma(n)}n-\lambda\log n
=\log\frac{\sigma(n)}{n^{1+\lambda}}.
\tag{455.1}
$$

经典定义中的 colossally abundant (CA) 数，正是存在某个 $\varepsilon>0$，
使 $\sigma(n)/n^{1+\varepsilon}$ 在所有正整数上取得全局最大值的整数。
因此，CA 的参数 $\varepsilon$ 与本卷价格 $\lambda$ 是同一个参数，
不是两个不同的优化问题。

### 命题 455.1（自匹配根的 CA 识别）

若 $z$ 是严格稳定自匹配根，且

$$
N^-(z)=\exp z,
\qquad
\lambda(z)=\frac1{z\log z},
$$

则 $N^-(z)$ 是 CA 数；若取定理 111.4 的根列 $z_j$，则所得
$N_j=N^-(z_j)$ 是一个无穷 CA 子列，并满足

$$
N_j\mid N_{j+1},\qquad N_j<N_{j+1}.
\tag{455.2}
$$

**证明。** 定义 111.1 的压力最大性给出：对每个正整数 $n$，

$$
\mathcal P_{\lambda(z)}(n)
\le
\mathcal P_{\lambda(z)}(N^-(z)).
$$

由（455.1）指数化，得到

$$
\frac{\sigma(n)}{n^{1+\lambda(z)}}
\le
\frac{\sigma(N^-(z))}{N^-(z)^{1+\lambda(z)}}.
$$

又 $z>1$，故 $\lambda(z)>0$，这正是 CA 定义，取
$\varepsilon=\lambda(z)$。定理 111.4 已给出根列无穷、严格递增及整除链，
所以（455.2）随之成立。$\square$

### 推论 455.2（有限仿射命中落在 CA 类中）

命题 454.1 的整数满足

$$
N_*=1+F_{11}g_*,
\qquad
z_*:=\log N_*\in(68,71),
\qquad
N^-(z_*)=N_*.
$$

所以它是一个同时具有以下三种描述的同一整数：

$$
\boxed{
\text{严格库存的自匹配根}
\;=\;
\text{CA 优化源的一个点}
\;=\;
\text{有限 Fibonacci 仿射命中}.}
$$

其 CA 参数为

$$
\lambda_*=
\frac1{z_*\log z_*}
\approx0.0033659135598482458.
$$

这只关闭了“严格库存自匹配子列是否属于 CA 源”的识别义务。它没有把任意
$1+F_rg$ 识别为 CA：一般仿射条件只给一个同余表示，不给全局压力最大性。
它也没有给出 Robin 不等式，因为 CA 约化仍要求在这个实际整数上证明

$$
\frac{\sigma(N_j)}{N_j}<e^\gamma\log\log N_j.
$$

命题 454.1 给出 $N_*$ 的严格正裕度；该单点事实不能交换成根列的
全称结论。

### 边界 455.3（与高阶 CA 接触定理的真实接口）

命题 455.1 使定理 111.4 的 $N_j$ 可以进入只比较同一 CA 集合的高阶接触
框架。但这还不是该框架的 FIB 应用。若要使用 Musin 的坐标传递定理，仍须
对同一批实际整数给出坐标函数的正导数、增长、凹性、支撑取得以及层间过渡
条件；仅知道 $N_j$ 是 CA，或知道它们沿 $F_r$ 有仿射表示，都不自动
提供这些条件。

因此，当前剩余问题应精确分成两层：

1. 对严格库存自匹配根，CA 来源识别已经完成；新的工作只能是验证一组适用
   于 $N_j$ 的 FIB 坐标条件，或直接控制同一 $N_j$ 上的有符号 Robin 尾项。
2. 对一般 $1+F_rg$ 仿射族，CA/SA 来源保持仍未解决；继续把同余命中当成
   CA 证据会重复并混淆两个问题。

这一区分把 §454 的有限仿射命中接到现有 CA 结构，并保留 §§441–448 的来源限制；它不推出 Robin 或 RH 的全称结论。

### 命题 455.4（严格库存覆盖 CA 价格区间的内部节点）

对整数 $n>1$，记其已采用层和下一层的价格端点为

$$
\varepsilon_-(n)=\max_{p\text{ prime}}\,r_{p,v_p(n)+1},
\qquad
\varepsilon_+(n)=\min_{p\mid n}\,r_{p,v_p(n)},
$$

下端点遍历全部素数，包括 $v_p(n)=0$ 的未采用方向；上端点只遍历非空支撑。若

$$
\varepsilon_-(n)<\varepsilon_+(n),
\tag{455.3}
$$

则存在 $t>1$ 使 $N^-(t)=n$。

**证明。** 由价格区间判据，式（455.3）给出一个
$\lambda\in(\varepsilon_-(n),\varepsilon_+(n))$。函数

$$
t\longmapsto\lambda(t)=\frac1{t\log t}
$$

在 $(1,\infty)$ 上严格递减并取遍正实数，故存在唯一 $t>1$ 使
$\lambda(t)=\lambda$。严格不等式说明：$n$ 的所有已采用层满足
$r_{p,k}>\lambda$，所有下一层及以后满足 $r_{p,k}<\lambda$。逐素数前缀最优性遂给出
$N^-(t)=n$。$\square$

因此，严格库存 $N^-(t)$ 覆盖所有 CA 价格区间的内部节点。若
$\varepsilon_-(n)=\varepsilon_+(n)$，则 $n$ 只在同价事件上取得最优性；
这种退化节点不应被强行塞入严格库存，而应使用定义 111.1 的事件层集和
命题 112.4 的子集选择。换句话说：

$$
\boxed{
\text{严格库存 }N^-\;=\;\text{CA 的非事件内部部分},
\qquad
\text{事件子集}\;=\;\text{CA 的同价边界部分}.}
$$

这比“某个仿射命中碰巧是 CA”更强，但仍没有把 FIB 地址覆盖全部 CA：
它只说明 CA 优化源可以被库存参数化；要得到 FIB 覆盖，还要证明该 CA 节点
的库存指数或事件子集满足指定五窗来源。对 Robin 而言，仍需在同一个 CA 节点
上控制点值余量；参数化本身不产生正号。

## 456. CA 胞腔内的 floor residual 与 FIB 同余脱钩

上一节把严格库存根识别成 CA 来源，但这仍没有说明 Vega 窗口中的分数部
残差由什么决定。本节给出一个精确的局部接口：**在同一个 CA 指数剖面的
稳定胞腔内，整数及其所有 FIB 同余保持不变，而 floor residual 严格变化。**
这不是重复 CA 极值约化；它说明为什么同余观察本身不能支付 Vega 的残差义务。

对素数 $p$ 和参数 $\varepsilon>0$，置

$$
Y_p(\varepsilon)
=\frac{\log\!\left((p^{1+\varepsilon}-1)/(p^\varepsilon-1)\right)}{\log p}.
\tag{456.1}
$$

有限几何和满足

$$
\frac{G_p(a)}{G_p(a-1)}
=\frac{p^{a+1}-1}{p^{a+1}-p}.
\tag{456.2}
$$

因此

$$
\frac{G_p(a)}{G_p(a-1)}>p^\varepsilon
\iff
a+1<Y_p(\varepsilon).
\tag{456.3}
$$

在非事件参数（即没有 $Y_p(\varepsilon)\in\mathbb Z$）处，严格库存的
指数恰为

$$
a_p^-(\varepsilon)=\left\lfloor Y_p(\varepsilon)\right\rfloor-1.
\tag{456.4}
$$

在 $Y_p(\varepsilon)\in\mathbb Z$ 时，严格端点和含同价层的右端点相差一层；
这正是 $N^-$ 与 $N^+$ 的事件区别，不能用一个 floor 公式掩盖。

固定一个稳定胞腔，使指数向量 $a_p$ 和最大支撑素数 $P$ 不变。定义

$$
\mathcal S_P(\varepsilon)
=\sum_{p\le P}Y_p(\varepsilon)\log p,
\qquad
\mathcal F_P(\varepsilon)
=\sum_{p\le P}\{Y_p(\varepsilon)\}\log p,
\qquad
\vartheta(P)=\sum_{p\le P}\log p.
$$

由（456.4）得到 Vega 分解的精确版本

$$
\boxed{
\log N
=\mathcal S_P(\varepsilon)-\mathcal F_P(\varepsilon)-\vartheta(P).
}
\tag{456.5}
$$

它只是把同一个整数的 CA 指数逐素数展开；没有把 residual 当成新的独立
权重，也没有把它误认为只由 $N$ 决定的量。

### 命题 456.1（稳定胞腔内 residual 严格变化）

在上述稳定胞腔内，

$$
\boxed{
\mathcal F_P'(\varepsilon)=\mathcal S_P'(\varepsilon)<0.
}
\tag{456.6}
$$

因而同一整数 $N$、同一素数支撑、同一 CA 指数向量以及同一同余条件，
对应一整段不同的 floor residual。

**证明。** 直接微分（456.1）：

$$
Y_p'(\varepsilon)
=\frac1{1-p^{-(1+\varepsilon)}}
-\frac1{1-p^{-\varepsilon}}<0.
\tag{456.7}
$$

稳定胞腔内没有分数部穿越整数，故
$\{Y_p(\varepsilon)\}'=Y_p'(\varepsilon)$。
逐项求和即得

$$
\mathcal F_P'=\sum_{p\le P}Y_p'\log p
=\mathcal S_P'<0.
$$

另一方面，指数向量固定，所以（456.5）的左端 $\log N$ 和
$\vartheta(P)$ 都固定；这也直接给出同一恒等式。若 $M\mid N-1$，
例如 $M=F_r$ 的 FIB 仿射条件 $N=1+F_rg$，则该同余在整个胞腔内
保持不变，而（456.6）说明 residual 仍严格变化。证毕。 $\square$

### 边界 456.2（当前 FIB 观察还缺什么）

命题 456.1 给出一个明确的同观察不可识别性：知道 $N$ 的 FIB 仿射同余、
CA 支撑和指数剖面，并不能确定 Vega 的 $\mathcal F_P(\varepsilon)$，因为
同一剖面允许一整段 $\varepsilon$ 而 residual 在该段严格变化。自匹配条件

$$
\varepsilon_*=\frac1{(\log N)\log\log N}
$$

会从胞腔中选出一个参数，但它提供的是额外的实数尺度方程，不是 FIB 同余
的推论。因此，若要用 Vega 窗口推进 Robin，必须再证明以下至少一项：

1. 自匹配尺度 $\varepsilon_*$ 处的 $\mathcal F_P$ 有独立的点值界；
2. FIB 地址能控制 $\mathcal S_P(\varepsilon_*)$ 的误差，从而通过（456.5）支付 residual；
3. 引入保留 $\varepsilon_*$ 与完整指数剖面的新观察，而不是继续只使用
   $N\equiv1\pmod{F_r}$。

所以，严格自匹配根的 CA 识别已经完成，但“FIB 同余 $\Rightarrow$ Robin
符号”仍然没有成立；本节把缺口收缩为同一 CA 胞腔内的实参数 residual 控制。

## 457. 自匹配点的连续包络与 floor 损失分解

§456 的 residual 还可以沿另一个切面拆开。这个拆分不引入新的价格源：它把
同一 CA 指数剖面的整数约数和，与允许指数取实数的连续 Euler 包络逐素数比较。

固定一个非事件稳定胞腔，记其支撑上界为 $P$，并置

$$
m_p(\varepsilon)=\lfloor Y_p(\varepsilon)\rfloor
=a_p^-(\varepsilon)+1.
$$

定义连续包络和取整损失

$$
\mathcal C_P(\varepsilon)
=\prod_{p\le P}\left(1-p^{-1-\varepsilon}\right)^{-1},
$$

$$
\mathcal L_P(\varepsilon)
=\sum_{p\le P}
\log\frac{1-p^{-Y_p(\varepsilon)}}
{1-p^{-m_p(\varepsilon)}}.
$$

由于 $m_p\le Y_p$，每一项损失非负：

$$
\boxed{\mathcal L_P(\varepsilon)\ge0.}
\tag{457.1}
$$

### 命题 457.1（连续 Euler 包络的精确拆分）

在该稳定胞腔内，令 $N=N^-(\varepsilon)$。则

$$
\boxed{
\log\frac{\sigma(N)}N
=\log\mathcal C_P(\varepsilon)-\mathcal L_P(\varepsilon).
}
\tag{457.2}
$$

**证明。** 对每个支撑素数，式（456.4）给出
$a_p+1=m_p$，因而

$$
\log\frac{\sigma(N)}N
=\sum_{p\le P}
\log\frac{1-p^{-m_p}}{1-p^{-1}}.
$$

另一方面，由（456.1），

$$
p^{-Y_p(\varepsilon)}
=\frac{p^\varepsilon-1}{p^{1+\varepsilon}-1},
$$

所以

$$
\frac{1-p^{-Y_p(\varepsilon)}}{1-p^{-1}}
=\frac{p^{1+\varepsilon}}{p^{1+\varepsilon}-1}
=\left(1-p^{-1-\varepsilon}\right)^{-1}.
$$

逐素数相减即得（457.2）。$m_p\le Y_p$ 又给出（457.1）。$\square$

### 推论 457.2（自匹配点的两份 Robin 预算）

若 $t>1$ 是严格自匹配根，满足

$$
N^-(t)=e^t,
\qquad
\varepsilon_*={1\over t\log t},
$$

则其对数 Robin 裕度有精确分解

$$
\boxed{
\log\frac{e^\gamma\log\log N^-(t)}
{\sigma(N^-(t))/N^-(t)}
=\underbrace{\gamma+\log(\log t)-\log\mathcal C_P(\varepsilon_*)}
_{\text{连续包络差}}
+\underbrace{\mathcal L_P(\varepsilon_*)}
_{\text{floor 取整损失}}.
}
\tag{457.3}
$$

因此，连续包络差可以为负；要得到 Robin 正性，必须证明它的负部由同一
指数剖面的取整损失支付。FIB 同余、支撑和指数向量本身不提供这两项的独立
符号界；它们至多通过（457.2）确定两项之差的实际总和。

### 命题 457.3（取整损失的逐素数界）

令 $u_p=\{Y_p(\varepsilon)\}$，并令 $x_p=p^{-Y_p(\varepsilon)}$。则

$$
\boxed{
\frac{x_p}{1-x_p}\,u_p\log p
\le
\log\frac{1-x_p}{1-x_pp^{u_p}}
\le
\frac{x_pp^{u_p}}{1-x_pp^{u_p}}\,u_p\log p.
}
\tag{457.4}
$$

求和后，左、右两侧分别给出 $\mathcal L_P(\varepsilon)$ 的下界和上界。

**证明。** 对 $0\le s\le u_p\log p$ 积分：

$$
\log\frac{1-x_p}{1-x_pp^{u_p}}
=\int_0^{u_p\log p}
\frac{x_pe^s}{1-x_pe^s}\,ds.
$$

被积函数严格递增，分别用其在区间左、右端点的值估计，即得（457.4）。
$\square$

式（457.4）给出当前 FIB 观察的一个具体缺口：§456 中的无权 residual
$\sum u_p\log p$ 不是取整损失本身；后者还带有随 $p$ 变化且随素数衰减的
Euler 权重。要把 FIB 地址用于（457.3），必须增加能恢复这些
加权分数部，或直接恢复同一素数幂层的取整损失的观察器。继续增加只记录
$N\equiv1\pmod {F_r}$ 的状态不会支付这个新义务。

本节是 §456 的同一 CA 胞腔内代数分解；它没有给出连续包络差的全局符号，
没有证明 Robin 不等式或 RH，也没有把有限自匹配点的正裕度提升为无穷全称结论。

## 458. 连续包络差的 Mertens—截断—取整三项分解

§457 的连续包络仍把有限素数乘积和 Robin 预算放在同一个符号里。再引入

$$
\mathcal M(P)=\prod_{p\le P}(1-p^{-1})^{-1},
$$

$$
\mathfrak m(P)
=\log\frac{\mathcal M(P)}{e^\gamma\log P},
$$

以及连续指数造成的衰减

$$
\mathcal A_P(\varepsilon)
=\log\frac{\mathcal M(P)}{\mathcal C_P(\varepsilon)}.
$$

因为 $p^{-1-\varepsilon}<p^{-1}$，有

$$
\boxed{\mathcal A_P(\varepsilon)\ge0.}
\tag{458.1}
$$

### 命题 458.1（自匹配点的三项精确账本）

在严格自匹配根 $t$ 上，记 $\varepsilon_*=(t\log t)^{-1}$，并令 $P$
为 $N^-(t)$ 的最大支撑素数；由严格库存的支撑截止，其支撑正好是
所有 $p\le P$ 的素数。则

$$
\boxed{
\log\frac{e^\gamma\log\log N^-(t)}
{\sigma(N^-(t))/N^-(t)}
=
\log\frac{\log t}{\log P}
-\mathfrak m(P)
+\mathcal A_P(\varepsilon_*)
+\mathcal L_P(\varepsilon_*).
}
\tag{458.2}
$$

**证明。** 由（457.3），连续包络部分为

$$
\gamma+\log(\log t)-\log\mathcal C_P(\varepsilon_*).
$$

又

$$
\log\mathcal C_P(\varepsilon_*)
=\log\mathcal M(P)-\mathcal A_P(\varepsilon_*)
=\gamma+\log(\log P)+\mathfrak m(P)
-\mathcal A_P(\varepsilon_*).
$$

代入并保留（457.3）的 $\mathcal L_P$ 即得（458.2）。同一恒等式还给出

$$
\mathcal A_P(\varepsilon)+\mathcal L_P(\varepsilon)
=\log\frac{\mathcal M(P)}{Z(N)}
=-\sum_{p\le P}\log(1-p^{-a_p-1}).
\tag{458.5}
$$

因此，在指数向量固定的同一个稳定胞腔内，完整补偿不随价格变化；价格只改变
两部分之间的分配。右端是既有有限指数 Euler 修正，见
[Polak 的完整支撑恒等式](../../../Library/Analytic/polak2026finiterobinca.md#directly-reusable-effective-core)。$\square$

因此，自匹配根上的 Robin 不等式等价于同一个实际支撑上的严格条件

$$
\boxed{
\mathfrak m(P)
<
\log\frac{\log t}{\log P}\,+\mathcal A_P(\varepsilon_*)\,+\mathcal L_P(\varepsilon_*).
}
\tag{458.3}
$$

左侧是有限 Mertens 乘积相对于 $e^\gamma\log P$ 的实际偏差；右侧的三项
分别来自支撑截断、连续价格衰减和整数取整。这个条件没有把 Mertens 误差
替换成平均估计，也没有把取整损失隐藏进定义。

### 命题 458.2（连续价格衰减的显式上界）

对 $\varepsilon>0$，有

$$
\boxed{
0\le\mathcal A_P(\varepsilon)
\le
\varepsilon\sum_{p\le P}\frac{\log p}{p-1}.
}
\tag{458.4}
$$

**证明。** 对每个 $p$，函数

$$
u\longmapsto\log(1-p^{-1-u})
$$

的导数为

$$
\frac{(\log p)p^{-1-u}}{1-p^{-1-u}},
$$

它在 $u\ge0$ 上不超过 $\log p/(p-1)$。从 $u=0$ 积分到
$u=\varepsilon$，再求和即得（458.4）。$\square$

式（458.3）要求控制同一支撑 $P$ 上的 $\mathfrak m(P)$ 与完整 Euler
修正的联合预算。可以分别估计两份补偿，也可以直接估计（458.5）；逐项恢复
加权分数部并非后一条路线的必要条件。在严格自匹配点，完整指数向量还决定
$t=\sum_pa_p\log p$ 及唯一价格 $\varepsilon_*$，所以此时剩余义务是
统一的有符号估计，而非一个仍未指定的胞腔内价格。FIB 同余单独没有给出该估计。

本节是 §457 的代数重排；它没有提供 $\mathfrak m(P)$ 的新全局界，
没有证明（458.3）对所有自匹配根成立，也没有证明 Robin 不等式或 RH。

## 459. 把最新有限 Mertens 乘积界接入同一预算

Broadbent--Fiori--Kadiri--Ng--Wilk 的
[逆素数乘积上界](../../../Library/Weil/broadbent2026mertens.md)给出以下前置：对
$\ell\in\{1,2,3,4,5\}$ 及 $P\ge x_0\ge2$，存在其文中定义的正数
$\mathcal D_\ell(x_0),\mathcal D'_\ell(x_0)$，使

$$
e^\gamma\log P\left(1-\frac{\mathcal D_\ell(x_0)}{(\log P)^\ell}\right)
\le \mathcal M(P)
\le
e^\gamma\log P\left(1+\frac{\mathcal D'_\ell(x_0)}{(\log P)^\ell}\right).
\tag{459.1}
$$

下界只在左侧因子为正时使用；上界无需这一附加条件。这里复用的是该文的
有限乘积定理及其适用范围，不把文中的数值表当作本项目重新认证的计算。

### 命题 459.1（有限 Mertens 偏差的显式包络）

令

$$
\delta_+(P;x_0,\ell)=
\frac{\mathcal D'_\ell(x_0)}{(\log P)^\ell},
\qquad
\delta_-(P;x_0,\ell)=
\frac{\mathcal D_\ell(x_0)}{(\log P)^\ell}.
$$

则由（459.1）直接得到

$$
\boxed{
\log(1-\delta_-)
\le \mathfrak m(P)
\le \log(1+\delta_+)
}
\tag{459.2}
$$

其中左侧要求 $0<\delta_-<1$。特别地，

$$
0\le \mathfrak m(P)\le\log(1+\delta_+)
$$

只有在额外知道 $\mathcal M(P)\ge e^\gamma\log P$ 时才成立；一般不能把
有限 Mertens 偏差预先当成非负量。

**证明。** 将（459.1）除以 $e^\gamma\log P$，再使用对数函数在正数上的
严格单调性即可。上界中的 $1+\delta_+$ 始终为正；下界需要
$1-\delta_->0$。$\square$

### 推论 459.2（Robin 三项账本的可检验充分条件）

在 §458 的严格自匹配根上，若 $P\ge x_0$，则

$$
\boxed{
\Delta_{\rm Robin}
\ge
\log\frac{\log t}{\log P}
-\log(1+\delta_+)
+\mathcal A_P(\varepsilon_*)
+\mathcal L_P(\varepsilon_*).
}
\tag{459.3}
$$

因此定义所需的剩余阈值

$$
\Theta_+(P,t;x_0,\ell)
=
\max\!\left\{0,
\log\frac{(1+\delta_+(P;x_0,\ell))\log P}{\log t}
\right\},
$$

则下面的联合条件足以推出严格 Robin 不等式：

$$
\boxed{
\mathcal A_P(\varepsilon_*)+\mathcal L_P(\varepsilon_*)
>\Theta_+(P,t;x_0,\ell).
}
\tag{459.4}
$$

还可以丢弃连续价格衰减这一非负项，得到较强但更直接的 floor 证书：

$$
\boxed{
\mathcal L_P(\varepsilon_*)
>\Theta_+(P,t;x_0,\ell)
\quad\Longrightarrow\quad
\Delta_{\rm Robin}>0.
}
\tag{459.5}
$$

由（457.4），一个完全逐素数、可由 FIB 观察继续攻击的充分条件是

$$
\boxed{
\sum_{p\le P}
\frac{p^{-Y_p(\varepsilon_*)}}{1-p^{-Y_p(\varepsilon_*)}}
\{Y_p(\varepsilon_*)\}\log p
>
\Theta_+(P,t;x_0,\ell).
}
\tag{459.6}
$$

**证明。** 将（459.2）的上界代入（458.2），并用
$\mathcal A_P\ge0$、（457.4）的取整损失下界，即得（459.3）--（459.6）。
$\square$

式（459.4）是有限尺度的充分判据。完整 CA 指数向量与自匹配条件足以确定
其全部量；FIB 同余与支撑单独则不足。这里需要的是足够强的联合估计，而不能
把完整补偿拆分后当成两份独立增加的预算。

## 追加锚（本行以下为增补区）

## 460. 实际自匹配源对单独头部证书的条件性障碍

本节将主卷 §111.4 的实际自匹配链接到同窗素数头部，得到一种证书路线的条件性障碍。
这是既有来源的仓内应用（`repo-derived`），不主张文献原创性。假设 RH，并沿用
[Nicolas 比较笔记](../../../Library/ArithSums/nicolas2025comparison.md) 的完整零点公式及误差范围；
另明确采用 RH 下 $\vartheta(u)-u=O(\sqrt u\log^2u)$ 作为外部解析输入。
下面的非存在结论只在这些条件下成立，不给出无条件 Robin 结论或 RH 结论。

取主卷 §111.4 的同一实际链 $N_j$，置

$$
A_j=\log N_j,\qquad L_j=\log A_j,\qquad T_j=\sqrt{A_j}\,L_j.
$$

定义这个整数自己的窗口：

$$
\begin{aligned}
D_j&=\lfloor A_j^{1/8}\rfloor,\\
G_j&=\sum_{\substack{d\le D_j\\d\mid\operatorname{rad}(N_j)}}
       \frac{\mu^2(d)}{\varphi(d)},\\
h_j&=\min\{L_j/2000,G_j/100\},\qquad B_j=A_j e^{h_j}.
\end{aligned}
$$

这里 $\mu$ 是 Möbius 函数。令 $Y_j=\sqrt{B_j}$，令 $P_j$ 为所有满足
$p\le Y_j$ 且 $p\mid N_j$ 的素数之积，并记

$$
\begin{aligned}
S_j^\circ&=\sum_{\substack{A_j<r\le B_j\\(r,P_j)=1}}\frac1r
-\sum_{\substack{k\ge2,\ A_j<p^k\le B_j\\p\nmid N_j}}\frac1{p^k},\\
V_j&=-\frac{\vartheta(A_j)-A_j}{A_jL_j}
 +\log\frac{L_j+h_j}{L_j}-S_j^\circ.
\end{aligned}
$$

### 460.1. 实际支撑覆盖与零价格亏损

因为 $0\le h_j\le L_j/2000$，先有
$Y_j\le A_j^{1/2+1/4000}$。对充分大的 $j$ 和全部 $p\le Y_j$，首层价格满足

$$
r_{p,1}=\frac{\log(1+1/p)}{\log p}
>\frac1{(p+1)\log p}
>\frac1{A_j\log A_j}=\lambda(A_j),
$$

因为 $(A_j^{1/2+1/4000}+1)\log(A_j^{1/2+1/4000})<A_j\log A_j$ 最终成立。
§111.4 的唯一价格最优者取尽全部严格有益层，所以这些素数确实都出现在 $N_j$ 中。
特别地，每个 $d\le D_j$ 的平方自由核都被支撑覆盖。

此处只需要有限的调和和比较。按 $d=\operatorname{rad}(n)$ 分组，使用
$\sum_{\operatorname{rad}(n)=d}1/n=1/\varphi(d)$（$d$ 平方自由），便有

$$
H_{D_j}=\sum_{n\le D_j}\frac1n
\le\sum_{d\le D_j}\frac{\mu^2(d)}{\varphi(d)}
=G_j,\qquad H_{D_j}\ge\log(D_j+1)>L_j/8.
$$

因此最终 $h_j=L_j/2000$，$B_j=A_j^{1+1/2000}$。
区间 $(A_j,B_j]$ 中的每个合数都有一个不超过 $Y_j$ 的素因子，
而第二个和中的每个素数底数也不超过 $Y_j$；它们全被实际支撑覆盖。
又有 $Y_j<A_j$，故

$$
S_j^\circ=\sum_{A_j<p\le B_j}\frac1p.
$$

同一整数的价格亏损为

$$
d_{A_j}(N_j)
=S(\lambda(A_j))-
 \left(\log Z(N_j)-\lambda(A_j)\log N_j\right)=0,
$$

其中 $S$、$Z$ 和 $\lambda$ 沿用主卷 §98.1；没有换成另一个极值整数。

### 460.2. 完整尾项决定头部的条件性下界

沿用 Nicolas 笔记的正核，明确置

$$
\begin{aligned}
K(u)&=\frac{1+\log u}{u^2\log^2u},\\
J_1^\vartheta(A)&=-\int_A^\infty(\vartheta(u)-u)K(u)\,du,\\
J_1^\psi(A)&=-\int_A^\infty(\psi(u)-u)K(u)\,du,\\
J_1^{\ge2}(A)&=-\int_A^\infty(\psi(u)-\vartheta(u))K(u)\,du,\\
R_\vartheta(B)&=\frac{\vartheta(B)-B}{B\log B}+J_1^\vartheta(B).
\end{aligned}
$$

这里 $\vartheta(u)=\sum_{p\le u}\log p$，
$\psi(u)=\sum_{p^k\le u}\log p$；两者均保留包含端点的实际原子及其对数权重。
有限 Stieltjes 分部积分保留 $(A_j,B_j]$ 的全部素数原子，直接给出

$$
J_1^\vartheta(A_j)=V_j+R_\vartheta(B_j).
$$

在本节的 RH 与完整显式公式条件下，对 Nicolas 笔记的 GR5–GR8 与 GAK10–GAK16
取确定尺度 $c=1$，结合经典完整零点权重恒等式，得到

$$
|T_jJ_1^\psi(A_j)|\le c_0+o(1),\qquad
c_0=2+\gamma-\log(4\pi)<1/20.
$$

这里保留完整积分系数及 GAK16 的初等修正；后者乘以 $T_j$ 后为 $O(A_j^{-1/2})$，
不能把完整显式公式直接替换成零点首项。GPP1–GPP4 的同一完整高次幂估计在尺度 $c=1$ 给出

$$
T_jJ_1^{\ge2}(A_j)\longrightarrow-2.
$$

由于 $J_1^\vartheta=J_1^\psi-J_1^{\ge2}$，于是

$$
T_jJ_1^\vartheta(A_j)\ge2-c_0-o(1).
$$

RH 下 $\vartheta(u)-u=O(\sqrt u\log^2u)$ 还控制同一端点及整个尾项，故

$$
R_\vartheta(B_j)=O\!\left(\frac{\log B_j}{\sqrt{B_j}}\right),
\qquad
T_jR_\vartheta(B_j)=O(A_j^{-1/4000}L_j^2)\longrightarrow0.
$$

从而在这些完整条件下

$$
\liminf_{j\to\infty}T_jV_j\ge2-c_0>\frac{39}{20}.
$$

因此，不存在一种适用于所有实际整数、只使用上述头部的统一点态证书，
其预算在价格亏损为零时强迫

$$
T_jV_j\le b(A_j),\qquad b(A_j)\le b_0<1.
$$

这只排除该类单独头部证书。GPP1–GPP4 保留的完整高次幂项提供同尺度补偿，
所以同一实际整数、同一概率律上的头部与高次幂联合预算仍是另一项研究对象。
这里没有排除只在额外选定的潜在 Robin 极值整数上要求成立的证书，
也没有得到无条件非存在结论、Robin 反例或 RH 反例。

## 追加锚（本行以下为增补区）

## 461. 变化秩问题的既有固定参数输入

固定禁素集的限制最大阶直接由 Tóth–Wirsing (2003), Corollary 2 给出。
[增长模数文献笔记的固定参数应用](../../../Library/ArithSums/fibaffine2026growingmoduli.md)
记录原文、$f(n)=\sigma(n)/n$、$S=\{p:p\mid m\}$ 的参数对应，及其
对 $1+F_rg$ 的固定秩消费者。该已发表输入同时给出固定 $m$ 的严格
尾部和因子 $c_m=\prod_{p\mid m}(1-p^{-1})$；本卷不重证它。

下面 §462 需要研究的是这个固定参数因子在 $m=F_r$ 变化时的退化，
以及同一变化秩候选的完整 Robin 预算。固定秩的
$\forall r\,\exists G_r\,\forall g\ge G_r$ 不能交换成共同阈值。

## 462. 素秩 Fibonacci 禁素因子的 Euler 余量窗口

§461 引用的固定禁素集结论留下了一个具体的变化秩问题：固定参数结果中的
严格因子

$$
c_m=\prod_{p\mid m}\left(1-\frac1p\right)
$$

在 $m=F_r$ 随 $r$ 变化时究竟能被统一控制到什么程度。§450.7 已经给出
了素秩 $r$ 的每个素因子 $p\mid F_r$ 满足 $p\ge 2r-1$。主卷 §171 已登记
Luca--Mejía Huguet--Nicolae (2009) 对同一入口秩桶的更强倒数素数估计；
下面只把该既有估计接到 Euler 因子和 Robin 量词，不把文献结果重复写成
本仓原创定理。

### 命题 462.1（素秩 Euler 缺口的双边夹逼）

设 $r>5$ 为素数，置

$$
\delta_r=1-c_{F_r}.
$$

则

$$
\boxed{
\frac1{F_r}\le \delta_r
\le
\frac{r\log\varphi}{(2r-1)\log(2r-1)}.
}
\tag{462.1}
$$

此外，已有文献估计给出某个绝对常数 $C>0$，使

$$
\boxed{
\delta_r\le C\frac{\log r}{r}.
}
\tag{462.2}
$$

因此实际 $\delta_r\to0$（沿素数秩）。这说明固定禁素集证明中的 Euler
缺失因子在变化秩上确实退化；它不是一个可以统一保留的正余量。

**证明。** 先取任意素数 $p\mid F_r$。因为 $F_r>1$ 且 $p\le F_r$，有

$$
c_{F_r}\le1-\frac1p\le1-\frac1{F_r},
$$

得到左侧。

对（462.1）的右侧，$p\ge2r-1$ 给
$\omega(F_r)\log(2r-1)\le\log F_r<r\log\varphi$，故
$\delta_r\le\omega(F_r)/(2r-1)$ 即得该显式界。

对更强的（462.2），任意 $p\mid F_r$ 的入口秩满足 $z(p)\mid r$；因 $r>5$
为素数，$p=2,5$ 被排除且 $z(p)=r$。因此

$$
\delta_r
\le\sum_{p\mid F_r}\frac1p
\le\sum_{z(p)=r}\frac1p.
$$

最后一项的 $O(\log r/r)$ 界正是主卷 §171 所引
Luca--Mejía Huguet--Nicolae (2009), Lemma 3, 式 (5) 的结果。故
（462.2）是该文献估计对 $c_{F_r}$ 的直接应用，而非重新证明其素数桶
估计。证毕。 $\square$

### 推论 462.2（固定禁素集预算的迭代极限障碍）

对 $r>5$ 为素数，令 $q_{r,1}<q_{r,2}<\cdots$ 是不整除 $F_r$ 的素数，
并置

$$
Q_{r,k}=\prod_{j\le k}q_{r,j},\qquad
A_{r,k}=\prod_{j\le k}\frac{q_{r,j}}{q_{r,j}-1}.
$$

则

$$
\boxed{
\lim_{\substack{r\to\infty\\ r\ {\rm prime}}}
\ \lim_{k\to\infty}
\frac{A_{r,k}}{e^\gamma\log\log Q_{r,k}}
=1.
}
\tag{462.3}
$$

因此不存在固定的 $\eta>0$ 和 $k_0$，使所有素数秩 $r>5$ 及所有
$k\ge k_0$ 都满足

$$
A_{r,k}\le(1-\eta)e^\gamma\log\log Q_{r,k}.
$$

**证明。** §461 所引的经典 Mertens 极限给出，对每个固定 $r$，

$$
\lim_{k\to\infty}
\frac{A_{r,k}}{e^\gamma\log\log Q_{r,k}}
=c_{F_r}.
$$

命题 462.1 的文献上界给出 $c_{F_r}=1-\delta_r\to1$，再取外层极限
即得（462.3）。若存在所述统一 $\eta,k_0$，固定一个使
$c_{F_r}>1-\eta/2$ 的素数秩，再令 $k$ 足够大，便与该统一界矛盾。
证毕。 $\square$

这个障碍只针对“缺失 Euler 因子提供固定比例安全余量”的路线。它不构成
Robin 反例：$Q_{r,k}$ 是允许素数的 primorial，且
$A_{r,k}$ 只是约数比的上包络；真实整数的指数层、同一来源的完整素支撑
和有符号 Robin 余量仍未被此迭代极限确定。

### 推论 462.3（固定禁素集路线的最坏分辨率代价）

若只使用命题 462.1 的下界来选择固定禁素集证书的严格余量，可以安全取

$$
\eta_r=\frac1{2F_r}\le\frac{\delta_r}{2}.
\tag{462.4}
$$

因此，若证书只使用这份最坏余量而不读取 $F_r$ 的完整支撑，就必须把
相对误差压到 $O(F_r^{-1})$ 的量级，才能闭合高素支撑分支。具体地，沿用 §459 的有效
上界

$$
\mathcal M(x)
\le e^\gamma\log x
\left(1+\frac{\mathcal D'_\ell(x_0)}{(\log x)^\ell}\right),
$$

一个足以使该误差不超过 $1/(4F_r)$ 的尺度条件是

$$
\boxed{
\log x\ge
\bigl(4\mathcal D'_\ell(x_0)F_r\bigr)^{1/\ell}.
}
\tag{462.5}
$$

这只支付有限 Euler 乘积的误差；允许素数 primorial 与
$\log\log Q_k$ 的比较、有限个低 $\omega$ 分支仍须另行处理。因而（462.5）不是一个已经闭合的统一 Robin 阈值，而是当前路线的
可核查分辨率成本。

若把 $x$ 视为最后一个允许素数，$\log Q_k\asymp x$ 的经典尺度关系还会
把这个保守证书推到

$$
\log n\ \text{约需达到}\
\exp\!\bigl((4\mathcal D'_\ell(x_0)F_r)^{1/\ell}\bigr)
$$

的量级。这个表达只描述所选 Mertens 证书的充分尺度，不是实际 Robin
阈值的下界，也不排除在同一 $N_{r,g}$ 上使用完整素支撑、指数层或有符号
余量得到更强的估计。

### 变化秩接口的剩余义务

命题 462.1 把缺口分成两种可区分的改进方向：

1. 证明 $c_{F_r}$ 的实际缺口 $\delta_r$ 远大于 $1/F_r$，从而降低
   （462.5）的分辨率成本；或
2. 不再把固定禁素集的 Euler 因子作为唯一余量，直接在同一个
   $N_{r,g}=1+F_rg$ 上控制完整素支撑、素数幂层和 Robin 有符号尾项。

仅把（462.1）与 §461 的逐秩量词拼接，仍只能得到

$$
\forall r\ \exists G_r\ \forall g\ge G_r,
$$

不能交换为变化秩的统一 $G$，更不能推出 Robin 全称不等式或 RH。该节是
仓内对已有入口秩约束的量化组合，未新增 Lean 声明、未重复外部 Robin
判据，也未把分辨率成本冒充定理结论。

## 463. 超丰数整除条件对变化秩 FIB 候选的必要过滤

§462 只使用 $F_r$ 的缺失 Euler 因子。这里接入一个不同的、只针对最小
反例的外部结构输入：[Segovia 的分拆预印本](../../../Library/ArithSums/segovia2026partitions.md)
Lemma 8 声称：对每个固定 $0<c<1$，存在 $N_0(c)$，使得每个大于该阈值的
超丰数 $N$ 都被

$$
L_c(N):=\operatorname{lcm}\bigl(1,\ldots,\lfloor c\log N\rfloor\bigr)
$$

整除。这里使用的是该来源的陈述；本项目没有独立审计其完整证明，也没有把
它当作无条件的 Robin 定理。

### 命题 463.1（FIB 同余与超丰数整除的相容性条件）

固定 $0<c<1$。若 $r>5$ 为素数，且

$$
N_{r,g}=1+F_rg
$$

是大于 $\max\{5040,N_0(c)\}$ 的最小 Robin 反例，则

$$
\boxed{
\gcd(F_r,L_c(N_{r,g}))=1,\qquad
P^-(F_r)>\lfloor c\log N_{r,g}\rfloor,
}
\tag{463.1}
$$

其中 $P^-(m)$ 表示 $m>1$ 的最小素因子。

**证明。** 最小 Robin 反例是超丰数，这是 Robin 候选缩减所使用的已知结构
输入。由上述 Segovia 引理，$L_c(N_{r,g})\mid N_{r,g}$。另一方面

$$
N_{r,g}\equiv1\pmod {F_r},
$$

所以 $\gcd(N_{r,g},F_r)=1$。任何同时整除 $F_r$ 与 $L_c(N_{r,g})$ 的素数
都会整除 $N_{r,g}$，矛盾，得到第一个结论。若素数 $p\mid F_r$ 且
$p\le\lfloor c\log N_{r,g}\rfloor$，则 $p\mid L_c(N_{r,g})$，又得到同一
矛盾。因此所有 $F_r$ 的素因子都大于该整数，得到第二个结论。证毕。
$\square$

### 推论 463.2（窗口形式与路线边界）

若同时取已有窗口

$$
g\in I_r=\left[\left\lceil\frac{F_r}{10}\right\rceil,
             \left\lfloor\frac{F_r}{5}\right\rfloor\right]\cap\mathbb Z,
$$

则任何满足命题 463.1 的候选都必须满足

$$
\boxed{
P^-(F_r)>c\bigl(2\log F_r-\log 10\bigr)-1.
}
\tag{463.2}
$$

因为 $N_{r,g}\ge F_r^2/10$，而
$\lfloor x\rfloor\ge x-1$。若 $F_r$ 为合数，则还必须有

$$
c\bigl(2\log F_r-\log 10\bigr)-1< P^-(F_r)\le\sqrt{F_r}.
\tag{463.3}
$$

这是一条可以只用 $F_r$ 的实际分解检查的候选排除条件：一旦发现
$p\mid F_r$ 且 $p\le\lfloor c\log N_{r,g}\rfloor$，整个该窗口都不可能含有
这样的**最小** Robin 反例。

这条过滤没有关闭变化秩缺口。对素数秩，已有入口秩下界
$p\ge2r-1$，而窗口中 $\log F_r\sim r\log\varphi$；因此对固定 $c<1$
，已知下界本身通常已经高于（463.2）的右侧，不能产生统一矛盾。若 $F_r$
本身为素数，条件更不会排除候选。故（463.1）是最小反例的必要结构，
不是所有 $N_{r,g}$ 的 Robin 安全定理，也不是 RH 证明；它只把最新的
超丰数整除输入接回 FIB 同余，并明确显示该接口还不足以支付完整有符号余量。

本节复用 Robin 的最小反例—超丰数缩减、Fibonacci 同余和 Segovia 的来源
陈述；没有重做这些外部结果，未新增 Lean 声明。

## 464. 素秩 Fibonacci 支撑的局部修复分层

上一节的超丰数整除条件只给出 $F_r$ 与小素数库存互素。这里接入一个不同
的近期局部结果：[Chuysurichay--Jaidee--Panraksa--Ward 的 Dold 文献卡](../../../Library/Scale/chuysurichay2026fibdold.md)
的 Theorem 2.4 给出 Fibonacci 序列在每个素数 $p$ 处的精确修复因子。文献把
入口秩记作 $\varphi(p)$；本节改写为 $z(p)$，以免与黄金比混淆。

### 命题 464.1（素秩支撑的两类局部因子）

设 $r>5$ 为素数，并定义

$$
\mathcal P_r^+=\{p:p\mid F_r,\ (5/p)=1\},
\qquad
\mathcal P_r^-=\{p:p\mid F_r,\ (5/p)=-1\},
$$

其中 $(5/p)$ 是 Legendre 符号。对每个 $p\mid F_r$，有

$$
\boxed{
\operatorname{Fail}_p(F)=
\begin{cases}
1,&p\in\mathcal P_r^+,\\
r,&p\in\mathcal P_r^-.
\end{cases}}
\tag{464.1}
$$

因此，所有 $F_r$ 支撑素数的局部修复因子之最小公倍数为

$$
\boxed{
\operatorname{lcm}_{p\mid F_r}\operatorname{Fail}_p(F)
=
\begin{cases}
1,&\mathcal P_r^-=\varnothing,\\
r,&\mathcal P_r^-\ne\varnothing.
\end{cases}}
\tag{464.2}
$$

**证明。** 对 $p\mid F_r$，强整除性给出 $z(p)\mid r$。由于 $r>5$ 为素数，
$p\ne2,5$ 且 $z(p)>1$，故 $z(p)=r$。标准的 Fibonacci 入口秩同余给出

$$
r\mid p-(5/p).
$$

若 $(5/p)=1$，则 $r\mid p-1$，于是
$z(p)/\gcd(z(p),p-1)=1$。若 $(5/p)=-1$，则 $r\mid p+1$；因 $r$ 为奇素数，
$\gcd(r,p-1)=1$，故该比值为 $r$。代入文献 Theorem 2.4 得（464.1），再取
最小公倍数得（464.2）。证毕。 $\square$

这里的分层可直接用模 $5$ 的支撑检查识别：$\mathcal P_r^+$ 中的素数都
同余于 $\pm1\pmod5$，而 $\mathcal P_r^-$ 中的素数都同余于 $\pm2\pmod5$。
例如 $F_7=13$ 给出一个 $r$ 级局部因子，而 $F_{11}=89$ 给出修复因子 $1$。
若 $F_r\equiv\pm2\pmod5$，则 $\mathcal P_r^-$ 必非空，因为只由
$\pm1\pmod5$ 的素数幂组成的乘积不可能同余于 $\pm2\pmod5$。

Fibonacci 数模 $5$ 的周期为 $20$。因此对素数 $r>5$，还可把这个充分条件写成

$$
r\equiv3,7,13,17\pmod{20}
\quad\Longrightarrow\quad
\operatorname{lcm}_{p\mid F_r}\operatorname{Fail}_p(F)=r.
\tag{464.3}
$$

这覆盖素数秩的四个约化剩余类；其余四类不能由模 $5$ 的乘积单独判定。
例如 $r=31\equiv11\pmod{20}$ 时，$F_{31}=557\cdot2417$ 的两个支撑素数仍都
属于 $\mathcal P_r^-$，说明（464.3）是充分条件而非分类的逆命题。

命题 464.1 是一个新的素切面：它把同一 $F_r$ 的素支撑区分为“局部可直接
实现”和“必须支付 $r$ 级修复”的两类。它仍不提供 $N_{r,g}=1+F_rg$ 的
素数幂赋值，也不控制 $\sigma(N_{r,g})/N_{r,g}$ 的有符号 Robin 余量；因此
不能把（464.2）当作 Robin 安全因子或 RH 证明。要让它推进 Robin，下一步必须
证明这两类支撑在同一个候选 $N_{r,g}$ 的完整 Euler 库存中产生可组合的联合界，
而不是只读取 $F_r$ 自身的局部标签。

本节只组合近期的局部 Fibonacci 结果与已有入口秩同余，未重复 Dold、Robin 或
CA/SA 的一般理论，也未新增 Lean 声明。
