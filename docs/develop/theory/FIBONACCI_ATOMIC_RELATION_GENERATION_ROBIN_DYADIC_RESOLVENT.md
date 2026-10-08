# Robin 二倍递归的逆算子与局部 Mertens 供应

本卷续接 [原曲率逼近卷](FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_CURVATURE_APPROXIMATION.md) §472。
本文区分纸面推导、已有严格编译结果与尚待编译的组合。

## 473. 同一个素数剥离为何既可逆又会失去统一控制

令 μ 为实际整数 Möbius 函数，定义有限原和
\[
 H_\sigma(N)=\sum_{1\le n\le N}\mu(n)n^{-\sigma},\qquad
 G_\sigma(N)=\sum_{\substack{1\le n\le N\\n\text{ 奇}}}\mu(n)n^{-\sigma},
 \qquad H_\sigma(0)=G_\sigma(0)=0.
\]
这里所有求和都是自然截断，σ 为实数。

### 473.1 加权归一化改变递归的收缩系数

**命题 473.1。** 对任意实数 σ 与自然数 N、K，有
\[
 H_\sigma(N)=G_\sigma(N)-2^{-\sigma}G_\sigma(\lfloor N/2\rfloor),
\]
\[
 G_\sigma(N)=\sum_{a=0}^{K-1}2^{-a\sigma}H_\sigma(\lfloor N/2^a\rfloor)
       +2^{-K\sigma}G_\sigma(\lfloor N/2^K\rfloor).
\]
证明以奇偶分拆开始：奇数 m 满足 μ(2m)=−μ(m)，偶数 m 满足 μ(2m)=0，且
(2m)^{-σ}=2^{-σ}m^{-σ}。第二式由第一式有限迭代，并保留整数除法的完整余项。
当 2^K>N 时，末项精确为零；无需交换无限求和。
σ=1 的两个完整恒等式已在奇数调和递归单元中严格编译；此处任意 σ 的扩展是纸面证明。

定义 (Tu)(N)=u(⌊N/2⌋)。在满足 u(0)=0 的有界序列空间上，||T||≤1。
若 σ>0，算子 I−2^{-σ}T 的逆由范数收敛的几何级数给出，且
\[
 \|(I-2^{-\sigma}T)^{-1}\|\le\frac1{1-2^{-\sigma}}.
\]
这一结论适用于有界输入；它不声称 σ≤1 的实际 Möbius 级数绝对收敛。
σ 趋向零时，上述逆界发散。在 σ=0 时有限迭代仍终止，但整个有界序列空间上没有
对应的统一有界逆：取 h(0)=0、h(N)=1（N≥1），则唯一逐点解是
g(N)=1+⌊log₂N⌋，它无界。

这给“等价形态像群”的直觉一个可检验的范围：有限剥离确实可逆；
无限尺度的误差控制还依赖归一化后的系数和所用范数。
Fibonacci 的矩阵递归同样需要检查迭代增长，但这不提供两种算术对象之间的同构。
5040 的有限素因子分解也不能独自支付无限尾项的统一估计。

### 473.2 完整商族把普通 Mertens 界转成调和界

记 M(N)=Σ_{1≤n≤N}μ(n)，H=H₁。已有本地严格编译的普通 Mertens 供应为
\[
 \exists C>0\quad\forall N\ge1,\qquad
 |M(N)|\le\frac{CN}{(1+\log N)^4}.
\]
它来自实际截断 Perron、零点自由区域与完整矩形轮廓，不以 RH 为前提。
此供应尚未作为本节组合在仓库内交付；供应自身的严格编译不代替组合的验收。

Gaussian 库的有限双曲线证明保留全部 M(⌊DQ/q⌋)（1≤q≤Q）与有符号取整余项，给出
\[
 \bigl[\forall n\ge D,\ |M(n)|\le\delta n\bigr]
 \Longrightarrow |H(D)|\le\frac2Q+\delta(2+\log Q)
 \quad(D,Q\ge1,\ \delta\ge0).
\]
此处每个商截断都满足 ⌊DQ/q⌋≥D；只控制 M(D) 一个值不足以代替前提。
取 Q=D、L=1+log D、δ=C/L⁴，则纸面上得到
\[
 |H(D)|\le\frac2D+\frac{C(L+1)}{L^4}
           \le\frac2D+\frac{2C}{L^3}.
\]
由 L³/D→0，存在 D₀，使全部 D≥D₀ 满足
|H(D)|≤(2C+1)/L³。因此完整普通 Mertens 供应足以支付 p>1 的调和衰减；
无需额外假设 H 的无穷极限等于零。
本节的有限双曲线转移及最终组合仍待真实编译。

### 473.3 接入 Robin 的具体意义与剩余目标

σ=1 的有限逆递归保留 2^{-K}G₁(⌊N/2^K⌋)，且已有全 N 界 |G₁(N)|≤4。
在长尺度上取约一半的二进制深度，可同时保持前段商截断至少为 √N 量级，并把余项压到
O(N^{-1/2})。因而完整 H 的对数幂衰减可传给同一个实际奇数调和和 G₁。
这条组合正在形式化，不能把其待编译结论记为既成 Lean 定理。

已严格编译的实际 Robin 解析单元给出整个高区间积分的真实导数、物理低高分拆、
二倍增长权导数，以及在明确 G₁ 对数幂衰减前提下的完整自然尾和 clipped 配对极限。
支付该算术前提可关闭固定 x 的收敛链；RH 所需临界尺度上的统一有符号补偿仍是另一项证明目标。

## 追加锚（本行以下为增补区）

## 474. 已支付的调和衰减与仍保留锚点的共同尺度

本节增补 §473 的编译边界，不改写旧章。全 Möbius 调和和的二阶对数衰减及其
奇数部分的二阶衰减，现在已分别通过本地严格 Lean 内核验收。这里的“本地验收”
与经 canonical 报告、冻结及 PR 交付是不同事实；新供应链尚待完成后者。
本节新的中心化尺度估计仍是纸面推导，尚未另行编译。

### 474.1 从完整商族到同一个实际奇数和

沿用 $H=H_1$、$H_o=G_1$。本地已验收的结果为

$$
\begin{aligned}
&\exists C_2>0,\ N_2\in\mathbb N,\quad
  \forall N\ge N_2,\quad |H(N)|\le \frac{C_2}{(\log N)^2},\\
&\exists A>0,\ D_0\in\mathbb N,\quad
  \forall N\ge D_0,\quad |H_o(N)|\le \frac{A}{(\log N)^2}.
\end{aligned}
$$

两者不含 RH 或调用者提供的抵消假设。第一步消费普通 Mertens 四阶对数供应，
保留有限双曲线恒等式的全部商截断与有符号取整误差。第二步消费实际二倍递归，
保留所有 $\lfloor N/2^a\rfloor$ 和有限余项；选取约一半的二进制深度，
用全 $N$ 的 $|H_o(N)|\le4$ 支付不超过 $8/\sqrt N$ 的余项。
本地验收的是上述二阶率；§473 所列更强三阶率仍只是纸面候选。

因此同一个 $A,D_0$ 可以先于全部 Robin 参数 $x$ 和截断 $D$ 选定。
原配对宿主直接消费这条供应，已通过本地严格编译，去掉了完整 clipped 极限的
调用者衰减前提，同时保留旧三条结论和新合成的六条结论；其 canonical 交付仍待完成。

### 474.2 中心化保留的正是原有符号锚点

沿用原物理积分 $P_x(s)$ 和实际二倍增长权

$$
b_x(s)=s\bigl(P_x(s)-P_x(2s)\bigr).
$$

对 $x>1$、$\ell=\log x\ge1$，以及自然数 $D\ge D_0$、$x\le D$，
原自然截断为

$$
T_x(D,M)=\sum_{\substack{D<n\le M\\n\text{ 奇}}}
             \frac{\mu(n)}n b_x(n).
$$

记其自然截断极限为 $T_x(D)$，有符号锚点为
$\mathfrak a_x(D)=b_x(D+1)H_o(D)$。
完整有限 Abel 恒等式保留终端项；已验收的解析合同在实际二阶率下给出

$$
T_x(D)=-\mathfrak a_x(D)
       -\sum_{n>D}\bigl(b_x(n+1)-b_x(n)\bigr)H_o(n).
$$

这里绝对可和的是变差级数。原 Möbius 原子和采用自然有限截断的极限，
不据此声称原子级数绝对可和。令 $r=\log(D+1)\ge\ell$，其中心化预算为

$$
|T_x(D)+\mathfrak a_x(D)|
\le\frac{2A}{r}\left(\log\frac r\ell+1+\frac{21}{\ell}\right).
$$

这正是原完整变差预算 $4A\,\operatorname{tailBudget}(\ell,2,D+1)$，
没有更换权函数或删除锚点。

### 474.3 远截止能支付中心化误差，主体的符号仍需证明

以下是从同一预算推出的纸面估计。对 $r\ge\ell$，函数

$$
g_\ell(r)=\frac{\log(r/\ell)+1+21/\ell}{r},\qquad
g'_\ell(r)=-\frac{\log(r/\ell)+21/\ell}{r^2}\le0.
$$

故有共同上界

$$
|T_x(D)+\mathfrak a_x(D)|
\le A\left(\frac2{\log x}+\frac{42}{(\log x)^2}\right).
$$

此上界乘以 $\sqrt x\log x$ 不趋零；这只说明该上界尚未支付临界尺度，
不说明真实有符号尾发散。选择满足 $D(x)+1\ge\exp x$ 的远截止，则同一单调性给出

$$
|T_x(D(x))+\mathfrak a_x(D(x))|
\le\frac{2A(\log x+22)}x,
$$

于是

$$
\sqrt x\log x\,|T_x(D(x))+\mathfrak a_x(D(x))|\longrightarrow0.
$$

证明的最后一步是 $((\log x)^2+22\log x)/\sqrt x\to0$。
例如选 $D(x)=\max(D_0,\lceil\exp x\rceil)$，整数取整保持所需不等式。
这无需平方根级 Möbius 抵消；它用更远的截止支付中心化远尾，因而同时扩大了有限首部。
原尾本身还必须支付 $\sqrt x\log x\,|\mathfrak a_x(D(x))|$。
完整有限首部与实际锚点相对正储备的单向比较仍未完成，不能从这个中心化极限推出 RH。

这个进展具体化了等价形态之间的联系：二倍递归传递的是带明确余项的算术率，
Abel 变换把同一率变成完整变差预算，截止尺度决定预算是否适合最终归一化。
递归可逆、固定参数收敛、共同尺度误差和单向符号各有不同的证明义务。
Fibonacci 递归与五分类的启发应落实为这些可检查的传输与误差结构；
5040 的有限关卡本身仍不能代替无限部分的符号证明。

## 追加锚（本行以下为增补区）

## 475. 支付有符号锚点后，整个原远尾已达到共同临界尺度

**符号约定。** 沿用 §474 的实际原配对、二倍权函数与奇数调和二阶率。
本节估计原远尾及其有符号锚点，不以 RH 为假设。

### 475.1 同一个全局算术常数支付锚点和变差

仍用实际奇数调和和 $H_o$、物理积分 $P_x$ 与二倍权

$$
b_x(s)=s\bigl(P_x(s)-P_x(2s)\bigr).
$$

对自然截断原和定义

$$
T_x(D)=\lim_{M\to\infty}
\sum_{\substack{D<n\le M\\n\text{ 奇}}}\frac{\mu(n)}n b_x(n).
$$

此极限的存在由完整自然尾合同保证；绝对可和的是 signed variation 级数。
沿用已支付的全局奇数调和二阶率，选 $A>0$ 与自然数 $D_0$，使
所有 $n\ge D_0$ 满足 $|H_o(n)|\le A/(\log n)^2$。
它们先于参数 $x$ 和自然截断 $D$ 选定。

**命题 475.1（实际锚点与完整远尾）。** 可以选择这样的 $A,D_0$，使对所有
$x>1$、$\log x\ge1$、$x\le D$、$D_0\le D$ 及 $e^x\le D+1$，记
$r=\log(D+1)$，有

$$
\begin{aligned}
|b_x(D+1)|&\le r(2\log r+13),\\
|b_x(D+1)H_o(D)|&\le\frac{A(8\log x+52)}x,\\
|T_x(D)|&\le\frac{A(10\log x+96)}x.
\end{aligned}
$$

证明中完整保留二倍物理分拆的 $1/2$ 和实际高余项。其低原函数与高余项预算给出
第一式。由 $D+1\le2D$ 及 $\log D\ge1$，有 $r\le2\log D$，故

$$
|H_o(D)|\le\frac{4A}{r^2},\qquad
|b_x(D+1)H_o(D)|\le\frac{4A(2\log r+13)}r.
$$

对于 $c\ge1$ 和 $1\le x\le r$，已证明

$$
\frac{\log r+c}{r}\le\frac{\log x+c}{x}.
$$

取 $c=13/2$ 支付锚点。另一方面，原中心化预算在同一截止下给出

$$
|T_x(D)+b_x(D+1)H_o(D)|\le\frac{2A(\log x+22)}x.
$$

将两个实际预算相加得到第三式。这一步控制整个远尾，无需改变 $b_x$，
也没有把有符号锚点删掉或预设它有利于 Robin 不等式。

### 475.2 真实整数截止上的共同临界极限

取与上述 $D_0$ 相同的自然截止

$$
D(x)=\max\bigl(D_0,\lceil e^x\rceil\bigr).
$$

**命题 475.2（整个远尾的临界极限）。** 对这同一选择，有

$$
\sqrt x\log x\,|T_x(D(x))|\longrightarrow0
\qquad(x\to+\infty).
$$

证明保留真实自然数上取整；$e^x\le D(x)$ 及 $x\le e^x$ 支付截止前提。
当 $x$ 足够大时，命题 475.1 给出

$$
0\le\sqrt x\log x\,|T_x(D(x))|
\le A\frac{10(\log x)^2+96\log x}{\sqrt x}\longrightarrow0.
$$

这里同时趋向无穷的是参数 $x$ 和截止 $D(x)$；上述同一截止的显式上界给出对角极限。

### 475.3 剥离形态传递同一信息，截止把困难移入有限首部

二倍剥离把完整 Möbius 调和和的二阶对数率传给实际奇数和，保留有限递归余项；
Abel 变换再把同一个率传给原权函数的变差和有符号端点。
远截止使这些预算适合 $\sqrt x\log x$ 归一化，因而无需先假定平方根级 Möbius 抵消。
这些是同一算术信息经过不同变换后的可核查关系，具体支持“等价形态之间有关联”的直觉。

但较远截止同时扩大了原有限首部。精确分拆仍是

$$
\lim_{M\to\infty}\sum_{\substack{1\le n\le M\\n\text{ 奇}}}
\frac{\mu(n)}n b_x(n)
=\sum_{\substack{1\le n\le D(x)\\n\text{ 奇}}}\frac{\mu(n)}n b_x(n)+T_x(D(x)).
$$

完整有限首部与原正储备的单向比较尚未证明；若改用 clipped 首部，还须支付同一
$D(x)$ 上的 diagonal collar，而固定 $x$ 的 collar 极限不自动完成这项义务。
5040 的有限反例关卡与 Fibonacci 递归的结构启发，应继续落实为实际算术桥及完整余项，
不能从数值重合推出首部符号。最终 Robin 不等式与 RH 仍未证明。

## 追加锚（本行以下为增补区）

## 476. 同一远截止也支付了真实奇数窗口的 clipping 边界

**符号约定。** 沿用 §475 的实际原远尾与自然截止。
本节的统一增长预算与有符号裁剪边界估计使用同一个自然阈值。

### 476.1 增长阈值必须先于全部参数选择

记实际低原函数与完整高余项之和为 $G_\ell(r)=L_\ell(r)+E(r)$，
沿用原变差预算中的实际 $\operatorname{majorant}(\ell,r)$。
对全部 $1\le\ell\le r$，有

$$
|G_\ell(r)|\le r(\log r+7),\qquad
|\operatorname{majorant}(\ell,r)|\le\log r+11.
$$

由 $(\log r+11)/r^{1/4}\to0$，可以选择一个与 $\ell,x$ 无关的 $R_0\ge1$，
使对全部 $\ell\ge1$ 和 $r\ge\max(R_0,\ell)$，有

$$
|G_\ell(r)|\le r^{5/4},\qquad
|\operatorname{majorant}(\ell,r)|\le r^{1/4}.
$$

第二式也给出旧完整 collar 合同需要的较粗 $r^{5/4}$ 预算。
这里共享的是先选定的 $R_0$；不能分别给每个固定 $x$ 找一个阈值，再据此宣称统一估计。

### 476.2 实际 floor 窗口与临界归一化

对原物理积分 $P_x$ 定义完整有符号 collar

$$
C_x(N)=\sum_{\substack{1\le m\le N\\m\text{ 奇}\\\lfloor N/2\rfloor<m}}
\mu(m)\bigl(P_x(2m)-P_x(N+1)\bigr).
$$

完整有限配对恒等式已保留

$$
\operatorname{clippedCutoff}_x(N)-\operatorname{naturalCutoff}_x(0,N)=C_x(N).
$$

**命题 476.1（共同截止上的实际边界）。** 可以选择同一实际奇数调和率的
$A>0,D_0\in\mathbb N$，使对 $D(x)=\max(D_0,\lceil e^x\rceil)$，当 $x$ 足够大时，

$$
|C_x(D(x))|
\le4A\bigl(2+4\cdot2^{5/4}\bigr)x^{-3/4}.
$$

因而

$$
\begin{aligned}
\sqrt x\log x\,|C_x(D(x))|&\longrightarrow0,\\
\sqrt x\log x\,
|\operatorname{clippedCutoff}_x(D(x))-
  \operatorname{naturalCutoff}_x(0,D(x))|&\longrightarrow0.
\end{aligned}
$$

证明使用原完整 collar 合同的 $p=2,q=5/4$。取 $N=D(x)$、$k=\lfloor N/2\rfloor$，
整数除法给出 $N\le2k+1$；当 $N\ge8$ 时，$N\le k^2$，所以

$$
x\le\log N\le2\log k.
$$

再由 $\log x\le x/2$、$x\ge2R_0$ 及固定 $D_0$，得到实际窗口前提
$D_0<k$、$x\le k$ 和 $\max(R_0,\log x)\le\log k$。
因此原奇数和、两个真实端点以及整个 $\lfloor N/2\rfloor<m\le N$ 窗口均进入预算，
并得到 $(\log N)^{-3/4}\le x^{-3/4}$。乘临界因子后，上界为常数倍
$\log x/x^{1/4}$，它趋于零。

### 476.3 任意固定阈值接口保证可以共用原远尾的见证

对每个固定自然数 $D_*$，同样的两个临界极限成立，截止均为
$\max(D_*,\lceil e^x\rceil)$。理由是任意两个固定阈值的 max 截止最终都等于
$\lceil e^x\rceil$；这是保留实际取整后的 eventual equality。

于是可以直接采用 §475 原远尾定理选出的 $D_0$。没有把两个独立存在式的隐藏见证
假定成相等，也没有用 fixed-$x$ 收敛替代 diagonal 极限。
整个原远尾与真实 clipping 边界现在都在同一临界尺度上趋零。
扩大后的有限首部与原正储备的单向比较，以及该标量与实际整数 Robin margin 的完整连接，
仍须证明；这两个消失的误差项本身不推出 RH。

## 追加锚（本行以下为增补区）

## 477. 原有限首部的锚点把平滑修正压缩为两个实际矩

**符号约定。** 沿用 §§85、87、424、475、476 的实际素数层、无附加整数约束的压力、阶乘核与有限配对。

### 477.1 实际素数层共享收益坐标，价格切线带有两个不同修正

对素数 $p$ 和正层号 $j$，定义实际插入收益与价格

$$
\beta(p,j)=\log\left(1+\frac1{p+p^2+\cdots+p^j}\right),\qquad
\theta(p,j)=\frac{\beta(p,j)}{\log p}.
$$

对于 $n=\prod_p p^{a_p}\ge1$，全部指数层的质量与收益分别为

$$
E(n)=\sum_p\sum_{j=1}^{a_p}\log p=\log n,\qquad
W(n)=\sum_p\sum_{j=1}^{a_p}\beta(p,j)=\log\frac{\sigma(n)}n.
$$

这些已有关系由素因数分解与逐素数层的望远镜恒等式给出；求和只有有限支撑。

沿用 §85 的压力 $M(\lambda)=\max_{n\ge1}(W(n)-\lambda E(n))$，其中 $\lambda>0$。
对 $u,x>1$，定义 $h(u)=\gamma+\log\log u$、$\lambda_x=1/(x\log x)$，并记

$$
\begin{aligned}
\Delta(x)&=h(x)-\lambda_xx-M(\lambda_x),\\
d_x(n)&=M(\lambda_x)-\bigl(W(n)-\lambda_xE(n)\bigr),\\
B_h(E,x)&=h(x)+\lambda_x(E-x)-h(E).
\end{aligned}
$$

对于 $E(n)>1$，原余量恒等式在同一坐标下写为

$$
h(E(n))-W(n)=\Delta(x)+d_x(n)-B_h(E(n),x),\qquad d_x(n),B_h(E(n),x)\ge0.
$$

**证明。** 代入上述定义后，压力、价格项与 $h(x)$ 相消，得到等式。
最大值的定义给出 $d_x(n)\ge0$；由
$h'(x)=\lambda_x$ 与 $h''(x)=-(1+\log x)/(x^2(\log x)^2)<0$，凹函数的切线不等式给出
$B_h(E(n),x)\ge0$。取 $x=E(n)=\log n$ 时，$B_h(E(n),x)=0$。
$d_x(n)=0$ 则要求 $n$ 在同一价格 $\lambda_x$ 下达到压力的最大值。
这复用原余量的精确三项修正及 §87 的压力定义。$\square$

### 477.2 保留 N+1 锚点的有限重构

**定义。** 使用同一个阶乘核
$\eta(y)=\log(\lfloor y\rfloor!)-y\log y+y$，其中 $y>0$。对 $N\ge1$，记

$$
\begin{aligned}
H_N&=\sum_{m=1}^N\frac{\mu(m)}m,&
L_N&=\sum_{m=1}^N\frac{\mu(m)\log m}m,&
M_N&=\sum_{m=1}^N\mu(m),\\
h_N&=H_N-\frac{M_N}{N+1},&
\ell_N&=L_N-\frac{M_N\log(N+1)}{N+1},\\
C_N(t)&=\sum_{m=1}^N\mu(m)\eta(t/m)-M_N\eta(t/(N+1)).
\end{aligned}
$$

**命题 477.1（双锚定矩的有限重构）。** 对全部 $0<t\le N+1$，有

$$
C_N(t)=\psi(t)-t(\log t-1)h_N+t\ell_N.
$$

**证明。** 这里 $\psi(t)=\sum_{1\le r\le\lfloor t\rfloor}\Lambda(r)$ 是实际 Chebyshev 函数。
复用有限 Dirichlet 卷积 $\mu*\log=\Lambda$，有

$$
\begin{aligned}
\psi(t)
&=\sum_{1\le r\le\lfloor t\rfloor}\sum_{m\mid r}\mu(m)\log(r/m)\\
&=\sum_{1\le m\le\lfloor t\rfloor}\mu(m)
  \sum_{1\le k\le\lfloor t/m\rfloor}\log k
=\sum_{1\le m\le\lfloor t\rfloor}\mu(m)\log(\lfloor t/m\rfloor!).
\end{aligned}
$$

当 $t\le N+1$ 时，可将其截在 $N$：$m>t$ 时只有 $\log(0!)=0$，
可能遗漏的端点 $m=t=N+1$ 也只有 $\log(1!)=0$。
锚点 $t/(N+1)\le1$ 的阶乘对数同样为零。展开原 $\eta$，得到

$$
\begin{aligned}
\sum_{m=1}^N\mu(m)\eta(t/m)
 &=\psi(t)-t(\log t-1)H_N+tL_N,\\
-M_N\eta(t/(N+1))
 &=\frac{M_Nt}{N+1}\bigl(\log t-\log(N+1)-1\bigr).
\end{aligned}
$$

相加即得结论，包含 $t=N+1$。$\square$

**定义与等价矩表示。** 在逆尺度坐标 $a>0$ 上定义有限有符号测度

$$
\nu_N=\sum_{m=1}^N\mu(m)\delta_{1/m}-M_N\delta_{1/(N+1)}.
$$

由点质量的定义，直接得到

$$
\int d\nu_N=0,\qquad
\int a\,d\nu_N=h_N,\qquad
\int a\log a\,d\nu_N=-\ell_N,
\qquad C_N(t)=\int\eta(ta)\,d\nu_N(a).
$$

缩放后的平滑核为 $-ta\log(ta)+ta$，其积分正是
$-t(\log t-1)h_N+t\ell_N$。因此平滑修正处于 $t$ 与 $t\log t$ 的线性包络中。
总质量为零不使两个加权矩为零；两个 $N+1$ 锚定修正均保留在上式中。

### 477.3 两个矩的完整修正具有显式原函数

**定义。** 沿用实际物理权 $w(t)=(1+\log t)/(t^2(\log t)^2)$。
对 $u>0$，定义

$$
F_N(u)=(1+\ell_N)\left(\log u-\frac1u\right)
-h_N\left(u+\frac1u\right).
$$

**命题 477.2（完整平滑修正的积分）。** 对 $1<x\le N+1$，有

$$
\int_x^{N+1}t\bigl[1-(\log t-1)h_N+\ell_N\bigr]w(t)\,dt
=F_N(\log(N+1))-F_N(\log x).
$$

**证明。** 直接求导给出

$$
F_N'(u)=\frac{1+u}{u^2}\bigl[1+\ell_N-(u-1)h_N\bigr].
$$

链式法则于是给出
$\frac d{dt}F_N(\log t)=t[1-(\log t-1)h_N+\ell_N]w(t)$，其中 $t>1$。
在 $[x,N+1]$ 上应用微积分基本定理即得结论。$\square$

**假设（完整无穷配对的身份）。** 若要将上述有限配对用于整个无穷物理积分，
须另有相应积分与极限的存在性，以及身份

$$
\lim_{N\to\infty}H_N=0,\qquad
\lim_{N\to\infty}L_N=-1,\qquad
\lim_{N\to\infty}\int_x^\infty C_N(t)w(t)\,dt
=\int_x^\infty(\psi(t)-t)w(t)\,dt.
$$

有限重构在物理分拆中仍保留 $t>N+1$ 的积分补区。
本节的有限恒等式及原函数未以两个矩替代这个补区，也未假定完整首部相对于 §87 正储备的符号。

### 477.4 两个锚定矩是同一平滑核缩放作用的矩阵坐标

**定义。** 记 $S(t)=t\log t-t$，其中 $t>0$，并固定函数空间
$V=\operatorname{span}_{\mathbb R}\{t\log t,t\}$。
使用经典正缩放作用 $f(t)\mapsto f(at)$，其中 $a>0$。在函数值列向量
$\mathbf v(t)=(t\log t,t)^{\mathsf T}$ 上，记

$$
R(a)=\begin{pmatrix}a&a\log a\\0&a\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\0&0\end{pmatrix}.
$$

**命题 477.3（原平滑核的缩放矩表示）。** $S$ 的全部正缩放的线性包络恰为 $V$，
且实际锚定测度满足

$$
\mathbf v(at)=R(a)\mathbf v(t),\qquad
R(a)R(b)=R(ab),\qquad R(1)=I,
$$

$$
\int R(a)\,d\nu_N(a)
=\begin{pmatrix}h_N&-\ell_N\\0&h_N\end{pmatrix},\qquad
\int S(at)\,d\nu_N(a)=t\log t\,h_N-t(h_N+\ell_N).
$$

因此对 $0<t\le N+1$，命题 477.1 等价地写成

$$
C_N(t)=\psi(t)-t\log t\,h_N+t(h_N+\ell_N).
$$

若另有 $h_N\to0$ 与 $\ell_N\to-1$，则平均矩阵趋向 $J$，
对每个固定 $t>0$ 有 $C_N(t)\to\psi(t)-t$。

**证明。** 由 $\log(at)=\log a+\log t$，有
$S(at)=aS(t)+a\log a\,t$，所以缩放包络包含于 $V$。
若 $c\,t\log t+d\,t=0$ 对全部 $t>0$ 成立，取 $t=1$ 得 $d=0$，再取 $t=e$ 得 $c=0$。
此外 $S(et)/e-S(t)=t$，故两种独立模式均在缩放包络内，维数恰为二。

函数值的矩阵恒等式直接来自对数乘法公式；同一公式给出矩阵乘法关系。
$\det R(a)=a^2>0$，所以 $R(a)^{-1}=R(1/a)$。
对实际 $\nu_N$ 逐项积分，并使用 $\int a\,d\nu_N=h_N$ 与
$\int a\log a\,d\nu_N=-\ell_N$，得到平均矩阵。
左乘行向量 $(1,-1)$ 再作用于 $\mathbf v(t)$，即得 $S$ 的积分式。
最后使用命题 477.1；固定 $t$ 时最终有 $t\le N+1$，所以两个矩的假设极限给出所示极限。
这一步仅是逐点极限，未交换无穷积分。$\square$

**矩阵不变量。** 对 $a=e^u$，有经典表示
$R(e^u)=e^u(I+uJ)$，其中 $J^2=0$。
Fibonacci 递推矩阵 $Q=\begin{pmatrix}1&1\\1&0\end{pmatrix}$ 的行列式为 $-1$，
而 $R(a)$ 的行列式为 $a^2>0$；相似变换保留行列式，故两者不相似。
等价地，$Q$ 的特征判别式为 $5$，$R(a)$ 的特征判别式为 $0$。
上式给出了原平滑核的具体缩放作用；它没有给出这个作用与 Fibonacci 递推的同构。

## 追加锚（本行以下为增补区）
