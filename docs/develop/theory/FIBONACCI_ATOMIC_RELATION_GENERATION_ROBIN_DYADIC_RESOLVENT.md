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

## 478. 锚定 Mellin 一阶资料与递归的两种效应

### 478.1. 两个矩来自同一个有限变换

沿用第 477 节的实际有限量，令 $N\ge1$，

$$
\begin{aligned}
M_N&=\sum_{m=1}^N\mu(m),&
H_N&=\sum_{m=1}^N\frac{\mu(m)}m,&
L_N&=\sum_{m=1}^N\frac{\mu(m)\log m}m,\\
h_N&=H_N-\frac{M_N}{N+1},&
\ell_N&=L_N-\frac{M_N\log(N+1)}{N+1}.
\end{aligned}
$$

在正尺度上取同一锚定有符号测度

$$
\nu_N=\sum_{m=1}^N\mu(m)\delta_{1/m}-M_N\delta_{1/(N+1)},
\qquad
\Phi_N(s)=\int a^s\,d\nu_N(a).
$$

这里 $a^s=\exp(s\log a)$，故有限和 $\Phi_N$ 对复变量 $s$ 是整函数。
实数限制与通常实幂一致。

**命题 478.1（实际锚定变换的三个读数）。**

$$
\Phi_N(0)=0,\qquad \Phi_N(1)=h_N,\qquad \Phi_N'(1)=-\ell_N.
$$

证明。第一式是 $M_N-M_N=0$。第二式直接代入 $s=1$。
逐项求导得到

$$
\Phi_N'(s)=-\sum_{m=1}^N\mu(m)\log m\,m^{-s}
 +M_N\log(N+1)(N+1)^{-s},
$$

于是第三式成立。总质量消去是 $s=0$ 的读数，而阶乘平滑项使用 $s=1$
的值与导数；前一读数本身不约束后两个读数。

令 $J=\begin{pmatrix}0&1\\0&0\end{pmatrix}$。第 477 节的尺度表示满足

$$
R(a)=a(I+\log a\,J)=a^{I+J},\qquad J^2=0,
$$

从而

$$
\int R(a)\,d\nu_N(a)=\Phi_N(1)I+\Phi_N'(1)J
 =h_NI-\ell_NJ.
$$

这就是解析函数在二阶 Jordan 块上的一阶函数演算。
两个实际算术矩是同一 Mellin 变换在 $1$ 的一阶资料。

### 478.2. 尺度群、有限卷积与截断族的边界

对正尺度上的任意有限支撑有符号离散测度 $\nu$，定义

$$
(T_\nu f)(t)=\int f(at)\,d\nu(a),\qquad
\Phi_\nu(s)=\int a^s\,d\nu(a).
$$

**命题 478.2（有限递归的准确乘法）。** 若 $\omega$ 也是有限支撑有符号离散测度，且 $\nu\star_\times\omega$
是有限乘法卷积，即将 $\nu\otimes\omega$ 经 $(a,b)\mapsto ab$ 推前，则

$$
T_\nu T_\omega=T_{\nu\star_\times\omega},\qquad
\Phi_{\nu\star_\times\omega}(s)=\Phi_\nu(s)\Phi_\omega(s).
$$

在 $V=\operatorname{span}\{t\log t,t\}$ 上，若
$\mathcal J(\Phi)=\Phi(1)I+\Phi'(1)J$，则

$$
\mathcal J(\Phi\Psi)=\mathcal J(\Phi)\mathcal J(\Psi).
$$

证明。所有积分都是有限和，双重求和与 $(ab)^s=a^sb^s$ 给出前两式。
后一式由乘积求导法则和 $J^2=0$ 给出。

特别地，实际锚定测度的两次作用在 $V$ 上对应

$$
(h_NI-\ell_NJ)(h_MI-\ell_MJ)
=h_Nh_MI-(h_N\ell_M+\ell_Nh_M)J.
$$

正尺度本身组成群，因为 $R(a)R(b)=R(ab)$ 且 $R(a)$ 可逆。
有符号平均却可能不可逆；实际极限矩阵 $J$ 就是一个例子。
有限乘法卷积还会产生 $1/(mn)$ 等新支点，因而 $\nu_N\star_\times\nu_M$
一般不属于原来单一自然截断的 $\nu_K$ 族。
递归具有准确的卷积乘法，但不能据此任意替换自然截断、端点或锚。

### 478.3. 极点归一化支付平滑主项

在 $\operatorname{Re}s>1$，实际 Möbius Dirichlet 级数绝对收敛并满足

$$
\sum_{m\ge1}\mu(m)m^{-s}=\frac1{\zeta(s)}.
$$

由 $|M_N|\le N$，锚的绝对值不超过 $N/(N+1)^{\operatorname{Re}s}$，趋于零。
因此 $\Phi_N$ 在这个半平面逐点趋于实际倒数 zeta。
这一步没有把收敛域扩展到边界 $s=1$。

实际 zeta 在 $1$ 的留数为一。其局部形式是

$$
\zeta(s)=\frac1{s-1}+g(s),\qquad
Z(s)=\frac{s-1}{1+(s-1)g(s)},
$$

其中 $g$ 在 $1$ 附近解析，$Z$ 是倒数的全纯延拓，满足
$Z(1)=0$、$Z'(1)=1$。这里延拓的值不依赖在极点处为原函数指定的总化取值。

若实际算术边界极限 $h_N\to0$、$\ell_N\to-1$ 已独立建立，则

$$
h_NI-\ell_NJ\longrightarrow J.
$$

对 $S(t)=t\log t-t$，这给出 $T_{\nu_N}S(t)\to t$。
因此原有限阶乘重构

$$
\sum_{m=1}^N\mu(m)\eta(t/m)-M_N\eta(t/(N+1))
=\psi(t)-t(\log t-1)h_N+t\ell_N,
\qquad 0<t\le N+1,
$$

在每个固定 $t>0$ 趋于 $\psi(t)-t$。
全物理积分的识别还使用完整有符号块的 $L^1$ 可求和性及几乎处处识别；
有限重构与局部 Mellin 资料本身没有支付这个积分交换。

### 478.4. 递归消去平滑模式，同时提高其它奇点的阶

**命题 478.4（有限二次作用的平滑消去）。**
若 $h_N\to0$ 且 $\ell_N\to-1$，则对每个固定 $f\in V$，

$$
T_{\nu_N}T_{\nu_N}f(t)\longrightarrow0.
$$

证明。有限二次作用的矩阵为 $h_N^2I-2h_N\ell_NJ$，其两个系数均趋于零。
例如

$$
T_{\nu_N}^2S(t)=h_N^2S(t)-2h_N\ell_Nt.
$$

这个有限结论只涉及固定平滑空间 $V$。
若改看未锚定 Möbius 算子在绝对收敛半平面的 $r$ 次 Dirichlet 卷积，
其乘子是 $Z(s)^r=\zeta(s)^{-r}$。
它在 $s=1$ 有 $r$ 阶零，因而 $r\ge2$ 时在 $1$ 的值和一阶导数都消去。
与此同时，若实际 zeta 在 $\rho\ne1$ 有 $q$ 阶零，写成
$\zeta(s)=(s-\rho)^q u(s)$ 且 $u(\rho)\ne0$，则

$$
Z(s)^r=(s-\rho)^{-rq}u(s)^{-r}
$$

在 $\rho$ 有 $rq$ 阶极点。
所以改善极点 $1$ 所对应的平滑主项消去，并不自动改善其它零点附近的解析控制。
有限锚定算子的临界尺度界仍须保留其实际积分核、截断和所有端点。

素数原子也记录了同一递归：令 $\mu^{\star r}$ 是 $r$ 次 Dirichlet 卷积，则

$$
\sum_{k\ge0}\mu^{\star r}(p^k)z^k=(1-z)^r,\qquad
\mu^{\star r}(p^k)=
\begin{cases}(-1)^k\binom rk,&0\le k\le r,\\0,&k>r.\end{cases}
$$

证明。素数幂上的原 Möbius 系数为 $(1,-1,0,\ldots)$，
有限卷积就是相应多项式相乘，最后使用二项式定理。
这是卷积次数产生的二项式递归；它没有给出 Fibonacci 权重、五分类或 $5040$
与 zeta 零点之间的新恒等式。

本节使用通常的 Mellin 变换、有限乘法卷积与 Jordan 函数演算。
Möbius Dirichlet 级数与卷积乘积的标准供应分别是 Mathlib 的
`ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius`、
`ArithmeticFunction.LSeries_zeta_eq_riemannZeta` 和 `LSeries_convolution'`；
实际留数由 `riemannZeta_residue_one` 表达。
全物理积分与整数 Robin margin 的有限素数幂连接，以及完整有限首部的单向符号，
仍是后续需要支付的数学结论。

## 追加锚（本行以下为增补区）

## 479. 有符号阶乘配对、素数幂边界与同一个物理积分

### 479.1. 原积分核与完整块级数

取 $x>1$，沿用实际阶乘余项与原权重

$$
\eta(u)=\log(\lfloor u\rfloor!)-u\log u+u,
\qquad
w(t)=\frac{1+\log t}{t^2(\log t)^2},
\qquad
P_x(s)=\int_x^\infty\eta(t/s)w(t)\,dt.
$$

令 $M_m=\sum_{a=1}^m\mu(a)$、$\psi(t)=\sum_{n\le t}\Lambda(n)$，并记

$$
B_m(t)=M_m\bigl[\eta(t/m)-\eta(t/(m+1))\bigr]w(t),
\qquad
I_\psi(x)=\int_x^\infty(\psi(t)-t)w(t)\,dt.
$$

**命题 479.1（完整物理配对）。** 对每个 $x>1$，
$(\psi(t)-t)w(t)$ 在 $(x,\infty)$ 可积，而且

$$
\sum_{m=1}^\infty M_m\bigl[P_x(m)-P_x(m+1)\bigr]=I_\psi(x).
$$

证明。完整块预算给出

$$
\sum_{m=1}^\infty\int_x^\infty |B_m(t)|\,dt<\infty.
$$

因此 $\sum_m B_m$ 在 $L^1(x,\infty)$ 收敛，且几乎处处有与之相容的点态级数和。
有限 Abel 配对及第 477 节的精确阶乘重构给出

$$
\sum_{m=1}^N B_m(t)
=\bigl[\psi(t)-t(\log t-1)h_N+t\ell_N\bigr]w(t),
\qquad 0<t\le N+1.
$$

对每个固定 $t>0$，实际算术极限 $h_N\to0$、$\ell_N\to-1$
识别点态极限为 $(\psi(t)-t)w(t)$。
由 $L^1$ 极限的几乎处处识别及完整范数积分可求和性，可交换整个块级数与积分。
第一物理项 $m=1$ 的可积性独立成立，后续项也完整保留。
逐块积分便得到所述等式。

这个证明支付的是配对块的绝对积分预算，未把未配对的 Möbius 原子级数宣告为绝对收敛。
原有限自然首部与有符号尾项的共同极限，因而具有实际值 $I_\psi(x)$。
在原全局阈值、$\log x\ge1$ 及 $x\le D$ 条件下，第 475 节的完整自然分解满足

$$
\operatorname{naturalCutoff}_x(0,D)+\operatorname{tail}_x(D)=I_\psi(x).
$$

这里尾项仍含原有符号锚，等式没有给有限首部任何单向符号。

### 479.2. 素数幂公式的全部端点

定义

$$
P_0(x)=\sum_{1\le n\le x}\frac{\Lambda(n)}{n\log n}
=\sum_{\substack{p\ {\rm prime},\ k\ge1\\p^k\le x}}\frac1{kp^k},
\qquad x>1.
$$

第一式的 $n=1$ 项约定为零，与 $\Lambda(1)=0$ 一致。
第二式是完整有限素数幂重排，包含 $p^k=x$ 的边界项；
指数范围可取 $1\le k\le\lfloor\log x/\log2\rfloor$。

取实际 Euler 常数 $\gamma$，定义

$$
\Phi(x)=\gamma+\log\log x-P_0(x)
 +\frac{\psi(x)-x}{x\log x}.
$$

**命题 479.2（有限窗与无限边界的同一公式）。** 对全部 $1<x\le y$，

$$
\int_{(x,y]}(\psi(t)-t)w(t)\,dt=\Phi(x)-\Phi(y),
\qquad
\Phi(x)=I_\psi(x).
$$

证明。对 $v(t)=1/(t\log t)$ 使用完整有限 Abel 求和，因 $v'(t)=-w(t)$，得到

$$
P_0(y)-P_0(x)
=\frac{\psi(y)}{y\log y}-\frac{\psi(x)}{x\log x}
 +\int_{(x,y]}\psi(t)w(t)\,dt.
$$

平滑主项的原函数为 $\log\log t-1/\log t$，即

$$
\int_{(x,y]}t w(t)\,dt
=\left[\log\log t-\frac1{\log t}\right]_x^y.
$$

两式相减即得有限窗恒等式，包括 $x=y$ 及两端的完整素数幂约定。
原 Mertens 误差 $P_0(y)-\log\log y-\gamma$ 趋于零。
实际线性 Chebyshev 界 $0\le\psi(y)\le Cy$ 给出

$$
\left|\frac{\psi(y)-y}{y\log y}\right|\le\frac{C+1}{\log y}\longrightarrow0.
$$

故 $\Phi(y)\to0$。命题 479.1 的实际可积性允许完整有限物理窗趋于
$(x,\infty)$ 的积分，得到第二式。
这个上端点估计不要求额外的有效素数定理。

### 479.3. 原子跳跃在值中抵消，在斜率中保留

若 $q=p^k$ 是素数幂，则 $P_0$ 在 $q$ 的跳跃为 $1/(kq)$，
$\psi$ 的跳跃为 $\log p$。它们在 $\Phi$ 中贡献

$$
-\frac1{kq}+\frac{\log p}{q\log q}=0.
$$

因此实际素数幂阈值不会使 $\Phi$ 的值跳跃。
完整积分表示还说明 $\Phi$ 在 $(1,\infty)$ 连续。
在不含素数幂的开区间内，$\psi$ 为常数且

$$
\Phi'(t)=(t-\psi(t))w(t).
$$

素数原子仍改变这个斜率。连续性没有给出 $\Phi$ 的符号；
局部一个区间的斜率也没有支付整个无限有符号累积。

结合第 475、476 节，完整尾项与对角 collar 的临界零极限现在可解释为同一
实际 $I_\psi(x)=\Phi(x)$ 的完整自然截断余项及两种截断之间的差。
完整整数 Robin margin 还含原离散储备、实际压力亏损与切线凹性修正。
它们与有限首部的单向比较仍需独立证明；本节的积分恒等式没有推出最终 Robin 不等式或 RH。

本节的有限 Abel 与素数幂重排使用实际 von Mangoldt 与 Chebyshev 对象。
Mertens 误差和 Euler 常数归一化沿用原 Mertens 供应；
锚定算术常数沿用 David Sanftenberg 的完整 Euler 修正与实际 harmonic 估计。

## 追加锚（本行以下为增补区）

## 480. 实际价格迭代的整除质量间隔与两种下降成本

### 480.1. 嵌套最优者的质量间隔

沿用第 98、112 节的完整正整数压力与严格正层最优整数 $n_x$，记

$$
E(n)=\log n,\quad W(n)=\log\frac{\sigma(n)}n,\quad
h(x)=\gamma+\log\log x,\quad \lambda_x=\frac1{x\log x},
$$

$$
M(\lambda)=\max_{n\ge1}\{W(n)-\lambda E(n)\},\quad
\Delta(x)=h(x)-\lambda_xx-M(\lambda_x),\quad F(x)=\log n_x.
$$

这里并列的零收益层全部省略。
若 $1<s<t$，严格活跃层集从 $s$ 到 $t$ 只增不减，故逐素数指数不减，得到

$$
n_s\mid n_t.
$$

若两整数不同，整除商为整数 $r\ge2$，因此

$$
\log n_t-\log n_s=\log r\ge\log2.
$$

这是实际嵌套层集的算术间隔。任意两个不同整数的对数并没有这个间隔，
例如 $\log(N+1)-\log N\to0$。

取一个已经证明对 $F$ 不变的区间 $[a,b]\subset(1,\infty)$，
从 $x_0\in[a,b]$ 开始递归 $x_{j+1}=F(x_j)$。
第 112 节已给出方向单调性及有限停机。
从 $j=1$ 起，每个状态都是实际最优整数的对数，故每次非恒定更新满足

$$
|x_{j+1}-x_j|\ge\log2.
$$

若第一次固定的指标为 $K\ge1$，单调望远镜求和给出

$$
(K-1)\log2\le|x_K-x_1|\le b-a,
\qquad
\boxed{K\le1+\left\lfloor\frac{b-a}{\log2}\right\rfloor.}
$$

同一个估计也直接排除无穷多次非恒定更新，而无需枚举整个激活层集。
任意实数初值到 $x_1$ 的第一步未计入质量间隔；
也没有断言第一个最优整数与提供该初值的任意整数之间存在整除关系。

### 480.2. 每一步保留切线成本与新价格亏损

对 $x,y>1$，定义

$$
B_h(y,x)=h(x)+\lambda_x(y-x)-h(y),\qquad
d_y(n)=M(\lambda_y)-[W(n)-\lambda_yE(n)].
$$

它们分别非负。把既有完整裕量身份用于 $y=F(x)>1$，旧价格下的最优性给出

$$
\boxed{\Delta(x)-\Delta(F(x))=B_h(F(x),x)+d_{F(x)}(n_x).}
$$

证明。旧尺度处
$\Delta(x)=h(x)+\lambda_x(F(x)-x)-W(n_x)$；
新尺度处
$\Delta(F(x))=h(F(x))-W(n_x)-d_{F(x)}(n_x)$。
两式相减。这是同一完整压力的切线主导更新；两个成本都保留在准确端点之间。

令 $w(t)=(1+\log t)/(t^2\log^2t)$。因为

$$
w'(t)=-\frac1{t^3}\left(\frac2{\log t}+\frac3{\log^2t}
+\frac2{\log^3t}\right)<0,
$$

对 $x,y\in[a,b]$，切线差的二阶积分余项给出

$$
B_h(y,x)\ge\frac{w(b)}2(y-x)^2.
$$

当 $y\ge x$ 时余项为 $\int_x^y(y-t)w(t)\,dt$；
当 $y\le x$ 时为 $\int_y^x(t-y)w(t)\,dt$。
逐点用 $w(t)\ge w(b)$ 即得两种方向的同一个估计。

因此从第一个整数对数状态开始，每次非恒定更新至少消耗
$c_b=w(b)(\log2)^2/2$ 的实际裕量。
对首次固定指标 $K\ge1$，完整求和为

$$
\Delta(x_1)-\Delta(x_K)
=\sum_{j=1}^{K-1}\bigl[B_h(x_{j+1},x_j)+d_{x_{j+1}}(n_{x_j})\bigr]
\ge(K-1)c_b.
$$

若另有同一区间的下界 $\Delta\ge L$，便得到
$(K-1)c_b\le\Delta(x_1)-L$。
这个成本估计没有给出正的 $L$。

### 480.3. 已有停机结论与仍需支付的符号

第 112 节的有限轨道、严格下降终点及并列绕越结论保持各自的原假设。
这里补充的是实际整除所强制的质量间隔，以及准确下降身份中的成本下界。
区间不变性、$n>5040$ 的边界、并列层与终端 Robin 裕量的符号仍须按原对象核对。
向较低裕量递归搜索的有限停机不推出这些裕量为正，也不提供无限整数域的共同覆盖。

## 追加锚（本行以下为增补区）

## 481. 完整实际整数的严格参考比较与储备零点

沿用 §§85、87、98 的全部正整数压力、参考素数幂前缀与价格。对 $x>1$ 置

$$
\lambda_x=\frac1{x\log x},\qquad
J_x(n)=\log\frac{\sigma(n)}n-\lambda_x\log n,\qquad
M(\lambda_x)=\max_{n\ge1}J_x(n),
$$

$$
F(x)=P(x)-\lambda_x\psi(x),\qquad
R(x)=F(x)-M(\lambda_x).
$$

这里的 $x$ 是实切线坐标，$n$ 是实际整数，二者不互换。$P$ 保留全部 $p^k\le x$ 的项 $1/(kp^k)$，$\psi$ 保留对应的 $\log p$。压力包含单位整数 $1$，其目标值为零。最大值存在性复用实际正价格目标的有限尾归约；当非单位最大值为负时，补入 $1$ 就给出完整正整数域的最大者。

**定理 481.1（非单位整数的严格整段比较）。** 对每个 $x>1$ 和每个整数 $n>1$，

$$
J_x(n)<F(x).
$$

**证明。** 写 $a_p=v_p(n)$，并沿用 §87 的

$$
Q_p(a)=\sum_{k=1}^a\frac1{kp^k},\qquad
G_p(a)=\sum_{k=0}^ap^{-k},\qquad
v_p(x)=\max\bigl(\{0\}\cup\{k\ge1:p^k\le x\}\bigr).
$$

实际分解给

$$
J_x(n)=\sum_{p\mid n}
\bigl(\log G_p(a_p)-\lambda_xa_p\log p\bigr).
$$

在 $n$ 的素因子与 $p\le x$ 的素数的有限并集上补零。对每个方向先用完整前缀比较，再用参考目标最大化：

$$
\log G_p(a_p)-\lambda_xa_p\log p
\le Q_p(a_p)-\lambda_xa_p\log p
\le Q_p(v_p(x))-\lambda_xv_p(x)\log p.
$$

$n>1$ 保证至少有一个素因子且其 $a_p\ge1$；§87.5 的严格前缀不等式使该方向的第一个比较严格。因此有限和严格小于参考最优值之和，即 $F(x)$。这一论证比较整个前缀，不要求实际边际逐层小于参考边际。$\square$

**定理 481.2（实际储备的准确零点集合）。** 对所有 $x>1$，

$$
\boxed{R(x)=0\iff x\le2,\qquad R(x)>0\iff x>2.}
$$

在 $1<x\le2$ 上，$M(\lambda_x)=0$，且实际唯一最大整数是 $1$。

**证明。** 若 $1<x<2$，参考没有素数幂，故 $F(x)=0$。在 $x=2$，唯一参考项的净收益为

$$
\frac12-\lambda_2\log2=0,
$$

所以仍有 $F(2)=0$。定理 481.1 给每个非单位整数的目标严格为负，而 $J_x(1)=0$，得到零压力、唯一最大者与零储备。

若 $x>2$，参考第一项 $1/2-\lambda_x\log2$ 严格为正，因为 $x\log x>2\log2$。参考其余已取增量都非负，因此 $F(x)>0$。取实际达到压力的整数 $n_x$。若 $n_x=1$，则 $R(x)=F(x)>0$；若 $n_x>1$，则由定理 481.1 得 $R(x)=F(x)-J_x(n_x)>0$。最大值实际达到是这一步的必要输入：所有离散候选各自严格低于某上界，并不能单凭严格性排除其上确界等于该上界。$\square$

本节接续 §477.2 的完整 Robin 裕量公式及 §479 的同一物理积分身份。对于 $n>5040$，记 $E=\log n$、$h(E)=\log\log E$、$d_x(n)=M(\lambda_x)-J_x(n)$，则准确关系仍是

$$
\gamma+h(E)-\log\frac{\sigma(n)}n
=I_\psi(x)+R(x)+d_x(n)-B_h(E,x),
$$

$$
B_h(E,x)=h(x)+\lambda_x(E-x)-h(E)\ge0.
$$

取 $x=E$ 时切线差为零而实际亏损保留。完整物理积分到实际整数裕量的恒等式已经明确；正储备的存在仍没有给出 $I_\psi+R$ 的单向符号比较。$x=2$ 的储备起点也没有把 $5040$、Fibonacci 来源或拓扑例外识别为同一个数学对象。

## 追加锚（本行以下为增补区）

## 482. 两个首素数边界与第一段准确储备平台

沿用同一实际压力，令实际事件阈值为

$$
\theta_{p,j}=\frac{\beta_{p,j}}{\log p},\qquad
\beta_{p,j}=\log\left(1+\frac1{p+\cdots+p^j}\right),
\qquad
\alpha=\frac{\log(3/2)}{\log2}.
$$

这些是 §85 的实际几何前缀事件，亦是 Robin1984 原始事件表示；不把参考项 $1/(jp^j)$ 当作实际收益。

**命题 482.1（完整正整数压力的首边界）。** 对每个正价格 $\lambda$，

$$
M(\lambda)=0\iff\lambda\ge\alpha.
$$

$\lambda>\alpha$ 时唯一最大整数是 $1$；$\lambda=\alpha$ 时最大整数恰为 $1,2$。

**证明。** 每个实际事件都有 $\theta_{p,j}\le\alpha$，等号恰在 $(p,j)=(2,1)$。同一素数增大层数严格扩大正分母，故阈值严格下降。对 $p>2$，第一层的正分子小于 $\log(3/2)$，正分母大于 $\log2$，故其商严格小于 $\alpha$。实际整数目标正是其有限事件包的净收益之和。

若 $\lambda>\alpha$，每个非单位整数至少含一个严格负事件，目标严格为负。若 $\lambda=\alpha$，唯一零事件为 $(2,1)$；空包和只含该事件的包分别实现 $1,2$，其余整数都含严格负事件。若 $0<\lambda<\alpha$，整数 $2$ 的目标为 $\log(3/2)-\lambda\log2>0$，故压力严格正。$\square$

**定理 482.2（首胞腔的全整数准确公式）。** 对全部 $1<x\le3$，

$$
\boxed{M(\lambda_x)=\max\{0,\log(3/2)-\lambda_x\log2\}.}
$$

**证明。** 对 $p\ge3$，第一层阈值至多 $\log(4/3)/\log3$，而严格对数上界给

$$
\frac{\log(4/3)}{\log3}<\frac1{3\log3}=\lambda_3.
$$

同一素数后续层只会降低阈值。对 $p=2,j\ge2$，

$$
\theta_{2,j}\le\frac{\log(7/6)}{\log2}
<\frac1{6\log2}<\frac1{3\log3}=\lambda_3;
$$

最后一步等价于 $\log3<2\log2$，来自 $3<4$。$x\le3$ 给 $\lambda_x\ge\lambda_3$，所以除 $(2,1)$ 外全部事件净收益严格负。任意实际整数的有限事件和至多为首事件净收益的正部；$1$ 和 $2$ 分别实现零与首事件收益，因此上界实际达到。$\square$

**推论 482.3（参考先起、实际后起、继而平台）。** 存在唯一 $x_c\in(2,3)$ 满足

$$
x_c\log x_c=\frac{\log2}{\log(3/2)}.
$$

在 $1<x\le3$ 上储备的准确分段公式是

$$
\boxed{
R(x)=
\begin{cases}
0,&1<x\le2,\\
\frac12-\lambda_x\log2,&2\le x\le x_c,\\
\frac12-\log(3/2),&x_c\le x\le3.
\end{cases}}
$$

在 $2<x<x_c$，实际最大整数仍唯一为 $1$，但储备严格为正；在 $x=x_c$，$1,2$ 并列且储备仍正；在 $x_c<x\le3$，唯一最大整数为 $2$，储备保持同一个正平台。

**证明。** $x\log x$ 在 $x>1$ 连续严格增加。严格对数界给

$$
\frac13<\log(3/2)<\frac12,
\qquad
\lambda_3\log2<\frac13<\log(3/2)<\lambda_2\log2,
$$

故唯一交点确在 $(2,3)$。对 $2\le x<3$，参考目标为 $F(x)=1/2-\lambda_x\log2$。在 $x=3$，新增素数 $3$ 的净收益 $1/3-\lambda_3\log3$ 恰为零，故同一表达式仍成立。减去定理 482.2 的准确压力，得到分段公式；严格对数上界保证平台高度 $1/2-\log(3/2)>0$。最大者的声明由其余全部事件严格为负得到。$\square$

这里显示的联系是同一素数坐标上的两种收益：参考首收益 $1/2$ 与实际首收益 $\log(3/2)$。二者不同，因而参考储备先出现，实际非单位配置稍后激活。平台来自同一价格惩罚的精确抵消，不是一个无穷尺度的正下界。

## 追加锚（本行以下为增补区）

## 483. 第一段实际储备下降区间

§87 已指出 $\log(7/6)>1/8$，所以完整前缀支配不等于边际逐层支配。§98 已给稳定胞腔的准确导数 $R'(x)=(\psi(x)-\log n_x)w(x)$；§238 已说明固定素数的正前缀差会随指数增加而减少。本节把这些既有事实落实到完整实际压力的一个明确开区间，不重新提出一般单调性定理。

令 $\tau\in(3,4)$ 是唯一满足

$$
\lambda_\tau=\frac{\log(7/6)}{\log2}
$$

的点。

**引理 483.1（第二个二幂事件的准确位置）。** 上述 $\tau$ 确实唯一位于 $(3,4)$，且素数 $3$ 的第一事件阈值严格高于 $\lambda_\tau$。

**证明。** §482 的比较给 $\lambda_\tau<\lambda_3$。严格下界 $\log(7/6)>1/7>1/8$ 给

$$
\lambda_\tau>\frac1{8\log2}=\lambda_4.
$$

价格连续严格下降，所以交点唯一并位于 $(3,4)$。又

$$
\log(4/3)>\frac27,\qquad
\log(7/6)<\frac16,\qquad
12\log2>7\log3,
$$

最后一式来自 $2^{12}=4096>2187=3^7$。因此

$$
\frac{\log(4/3)}{\log3}
>\frac2{7\log3}>\frac1{6\log2}
>\frac{\log(7/6)}{\log2}.
$$

其中 $\log(4/3)>2/7$ 可由 $\log z>2(z-1)/(z+1)$（$z>1$）得到；该对数界亦可直接对两侧求导并在 $z=1$ 比较。$\square$

**定理 483.2（完整压力的首下降胞腔）。** 对每个 $\tau<x\le4$，实际唯一最大整数为 $12$，且

$$
\boxed{
M(\lambda_x)=\log(7/3)-\lambda_x\log12,\qquad
R(x)=\frac56-\log(7/3)+\lambda_x\log2.}
$$

因此任意 $\tau<x<y\le4$ 都满足 $0<R(y)<R(x)$。

**证明。** 当 $\tau<x\le4$，事件 $(2,2)$ 的阈值高于 $\lambda_x$，同一素数的第一事件更高；引理 483.1 保证 $(3,1)$ 也严格有益。除此三项外，全部事件严格无益：

$$
\beta_{2,3}=\log(15/14)<\frac1{14}<\lambda_4\log2=\frac18,
$$

$$
\beta_{3,2}=\log(13/12)<\frac1{12}<\frac18<\lambda_4\log3.
$$

同一素数更高层的收益更小。对素数 $p\ge5$，

$$
\theta_{p,1}<\frac1{p\log p}<\frac1{4\log4}=\lambda_4.
$$

$\lambda_x\ge\lambda_4$，故这些排除覆盖所有剩余事件。恰好取三项正事件构成 $2^2\cdot3=12$；实际事件包恒等式给其目标 $\log(7/3)-\lambda_x\log12$。其余整数遗漏正事件或加入严格负事件，目标都严格更小。

对 $3<x<4$，参考只含 $2,3$ 的第一层，故 $F(x)=5/6-\lambda_x\log6$。在 $x=4$ 新参考项的净收益 $1/8-\lambda_4\log2$ 恰为零，同一表达式仍成立。两目标相减给准确储备公式。价格严格下降，故

$$
R(y)-R(x)=(\lambda_y-\lambda_x)\log2<0.
$$

严格正性来自定理 481.2。$\square$

这段真实下降并不与全域 $R\ge0$ 矛盾。正性来自整个前缀的比较；变化方向来自参考对数质量与实际优化质量的差。在上述区间，参考质量为 $\log6$，实际质量为 $\log12$，所以既有导数公式给 $R'(x)=-\log2\,w(x)<0$。递归增加素数指数可以保持正储备并消耗其中一部分；若要把五分类与迭代用于无限 Robin 证明，需要控制这种实际消耗及完整有符号积分，而不是由每一状态都有正储备推断储备随迭代递增。

## 追加锚（本行以下为增补区）

## 484. 实际最后二幂层支付一个显式价格储备

本节复用 §209.1 的正前缀核下界，结合实际达到压力的配置的最后一层条件。正核本身与素数事件表示都是既有结果；此处不另证明它们，也不把较弱的核估计作为新供应。

对素数 $p$ 和 $a\ge1$，记

$$
\delta_p(a)=Q_p(a)-\log G_p(a).
$$

§209.1 给

$$
\delta_p(a)\ge\frac{a p^{-(a+1)}}{(a+1)(1+1/p)}.
$$

在 $p=2$ 时，$a/(a+1)\ge1/2$，所以

$$
\delta_2(a)\ge\frac{2^{-(a+1)}}3.
$$

**命题 484.1（实际最优者的最后二幂层约束）。** 若 $0<\lambda<\alpha=\log(3/2)/\log2$，任意达到完整正整数压力的整数 $n$ 都有 $a=v_2(n)\ge1$，且

$$
2^{-(a+1)}\ge\frac{\lambda\log2}2.
$$

在 $\lambda=\alpha$ 时，选择实际最优整数 $2$ 也满足这一结论；此时单位整数仍是另一最大者。

**证明。** 若 $n$ 为奇数，添入首二层增加目标 $\log(3/2)-\lambda\log2>0$，与最大性矛盾。删去已取的最后二幂层也不能改善目标，因此

$$
\beta_{2,a}=\log\left(1+\frac1{2^{a+1}-2}\right)\ge\lambda\log2.
$$

令 $q=2^{-(a+1)}$、$r=\exp(\lambda\log2)$。$a\ge1$ 给 $0<q\le1/4$，所有以下分母为正。指数化并使用准确几何比值得

$$
r\le\frac{1-q}{1-2q},\qquad
q\ge\frac{r-1}{2r-1}.
$$

$1<r<3/2$ 给 $2r-1<2$；再用 $e^u\ge1+u$，得到

$$
q\ge\frac{r-1}{2r-1}\ge\frac{r-1}2\ge\frac{\lambda\log2}2.
$$

在 $\lambda=\alpha$ 时由 §482.1 选最大者 $n=2$，此时 $r=3/2$，上述非严格比较仍成立。$\square$

**推论 484.2（全部有限尺度的显式正储备下界）。** 沿用 §482 的 $x_c\in(2,3)$，有

$$
\begin{aligned}
2<x\le x_c&\implies R(x)\ge\frac12-\lambda_x\log2>0,\\
x\ge x_c&\implies R(x)\ge\frac{\lambda_x\log2}6>0.
\end{aligned}
$$

因而对所有 $x>2$，

$$
\boxed{R(x)\ge
\min\left\{\frac12-\frac{\log2}{x\log x},
\frac{\log2}{6x\log x}\right\}>0.}
$$

**证明。** 对任意实际整数 $n$，在实际支撑与参考支撑的有限并集上，参考最优值大于等于实际指数处的参考值；同一指数处的价格惩罚精确相消，所以

$$
F(x)-J_x(n)\ge\sum_{p\mid n}\delta_p(v_p(n)).
$$

当 $x>x_c$ 时，$0<\lambda_x<\alpha$。选实际达到压力的最大者，应用命题 484.1 并只保留其非负总前缀差中的二素数项：

$$
R(x)\ge\delta_2(v_2(n_x))
\ge\frac{2^{-v_2(n_x)-1}}3
\ge\frac{\lambda_x\log2}6.
$$

在 $x=x_c$ 明确选最大者 $2$，得到相同下界。在 $2<x\le x_c$，压力为零，而参考最优值至少为只取首二层的试探目标 $1/2-\lambda_x\log2$。两段证明给分段式；每段得到的下界都大于等于所显示的两个数的最小值。对 $x>2$，价格严格小于 $\lambda_2$，故最小值的两项均正。$\square$

这个下界不依赖一个尚未指定的素数分布有限起点，量级为 $1/(x\log x)$。§87.4 的聚合素数子储备已有更强的渐近平方根量级；本节不取代它。新的回接是把实际最优配置的最后一个已采用事件变成明确的有限尺度储备预算，仍没有与完整有符号 $I_\psi$ 比较，也没有证明 Robin 或 RH 的最终正号。

## 追加锚（本行以下为增补区）
