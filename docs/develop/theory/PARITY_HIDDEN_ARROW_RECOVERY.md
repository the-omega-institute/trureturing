# 奇偶马尔可夫核的支持恢复极限

## 20. 格点边界的后验平分与相位振荡

**定义 20.1（算术振幅、边界相位与格点曲线）。** 沿用[原卷第 17—19 章及定义 19.1](PARITY_HIDDEN_ARROW.md)的实验、
风险、固定基数 $`q=\lfloor M^{1-\beta}\rfloor`$ 与临界参数
$`\alpha_E,\theta,\gamma,V`$。本章改用算术振幅：存在互素正整数
$`m,k`$ 及 $`h\gt0`$，使

```math
\log(1+r)=mh,\qquad \log(1-r)=-kh.
\tag{20.1}
```

由 $`(1+r)(1-r)\lt1`$ 得 $`k\gt m`$；互素条件确定最大格距
$`h`$。记 $`\eta=1-\theta`$，并定义

```math
\delta_M=\beta\ell-h\left\lfloor\frac{\beta\ell}{h}\right\rfloor,
\quad C_c=\frac{e^{c g(\theta)}}{\sqrt{2\pi V}},\quad
x_j(\delta)=hj-\delta,
\quad a_j=C_ch e^{-\theta x_j(\delta)},\quad
b_j=C_ch e^{\eta x_j(\delta)}.
\tag{20.2}
```

相位空间为把端点 $`0,h`$ 识别的圆。对 $`a,b\gt0`$ 置

```math
H(a,b)=
\begin{cases}
\displaystyle\frac{a(e^{-b}-e^{-a})}{a-b},&a\ne b,\\[4pt]
ae^{-a},&a=b,
\end{cases}
\qquad
\Psi_h(c,\delta)=\sum_{j\in\mathbb Z}
\exp\!\left\{-\frac{a_j}{e^{\theta h}-1}
               -\frac{b_j}{e^{\eta h}-1}\right\}H(a_j,b_j).
\tag{20.3}
```

**定理 20.2（实际平稳实验的格点临界曲线）。** 在定义 20.1 的条件下，若

```math
\lambda=\alpha_E\ell-\frac{\log\ell}{2\gamma}+c_M,
\qquad c_M\longrightarrow c\in\mathbb R,
\tag{20.4}
```

则已知方向、未知方向及联合支持与方向恢复的三种精确错误风险均满足

```math
R_M=1-\Psi_h(c,\delta_M)+o(1).
\tag{20.5}
```

该式分别适用于实际平稳独立对实验与实际平稳路径实验，误差对真实支持一致。
函数 $`\Psi_h`$ 连续、关于相位以 $`h`$ 为周期，且
$`0\lt\Psi_h(c,\delta)\lt1`$。另外，若 (20.4) 中
$`c_M\to+\infty`$ 或 $`c_M\to-\infty`$，三种错误风险分别趋于
$`0`$ 或 $`1`$；后两项不要求 $`\lambda/\ell\to\alpha_E`$，只要求样本量非负。

证明。先固定一条 $`\delta_M\to\delta`$ 的子序列，并暂定方向已知；若为反向，先按第 18 章的观测反向映射对齐计数。
第 19 章证明中的任意固定行数比较、全观测似然与计数截断均不使用非格点假设。
以下只替换局部极限定理和边界上的决策步骤。

记不含补偿的行分数为
$`Z_x=N_x^+\log(1+r)+N_x^-\log(1-r)\in h\mathbb Z`$，
完整似然排序分数为 $`W_x`$。先在独立复合 Poisson 参照中作固定指数倾斜
$`Q_\theta`$。单位时间增量的支持含 $`0,mh,-kh`$，故除以
$`h`$ 后最大格距为 $`1`$，均值与方差分别为
$`g'(\theta)/h`$、$`g''(\theta)/h^2`$。
[Stone 的格点局部极限定理](../../../Library/Dynamics/stone1967local.md)
应用于这个增量分布，给出对固定 $`j`$ 的

```math
Q_\theta\!\left\{Z=h\left\lfloor\frac{\beta\ell}{h}\right\rfloor+hj\right\}
=\frac{h}{\sqrt{2\pi\lambda g''(\theta)}}(1+o(1)).
\tag{20.6}
```

这里格点与倾斜均值之差为 $`O(\log\ell)`$。
将 $`\lambda`$ 分成整数部分与不足一单位的独立增量，即可处理非整数时间：
后者的均值、方差一致有界；先截断该增量，再用局部极限定理的全位置一致误差，
最后移去截断。该定理也给出所有格点质量的上界 $`O(\lambda^{-1/2})`$。
这里使用的是最大格距条件，没有把连续密度或非格点假设带入 (20.6)。

设 $`p_{0,M}(j)`$、$`p_{1,M}(j)`$ 分别为补偿背景与信号行的格点概率。
撤销固定倾斜，利用 $`\alpha_Eg'(\theta)=\beta`$、
$`\theta\beta-\alpha_Eg(\theta)=1`$ 及 (20.4)，得到

```math
(M-q)p_{0,M}(j)\longrightarrow a_j,
\qquad q\,p_{1,M}(j)\longrightarrow b_j.
\tag{20.7}
```

补偿的处理仍在原计数上完成：在总计数至多 $`L\ell`$ 的截断内，
补偿背景与未补偿背景的概率质量比为 $`1+o(1)`$，一致于计数组合；
截断外概率可取任意固定的 $`M^{-D}`$。所以 (20.7) 保留了点概率的相对精度。
这里不能把 $`W-Z=o(1)`$ 当作格点上的事件相同；(20.7) 计算的始终是
$`Z`$ 的格点事件，$`W`$ 留待后验论证。

对固定有限的格点集合，令 $`U_{M,j}`$、$`V_{M,j}`$ 分别计数其中的背景行与信号行。
把任意混合下降阶乘展开为互异行的和，全部行都在同一个真实支持下取样。
若总阶数为固定 $`s`$，第 19 章的比较给出相对误差
$`O(\ell^{s+1}/n)`$ 与任意 $`M^{-D}`$ 的加性误差；取 $`D\gt s`$ 后求和，
再用 (20.7)，得

```math
\mathbb E_S\prod_j(U_{M,j})_{u_j}(V_{M,j})_{v_j}
\longrightarrow\prod_j a_j^{u_j}b_j^{v_j}.
\tag{20.8}
```

有限维分布因此趋于全部独立的 Poisson 变量
$`U_j\sim\operatorname{Pois}(a_j)`$、$`V_j\sim\operatorname{Pois}(b_j)`$。
具体地，可对各类格点计数作独立的辅助稀疏化；固定阶 Bonferroni 上下界与
(20.8) 先给出稀疏化后无点的概率，再让阶数趋于无穷，得到联合概率母函数
$`\exp\{-\sum_j(t_ja_j+s_jb_j)\}`$，其中各保留概率在 $`[0,1]`$ 内。
这识别了所述有限维分布，并未假设实际观测行独立。

定义背景最高格点指标与信号最低格点指标为 $`J_{0,M}`$、$`J_{1,M}`$。
局部极限定理的全位置上界、固定倾斜与几何求和给出

```math
\limsup_{M\to\infty}\Pr_S\{J_{0,M}\gt J\}
\le K e^{-\theta hJ},\qquad
\limsup_{M\to\infty}\Pr_S\{J_{1,M}\lt-J\}
\le K e^{-\eta hJ}.
\tag{20.9}
```

常数可一致于紧的 $`(c,\delta)`$ 集。相反方向的紧性由固定格点的无点概率得到：
$`a_{-J}\to\infty`$、$`b_J\to\infty`$ 随 $`J\to\infty`$，
而 $`J_{0,M}\lt-J`$ 蕴含 $`U_{M,-J}=0`$，
$`J_{1,M}\gt J`$ 蕴含 $`V_{M,J}=0`$。
因此两种极值格点都紧。

现在返回全部实际观测。对单行截断取 $`D\gt1`$ 并对所有行取并集，得概率趋于一的事件
$`G_M`$，使

```math
\max_x(N_x^++N_x^-)\le L\ell,
\qquad \max_x|W_x-Z_x|\le\varepsilon_M\longrightarrow0.
\tag{20.10}
```

后一上界可取 $`O((q/M)\ell)`$。在 $`2\varepsilon_M\lt h`$ 时，
不同 $`Z`$ 格点之间的 $`W`$ 排序不变。令 $`j_*`$ 为观测中第
$`q`$ 大的 $`Z`$ 所在格点，$`N_*`$ 为该格点总行数，
$`K_*`$ 为从该格点仍须选取的行数。粗排序最优族 $`\mathcal F`$
包括所有高于 $`j_*`$ 的行，并从边界格点任选 $`K_*`$ 行，故
$`|\mathcal F|=\binom{N_*}{K_*}`$。

均匀支持先验下，第 18 章的完整观测似然给每个候选支持 $`T`$ 的后验权重
$`\exp\{\sum_{x\in T}W_x\}`$ 乘上同一个归一化因子。
在 $`G_M`$ 上，每个 MAP 支持都属于 $`\mathcal F`$；族内两权重之比在
$`[e^{-2N_*\varepsilon_M},e^{2N_*\varepsilon_M}]`$ 内。
边界格点 $`j_*`$ 位于 $`J_{0,M}`$ 与 $`J_{1,M}`$ 之间，包含端点：
所有信号都不低于 $`J_{1,M}`$；若该值不高于背景最大值，则严格高于背景最大值的
行至多有 $`q-1`$ 个；若它更高，则第 $`q`$ 大值恰为最低信号值。
极值紧性与固定窗口内 (20.8) 的计数紧性遂给出 $`N_*`$ 紧。

对 $`N_*\le L_0`$ 先固定截断，比较族内权重，随后平均、应用条件期望塔式法则，
再令 $`L_0\to\infty`$，得到实际 Bayes 成功概率

```math
P_M^{\mathrm{Bayes}}=
\mathbb E\!\left[
 \frac{\mathbf1_{\{S\in\mathcal F\}}}{\binom{N_*}{K_*}}
\right]+o(1).
\tag{20.11}
```

这个结论容许补偿在同一格点内重新排序，也容许实际 $`W`$ 精确并列；
没有给小的分数余项假设独立标记。

事件 $`S\in\mathcal F`$ 等价于 $`J_{1,M}\ge J_{0,M}`$。
若严格大于，边界格点全为信号，(20.11) 中分母为 $`1`$；
若相等于 $`j`$，分母为 $`\binom{U_{M,j}+V_{M,j}}{U_{M,j}}`$。
固定窗口内 (20.8) 的分布收敛适用于这个有界函数，再由极值紧性移去窗口。
按唯一的最高背景格点 $`j`$ 分拆，有

```math
P_M^{\mathrm{Bayes}}\longrightarrow
\sum_j e^{-\sum_{i\gt j}a_i-\sum_{i\lt j}b_i}
\mathbb E\!\left[
 \frac{\mathbf1_{\{U_j\ge1\}}}{\binom{U_j+V_j}{U_j}}
\right].
\tag{20.12}
```

其中 $`V_j=0`$ 恰好包含严格分离，不会重复计数。几何求和给出 (20.3) 的外因子，
而独立 Poisson 变量直接给出

```math
\mathbb E\!\left[
 \frac{\mathbf1_{\{U\ge1\}}}{\binom{U+V}{U}}
\right]
=e^{-a-b}\sum_{u\ge1,v\ge0}\frac{a^ub^v}{(u+v)!}
=a\int_0^1e^{-ta-(1-t)b}\,dt=H(a,b).
\tag{20.13}
```

按 $`u+v`$ 分组即得第一种闭式，取 $`a=b`$ 得第二种闭式。
这证明了所要求的后验平分系数。

正项级数在 $`(c,\delta)`$ 的紧集上一致可和：
当 $`j\to-\infty`$，$`a_j`$ 指数增长，外因子中的背景尾抑制所有幂次；
当 $`j\to+\infty`$，信号尾同样抑制 $`b_j`$ 的增长。
也可直接用 $`H(a,b)\le a e^{-\min(a,b)}`$ 给出可和包络。
所以曲线连续；把 $`\delta`$ 加 $`h`$ 只将指标平移一格。
任何固定相位子序列都已证明同一公式，圆的紧性遂将其提升为 (20.5)。

上述独立 Poisson 格点族的背景最大值与信号最小值均有限。
严格分离事件有正概率，反向交错事件也有正概率，因此曲线严格处于 $`0`$ 与 $`1`$ 之间。
第 18 章的置换对称性使随机化 MAP 的各支持风险相等，Bayes 值等于全规则 minimax 值。
同章的一致方向分类器与同数据联合界，将极限传递给未知方向及联合恢复；
因为 $`\alpha_E\gt\alpha_D`$，临界尺度上其方向错误趋于零。

最后，当 $`c\to+\infty`$ 时 $`C_c\to0`$。
无背景格点不低于 $`0`$ 且无信号格点不高于 $`0`$ 的概率趋于一，且对相位一致。
当 $`c\to-\infty`$ 时 $`C_c\to\infty`$；粗分离蕴含
背景最大格点不高于 $`0`$ 或信号最小格点不低于 $`0`$，两种无点概率之和
对相位一致趋于零。由第 19 章的样本前缀单调性，将任意发散偏移夹在固定有限偏移之外，
再令固定偏移趋于相应无穷，即得两端结论。∎

**定理 20.3（低成功率端的相位衰减率）。** 在定义 20.1 下，记

```math
A=\frac1{e^{\theta h}-1},\qquad B=\frac1{e^{\eta h}-1},\qquad
F_+(x)=h\bigl((A+1)e^{-\theta x}+Be^{\eta x}\bigr),\qquad
\rho_h(\delta)=F_+(h-\delta).
\tag{20.14}
```

则对每个固定 $`\delta\in[0,h]`$，

```math
\lim_{c\to-\infty}\frac{-\log\Psi_h(c,\delta)}{C_c}
=\rho_h(\delta).
\tag{20.15}
```

端点的值相同，而 $`\rho_h`$ 在 $`[0,h]`$ 上严格凸，唯一最小相位为

```math
\delta_*=h-\log\frac{\theta(A+1)}{\eta B}\in(0,h).
\tag{20.16}
```

特别地，存在有限 $`c_0`$，使对每个 $`c\lt c_0`$ 都有
$`\Psi_h(c,\delta_*)\gt\Psi_h(c,0)`$。更一般地，集合
$`E_h=\{c\in\mathbb R:\Psi_h(c,\delta_*)=\Psi_h(c,0)\}`$
在实轴上局部有限，并与 $`(-\infty,c_0)`$ 不交。

证明。暂把 $`C=C_c`$ 视为独立正参数。置

```math
F_-(x)=h\bigl(Ae^{-\theta x}+(B+1)e^{\eta x}\bigr),\qquad
F(x)=h\bigl(Ae^{-\theta x}+Be^{\eta x}
                 +\min(e^{-\theta x},e^{\eta x})\bigr).
\tag{20.17}
```

于是 $`F=F_+`$ 于非负半轴，$`F=F_-`$ 于非正半轴，且

```math
F_-(x)=F_+(x+h),\qquad
F_+(x+h)-F_+(x)=h(e^{\eta x}-e^{-\theta x}),\qquad
F_-(x-h)-F_-(x)=h(e^{-\theta x}-e^{\eta x}).
\tag{20.18}
```

当 $`0\lt\delta\lt h`$，令 $`x_0=h-\delta\in(0,h)`$。
格点 $`x_0`$ 与 $`x_0-h`$ 的 $`F`$ 值相等；由后两式，
向正、负两端逐格远离时该值严格增加。因此
$`\min_jF(hj-\delta)=F_+(h-\delta)`$。
端点由同样的非严格不等式得到，且
$`F_+(0)=F_+(h)`$。

对任一固定格点，(20.13) 的闭式说明相应级数项的负对数除以
$`C`$ 趋于 $`F(x_j)`$；在 $`a_j=b_j`$ 时，多出的因子
$`Ch`$ 不改变这个极限。保留一个最小格点即给出 (20.15) 的上极限界。
反方向利用 $`H(a,b)\le ae^{-\min(a,b)}`$：当 $`C\ge1`$ 时，

```math
\Psi_h(c,\delta)
\le C e^{-(C-1)\rho_h(\delta)}
\sum_{j\in\mathbb Z}h e^{-\theta x_j}e^{-F(x_j)}.
\tag{20.19}
```

右侧级数有限，因为 $`F(x)`$ 在两端指数增长。这给出匹配的下极限界，证明 (20.15)。

$`F_+''(x)\gt0`$，且 $`F_+'(x)=0`$ 恰好给出
$`x_* =\log(\theta(A+1)/(\eta B))`$。
由
$`\theta/(1-e^{-\theta h})\gt1/h\gt\eta/(e^{\eta h}-1)`$
得到 $`x_*\gt0`$；交换 $`\theta,\eta`$ 的同一不等式得到
$`x_*\lt h`$。所以 (20.16) 是严格内点最小值，
$`\rho_h(0)\gt\rho_h(\delta_*)`$。
最后将 (20.15) 分别用于这两个相位，得

```math
\frac1{C_c}\log\frac{\Psi_h(c,\delta_*)}{\Psi_h(c,0)}
\longrightarrow\rho_h(0)-\rho_h(\delta_*)\gt0,
\qquad c\to-\infty.
\tag{20.20}
```

因 $`C_c\to\infty`$，所述严格不等式对所有充分负的 $`c`$ 成立。

为证明例外集合的局部有限性，将 (20.13) 的积分式代回 (20.3)，
并将 $`C`$ 扩展到复半平面 $`\Re C\gt0`$。记
$`a_j^0=h e^{-\theta x_j}`$、$`b_j^0=h e^{\eta x_j}`$，每一项为整函数

```math
C a_j^0\int_0^1
\exp\{-C[(A+t)a_j^0+(B+1-t)b_j^0]\}\,dt.
```

对任意紧集 $`\Re C\ge\epsilon\gt0`$、$`|C|\le K`$，
该项的绝对值至多 $`K a_j^0e^{-\epsilon F(x_j)}`$，构成可和包络。
故级数在此半平面定义全纯函数。相位 $`\delta_*`$ 与 $`0`$ 的函数之差
由 (20.20) 不是恒零，其零点因而孤立。
$`c\mapsto C_c`$ 是实轴到正实轴的连续双射，且紧集映为半平面内部的紧集，
所以 $`E_h`$ 在每个有界闭区间内只有有限个点。∎

**定理 20.4（固定偏移下实际风险不收敛的振幅）。** 取

```math
\varphi=\frac{1+\sqrt5}{2},\qquad
r=\varphi^{-1},\qquad h=\log\varphi,\qquad \beta=\frac34.
\tag{20.21}
```

则 (20.1) 中 $`m=1,k=2`$。对每个固定 $`c\notin E_h`$，
因而也对每个充分负的固定偏移，沿全部整数维数 $`d\to\infty`$，取可实现的整数样本量满足

```math
\lambda=\alpha_E\ell-\frac{\log\ell}{2\gamma}+c+o(1),
\tag{20.22}
```

三种精确错误风险在实际平稳独立对实验和路径实验中都不收敛。
它们分别有趋于 $`1-\Psi_h(c,0)`$ 和 $`1-\Psi_h(c,\delta_*)`$
的两条子序列，且这两个极限不同。离散极值及并列振荡的相关结果见
[Ottolini](../../../Library/Dynamics/ottolini2020oscillations.md)。

证明。恒等式 $`1+r=\varphi`$、$`1-r=\varphi^{-2}`$ 给出格距与整数对。
比值 $`\log2/\log\varphi`$ 无理：若为有理数，则存在正整数
$`p,q`$ 使 $`2^q=\varphi^p`$；在数域 $`\mathbb Q(\sqrt5)`$
中取范数将给出 $`4^q=(-1)^p`$，矛盾。
因此 $`(3/4)\log2/\log\varphi`$ 也无理，圆上的无理旋转使

```math
\delta_M=\frac34(d-1)\log2\pmod{\log\varphi}
\tag{20.23}
```

稠密，且每个尾序列仍稠密。可分别选择相位趋于 $`0`$ 与 $`\delta_*`$ 的子序列。
对目标样本数取最近整数只改变 $`\lambda`$ 至多 $`O(1/n)`$，
不改变 (20.22)，而目标样本数最终为正。
定理 20.2 给出两条子序列的风险极限，定理 20.3 保证其不同。
若 $`c\in E_h`$，本命题的两相位比较不判定风险是否收敛。∎

## 追加锚（本行以下为增补区）
