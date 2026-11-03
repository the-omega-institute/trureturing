**AURIC RESEARCH / C121-$\zeta$**

# 内生差分接续与 $\zeta$ 零点

**二元关系、全局正性及量子重构**

完整候选、定义、定理与证明

对本稿固定的实际算术核，已经能够严格证明

$$
\boxed{\quad
\mathrm{RH}\quad\Longleftrightarrow\quad
\left|\mathcal K(t)\right|\leq \mathcal K(0)\quad(\forall t\in\mathbb R).
\quad}
$$

这恰好要求每一对算术历史的归一化比较落在合法二元球内。临界线外零点若存在，就有两个有限整数地址见证失败。

这一等价定理给出精确研究目标；它没有证明实际素数核在所有尺度上满足该不等式。

 版本：C121-$\zeta$，2026 年 11 月 3 日。

对话研究续稿编号，不是仓库发布标签。

固定来源：`dev@c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539`

快照提交时间：2026-11-03 14:56:58 UTC。

核对范围：相关纸稿、Lean 声明及证明正文；本轮没有运行 Lean 编译或审计全部传递依赖。

本稿回答：内生量子关系、二元有限三维提升，是否与 Riemann $\zeta$ 的零点及临界线外零点存在严格联系？答案是有，而且项目已经具备实际算术核、局部正性及零点–Laplace 桥。本稿把这一联系压缩成全尺度二元不等式，给出完整反向证明，并推得有限整数双地址的负见证。随后以一个不依赖 RH 的 Volterra 恒等式，把项目实际核连接到 Suzuki 的螺旋函数。在全局正性（等价于 RH）条件下，“当前差异与累计历史”进一步具有 Hilbert 空间中的酉 cocycle 实现；这个几何实现不是无条件结论。

本轮完整候选 C121 以同一个 $\Omega$ 内的历史代数、正评价、完整支路、独立并置和连续接续为模型条件。其有限维表示恢复 Hilbert 空间、Born 规则、量子仪器、张量积、理想滤波更新及 Hamiltonian 形式。复结构、正性、完整读出和复合供给都是明确的承重条件；“全部内生”本身没有证明它们。候选的内容是可检验的内部约束，不是从零前提推出量子力学。

| 结论层级 | 本稿所做的事 |
|---|---|
| 项目来源 | 固定已读文件及声明的量词，不把理论稿或网页标签升级为本次形式化认证。 |
| 普通证明 | 给出二元判据、整数见证、Volterra 桥、差分接续、Schur 递归及有限量子表示的推导。 |
| 模型候选 | 提出 C121 的完整内部关系约束；其物理适用性及原生实现仍需论证。 |
| 未解决 | $\mathcal K$ 的全尺度界、RH、宇宙态唯一选择、具体 Hamiltonian、$\hbar$ 数值及物理时空维数。 |

本文的基础结论继承经典量子理论、正定核理论和已发表的 RH 等价判据；不主张这些工具或等价关系的文献首创。新一轮工作重点是把项目指定对象、二元检验和量子解释放在同一条不偷换对象的推导链上。

## 目录

- [1. 项目进展与本轮的准确起点](#section-1)
- [2. 固定实际算术对象](#section-2)
- [3. RH 的全尺度二元判据](#section-3)
- [4. 二元有限三维提升：哪一部分真的在球里](#section-4)
- [5. 从项目核到“欧拉弹簧”：一个无条件积分桥](#section-5)
- [6. 简洁几何：静态频谱、当前差异与累计历史](#section-6)
- [7. 完整候选 C121：内生差分与忠实接续](#section-7)
- [8. 从候选恢复标准有限维量子力学](#section-8)
- [9. 反着推：离线模式与被破坏的关系](#section-9)
- [10. 可以继续证明的具体目标及其限制](#section-10)
- [11. 一段完整的白话描述](#section-11)
- [12. 符号、零边界与可复核口径](#section-12)
- [13. 来源、归属与固定路径](#section-13)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 项目进展与本轮的准确起点

本次读取时，仓库的公开默认分支为 `dev`。以下结论固定在标题页所列提交；不声称回答结束时分支仍停留于该提交。完整来源路径见文末。

### 1.1 实际核已有短窗口的任意阶正性

`ActualKernelLocalPositivity.exists_window_posDef` 的声明为：存在
$\delta\in(0,\log2)$，对于任意有限个互异节点 $x_1,\ldots,x_n$，若全部距离不超过 $\delta$，则

$$
\left[\mathcal K(x_i-x_j)\right]_{i,j=1}^{n}>0.
$$

声明使用实际的完整素数核，没有把 RH 或任选正核作为参数。这里 $>0$ 是严格正定，重复节点被排除。本轮读了声明和证明正文，没有重新编译。

这意味着局部工作并非只验了两三阶矩阵：一个固定短窗内的任意有限阶已经进入源码。余下的问题是**同一个实际核的远距离交叉值**。一个局部正核可以有某个全轴正扩张，但该扩张在窗外未必等于算术指定的 $\mathcal K$。

### 1.2 实际零点与对数导数已有精确桥

`ActualZeroLaplace.lean` 中的 `actualZero` 按解析重数枚举非平凡零点，`actualH` 是完整加权零点和；`actual_resolvent_hasSum` 和 `actualH_laplace` 在原变量 $\operatorname{Re} s>1$ 上给出 resolvent 与积分恒等式。平移 $s=z+\tfrac12$ 后得到本稿第 [2](#sec-arithmetic) 节的公式，初始域为 $\operatorname{Re} z>\tfrac12$，不能直接当作已知在整个右半平面成立。

### 1.3 Weil 负见证与等价定理的条件

`offLineNonrealZero_yields_negative_weil_square` 对所供应的
`ZeroData` 及非实离线零点，构造完整负 Weil 平方见证。证明不是只找出一个负四元组：它还以有限插值和卷积幂控制其余零点尾项。

`rh_iff_explicitFormulaPositivity` 还带有 `ZeroData` 以及每个卷积平方的 Archimedean 收敛供应条件。它把 RH 改写为实际显式公式的全测试正性，没有证明后者。这里保持这些条件，不用网页上的简短定理名代替原声明。

### 1.4 C117 已有的量子关系结果

本次找到并读取相关章节的 C117 纸稿已经讨论全效果可加性、完整过程保比较、独立复合、共同细化、GNS 及全部自由 Gram 完成。它也明确区分：

- 比较空间与物理振幅空间；
- 一对历史的 Gram 秩一与条件物理态纯；
- 某个自由正完成的存在与算符词积、张量关系的实际相容；
- 同一个循环向量与物理宇宙态纯性。

本稿承接这些边界。C118–C120 的对话工作不因本次目录未见同名文件而被否定；本稿使用 C121-$\zeta$ 作为本轮工作标识。

<a id="section-2"></a>

## 2. 固定实际算术对象

<a id="sec-arithmetic"></a>

### 定义 2.1（完整素数核）

以 $\gamma_E$ 表示 Euler 常数，所有对数为自然对数。对 $x\geq1$，令

$$
\begin{aligned}
\mathcal F(x)={}&x(1+\gamma_E-\log x)-\log(2\pi)
 +\sum_{k=1}^{\infty}\frac{x^{-2k}}{2k(2k+1)}
\end{aligned}
$$

<a id="eq-prime"></a>

$$
\begin{aligned}
&+\sum_{p^j\leq x}\log p\left(\frac{x}{p^j}-1\right),
\end{aligned}
\tag{1}
$$

<a id="eq-K"></a>

$$
\begin{aligned}
\mathcal K(t)={}&e^{-|t|/2}\mathcal F(e^{|t|}),\qquad t\in\mathbb R.
\end{aligned}
\tag{2}
$$

最后一和遍历全部实际素数幂。新素数幂在端点的斜坡值为零，故 $\mathcal K$ 连续；它按定义实值、偶对称。

不得省略平凡零点尾项、改换素数幂端点或重新选择总量。直接代入得

<a id="eq-S"></a>

$$
S:=\mathcal K(0)=2+\gamma_E-\log(4\pi)>0.
\tag{3}
$$

这里的正性是已知的第一 Li 总质量正性；也可由下面绝对收敛零点和配对得到。

采用标准完成函数

$$
\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
\qquad \xi(s)=\xi(1-s).
$$

非平凡零点均按重数计。项目实际显式公式供应

<a id="eq-zero-K"></a>

$$
\mathcal K(t)=\sum_{\rho}\frac{e^{(\rho-\frac12)t}}{\rho(1-\rho)},
\qquad t\in\mathbb R.
\tag{4}
$$

零点条带与计数估计保证该和在每个紧实区间上一致绝对收敛。反射配对保证偶性，共轭配对保证实值。若 $\rho=\beta+i\tau$，则

$$
\operatorname{Re}\frac1{\rho(1-\rho)}
=\frac{\beta(1-\beta)+\tau^2}
 {[\beta(1-\beta)+\tau^2]^2+\tau^2(1-2\beta)^2}>0.
$$

因此总质量 $S$ 严格正。该式没有把复权重逐项当成非负实权重。

定义

$$
D(z)=\frac{\xi'}{\xi}\left(\tfrac12+z\right).
$$

项目提供的关键无条件恒等式为

<a id="eq-LK"></a>

$$
L_K(z):=\int_0^\infty e^{-zt}\mathcal K(t)\,\mathrm d t
=\frac{Sz-D(z)}{z^2-\frac14},
\qquad \operatorname{Re} z>\frac12.
\tag{5}
$$

原域的绝对收敛允许换序。右式在 $z=\pm\tfrac12$ 的表观奇点可去；实际离线零点产生的极点具有非零留数。下节的证明会先乘去分母，因而无需在可去点反复分情况。

<a id="section-3"></a>

## 3. RH 的全尺度二元判据

### 定理 3.1（实际核的二元锁定）

<a id="thm-binary"></a>

对定义 [(1)](#eq-prime)–[(2)](#eq-K) 的固定实际核，下列命题等价：

1. RH：每个非平凡零点满足 $\operatorname{Re}\rho=\tfrac12$；

2. $\mathcal K$ 在 $\mathbb R$ 上有界；

3. 对全部 $t\in\mathbb R$，$\left|\mathcal K(t)\right|\leq S$；

4. 对全部 $t\in\mathbb R$，


   $$
   M(t)=\begin{pmatrix}S&\mathcal K(t)\\ \mathcal K(t)&S\end{pmatrix}\succeq0;
   $$

5. 对任意有限实节点，矩阵
   $\left[\mathcal K(t_i-t_j)\right]_{i,j}$ 半正定。

**证明。**
先假设 RH。写 $\rho=\tfrac12+i\gamma$，则

<a id="eq-positive-spectral"></a>

$$
\mathcal K(t)=\sum_\gamma\frac{e^{i\gamma t}}{\frac14+\gamma^2},
\qquad
S=\sum_\gamma\frac1{\frac14+\gamma^2}.
\tag{6}
$$

所有权重非负，总质量有限，故三角不等式给出 (3)。对任意系数，

$$
\sum_{i,j}\overline{c_i}c_j\mathcal K(t_i-t_j)
=\sum_\gamma
\frac{\left|\sum_j c_j e^{-i\gamma t_j}\right|^2}{\frac14+\gamma^2}
\geq0.
$$

换序由绝对总质量和有限项性保证，所以 (5) 成立。(5) 蕴含 (4)；$M(t)$ 的两个特征值为 $S+\mathcal K(t)$、$S-\mathcal K(t)$，故 (4) 等价于 (3)；(3) 蕴含 (2)。

现在证明真正关键的反向 (2) 蕴含 (1)。设 $|\mathcal K(t)|\leq C$。积分 $L_K(z)$ 在整个 $\operatorname{Re} z>0$ 全纯：对任意紧子集取 $\operatorname{Re} z\geq\eta>0$，函数及其各阶 $z$ 导数分别由
$C t^m e^{-\eta t}$ 支配。

令 $F(z)=\xi(\tfrac12+z)$。在 $\operatorname{Re} z>\tfrac12$，由 [(5)](#eq-LK) 得

<a id="eq-ode"></a>

$$
F'(z)+\left[\left(z^2-\tfrac14\right)L_K(z)-Sz\right]F(z)=0.
\tag{7}
$$

两项在整个右半平面全纯，恒等定理使等式延拓到 $\operatorname{Re} z>0$。

若 $F$ 在该域有 $m\geq1$ 阶零点 $z_0$，则 $F'$ 在 $z_0$ 的阶数恰为 $m-1$，而方括号乘 $F$ 的阶数至少为 $m$。二者不可能相消，与 [(7)](#eq-ode) 矛盾。因此没有 $\operatorname{Re}\rho>\tfrac12$ 的零点。函数方程把任一 $\operatorname{Re}\rho<\tfrac12$ 的零点反射到右侧，故左侧也没有零点，RH 成立。

这一定理证明的是：若实际算术关系满足全尺度二元界，离线零点就不可能存在。
它没有把该界证明出来，也没有用“量子关系理应正定”代替算术证明。

### 3.1 离线零点必给有限的二元负见证

### 推论 3.2（离线的内部失败位置）

<a id="cor-witness"></a>

若 RH 为假，则存在有限实数 $t_0$，使
$\left|\mathcal K(t_0)\right|>S$。取
$\varepsilon=\operatorname{sgn}\mathcal K(t_0)\in\{1,-1\}$，有

$$
(1,-\varepsilon)M(t_0)(1,-\varepsilon)^{\mathsf T}
=2(S-|\mathcal K(t_0)|)<0.
$$

**证明。**
这是定理 [3.1](#thm-binary) 的逆否命题与直接矩阵乘法。因为 $S>0$，超界时符号确定。

这避免了一个常见漏洞：从某个离线模式的指数增长，直接断言整个无限和增长。这里的解析恒等式已经处理全部可能抵消，才推出负见证存在。

### 3.2 无需先定位零点：两个整数地址足够见证失败

### 定理 3.3（整数双地址判据）

<a id="thm-integer"></a>

下列条件等价：

1. RH；

2. 对任意正整数 $m,n$，


   $$
   \left|\mathcal K\!\left(\log\frac mn\right)\right|\leq S;
   $$

3. 对任意真正遍历所有正整数的排列 $(a_j)_{j\geq1}$，每个前缀的所有二元主块均半正定；

4. 对这样的任一排列，每个前缀矩阵


   $$
   G_N=\left[\mathcal K(\log a_i-\log a_j)\right]_{i,j\leq N}
   $$


   都半正定。

如果 RH 为假，存在互素的 $m\ne n$ 和系数 $1,\pm1$，给出严格负的二地址二次型。任何上述排列都在某个有限前缀中包含该见证。

**证明。**
$\log\mathbb Q_{>0}$ 在 $\mathbb R$ 中稠密。若 $|\mathcal K(t_0)|>S$，连续性给出一个保持严格超界的开区间，选
$\log(m/n)$ 落在其中，约去公因子即可；开区间不含零可取 $m\ne n$。整数符号向量由推论 [3.2](#cor-witness) 给出。

反向，若整数双地址均满足界，稠密性及连续性给全部实数上的界，再用定理 [3.1](#thm-binary)。一个排列在有限前缀中包含 $m,n$，向其余坐标补零可把负二次型嵌入该前缀。RH 下全部前缀正性已由定理 [3.1](#thm-binary) 证明。

项目的 Zeckendorf 贪心排列可以提供这种穷尽顺序，但本推论只使用它确为正整数排列这一性质；相邻展开的共同项性质没有替代符号控制。仅检查相邻枚举项不足。这里也没有得到见证高度、$m,n$ 大小或前缀索引的统一上界。

<a id="section-4"></a>

## 4. 二元有限三维提升：哪一部分真的在球里

### 定理 4.1（二元正关系与三实坐标）

<a id="thm-bloch"></a>

设

$$
B=\begin{pmatrix}a&c\\ \overline c&b\end{pmatrix},
\qquad T=a+b>0.
$$

则

<a id="eq-bloch"></a>

$$
\frac BT=\frac12(I+\bm r\cdot\bm\sigma),\qquad
\bm r=\frac{(2\operatorname{Re} c,-2\operatorname{Im} c,a-b)}{T},
\tag{8}
$$

且

<a id="eq-ball"></a>

$$
B\succeq0\quad\Longleftrightarrow\quad
|\bm r|\leq1,\qquad
|\bm r|^2=1-\frac{4(ab-|c|^2)}{T^2}.
\tag{9}
$$

**证明。**
把 Pauli 矩阵代入即可得到 [(8)](#eq-bloch)。归一化矩阵的特征值为
$(1\pm|\bm r|)/2$，故半正定性等价于球内条件。最后一个等式直接展开。

迹零的正矩阵只能是零矩阵，此时没有可归一化的球坐标；不能除以零。球面对应关系表秩一。若 $B$ 是两个比较向量的 Gram，这表示两向量线性相关，不自动表示某个条件物理态纯。

对本稿实际算术核，

<a id="eq-Kball"></a>

$$
\frac{M(t)}{2S}
=\frac12\left[I+\frac{\mathcal K(t)}S\sigma_x\right],
\qquad
\bm r(t)=\left(\frac{\mathcal K(t)}S,0,0\right).
\tag{10}
$$

因此实际二元读出只用到三维球的一条直径。临界线外零点若存在，某个有限尺度会使 $|\bm r(t)|>1$。这张表不能成为两个正内积向量的归一化关系表。它不是已经实现的物理负概率，而是该算术数据不能按指定方式实现为量子关系的证据。

### 4.1 为什么一般两两合法仍然不够

### 例 4.2（两两正定而整体失败）

$$
G=\begin{pmatrix}
1&-\tfrac34&-\tfrac34\\
-\tfrac34&1&-\tfrac34\\
-\tfrac34&-\tfrac34&1
\end{pmatrix}.
$$

每个二元主块的特征值为 $1/4,7/4$，但 $G$ 在向量 $(1,1,1)$ 上的特征值为 $-1/2$，其余两个为 $7/4$。所以一般的二元正性不蕴含共同正实现。

定理 [3.1](#thm-binary) 没有违反此反例：它额外使用了固定 $\mathcal K$ 的全部算术值、连续性以及 $\xi'/\xi$ 的解析恒等式。正是这一特殊结构，把所有二点界提升到了 RH，继而才得到任意阶正性。

### 4.2 真正可递归的“旧整体–新关系”检验

### 定理 4.3（含奇异边界的 Schur 接续）

<a id="thm-schur"></a>

有限 Hermitian 分块矩阵

$$
G_{n+1}=\begin{pmatrix}G_n&k\\ k^*&a\end{pmatrix}
$$

半正定，当且仅当

<a id="eq-schur"></a>

$$
G_n\succeq0,\qquad k\in\operatorname{Ran} G_n,\qquad
a-k^*G_n^+k\geq0,
\tag{11}
$$

其中 $G_n^+$ 是 Moore–Penrose 逆。

**证明。**
半正定性要求主块非负。若 $z\in\ker G_n$，在向量 $(tz,1)$ 上展开并任意改变 $t\in\mathbb C$，得到 $z^*k=0$，即范围条件。写 $h=G_n^+k$，则 $G_nh=k$，并有

$$
\begin{pmatrix}x\\y\end{pmatrix}^{\!*}
G_{n+1}
\begin{pmatrix}x\\y\end{pmatrix}
=(x+hy)^*G_n(x+hy)
+|y|^2(a-k^*G_n^+k).
$$

取 $x=-hy$ 得必要性，右式也给充分性。

这是二元递归的正确实现：一元是已有全部历史，另一元是新增分支；向量 $k$ 保留新增分支与全部旧历史的交叉关系。验证步骤可以二元化，数据本身不能无损压成固定三个实数。

对实际 $\mathcal K$，新增对角为同一个 $S$，待证余量就是

$$
S-k^*G_n^+k\geq0.
$$

自由完成可以选择一个使余量非负的 $k$，而实际算术已经指定 $k_i=\mathcal K(t_i-t_{\rm new})$。证明必须针对后者。

### 4.3 接回 C119 的三元余关系圆盘

三个归一比较向量的矩阵写作

$$
\begin{pmatrix}
1&a&c\\ \overline a&1&b\\ \overline c&\overline b&1
\end{pmatrix}.
$$

以中间向量为共同参考作 Schur 消元，得到精确条件

<a id="eq-triple"></a>

$$
|a|\leq1,\quad |b|\leq1,\quad
|c-ab|^2\leq(1-|a|^2)(1-|b|^2).
\tag{12}
$$

这是“已解释关系 $ab$ 加剩余交叉关系”的圆盘。若某侧剩余为零，就强制
$c=ab$，没有可任意补入的自由度。

令 $k(t)=\mathcal K(t)/S$。对于时间 $0,s,s+t$，RH 下必有

$$
|k(s+t)-k(s)k(t)|^2
\leq[1-k(s)^2][1-k(t)^2].
$$

单频圆周 $k(t)=\cos(\nu t)$ 在此取等号，正是三角加法公式；多频整体通常出现非零剩余维数。它给“圆周模块如何拼成更大的历史结构”一个精确关系，但实际 $\mathcal K$ 是否在全尺度满足这些关系仍由定理 [3.1](#thm-binary) 控制。

<a id="section-5"></a>

## 5. 从项目核到“欧拉弹簧”：一个无条件积分桥

### 定义 5.1（算术差分函数）

对 $t\geq0$，定义

<a id="eq-volterra"></a>

$$
\Psi(t)=S-\mathcal K(t)+\frac14\int_0^t(t-u)\mathcal K(u)\,\mathrm d u,
\qquad \Psi(-t)=\Psi(t).
\tag{13}
$$

定义只用实际素数核，因此不预设任何零点位于临界线上。

### 定理 5.2（Volterra 桥）

<a id="thm-volterra"></a>

$\Psi$ 连续、实值、偶对称、$\Psi(0)=0$，并满足

<a id="eq-LPsi"></a>

$$
\int_0^\infty e^{-zt}\Psi(t)\,\mathrm d t
=\frac1{z^2}\frac{\xi'}{\xi}\left(\frac12+z\right),
\qquad \operatorname{Re} z>\frac12.
\tag{14}
$$

它正是 Suzuki 螺旋函数论文中的 $\Psi_\zeta$，而非项目 $\mathcal K$ 本身。

**证明。**
连续性与偶性由定义得到。原域的指数控制允许对 Volterra 积分换序，其 Laplace 变换为 $L_K(z)/z^2$。因此右端变换为

$$
\frac Sz-\left(1-\frac1{4z^2}\right)
\frac{Sz-D(z)}{z^2-\frac14}
=\frac{D(z)}{z^2}.
$$

Suzuki 的无条件变换式具有同一右端；连续且具有指数阶控制的函数由 Laplace 变换唯一确定，故两函数相等  [7](#ref-Suzuki)。

如需直接在素数侧计算，文献中的同一函数可写成

<a id="eq-psi-prime"></a>

$$
\begin{aligned}
\Psi(t)={}&8\left(\cosh\frac t2-1\right)
-\sum_{n\leq e^t}\frac{\Lambda(n)}{\sqrt n}(t-\log n)
\\
&+\frac t2\left[\frac{\Gamma'}{\Gamma}\left(\frac14\right)-\log\pi\right]
+\sum_{k=0}^{\infty}
\frac{1-e^{-(2k+\frac12)t}}{(2k+\frac12)^2},
\qquad t\geq0.
\end{aligned}
\tag{15}
$$

这保留全部素数幂与尾项。本文主要使用 [(13)](#eq-volterra)，因为它直接对接仓库的现有对象。

### 5.1 完整历史增量的 Gram 核

令

<a id="eq-GPsi"></a>

$$
G_\Psi(t,u)=\Psi(t)+\Psi(u)-\Psi(t-u).
\tag{16}
$$

Suzuki 的判据为

$$
\mathrm{RH}\quad\Longleftrightarrow\quad G_\Psi\ \text{在全部实轴上半正定}.
$$

下面给出适合本轮结构的自含推导；调用的解析输入只是实际核桥、零点公式与 [(14)](#eq-LPsi)。

### 定理 5.3（差分正性与连续接续）

<a id="thm-cocycle"></a>

设 $\psi:\mathbb R\to\mathbb R$ 连续、偶对称且 $\psi(0)=0$。若

$$
G_\psi(s,t)=\psi(s)+\psi(t)-\psi(s-t)
$$

的全部有限矩阵半正定，则存在最小实 Hilbert 空间、连续向量 $b(t)$ 及强连续正交群 $U(a)$，满足

<a id="eq-gram-b"></a>

$$
\begin{aligned}
\langle b(s),b(t)\rangle&=G_\psi(s,t),
\end{aligned}
\tag{17}
$$

<a id="eq-distance"></a>

$$
\begin{aligned}
\lVert b(t)-b(s)\rVert^2&=2\psi(t-s),
\end{aligned}
\tag{18}
$$

<a id="eq-cocycle"></a>

$$
\begin{aligned}
b(t+a)&=b(a)+U(a)b(t).
\end{aligned}
\tag{19}
$$

复化后 $U$ 为酉群。最小实现由 $b(t)$ 的闭线性张成给出，并在等距意义下唯一。

**证明。**
取形式符号 $[t]$ 的有限线性组合，以 $G_\psi$ 定义半内积；商去零范数子空间并完备化，记 $[t]$ 的像为 $b(t)$。Cauchy–Schwarz 使零范数向量与所有向量正交，故商空间良定义。展开 Gram 得 [(18)](#eq-distance)，特别地 $b(0)=0$ 且 $b$ 连续。

在稠密张成空间定义

$$
U(a)b(t)=b(a+t)-b(a).
$$

直接展开四个核值，得到

$$
\begin{aligned}
&\langle b(a+s)-b(a),b(a+t)-b(a)\rangle\\
&\quad=G_\psi(a+s,a+t)-G_\psi(a+s,a)-G_\psi(a,a+t)+G_\psi(a,a)\\
&\quad=G_\psi(s,t).
\end{aligned}
$$

故此映射保持全部内积和零关系，因而良定义且等距。再展开可得
$U(a)U(c)=U(a+c)$、$U(-a)=U(a)^{-1}$，所以延拓为正交群。连续性先在稠密张成空间由 $b$ 的连续性得到，再以统一范数一延拓至全部空间。相同 Gram 的两个最小实现之间，按 $b(t)$ 对应定义的映射是稠密满等距，故唯一性成立。

### 定理 5.4（螺旋核的 RH 等价）

<a id="thm-screw"></a>

对 [(13)](#eq-volterra) 定义的实际 $\Psi$，下列条件等价：

$$
\mathrm{RH};\qquad
G_\Psi\ \text{全部有限阶半正定};\qquad
G_\Psi\ \text{全部一、二阶半正定}.
$$

**证明。**
RH 下零点频率 $\gamma$ 为实数，标准零点表示给

$$
\Psi(t)=\sum_\gamma\frac{1-\cos(\gamma t)}{\gamma^2},
\qquad
b(t)_\gamma=\frac{e^{i\gamma t}-1}{\gamma}.
$$

因 $\sum_\gamma \gamma^{-2}<\infty$，$b(t)\in\ell^2$，且

$$
\langle b(t),b(u)\rangle
=\sum_\gamma
\frac{(e^{-i\gamma t}-1)(e^{i\gamma u}-1)}{\gamma^2}
=G_\Psi(t,u).
$$

最后一步利用频率正负对称性。因此全部有限阶正性成立。

反向只假设一、二阶正性。对角给 $\Psi(t)\geq0$，二点 Cauchy–Schwarz 用于 $s,-t$，给

$$
|\Psi(s)+\Psi(t)-\Psi(s+t)|
\leq2\sqrt{\Psi(s)\Psi(t)}.
$$

因此 $m(t)=\sqrt{\Psi(t)}$ 次可加。连续性给 $m$ 在 $[0,1]$ 有界，把任意 $t\geq0$ 分为整数步和余步，得到
$\Psi(t)=O((1+t)^2)$。

所以 $L_\Psi(z)=\int_0^\infty e^{-zt}\Psi(t)\,\mathrm d t$ 在 $\operatorname{Re} z>0$ 全纯。令 $F(z)=\xi(\tfrac12+z)$，由 [(14)](#eq-LPsi) 初始域恒等式得

$$
F'(z)-z^2L_\Psi(z)F(z)=0.
$$

恒等定理把它延拓到整个右半平面。零点阶数的同一论证排除该域全部零点，再用函数方程得到 RH。

文献已有该 RH 等价；本证明把反向步骤整理成“二元 Cauchy–Schwarz、次可加增长、解析零点排除”这条链。它没有声称一般二元正核均可全局拼接。

<a id="section-6"></a>

## 6. 简洁几何：静态频谱、当前差异与累计历史

### 6.1 从原实际核构造统一门流

### 命题 6.1（平移正核的酉实现）

<a id="prop-stationary"></a>

若 $\mathcal K(t-s)$ 全局半正定，则存在 Hilbert 空间、向量 $v$ 和强连续酉群 $U(t)$，使

$$
\lVert v\rVert^2=S,\qquad
\langle U(s)v,U(t)v\rangle=\mathcal K(t-s).
$$

**证明。**
以形式符号 $e_t$ 定义内积 $\langle e_s,e_t\rangle=\mathcal K(t-s)$，商零并完备化。平移 $e_t\mapsto e_{t+a}$ 保内积，逆为平移 $-a$，故诱导酉群。连续性来自
$\lVert e_{t+h}-e_t\rVert^2=2[S-\mathcal K(h)]\to0$。取 $v=e_0$。

在 RH 下可直接选择

$$
v_\gamma=\frac1{\sqrt{\frac14+\gamma^2}},
\qquad (U(t)w)_\gamma=e^{i\gamma t}w_\gamma.
$$

于是每个频率是一个圆周相位，整体是可数多个二维旋转平面的 Hilbert 直和。这里的谱坐标还不是某个已识别物理系统的能量；把它作为实际 Hamiltonian 需要时间单位、作用尺度和操作对应。

### 定理 6.2（当前差异加累计历史）

<a id="thm-history"></a>

在命题 [6.1](#prop-stationary) 的实现中，定义有向 Bochner 积分

$$
c(t)=\int_0^tU(r)v\,\mathrm d r,\qquad
b(t)=(U(t)v-v)\oplus\tfrac12c(t).
$$

则

$$
\lVert b(t)\rVert^2=2\Psi(t),\qquad
\langle b(s),b(t)\rangle=G_\Psi(s,t),
$$

且 $b$ 对 $U\oplus U$ 满足 cocycle 接续式。

**证明。**
由于 $\mathcal K$ 实偶，

$$
\lVert c(t)\rVert^2
=\int_0^t\int_0^t\mathcal K(r-u)\,\mathrm d r\,\mathrm d u
=2\int_0^t(t-u)\mathcal K(u)\,\mathrm d u \quad(t\geq0).
$$

同时 $\lVert U(t)v-v\rVert^2=2[S-\mathcal K(t)]$，两项相加与 [(13)](#eq-volterra) 一致。积分换元给
$c(t+a)=c(a)+U(a)c(t)$，当前差异也满足同样接续式，故 $b$ 满足 cocycle。其增量长度只依赖时间差，实内积的极化恒等式给出 $G_\Psi$。负参数由有向积分及偶性处理。

这是可以精确使用的“欧拉弹簧”图像：静态对象给出频谱和 $v$，内部参数选择 $U(t)v$；当前与原点的差异，加上累计历史，共同组成一个保持增量关系的几何对象。这个整体通常无限维；三维只属于每一对关系的规范化窗口。

### 6.2 仿射关系何时能成为同一中心的旋转

一般 cocycle 给出的作用是

$$
T(a)x=U(a)x+b(a).
$$

它首先是“保持长度的转动加平移”，未必有固定中心。

### 定理 6.3（有界轨道与固定中心）

<a id="thm-fixed"></a>

若定理 [5.3](#thm-cocycle) 中的 $b(\mathbb R)$ 有界，则存在 $v_0\in\mathcal H$，使

$$
b(t)=v_0-U(t)v_0.
$$

**证明。**
有界集合 $B=b(\mathbb R)$ 在 Hilbert 空间中有唯一最小包围球中心。可由平行四边形恒等式证明：任意趋向最小半径的中心序列为 Cauchy 列，极限存在；若有两个不同中心，其中点会给更小半径，矛盾。每个 $T(a)$ 是保持 $B$ 的仿射满等距，故保持这个唯一中心 $v_0$。于是
$U(a)v_0+b(a)=v_0$。

### 例 6.4（连续正差分不自动有固定中心）

取 $\psi(t)=t^2$，则 $G_\psi(s,t)=2st$ 半正定。可取
$b(t)=\sqrt2\,t\in\mathbb R$、$U(t)=I$。其增量连续且完全相容，却无有界轨道或固定中心。

因此“所有态都是同一个全局态的酉读出”比一般的差分相容更强。有界性不能未经证明就赋给实际算术核。

### 6.3 完整零点轨迹并非光滑曲线

<a id="sec-nonsmooth"></a>

### 定理 6.5（RH 下完整螺旋的不可微性）

即使 RH 成立，标准向量

$$
b(t)_\gamma=\frac{e^{i\gamma t}-1}{\gamma}
$$

在 Hilbert 范数意义下仍处处不可微。

**证明。**
在 $t=0$，对任意有限频率集合 $E$，

$$
\liminf_{h\to0}\left\|\frac{b(h)}h\right\|^2
\geq\sum_{\gamma\in E}
\lim_{h\to0}\left|\frac{e^{i\gamma h}-1}{\gamma h}\right|^2
=|E|,
$$

重数按独立坐标计。非平凡零点无限，故右侧可任意大。平稳增量把同一结论传到每个 $t$。

等价地，$v_\gamma=1/\gamma\in\ell^2$，但对角生成元
$(Aw)_\gamma=\gamma w_\gamma$ 的定义域要求
$\sum_\gamma\gamma^2|w_\gamma|^2<\infty$；该 $v$ 不满足。实际核轨道的
$v_\gamma=(\tfrac14+\gamma^2)^{-1/2}$ 也不在该定义域。

应当采用的精确表述是：门群可以强连续；有限频率截断有光滑轨迹；无限轨迹的微分方程只在生成元定义域上成立。把所有轨迹都预设为光滑，会排除这里本来合法的完整算术实现。平滑滤波会改变核，返回原核时必须控制极限。

<a id="section-7"></a>

## 7. 完整候选 C121：内生差分与忠实接续

### 7.1 一条总原则及其明确条件

**C121 总原则。**
同一 $\Omega$ 中，内容由可相干组合、可顺序接续的内部关系确定。完整表示保留既有内容之间的全部比较；读出是内部支路的归一分解；后继由实际接续决定；独立并置保留各自的复相位约定。比较历史增量时，共同的平稳接续保持增量之间的关系。任何改写、完成或极限都须保留所声称的同一个对象。

以下条件合起来构成一份完整候选，不是任择菜单。有限模型是主范围；无限模型需另行注明有界表示、完备化及生成元定义域。

### 定义 7.1（C121 的六组内部约束）

<a id="def-candidate"></a>

1. **Q1.** **相干历史的类型。**
   有限历史的线性组合组成复含幺结合 $*$-代数 $\mathcal A$。乘法 $ba$ 表示先 $a$ 后 $b$，$1$ 表示空接续，$*$ 表示对偶而非每个过程的物理逆。也可从实结构表述复性：提供内部中心 $J$，满足


   $$
   J^2=-1,\qquad J^*=-J,
   $$


   并要求物理接续与 $J$ 相容。这是承重条件，没有从“两个读出正交”自动推出。

2. **Q2.** **同源的归一正比较。**
   存在内部线性评价 $\omega:\mathcal A\to\mathbb C$，满足


   $$
   \omega(1)=1,\qquad \omega(a^*a)\geq0.
   $$


   定义 $K_\omega(a,b)=\omega(a^*b)$。不同窗口在保单位、保乘法、保对偶的嵌入上保持同一评价。有限扇区采用有限维表示；模型允许全部相应正评价。

3. **Q3.** **读出拆并与完整支路。**
   完整有限读出由内部支路 $m_r$ 给出，


   $$
   \sum_r m_r^*m_r=1,\qquad p_r=\omega(m_r^*m_r).
   $$


   同一效果在不同合法拆分中有同一读数；正效果的合法二元合并可加。概率和内部评价的对应是操作性条件。实际支路与它对全部后继读口的交叉关系一并保存。

4. **Q4.** **完整过程与内部记录。**
   在已建立的物理振幅空间中，完整过程可以先仅视为函数 $V$，但要求对整个输入空间保持完整复内积：


   $$
   \langle Vx,Vy\rangle=\langle x,y\rangle.
   $$


   记录和失败分支均在 $\Omega$ 内。选取记录给条件过程，忽略记录给非选择过程。要覆盖全部标准有限量子仪器，还须供应所需初始化记录及全部这类有限接口；受限门菜单不自动拥有这些资源。

5. **Q5.** **独立复合与覆盖。**
   独立准备的产品历史比较按乘法复合，产品向量的相干张成覆盖联合振幅空间，并共享同一内部 $J$。允许全部联合正评价以及非零角代数和有限经典直和。独立准备的因子化只定义产品结构，不强迫所有联合态因子化；联合态可纠缠。
   若要重构全部有限维量子系统，还要求至少一个维数 $q\geq2$ 的非交换矩阵扇区、任意有限独立副本及全部非零投影角的供给。

6. **Q6.** **可逆接续、平稳增量与对象忠实。**
   双向完整过程称可逆。讨论连续时间时，另给强连续一参数群与时间单位。平稳子系统的平移保持增量内积，按定理 [5.3](#thm-cocycle) 重构接续；不要求所有外控或时变过程平稳。对于算术实例，所有关系必须等于 [(2)](#eq-K) 的实际数值，不能用另一个正完成替代。

### 7.2 哪些是定义约束，哪些还需要证明

内生性在这里的含义是：评价、参考、记录、控制和检验对象都属于同一个 $\Omega$，无需外部观察者补测量。它不意味着每个可写下的数表天然为正，也不意味着该模型类必然等于物理世界。

Q1–Q6 给出可重构的模型类；原生项目是否供应复结构、全部效果、共同源、记录资源、独立性和覆盖，是需要证明或实验检验的实例化问题。正性决定哪些数表能被实现；给一个对象起名为“合法关系”不能证明其存在。

完全交换的有限代数产生经典概率，非交换矩阵块产生量子部分。纯粹的静态性、地址内生性或一般关系一致性都容许经典模型。因此本候选没有声称从“一切内生”唯一排除经典或实数量子替代方案。

<a id="section-8"></a>

## 8. 从候选恢复标准有限维量子力学

### 8.1 Hilbert 表示及平方范数

### 定理 8.1（有限 GNS 重构）

<a id="thm-GNS"></a>

在有限维复 $*$-代数 $\mathcal A$ 及归一正评价 $\omega$ 上，定义

$$
N_\omega=\{a:\omega(a^*a)=0\}.
$$

则向量商 $\mathcal H_\omega=\mathcal A/N_\omega$ 是 Hilbert 空间，左乘定义 $*$-表示
$\pi(a)[b]=[ab]$，且

$$
\Omega_\omega=[1],\qquad
\omega(a)=\langle \Omega_\omega,\pi(a)\Omega_\omega\rangle.
$$

特别地，

$$
p_m=\omega(m^*m)=\lVert \pi(m)\Omega_\omega\rVert^2.
$$

**证明。**
令 $\langle a,b\rangle=\omega(a^*b)$。正性与极化给 Hermitian 半内积；对
$\omega((a+zb)^*(a+zb))\geq0$ 选择复参数 $z$，得到

$$
|\omega(a^*b)|^2\leq\omega(a^*a)\omega(b^*b).
$$

故零范数元素与全部元素正交，商内积良定义。

若 $b\in N_\omega$，取 $x=a^*ab$，Cauchy–Schwarz 给
$\omega(x^*b)=0$。而 $x^*b=b^*a^*ab$，故 $ab\in N_\omega$；
所以 $N_\omega$ 是左理想。左乘良定义，并由

$$
\omega((ab)^*c)=\omega(b^*a^*c)
$$

得到 $\pi(a)^*=\pi(a^*)$。有限维保证算符有界且空间完备。其余公式由 $\omega(1)=1$ 及定义直接得到。

必须注意：$N_\omega$ 通常不是双边理想，$\mathcal A/N_\omega$ 是**向量商**，不是商代数。代数的忠实像是 $\pi(\mathcal A)\cong\mathcal A/\ker\pi$。

有限维 $*$-矩阵像 $\pi(\mathcal A)$ 是有限维 $C^*$-代数，分解为有限个全矩阵块。去掉经典超选择标签后的一个单块是 $M_d(\mathbb C)$。允许的独立复合及非零角闭包给所声明的有限系统；若没有这些供给，不能只凭一个代数断言任意维数或任意门均可实现。

### 8.2 从效果拆并推出 Born 形式

### 定理 8.2（全部效果的概率表示）

<a id="thm-born"></a>

设有限维复空间上的效果概率
$\mu:\{E:0\leq E\leq I\}\to[0,1]$ 满足

$$
\mu(I)=1,\qquad
\mu(E+F)=\mu(E)+\mu(F)\quad(E+F\leq I).
$$

则唯一存在 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，使

$$
\mu(E)=\operatorname{Tr}(\rho E).
$$

**证明。**
可加性首先给有理齐次性，非负性给单调性。用有理数上下逼近，得到
$\mu(tE)=t\mu(E)$ 对 $t\in[0,1]$ 成立。对任意 $A\succeq0$，选择
$r\geq\lVert A\rVert$，定义 $L(A)=r\mu(A/r)$；齐次性保证其与 $r$ 无关。
在共同缩放下用可加性，得到正锥上的可加、齐次泛函。再令
$L(A-B)=L(A)-L(B)$，可加性保证自伴部分的扩张良定义，最后复线性扩张到全部矩阵。

有限维迹配对非退化，故唯一有自伴矩阵 $\rho$ 满足
$L(A)=\operatorname{Tr}(\rho A)$。对每个秩一正投影的非负性给 $\rho\succeq0$，
$L(I)=1$ 给 $\operatorname{Tr}\rho=1$。

这是效果版 Gleason 结果的有限维证明  [8](#ref-Busch)，包含 $d=2$。
密度矩阵集合的极点恰为秩一投影：有两个正特征值时可作相反的小扰动而非极点；秩一时任何正凸分解都须在其一维支撑上。于是对纯态及秩一效果，

$$
\rho=\lvert \psi\rangle\langle \psi\rvert,\quad E=\lvert \phi\rangle\langle \phi\rvert
\quad\Longrightarrow\quad
p=|\langle \phi,\psi\rangle|^2.
$$

平方律来自正评价的 Hilbert 表示及全部效果拆并，没有从“存在一个允许结果”直接推出概率数值。

### 例 8.3（qubit 仅有投影配对归一不够）

对 Bloch 单位方向 $\bm n$，令

$$
\mu(P_{\bm n})=\frac{1+n_z^3}{2}.
$$

它非负并满足
$\mu(P_{\bm n})+\mu(P_{-\bm n})=1$，但不是任何密度矩阵的仿射 Born 形式。因此不能把全部效果可加性弱化为二态的正交投影配对归一。

### 8.3 内积保持推出过程线性

### 定理 8.4（完整比较保持的刚性）

若全空间函数 $V:\mathcal H_1\to\mathcal H_2$ 保持全部复内积，则 $V$ 复线性且等距。若又满射，则 $V$ 酉。

**证明。**
先有 $V0=0$。把
$\lVert V(x+y)-Vx-Vy\rVert^2$ 展开，每一项由内积保持换回输入内积，结果为零。类似地，对每个 $\lambda\in\mathbb C$，展开
$\lVert V(\lambda x)-\lambda Vx\rVert^2$，也为零。故可加且复齐次。
满射等距的逆也等距，因此为酉。

这使用完整复比较；仅保留内积模平方还允许反酉变换，不能使用同一结论。

### 8.4 内部记录给出 Kraus 仪器与完全正性

设完整等距过程 $V:\mathcal H\to\mathcal H'\otimes\mathcal H_R$，取记录正交基 $\lvert r,\alpha\rangle$。展开

$$
V\psi=\sum_{r,\alpha}M_{r\alpha}\psi\otimes\lvert r,\alpha\rangle,
\qquad
\sum_{r,\alpha}M_{r\alpha}^*M_{r\alpha}=I.
$$

选择记录 $r$ 给

$$
\mathcal I_r(\rho)=\sum_\alpha M_{r\alpha}\rho M_{r\alpha}^*.
$$

对任意旁观参考系统，$\mathcal I_r\otimes\mathrm{id}$ 仍是正项夹乘之和，所以完全正；全部结果求和保迹。反向，任意有限 Kraus 家族都由上述 $V$ 给出内部记录实现。所需空白记录和允许的等距必须属于模型资源。

### 8.5 实际支路决定测后态

先支路 $m$ 后支路 $n$，联合权重为

$$
p(n,m)=\omega((nm)^*(nm))
=\omega(m^*n^*nm).
$$

若 $p_m=\omega(m^*m)>0$，条件归一唯一给

<a id="eq-update"></a>

$$
\omega_m(A)=\frac{\omega(m^*Am)}{\omega(m^*m)},
\qquad
\rho_m=\frac{m\rho m^*}{\operatorname{Tr}(\rho m^*m)}.
\tag{20}
$$

这也是正归一评价，因为
$\omega_m(A^*A)=\omega((Am)^*(Am))/p_m\geq0$。而且，只要相应分支概率非零，就有严格的关系接续式

<a id="eq-conditional-cocycle"></a>

$$
(\omega_m)_n=\omega_{nm}.
\tag{21}
$$

证明是将两次条件归一展开：中间的 $p_m$ 约去，剩下
$\omega(m^*n^*Anm)/\omega(m^*n^*nm)$。
当实际理想支路 $m=P=P^*=P^2$ 时，

$$
\rho_P=\frac{P\rho P}{\operatorname{Tr}(\rho P)}.
$$

这就是 Lüders 形式。零概率分支没有由该公式定义的条件后态。

$\sqrt E$ 与 $U\sqrt E$ 具有同一效果 $E$，当前概率完全相同，后继通常不同。因此“给定效果”不等于“给定支路”。把理想支路选为 $\sqrt E$ 或 $P$，需要明确的无额外转动/最大比较保留条件，或把该支路作为实际结构给定；不能单靠概率推出。

### 8.6 复合、纠缠与连续动力学

独立准备的产品向量比较若满足

$$
\langle x\otimes y,x'\otimes y'\rangle
=\langle x,x'\rangle\langle y,y'\rangle,
$$

则把形式产品映入联合空间的映射保内积；产品张成完备使其满射，得到 Hilbert 张量积。允许全部联合正态后，$(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$ 这样的非乘积态出现，因而可以纠缠。共享历史本身并不等于纠缠；$\lvert 00\rangle$ 可由同一制备过程产生，却仍是乘积态。

有限维可微一参数酉群 $U(t)$ 满足 $U(t)^*U(t)=I$。令

$$
H=i\hbar U'(0),
$$

求导给 $H=H^*$，群律给

$$
U(t)=e^{-itH/\hbar},\qquad i\hbar\dot\psi=H\psi.
$$

无限维强连续群采用 Stone 定理  [9](#ref-Stone)；强导数只对
$D(H)$ 中的态成立。参数 $t$ 的校准及 $\hbar$ 的量纲没有从离散历史计数自动产生。

### 8.7 循环向量与“唯一宇宙态”的区别

取 $\mathcal A=M_2(\mathbb C)$、$\omega(A)=\operatorname{Tr}(A)/2$。GNS 空间可写成 Hilbert–Schmidt 矩阵空间，内积
$\langle A,B\rangle=\operatorname{Tr}(A^*B)/2$，循环向量为 $I$，代数按左乘作用。
循环向量是一个固定向量，但物理代数上的态仍是混态 $I/2$。所以 GNS 的统一向量表示并没有证明物理宇宙态纯，更没有选择唯一宇宙、粒子或 Hamiltonian。

### 8.8 有限量子重构的范围汇总

有非交换种子 $M_q(\mathbb C)$、$q\geq2$，任意独立副本给
$M_{q^n}(\mathbb C)$。对任意 $d$，选 $q^n\geq d$，取秩 $d$ 的非零投影 $P$，便有

$$
P M_{q^n}(\mathbb C)P\cong M_d(\mathbb C).
$$

这里代数角的存在与某固定状态能成功条件化是两个问题；后者还需 $\omega(P)>0$。模型允许全部正评价，才可为每个非零角选择支持其中的准备。

| 通常量子公理 | 本候选的来源与条件 |
|---|---|
| 复 Hilbert 空间 | 复历史类型与全有限正评价给 GNS；复结构或内部 $J$ 的供给仍明确保留。 |
| 叠加与线性 | 相干组合属于历史类型；完整复比较保持把全过程函数强制为线性等距。 |
| 密度态与 Born | 全效果可加性给正归一线性泛函，矩阵迹对偶给 $\operatorname{Tr}(\rho E)$。 |
| 量子仪器 | 完整等距加内部正交记录给 Kraus，选择或忽略记录给 CP 仪器与 CPTP 通道。 |
| 测后更新 | 实际支路的接续和条件归一给 [(20)](#eq-update)；理想投影支路给 Lüders。 |
| 张量积与纠缠 | 共享复中心、产品比较与张成完备给张量积；全部联合正态容许纠缠。 |
| Hamiltonian 运动 | 可逆完整过程给酉；另给连续群与时间单位，得到生成元及其定义域。 |
| 观察者内生 | 记录、参考与支路都在同一对象中；共同细化保持固定问题的评价。 |

这是完整的条件式表示理论，没有证明这六组条件逻辑独立或绝对最少，也没有把所有量子力学内容变成逻辑恒真式。

<a id="section-9"></a>

## 9. 反着推：离线模式与被破坏的关系

### 9.1 反射对称可以保持不定形式，不能保证正长度

考虑形式频率
$\lambda_\pm=\gamma\pm i\delta$，其中 $\delta>0$，及

$$
A=\begin{pmatrix}\gamma+i\delta&0\\0&\gamma-i\delta\end{pmatrix}.
$$

其传播为

$$
e^{-itA}=e^{-i\gamma t}
\begin{pmatrix}e^{\delta t}&0\\0&e^{-\delta t}\end{pmatrix}.
$$

一方向放大，另一方向缩小。它保持不定 Hermitian 形式

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
e^{itA^*}J e^{-itA}=J.
$$

但不存在正定 $G$ 使 $A^*G=GA$。若 $Aw=\lambda w$ 且 $\lambda\notin\mathbb R$，该等式给

$$
(\lambda-\overline\lambda)w^*Gw=0,
$$

与 $G>0$、$w\ne0$ 矛盾。

这解释了为何零点的反射四元组不自动等于正定的酉平衡。这个二模例子只描述离线频率的结构；完整 $\zeta$ 无限和的失败则由定理 [3.1](#thm-binary) 证明，不能用这个玩具模式替代。

### 9.2 两条必须排除的错误捷径

### 例 9.1（普通正定函数仍可有非实零点）

任取 $a>1$，

$$
f(z)=\frac{a+\cos z}{a+1}.
$$

它偶对称、实型、$f(0)=1$，而 $f(t-s)$ 是正核，因为

$$
f(t)=\int_{\mathbb R}e^{itx}\,\mathrm d\mu(x),\qquad
\mu=\frac a{a+1}\delta_0+
\frac1{2(a+1)}(\delta_1+\delta_{-1}).
$$

然而所有零点

$$
z=(2k+1)\pi\pm i\,\operatorname{arcosh}(a)
$$

都不在实轴。

因此不能从某个函数的正定性直接推出该函数实零点。实际上，$\Xi(t)=\xi(\tfrac12+it)$ 的归一化已有无条件正 Fourier 表示  [10](#ref-RodgersTao)；本稿必须使用与 $\xi'/\xi$ 忠实对应的特殊核 $\mathcal K$ 或 $G_\Psi$。

第二条捷径是把任意 $\rho=\beta+i\gamma$ 只保留虚部 $\gamma$，然后定义实谱对角算子。这当然得到实谱，却删去了待检验的 $\beta-\tfrac12$。谱实现必须保留完整零点及实际解析恒等式，否则无法判别 RH。

### 9.3 删去条件后的后果

| 删去的条件 | 明确后果 | 应检查的二元关系 |
|---|---|---|
| 全有限正比较 | 三阶反例出现负范数方向，尽管每对合法。 | 旧整体与新分支。 |
| 实际对象忠实 | 可以造出正扩张，却改变真实远距离值，无法推出 RH。 | 局部实现与指定算术数据。 |
| 完整复比较 | 反酉变换仍可能保转移概率，不能推出复线性。 | 接续前后两个幅度。 |
| 全效果拆并 | $n_z^3$ 例满足投影配对归一，却非 Born。 | 同一效果的不同分解。 |
| 实际后继支路 | $\sqrt E$ 和 $U\sqrt E$ 同概率不同后态。 | 当前事件与未来读口。 |
| 独立复合完备性 | 产品实验外可加不可见扇区，张量积不唯一。 | 产品关系与整体关系。 |
| 固定中心/有界性 | $b(t)=\sqrt2\,t$ 是纯平移，不能成为固定态轨道差。 | 历史增量与共同中心。 |
| 生成元定义域 | 完整 $\zeta$ 轨迹虽连续却不可微。 | 有限截断与无限极限。 |
| 全部尺度 | 短窗任意阶正性仍不能排除远处越界。 | 近关系与远交叉关系。 |

<a id="section-10"></a>

## 10. 可以继续证明的具体目标及其限制

### 10.1 全尺度任务被压缩成一个确定不等式

下一项真正足够的算术命题是

<a id="eq-target"></a>

$$
\boxed{\quad
|\mathcal K(\log(m/n))|\leq
2+\gamma_E-\log(4\pi)
\quad\text{对全部正整数 }m,n.
\quad}
\tag{22}
$$

它与 RH 等价，因而仍然承担完整难度。它的好处是对象、归一化、负见证与穷尽顺序都明确。

等价的全局任务还可写为所有实际 Schur 余量非负、$G_\Psi$ 全轴正性，或相应完整 Weil 测试正性。等价改写之间可以传递结论，不能用几种改写互相当作已证明前提。

### 10.2 为什么归一化与小误差本身没有消除障碍

设 Hermitian $B$ 有负方向 $c^*Bc<0$。对任意可逆坐标变换 $T$，令
$d=T^{-1}c$，则

$$
d^*T^*BTd=c^*Bc<0.
$$

所以可逆重编码、正尺度归一化不消除负方向。投影删除该方向可以得到正压缩，但同时丢弃实际关系，不能作为原对象的忠实实现。

在近邻极限中 Schur 余量可趋零，因而不能要求一个对所有尺度、所有节点间距都统一为正的谱隙。这也意味着有限精度验证必须有与具体配置匹配的误差界。

### 10.3 若想用遍历和贪心完成证明，还缺哪一步

整数双地址定理使反例搜索有明确的穷尽对象。若 RH 为假，某个有限双地址严格越界；精确区间计算若最终分离出负余量，就可认证反例。它没有给反例索引上界；若 RH 为真，有限搜索永远不能单独认证全称命题。

要把 Zeckendorf 排列的特殊递归用于证明，必须进一步证明：它产生的结构关系能控制**所有跨距离**的实际 $\mathcal K$ 值，或使新增全部交叉关系的 Schur 余量始终非负。仅有遍历性、相邻共同项或局部小步正性，不提供这个控制。

### 10.4 理论完整性与物理解释的现阶段

本稿已经给出一个有经典与量子扇区、内部记录、操作、概率、复合及时间解释的完整条件模型，并给出其精确算术接口。尚未完成的来源选择包括：为何项目原生构造必给复相位结构；为何它覆盖全部所需正评价与独立复合；实际宇宙对应哪一个内部态和 Hamiltonian；为何实际素数核满足全轴二元界。

这些问题不应藏进“$\Omega$ 内部已经都有”的语句中。内生性给出对象归属；存在性、唯一性、正性和可取得性仍分别需要证明。

<a id="section-11"></a>

## 11. 一段完整的白话描述

可以把整个结构想成一张静止的关系网。观察者、记忆、门和读口都在网里；观察者每次往前走，读到的是“现在与刚才怎样对应”，并把尚未读出的差异留在内部记录中。一对内容加上它们的相位和相对权重，归一化后可以放进一个三维球；整张网要求这些比较能接成同一个整体，不能某处突然要求负的长度平方。可逆地保留完整比较，就表现成酉运动；把一次读出拆成完整支路并保持总权重，就得到平方概率；选中一条实际支路，再沿它接续，就得到测后态。

素数也定义了一张非常具体的关系网：关系值是本文的实际核 $\mathcal K$。如果这张算术网在所有尺度都能保持合法的二元比较，它就可以组成守长度的连续门流，全部非平凡零点也被锁在临界线上。假如有离线零点，那么一定存在两个有限整数地址，使比较越出球的边界。我们已经证明这种失败一定会怎样出现，也把当前差异与累计历史连接成精确的螺旋关系；还没有证明的是，实际素数给出的比较在所有尺度都不会越界。

<a id="section-12"></a>

## 12. 符号、零边界与可复核口径

| 符号 | 含义 |
|---|---|
| $\Omega$ | 候选中的共同内部对象；不是预先认证的物理宇宙态。 |
| $\omega$ | 内部正归一评价；与 $\Omega$ 区分。 |
| $\Omega_\omega$ | GNS 循环向量；不单独保证评价纯。 |
| $\mathcal K$ | 固定素数核 [(2)](#eq-K)，对角总量为 $S>0$。 |
| $\Psi$ | Volterra 差分函数 [(13)](#eq-volterra)，不是 $\mathcal K$。 |
| $G_\Psi$ | 非平移不变的锚定增量 Gram 核；其增量距离平移不变。 |
| $K_\omega$ | 历史词核 $\omega(a^*b)$，不与算术核自动认同。 |
| $\rho,\gamma$ | $\rho$ 为完整复零点；只有在声明 RH 后，$\rho=\tfrac12+i\gamma$ 中 $\gamma$ 才按实频率使用。 |
| $J$ | 第 7 节的内部复结构；第 9 节玩具例的不定形式另按该处定义，二者不是同一对象。 |

 主要边界：

- 二元迹为零时不作 Bloch 归一化；正矩阵此时只能为零。
- Schur 逆使用 Moore–Penrose 逆并保留范围条件。
- 零概率分支不定义条件后态。
- $N_\omega$ 是左理想，不擅自称为双边商代数。
- 参考未被弃置的完整过程保内积；局部条件过程可以不保范数。
- $\mathcal K$ 的全轴界以及与其等价的 RH 均未证明。

<a id="section-13"></a>

## 13. 来源、归属与固定路径

本稿新整理的二元整数见证、差分接续与模型解释属于普通数学推导，未另行声称 Lean 认证。以下所有仓库路径固定到同一快照；文献条目使用作者原文或官方来源。

<a id="references"></a>

## 参考文献

<a id="ref-RepoLocal"></a>

### [1]

The Omega Institute. *ActualKernelLocalPositivity.lean*.
[https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.lean](https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.lean).
已读实际核定义、相关证明和最终 `exists_window_posDef` 声明。

<a id="ref-RepoLaplace"></a>

### [2]

The Omega Institute. *ActualZeroLaplace.lean*.
[https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.lean](https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.lean).
实际重数零点、总质量、加权 resolvent 和原域 Laplace 恒等式。

<a id="ref-RepoWeil"></a>

### [3]

The Omega Institute. *ExplicitFormulaWeilCriterion.lean*.
[https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/D5/S3/Weil/Separator/ExplicitFormulaWeilCriterion.lean](https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/D5/S3/Weil/Separator/ExplicitFormulaWeilCriterion.lean).
`ZeroData` 与 Archimedean 收敛前提均保留。

<a id="ref-RepoOff"></a>

### [4]

The Omega Institute. *OffLineNonrealZeroNegativeWeilSquare.lean*.
[https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.lean](https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/D5/S3/Weil/ZetaBridge/OffLineNonrealZeroNegativeWeilSquare.lean).
离线非实零点给负平方见证的有条件接口及尾项控制。

<a id="ref-RepoBoundary"></a>

### [5]

The Omega Institute. *AURIC actual zeta boundary, bulk, Cayley defect and A370630 Schur recursion*.
[https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/docs/develop/theory/AURIC_ACTUAL_ZETA_BOUNDARY_BULK_CAYLEY_DEFECT_AND_A370630_SCHUR_RECURSION.md](https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/docs/develop/theory/AURIC_ACTUAL_ZETA_BOUNDARY_BULK_CAYLEY_DEFECT_AND_A370630_SCHUR_RECURSION.md).
已读实际算术对象、Laplace 桥、全轴正性桥及剩余缺口；它是理论参考稿。

<a id="ref-RepoC117"></a>

### [6]

The Omega Institute. *AURIC common source, self-reference and observer sequences C117*.
[https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md](https://github.com/the-omega-institute/trureturing/blob/c7f3e33e5c6a0f7067e09f4dbd0d101e5e675539/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md).
已读相关 Gram 完成、量子恢复与完整候选章节；未认证整卷。

<a id="ref-Suzuki"></a>

### [7]

Masatoshi Suzuki. *Aspects of the screw function corresponding to the Riemann zeta-function*.
arXiv:2206.03682v4, 2023.
[https://arxiv.org/abs/2206.03682v4](https://arxiv.org/abs/2206.03682v4).
Theorems 1.1–1.2 及 4.2 分别提供实际变换、螺旋正性等价和小窗口正性。

<a id="ref-Busch"></a>

### [8]

Paul Busch. *Quantum states and generalized observables: a simple proof of Gleason's theorem*.
Physical Review Letters 91, 120403 (2003).
[https://arxiv.org/abs/quant-ph/9909073v3](https://arxiv.org/abs/quant-ph/9909073v3).

<a id="ref-Stone"></a>

### [9]

Marshall H. Stone. *Linear transformations in Hilbert space. III. Operational methods and group theory*.
PNAS 16, 172–175 (1930).
[https://pmc.ncbi.nlm.nih.gov/articles/PMC1075964/](https://pmc.ncbi.nlm.nih.gov/articles/PMC1075964/).
连续酉群的生成元背景；无限维强微分须保留定义域。

<a id="ref-RodgersTao"></a>

### [10]

Brad Rodgers and Terence Tao. *The de Bruijn–Newman constant is non-negative*.
arXiv:1801.05914v5 (2021), introduction equations (1)–(3).
[https://arxiv.org/abs/1801.05914](https://arxiv.org/abs/1801.05914).
引用其完成函数的 Fourier 表示，不把该正定性当作 RH 证明。

<a id="ref-Clay"></a>

### [11]

Clay Mathematics Institute. *Riemann Hypothesis*.
[https://www.claymath.org/millennium/riemann-hypothesis/](https://www.claymath.org/millennium/riemann-hypothesis/).
本轮访问时仍列为未解决问题。
