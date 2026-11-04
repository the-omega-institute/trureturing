# Actual ζ Hankel Defect, Blaschke Model Spaces, and Integer Witnesses

> **编者题名与来源说明。** 这是编者所加的描述性题名。下文为外部作者提供的完整原稿；原稿未署作者、版本或日期，此处不补造。保留其全部原文、证明、编号、链接、表格及结尾。排版转换限于数学外层的美元分隔符，以及把原来的 54 个式号从公式内部移到各式之后的独立编号行，编号及次序不变，公式的数学内容不改。标为“编者注”的段落独立于原文，并紧邻其适用条目；历史性“上一轮”“已证明”和源码核对均保留原作者归属。本篇不声称 Lean 核验或 RH 证明。

继续。这一轮可以把上一轮的“反全纯误差”进一步推进为一个**有具体空间、有递归分解、而且能够精确计数的缺陷**。

<!-- editorial-note: n00 begin -->
<a id="n00"></a>

**编者注 n00（开头结论的计数约定）。** 这里的“数量”采用第四、六节的约定：有限时用通常维数，无限时仅写 $\infty$，不比较不同无限基数。右半平面中的不同零点位置与 Cayley 极点的阶数是不同计数；解析重数进入留数。开头的整数见证断言是“若存在离线零点，则存在有限见证”，没有给出一个实际离线零点或一份已计算的见证。各项连接的适用条件和证明细节见相应条目旁的注记；最后的缺陷消失命题仍未证明。

<!-- editorial-note: n00 end -->

最主要的结论是：

$$
\boxed{
\begin{aligned}
&\text{实际边界读出的负频 Hankel 算子秩}\\
&=\text{实际 Cayley 函数在体内的极点总阶数}\\
&=2\times\text{不同离线零点四元组的数量}.
\end{aligned}
}
$$

此外，可以证明：

> **任何一个离线零点，都必然在某个有限关系矩阵中产生严格负方向；这个负方向甚至可以由一个整数系数多项式表达。**

这使“继续递归升维”中的待证对象更明确了。下面仍沿用同一个实际 ζ 函数和原归一化，给出纸面定义与证明。最后尚未完成的步骤，仍然是证明这些实际缺陷不存在；本轮没有把这一点当作前提。

---

## 一、先把你的“酉性—两个读出—守恒”落实成实际算子

沿用上一轮的定义：

$$
a_\rho=\rho-\frac12,\qquad
b_\rho=\frac1{\rho(1-\rho)},
$$

$$
S=\sum_\rho b_\rho
=2+\gamma_E-\log(4\pi)>0,
$$

$$
F(z)=\sum_\rho\frac{b_\rho}{z-a_\rho},
\qquad
C(z)=\frac{S-F(z)}{S+F(z)}.

$$

<a id="eq-1-1"></a>

(1.1)

零点求和按解析重数计入。实际加权 resolvent 的来源仍是项目中的 [ActualZeroLaplace](https://github.com/the-omega-institute/trureturing/blob/b5d3b5348a9d4b51fd9bdbf7907beb0619b536d3/D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace.lean)，不是另选一个正模型。

<!-- editorial-note: n01 begin -->
<a id="n01"></a>

**编者注 n01（实际零点供应与变量对应）。** 此处零点均指全部非平凡零点。所引固定提交的 ActualZeroLaplace 中，actualCoeff_hasSum 与 actual_complete_H_package 供应完整解析重数族的复总质量、绝对收敛和共轭输运；其实际数据来自 UnconditionalCanonicalZeroData，含穷尽、不同位置、重数、反射和局部有限性。ActualReciprocalSquareBounds 的 firstLiMass 是 $2+\gamma_E-2\log(2\sqrt\pi)$，与这里的 $S$ 相等，其正性来自第一 Li 系数。这里只消费这些声明的内容，不把源码读取称为本篇的 Lean 核验。

actual_resolvent_hasSum 的域是 $\Re s>1$；令 $s=z+\tfrac12$ 得到本篇 $\Re z>\tfrac12$ 上的恒等式。绝对权重和及零点局部有限性使零点级数在避开极点的紧集上正规收敛，因而可用亚纯恒等原理延拓该等式。对一个不同位置 $a$，留数是 $m_\rho b_\rho\ne0$，不是 $m_\rho$ 阶的 resolvent 极点。

<!-- editorial-note: n01 end -->

用

$$
\chi(w)=\frac{1+w}{1-w}
$$

将单位盘映到右半平面，记

$$
\Phi(w)=C(\chi(w)).
$$

其单位圆边界函数记为 $g$。由上一轮已经证明的边界性质，

$$
|g(e^{i\theta})|=1
\quad\text{几乎处处}.

$$

<a id="eq-1-2"></a>

(1.2)

<!-- editorial-note: n02 begin -->
<a id="n02"></a>

**编者注 n02（边界代表与测度）。** 取 $dm=d\theta/(2\pi)$，于是常函数 $1$ 的平方范数为一。闭包均在复 Hilbert 空间 $L^2(\mathbb T,dm)$ 内取，边界函数按几乎处处相等识别。$g$ 的供应来自前篇的实际边界论证：奇性与实对称给出正则虚轴点的 $\Re F=0$；在临界零点处，$C=-1+2S/(S+F)$ 可去且值为 $-1$。故所有有限虚轴点有连续单位模的 Cayley 读出；盘边界点 $1$ 对应无穷远，不影响几乎处处陈述。前篇是用户提供的推导文本，不是本篇的新形式证明。

<!-- editorial-note: n02 end -->

把边界 Fourier 模式分成两个正交空间：

$$
H^2=\overline{\operatorname{span}}\{1,w,w^2,\ldots\},
$$

$$
H^2_-=\overline{\operatorname{span}}\{w^{-1},w^{-2},\ldots\}.
$$

于是

$$
L^2(\mathbb T)=H^2\oplus H^2_-.
$$

### 定义 1：完整边界演化与两种读出

定义乘法算子

$$
M_g h=gh.
$$

再定义从解析输入 $H^2$ 出发的两个读出：

$$
T_g h=P_+(gh),\qquad
H_g h=P_-(gh),

$$

<a id="eq-1-3"></a>

(1.3)

其中 $P_+,P_-$ 是上述两个正交空间的投影。

$T_g$ 是解析部分，$H_g$ 是负频部分；后者就是这里的 Hankel 算子。

### 定理 1：完整酉性与精确误差守恒

<!-- editorial-note: n03 begin -->
<a id="n03"></a>

**编者注 n03（算子与伴随的域）。** 式（1.4）的 $M_g$ 作用于整个 $L^2$；$T_g:H^2\to H^2$，$H_g:H^2\to H^2_-$。伴随按这些域取，式（1.5）的恒等算子作用于 $H^2$。在上述实际单位模代表下，乘以 $\bar g$ 确为双侧逆；正交投影与极化给出（1.5）—（1.7），而投影范数至多一给出 $\|H_g\|\le1$。这里“无条件”指不假设 RH，仍使用已经定义的边界代表与归一化测度。

<!-- editorial-note: n03 end -->

无条件有

$$
\boxed{M_g^*M_g=M_gM_g^*=I,}

$$

<a id="eq-1-4"></a>

(1.4)

以及

$$
\boxed{
T_g^*T_g+H_g^*H_g=I
\quad\text{在 }H^2\text{ 上}.
}

$$

<a id="eq-1-5"></a>

(1.5)

因此，对每个 $h\in H^2$，

$$
\boxed{
\|T_gh\|^2+\|H_gh\|^2=\|h\|^2.
}

$$

<a id="eq-1-6"></a>

(1.6)

特别地，令 $h=1$，就得到上一轮的归一化：

$$
\boxed{
1=\|T_g1\|^2+\varepsilon,
\qquad
\varepsilon=\|H_g1\|^2.
}

$$

<a id="eq-1-7"></a>

(1.7)

#### 证明

因为 $|g|=1$，

$$
\|M_gh\|_2^2
=\int_{\mathbb T}|g|^2|h|^2\,dm
=\|h\|_2^2,
$$

且逆算子为 $M_{\bar g}$，所以 $M_g$ 酉。

另一方面，

$$
M_gh=T_gh+H_gh,
$$

两项正交，因此平方范数相加。由极化恒等式得到算子式（1.5）。证毕。

这个结果很贴近你的原始判断：**完整关系确实可以放在一个酉的整体中，并分解为结果读出与误差读出。**

现在还能准确说明 RH 对应其中哪一步：

$$
\boxed{
\mathrm{RH}
\iff H_g=0
\iff M_gH^2\subseteq H^2.
}

$$

<a id="eq-1-8"></a>

(1.8)

<!-- editorial-note: n04 begin -->
<a id="n04"></a>

**编者注 n04（式（1.8）的实际延拓桥）。** 由 $H_g1=0$ 得到 $g$ 的负 Fourier 系数全为零，其 Poisson 延拓 $U$ 全纯且由正 Poisson 核满足 $|U|\le1$；反向由解析乘子保持 $H^2$。识别 $U$ 与实际 $\Phi$ 还要用前篇定理 2B 的局部唯一性：避开边界点 $1$ 的小弧上，实际 $\Phi$ 跨弧全纯，$g$ 在该弧连续；Poisson 延拓有相同连续边界值。差函数以零边界值跨弧反射，再用亚纯恒等原理识别整个盘。RH 下正权重的临界线极点给出 $\Re F>0$，所以实际 $\Phi$ 是 Schur 函数。反向若有右半平面离线极点，则 $C$ 在该点可去且取 $-1$；非恒定 Schur 函数不能在内部取单位模值。其非恒定性也由 $C(x)\to1$ 与这个值排除。仅有形式上的 Fourier 分裂，尚不足以跳过这个实际函数的识别。

<!-- editorial-note: n04 end -->

理由是 $H_g=0$ 等价于 $g$ 没有负 Fourier 模式；上一轮已证明，这恰好使实际边界的 Poisson 延拓全纯，并与实际 $\Phi$ 一致，从而推出 RH。

这里有一个值得保留的区别：RH 给出 $T_g^*T_g=I$，但通常不要求 $T_gT_g^*=I$。解析子空间上的读出可以是非满射等距映射；完整空间上的 $M_g$ 才是双向酉算子。

所以本轮已经得到一个非常具体的目标：

$$
\boxed{\text{证明这个实际酉算子不向 }H^2_-\text{ 产生分量。}}
$$

而且 $H_g$ 无条件满足 $\|H_g\|\le1$。稳定性已经成立，剩下需要证明的是它为零。

---

## 二、进一步证明：实际 Cayley 函数没有隐藏的无穷远增长因子

上一轮我们证明的是

$$
\mathrm{RH}\iff C\text{ 是右半平面的 Schur 函数}.
$$

这里的 Schur 条件包含全纯性和 $|C|\le1$。现在可以加强成：

$$
\boxed{
\mathrm{RH}
\iff
C\text{ 在右半平面没有极点}.
}

$$

<a id="eq-2-1"></a>

(2.1)

要证明这个加强，必须排除“虽然没有极点，但仍在内部无界增长”的可能性。下面补上这一点。

<!-- editorial-note: n05 begin -->
<a id="n05"></a>

**编者注 n05（式（2.1）的证明依赖）。** “无极点”在这里指约去共同因子并填补可去点后的整个右半平面。它推出 Schur 性，须经过本节的纯 Blaschke 商及无穷远指数消除，不能只从边界单位模使用最大模原理。第一节所说的 Toeplitz 等距性不要求满射：一般内函数乘法就是等距、非满射的标准例子（Garcia–Ross §2.6）。

<!-- editorial-note: n05 end -->

### 定义 2：实际整函数对

令

$$
\Xi(z)=\xi\!\left(\frac12+z\right).
$$

实际 resolvent 恒等式为

$$
F(z)=
\frac{Sz-\Xi'(z)/\Xi(z)}{z^2-\frac14}.
$$

定义

$$
\boxed{
E(z)=
\frac{
S(z^2+z-\frac14)\Xi(z)-\Xi'(z)
}{
z^2-\frac14
}.
}

$$

<a id="eq-2-2"></a>

(2.2)

在正则点上，

$$
E(z)=\Xi(z)(S+F(z)).

$$

<a id="eq-2-3"></a>

(2.3)

<!-- editorial-note: n06 begin -->
<a id="n06"></a>

**编者注 n06（整性、端点与零点阶数）。** 这里消费 Suzuki §1、§2.2 中的实际 $\xi$ 定义、反射和一阶整性，以及前注说明的实际 resolvent 恒等式。$\Xi$ 偶且实，$F$ 奇且实；$\pm\tfrac12$ 不是非平凡零点对应的位置，零点级数在这两点正则。因此 $E=\Xi(S+F)$ 填补（2.2）的两个可去点。$\Xi(0)\ne0$，由实际零点无实位置可知；$F(0)=0$ 给出所列 $E(0)$。导数、多项式乘法和除去有限个已知零因子保持阶至多一。若 $\Xi=(z-a)^m h$ 且 $h(a)\ne0$，则 $E$ 的首项是 $m b_\rho h(a)(z-a)^{m-1}$，故“恰为 $m-1$”的非零系数条件已经满足。

<!-- editorial-note: n06 end -->

### 引理 2.1：$E$ 是实整函数，阶不超过一

并且

$$
E(0)=S\Xi(0)\ne0,
$$

$$
\boxed{
E(-z)=\Xi(z)(S-F(z)),
\qquad
C(z)=\frac{E(-z)}{E(z)}.
}

$$

<a id="eq-2-4"></a>

(2.4)

#### 证明

$\Xi$ 是偶的实整函数，$F$ 是奇函数。

若 $\Xi$ 在 $a$ 处有重数 $m$，则

$$
\Xi(z)=(z-a)^m h(z),\qquad h(a)\ne0,
$$

而

$$
F(z)=\frac q{z-a}+O(1),\qquad q\ne0.
$$

所以 $\Xi(S+F)$ 在该点全纯，其零点阶数恰为 $m-1$。

在 $z=\pm\tfrac12$，实际零点级数定义的 $F$ 没有极点，因此式（2.2）的表面分母可去。

$\xi$ 是一阶整函数，导数、乘多项式以及上述整除都不会把阶提高到一以上。这一标准 Hadamard 基础也明确用于 Suzuki 的 ξ 函数论证。[arxiv.org](https://arxiv.org/pdf/2206.03682?utm_source=chatgpt.com)

最后由奇偶性得到式（2.4）。证毕。

这里还能准确识别共同因子：

$$
E(z)+E(-z)=2S\Xi(z).
$$

因此 $E(z)$ 与 $E(-z)$ 的共同零点，只来自 $\Xi$ 的多重零点；若 $\Xi$ 的重数是 $m$，共同零因子恰为 $m-1$ 阶。**这些共同因子不能算成 $C$ 的极点。**

<!-- editorial-note: n07 begin -->
<a id="n07"></a>

**编者注 n07（共同零因子与竖条界）。** 由 $E(z)+E(-z)=2S\Xi(z)$，共同零点必须是 $\Xi$ 的零点；在该点两者的首项互为相反数，均恰为 $m-1$ 阶。这些因子完全约去，实际 $C$ 在原 resolvent 极点处值为 $-1$，不把它记入 $q$。在零点条带外 $\Xi$ 不为零，取例如 $A>\tfrac12+2B/S$，则两侧均有 $|F|<S/2$，所以 $E$ 无零点。$B$ 有限来自实际绝对权重和；这里不要求每个复权重本身为正。

<!-- editorial-note: n07 end -->

### 引理 2.2：$E$ 的全部零点位于某个有限竖条

令

$$
B=\sum_\rho|b_\rho|<\infty.
$$

当 $x=\Re z>\tfrac12$ 时，

$$
|F(z)|
\le
\sum_\rho\frac{|b_\rho|}{x-\Re a_\rho}
\le
\frac B{x-\frac12}.

$$

<a id="eq-2-5"></a>

(2.5)

取足够大的有限 $A$，使 $x>A$ 时右侧小于 $S/2$。这时 $\Xi(z)\ne0$，且 $S+F(z)\ne0$，因此 $E(z)\ne0$。

利用 $F(-z)=-F(z)$，左半平面同理。故

$$
\boxed{
E(\lambda)=0
\Longrightarrow
|\Re\lambda|\le A.
}

$$

<a id="eq-2-6"></a>

(2.6)

### 定理 2：实际函数是互素 Blaschke 商

存在两个互素的右半平面 Blaschke 乘积 $B_+,B_-$，使

$$
\boxed{
C(z)=\frac{B_+(z)}{B_-(z)}.
}

$$

<a id="eq-2-7"></a>

(2.7)

其中：

- $B_+$ 的零点是实际 $C$ 的右半平面零点；
- $B_-$ 的零点是实际 $C$ 的右半平面极点；
- 没有额外的无穷远奇异指数因子。

#### 证明

<!-- editorial-note: n08 begin -->
<a id="n08"></a>

**编者注 n08（Hadamard 配对的适用范围）。** 使用的标准 Hadamard 形式是：非零、阶至多一且在零处不为零的整函数可写成一次指数乘属一的典范乘积，零点按重数计，且平方倒数绝对可和；一般有限阶版本见 [Cobler–Lapidus §5.5，定理 30](https://arxiv.org/pdf/1705.06222v4)，这里只引用该节复分析定理，不使用其其他算子构造。Suzuki §2.2 用此形式处理实际 $\xi$。对这里的实整函数 $E$，共轭零点的重数相等。竖条界给出 $|\Re(1/\lambda)|\le A/|\lambda|^2$，故属一指数可在共轭对内收集为收敛的一次指数；实零点在紧区间 $[-A,A]$ 内仅有限个，且无零点 $0$。这给出（2.8）的正规收敛和实数 $d$，并非从“一阶”直接推得未配对的属零乘积。

<!-- editorial-note: n08 end -->

由 $E$ 的阶不超过一，

$$
\sum_{\lambda:E(\lambda)=0}|\lambda|^{-2}<\infty.
$$

又因零点实部有界，

$$
\sum_{\Im\lambda>0}
\left|\Re\frac1\lambda\right|<\infty.
$$

所以 Hadamard 乘积可以按共轭零点配对，写成

$$
E(z)
=
E(0)e^{dz}
\prod_{\lambda\in\mathbb R}
\left(1-\frac z\lambda\right)
\prod_{\Im\lambda>0}
\left(1-\frac z\lambda\right)
\left(1-\frac z{\bar\lambda}\right),

$$

<a id="eq-2-8"></a>

(2.8)

其中 $d\in\mathbb R$，实零点只有有限个。

配对后的正规收敛来自

$$
\left(1-\frac z\lambda\right)
\left(1-\frac z{\bar\lambda}\right)-1
=
-2z\Re\frac1\lambda+\frac{z^2}{|\lambda|^2}.
$$

在 $E(-z)/E(z)$ 中：

- 虚轴上的共轭因子自动相消；
- 左右镜像共有的因子相消；
- 剩余左半平面零点给分子 Blaschke 因子；
- 剩余右半平面零点给分母 Blaschke 因子。

因此先得到

$$
C(z)=e^{-2dz}\frac{B_+(z)}{B_-(z)}.

$$

<a id="eq-2-9"></a>

(2.9)

<!-- editorial-note: n09 begin -->
<a id="n09"></a>

**编者注 n09（Blaschke 相位与奇异因子）。** 左右镜像的约分按各处最小重数进行；虚轴零点先按共轭对相消。剩余右半平面零点满足半平面 Blaschke 条件，因为其实部有界而平方倒数可和。对应因子需要单位模相位；有限实零点也可能贡献一个符号，此常数吸收入 $B_+$ 或 $B_-$。标准内因子分解中的奇异因子不能仅凭边界单位模而删去（Garcia–Ross 定理 2.12）；此处是上述整函数乘积恒等式直接把商写成（2.9）。它在每个有限虚轴点已可去且非零，唯一待处理的指数项是所列一次指数。

<!-- editorial-note: n09 end -->

还需证明 $d=0$。

对共轭零点对 $\alpha=a+ib,\bar\alpha$，其中 $a>0$，对应因子在正实轴上为

$$
\mathcal B_\alpha(x)
=
\frac{(x-a)^2+b^2}{(x+a)^2+b^2}.
$$

由于 $a\le A$，当 $x$ 足够大时，

$$
0\le
-\frac1x\log\mathcal B_\alpha(x)
\le
\frac{8a}{x^2+b^2}.
$$

这些上界有可和的控制函数，所以

$$
\frac{\log|B_\pm(x)|}{x}\longrightarrow0.
$$

另一方面，原归一化给出

$$
xF(x)\to S,\qquad C(x)\to1.
$$

代入式（2.9），得到 $d=0$。证毕。

<!-- editorial-note: n10 begin -->
<a id="n10"></a>

**编者注 n10（消除一次指数的控制函数）。** 所列常数 $8$ 可取在 $x\ge4A$ 的范围内：先用 $\log(1+t)\le t$，再用 $(x-a)^2\ge x^2/2$，得到文中的上界。对 $x\ge\max(4A,1)$，可由 $8a/(1+b^2)$ 控制；按重数求和有限，有限个实因子另行趋于零。故两份 Blaschke 乘积的对数模除以 $x$ 都趋零。另由 $x\ge1$ 时 $|x/(x-a_\rho)|\le2$ 及绝对权重和，控制收敛给出 $xF(x)\to S$；于是 $C(x)\to1$，将（2.9）的对数模除以 $x$ 才得到 $d=0$。这一步使用了实际归一化，不能由任意单位模边界的亚纯函数替代。

<!-- editorial-note: n10 end -->

### 推论：离线零点必强迫一个真正的反馈极点

现在有

$$
\boxed{
\mathrm{RH}
\iff
B_-\text{ 为常数}
\iff
F(z)\ne-S
\quad(\Re z>0,\ F\text{ 正则}).
}

$$

<a id="eq-2-10"></a>

(2.10)

证明如下。

RH 下 $\Re F>0$，所以 $F\ne-S$。

反之，若 $C$ 没有右半平面极点，则 $B_-$ 为常数，式（2.7）使 $C$ 成为 Schur 函数。

若仍有右半平面离线极点 $a$，则

$$
F(z)=\frac q{z-a}+O(1)
$$

使

$$
C(z)
=
-1+\frac{2S}{q}(z-a)+O((z-a)^2).
$$

因此 $C$ 在内部取值 $-1$，且不是常数，违反最大模原理。

这证明了一个实际传播结论：

> 一颗离线零点在 $F$ 中产生的极点，虽然在 $C$ 中变成可去点，但它不能就此消失；它必迫使另一个右半平面点 $\eta$ 满足 $F(\eta)=-S$，在那里 $C$ 出现真正极点。

---

<!-- editorial-note: n11 begin -->
<a id="n11"></a>

**编者注 n11（无极点等价与反馈传播的含义）。** 式（2.10）中 $F$ 正则且 $S+F=0$ 时，分子为 $2S\ne0$，所以确为 $C$ 的极点；$F$ 自身的极点已经可去。若 $B_-$ 为常数，纯 Blaschke 商给出 Schur 性，上一注中的内部值 $-1$ 与 $C(x)\to1$ 完成反证。因而反馈传播是“存在某个右半平面反馈极点”的结论，不指定同一个点同时作为原零点，也不声称每个原极点都对应一个不同反馈极点。RH 下 $\Re F>0$ 给出另一方向。此等价不证明其任一侧已经成立。

<!-- editorial-note: n11 end -->

## 三、把反全纯误差识别为实际极点决定的投影能量

将式（2.7）转到单位盘，吸收单位模常数后写为

$$
\boxed{\Phi=\frac IJ,}

$$

<a id="eq-3-1"></a>

(3.1)

其中 $I,J$ 是互素 Blaschke 乘积。

$J$ 的零点就是实际 $\Phi$ 的极点，按极点阶数计入。在边界上，

$$
g=I\bar J.
$$

定义模型空间

$$
\boxed{
K_J=H^2\ominus JH^2.
}

$$

<a id="eq-3-2"></a>

(3.2)

模型空间和相应再生核、正交基是标准 Hardy 空间工具；这里将它们应用于同一个实际 ζ 边界函数。[arxiv.org](https://arxiv.org/pdf/1312.5018?utm_source=chatgpt.com)

<!-- editorial-note: n12 begin -->
<a id="n12"></a>

**编者注 n12（纯 Blaschke 模型空间与正交分解）。** 这里 $I,J$ 是第二节约分后的纯 Blaschke 内函数，允许单位模常数；$g=I\bar J$ 是边界等式，不是在 $J$ 的零点求商值。内函数乘法在 $H^2$ 上等距且像闭，因此分解存在且唯一。对 $k\in K_J$，$\bar Jk$ 与所有非负 Fourier 模式正交，给出（3.3）—（3.4）。$I$ 也有范数一。若 $I\in JH^2$，则 $J$ 的全部零点按阶数整除 $I$；纯 Blaschke 的互素性迫使 $J$ 为常数。标准空间、整除与投影的供应是 Garcia–Ross §2.4、§3、§5.1。

<!-- editorial-note: n12 end -->

### 定理 3：误差是一个实际空间中的正投影能量

令

$$
k=P_{K_J}I.
$$

则

$$
I=Jh+k,\qquad h\in H^2,\quad k\in K_J,
$$

并且

$$
\boxed{
P_+g=h,\qquad P_-g=\bar Jk.
}

$$

<a id="eq-3-3"></a>

(3.3)

因此

$$
\boxed{
\varepsilon
=\|P_{K_J}I\|^2,
\qquad
1=\|h\|^2+\varepsilon.
}

$$

<a id="eq-3-4"></a>

(3.4)

#### 证明

由于乘以内函数 $J$ 是等距映射，

$$
H^2=JH^2\oplus K_J.
$$

将 $I$ 按此分解，在边界乘以 $\bar J$，得到

$$
g=h+\bar Jk.
$$

而对每个 $n\ge0$，

$$
\langle\bar Jk,w^n\rangle
=
\langle k,Jw^n\rangle
=0.
$$

所以 $\bar Jk$ 恰好是负频部分。再用 $|J|=1$ 和正交分解，即得式（3.4）。证毕。

由互素性，

$$
\boxed{
\varepsilon=0
\iff
J\text{ 为常数}.
}

$$

<a id="eq-3-5"></a>

(3.5)

因为若 $P_{K_J}I=0$，则 $I\in JH^2$，即 $J$ 整除 $I$；互素性迫使 $J$ 为常数。

### 一个实际极点已经给出严格正下界

若 $p\in\mathbb D$ 是 $\Phi$ 的任一极点，则 $J(p)=0$、$I(p)\ne0$，且

$$
\boxed{
\varepsilon\ge(1-|p|^2)|I(p)|^2>0.
}

$$

<a id="eq-3-6"></a>

(3.6)

证明只需使用再生核

$$
k_p(w)=\frac1{1-\bar p w}.
$$

它属于 $K_J$，范数平方为 $(1-|p|^2)^{-1}$。又由 $I=Jh+k$，

$$
k(p)=I(p).
$$

Cauchy–Schwarz 因而给出式（3.6）。

<!-- editorial-note: n13 begin -->
<a id="n13"></a>

**编者注 n13（极点处的下界）。** 式（3.6）求值的是全纯分子 $I$ 和投影 $k$，不是在极点求 $\Phi(p)$。$J(p)=0$ 使通常 Szegő 核属于 $K_J$，其范数及再生性质见 Garcia–Ross §2.3、§5.1；互素性给出 $I(p)\ne0$，所以该下界严格为正。它是条件于一个极点存在的下界，没有提供实际数值或极点。空零点情形的 $K_J$ 为零空间。

<!-- editorial-note: n13 end -->

### 递归分解也可以完全写出

将 $J$ 的零点按阶数列为 $p_1,p_2,\ldots$，定义

$$
b_p(w)=\frac{w-p}{1-\bar p w},
\qquad
J_N=\prod_{j=1}^{N}b_{p_j},
$$

以及

$$
e_j(w)=
J_{j-1}(w)
\frac{\sqrt{1-|p_j|^2}}{1-\bar p_jw}.

$$

<a id="eq-3-7"></a>

(3.7)

<!-- editorial-note: n14 begin -->
<a id="n14"></a>

**编者注 n14（无限乘积相位与重复零点）。** 有限 $J_N$ 使用文中的 $b_p$ 没有问题；无限乘积不能一般地直接定义为这批未归一化因子的极限。$J$ 仍指标准带单位模相位的收敛 Blaschke 乘积（Garcia–Ross（2.8））。给各个有限乘积补相位只改变 $e_j$ 的相位，不改变正交性或系数绝对值。重复零点须重复列出；用 $K_{AB}=K_A\oplus AK_B$ 逐次加入每个一次因子，包含重数所需的方向。穷尽零点后，若函数垂直于这些空间，则可被整个纯 Blaschke 乘积整除，因此在 $K_J$ 中只能为零。这是本处完备性的条件；若还剩奇异内因子，该论证不成立。供应见 Garcia–Ross 命题 3.18、5.12 及 §5.4。

<!-- editorial-note: n14 end -->

这些向量构成 $K_J$ 的正交归一基，因而

$$
\boxed{
\varepsilon
=
\sum_j|\langle e_j,I\rangle|^2.
}

$$

<a id="eq-3-8"></a>

(3.8)

关键结构是

$$
K_{AB}=K_A\oplus AK_B.
$$

逐次应用它，就得到式（3.7）；完备性来自对全部 Blaschke 零点的穷尽。相应基通常称为 Takenaka–Malmquist–Walsh 基。[arxiv.org](https://arxiv.org/pdf/1312.5018?utm_source=chatgpt.com)

于是每一步都有正交守恒式

$$
\|f_{j-1}\|^2
=
|c_j|^2+\|f_j\|^2,
$$

最终

$$
\sum_{j=1}^{N}|c_j|^2\uparrow\varepsilon,
\qquad
\|f_N\|^2\longrightarrow1-\varepsilon.

$$

<a id="eq-3-9"></a>

(3.9)

<!-- editorial-note: n15 begin -->
<a id="n15"></a>

**编者注 n15（式（3.9）的残量定义与停止情形）。** 可具体取 $f_0=I$，令 $u_j$ 为（3.7）中不含 $J_{j-1}$ 的归一化核，采用内积对第二变量线性的约定，设 $c_j=\langle u_j,f_{j-1}\rangle$，再取

$$
f_j=\frac{f_{j-1}-c_ju_j}{b_{p_j}}.
$$

分子在 $p_j$ 为零，故除法仍给出 $H^2$ 函数，且等距分解给出所列范数守恒。有限阶段残量为 $J_N f_N$，也即 $I$ 减去前 $N$ 个正交分量。它在 $H^2$ 中趋向 $P_{JH^2}I$，从而得到（3.9）的范数极限；不额外声称 $f_N$ 自身收敛。$J$ 为常数时为空和、$f_0=I$；只有有限 $d$ 个零点时在 $j=d$ 停止，极限解释为停止后的恒定残量范数。若采用对第一变量线性的内积，系数取共轭，所有平方范数公式不变。

<!-- editorial-note: n15 end -->

这给了你的递归思路一个精确实现：**递归逐项读出隐藏误差，全部预算非负且收敛。**

这里被逐步提取的是误差质量。已经提取出的正质量仍然属于总误差，不能在下一次归一化中将它删掉。

---

## 四、核心定理：边界、体和关系矩阵中的缺陷维数精确相等

现在定义两个计数，注意它们的重数规则不同。

令

$$
\kappa
=
\#\{\rho:\Re\rho>\tfrac12\},
$$

按**不同 ζ 零点位置**计数。

令

$$
q
=
\sum_{\substack{\eta:\Re\eta>0\\
\eta\text{ 是 }C\text{ 的极点}}}
\operatorname{ord}_{\eta}(C\text{ 的极点}),
$$

按**实际 Cayley 极点阶数**计数。

允许它们为无穷。

定义实际 Pick 核

$$
\boxed{
\mathcal P_F(z,w)
=
\frac{F(z)+\overline{F(w)}}{z+\bar w}.
}

$$

<a id="eq-4-1"></a>

(4.1)

其负指数 $\nu_-(\mathcal P_F)$ 是全部有限合法节点矩阵中，严格负特征值个数的上确界。

<!-- editorial-note: n16 begin -->
<a id="n16"></a>

**编者注 n16（合法节点与无限计数）。** 半平面 Pick 矩阵的节点是有限个互异的 $\Re z>0$ 正则点；$z+\bar w$ 的实部为正，故分母非零。$\kappa$ 统计不同右半平面 $F$ 极点位置；$q$ 统计约分后 $C$ 的右半平面极点阶数，两者的相等需要本节证明。所有无限维和无限秩在本篇仅记为 $\infty$；负指数是有限节点负特征值数的上确界，不是某一个无限矩阵的谱计数。

<!-- editorial-note: n16 end -->

### 定理 4：缺陷维数恒等式

$$
\boxed{
\kappa
=
\nu_-(\mathcal P_F)
=
q
=
\dim K_J
=
\operatorname{rank}H_g.
}

$$

<a id="eq-4-2"></a>

(4.2)

有限维时秩和维数采用通常定义；无限情形统一记作 $\infty$。

### 证明第一步：每个右半平面离线零点贡献一个负方向

设 $a$ 是 $F$ 的右半平面极点，留数为 $r\ne0$。其镜像极点为 $-\bar a$，留数为 $\bar r$。

这一对贡献

$$
F_a(z)=\frac r{z-a}+\frac{\bar r}{z+\bar a}.
$$

它对应的 Pick 核为

$$
\frac r{(z-a)(\bar w+a)}
+
\frac{\bar r}{(z+\bar a)(\bar w-\bar a)}.
$$

在两个特征函数

$$
u(z)=\frac1{z-a},\qquad
v(z)=\frac1{z+\bar a}
$$

上，系数矩阵是

$$
\begin{pmatrix}
0&r\\
\bar r&0
\end{pmatrix}.
$$

其特征值为 $\pm|r|$，恰有一个负方向。

所有临界线极点的留数则为正，贡献正 Gram 核。因此，若右半平面不同极点只有 $\kappa$ 个，任何有限矩阵最多有 $\kappa$ 个负方向。

<!-- editorial-note: n17 begin -->
<a id="n17"></a>

**编者注 n17（留数配对与上界的正尾项）。** 实际反射及共轭对称使 $a$ 与 $-\bar a$ 的留数为 $r$ 与 $\bar r$；在 $u, v$ 这两个特征函数上的两个交叉项恰为原文所列，Hermitian 系数矩阵的负惯性数为一。临界线位置 $a=i\gamma$ 的留数是 $m/(1/4+\gamma^2)>0$，单项核为正 Gram 核。有限合法节点上的尾项由绝对收敛控制，正尾项的极限仍正。$\kappa$ 有限时，负读出至多有 $\kappa$ 个，故负定子空间向这些读出的映射必须单射，得所列上界；$\kappa=\infty$ 时上界按约定无须有限估计。局部系数矩阵有负方向本身尚不保证有限节点能读出，所以下一步的可见性证明不可省略。

<!-- editorial-note: n17 end -->

### 证明第二步：这些负方向确实全部可见

任取不同右半平面极点

$$
a_1,\ldots,a_m,
$$

相应留数为 $r_1,\ldots,r_m$。令

$$
z_j=a_j-\epsilon r_j,
\qquad \epsilon>0.
$$

当 $\epsilon$ 足够小时，节点仍在右半平面，并且

$$
F(z_j)=-\frac1\epsilon+O(1).
$$

于是

$$
\boxed{
[\mathcal P_F(z_i,z_j)]
=
-\frac2\epsilon
\left[
\frac1{a_i+\bar a_j}
\right]
+O(1).
}

$$

<a id="eq-4-3"></a>

(4.3)

中间的 Cauchy 矩阵严格正定，因为

$$
\frac1{a_i+\bar a_j}
=
\int_0^\infty
e^{-a_it}\overline{e^{-a_jt}}\,dt,
$$

且不同指数函数线性无关。

所以 $\epsilon$ 充分小时，式（4.3）严格负定，具有 $m$ 个负方向。

任意有限个离线极点都可以这样同时读出，因此

$$
\boxed{\nu_-(\mathcal P_F)=\kappa.}

$$

<a id="eq-4-4"></a>

(4.4)

<!-- editorial-note: n18 begin -->
<a id="n18"></a>

**编者注 n18（多极点逼近的余项与严格性）。** 固定有限个不同极点后，可选互不相交的小邻域，解析余项在那里一致有界。沿 $z_j=a_j-\epsilon r_j$ 取共同实数 $\epsilon>0$，各点仍在右半平面且避开极点，所得 $O(1)$ 是这个固定有限矩阵的算子范数余项；分母展开的误差亦为 $O(1)$。Cauchy 矩阵是半直线指数函数的 Gram 矩阵；不同指数的线性无关性使其最小特征值严格为正。因此主项 $-2/\epsilon$ 乘它压过有界余项，给出整个 $m$ 维负定空间。无穷情形只对每个有限 $m$ 分别取邻域与 $\epsilon$，不要求统一裕量。

<!-- editorial-note: n18 end -->

### 证明第三步：Cayley 变换保留负指数

直接计算：

$$
\boxed{
\frac{1-C(z)\overline{C(w)}}{z+\bar w}
=
\frac{2S}{
(S+F(z))(S+\overline{F(w)})
}
\mathcal P_F(z,w).
}

$$

<a id="eq-4-5"></a>

(4.5)

在正则节点上，两个有限矩阵只差一个可逆对角合同，因此负指数相同。转到单位盘同样只增加非零的分离因子，也不改变负指数。

<!-- editorial-note: n19 begin -->
<a id="n19"></a>

**编者注 n19（合同的共同域与节点密度）。** 式（4.5）先在 $F$ 正则且 $S+F\ne0$ 的共同域使用，对角因子可取 $\sqrt{2S}/(S+F(z))$。转盘后，由 $z+\bar w=2(1-u\bar v)/((1-u)(1-\bar v))$，再乘非零的分离因子。排除的点是离散的：任一原来合法的有限矩阵都可由共同域节点逼近，核在这些原合法点连续；严格负特征值对足够小的有限矩阵扰动保持。$F$ 极点处的 $C$ 可去点也这样处理，$C$ 真极点则不属于其合法节点。由此才把共同域的合同等价推广到两边完整的负指数。

<!-- editorial-note: n19 end -->

### 证明第四步：盘内负指数就是 $\dim K_J$

对内函数 $I,J$，模型空间核为

$$
K_I(u,v)=
\frac{1-I(u)\overline{I(v)}}{1-u\bar v}.
$$

由 $\Phi=I/J$，

$$
\boxed{
K_\Phi(u,v)
=
\frac{K_I(u,v)-K_J(u,v)}
{J(u)\overline{J(v)}}.
}

$$

<a id="eq-4-6"></a>

(4.6)

互素性给出

$$
K_I\cap K_J=\{0\}.

$$

<a id="eq-4-7"></a>

(4.7)

具体地，由 Beurling 定理，$\overline{IH^2+JH^2}$ 对应于 $I,J$ 的共同内因子；共同因子为常数，所以该和稠密于 $H^2$，取正交补即得式（4.7）。

令

$$
T=P_{K_I}-P_{K_J}.
$$

对任何非零 $v\in K_J$，

$$
\begin{aligned}
\langle v,Tv\rangle
&=\|P_{K_I}v\|^2-\|v\|^2\\
&=-\|(I-P_{K_I})v\|^2\\
&<0.
\end{aligned}

$$

<a id="eq-4-8"></a>

(4.8)

因此整个 $K_J$ 是严格负空间。

任取其中一个有限维子空间，其单位球面紧，故存在严格负裕量。再用有限个 Szegő 核向量逼近其基，就得到同维数的有限节点负方向。

反过来，任何严格负子空间上的 $P_{K_J}$ 必须单射；否则存在非零 $v$ 满足 $P_{K_J}v=0$，从而

$$
\langle v,Tv\rangle=\|P_{K_I}v\|^2\ge0,
$$

矛盾。

所以

$$
\nu_-(K_\Phi)=\dim K_J.
$$

而 $J$ 是纯 Blaschke 乘积，模型空间维数恰等于其零点总阶数，即实际 Cayley 极点总阶数 $q$。

<!-- editorial-note: n20 begin -->
<a id="n20"></a>

**编者注 n20（模型核与投影差的完整对应）。** Beurling 定理给出 $\overline{IH^2+JH^2}=DH^2$，其中 $D$ 是共同内因子；互素时 $D$ 为常数，故（4.7）成立。投影差 $T$ 的二次型在 $K_J$ 的任意有限维子空间上有严格负裕量。通常 Szegő 核在 $H^2$ 中总稠密，即使只取避开 $J$ 零点的节点也如此（垂直者是于开集消失的解析函数）。用有限核组合逼近一个有限负空间的基，保持其裕量。其 Gram 正是 $K_I-K_J$ 在那些节点上的矩阵；再用（4.6）的可逆对角合同得到 $K_\Phi$。反向，负矩阵的系数空间映入这些核的线性张成必单射，而 $P_{K_J}$ 在任何负空间上亦单射。因此上下界都在同一核、同一形式上成立。纯 Blaschke 的维数按重复零点计，见 Garcia–Ross 命题 3.15—3.18。

<!-- editorial-note: n20 end -->

### 证明第五步：负频 Hankel 算子的秩也是同一维数

对 $h\in H^2$，

$$
\boxed{
H_gh=\bar J\,P_{K_J}(Ih).
}

$$

<a id="eq-4-9"></a>

(4.9)

如果 $u\in K_J$ 垂直于全部 $P_{K_J}(Ih)$，则它垂直于 $IH^2$，所以

$$
u\in K_I\cap K_J=\{0\}.
$$

故 $P_{K_J}(IH^2)$ 在 $K_J$ 中稠密。乘以 $\bar J$ 保持范数，因此

$$
\overline{\operatorname{ran}H_g}
=
\bar J K_J,
$$

得到

$$
\operatorname{rank}H_g=\dim K_J.
$$

所有等式合并，定理成立。证毕。

<!-- editorial-note: n21 begin -->
<a id="n21"></a>

**编者注 n21（Hankel 像的闭包与秩）。** 式（4.9）的投影公式应用于每个 $Ih\in H^2$。原文的正交补论证证明的是像稠密及所列闭包等式；有限维时稠密子空间就是全空间，故通常代数秩等于 $\dim K_J$。无限维时它只保证秩不是任何有限整数；按本篇统一写 $\infty$ 的约定足以得到（4.2）。不由此断言像闭、满射，或将无限代数维数与 Hilbert 基数精确等同。

<!-- editorial-note: n21 end -->

### 与离线四元组的关系

非平凡离线零点按

$$
\{\rho,\bar\rho,1-\rho,1-\bar\rho\}
$$

组成四元组。每个不同四元组在右半平面有两个不同位置。

若这样的四元组数为 $M$，则

$$
\boxed{
\operatorname{rank}H_g
=
\dim K_J
=
q
=
\nu_-(\mathcal P_F)
=
2M.
}

$$

<a id="eq-4-10"></a>

(4.10)

ζ 零点的解析重数进入留数，但不会重复增加一个简单 resolvent 极点的独立负方向。相反，实际 Cayley 极点的阶数必须计入 $q$。这两种计数不能混用。

---

<!-- editorial-note: n22 begin -->
<a id="n22"></a>

**编者注 n22（四元组与重数）。** 实际非平凡零点无实位置（固定实际供应中的 actual_height_gt_ten 已比这里所需更强），离线时四个位置均不同；反射和共轭保持重数。每个四元组恰有两个位置满足 $\Re\rho>\tfrac12$，即 $F$ 的两个不同右半平面极点，所以 $\kappa=2M$。即使原零点有高解析重数，局部 $F$ 仍是一个简单极点；真正 Cayley 极点的高阶则必须计入 $q$。这是（4.10）和后表格的不同计数依据。

<!-- editorial-note: n22 end -->

## 五、继续推进：离线零点必有有限的整数多项式负见证

上一节给出了体内节点上的有限负矩阵。现在把它进一步搬到原点附近的边界 Taylor 数据，得到一个纯有限代数形式。

### 定义 5：折叠谱与一条矩链

令

$$
f(w)=iF(-iw)
=\sum_{n\ge0}\alpha_nw^n.
$$

由于 $f$ 为奇函数，记

$$
c_j=\alpha_{2j+1}.
$$

定义

$$
\kappa_\rho=i\left(\rho-\frac12\right),
\qquad
\lambda_\rho=\kappa_\rho^{-2}
=-\frac1{(\rho-\frac12)^2}.

$$

<a id="eq-5-1"></a>

(5.1)

<!-- editorial-note: n23 begin -->
<a id="n23"></a>

**编者注 n23（Taylor 域与折叠权重的符号）。** 令 $R=\min_\rho|\rho-\tfrac12|>0$，最小值存在于离散零点族；Taylor 展开限于 $|w|<R$。任意更小闭盘上的几何展开由绝对权重和控制，可交换求和。代入 $\kappa_\rho=i a_\rho$，单项 $i b_\rho/(-iw-a_\rho)=b_\rho/(\kappa_\rho-w)$，所以奇次系数的符号正是原文所列。碰撞 $\lambda(a)=\lambda(a')$ 当且仅当 $a'=\pm a$；合并这两个位置且仅计一次解析重数 $m_\rho$，利用 $b_\rho=\lambda/(1+\lambda/4)$，得到（5.3）。分母不为零：$\lambda=-4$ 会给出被排除的端点 $a=\pm\tfrac12$。

<!-- editorial-note: n23 end -->

逐项展开给出

$$
c_j
=
\sum_\rho
b_\rho\kappa_\rho^{-2}
\left(\kappa_\rho^{-2}\right)^j.
$$

将 $\rho$ 与 $1-\rho$ 合并，得到不同折叠谱点集合 $\mathcal T$ 及权重 $\omega_\lambda$，使

$$
\boxed{
c_j=\sum_{\lambda\in\mathcal T}
\omega_\lambda\lambda^j.
}

$$

<a id="eq-5-2"></a>

(5.2)

若对应 ζ 零点的重数为 $m_\rho$，则

$$
\boxed{
\omega_\lambda
=
\frac{2m_\rho\lambda^2}{1+\lambda/4}.
}

$$

<a id="eq-5-3"></a>

(5.3)

这些权重绝对可和，$\mathcal T\cup\{0\}$ 紧，唯一可能的聚点为 $0$。

写

$$
\rho=\frac12+\delta+i\gamma,
$$

则

$$
\boxed{
\lambda_\rho
=
\frac{\gamma^2-\delta^2+2i\delta\gamma}
{(\delta^2+\gamma^2)^2}.
}

$$

<a id="eq-5-4"></a>

(5.4)

非平凡零点没有实轴位置。因此：

$$
\delta=0
\Longrightarrow
\lambda_\rho=\gamma^{-2}>0,\quad \omega_\lambda>0;
$$

$$
\delta\ne0
\Longrightarrow
\lambda_\rho\notin\mathbb R.
$$

一个离线四元组恰好对应一个非实共轭谱点对。

<!-- editorial-note: n24 begin -->
<a id="n24"></a>

**编者注 n24（谱的紧性、共轭和正性）。** 谱点均非零，受 $R^{-2}$ 控制；实际零点局部有限且高度逃向无穷，故它们唯一可能的聚点为 $0$，每个离零的谱截集有限。又有 $\sum|\omega_\lambda|<\infty$，可由合并前的 $\sum|b_\rho||\lambda_\rho|$ 控制。式（5.4）的虚部为 $2\delta\gamma/(\delta^2+\gamma^2)^2$；实际 $\gamma\ne0$，故非实谱恰对应离线零点，临界线谱为正实且权重正。反射折叠后，共轭零点还给出共轭谱和共轭权重；一个离线四元组恰对应一对这样的谱点。

<!-- editorial-note: n24 end -->

定义实多项式上的泛函

$$
\mathcal L(p)
=
\sum_{\lambda\in\mathcal T}
\omega_\lambda p(\lambda).
$$

对

$$
p(t)=\sum_{j=0}^{N}u_jt^j,\qquad u_j\in\mathbb R,
$$

有

$$
\boxed{
\mathcal L(p^2)
=
u^{\mathsf T}J_Nu,
\qquad
J_N=(c_{i+j})_{i,j=0}^{N}.
}

$$

<a id="eq-5-5"></a>

(5.5)

这里必须保留实际表达 $p(\lambda)^2$。在非实谱点上，不能擅自将它替换为 $|p(\lambda)|^2$。

<!-- editorial-note: n25 begin -->
<a id="n25"></a>

**编者注 n25（实二次型的域）。** 有限实多项式在这个紧谱上有界，故 $\mathcal L$ 绝对定义；共轭配对使其对实多项式取实值。有限展开给出（5.5），其中 $u=(u_0,\ldots,u_N)^{\mathsf T}$，$J_N$ 是 $(N+1)$ 阶实对称矩阵。非实谱处采用 $p(\lambda)^2$ 是本二次型的定义，若换成绝对平方会改变符号问题；此处不是正测度积分的先验假设。

<!-- editorial-note: n25 end -->

### 定理 5：任何离线零点都产生有限负见证

若存在非实折叠谱点 $\lambda_0$，则存在有限实多项式 $p$，使

$$
\boxed{\mathcal L(p^2)<0.}

$$

<a id="eq-5-6"></a>

(5.6)

而且可以进一步取 $p\in\mathbb Z[t]$。

### 证明：有限插值消主项，高幂压尾项

取

$$
r=\frac{|\lambda_0|}{4},
\qquad
E=\{\lambda\in\mathcal T:|\lambda|\ge r\}.
$$

$E$ 是有限共轭对称集合，包含 $\lambda_0,\bar\lambda_0$。

定义 Lagrange 基多项式

$$
\ell_0(z)
=
\prod_{\substack{\zeta\in E\\\zeta\ne\lambda_0}}
\frac{z-\zeta}{\lambda_0-\zeta}.
$$

它在 $\lambda_0$ 取一，在 $E$ 的其他点取零。令

$$
\ell_{\bar0}(z)=\overline{\ell_0(\bar z)}.
$$

选单位复数 $u$，使

$$
\omega_{\lambda_0}u^2=-|\omega_{\lambda_0}|.

$$

<a id="eq-5-7"></a>

(5.7)

对整数 $m\ge1$，定义

$$
\boxed{
p_m(z)
=
z^m
\left[
u\lambda_0^{-m}\ell_0(z)
+
\bar u\,\bar\lambda_0^{-m}\ell_{\bar0}(z)
\right].
}

$$

<a id="eq-5-8"></a>

(5.8)

<!-- editorial-note: n26 begin -->
<a id="n26"></a>

**编者注 n26（插值的实性与相位）。** 因为 $r=|\lambda_0|/4>0$ 且非零聚点不存在，$E$ 有限并共轭对称；其节点互异，Lagrange 分母均非零。权重非零，故可选单位 $u$ 满足（5.7）。$\ell_{\bar0}$ 的系数是 $\ell_0$ 的共轭，第二项的系数也是第一项的共轭，所以乘以 $z^m$ 后仍为实系数。目标点的交叉 Lagrange 值为零，正好给出 $u,\bar u$，其他 $E$ 节点为零，不要求目标谱点为模最大的点。

<!-- editorial-note: n26 end -->

它具有实系数，且

$$
p_m(\lambda_0)=u,\qquad
p_m(\bar\lambda_0)=\bar u,
$$

在 $E$ 的其余点全部为零。

令 $L_r$ 是两份 Lagrange 多项式在 $|z|\le r$ 上的共同上界。例如可取

$$
L_r=
\prod_{\substack{\zeta\in E\\\zeta\ne\lambda_0}}
\frac{r+|\zeta|}{|\lambda_0-\zeta|}.
$$

于是

$$
|p_m(z)|\le2L_r4^{-m}
\qquad(|z|\le r).

$$

<a id="eq-5-9"></a>

(5.9)

再记

$$
T_r=\sum_{|\lambda|<r}|\omega_\lambda|<\infty.
$$

目标共轭对的贡献恰为

$$
-2|\omega_{\lambda_0}|,
$$

全部尾项的绝对值至多为

$$
4L_r^2T_r16^{-m}.
$$

因此

$$
\boxed{
\mathcal L(p_m^2)
\le
-2|\omega_{\lambda_0}|
+
4L_r^2T_r16^{-m}.
}

$$

<a id="eq-5-10"></a>

(5.10)

<!-- editorial-note: n27 begin -->
<a id="n27"></a>

**编者注 n27（尾界常数与有限次数）。** 共轭对称使两份 Lagrange 多项式在半径 $r$ 盘上有同一个所列积上界。每份乘入 $z^m\lambda_0^{-m}$ 后至多 $L_r4^{-m}$，两份相加后平方模至多 $4L_r^2 16^{-m}$；乘尾部绝对权重和即得（5.10）。目标共轭对恰为 $-2|\omega_{\lambda_0}|$，而整个泛函为实数，故可用尾部绝对值作上界。$T_r$ 有限且 $\omega_{\lambda_0}\ne0$，于是存在有限整数 $m$ 满足严格阈值，次数至多 $m+|E|-1$。这是存在性和误差控制，未执行谱枚举或算出实际系数。

<!-- editorial-note: n27 end -->

取有限 $m$ 使

$$
4L_r^2T_r16^{-m}<|\omega_{\lambda_0}|,
$$

便得到

$$
\mathcal L(p_m^2)<-|\omega_{\lambda_0}|<0.
$$

而

$$
\deg p_m\le m+|E|-1.
$$

因此严格负方向已经出现在某个有限 $J_N$ 中。

这个构造不要求所选离线零点最近，也不要求它具有最大的实部。

最后，因为二次型 $u^{\mathsf T}J_Nu$ 对有限系数向量连续，严格负值在充分小扰动下保持。用有理系数逼近 $p_m$，再清除分母，就得到

$$
\boxed{
\exists p\in\mathbb Z[t]:
\mathcal L(p^2)<0.
}

$$

<a id="eq-5-11"></a>

(5.11)

证毕。

<!-- editorial-note: n28 begin -->
<a id="n28"></a>

**编者注 n28（整数化与全层量词）。** 固定已得多项式的有限次数后，$u^{\mathsf T}J_Nu$ 是实系数向量的连续函数；严格负裕量保持于某个开邻域。有理向量稠密，故可取同次数的有理系数，再乘正整数公分母 $D$；二次型乘 $D^2$，负号保留，得到（5.11）。不要求先给出可执行的搜索界。式（5.12）在全部 $N\ge0$ 上量化：RH 给出正实谱的正平方和；若任一离线零点存在，前面的有限实、再整数负见证使某一层失败。单独验证有限多层不推出 RH。Suzuki 的矩问题是所引文献背景，不把他的另一条矩列直接当作本篇的 $c_j$。

<!-- editorial-note: n28 end -->

### 一个直接加强：只需要一条折叠矩链

因此

$$
\boxed{
\mathrm{RH}
\iff
J_N\succeq0\quad\forall N.
}

$$

<a id="eq-5-12"></a>

(5.12)

RH 下，全部折叠谱点是正实数、权重为正，所以正性直接成立。

反向则由刚才的有限负见证证明。

对一般矩问题，两条不同的 Hankel 链可能分别承担不同条件；对这里已经固定的实际 ζ 折叠谱，单独这一条全层正性已经足够。Hankel 矩与 RH 的联系在既有文献中已有成熟研究；这里使用的是本轮实际 resolvent 的特定矩列及其有限隔离证明。[arxiv.org](https://arxiv.org/pdf/2206.03682?utm_source=chatgpt.com)

---

## 六、连有限矩阵中的负方向数量也能精确算出

仍令 $M$ 为不同离线四元组的数量。

### 定理 6：折叠矩链的精确负指数

$$
\boxed{
\sup_N n_-(J_N)=M.
}

$$

<a id="eq-6-1"></a>

(6.1)

### 上界证明

对一个非实共轭谱点对，其对实多项式 $p$ 的贡献是

$$
2\Re\bigl[\omega_\lambda p(\lambda)^2\bigr].
$$

写 $\omega_\lambda=|\omega_\lambda|e^{i\phi}$，则

$$
\boxed{
2\Re[\omega_\lambda p(\lambda)^2]
=
2|\omega_\lambda|
\left[
\bigl(\Re(e^{i\phi/2}p(\lambda))\bigr)^2
-
\bigl(\Im(e^{i\phi/2}p(\lambda))\bigr)^2
\right].
}

$$

<a id="eq-6-2"></a>

(6.2)

所以一个非实共轭对只提供一个负平方读出；正实谱点只提供非负平方。

若 $M$ 有限，任何维数大于 $M$ 的多项式子空间，都存在非零多项式使这 $M$ 个负读出同时为零。该多项式上的整个二次型非负，所以负定子空间维数不可能超过 $M$。

<!-- editorial-note: n29 begin -->
<a id="n29"></a>

**编者注 n29（一个共轭对的一条负读出）。** 式（6.2）是复平方的实部展开，两个实线性读出前的系数分别为正、负；改变平方根相位只同时改变符号，不改变其惯性。$M$ 有限时，任何维数大于 $M$ 的实多项式空间向这 $M$ 个负读出的映射有核；核内的非零多项式其剩余正实谱贡献和正读出均非负，故不可能是负定空间。$M=0$ 的结论亦包括在内。$M=\infty$ 时只需要随后对每个有限 $k$ 的下界。

<!-- editorial-note: n29 end -->

### 下界证明

任取 $k$ 个不同非实共轭谱点对。

用同一个有限集合 $E$，同时构造上一节的 $k$ 个隔离多项式。每个多项式只在自己的目标对上取指定相位，在其他有限主项上全部为零。

当高幂次数趋于无穷时，这 $k$ 个多项式的二次型 Gram 趋向

$$
-\operatorname{diag}
\left(
2|\omega_{\lambda_1}|,
\ldots,
2|\omega_{\lambda_k}|
\right).
$$

尾项趋于零。因此某个有限次数已经给出 $k$ 维严格负空间。

$M$ 有限时取 $k=M$；$M$ 无限时可取任意有限 $k$。上下界合并，定理成立。证毕。

<!-- editorial-note: n30 begin -->
<a id="n30"></a>

**编者注 n30（同时隔离与移位权重）。** 对固定的 $k$ 个目标，统一取 $r$ 不大于各目标模的四分之一，取同一个有限 $E$。第 $j$ 份多项式的目标幅度按各自的 $\lambda_j^{-m}$ 归一；尾部混合项由两个几何尾界相乘再乘 $\sum|\omega|$ 控制，故每个 Gram 项趋向所列对角矩阵。有限维中取误差算子范数小于该对角矩阵最小正模，即保留严格负定性，也保证这些多项式线性无关。移位只将权重换成 $\omega_\lambda\lambda$：非零目标仍非零、共轭仍配对、绝对和仍有限，正实点的新权重仍正。因此同一上下界证明成立，不能只因为矩阵名称相似而断言相同指数。

<!-- editorial-note: n30 end -->

对移位矩链

$$
J_N^{(1)}=(c_{i+j+1}),
$$

相同证明给出同一负指数 $M$：只需把权重改为 $\omega_\lambda\lambda$。

而上一轮的完整矩阵

$$
\mathsf H_N=(\alpha_{i+j+1})
$$

按奇偶指标重排后满足

$$
\mathsf H_{2N+1}
\cong
J_N\oplus J_N^{(1)}.
$$

因此

$$
\boxed{
\sup_Nn_-(\mathsf H_N)=2M.
}

$$

<a id="eq-6-3"></a>

(6.3)

<!-- editorial-note: n31 begin -->
<a id="n31"></a>

**编者注 n31（完整矩阵的下标与表格范围）。** 沿用前篇的下标 $\mathsf H_N=(\alpha_{i+j+1})_{i,j=0}^N$，所以 $\mathsf H_{2N+1}$ 有 $2N+2$ 行列。偶数下标块为 $c_{i+j}$，奇数下标块为 $c_{i+j+1}$，交叉块因 $\alpha_{2j}=0$ 而为零，得所列合同。两条主子矩阵链的负惯性数各随 $N$ 不减；有限 $M$ 时最终都达到 $M$，无限时可越过任意有限整数。故求上确界得到 $2M$。表格是此前证明与无限计数约定的合并，未将某个有限 $J_N$ 的负特征值数与无限边界算子秩直接等同。

<!-- editorial-note: n31 end -->

现在各个表示的数量关系完全对齐：

| 实际对象 | 精确缺陷数量 |
|---|---:|
| 折叠矩链 $J_N$ 的负指数上确界 | $M$ |
| 完整 Taylor 矩链 $\mathsf H_N$ 的负指数上确界 | $2M$ |
| 实际 Pick 核 $\mathcal P_F$ 的负指数 | $2M$ |
| Cayley 函数 $C$ 的右半平面极点总阶数 | $2M$ |
| 模型空间 $K_J$ 的维数 | $2M$ |
| 边界负频 Hankel 算子 $H_g$ 的秩 | $2M$ |

这里“负频 Hankel 算子的秩”和“矩链的负特征值个数”是不同量；它们通过上述证明取得明确的对应，不能仅因为都叫 Hankel 就混同。

---

## 七、这对 AURIC 的递归证明意味着什么？

现在可以将你的构想写成以下严格结构：

$$
\boxed{
\text{完整边界酉算子}
\;\longrightarrow\;
\text{两个正交读出}
\;\longrightarrow\;
\text{实际误差空间}
\;\longrightarrow\;
\text{有限矩阵中的负见证}.
}
$$

其中每一项都有明确对象：

$$
M_g,\qquad
(T_g,H_g),\qquad
K_J,\qquad
\mathcal L(p^2).
$$

而且归一化始终保持：

$$
T_g^*T_g+H_g^*H_g=I,
$$

$$
\varepsilon=\|H_g1\|^2\in[0,1].
$$

这说明误差完全可以被归一化、可以被三轴表示、可以递归展开，也可以保持稳定。

但它同时具有一个不能靠换坐标消除的维数：

$$
\operatorname{rank}H_g=2M.
$$

<!-- editorial-note: n32 begin -->
<a id="n32"></a>

**编者注 n32（三轴表述与不变性的范围）。** 前面的投影与范数结论确立的是同一实际边界函数的正交预算；“三轴”沿用前篇的 Cayley 球面坐标解释，并未另证实现、物理性质、native gate 或成本结论。共同酉变换须同时作用于状态和子空间，才有下一式中的 $P_{UK_J}=UP_{K_J}U^{-1}$。有限形式的负惯性在可逆合同下保持；“忠实等距提升”必须指同一形式在其完整像上的拉回且不丢失方向。任意矩形等距压缩可以丢掉负方向；直和正块虽保持负指数，却改变正惯性数，增广后的任意再压缩也无保持保证。不能把这些不同操作统称为完整形式的惯性不变。

<!-- editorial-note: n32 end -->

若对整个关系作共同酉变换，状态与读口一起变换，投影能量保持：

$$
\|P_{UK_J}(UI)\|^2
=
\|UP_{K_J}I\|^2
=
\varepsilon.
$$

有限实际关系矩阵的负惯性指数，同样在可逆合同和忠实等距提升下保持。

因此，递归的正确证明任务现在可以写成两个完全具体的版本：

$$
\boxed{
S+F(z)\ne0
\qquad
(\Re z>0,\ F\text{ 正则}),
}

$$

<a id="eq-7-1"></a>

(7.1)

或

$$
\boxed{
\mathcal L(p^2)\ge0
\qquad
\text{对所有 }p\in\mathbb Z[t].
}

$$

<a id="eq-7-2"></a>

(7.2)

两者都等价于 RH。

<!-- editorial-note: n33 begin -->
<a id="n33"></a>

**编者注 n33（最终等价与组织工具的边界）。** 式（7.1）使用第二节的全右半平面正则域；式（7.2）在所有整数系数多项式上量化。由第五节，任一离线零点都会违反后者；RH 下正谱平方和给出后者。因此它们是 RH 的等价目标，不是已经证明的符号结论。固定提交中 ZeckendorfGreedyPermutation.result 的供应范围是一基贪心序列的正整数置换、无重复及穷尽性；在此只用作有限编码的穷尽组织。重排绝对收敛和、全部有限节点或全部多项式的量词不会改变这些全局量，但排序不供应实际 $\mathcal L$ 的符号，也不供应关于该函数的数值证书。原稿末句的“已经证明”是对本篇条件连接的作者陈述，未消除其明确保留的实际正性缺口。

<!-- editorial-note: n33 end -->

A370630 的已证遍历性，可以用于组织有限整数系数的编码、分类和穷尽顺序；任意穷尽重排都不会改变上面这些全局缺陷量。它尚未提供的是式（7.2）所需的实际符号控制。

**本轮已经证明：离线缺陷若存在，它会在边界与体之间保持可追踪的维数，并且必有有限的整数系数负见证。** 尚未证明的是这些见证全部不存在。要继续向 RH 本身推进，下一步必须从实际 ξ 函数或原素数显式公式中证明式（7.1）或式（7.2），而不能再把“误差有稳定归一化”替代为“误差等于零”。