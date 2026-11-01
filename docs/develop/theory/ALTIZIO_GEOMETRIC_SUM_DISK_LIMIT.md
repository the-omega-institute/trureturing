# Altizio 几何和圆盘上的最小值极限

## 1. 原问题与记号

对正整数 \(n\)，定义字面有限和

$$
G_n(z):=\sum_{k=0}^{n-1}z^k\qquad (z\in\mathbb C),
$$

并令

$$
B:=\{z\in\mathbb C:|z-2|\le 1\},
\qquad
m_n:=\min_{z\in B}\left|\frac{G_n(z)}{z}\right|.
$$

这里 \(G_n(1)=n\) 是上述有限和的字面值，分母和分子取同一个点 \(z\)。Altizio 在 *Zeros of Stern polynomials in the complex plane* 第 2 节把 \((z)_n\) 定义为这一有限和，并在第 3 节取同一闭圆盘 \(B=B_1[2]\)。第 4.3 节第 20 页 Remark 4 提出
\(\min_{z\in B}|(z)_n/z|\to2\pi\) 的问题；该 Remark 是问题来源，不承担下文任何证明步骤。

仓库供给的 \`D5.S3.Zeros.AltizioGeometricSumDisk.result\` 是另一项独立的分类：对每个正整数 \(n\)，闭圆盘上的不等式

$$
\forall z\in B,\qquad n|z|\le |G_n(z)|
$$

成立当且仅当 \(n\in\{5,6,7\}\)。其私有 \`disk_bound\` 的参数恰限于这三个次数；本卷不把它用作任意 \(n\) 的前提，也不从该分类推出极限。

## 2. 闭圆盘上的基本性质

**命题 2.1（最小值存在且为正）。** 对每个正整数 \(n\)，\(m_n\) 存在并且 \(m_n>0\)。

**证明。** 若 \(z\in B\)，三角不等式给出

$$
|z|\ge 2-|z-2|\ge1.
$$

当 \(|z|=1\) 时，\(|z-2|\le1\) 与仓库原始文件 \`D5/S3/Zeros/AltizioGeometricSumDisk.lean\` 的私有 \`unit_intersection\` 具有完全相同的假设，故 \(z=1\)。因而 \(0\notin B\)。同一原始文件的私有 \`G_ne_zero\` 在假设 \(0<n\) 与 \(|z-2|\le1\) 下给出 \(G_n(z)\ne0\)；它使用的也是本卷的字面有限和以及上述单位圆交点。于是

$$
f_n(z):=\left|\frac{G_n(z)}z\right|
$$

在紧集 \(B\) 上连续且处处严格为正。紧集上的连续函数取得最小值，且该最小值严格为正。∎

**命题 2.2（边界化）。** 令

$$
H_n(z):=\frac z{G_n(z)}.
$$

则

$$
m_n=\frac1{\displaystyle\max_{z\in B}|H_n(z)|}
      =\frac1{\displaystyle\max_{z\in\partial B}|H_n(z)|}.
$$

**证明。** 命题 2.1 的非零性使 \(H_n\) 在 \(B\) 上连续且在其内部全纯。标准最大模原理把 \(|H_n|\) 的最大值移到 \(\partial B\)；又 \(f_n=1/|H_n|\)，故正函数的最小值等于其倒数取最大值的倒数。这里没有使用仓库的三次数 \`disk_bound\`，也没有使用 Altizio 对 \(n=5,6\) 的有限次数估计。∎

## 3. 边界参数与两个精确恒等式

边界可写成

$$
z(\theta):=2-e^{i\theta},\qquad -\pi\le\theta\le\pi.
$$

共轭对称性允许只取 \(0\le\theta\le\pi\)。记

$$
d(\theta):=|z(\theta)-1|=2\sin\frac\theta2,
\qquad
r(\theta):=|z(\theta)|.
$$

直接计算得

$$
r(\theta)^2=5-4\cos\theta=1+8\sin^2\frac\theta2=1+2d(\theta)^2. \tag{3.1}
$$

当 \(0\le\theta\le\theta_0\) 且 \(\theta_0>0\) 足够小时，\(z(\theta)\) 位于右半平面，于是存在唯一的 \(\beta(\theta)\in[0,\pi/2)\) 使

$$
z(\theta)=r(\theta)e^{-i\beta(\theta)}.
$$

由

$$
\tan\beta(\theta)=\frac{\sin\theta}{2-\cos\theta}
$$

以及 \(d(\theta)=2\sin(\theta/2)\)，得到

$$
d(\theta)\sim\theta,
\qquad
\beta(\theta)\sim\theta,
\qquad
\frac{\log r(\theta)}{\theta^2}\longrightarrow1
\quad(\theta\downarrow0). \tag{3.2}
$$

这是正弦、正切和对数的标准 Taylor 展开。缩小 \(\theta_0\) 后还可固定为

$$
\frac12d(\theta)\le\beta(\theta)\le\theta
\qquad(0\le\theta\le\theta_0). \tag{3.3}
$$

对 \(\theta>0\)，字面有限和的几何恒等式给出

$$
Q_n(\theta):=|H_n(z(\theta))|
 =\frac{r(\theta)d(\theta)}{|z(\theta)^n-1|}. \tag{3.4}
$$

在 \(\theta=0\) 处，字面定义 \(G_n(1)=n\) 给出

$$
Q_n(0)=\frac1n. \tag{3.6}
$$

由 \(z(\theta)=r(\theta)e^{-i\beta(\theta)}\)，有精确分解

$$
|z(\theta)^n-1|^2
 =\bigl(r(\theta)^n-1\bigr)^2
   +4r(\theta)^n\sin^2\frac{n\beta(\theta)}2. \tag{3.5}
$$

## 4. 边界最大值的上极限

**引理 4.1（远离切点）。** 对任意固定的 \(\theta_0>0\) 足够小，

$$
\sup_{\theta_0\le\theta\le\pi}Q_n(\theta)\longrightarrow0.
$$

**证明。** \(d(\theta)\) 在 \([0,\pi]\) 上递增，所以由 (3.1)，\(r(\theta)\ge r(\theta_0)>1\)。同时 \(r(\theta)\le3\)、\(d(\theta)\le2\)。反三角不等式和 (3.4) 给出

$$
Q_n(\theta)\le\frac{r(\theta)d(\theta)}{r(\theta)^n-1}\le\frac6{r(\theta_0)^n-1},
$$

右端趋于零。∎

**命题 4.2（边界商的上极限）。** 设

$$
M_n:=\max_{z\in\partial B}\left|\frac z{G_n(z)}\right|.
$$

则

$$
\limsup_{n\to\infty}M_n\le\frac1{2\pi}. \tag{4.3}
$$

**证明。** 对 \(n\ge2\)、\(\theta>0\)，令 \(x=n\,d(\theta)\)。由 (3.1) 及指数为 \(n/2\ge1\) 的 Bernoulli 不等式，

$$
r(\theta)^n=(1+2d(\theta)^2)^{n/2}\ge1+n\,d(\theta)^2.
$$

于是

$$
Q_n(\theta)\le\frac{r(\theta)}{x}. \tag{4.1}
$$

当 \(n\ge4\) 时令 \(t=n\theta\)，则 \(z(\theta)=w_{n,t}:=2-e^{it/n}\)。Altizio 第 4.3 节 Proposition 6 在其确切假设 \(n\ge4,\ t\ge0\) 下给出

$$
\left|\frac{G_n(w_{n,t})}{w_{n,t}-1}\right|\ge2n\sin\frac{t}{2n}=n\,d(\theta),
$$

所以它正好供应 (4.1) 的 \(n\ge4\) 部分。Bernoulli 推导则把同一上界延伸到 \(n=2,3\)；没有扩大 Proposition 6 的适用范围。

固定 \(\delta\in(0,2\pi)\)，再取 \(C>2\pi-\delta\)。将 \(0\le\theta\le\theta_0\) 按 \(x=n\,d(\theta)\) 分为

$$
0\le x\le2\pi-\delta,
\qquad
2\pi-\delta\le x\le C,
\qquad
x\ge C.
$$

在第一段，\(x\) 有界即 \(\theta\to0\) 一致，故 \(n\theta=x\,\theta/d(\theta)\) 最终不超过 \(2\pi-\delta/2\)。Altizio 第 4.3 节 Proposition 5 的精确陈述是：对 \(n\ge1,t\ge0\)，同一 \(w_{n,t}\) 满足

$$
\left|\frac{G_n(w_{n,t})}{w_{n,t}-1}\right|\ge n\left(1-\frac{t}{2\pi}\right).
$$

取 \(t=n\theta\) 后，第一段得到 \(Q_n(\theta)=O_\delta(n^{-1})\)；\(\theta=0\) 处用 (3.6)。这一步使用的是 Proposition 5 所覆盖的更强小相位估计，而不是另立一个同范围的已知引理。

第二段由 (4.1) 得
\(Q_n(\theta)\le r(\theta)/(2\pi-\delta)\)；该段中 \(d(\theta)\le C/n\)，故 \(r(\theta)\to1\) 一致，第二段的上极限不超过 \((2\pi-\delta)^{-1}\)。第三段由 (4.1) 得 \(Q_n(\theta)\le r(\theta_0)/C\)。最后，\(\theta\ge\theta_0\) 的部分由引理 4.1 趋于零。因此

$$
\limsup_{n\to\infty}M_n
\le\max\left\{\frac1{2\pi-\delta},\frac{r(\theta_0)}C\right\}.
$$

先令 \(C\to\infty\)，再令 \(\delta\downarrow0\)，得到 (4.3)。∎

## 5. 达到相位 \(2\pi\) 的边界序列

**引理 5.1（相位匹配）。** 存在正整数 \(N\)，使得每个 \(n\ge N\) 都有唯一的 \(\theta_n\in(0,\theta_0)\) 满足

$$
\beta(\theta_n)=\frac{2\pi}{n}.
$$

并且

$$
 n\theta_n\longrightarrow2\pi,
\qquad
 n\,d(\theta_n)\longrightarrow2\pi. \tag{5.1}
$$

**证明。** \(\beta\) 在零点可微，且由 (3.2) 有 \(\beta'(0)=1\)。缩小 \(\theta_0\) 后，\(\beta'\) 在 \([0,\theta_0]\) 上为正，故 \(\beta\) 严格递增。对充分大的 \(n\)，\(2\pi/n<\beta(\theta_0)\)，于是由介值定理存在唯一的 \(\theta_n\)。再由 \(\beta(\theta)/\theta\to1\) 得 \(n\theta_n\to2\pi\)，结合 \(d(\theta)/\theta\to1\) 即得第二个极限。这里使用的只是标准的一元微积分与介值定理。∎

**命题 5.2（边界商的下极限）。** 对上面取的 \(\theta_n\)，令 \(z_n=z(\theta_n)\)。则

$$
\left|\frac {z_n}{G_n(z_n)}\right|\longrightarrow\frac1{2\pi}.
$$

**证明。** 由相位匹配，\(z_n=r_ne^{-2\pi i/n}\)，所以 \(z_n^n=r_n^n\)，其中 \(r_n=r(\theta_n)\)。由 (3.2) 和 (5.1)，

$$
 n^2\log r_n
 = (n\theta_n)^2\frac{\log r(\theta_n)}{\theta_n^2}
 \longrightarrow4\pi^2. \tag{5.2}
$$

特别地 \(n\log r_n\to0\)。因此

$$
 n(r_n^n-1)
 =n\bigl(e^{n\log r_n}-1\bigr)
 =n^2\log r_n\,\frac{e^{n\log r_n}-1}{n\log r_n}
 \longrightarrow4\pi^2. \tag{5.3}
$$

又由 (3.4) 和 (5.1)，

$$
\left|\frac {z_n}{G_n(z_n)}\right|
 =\frac{r_n d(\theta_n)}{r_n^n-1}
 \longrightarrow\frac{2\pi}{4\pi^2}=\frac1{2\pi}.
$$

∎

**推论 5.3。** 有

$$
\liminf_{n\to\infty}M_n\ge\frac1{2\pi}. \tag{5.4}
$$

**证明。** \(M_n\) 是边界上的最大值，而命题 5.2 给出一个边界点 \(z_n\) 使对应商趋于 \(1/(2\pi)\)。∎

## 6. 主定理

**定理 6.1（全正整数的几何和圆盘极限）。** 对每个正整数 \(n\)，\(m_n\) 存在且 \(m_n>0\)，并且

$$
\boxed{\displaystyle\lim_{n\to\infty}m_n=2\pi}.
$$

**证明。** 存在性和正性是命题 2.1。由命题 2.2，\(m_n=1/M_n\)。命题 4.2 给出

$$
\limsup M_n\le\frac1{2\pi},
$$

而推论 5.3 给出

$$
\liminf M_n\ge\frac1{2\pi}.
$$

故 \(M_n\to1/(2\pi)\)。由于所有 \(M_n\) 都严格为正，取倒数得到 \(m_n\to2\pi\)。这个结论沿所有正整数 \(n\) 成立，没有抽取子序列，也没有删去圆盘边界或点 \(z=1\)。它是本卷由边界上、下两端推理合成的完整极限；Altizio 的 Remark 4、Proposition 5、Proposition 6、有限次数 Proposition 8 以及仓库的 \(n=5,6,7\) 分类各自只提供其在本卷相应证明处标明的中间事实或问题来源。∎

## 7. 结论范围与来源对应

本卷证明的是 Altizio Remark 4 所提出的完整极限以及最小值存在性。它没有推出 Altizio Remark 3 的统一不等式 \(|G_n(z)|\ge\min(n,2\pi)\)，没有改变仓库中已供给的 \(n=5,6,7\) 分类，也没有涉及 Stern 多项式零点的半平面问题、收敛速率、单调性或极小点分类。

实际中间事实的来源与适用范围如下。

- **Altizio 原文（literature-attested）。** 第 2 节提供 \((z)_n=1+z+\cdots+z^{n-1}\) 的字面约定及 \(z=1\) 时的值 \(n\)；第 3 节提供 \(B=\{|z-2|\le1\}\)；第 4.3 节 Proposition 5 提供 \(n\ge1,t\ge0\) 的小相位估计，经过 \(t=n\theta\) 用于命题 4.2 的第一段；同节 Proposition 6 提供确切范围 \(n\ge4,t\ge0\) 的径向估计，经过 \(t=n\theta\) 用于 (4.1) 的 \(n\ge4\) 部分；同节 Proposition 8 的 \(n=5,6\) 估计属于有限次数材料，本卷不把它扩展为全 \(n\) 供应；Remark 4 只提供原问题。
- **仓库已有内容（repository supply）。** \`D5/S3/Zeros/AltizioGeometricSumDisk.lean\` 的私有 \`unit_intersection\` 只用于命题 2.1 中的单位圆交点，私有 \`G_ne_zero\` 只用于同一命题的全正整数非零性；这些事实在本卷作为证明内的中间步骤使用，未另列为重命名的定理。该文件的私有证明也调用标准有限和恒等式 \`geom_sum_mul\`，本卷只把同一恒等式作为直接的字面代数步骤。该文件及其 Blueprint Scribe、\`Library/Zeros/altizio2025stern.md\` 所承载的 \`n=5,6,7\` 分类是独立供给；其私有 \`disk_bound\` 仅有这三个次数的参数，本卷不调用它来证明极限。
- **标准数学原则（standard principles）。** 各证明直接使用三角不等式与反三角不等式、复数有限几何和恒等式、紧集上的连续极值定理、最大模原理、Bernoulli 不等式、正弦商的连续正性、正弦/正切/对数的 Taylor 展开、单调性和介值定理；它们只承担所标出的局部推理，不被包装成新的理论条目。

除这些已标明来源的中间步骤外，命题 2.1 的全正整数最小值结论、命题 2.2 的本题边界化、命题 4.2 的三段式上极限、引理 5.1 的全正整数相位匹配、命题 5.2 的下极限、推论 5.3 以及定理 6.1 的合成，构成本卷在保持原问题全部量词和整个闭圆盘条件下的本卷推理（repo-derived）。这里没有对全球文献优先权或当前开放状态作穷尽性断言。

## 追加锚（本行以下为增补区）
