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

这里 \(G_n(1)=n\) 是上述有限和的字面值，分母和分子取同一个点 \(z\)。Altizio 在 *Zeros of Stern polynomials in the complex plane* 第 2 节把 \((z)_n\) 定义为这一个有限和，并在第 3 节取同一闭圆盘 \(B=B_1[2]\)。第 4.3 节第 20 页 Remark 4 提出
\(\min_{z\in B}|(z)_n/z|\to2\pi\) 的问题；该 Remark 是问题来源，不是下文证明的来源。

仓库供给的 D5.S3.Zeros.AltizioGeometricSumDisk.result 是另一项独立的分类：对每个正整数 \(n\)，闭圆盘上的不等式
\[
\forall z\in B,\qquad n|z|\le |G_n(z)|
\]
成立当且仅当 \(n\in\{5,6,7\}\)。其证明中的私有 disk_bound 只在 \(n=5,6,7\) 的参数范围内成立；本卷不把它当作任意 \(n\) 的事实，也不从该分类推出极限。

## 2. 闭圆盘上的基本性质

**引理 2.1（圆盘几何）。** 对 \(z\in B\)，有 \(|z|\ge 1\)；若 \(|z|=1\)，则 \(z=1\)。因而 \(0\notin B\)。

**证明。** 三角不等式给出

$$
|z|\ge 2-|z-2|\ge1.
$$

若 \(|z|=1\)，则

$$
|z-2|^2=|z|^2-4\operatorname{Re}z+4=5-4\operatorname{Re}z\le1,
$$

所以 \(\operatorname{Re}z\ge1\)。这里的等号情形也可精确地调用仓库原始文件
D5/S3/Zeros/AltizioGeometricSumDisk.lean 中私有 unit_intersection：其假设正是
\(|z-2|\le1\) 与 \(|z|=1\)，结论正是 \(z=1\)。这只是本引理证明中的已供应中间事实，并未在本卷另列为定理。反之 \(1\in B\)。∎

**命题 2.2（最小值存在且为正）。** 对每个正整数 \(n\)，\(m_n\) 存在并且 \(m_n>0\)。

**证明。** \(B\) 是复平面中的紧集。对本节字面定义的 \(G_n\)，仓库原始文件
D5/S3/Zeros/AltizioGeometricSumDisk.lean 中私有 G_ne_zero 已给出完全相同的供应事实：若 \(0<n\) 且 \(|z-2|\le1\)，则 \(G_n(z)\ne0\)。它的有限和约定与本卷逐项相同；其证明使用有限几何和恒等式以及引理 2.1 所述的单位圆交点。这里把该事实作为本命题证明的中间步骤使用，不把它另列为新的引理。

由引理 2.1 和该供应事实，
\[
f_n(z):=\left|\frac{G_n(z)}z\right|
\]
在 \(B\) 上连续且处处严格为正。紧集上的连续函数取得最小值，且该最小值严格为正。∎

**命题 2.3（边界化）。** 令

$$
H_n(z):=\frac z{G_n(z)}.
$$

则

$$
m_n=\frac1{\displaystyle\max_{z\in B}|H_n(z)|}
      =\frac1{\displaystyle\max_{z\in\partial B}|H_n(z)|}.
$$

**证明。** 命题 2.2 给出 \(H_n\) 在 \(B\) 上连续且在 \(B\) 内全纯。由标准最大模原理（也可先取包含 \(B\) 的无零开邻域）其最大模在 \(\partial B\) 上取得。因为 \(f_n=1/|H_n|\)，正函数取最小值等于其倒数取最大值的倒数。Altizio 第 4.3 节 Proposition 8 在 \(n=5,6\) 的边界估计中使用同一最大模原理，仓库供应的 disk_bound 也只在 \(n=5,6,7\) 的分类范围内使用它；本命题的全正整数范围来自前面的全 \(n\) 非零性。∎

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

当 \(0\le\theta\le\theta_0\) 且 \(\theta_0>0\) 足够小时，\(z(\theta)\) 位于右半平面。于是存在唯一的 \(\beta(\theta)\in[0,\pi/2)\) 使

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

这是正弦、正切和对数的标准 Taylor 展开；缩小 \(\theta_0\) 后还可固定为

$$
\frac12d(\theta)\le\beta(\theta)\le\theta
\qquad(0\le\theta\le\theta_0). \tag{3.3}
$$

对 \(\theta>0\)，有限几何和恒等式给出

$$
Q_n(\theta):=|H_n(z(\theta))|
 =\frac{r(\theta)d(\theta)}{|z(\theta)^n-1|}. \tag{3.4}
$$

在 \(\theta=0\) 处，字面定义 \(G_n(1)=n\) 给出

$$
Q_n(0)=\frac1n. \tag{3.6}
$$

同一有限几何和恒等式在仓库供应的 G_ne_zero 与 boundary_defect 的原始证明中也被使用；此处只使用它的字面代数等式。由 \(z(\theta)=r(\theta)e^{-i\beta(\theta)}\)，有精确分解

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
Q_n(\theta)
\le\frac{r(\theta)d(\theta)}{r(\theta)^n-1}
\le\frac6{r(\theta_0)^n-1},
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

**证明。** 先记录本证明中唯一与 Altizio 已有命题重叠的估计。对 \(n\ge2\)、\(\theta>0\)，令 \(x=n\,d(\theta)\)。由 (3.1) 及指数为 \(n/2\ge1\) 的 Bernoulli 不等式，

$$
 r(\theta)^n=(1+2d(\theta)^2)^{n/2}\ge1+n\,d(\theta)^2.
$$

于是

$$
 Q_n(\theta)\le\frac{r(\theta)}{x}. \tag{4.1}
$$

当 \(n\ge4\) 时令 \(t=n\theta\)，并写 Altizio 第 4.3 节 Proposition 6 的
\(w_{n,t}=\overline{2-e^{it/n}}\)。则 \(z(\theta)=\overline{w_{n,t}}\)，共轭保持所有范数，且 Proposition 6 的假设正是 \(n\ge4,t\ge0\)；其结论在这个替换下恰为 (4.1)。因此 \(n\ge4\) 的部分逐参数、逐次数地归属于该 Proposition 6。上面的 Bernoulli 推导把同一估计延伸到 \(n=2,3\)，这是本卷新增的范围；没有把 Altizio 的命题扩写成任意 \(n\) 的供应。

取任意 \(\delta\in(0,2\pi)\)，再取任意 \(C>2\pi-\delta\)。将 \(0\le\theta\le\theta_0\) 按 \(x=n\,d(\theta)\) 分为三段：

$$
0\le x\le2\pi-\delta,
\qquad
2\pi-\delta\le x\le C,
\qquad
x\ge C.
$$

第一段由下一个引理的上界趋于零。第二段由 (4.1) 得
\(Q_n(\theta)\le r(\theta)/(2\pi-\delta)\)；该段中 \(d(\theta)\le C/n\)，故 \(r(\theta)\to1\) 一致，第二段的上极限不超过 \((2\pi-\delta)^{-1}\)。第三段由 (4.1) 得 \(Q_n(\theta)\le r(\theta_0)/C\)。最后，\(\theta\ge\theta_0\) 的部分由引理 4.1 趋于零。因此

$$
\limsup_{n\to\infty}M_n
\le\max\left\{\frac1{2\pi-\delta},\frac{r(\theta_0)}C\right\}.
$$

先令 \(C\to\infty\)，再令 \(\delta\downarrow0\)，得到 (4.3)。∎

**引理 4.3（相位区间）。** 固定 \(0<\delta<2\pi\)。当 \(n\to\infty\) 时，满足 \(0\le n\,d(\theta)\le2\pi-\delta\) 且 \(0\le\theta\le\theta_0\) 的点一致满足

$$
Q_n(\theta)\longrightarrow0. \tag{4.2}
$$

**证明。** 若 \(n\,d(\theta)\) 有界，则 \(\theta\to0\)，并由 (3.2) 一致得到 \(\beta(\theta)/d(\theta)\to1\)。故当 \(n\) 足够大时，

$$
0\le \frac{n\beta(\theta)}2\le\pi-\frac\delta4.
$$

函数 \(u\mapsto\sin u/u\) 在 \([0,\pi-\delta/4]\) 上有正的最小值 \(c_\delta\)（在 \(u=0\) 取连续值 \(1\)），从而

$$
\sin\frac{n\beta(\theta)}2
\ge c_\delta\frac{n\beta(\theta)}2.
$$

由 (3.5)、\(r\ge1\) 和 (3.3)，

$$
Q_n(\theta)
\le\frac{d(\theta)}{2\sin(n\beta(\theta)/2)}
\le\frac{d(\theta)}{c_\delta n\beta(\theta)}
\le\frac2{c_\delta n}.
$$

在 \(\theta=0\) 处使用 (3.6)。这证明了一致收敛。∎

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

**证明。** \(\beta\) 在零点可微，且由 (3.2) 有 \(\beta'(0)=1\)。缩小 \(\theta_0\) 后，\(\beta'\) 在 \([0,\theta_0]\) 上为正，故 \(\beta\) 严格递增。对充分大的 \(n\)，\(2\pi/n<\beta(\theta_0)\)，于是由介值定理存在唯一的 \(\theta_n\)。再由 \(\beta(\theta)/\theta\to1\) 得 \(n\theta_n\to2\pi\)，结合 \(d(\theta)/\theta\to1\) 即得第二个极限。这里使用的只是标准的一元微积分与介值定理。

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

**证明。** 存在性和正性是命题 2.2。由命题 2.3，\(m_n=1/M_n\)。命题 4.2 给出

$$
\limsup M_n\le\frac1{2\pi},
$$

而推论 5.3 给出

$$
\liminf M_n\ge\frac1{2\pi}.
$$

故 \(M_n\to1/(2\pi)\)。由于所有 \(M_n\) 都严格为正，取倒数得到 \(m_n\to2\pi\)。这个结论沿所有正整数 \(n\) 成立，没有抽取子序列，也没有删去圆盘边界或点 \(z=1\)。这一步是本卷的实质性全极限推论；它不由 Altizio 的 Remark 4、Proposition 6、Proposition 8 或仓库的 \(n=5,6,7\) 分类单独给出。

## 7. 结论范围与来源对应

本卷证明的是 Altizio Remark 4 所提出的完整极限以及最小值存在性。它没有推出 Altizio Remark 3 的统一不等式 \(|G_n(z)|\ge\min(n,2\pi)\)，没有改变仓库中已供给的 \(n=5,6,7\) 分类，也没有涉及 Stern 多项式零点的半平面问题、收敛速率、单调性或极小点分类。

逐项来源边界如下。

- **Altizio 原文。** 第 2 节提供 \((z)_n=1+z+\cdots+z^{n-1}\) 的字面约定及 \(z=1\) 时的值 \(n\)；第 3 节提供 \(B=\{|z-2|\le1\}\)；第 4.3 节 Proposition 6 提供在确切范围 \(n\ge4,\ t\ge0\) 内的径向估计，经过 \(t=n\theta\) 和共轭替换后用于 (4.1)；第 4.3 节 Proposition 8 的 \(n=5,6\) 估计与本卷的边界化原则相邻，但不承担本卷的全 \(n\) 极限；Remark 4 只提供原问题。
- **仓库已有内容。** D5/S3/Zeros/AltizioGeometricSumDisk.lean 的私有 unit_intersection 提供引理 2.1 所用的精确单位圆交点，私有 G_ne_zero 提供命题 2.2 所用的所有正整数、整个闭圆盘上的非零性；同一文件的公开 result、其 Blueprint Scribe 与 Library/Zeros/altizio2025stern.md 共同承载 \(n=5,6,7\) 的分类。私有 disk_bound 的参数仅为这三个次数，本卷从未把它提升为任意 \(n\) 的前提。
- **标准数学原则。** 本卷另用三角不等式与反三角不等式、紧集上的极值定理、最大模原理、Bernoulli 不等式、正弦商的连续正性、Taylor 展开、单调性与介值定理；这些在各自证明处按其实际作用使用，不被包装成新的理论条目。

除上述已明确标出的中间步骤外，边界参数的统一上界、相位 \(2\pi\) 的全正整数匹配序列、下界以及由上下极限合成的完整极限，是本卷在保持原问题全部量词和整个闭圆盘条件下补足的数学内容。这里没有对全球文献优先权或当前开放状态作穷尽性断言。

## 追加锚（本行以下为增补区）
