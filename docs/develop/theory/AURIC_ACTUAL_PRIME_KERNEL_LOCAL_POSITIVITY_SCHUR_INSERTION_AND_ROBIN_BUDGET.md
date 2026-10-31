# AURIC 实际素数核、局部正性、Schur 插入与 Robin 预算（编者拟题）

> **编者说明。** 本标题为描述性拟题；作者原文未提供标题、版本或日期。下方“作者正文”完整保留所供来源的开场、十个有序部分、全部定义、定理、证明、推导、表格、强调、列表、链接、公式内容与结尾。为适配本卷的便携 Markdown 渲染，仅把作者的行内与成对展示数学外层定界符改写为本渲染器支持的美元定界符；公式内部字符不改写。分节与公式锚点以及文末编者条件注均为单独的编辑结构，不替代作者正文。

导航：[开场](#opening) · [一](#section-1) · [二](#section-2) · [三](#section-3) · [四](#section-4) · [五](#section-5) · [六](#section-6) · [七](#section-7) · [八](#section-8) · [九](#section-9) · [十](#section-10)。

<style>
#auric-prime-kernel-paper .katex-display > .katex { width: max-content; min-width: 100%; }
#auric-prime-kernel-paper .katex-display > .katex > .katex-html > .katex-tag { position: static; display: inline-block; margin-left: 1em; }
</style>

<div id="auric-prime-kernel-paper">

<!-- author-begin -->
<a id="opening"></a>

继续。这一轮可以补上一个实质性的递归步骤：

> **对于由实际素数公式定义的核，存在一个固定的短对数区间，使区间内任意多个互异节点的关系矩阵都严格正定；每次插入新节点，还能给出明确的正余量和误差容忍界。**

这就把你提出的“结果—剩余—总量守恒，再递归用 AURIC 表示”，在一个明确范围内变成了可证明的结构。同时，我们还能给原整数的 Robin 分解增加一条无条件正下界。

下面依次给出定义、定理与证明。**本轮完成的是局部递归与正预算估计；跨越所有尺度的实际算术正性仍有一个明确缺口，尚未完成黎曼猜想的证明。**

<a id="section-1"></a>
## 一、固定真实算术对象

项目已经有两项与这里直接相关的基础：

- [有限零点 Gram 层级](https://github.com/the-omega-institute/trureturing/blob/1a5020ef545f364fd70cf83f8829c38302284b1b/Blueprint/D5/S3/Weil/FiniteZeroGramHierarchy.md)：给定非负权重的实际 Gram 分解，可以推出矩阵正性；该文件也明确保留了无限收敛和实际零点定位所需的额外条件。
- [AURIC 三轴误差几何与酉相容](https://github.com/the-omega-institute/trureturing/blob/08e8767227de53351c42cb35028e01de5e88287d/docs/develop/theory/AURIC_THREE_AXIS_ERROR_GEOMETRY_UNITARY_COMPATIBILITY_AND_ENDOGENOUS_STABILITY_V35.md)：二元正关系归一后可以用三轴表达，同时必须保存尺度、符号及后续关系所需的信息。

下面的新增结论是纸面推导，不把它们表述为已经完成的项目形式化定理。

### 定义 1：实际素数核

所有对数均为自然对数。令 $\gamma$ 为欧拉常数，对 $x\ge1$ 定义

<a id="eq-1"></a>

$$
\begin{aligned}
\mathcal F(x)
={}&x(1+\gamma-\log x)-\log(2\pi)\\
&+\sum_{k=1}^{\infty}
\frac{x^{-2k}}{2k(2k+1)}\\
&+\sum_{p^j\le x}
\log p\left(\frac{x}{p^j}-1\right),
\end{aligned}
\tag{1}
$$

其中 $p$ 遍历实际素数，$j\ge1$。再令

<a id="eq-2"></a>

$$
\boxed{
\mathscr K(t)=e^{-|t|/2}\mathcal F(e^{|t|}).
}
\tag{2}
$$

这是上一轮使用的真实核：素数幂项、常数项和无穷尾项均完整保留。素数幂端点 $x=p^j$ 的对应新增项为零，因此 $\mathcal F$ 连续。

其对角总量为

<a id="eq-3"></a>

$$
\boxed{
S=\mathscr K(0)=2+\gamma-\log(4\pi)>0.
}
\tag{3}
$$

由标准素数显式公式积分，得到此前使用的真实零点展开

<a id="eq-4"></a>

$$
\mathscr K(t)
=
\sum_{\rho}
\frac{e^{(\rho-\frac12)t}}{\rho(1-\rho)},
\tag{4}
$$

其中 $\rho$ 遍历实际非平凡零点并计重数。这里引用的经典输入是素数显式公式与零点计数估计；式 (1)—(4) 的联系是对这些公式的积分推导。[kskedlaya.org](https://kskedlaya.org/ant/chapter-8.html?utm_source=chatgpt.com)

特别地，$S>0$ 不需要假设 RH。写 $\rho=\beta+i\tau$，则

$$
\Re\frac1{\rho(1-\rho)}
=
\frac{\beta(1-\beta)+\tau^2}
{\bigl(\beta(1-\beta)+\tau^2\bigr)^2
+\tau^2(1-2\beta)^2}
>0.
$$

共轭零点配对后，每一对的贡献都为正。

---

<a id="section-2"></a>
## 二、引理：真实核在原点具有一个能产生正余量的尖点

### 引理 1

当 $t\downarrow0$ 时，

<a id="eq-5"></a>

$$
\boxed{
\begin{aligned}
\mathscr K'(t)&=\frac12\log t+O(1),\\
\mathscr K''(t)&=\frac1{2t}+O(1),\\
\mathscr K(t)
&=
S+\frac12t\log t
+\frac{\gamma-1+\log(2\pi)}2\,t
+O(t^2|\log t|).
\end{aligned}
}
\tag{5}
$$

因此存在一个固定的

$$
0<\delta<\log2
$$

使得

<a id="eq-6"></a>

$$
\boxed{
\mathscr K(t)>0,\qquad
\mathscr K'(t)<0,\qquad
\mathscr K''(t)>0
\quad(0<t\le\delta).
}
\tag{6}
$$

### 证明

当 $0<t<\log2$ 时，式 (1) 中的素数幂和为空。因此

$$
\mathscr K(t)=N(t)+P(t),
$$

其中

$$
N(t)=(1+\gamma-t)e^{t/2}
-\log(2\pi)e^{-t/2},
$$

$$
P(t)=
\sum_{k\ge1}c_k e^{-\lambda_k t},
\qquad
c_k=\frac1{2k(2k+1)},
\quad
\lambda_k=2k+\frac12.
$$

关键是两个精确系数恒等式：

$$
c_k\lambda_k
=
\frac1{2k}-\frac1{4k(2k+1)},
$$

$$
c_k\lambda_k^2
=
1+\frac1{8k(2k+1)}.
$$

所以

$$
P'(t)
=
\frac{e^{-t/2}}2\log(1-e^{-2t})
+
\frac{e^{-t/2}}4
\sum_{k\ge1}\frac{e^{-2kt}}{k(2k+1)},
$$

以及

$$
P''(t)
=
e^{-t/2}
\left[
\frac1{e^{2t}-1}
+
\sum_{k\ge1}
\frac{e^{-2kt}}{8k(2k+1)}
\right].
$$

后一式的第二项有界，而

$$
\frac1{e^{2t}-1}=\frac1{2t}+O(1).
$$

加上在原点附近光滑的 $N$，便得到前两条渐近式；继续积分得到第三条。

最后，由 $S>0$、$\mathscr K'(t)\to-\infty$ 和 $t\mathscr K''(t)\to\frac12$，可选取满足式 (6) 的 $\delta$。证毕。

**这里已经出现递归正性的来源：新节点靠近旧节点时，核值的下降量具有 $t\log(1/t)$ 的正主项。**

---

<a id="section-3"></a>
## 三、定理：任意阶的真实局部关系矩阵都严格正定

### 定理 1：短窗口内的全有限阶正定性

存在上述固定的 $\delta>0$，使得对任意 $m\ge1$ 和任意互异实数节点

$$
t_1,\ldots,t_m,
\qquad
\max_i t_i-\min_i t_i\le\delta,
$$

实际矩阵

<a id="eq-7"></a>

$$
\boxed{
H=\bigl[\mathscr K(t_i-t_j)\bigr]_{i,j=1}^{m}
}
\tag{7}
$$

都严格正定。

这里对节点数 $m$ 没有上界。

### 证明：把局部核写成正三角核的混合

定义

$$
r=-\mathscr K'(\delta)>0,
\qquad
L=\delta+\frac{\mathscr K(\delta)}r>\delta.
$$

再定义一个辅助核

<a id="eq-8"></a>

$$
\boxed{
\widetilde{\mathscr K}(t)
=
\int_0^\delta
(s-|t|)_+\mathscr K''(s)\,ds
+
r(L-|t|)_+.
}
\tag{8}
$$

其中 $u_+=\max(u,0)$。

先证明它在所需窗口内就是实际核。对 $0<t\le\delta$，分部积分给出

$$
\begin{aligned}
\int_t^\delta(s-t)\mathscr K''(s)\,ds
={}&
(\delta-t)\mathscr K'(\delta)\\
&-\mathscr K(\delta)+\mathscr K(t).
\end{aligned}
$$

利用

$$
\mathscr K'(\delta)=-r,
\qquad
r(L-\delta)=\mathscr K(\delta),
$$

得到

<a id="eq-9"></a>

$$
\boxed{
\widetilde{\mathscr K}(t)=\mathscr K(t)
\quad(|t|\le\delta).
}
\tag{9}
$$

在 $t=0$ 处，积分也收敛，因为

$$
s\mathscr K''(s)\longrightarrow\frac12,
\qquad
s\mathscr K'(s)\longrightarrow0.
$$

接下来，对每个 $s>0$，三角核具有精确表示

<a id="eq-10"></a>

$$
\boxed{
(s-|u-v|)_+
=
\int_{\mathbb R}
\mathbf1_{[u,u+s]}(x)
\mathbf1_{[v,v+s]}(x)\,dx.
}
\tag{10}
$$

所以它是一个 Gram 核，其任意有限关系矩阵均正半定。

而 $L$ 对应的三角核在互异节点上严格正定：如果

$$
\sum_{i=1}^{m}c_i\mathbf1_{[t_i,t_i+L]}=0
\quad\text{几乎处处},
$$

将节点从小到大排列，最左侧只有第一个区间出现的非空部分迫使 $c_1=0$；依次重复，得到全部 $c_i=0$。

因此，若

$$
H_L=\bigl[(L-|t_i-t_j|)_+\bigr],
$$

式 (8) 给出

<a id="eq-11"></a>

$$
\boxed{
H\succeq rH_L\succ0.
}
\tag{11}
$$

证毕。

这类“局部正性可以无条件成立，而全局正性承载 RH 信息”的现象有经典研究背景，例如 Suzuki 对相关 screw 核的局部正定性定理。上面给出的是针对当前 $\mathscr K$ 的直接证明。[arxiv.org](https://arxiv.org/pdf/2206.03682?utm_source=chatgpt.com)

---

<a id="section-4"></a>
## 四、真正的递归步骤：新增关系有多少正余量？

仅仅知道整个矩阵正定还不够。为了递归，我们需要知道加入新点时剩下多少空间。

### 定义 2：实际 Schur 余量

设旧节点的实际矩阵为 $H\succ0$，新节点为 $x$。定义真实新旧关系列

$$
\mathbf b=
\bigl(\mathscr K(t_1-x),\ldots,
\mathscr K(t_m-x)\bigr)^{\mathsf T}.
$$

新增矩阵为

$$
H_+
=
\begin{pmatrix}
H&\mathbf b\\
\mathbf b^*&S
\end{pmatrix}.
$$

其 Schur 余量为

<a id="eq-12"></a>

$$
\boxed{
\mathcal E(x\mid t_1,\ldots,t_m)
=
S-\mathbf b^*H^{-1}\mathbf b.
}
\tag{12}
$$

它的意义是：新向量的总平方范数为 $S$，已有空间能够解释的部分为 $\mathbf b^*H^{-1}\mathbf b$，剩余部分为 $\mathcal E$。

### 定理 2：内部插点的显式正余量

假设所有新旧节点仍落在同一个长度不超过 $\delta$ 的窗口内。若 $a<b$ 是两个相邻旧节点，且

$$
a<x<b,
$$

则

<a id="eq-13"></a>

$$
\boxed{
\mathcal E(x\mid\mathrm{old})
\ge
2r\,\frac{(x-a)(b-x)}{b-a}>0.
}
\tag{13}
$$

特别地，在一个长度为 $d$ 的间隙中插入中点时，

<a id="eq-14"></a>

$$
\boxed{
\mathcal E\ge\frac{rd}{2}.
}
\tag{14}
$$

### 证明

Schur 余量具有最小值表示：

$$
\mathcal E
=
\min_{\alpha}
\begin{pmatrix}-\alpha\\1\end{pmatrix}^{\!*}
H_+
\begin{pmatrix}-\alpha\\1\end{pmatrix}.
$$

由式 (11)，

$$
\mathcal E\ge r\,\mathcal E_L,
$$

其中 $\mathcal E_L$ 是三角核 $L-|u-v|$ 的相应余量。

令

$$
\ell=x-a,\qquad h=b-x.
$$

因为 $(a,b)$ 内没有旧节点，三角核对 $x$ 在该区间上是仿射的。因此新点对所有旧节点的关系都满足

$$
H_L(x,y)
=
\frac{h}{\ell+h}H_L(a,y)
+
\frac{\ell}{\ell+h}H_L(b,y).
$$

这说明只使用两个相邻端点的线性插值，就已经给出了三角核中的正交投影。其剩余平方范数为

$$
\begin{aligned}
\mathcal E_L
&=
L-\frac{h}{\ell+h}(L-\ell)
-\frac{\ell}{\ell+h}(L-h)\\
&=\frac{2\ell h}{\ell+h}.
\end{aligned}
$$

代回即得式 (13)。证毕。

**于是，“继续细分、继续加入关系”在这个窗口内可以进行任意多个有限步骤，并且每一步都有实际核提供的正预算。**

---

<a id="section-5"></a>
## 五、把这一步精确放回 AURIC 三轴

现在可以落实你提出的“结果、剩余、总量守恒”。

选定一个旧节点 $t_j$，定义

$$
a_0=\frac{\mathscr K(x-t_j)}S,
\qquad
p=\frac{\mathbf b^*H^{-1}\mathbf b}{S}.
$$

令

<a id="eq-15"></a>

$$
\boxed{
X=a_0^2,\qquad
Y=p-a_0^2,\qquad
Z=1-p=\frac{\mathcal E}{S}.
}
\tag{15}
$$

### 定理 3：真实关系的三轴守恒分解

在上述局部递归条件下，

<a id="eq-16"></a>

$$
\boxed{
X\ge0,\qquad Y\ge0,\qquad Z>0,
\qquad X+Y+Z=1.
}
\tag{16}
$$

三个读出对应以下正交分解：

| 读出 | 对应的正交部分 | 数学含义 |
|---|---|---|
| $X$ | 选定旧向量的方向 | 与当前锚点直接对应的部分 |
| $Y$ | 旧空间内与该锚点正交的部分 | 其余已有关系共同解释的部分 |
| $Z$ | 整个旧空间的正交补 | 本次新增的独立剩余 |

### 证明

取实际 Gram 向量 $v_1,\ldots,v_m,v_x$，使

$$
\langle v_i,v_k\rangle=\mathscr K(t_i-t_k),
\qquad
\|v_i\|^2=\|v_x\|^2=S.
$$

将 $v_x/\sqrt S$ 投影到上表的三个正交子空间。三部分的平方范数分别就是式 (15) 中的 $X,Y,Z$。

因此非负性来自实际正交投影，和为一来自总范数归一化；$Z>0$ 则由定理 2 保证。证毕。

### 与项目原五模式读口的明确对应

项目使用五模式次序

$$
(N,2,3,5,25).
$$

在这个次序下，取归一状态

<a id="eq-17"></a>

$$
\boxed{
|\chi\rangle
=
(0,\ a_0,\ \sqrt Z,\ \sqrt Y,\ 0)^{\mathsf T}.
}
\tag{17}
$$

项目原有的三个对易占据读口

$$
\begin{aligned}
N_X&=\operatorname{diag}(0,1,0,0,1),\\
N_Y&=\operatorname{diag}(0,0,0,1,1),\\
N_Z&=\operatorname{diag}(0,0,1,0,0)
\end{aligned}
$$

恰好读出

$$
\langle N_X\rangle=X,\qquad
\langle N_Y\rangle=Y,\qquad
\langle N_Z\rangle=Z.
$$

这采用的就是项目原本的占据轴定义。原始定义及其与其他三轴表示的关系，见项目 [AURIC 三轴误差几何文档](https://github.com/the-omega-institute/trureturing/blob/08e8767227de53351c42cb35028e01de5e88287d/docs/develop/theory/AURIC_THREE_AXIS_ERROR_GEOMETRY_UNITARY_COMPATIBILITY_AND_ENDOGENOUS_STABILITY_V35.md)。

这里还必须保存 $a_0$ 的符号，以及完整的 $H,\mathbf b$。因此，完整递归状态可以写成

<a id="eq-18"></a>

$$
\boxed{
\bigl(H,\mathbf b;\ a_0,X,Y,Z;\ S\bigr).
}
\tag{18}
$$

三轴负责表达本步的能量分配，矩阵负责保存所有已有关系。

---

<a id="section-6"></a>
## 六、酉性和误差控制都可以给出严格实现

### 1. 局部实际关系具有显式酉实现

由式 (8)，定义正测度

$$
d\mu(s)
=
\mathbf1_{(0,\delta)}(s)\mathscr K''(s)\,ds
+r\,\delta_L(ds).
$$

虽然它的总质量可以无限大，但其一阶矩有限：

$$
\int s\,d\mu(s)=S.
$$

在 Hilbert 空间

$$
\mathcal H
=
L^2\bigl((0,\infty)\times\mathbb R,\,
d\mu(s)\,du\bigr)
$$

中定义

$$
\Phi_t(s,u)=\mathbf1_{[t,t+s]}(u).
$$

于是

$$
\|\Phi_t\|^2=S,
\qquad
\langle\Phi_t,\Phi_v\rangle
=
\widetilde{\mathscr K}(t-v).
$$

特别地，当 $|t-v|\le\delta$ 时，

<a id="eq-19"></a>

$$
\boxed{
\langle\Phi_t,\Phi_v\rangle
=
\mathscr K(t-v).
}
\tag{19}
$$

平移算子

$$
(U_a f)(s,u)=f(s,u-a)
$$

满足

<a id="eq-20"></a>

$$
\boxed{
U_a^*U_a=I,\qquad
U_aU_b=U_{a+b},\qquad
U_a\Phi_t=\Phi_{t+a}.
}
\tag{20}
$$

所以，这个局部实际关系模型确实有酉平移实现。

这里实现于全实线的核是 $\widetilde{\mathscr K}$；它与实际核 $\mathscr K$ 的相等范围由式 (9) 精确限定。这一范围必须随证明一起保存。

### 2. 误差容忍量可以直接估计

将节点排序：

$$
t_1<\cdots<t_m,
\qquad
D=t_m-t_1\le\delta,
$$

令最小间距为

$$
h_{\min}=\min_{i<m}(t_{i+1}-t_i).
$$

### 定理 4：全矩阵谱隙下界

当 $m\ge2$ 时，

<a id="eq-21"></a>

$$
\boxed{
\lambda_{\min}(H)
\ge
\frac r4\min\{h_{\min},L-\delta\}.
}
\tag{21}
$$

### 证明

对任意复系数 $c_1,\ldots,c_m$，令

$$
C_i=\sum_{j\le i}c_j,\qquad M=C_m,
\qquad d_i=t_{i+1}-t_i.
$$

由区间指示函数表示，三角核能量恰为

<a id="eq-22"></a>

$$
\boxed{
c^*H_Lc
=
(L-D)|M|^2
+
\sum_{i=1}^{m-1}d_i
\bigl(|C_i|^2+|M-C_i|^2\bigr).
}
\tag{22}
$$

设

$$
\mu=\min\{h_{\min},L-\delta\}.
$$

丢弃一组非负项，得到

$$
c^*H_Lc\ge\mu\sum_{i=1}^{m}|C_i|^2.
$$

又因为 $c_i=C_i-C_{i-1}$、$C_0=0$，

$$
\sum_{i=1}^{m}|c_i|^2
\le4\sum_{i=1}^{m}|C_i|^2.
$$

结合 $H\succeq rH_L$，式 (21) 成立。证毕。

若实际读出的近似矩阵为

$$
\widehat H=H+E,\qquad E=E^*,
\qquad |E_{ij}|\le\eta,
$$

则

$$
|c^*Ec|
\le
\eta\left(\sum_i|c_i|\right)^2
\le m\eta\|c\|^2.
$$

所以得到明确的误差条件：

<a id="eq-23"></a>

$$
\boxed{
m\eta
<
\frac r4\min\{h_{\min},L-\delta\}
\quad\Longrightarrow\quad
\widehat H\succ0.
}
\tag{23}
$$

对于归一化矩阵 $H/S$，右端再除以 $S$。

这使“控制误差”有了具体内容：**每个有限阶段都存在正的误差容忍量，其大小取决于节点间距和已有矩阵的谱隙。**

---

<a id="section-7"></a>
## 七、进一步加强：任何已正定的实际配置，都可以在旧点附近继续扩张

上一节要求整个配置落在短窗口内。下面可以去掉这个要求，但保留“已有配置已经正定”这一前提。

### 定理 5：任意已正定配置的近点扩张

设

$$
H=[\mathscr K(t_i-t_j)]\succ0
$$

是任意一个实际有限配置。固定旧点 $t_j$，新增点取为

$$
t_j+h.
$$

则当 $h\ne0$ 足够小时，新增实际矩阵仍严格正定，并且

<a id="eq-24"></a>

$$
\boxed{
\mathcal E(h)
\sim |h|\log\frac1{|h|}
\qquad(h\to0).
}
\tag{24}
$$

### 证明

记

$$
d(h)=S-\mathscr K(h),
\qquad
\mathbf b(h)=He_j+\mathbf u(h).
$$

由于第 $j$ 个分量满足

$$
u_j(h)=-d(h),
$$

展开二次型得到精确恒等式

<a id="eq-25"></a>

$$
\boxed{
\mathcal E(h)
=
2d(h)-\mathbf u(h)^*H^{-1}\mathbf u(h).
}
\tag{25}
$$

由引理 1，

$$
d(h)
=
\frac{|h|}{2}\log\frac1{|h|}+O(|h|).
$$

对 $i\ne j$，$\mathscr K$ 在非零点 $t_i-t_j$ 附近局部 Lipschitz，因此

$$
u_i(h)=O(|h|).
$$

即使该差值恰为某个素数幂的对数，也只出现有限的导数跳跃，不影响这一估计。

于是，对固定的 $H$，

$$
\mathbf u(h)^*H^{-1}\mathbf u(h)
=
O\!\left(h^2\log^2\frac1{|h|}\right).
$$

代入式 (25)：

$$
\mathcal E(h)
=
|h|\log\frac1{|h|}+O(|h|)>0
$$

对足够小的非零 $h$ 成立。证毕。

这给出了另一条真正的递归接纳规则。

同时，新增矩阵的最小特征值满足

<a id="eq-26"></a>

$$
\boxed{
\lambda_{\min}(H_+(h))
\le S-\mathscr K(h)=d(h)\longrightarrow0.
}
\tag{26}
$$

证明只需取“旧点减新点”的单位向量计算 Rayleigh 商。

因此，近点插入虽然总能继续，但所需步长和误差精度依赖已有配置；它没有自动提供向任意远处推进的统一步长。

---

<a id="section-8"></a>
## 八、Zeckendorf 贪心序列现在能怎样参与证明？

项目的 [ZeckendorfGreedyPermutation.result](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.md) 给出了你指出的结果：

> 从 $1$ 出发，每次选择尚未使用、且与当前项的规范 Zeckendorf 展开恰有一个共同项的最小正整数，得到正整数的一个排列。

记该排列为 $a_1,a_2,\ldots$。

现在可以把它和上述局部定理严格组合。

### 定义 3：对数尺度分类

把正整数分入以下有限块：

<a id="eq-27"></a>

$$
\boxed{
\mathcal C_k
=
\left\{
m\ge1:
\frac{k\delta}{2}
\le\log m<
\frac{(k+1)\delta}{2}
\right\},
\qquad k\ge0.
}
\tag{27}
$$

### 推论

按 A370630 的顺序读取整数，有以下三个确定结论：

1. 每个正整数恰好进入一个块。
2. 每个固定块的全部整数，都在某个有限前缀中被读完。
3. 每个非空块，以及任意两个相邻块的并集，其实际核矩阵都严格正定。

前两条来自排列性和每块的有限性。第三条来自

$$
\operatorname{diam}\{\log m:
m\in\mathcal C_k\cup\mathcal C_{k+1}\}
<\delta
$$

及定理 1。

这样，**贪心序列负责遍历，尺度分类负责组织，局部正定定理负责保证每块内部的递归成立。**

### 尚需证明的跨块关系

两个已正定块的实际联合矩阵可写为

$$
\begin{pmatrix}
A&B\\
B^*&C
\end{pmatrix}.
$$

其正半定性等价于

$$
C-B^*A^{-1}B\succeq0,
$$

也等价于

<a id="eq-28"></a>

$$
\boxed{
\left\|A^{-1/2}BC^{-1/2}\right\|_{\mathrm{op}}
\le1.
}
\tag{28}
$$

这里 $B$ 的每一项都已经被实际算术核规定：

$$
B_{ij}=\mathscr K(t_i-u_j).
$$

**下一项全局任务，就是控制这些跨越较大对数距离的实际交叉关系。** 相邻块的情况已由局部定理覆盖；远距离块还没有得到式 (28) 的统一证明。

---

<a id="section-9"></a>
## 九、接回 Robin：再证明一条无条件正预算下界

上面主要推进关系矩阵。下面直接回到原整数 $n$，保留

$$
T=\log n,
\qquad
R(n)=\frac{\sigma(n)}
{e^\gamma n\log\log n}.
$$

Robin 判据要求对所有 $n>5040$ 有 $R(n)<1$，这与 RH 等价。[arxiv.org](https://arxiv.org/pdf/1112.6010?utm_source=chatgpt.com)

为与核 $\mathscr K$ 区分，把前面使用的素数层修正预算记为 $\mathcal B(T)$。

### 1. 精确分解

令

$$
q=\frac1{T\log T},
\qquad
z_p=q\log p,
$$

$$
\lambda_{p,j}
=
\log\frac{1-p^{-j-1}}{1-p^{-j}},
\qquad
\nu_{p,j}=\frac1{jp^j}.
$$

定义

$$
P(q)=\sum_{p,j}(\lambda_{p,j}-z_p)_+,
$$

$$
\mathcal D(n)
=
P(q)
-\left(\log\frac{\sigma(n)}n-qT\right)
\ge0,
$$

以及

$$
\mathcal B(T)
=
\sum_p\mathcal B_p(T),
$$

$$
\mathcal B_p(T)
=
\sum_{j\ge1}
\left[
\min(z_p,\lambda_{p,j})
-\min(z_p,\nu_{p,j})
\right].
$$

再定义

$$
I_\psi(T)
=
q\bigl(\psi(T)-T\bigr)
+\gamma+\log\log T
-\sum_{p^j\le T}\frac1{jp^j}.
$$

则有精确恒等式

<a id="eq-29"></a>

$$
\boxed{
-\log R(n)
=
\mathcal D(n)+I_\psi(T)+\mathcal B(T).
}
\tag{29}
$$

其代数依据是

$$
P(q)+\mathcal B(T)
=
\sum_{p^j\le T}\frac1{jp^j}
-q\psi(T).
$$

素数幂恰落在端点 $p^j=T$ 时，对应正部为零，所以端点取法不会改变该恒等式。

每素数预算都满足

$$
\mathcal B_p(T)\ge0.
$$

一种证明是注意到两组边际的总和相同，而

$$
\lambda_{p,1}<\nu_{p,1},
\qquad
\lambda_{p,j}>\nu_{p,j}\quad(j\ge2).
$$

因此对每个有限 $a\ge1$，

$$
e_p(a)
:=
\sum_{j\le a}\nu_{p,j}
-\sum_{j\le a}\lambda_{p,j}
=
\sum_{j>a}(\lambda_{p,j}-\nu_{p,j})
>0.
$$

比较两组前缀的最大收益，便得到预算非负性。

### 定理 6：仅用素数 $2$ 就能得到的正下界

对所有 $T\ge8$，

<a id="eq-30"></a>

$$
\boxed{
\mathcal B(T)>
\frac{7\log2}{16T\log T}.
}
\tag{30}
$$

### 证明

记

$$
z=\frac{\log2}{T\log T},
\qquad
b=\lfloor\log_2T\rfloor\ge3.
$$

选择最后一个严格活跃的二进素数层：

$$
a=\max\{j:\lambda_{2,j}>z\}.
$$

因为

$$
\lambda_{2,b}>
\nu_{2,b}
=\frac1{b2^b}
\ge z,
$$

所以

$$
a\ge b\ge3.
$$

由前缀收益比较，在这个实际活跃指数处有

<a id="eq-31"></a>

$$
\mathcal B_2(T)\ge e_2(a).
\tag{31}
$$

置

$$
x=2^{-a-1}\le\frac1{16}.
$$

最后一层严格活跃给出

$$
\begin{aligned}
z
&<\lambda_{2,a}\\
&=\log\left(1+\frac{x}{1-2x}\right)\\
&<\frac{x}{1-2x}
\le\frac87x.
\end{aligned}
$$

因此

<a id="eq-32"></a>

$$
x>\frac78z.
\tag{32}
$$

另一方面，

$$
e_2(a)
=
-\log(1-x)
-\sum_{j>a}\frac1{j2^j}.
$$

利用

$$
-\log(1-x)\ge x,
$$

以及

$$
\sum_{j>a}\frac1{j2^j}
\le
\frac1{a+1}\sum_{j>a}2^{-j}
=
\frac{2x}{a+1},
$$

得到

$$
e_2(a)
\ge
x\left(1-\frac2{a+1}\right)
\ge\frac x2
>\frac7{16}z.
$$

最后，

$$
\mathcal B(T)\ge\mathcal B_2(T)
\ge e_2(a)
>
\frac{7\log2}{16T\log T}.
$$

证毕。

### 对原整数的直接推论

由式 (29)—(30)，

<a id="eq-33"></a>

$$
\boxed{
-\log R(n)
>
I_\psi(T)+
\frac{7\log2}{16T\log T}.
}
\tag{33}
$$

因此，对满足 $n>5040$、$T=\log n\ge8$ 的原整数，

<a id="eq-34"></a>

$$
\boxed{
I_\psi(T)\ge
-\frac{7\log2}{16T\log T}
\quad\Longrightarrow\quad
R(n)<1.
}
\tag{34}
$$

这是一个明确的充分条件。我们没有把原整数换成优化整数，也没有删除其素数因子；优化只用于定义一个非负差额 $\mathcal D(n)$。

---

<a id="section-10"></a>
## 十、现在证明推进到了哪里？

本轮已经得到三项可以继续使用的结论：

$$
\boxed{
\begin{gathered}
\text{实际核在固定短窗口内，任意有限阶严格正定；}\\[1mm]
\text{递归插点具有显式正 Schur 余量和误差阈值；}\\[1mm]
\text{原整数 Robin 分解具有无条件的显式正预算。}
\end{gathered}
}
$$

这使你的 AURIC 递归思路具备了完整的局部数学实现：

$$
\text{真实关系}
\;\longrightarrow\;
\text{正交分解}
\;\longrightarrow\;
(X,Y,Z)
\;\longrightarrow\;
\text{守恒与误差界}
\;\longrightarrow\;
\text{下一次插入}.
$$

全局证明现在集中在两个具体位置：

- **关系矩阵方向：** 证明实际远距离交叉项满足式 (28)，从而把已经成立的局部块持续合并。
- **Robin 方向：** 证明所有原整数 $n>5040$ 的完整余额
$$
  \mathcal D(n)+I_\psi(\log n)+\mathcal B(\log n)
$$
  严格为正。式 (30) 供应了正预算，但 $I_\psi$ 的带符号波动仍须与完整预算比较。

其中最关键的界线是：**局部酉实现和每一步归一化已经能够严格构造；实际远距离关系的统一相容性，还需要来自素数分布本身的估计。** 本轮的定理把这条界线落实成了可继续攻击的 Schur 不等式，而不是继续停留在三维表示的直觉上。
<!-- author-end -->

</div>

---

## 编者条件注

- **Robin 端点约定（编者澄清）。** 第九节的 $\psi(T)$ 按与所示素数幂和一致的右连续约定定义：
  $$
  \psi(T):=\sum_{p^j\le T}\log p.
  $$
  原文“端点取法不会改变该恒等式”指两个端点和采用相同权重：在 $T=p^j$ 时，$1/(jp^j)=q\log p$，故同时纳入或同时删去这两项的净贡献均为零。此处须区别于所引 [Kedlaya 第八章定义 8.1](https://kskedlaya.org/ant/chapter-8.html?utm_source=chatgpt.com) 为显式公式采用的整数端点半权约定。若保留所示 $p^j\le T$ 的全权倒数和，却仅把 $\psi(T)$ 换为该半权函数，则在 $T=p^j$ 时，$P(q)+\mathcal B(T)$ 等式的右端会比左端多出 $q\log p/2$；半权须在两个和中一致使用才能抵消。此注仅补明原式的端点约定，不改变作者正文的定义域、公式或文字。
- **来源边界。** 作者正文对应 supplied source.md，原始 SHA256 为 <code style="overflow-wrap:anywhere">9c6672d5253c75ab0ca049f05ca85d7cbb5e405c23510c68f86bac1e66befa47</code>；正文转换只涉及外层数学定界符，锚点和本节均置于正文之外。原稿的“上一轮”“项目已有”“此前使用”等指代保留为作者叙述，不能单独当作本卷的新形式化证明。
- **固定材料核对。** 固定提交中的 `FiniteZeroGramHierarchy.md` 读数支持有限非负权重 Gram 分解；固定提交中的 `ZeckendorfGreedyPermutation.md` 与对应 Lean 源文支持该贪心序列是正整数排列；`EulerLayerRootCorrection.md` 仅作为背景供应。V35 固定 URL 的作者正文、Kedlaya 第八章页面、Suzuki 论文源文与 Robin 背景论文源文均已作非空文本读取。它们是来源核对材料，不是本卷新增 Lean 编译或 RH 认证。
- **纸面范围。** 逐段核对了实际核的常数项、素数幂项、无穷尾项、端点连续性和原点总量；尖点渐近中的两组系数恒等式与积分余项；三角核混合、端点零的可积性、严格 Gram 论证、Schur 最小值和相邻节点插值；三轴投影守恒、五模式读口、平移实现、谱隙与逐项误差阈值；任意正定配置的近点展开；Zeckendorf 分块与跨块 Schur 未决界；Robin 的精确分解、逐素数前缀比较、二进素数层的活跃指标和严格常数。上述检查保留作者给出的假设与量词，没有把纸面推导升级为项目形式化结果。
- **明确限制。** 式 (4) 的零点展开、零点计数导致的收敛、Robin 等价和相关素数分布输入仍是引用的经典材料；远距离块的统一 Schur 界、全局关系矩阵正性、全体整数余额的严格正性以及 RH 仍未完成。局部酉实现不等于原生制备、控制权限、观测取得或全局兼容性证明。

<!-- editorial-notes-end -->
