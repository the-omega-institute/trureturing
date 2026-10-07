# 来源域、未来操作与精确识别的稳定性

## 13. 来源域改变两次二次读数的识别能力

[Naming Relations and Stability 第 9–12 章](../../develop/theory/NAMING_RELATIONS_AND_STABILITY.md)询问同名关系能否与操作和目标相容。本章固定读数，改变允许产生状态的域，检验另一种区别：一个读数纤维中的候选实现是否都属于实际来源域。以下结论是经典二次型、二次方程与连续性结果的综合应用，不申报原创。全称结论由本章推导承担，有限实验只验证指定输入；没有新增冻结数学声明。

### 13.1 任意特征不为二的域上的判据

设 $K$ 是特征不为 $2$ 的域，$r,s,t\in K$。定义

$$
B=\begin{pmatrix}r&s\\s&t\end{pmatrix},\qquad
\Phi_B(a,b)=\bigl(a^2+b^2,\;ra^2+2sab+tb^2\bigr),\qquad
\Delta=(r-t)^2+4s^2.
\tag{13.1}
$$

这里观测是有序的两个值，不是它们的比值。以 $0$ 为平方，记平方集合为 $K^2_{\mathrm{sq}}=\{d^2:d\in K\}$。则

$$
\left[\forall x,y\in K^2,\quad
\Phi_B(x)=\Phi_B(y)\Longrightarrow y=x\ \text{或}\ y=-x\right]
\quad\Longleftrightarrow\quad
\Delta\notin K^2_{\mathrm{sq}}.
\tag{13.2}
$$

本判据不要求 $B$ 正定、可逆，或能够写成 $A^{\mathsf T}A$。在有限域上，第一读数是代数二次型，不是正的欧氏平方范数。

证明先把碰撞改写成共同实现上的两条约束。令 $u=x+y$、$v=x-y$，由对称性和 $2\ne0$，读数相等恰好等价于

$$
u^{\mathsf T}v=0,\qquad u^{\mathsf T}Bv=0.
\tag{13.3}
$$

非整体正负号碰撞恰好要求 $u,v$ 均非零。写 $u=(p,q)$，非零 $v$ 属于两行的共同零空间，迫使行列式为零，即

$$
sp^2+(t-r)pq-sq^2=0.
\tag{13.4}
$$

若 $\Delta$ 非平方，则 $s\ne0$；否则 $\Delta=(r-t)^2$。式（13.4）及 $u\ne0$ 又给出 $q\ne0$。令 $z=p/q$，得到

$$
sz^2+(t-r)z-s=0,\qquad (2sz+t-r)^2=\Delta,
\tag{13.5}
$$

与非平方矛盾，因此碰撞只能来自整体正负号。

反向，若 $s=0$，$(1,1)$ 与 $(1,-1)$ 已是非整体正负号碰撞。若 $s\ne0$ 且 $d^2=\Delta$，取

$$
z=\frac{r-t+d}{2s},\quad u=(z,1),\quad v=(-1,z),\quad
x=\frac12(z-1,1+z),\quad y=\frac12(z+1,1-z).
\tag{13.6}
$$

二次根公式给出式（13.5）的第一式，继而 $u^{\mathsf T}v=u^{\mathsf T}Bv=0$。$u,v$ 均非零，所以 $y\ne\pm x$，完成反向。

这也可以表述为：两次读数识别整体正负号，当且仅当 $B$ 没有定义在 $K$ 上的特征线。非平凡碰撞需要两行 $u^{\mathsf T}$、$u^{\mathsf T}B$ 成比例，正好给出这条特征线。

### 13.2 一般非退化第一二次型

设 $H,N$ 为 $K$ 上的对称二阶矩阵，且 $H$ 可逆。对

$$
\Psi(x)=\bigl(x^{\mathsf T}Hx,x^{\mathsf T}Nx\bigr),\qquad L=H^{-1}N,
$$

同一个证明得到

$$
\Psi\text{ 识别整体正负号}
\quad\Longleftrightarrow\quad
L\text{ 在 }K\text{ 中没有特征值}
\quad\Longleftrightarrow\quad
(\operatorname{tr}L)^2-4\det L\notin K^2_{\mathrm{sq}}.
\tag{13.7}
$$

确实，非零 $u,v$ 的约束变成 $u^{\mathsf T}Hv=u^{\mathsf T}Nv=0$；第一行因 $H$ 可逆而非零，故 $Nu=\lambda Hu$。反向，从这样的非零 $u$ 取非零 $H$ 正交向量 $v$ 即得碰撞。最后一步是二阶特征多项式的二次根判据。

因此不能把欧氏第一读数的实数失效推广为“任意两次实二次读数都失效”。例如

$$
(a,b)\longmapsto(a^2-b^2,2ab)
$$

是复数平方的实坐标表示，可在 $\mathbb R^2$ 上识别整体正负号；对应 $H^{-1}N$ 的判别式为 $-4$。第一型在此不定号，与式（13.1）的欧氏第一型不同。

### 13.3 同一更新在不同来源域上的实例

对更新 $A\in M_2(K)$，取 $B=A^{\mathsf T}A$。在 $\mathbb Q$ 或 $\mathbb R$ 上，式（13.1）就是更新前后的平方范数。Fibonacci 更新

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
B=M^2=\begin{pmatrix}1&1\\1&2\end{pmatrix},\qquad\Delta=5
\tag{13.8}
$$

给出 $\Phi_B(a,b)=(a^2+b^2,b^2+(a+b)^2)$。$5$ 在 $\mathbb Q$ 中不是平方，在 $\mathbb R$ 中是平方；所以两次精确读数识别所有有理状态到整体正负号，却不能识别所有实状态。

实碰撞可直接取

$$
x=(1,0),\qquad y=\frac{(-1,2)}{\sqrt5},\qquad
\Phi_B(x)=\Phi_B(y)=(1,1),\qquad y\ne\pm x.
\tag{13.9}
$$

第二个状态不属于 $\mathbb Q^2$。有理域的识别不是这两个读数在实数纤维中分辨了它，而是来源条件排除了它。

更新可逆不足以保证有理识别：$A=\operatorname{diag}(1,2)$ 的 $\Delta=9$，$(1,1)$ 与 $(1,-1)$ 碰撞。奇异 $A$ 也失效，因为 $\det B=0$，于是 $\Delta=(\operatorname{tr}B)^2$。若 $B=cI$，$\Delta=0$，第二读数只是第一读数的倍数。

在奇素数域上仍按式（13.2）判定，包括 $\Delta=0$ 的退化情形。特征二不在定理范围；本实验的 Fibonacci 模二读数恰好单射，并不证明特征二的一般判据。

## 14. 相同前两次读数，不同的未来操作

令 $E_n(x)=\|M^nx\|^2$。由于 $M$ 对称，$E_n(x)=x^{\mathsf T}B^nx$，而

$$
B^2-3B+I=0\quad\Longrightarrow\quad
E_{n+2}(x)=3E_{n+1}(x)-E_n(x),\qquad n\ge0.
\tag{14.1}
$$

所以对有理或实数状态，两次读数相等恰好等价于所有未来读数相等。Fibonacci 的全部平方范数历史不能消除式（13.9）的实歧义。这是指定更新的结论，没有推广到任意 $A$。

比较剪切更新

$$
S=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad S^{\mathsf T}S=B.
\tag{14.2}
$$

它与 Fibonacci 有相同的前两次读数，但其第三读数为 $E_2=a^2+4ab+5b^2$。对同一初始状态及同一个剪切操作，三次读数同时满足

$$
b^2=\frac{E_2-2E_1+E_0}{2},\qquad
a^2=E_0-b^2,\qquad ab=\frac{E_1-E_0-b^2}{2}.
\tag{14.3}
$$

故三次读数确定 $xx^{\mathsf T}$，并在实数域上确定 $x$ 到整体正负号。理由是 $a^2,b^2$ 确定各非零坐标的正负号候选，而 $ab$ 固定二者相对正负号；零坐标也包含在这个论证中。

式（13.9）的两状态在剪切下第三读数分别为 $1$ 与 $13/5$。前两次相同不足以判定未来是否相同；必须保留具体操作 $A$，不能只保留它的第一步 Gram 矩阵 $A^{\mathsf T}A$。

## 15. 精确算术识别与误差边界

### 15.1 实纤维中的反射与有理逼近

对有理对称 $B$ 且 $\Delta$ 在 $\mathbb Q$ 中非平方，令

$$
R_B=\frac{2B-(r+t)I}{\sqrt\Delta}.
\tag{15.1}
$$

此时 $\Delta>0$；中心化二阶矩阵恒等式给出 $R_B^{\mathsf T}R_B=I$，而 $R_B$ 与 $B$ 对易，故 $R_B^{\mathsf T}BR_B=B$。因此实状态 $x$ 与 $R_Bx$ 的两读数相同。

非零有理 $x$ 的分子是非零有理向量，除以无理数 $\sqrt\Delta$ 后不再有理。$R_Bx\ne\pm x$，因为否则它会给出有理特征线。取有理序列 $y_j\to R_Bx$，则

$$
\Phi_B(y_j)\to\Phi_B(x),\qquad
\min\{\|y_j-x\|,\|y_j+x\|\}
\to\min\{\|R_Bx-x\|,\|R_Bx+x\|\}>0.
\tag{15.2}
$$

这是普通拓扑推导：读数像取欧氏子空间拓扑，状态模整体正负号使用距离 $d([x],[y])=\min\{\|x-y\|,\|x+y\|\}$；有理状态模整体正负号的逆映射在每个非零有理状态对应的读数处不连续。它不涉及读数精度有限之外的统计噪声模型。

一个较窄但直接核验的边界是：不存在全局连续函数 $g:\mathbb R^2\to\mathbb R$，在所有有理初态的 Fibonacci 读数上返回 $a^2$。若有，由有理对的稠密性和复合映射连续性，该等式延伸到所有实初态。式（13.9）却要求 $g(1,1)$ 同时为 $1$ 和 $1/5$。这个边界不等同于已经形式化了式（15.2）的整个商空间断言。

### 15.2 无浮点平方根的任意精度近碰撞

定义非负整数序列

$$
p_0=1,\quad q_0=0,\qquad
p_{n+1}=9p_n+20q_n,\quad q_{n+1}=4p_n+9q_n.
\tag{15.3}
$$

它是经典 Pell 单位 $9+4\sqrt5$ 的幂。一步代数恒等式

$$
(9p+20q)^2-5(4p+9q)^2=p^2-5q^2
$$

及归纳给出 $p_n^2-5q_n^2=1$。非负性与 $p_{n+1}\ge9p_n$ 给出 $p_n\ge9^n$。因此有理状态 $y_n=(-q_n/p_n,2q_n/p_n)$ 对所有 $n\ge1$ 满足

$$
\Phi_B(y_n)=\left(1-\frac1{p_n^2},1-\frac1{p_n^2}\right),\qquad
\|\Phi_B(y_n)-(1,1)\|_\infty=\frac1{p_n^2}\le81^{-n},
\tag{15.4}
$$

但对目标 $T(a,b)=a^2$，

$$
T(1,0)-T(y_n)=1-\frac{q_n^2}{p_n^2}
=\frac45+\frac1{5p_n^2}>\frac45.
\tag{15.5}
$$

读数误差可以任意小，目标差仍有固定下界。第一项 $(p_1,q_1)=(9,4)$ 的读数为 $(80/81,80/81)$，误差 $1/81$，目标差 $65/81$。这是一组实际有理状态，不是独立优化两项误差后假定共同可达。实验精确计算前八项；全称归纳和读数公式由上述推导承担，八项计算不替代无限结论。

### 15.3 给定分母界后的有限误差保证

非平方 $\Delta$ 的有理 $B$ 下，若实际状态限制为 $(m/q,n/q)$，其中 $m,n\in\mathbb Z$、$1\le q\le H$，且正整数 $D$ 清除 $r,s,t$ 的分母，那么两次读数都在 $(Dq^2)^{-1}\mathbb Z$ 中。任意两个非整体正负号的合法状态 $x,y$ 必有至少一读数不同，由整数间距得

$$
\|\Phi_B(x)-\Phi_B(y)\|_\infty\ge\frac1{Dq^2q'^2}\ge\frac1{DH^4}.
\tag{15.6}
$$

若每项测量误差严格小于 $1/(2DH^4)$，同一测量值至多兼容一个合法整体正负号类。这个结论是唯一性保证，不保证候选存在、算法高效或实际来源确有分母上界。不能将它用于不限制分母的式（15.4）。

## 16. 研究含义、来源与未完成边界

本章也具体化了 [关系纤维演算第 3.6 节](../../develop/theory/FIB_RELATIONAL_FIBER_CALCULUS.md#3-表示纤维与观察纤维) 的关系型噪声观察：若报告允许每项误差不超过任意给定 $\varepsilon>0$，式（15.4）中足够大的 $n$ 使同一报告 $(1,1)$ 同时允许来源 $(1,0)$ 和 $y_n$，而目标 $a^2$ 不同。于是这份噪声关系不能零错误恢复该目标。报告重叠在此是关系，不把它误作等价关系。

本章支持一个具体研究区分：观测本身保留区别，来源条件排除另一种实现，以及未来操作补充区别，是三种不同的识别机制。比较必须保留同一个实际状态、状态来源和观测历史。精确来源条件带来的唯一性，也须另行检查能否承受误差。

用于“道与名”的读法是：一份命名是否足够，取决于它与生成来源、允许操作及目标的关系；名称的数值结构不能独自承担这个判断。这不是世界本体定理，也没有把有理域当作真实物理状态域。与圆周双覆盖相接仍需要指定共同载体、覆盖映射、操作和连续性条件；整体正负号出现于本章，尚不构成与圆周或五分类的同构。

### 16.1 文献与形式库复用

| 来源 | 使用范围 |
| --- | --- |
| Yang Wang、Zhiqiang Xu，[Generalized phase retrieval: measurement number, matrix recovery and beyond](https://arxiv.org/abs/1605.08034) | 已核对来源摘要；二次测量与低秩矩阵恢复的背景，未据此认定式（13.2）为其精确结论。 |
| Robert Beinert、Marzieh Hasannasab，[Phase retrieval and system identification in dynamical sampling via Prony’s method](https://doi.org/10.1007/s10444-023-10059-7)，Advances in Computational Mathematics 49:56 | 已核对原文摘要与引言的测量定义；研究 $|\langle x,A^\ell\varphi\rangle|$ 与系统辨识，测量向量及假设不同，不直接借用其结论证明总范数读数的判据。 |
| 仓内 GoldenModularStandardPair、FibonacciMatrixDiscriminant、MatrixTracePowerSum、FiniteTimeTomographySaturation、ExactGramianSeries | 现有矩阵、Cayley–Hamilton 和观测表示；线性观测的可观测性不能直接证明范数读数识别。私有声明也纳入复用检索，未重证为新增公开包装。 |
| 钉版 Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` | 二次判别式、二阶矩阵中心化恒等式、稠密等化与平方根结果；一般域非平方充分性、有理 Fibonacci 应用、剪切重构恒等式及无全局连续目标解码器经过临时精确应用编译。它们未新增为持久绑定声明。 |
| [DiscretePhaseRetrieval](https://github.com/josefgreilhuber/DiscretePhaseRetrieval/tree/84af22b3cd5652ad9f9e6a8a3a7625a2ac285d13)、[PhaseRetrieval](https://github.com/susannabertolini/PhaseRetrieval/tree/5b4669896af57746b6621634f49edc8cc0f16d79)、[Phaseless](https://github.com/joaquimortega/Phaseless/tree/48028b76f5bedddcacd9f6f42b76540116744213) | 已检索相关源码：涉及 Hermite/Fock 或函数空间相位恢复，所见声明不是本章两次有理二次读数的直接接口；未构建这些第三方库或核验其公理闭包。 |

式（13.2）、（13.7）的完整等价打包、全部历史递推、商空间逆不连续断言、Pell 全称构造和分母界由普通数学推导与独立数学评审核对，没有新增为 kernel 冻结声明。有限程序及其 JSON 是可复现实验，不是 Lean 证书。文献检索未完成穷尽性或原创性核查；外部 Pro 搜索没有可用执行池，未取得该渠道的研究结论。

### 16.2 可继续推进的实质问题

较高维的共同观测纤维如何随来源域改变，有限精度下来源约束能保留多少识别能力，以及哪些更新能把静态歧义转为可辨别的未来读数，仍需各自指定量词、误差和资源后研究。式（15.6）没有给出高效解码器；式（14.3）没有分类所有更新；本章没有完成合法 Fibonacci 词形向带符号模型的忠实桥梁、五分类关联或物理应用。

程序、输入结果和运行说明见 [算术观测实验](README.md)。
