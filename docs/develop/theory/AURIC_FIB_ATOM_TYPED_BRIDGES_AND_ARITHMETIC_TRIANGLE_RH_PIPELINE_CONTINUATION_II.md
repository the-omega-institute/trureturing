> **Mathematical scope.** This continuation concerns Fisher–Dirichlet spectra, triangle information budgets, geometric limits, bounded observation, and conditional RH relationships.
> Its mathematical source is commit `a2f195ceb64aaaea7eeb8a6bdea479ca2c3c7430`; individual source attributions and applicability limits accompany the corresponding statements.
> Finite constructions retain their stated hypotheses; physical interpretations, general source compatibility, and RH identifications require the additional bridges specified in the text.
>
> **Navigation.** This volume follows [the original volume](AURIC_FIB_ATOM_TYPED_BRIDGES_AND_ARITHMETIC_TRIANGLE_RH_PIPELINE.md) and [the first continuation](AURIC_FIB_ATOM_TYPED_BRIDGES_AND_ARITHMETIC_TRIANGLE_RH_PIPELINE_CONTINUATION.md).
> It carries the original source heading `后续严格补充` and sections 49–65 exactly once; no new mathematical section is introduced.
> Statements attributed to other sources retain those sources’ explicit hypotheses and limits.

## 后续严格补充

下面两节把一般有限 CPTP 的 SLD Fisher 收缩、triangle 源信息预算，以及 metric-measure/Mosco 极限条件接入前述预测商、曲率和量子场管线。它们保留有限维证明与极限假设的类型边界。

## 49. Fisher–Dirichlet 谱场与自伴能级接口

前面的能量泛函只说明了一个场如何产生势能、耦合和轨迹。本节把“能级”限定为势能在内禀度量下的二阶曲率，避免把任何有限矩阵的特征值直接叫作物理能量或 zeta 零点。

### 定义 49.1（Fisher 切空间）

令 \(p\in\Delta^\circ(\Sigma)\) 是五态单纯形内点，定义

\[
T_p\Delta(\Sigma)=\left\{a\in\mathbb R^\Sigma:\sum_s a_s=0\right\},
\qquad
g_p^F(a,b)=\sum_{s\in\Sigma}\frac{a_sb_s}{p_s}.
\]

对于 \(a\in T_p\Delta(\Sigma)\)，相对熵有局部展开

\[
D_{\rm KL}(p+\varepsilon a\Vert p)
=
\frac{\varepsilon^2}{2}g_p^F(a,a)+O(\varepsilon^3).
\tag{49.1}
\]

因此 Fisher 度量是概率场在观察点的二阶信息尺度。它是由概率与归一化产生的几何量，不预设物理单位。

### 定理 49.2（Fisher Hessian 的自伴能级）

设 \(\mathscr E:\Delta^\circ(\Sigma)\to\mathbb R\) 光滑，\(q\) 是约束临界点，令

\[
B_q(a,b)=d^2\mathscr E_q[a,b]
\]

为切空间上的 Hessian 双线性型。存在唯一线性算子 \(H_q:T_q\Delta\to T_q\Delta\)，满足

\[
B_q(a,b)=g_q^F(H_qa,b).
\tag{49.2}
\]

若 \(B_q\) 对称，则 \(H_q\) 在 Fisher 内积下自伴；若 \(B_q\) 半正定，则 \(H_q\) 半正定。令 \(G_q\) 表示 \(g_q^F\) 的矩阵，则欧氏共轭

\[
\widehat H_q
=
G_q^{1/2}H_qG_q^{-1/2}
=
G_q^{-1/2}B_qG_q^{-1/2}
\]

是实对称半正定矩阵。其特征值 \(\lambda_j\ge0\) 是严格意义上的局部场能级，零特征值对应势能的平坦方向、约束方向或规范冗余。

证明：Fisher 度量在内点的切空间上正定，故 Riesz 表示给出唯一 \(H_q\)。由 (49.2) 立即得到自伴性和半正定性。矩阵共轭把 Fisher 自伴算子变为普通欧氏对称矩阵。证毕。

### 推论 49.3（耗散率与保守频率必须分开）

若在 \(q\) 附近采用 Fisher 梯度流，令 \(\delta=p-q\)，则在 Fisher 正交坐标的一阶近似为

\[
\dot\delta=-H_q\delta.
\]

每个 \(\lambda_j\) 是相应模态的线性衰减率。若另有满足 \(J_q^*=-J_q\) 的保守结构，则

\[
\dot\delta=J_qH_q\delta.
\]

此时 \(H_q\) 仍是自伴能量算子，而 \(J_qH_q\) 一般不是自伴，轨迹谱可以出现 \(\pm i\omega\)。因此，若要讨论 Hilbert–Pólya，候选对象应优先取 \(H_q\) 或全局 Dirichlet 算子；耗散生成元和保守轨迹生成元不能直接互换为 zeta 的自伴算子。

### 定理 49.4（可逆图的 Dirichlet 自伴谱）

令 \(\Omega=V\times\Sigma\)，取 \(\pi_i>0\) 和转移核 \(P\)，满足

\[
\pi_iP_{ij}=\pi_jP_{ji}.
\]

在 \(L^2(\pi)\) 内积

\[
\langle f,g\rangle_\pi=\sum_i\pi_if_ig_i
\]

下，\(L=I-P\) 自伴半正定，并且

\[
\langle f,Lg\rangle_\pi
=
\frac12\sum_{i,j}\pi_iP_{ij}(f_i-f_j)(g_i-g_j).
\tag{49.3}
\]

于是 \(f_t=e^{-tL}f_0\) 满足

\[
\frac{d}{dt}\|f_t\|_\pi^2
=
-2\langle f_t,Lf_t\rangle_\pi
\le0.
\]

这给出了“地势沿图传播并耗散”的有限精确版本。若总场 Hessian 可写成

\[
B=L_G\otimes K,
\]

其中 \(L_G\) 是节点图拉普拉斯，\(K\) 是内部五态曲率型，则在相应度量下全局能级为

\[
\Lambda_{ab}=\mu_a\lambda_b,
\]

这里 \(\mu_a\) 是 \(L_G\) 的特征值，\(\lambda_b\) 是 \(K\) 的广义 Fisher 特征值。图传播与局部五态能级因此可以先分离，再研究耦合。

### 定理 49.5（镜像扇区与隐藏纤维的兼容分解）

令 \(R\) 交换状态 \(2\) 与 \(5\)，固定 \(0,3,25\)。当 \(q_2=q_5\) 时，\(R\) 是 Fisher 等距。若势满足

\[
\mathscr E\circ R=\mathscr E,
\]

则 \(H_qR=RH_q\)，切空间分解为 Fisher 正交的偶、奇两个谱块。

在坐标顺序 \((0,2,3,5,25)\) 下，奇方向可取

\[
o=(0,1,0,-1,0),
\]

而可见投影的隐藏方向是

\[
d=(1,-1,0,-1,1).
\]

它们不是同一个方向：\(o\) 是镜像奇向量，\(d\) 是镜像偶向量。全空间满足

\[
\mathbb R^5=E_+\oplus E_-,
\qquad
\dim(E_+,E_-)=(4,1),
\]

而 \(K=\ker P=\operatorname{span}\{e_0,d\}\subset E_+\)，所以

\[
\mathbb R^5/K
\quad\text{的奇偶维数为}\quad
(2,1).
\]

归一化切空间的维数为 \(4\)，商去 \(d\) 后得到可见切空间的维数 \(3=2+1\)。这与

\[
\dim(\ker P)+\dim(\operatorname{im}P)=2+3=5
\]

完全兼容，但二者表达不同的结构：前者是观察核的维数分解，后者是镜像对合的 parity 分解。

在对称参考点 \(q=(q_0,r,q_3,r,q_{25})\) 上，奇基 \(o\) 的 Fisher 范数为

\[
g_q^F(o,o)=\frac2r.
\]

例如取镜像不变的局部势

\[
\mathscr E_{\rm odd}(p)=\frac{\kappa_o}{2}(p_2-p_5)^2,
\]

则奇块唯一非零的广义能级为

\[
\lambda_{\rm odd}=2\kappa_or.
\]

这只是一个可计算的 toy 曲率模型，不能解释 zeta 零点。

### FIB 支持转移的边界

禁邻支持的转移矩阵

\[
A_{\rm Fib}=
\begin{pmatrix}
1&1\\
1&0
\end{pmatrix}
\]

是实对称矩阵，谱为

\[
\left\{\varphi,-\varphi^{-1}\right\}.
\]

这证明 Fibonacci 支持场拥有有限真实谱，但它没有提供素数 Euler 因子、Archimedean Gamma 因子或 zeta 行列式。一般带权转移矩阵只有在存在正权 \(d_i\) 使

\[
d_i^2T_{ij}=d_j^2T_{ji}
\]

时才能通过正对角共轭变成自伴矩阵；复杂振荡权不自动满足该条件。

---

## 50. 素数三胞胎的算术场、缺陷能量与局部曲率

素数三胞胎可以进入当前框架，但最稳的进入方式是把它看作局部算术统计场，而不是直接把三胞胎等同于五态 \(101\) 支持模式。

### 定义 50.1（固定模式的三点统计）

令 \(x(n)=\mathbf 1_{\mathbb P}(n)\)，取固定模式

\[
H=\{0,h_1,h_2\},
\qquad
t_H(n)=\prod_{h\in H}x(n+h),
\qquad
T_H(N)=\sum_{n\le N}t_H(n).
\]

当 \(T_H(N)>0\) 时，对模数 \(q\) 定义可容许起点集合

\[
A_H(q)=
\left\{a\bmod q:
\gcd\!\left(\prod_{h\in H}(a+h),q\right)=1
\right\}.
\]

经验条件分布和均匀可容许基准分别为

\[
\mu_{H,q}^{N}(a)
=
\frac1{T_H(N)}
\sum_{n\le N}t_H(n)\mathbf 1_{n\equiv a\pmod q},
\]

\[
\lambda_{H,q}(a)
=
\frac{\mathbf 1_{a\in A_H(q)}}{|A_H(q)|}.
\]

取 \(\epsilon>0\)，定义局部缺陷能量

\[
D_{H,q}^{2}(N)
=
\sum_{a\bmod q}
\frac{\bigl(\mu_{H,q}^{N}(a)-\lambda_{H,q}(a)\bigr)^2}
{\lambda_{H,q}(a)+\epsilon}.
\tag{50.1}
\]

对 \(q\le Q\) 和非负权 \(w_q\)，定义算术场能量

\[
\mathscr E_{\rm sieve}^{Q}(H,N)
=
\sum_{q\le Q}w_qD_{H,q}^{2}(N)\ge0.
\tag{50.2}
\]

它测量真实三点起点在局部模可容许场中的偏离，不是物理能量。

### 定义 50.2（模尺度输运与离散曲率）

若 \(q\mid q'\)，令 \(\rho_{q'\to q}\) 为剩余类归约。使用同一 \(N\) 的经验分布满足精确一致性

\[
(\rho_{q'\to q})_\#\mu_{H,q'}^N=\mu_{H,q}^N.
\tag{50.3}
\]

因此经验输运可以作为数据一致性检查。基准分布一般不满足同样的均匀性，定义

\[
\Theta_{q'\to q}
=
W_2\!\left(
(\rho_{q'\to q})_\#\lambda_{H,q'},
\lambda_{H,q}
\right).
\tag{50.4}
\]

在模数格的选定边集 \(q\sim q\ell\) 上，把

\[
U_H(q)=D_{H,q}^{2}(N)
\]

当作尺度势，定义

\[
K_H(q)
=
\sum_{\ell\in L(q)}
a_{q,\ell}\bigl[U_H(q\ell)-U_H(q)\bigr],
\qquad a_{q,\ell}\ge0.
\tag{50.5}
\]

这是模数图上的加权拉普拉斯差分，能定位筛约束随尺度的变化。称其为算术曲率时，含义仅限于这个离散统计场。

### 定理 50.3（局部奇异因子与正算子迹）

令

\[
\nu_H(\ell)
=
\left|\{-h\bmod\ell:h\in H\}\right|.
\]

在 \(\mathcal H_\ell=\mathbb C^\ell\) 上定义可容许投影

\[
P_{H,\ell}
=
\sum_{a\in A_H(\ell)}
|a\rangle\langle a|.
\]

它是正交自伴投影，归一化迹为

\[
\tau_\ell(P_{H,\ell})
=
1-\frac{\nu_H(\ell)}{\ell}.
\]

相对于独立单点基准，定义

\[
u_H(\ell)
=
\frac{1-\nu_H(\ell)/\ell}{(1-1/\ell)^3},
\qquad
\kappa_H(\ell)=\log u_H(\ell).
\tag{50.6}
\]

当 \(q\) 为平方自由数时，中国剩余定理给出局部投影的张量化，且

\[
\log \tau_q(P_{H,q})
=
\sum_{\ell\mid q}
\log\!\left(1-\frac{\nu_H(\ell)}{\ell}\right).
\tag{50.7}
\]

所以截断的奇异级数是局部正算子迹比的乘法势。有限截断保持严格自伴性和正性，但无限乘积、正则化行列式与全局谱参数仍未构造。

以 \(H=\{0,2,6\}\) 为例，

\[
\nu_H(2)=1,\qquad
\nu_H(3)=2,\qquad
\nu_H(\ell)=3\quad(\ell\ge5),
\]

从而 Hardy–Littlewood 型基准为

\[
\mathfrak S(H)
=
\frac92
\prod_{\ell\ge5}
\frac{\ell^2(\ell-3)}{(\ell-1)^3}.
\tag{50.8}
\]

其中 \(\mathfrak S(H)\) 以及由它得到的三胞胎渐近仍是猜想性基准。对应的局部算术曲率

\[
\kappa_H(2)=\log4,\qquad
\kappa_H(3)=\log\frac98,\qquad
\kappa_H(\ell)=
\log\frac{\ell^2(\ell-3)}{(\ell-1)^3}
\]

描述 CRT 局部模障碍，不是时空曲率，也不是 RH 的谱曲率。

若用 \(Y_n=(x(n+h))_{h\in H}\in\{0,1\}^3\) 的经验分布构造三阶指数族，则三体累积量是独立基线之外的不可约三点场强。它能作为三点相关的第三阶观测，但仍不足以决定全局一阶显式公式。

---

## 51. 从有限自伴能级到广义 RH 的必要门槛

镜像、Fisher Hessian 和局部正算子只能构造 RH 的候选接口。一个可审计的 Hilbert–Pólya 路线至少需要以下对象。

设 \(H_N=H_N^*\) 是有限场谱算子，\(D=D^*\) 是具有紧预解式的极限算子，且 \(D\) 的谱写为 \(\{\gamma_j\}\)。若正规化特征行列式 \(D_N^{\rm reg}(z)\) 在紧集上一致收敛到 \(D^{\rm reg}(z)\)，并存在无零整函数 \(e^{Q(z)}\) 使

\[
\Xi(z)
=
\xi\!\left(\frac12+iz\right)
=
C e^{Q(z)}D^{\rm reg}(z),
\tag{51.1}
\]

同时已匹配 Gamma 因子、Euler 局部因子、零点重数和增长条件，则 \(D\) 的实谱才会推出 \(\Xi\) 的全部零点位于实 \(z\) 轴，从而推出 RH。

若研究一般完成 \(L\)-函数，则非自对偶扇区必须成对出现。取单位ary 对合

\[
R:\mathcal H_\pi\to\mathcal H_{\widetilde\pi},
\qquad
R^2=I,
\]

并构造满足

\[
RDR^{-1}=-D
\tag{51.2}
\]

的一阶自伴算子，便得到谱的 \(\pm\gamma\) 配对，对应 \(s\leftrightarrow1-s\) 的功能方程对称。一个抽象模板是

\[
D=
\begin{pmatrix}
0&B^*\\
B&0
\end{pmatrix},
\qquad
D^2=
\begin{pmatrix}
B^*B&0\\
0&BB^*
\end{pmatrix}.
\]

这说明“镜像”首先给出对称配对；实谱仍来自自伴性和正定 Hilbert 结构。仅有有限矩阵实谱、谱间距相似、前若干数值吻合或 \(2\leftrightarrow5\) 的组合对称，都不构成 RH 证据。

等价的迹公式接口需要对测试函数 \(f\) 证明正规化恒等式，其结构必须同时包含恒等项、Archimedean 项、素数及幂次项、扇区对偶项和零点谱项。当前文档中的 Fibonacci 矩阵、模投影和有限 Hessian 只完成 field-side 的有限对象，尚未完成 prime-coded transfer、正则化、完成 \(L\)-函数行列式或全局自伴算子。

---

## 52. 有限谱与统计量的依赖条件

下列有限对象依赖各自指定的输入；其谱、统计量与收敛性质不提供额外的物理解读。

1. 对给定的 $q=(q_0,r,q_3,r,q_{25})$，Fisher Gram 矩阵及镜像不变势的二阶型采用下列偶基
   \[
   (1,0,0,0,-1),\quad
   (0,1,0,1,-2),\quad
   (0,0,1,0,-1)
   \]
   和奇基 $o=(0,1,0,-1,0)$；给定镜像不变势的二阶型相应分为 $3\times3$ 偶块与 $1\times1$ 奇块。

2. 有限节点图上 $B=L_G\otimes K$ 的乘积谱 $\mu_a\lambda_b$，以及图常数零模、内部隐藏核和镜像奇模态各自所属的因子。

3. 对有限 $N,Q$，$\mu_{H,q}^{N}$、$D_{H,q}^2$、$\Theta_{q'\to q}$ 和 $K_H(q)$ 的定义保留 $T_H(N)=0$ 时统计量未定义的边界；$H=\{0,2,6\}$ 与其他可容许三点模式对应不同的输入。

4. 有限 $H_N$ 的特征多项式为
   \[
   \det(H_N-zI)
   \]
   其反射奇偶、实谱、正定性和截断收敛性质分别依赖相应假设；在缺少 (51.1) 的完成函数恒等式时，这些 toy 零点不能被识别为 zeta 零点。

这四类对象分别表达“场产生能量、能量产生轨迹、观察产生三维投影、算术局部场产生尺度缺陷”的有限数学关系；从有限结构到 RH 仍需行列式与显式公式条件。


## 53. CPTP Fisher 收缩与 triangle 网络的信息预算

前文已经证明了 FIB seam 在对角量子扇区中等于经典 Fisher 信息。本节把这一结果推进到一般有限维输出态：三个独立量子源先形成乘积态，再通过局部 triangle 网络 CPTP 映射输出。输出可以是非对角、非交换的量子态，但其 SLD Fisher 信息不能超过独立源所携带的信息总量。

### 定义 53.1（SLD Fisher 的有限维二次型）

令 \(\rho\succ0\) 是有限维严格正定密度矩阵，令 \(X=X^\ast\) 且 \(\operatorname{tr}X=0\) 是一个合法切向量。定义 Lyapunov 超算子

\[
\mathcal J_\rho(Y)=\frac12(\rho Y+Y\rho).
\]

由于 \(\rho\succ0\)，\(\mathcal J_\rho\) 在 Hermitian 矩阵空间上可逆。令

\[
L_\rho(X)=\mathcal J_\rho^{-1}(X)
\]

为 SLD，并定义

\[
F_\rho(X)
=
\operatorname{tr}\bigl(XL_\rho(X)\bigr)
=
\operatorname{tr}\bigl(\rho L_\rho(X)^2\bigr).
\]

在 Hermitian 矩阵空间上使用实 Hilbert--Schmidt 配对

\[
\langle A,B\rangle_{\mathbb R}
=
\operatorname{Re}\operatorname{tr}(AB).
\]

### 引理 53.2（SLD Fisher 的变分表示）

对上述 \((\rho,X)\)，有

\[
\boxed{
F_\rho(X)
=
\sup_{Y=Y^\ast}
\left\{
2\operatorname{Re}\operatorname{tr}(XY)
-\operatorname{tr}(\rho Y^2)
\right\}.
}
\]

#### 证明

在 Hermitian 空间上，\(\mathcal J_\rho\) 是严格正的自伴算子。对任意 Hermitian \(Y\)，完成平方得到

\[
\begin{aligned}
&2\langle X,Y\rangle_{\mathbb R}
-\langle Y,\mathcal J_\rho(Y)\rangle_{\mathbb R}\\
&=
2\langle\mathcal J_\rho(L_\rho(X)),Y\rangle_{\mathbb R}
-\langle Y,\mathcal J_\rho(Y)\rangle_{\mathbb R}\\
&=
F_\rho(X)
-
\langle Y-L_\rho(X),
\mathcal J_\rho(Y-L_\rho(X))\rangle_{\mathbb R}.
\end{aligned}
\]

而

\[
\langle Y,\mathcal J_\rho(Y)\rangle_{\mathbb R}
=
\operatorname{tr}(\rho Y^2),
\]

最后一项非负，并在 \(Y=L_\rho(X)\) 时取零。证毕。

### 定理 53.3（一般 CPTP 映射下的 SLD Fisher 收缩）

令 \(\Phi:\mathsf L(H)\to\mathsf L(K)\) 为 CPTP 映射，令

\[
\sigma=\Phi(\rho)\succ0,
\qquad
Z=\Phi(X).
\]

则

\[
\boxed{
F_\sigma(Z)
\le
F_\rho(X).
}
\]

#### 证明

令 \(\Phi^\ast\) 为 Hilbert--Schmidt 伴随。因为 \(\Phi\) CPTP，\(\Phi^\ast\) 是首一完全正映射。对任意 Hermitian \(Y\in\mathsf L(K)\)，由伴随关系有

\[
\operatorname{Re}\operatorname{tr}(ZY)
=
\operatorname{Re}\operatorname{tr}(X\Phi^\ast(Y)),
\]

以及

\[
\operatorname{tr}(\sigma Y^2)
=
\operatorname{tr}(\rho\Phi^\ast(Y^2)).
\]

首一完全正映射满足 Kadison 不等式

\[
\Phi^\ast(Y^2)
\succeq
\Phi^\ast(Y)^2.
\]

因此

\[
\begin{aligned}
&2\operatorname{Re}\operatorname{tr}(ZY)
-\operatorname{tr}(\sigma Y^2)\\
&\le
2\operatorname{Re}\operatorname{tr}(X\Phi^\ast(Y))
-\operatorname{tr}\bigl(\rho\Phi^\ast(Y)^2\bigr)\\
&\le F_\rho(X),
\end{aligned}
\]

其中最后一步使用引理 53.2。对 \(Y\) 取上确界即得结论。证毕。

这个定理将 §29 的经典 Fisher 收缩推广到可以产生非对角量子相干的任意有限 CPTP 网络。它只需要有限矩阵的 Kadison 不等式和 SLD 的变分表示，不需要连续流形或物理测量公理。

### 推论 53.4（可逆 CPTP seam 上的 Fisher 等式）

若存在 CPTP 恢复映射

\[
\mathcal R:\mathsf L(K)\to\mathsf L(H)
\]

满足

\[
\mathcal R(\Phi(\rho))=\rho,
\qquad
\mathcal R(\Phi(X))=X,
\]

则

\[
F_{\Phi(\rho)}(\Phi(X))=F_\rho(X).
\]

#### 证明

定理 53.3 分别应用于 \(\Phi\) 和 \(\mathcal R\)，得到

\[
F_\rho(X)
\ge
F_{\Phi(\rho)}(\Phi(X))
\ge
F_{\mathcal R\Phi(\rho)}(\mathcal R\Phi(X))
=
F_\rho(X).
\]

两端相等，所以中间等式成立。证毕。

该推论提供了一个可形式化的“无信息逃逸”判据。若存在同一 CPTP 恢复映射同时恢复参考态和 seam 切向量，则 Fisher 几何在该 seam 上精确保持。若只有 Fisher 数值近似保持，不能直接声称存在恢复映射。量子 Fisher 度量的近似可恢复性依赖所选单调度量，SLD Fisher 本身不是一般恢复等价的充分统计判据。这个边界与 Gao、Li、Marvian、Rouzé 对量子 Fisher 度量和可恢复性的分析一致，见 [arXiv:2302.02341](https://arxiv.org/abs/2302.02341)。

### 定义 53.5（参数化 triangle quantum network）

令 \(E=\{AB,BC,CA\}\)。对每条边给定严格正定参数化源态

\[
\omega_e(\theta_e)\succ0,
\qquad
X_e=\partial_{\theta_e}\omega_e(\theta_e).
\]

独立源乘积态为

\[
\Omega_{\boldsymbol\theta}
=
\omega_{AB}(\theta_{AB})
\otimes
\omega_{BC}(\theta_{BC})
\otimes
\omega_{CA}(\theta_{CA}).
\]

令

\[
\mathcal N:
\mathsf L(H_{AB}\otimes H_{BC}\otimes H_{CA})
\to
\mathsf L(K_A\otimes K_B\otimes K_C)
\]

为由输入重排、局部节点 CPTP 映射和输出重排组成的网络信道，并定义

\[
\rho_{\boldsymbol\theta}
=
\mathcal N(\Omega_{\boldsymbol\theta}).
\]

以下定理在所考察参数点满足
\[
\rho_{\boldsymbol\theta}\succ0
\]
时陈述。若网络输出发生秩下降，则必须把 SLD 超算子限制到输出支撑，或改用带 Moore--Penrose 伪逆的广义 Fisher 型。

### 定理 53.6（triangle 网络的源信息预算）

对任意参数速度 \(\dot{\boldsymbol\theta}\)，有

\[
\boxed{
F_Q\left(\rho_{\boldsymbol\theta};
\dot{\boldsymbol\theta}\right)
\le
\sum_{e\in E}
\dot\theta_e^{\,2}
F_Q\left(\omega_e;
\partial_{\theta_e}\omega_e\right).
}
\]

#### 证明

先计算独立源的乘积态。每个边源的局部 SLD 记为 \(L_e\)。乘积态沿参数方向的全局 SLD 为

\[
L_{\Omega}
=
\sum_{e\in E}
\dot\theta_e
\,I_{\bar e}\otimes L_e.
\]

因为

\[
\operatorname{tr}(\omega_eL_e)
=
\operatorname{tr}(X_e)=0,
\]

不同边之间的交叉项在 \(\operatorname{tr}(\Omega L_\Omega^2)\) 中消失。因此

\[
F_Q(\Omega_{\boldsymbol\theta};
\dot{\boldsymbol\theta})
=
\sum_{e\in E}
\dot\theta_e^{\,2}
F_Q(\omega_e;X_e).
\]

对网络信道 \(\mathcal N\) 应用定理 53.3，得到

\[
F_Q(\rho_{\boldsymbol\theta};
\dot{\boldsymbol\theta})
\le
F_Q(\Omega_{\boldsymbol\theta};
\dot{\boldsymbol\theta}),
\]

代入前式即得。证毕。

### 推论 53.7（FIB 三角网络的量子 Fisher 上界）

若每条边源都位于 FIB 对角 seam：

\[
\omega_e(\kappa_e)
=
\iota_\Sigma(p_{\kappa_e}),
\]

则定理 40.2 和定理 53.6 给出

\[
\boxed{
F_Q\left(\rho_{\boldsymbol\kappa};
\dot{\boldsymbol\kappa}\right)
\le
\sum_{e\in E}
\dot\kappa_e^{\,2}
\mathcal I_e(\kappa_e).
}
\]

输出态可以因为局部节点信道而变成非对角态，右侧仍然只由三个独立 FIB 源的 seam Fisher 信息决定。这是当前三角网络中最严格的信息预算：节点局部相互作用可以重新组织信息，也可以将其编码为非交换相干，但不能从独立源中凭空产生新的 SLD Fisher 信息。

### 推论 53.8（多参数 Fisher 矩阵的 Loewner 收缩）

若每条边携带参数向量，令 (J_e) 为源态 (omega_e) 的 SLD Fisher 矩阵，令 (J_{mathrm{out}}) 为网络输出态的 SLD Fisher 矩阵，则
\[
\boxed{
J_{\mathrm{out}}
\preceq
\operatorname{diag}(J_{AB},J_{BC},J_{CA}).
}
\]
对任意实参数方向 (v)，该不等式的二次型正是定理 53.6 的标量预算；有限维对称矩阵的 Loewner 序由所有实二次型比较刻画，故结论成立。该矩阵形式可直接接到多参数量子 Cramér--Rao 界。

### 推论 53.9（量子半群只给出 Fisher 单调性，不能自动给出 QCD 指数率）

若 \(T_t^\ast\) 是 Schrödinger 表示的 CPTP 半群，且 \(\rho_t=T_t^\ast(\rho_0)\)、\(X_t=T_t^\ast(X_0)\)，则

\[
F_Q(\rho_t;X_t)
\le
F_Q(\rho_0;X_0).
\]

若同时满足 §38 的 detailed balance 和 \(QCD(K)\)，则 GNS Dirichlet 能量满足

\[
\mathcal E_\sigma(T_tA)
\le
e^{-2Kt}\mathcal E_\sigma(A),
\]

但不能仅由 \(QCD(K)\) 推出

\[
F_Q(\rho_t;X_t)
\le
e^{-2Kt}F_Q(\rho_0;X_0).
\]

后一个指数 Fisher 衰减需要额外的比较不等式，将 SLD Fisher 二次型与 GNS Dirichlet 型在同一切空间上联系起来。这个区分防止把量子曲率证书误读成未经证明的物理耗散率。

### 结论 53.9（量子层的严格闭环）

在各条相应假设下，量子层具有以下有限维关系：

\[
\begin{aligned}
&\text{FIB seam}
\longrightarrow
\text{对角密度矩阵切向量}
\longrightarrow
\text{源态 SLD Fisher};\\
&\text{独立边源}
\longrightarrow
\text{乘积态 Fisher 可加性};\\
&\text{局部 triangle CPTP 网络}
\longrightarrow
\text{输出 Fisher 收缩};\\
&\text{GNS detailed balance}
\longrightarrow
\text{QCD 谱隙和 Dirichlet 衰减};\\
&\text{恢复映射存在}
\longrightarrow
\text{seam Fisher 精确保持}.
\end{aligned}
\]

其中最后一项是“信息没有逃逸”的严格判据，第一到第四项是无物理前提的有限维数学定理。要把这条链连接到引力或 RH，仍需独立构造从 QFI/QCD 数据到度量、Hamiltonian 或谱行列式的桥接映射。





### 推论 53.9（多参数 Fisher 矩阵的 Loewner 收缩）

令 \(J_{\mathrm{out}}\) 为输出态关于 \((\theta_{AB},\theta_{BC},\theta_{CA})\) 的 SLD Fisher 矩阵，令 \(J_e\) 为边源的标量 SLD Fisher 信息。则
\[
\boxed{
J_{\mathrm{out}}
\preceq
\operatorname{diag}(J_{AB},J_{BC},J_{CA}).
}
\]

#### 证明

对任意实方向 \(v=(v_{AB},v_{BC},v_{CA})\)，定理 53.6 应用于参数速度 \(v\) 给出
\[
v^\mathsf T J_{\mathrm{out}}v
\le
\sum_{e\in E}v_e^2J_e
=
v^\mathsf T\operatorname{diag}(J_e)v.
\]
有限维对称矩阵的 Loewner 序由全部实二次型比较刻画，故得结论。证毕。

该矩阵版本可以接到多参数量子 Cramér--Rao 界，但是否达到可观测性最优还取决于测量兼容性、秩条件和先验选择。2026 年的 Bayesian monotone-metric 工作把这类多参数几何推广到 Petz 单调度量，但它不改变本节的 SLD 定理边界。

## 54. 有限 Dirichlet 数据到 metric-measure/Mosco 极限的严格顺序

本节把有限 \(CD_G\)、\(QCD\) 和图 Dirichlet 数据进一步分解为四个不可互换的层次：度量测度紧性、二次型 Mosco 收敛、局部性、曲率证书的极限稳定性。

### 定义 54.1（有限图的度量测度 Dirichlet 数据）

第 \(j\) 层数据为

\[
\mathfrak D_j=(X_j,d_j,m_j,\mathcal E_j,\mathcal F_j),
\]

其中 \(X_j=V_j\) 是有限集，\(d_j\) 是外部度量，\(m_j\) 是满支撑概率测度，

\[
\mathcal F_j=\mathbb R^{X_j},
\qquad
\mathcal E_j(f)
=
\frac12\sum_{x,y\in X_j}c^{(j)}_{xy}(f(x)-f(y))^2,
\]

\[
c^{(j)}_{xy}=c^{(j)}_{yx}\ge0,\qquad c^{(j)}_{xx}=0.
\]

令

\[
(L_jf)(x)
=
\frac1{m_j(x)}\sum_yc^{(j)}_{xy}(f(y)-f(x)).
\]

则

\[
\mathcal E_j(f)=\langle f,-L_jf\rangle_{L^2(m_j)}.
\]

这里 \(d_j\) 与 \(c^{(j)}_{xy}\) 是两个独立输入。前者决定 metric-measure 紧性，后者决定 Dirichlet 形式。必须另行假设它们相容。

### 定义 54.2（统一 metric-measure 紧性和局部化证书）

称一族 \((X_j,d_j,m_j)\) 满足 \(\operatorname{MMC}(D,C_D,c_-,c_+,Q)\)，如果

\[
\operatorname{diam}(X_j,d_j)\le D,
\]

令
\[
\rho_j=\min\{d_j(x,y):x\ne y\},
\]
并且只在有效离散尺度 \(\rho_j\le r\le D\) 上要求
\[
c_-r^Q
\le m_j(B_{d_j}(x,r))
\le c_+r^Q,
\tag{54.1}
\]
其中 \(\rho_j\) 是该层的最小非零网格尺度。不能把 (54.1) 要求到 \(r<\rho_j\)，因为有限原子球的质量不会随 \(r\downarrow0\) 消失。若 \(\rho_j\) 不适合统一控制，则改用统一 covering-number 界。

\[
m_j(B_{d_j}(x,2r))
\le C_Dm_j(B_{d_j}(x,r)).
\tag{54.2}
\]

若只要求子列紧性，可以把 (54.1) 的下界换成统一 covering-number 界。若要排除塌缩，至少需要某个固定 \(r_0>0\) 满足

\[
\inf_j\inf_{x\in X_j}m_j(B_{d_j}(x,r_0))>0,
\qquad
\inf_j\operatorname{diam}(X_j,d_j)>0.
\tag{54.3}
\]

定义跳跃半径

\[
\ell_j
:=
\sup\{d_j(x,y):c^{(j)}_{xy}>0\}.
\tag{54.4}
\]

称 \(\ell_j\to0\) 为 vanishing-jump 条件。它把有限图形式的非局部边耦合限制到局部极限。若另有统一 \(L^2\)-Poincaré 条件

\[
\int_B|f-f_B|^2\,dm_j
\le
C_Pr^2\mathcal E_j(f;\lambda B),
\tag{54.5}
\]

则得到统一的局部紧性控制。

### 定理 54.3（有限图 Dirichlet 数据的 metric-measure/Mosco 子列极限）

设 \(\mathfrak D_j\) 满足：

1. 统一 covering-number 界、总质量 \(m_j(X_j)=1\) 和直径上界；
2. 存在共同紧宿主空间 \(Z\) 和等距嵌入 \(\iota_j:X_j\hookrightarrow Z\)，使得 \(\iota_j(X_j)\) 的 Hausdorff 子列收敛到 \(X\subset Z\)，且
   \[
   (\iota_j)_\#m_j\rightharpoonup m;
   \]
3. 存在共同 \(L^2\) 识别，使扩展二次型 \(\overline{\mathcal E}_j\) 满足
   \[
   u_j\rightharpoonup u
   \Longrightarrow
   \mathcal E(u)\le\liminf_j\overline{\mathcal E}_j(u_j),
   \tag{54.6}
   \]
   且每个 \(u\in D(\mathcal E)\) 有恢复序列 \(u_j\to u\) 强收敛并满足
   \[
   \limsup_j\overline{\mathcal E}_j(u_j)\le\mathcal E(u);
   \tag{54.7}
   \]
4. 有限能量子水平集在共同识别下相对紧。

则存在子列

\[
(X_j,d_j,m_j)\to(X,d,m)
\]

以 measured Gromov-Hausdorff 意义收敛，且 \(\mathcal E\) 是 \(L^2(X,m)\) 上闭、Markov、对称的 Dirichlet 形式。其非负自伴生成元 \(A\) 和热半群 \(P_t=e^{-tA}\) 满足

\[
(I+\alpha A_j)^{-1}\to(I+\alpha A)^{-1},
\qquad
P_t^{(j)}\to P_t
\]

在共同 \(L^2\) 识别下的强算子收敛。

若另外满足 \(\ell_j\to0\) 和统一 Poincaré 条件 (54.5)，则极限形式强局部。

#### 证明账本

统一 covering-number 界和质量界给出 metric-measure 子列紧性。共同宿主中的弱测度收敛给出极限测度。条件 (54.6) 和 (54.7) 是 Mosco 下极限与恢复序列，故给出闭极限二次型。闭对称 Markov 二次型对应唯一的自伴非负生成元和收缩热半群，Mosco 收敛给出 resolvent 与半群的强收敛。若支集距离大于 \(\varepsilon\)，则 \(\ell_j<\varepsilon\) 时所有跨支集边消失，有限层互能为零；利用恢复序列和下极限即得极限互能为零，故形式强局部。证毕。

因此必须按下列顺序记账：

\[
\boxed{
\text{metric-measure 紧性}
\Rightarrow
\text{空间子列极限};
\quad
\text{Mosco}
\Rightarrow
\text{形式/半群极限};
\quad
\text{vanishing jumps}
\Rightarrow
\text{强局部性}.
}
\]

### 定理 54.4（谱隙和曲率证书的极限分层）

在定理 54.3 的假设下，若存在统一 Poincaré 常数 \(\lambda_0>0\)，即

\[
\mathcal E_j(f)\ge\lambda_0\operatorname{Var}_{m_j}(f),
\tag{54.8}
\]

并且常数核恰为 \(\mathbb R\mathbf1\)，则

\[
\operatorname{gap}(A)\ge\lambda_0.
\tag{54.9}
\]

若还存在统一半群梯度证书

\[
\Gamma_j(P_t^{(j)}f)
\le
e^{-2Kt}P_t^{(j)}\Gamma_j(f),
\tag{54.10}
\]

并且 \(\Gamma_j\) 在一个共同稠密 core 上收敛到 \(\Gamma\)，则

\[
\Gamma(P_tf)\le e^{-2Kt}P_t\Gamma(f).
\tag{54.11}
\]

因此有限 \(CD_G(K,\infty)\) 的曲率下界要进入极限，除了 Mosco 和谱隙，还必须证明 \(\Gamma\) 或梯度半群不等式的收敛。点态 \(CD_G\) 本身不能替代这个稳定性假设。

### 推论 54.5（有效电阻的极限条件）

若均值零子空间上的 Green 算子满足

\[
A_j^\dagger\to A^\dagger
\tag{54.12}
\]

强收敛，且点源差分 \(b_{x_jy_j}\to b_{xy}\)，则

\[
R_{m_j}(x_j,y_j)
=
\langle b_{x_jy_j},A_j^\dagger b_{x_jy_j}\rangle
\to
\langle b_{xy},A^\dagger b_{xy}\rangle
=R_m(x,y).
\tag{54.13}
\]

Mosco 收敛、质量非塌缩或谱隙下界单独都不能推出 (54.13)。还必须证明点源识别和 Green 算子收敛。

### 命题 54.6（曲率不排除塌缩）

取固定两点集 \(X_j=\{0,1\}\)，令

\[
m_j(0)=m_j(1)=\frac12,\qquad c^{(j)}_{01}=c^{(j)}_{10}=\frac12,
\]

但令 \(d_j(0,1)=j^{-1}\)。直接计算得

\[
\Gamma_2(f)=2\Gamma(f),
\]

所以每一层满足 \(CD_G(2,\infty)\)，且 Dirichlet 形式、谱隙和半群完全不变。然而

\[
(X_j,d_j,m_j)\to(\{\ast\},0,\delta_\ast)
\]

在 measured Gromov-Hausdorff 意义下塌缩到一点。因此

\[
CD_G(K,\infty)+\text{统一谱隙}
\not\Rightarrow
\text{非塌缩极限}.
\]

排除该反例需要 (54.3) 或等价的统一体积和直径下界。

### 命题 54.7（Mosco 形式极限不决定 metric 几何）

在固定 \(X=\{0,1\}\) 上取恒定形式 \(\mathcal E_j=\mathcal E\)，故 Mosco 收敛恒等成立；再令

\[
d_{2j}(0,1)=1,\qquad d_{2j+1}(0,1)=2.
\]

形式有唯一极限，度量没有全序列极限。因此

\[
\text{Mosco 收敛}
\not\Rightarrow
\text{metric-measure 收敛}.
\]

### 命题 54.8（谱隙不决定局部连续场）

令 \(X_j=\{1,\ldots,j\}\)，取均匀测度和

\[
L_jf=\bar f-f.
\]

则所有非零谱值恒为 \(1\)，但将点嵌入 \([0,1]\) 后边跳跃长度不趋于零，且

\[
\mathcal E_j(f)=\operatorname{Var}_{m_j}(f)
\to
\operatorname{Var}_{[0,1]}(f),
\]

其极限是非局部形式，不是

\[
\int_0^1|f'(x)|^2\,dx.
\]

所以统一谱隙不能替代 vanishing-jump 或非局部质量消失条件。

### 定义 54.9（量子度量极限的附加数据）

有限量子层

\[
\mathfrak Q_j=(\mathcal A_j,\sigma_j,\mathcal L_j)
\]

中的 \(QCD(K)\) 只约束 GNS Hilbert 空间中的二次型。要得到 metric-measure 极限，还必须给出量子 Lipschitz 半范数 \(\operatorname{Lip}_j\)，或状态空间距离

\[
d_j(\varphi,\psi)
=
\sup_{\operatorname{Lip}_j(a)\le1}
|\varphi(a)-\psi(a)|,
\]

并证明归一化 Lipschitz 球统一全有界、状态空间具有 quantum-GH 子列紧性、GNS resolvent 或量子 Dirichlet 形式满足 Mosco 条件，以及半范数与极限测度相容。没有这些附加数据，\(QCD(K)\) 只能给出非交换 Hilbert 空间的谱稳定性，不能推出 metric-measure 极限。

### 定理 54.10（四层桥接的必要充分结构）

在共同宿主空间框架中，要得到一个非塌缩、局部、带稳定谱隙的 metric-measure Dirichlet 极限，所需的可检验结构可分为：

\[
\boxed{
\begin{array}{ll}
\mathrm{(G)}&\text{统一 metric-measure 紧性和非塌缩};\\
\mathrm{(M)}&\text{共同 }L^2\text{ 识别下的 Mosco 下极限和恢复序列};\\
\mathrm{(L)}&\text{vanishing jumps 与局部 Poincaré 控制};\\
\mathrm{(K)}&\text{\(\Gamma\)/梯度不等式的稳定收敛}.
\end{array}}
\]

\((G)+(M)\) 给出空间和闭 Dirichlet 形式的子列极限；\((G)+(M)+(L)\) 给出强局部形式；加入 \((K)\) 才能把有限曲率证书传到极限。若再要求有效电阻收敛，还需 Green 算子和点源的识别条件。

对应的严格管线是

\[
\boxed{
\begin{aligned}
&\text{有限 FIB/图/量子数据}
\xrightarrow{\mathrm{(G)}}
\text{metric-measure 子列极限}\\
&\xrightarrow{\mathrm{(M)}}
\text{闭 Dirichlet 形式、resolvent、热半群}\\
&\xrightarrow{\mathrm{(L)}}
\text{强局部极限}\\
&\xrightarrow{\mathrm{(K)}}
\text{曲率梯度不等式或 RCD 型候选证书}.
\end{aligned}}
\]

Aobo Chen 的 2024/2026 工作在 pointed Gromov-Hausdorff 收敛、统一体积增长和统一热核估计下构造极限度量测度空间上的保守强局部正则对称 Dirichlet 形式，并沿子列证明 Mosco 收敛；其假设正好显示空间收敛、体积控制、热核控制和非退化尺度必须分别记账。参见 A. Chen, *Stability of heat kernel bounds under pointed Gromov--Hausdorff convergence*, arXiv:2411.19047。

Inagaki 2025 对具有 Ricci 下界、体积下界和直径上界的流形上的随机图 Laplacian 建立谱收敛，并延伸到非塌缩 Ricci 极限空间。该结果支持本节的分层原则：图谱或有限 Dirichlet 数据要取得连续几何解释，必须同时记录曲率、体积非塌缩、尺度和谱识别条件。参见 M. Inagaki, *Spectral convergence of graph Laplacians with Ricci curvature bounds and in non-collapsed Ricci limit spaces*, arXiv:2506.07427。



---

## 55. 可见压缩缺陷与隐藏场记忆

前述三维读出和统一场候选必须先通过有限状态可观测性检验。有限读出若没有满足 lumpability，不能被当作闭合 Markov 场变量。

### 定义 55.1（可观测子空间与压缩半群）

令 \(S\) 为有限状态集，令 \(\pi\) 为满支撑平稳分布，令 \(L\) 为满足
\[
\langle f,Lg\rangle_\pi=\langle Lf,g\rangle_\pi,\qquad
\sum_x\pi(x)Lg(x)=0
\]
的可逆 Markov 生成元。给定读出 \(q:S\to Y\)，定义
\[
\mathcal H_q=\{f:S\to\mathbb R:f=\bar f\circ q\},
\]
令 \(P:L^2(\pi)\to\mathcal H_q\) 为条件期望正交投影，\(S_t=e^{tL}\)，并令
\[
T_t=P S_t\big|_{\mathcal H_q}.
\]
称 \(q\) 强 lumpable，当且仅当
\[
L\mathcal H_q\subseteq\mathcal H_q,
\]
等价于 \((I-P)LP=0\)。

### 定理 55.2（可逆压缩的精确记忆缺陷）

对 \(f\in\mathcal H_q\) 和 \(t\ge0\)，
\[
\boxed{
\langle f,(T_{2t}-T_t^2)f\rangle_\pi
=
\|(I-P)S_t f\|_\pi^2.
}
\]
并且
\[
\lim_{t\downarrow0}
\frac{\langle f,(T_{2t}-T_t^2)f\rangle_\pi}{t^2}
=
\|(I-P)Lf\|_\pi^2.
\]
因此 \(q\) 强 lumpable 当且仅当所有 \(f\in\mathcal H_q\) 满足 \((I-P)Lf=0\)。

#### 证明

利用 \(f=Pf\)、\(P=P^\ast=P^2\) 和 \(S_t=S_t^\ast\)，
\[
\begin{aligned}
\langle f,T_{2t}f-T_t^2f\rangle_\pi
&=\langle f,PS_t(I-P)S_tf\rangle_\pi\\
&=\langle S_tf,(I-P)S_tf\rangle_\pi\\
&=\|(I-P)S_tf\|_\pi^2.
\end{aligned}
\]
有限维矩阵指数给出 \(S_tf=f+tLf+o(t)\)，而 \((I-P)f=0\)，故
\[
(I-P)S_tf=t(I-P)Lf+o(t).
\]
除以 \(t^2\) 取极限即得。证毕。

### 推论 55.3（dev 有限素因子盒反例）

在 dev 的有限素因子盒 \(s=(a,b,c,k)\) 上，读出
\[
q(s)=(u,v,w)=(a+k,b,c+k)
\]
忘掉隐藏坐标 \(k\)。对 dev 的 7-move 生成元，取
\[
s=(0,0,C-1,1),\qquad t=(1,0,C,0),
\]
则 \(q(s)=q(t)=(1,0,C)\)，但对 \(g=\mathbf 1_{\{(1,0,C+1)\}}\) 有
\[
L(g\circ q)(s)=1/5,\qquad L(g\circ q)(t)=0.
\]
因此不存在只依赖 \(q\) 的生成元 \(G\) 使 \(L(g\circ q)=G(g)\circ q\) 在整个盒上成立。若 \(\pi(s)\propto1/(2^a3^b5^c7^k)\)，则对 \(f=\mathbf1_{\{q=(1,0,2)\}}\) 的隐藏纤维，二阶缺陷中含严格正项
\[
\frac1{425Z}=\frac{21}{34255}>0.
\]
这说明三维 \(q\) 的观察路径存在不可消去的 hidden-field memory。来源：[dev DivisorAssociationFiber](https://github.com/the-omega-institute/trureturing/blob/dev/Blueprint/D5/S3/Arith/GoldenResource/DivisorAssociationFiber.md)，commit 41a47f1c3d，merge #15832。

### 场桥接边界

若要把 \(q\) 作为静态场的闭合坐标，必须额外证明 \((I-P)LP=0\)，或显式保留隐藏状态并使用记忆核
\[
K_t=P L(I-P)e^{t(I-P)L}(I-P)L P.
\]
没有该条件，\(q\)-层只能是观测量，不是闭合场本身。

## 56. 有限可见 Markov 层的密度完备性

### 定义 56.1（Fibonacci 开路径图与调和边泛函）

令
\[
B_n=\{b\in\{0,1\}^n:b_jb_{j+1}=0\},
\]
令 \(\Gamma_n\) 的边为合法 Hamming 距离一的词对。定义
\[
h(s,t)=
\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}
\]
以及
\[
\Phi_n(\mu)=\sum_{\{b,c\}\in E(\Gamma_n)}h(\mu(b),\mu(c)),\quad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\quad
c_\ast=\lim_{n\to\infty}\kappa_n/n.
\]

### 定义 56.2（有限可见阶密度）

令 \(Q\) 是
\[
X=\{x\in\{0,1\}^{\mathbb Z}:x_jx_{j+1}=0\}
\]
上的平稳律，且可见 Markov 阶数不超过 \(m\)。令 \(Q_n\) 为长度 \(n\) cylinder 分布，定义
\[
D_m(Q)=
\sum_{\substack{a,v\in B_m\\a_m=v_1=0}}
h\!\left(Q_{2m+1}(a0v),Q_{2m+1}(a1v)\right).
\]

### 定理 56.3（内部坐标的共同因子分组）

对 \(n\ge2m+1\)，
\[
\Phi_n(Q_n)=(n-2m)D_m(Q)+E_n,\qquad0\le E_n\le m/2.
\]
对所有 \(n\ge1\)，
\[
|\Phi_n(Q_n)-nD_m(Q)|\le m/2.
\]
因此 \(d(Q)=\lim_n\Phi_n(Q_n)/n\) 存在且 \(d(Q)=D_m(Q)\)。

#### 证明

对内部坐标 \(i=m+1,\ldots,n-m\)，成对完整词只在长度 \(m+1\) 的中心窗口改变，其余转移因子给共同非负因子 \(C_\omega\)。由 \(h\) 的正齐次性，
\[
\sum_\omega h(C_\omega A_0,C_\omega A_1)
=h\!\left(\sum_\omega C_\omega A_0,\sum_\omega C_\omega A_1\right),
\]
而两个和正是 \(Q_{2m+1}(a0v)\) 和 \(Q_{2m+1}(a1v)\)。内部坐标共有 \(n-2m\) 个，端点边贡献由 \(0\le h\le1/4\) 控制，得到余项界。零 cylinder 质量也可直接在非负质量上分组。证毕。

### 定理 56.4（有限可见记忆回收全局密度）

\[
\boxed{
c_\ast=\sup\{d(Q):m<\infty,\ Q\text{ 为允许的有限可见 Markov 阶平稳律}\}.
}
\]

#### 证明边界

上界来自 \(\Phi_n(Q_n)\le\kappa_n\)。下界使用 dev 的 guarded-payload 构造：给定有限层近极值 \(\mu\) 和 \(\varepsilon>0\)，构造固定有限可见阶数且 full-support 的平稳 \(Q\)，使 \(d(Q)>c_\ast-\varepsilon\)。因此全局密度近极值可以由某个有限可见记忆层回收。该步骤是有限概率和有限图论，不是量子、连续时空或 RH 定理。来源：[FIB LEGAL EDGE LOAD FINITE VISIBLE MEMORY COMPLETENESS](https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_COMPLETENESS.md)，dev commit 93f4ac5279，merge #15837。

## 57. 三维读出、隐藏源纤维与两种不相容的尺度

### 定义 57.1（有限源族与三维观测）

令 \(L_h=\{L,R\}^h\)，\(m=2^h\)，令 \(\omega:L_h\to\{0,1\}\)。按 dev 的 CE/source contract 构造
\[
\mathcal F_h=\{\nu_{h,\omega}:\omega\in\{0,1\}^{L_h}\},\qquad
|\mathcal F_h|=2^{2^h}.
\]
每个源具有相同 retained input、相同 native \(Q\)-row，并且三分量读出相同，例如 \(q(\nu_{h,\omega})=(0,0,0)\)，但 complete subtree valuation 两两不同。

### 定理 57.2（地址深度的固定维度排除）

设地址超度量 \(d_h^A\) 对首个不同原始叶地址深度赋值，且同一深度最小非零距离为 \(s_h>0\)。若存在固定 \(k\)、\(0<c\le C<\infty\) 及 \(\Psi_h:\mathcal F_h\to\mathbb R^k\) 使
\[
c\,d_h^A(u,v)\le\|\Psi_h(u)-\Psi_h(v)\|\le C\,d_h^A(u,v)
\]
对全部 \(h,u,v\) 成立，则
\[
2^{2^h}=|\mathcal F_h|\le(1+2C/c)^k,
\]
矛盾于 \(h\to\infty\)。

#### 证明

固定一个源后，所有像点位于半径 \(Cs_h\) 的球内，且任意两点距离至少 \(cs_h\)。以半径 \(cs_h/2\) 的球围绕各像点，这些球两两不交且包含于半径 \(Cs_h+cs_h/2\) 的球内。比较 \(k\)-维体积得到所示界。证毕。

### 定义 57.3（完整事件时钟与一维代码）

按 full-event trace 对叶按字典序编号 \(p_1,\ldots,p_m\)，定义
\[
e_0(1)=1,\quad
e_{r+1}(j)=
\begin{cases}1+e_r(j),&j\le2^r,\\
4\cdot2^r-1+e_r(j-2^r),&j>2^r,\end{cases}
\quad n_h(j)=2+e_h(j).
\]
对 \(\omega\ne\omega'\)，令 \(j(\omega,\omega')\) 为最小不同叶索引，定义
\[
d_h^E(\omega,\omega')=3^{-n_h(j)},\qquad
Z_h^E(\omega)=\sum_{j=1}^m2\omega(p_j)3^{-n_h(j)}.
\]
则
\[
d_h^E(\omega,\omega')\le|Z_h^E(\omega)-Z_h^E(\omega')|\le3d_h^E(\omega,\omega'),
\]
并且 \(n_h(1)=h+3\)、\(n_h(m)=4m-h-1\)。

### 定理 57.4（地址尺度与事件尺度不可对应）

端点事件距离与地址尺度的比值为 \(3^{4m-2h-4}\)。故不存在统一常数 \(c,C\) 与正的层内重标定 \(a_h,b_h\)，使
\[
c\,a_hd_h^A\le b_hd_h^E\le C\,a_hd_h^A
\]
对全部 \(h\) 和全部源对成立。故一维事件编码不等于三维地址几何的 faithful representation。

#### 证明边界

若统一双 Lipschitz 常数存在，端点距离比值必须在 \(h\) 上有界，但 \(m=2^h\) 时上式无界。证毕。

这些命题只证明给定 finite source family 上 \(q\) 是高度非注入的 readout，且 hidden fiber 随 \(h\) 指数增长。它们不推出物理空间维数下界，也不否定另一个与物理度量相容的三维表示。若要把 \(q\) 或 \(Z^E\) 解释成场的几何坐标，仍必须另给 metric、measure、operator domain、clock 和 source-to-geometry correspondence。来源：[FIB ATOM RECURSIVE HOLOGRAPHIC BOUNDARY GEOMETRY CONTINUATION III §90](https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md)，dev commits 205ab4d1ce/3779de5fbb，merge #15838。

## 58. 有界语法层上的统一残差观测反射

### 定义 58.1（有限残差语法与统一分离元）

令 \(\operatorname{MixedExpr}(\mathrm{Fin}\ m)\) 由有限 native ground、带 decoration 的共享 residual 名称及有序 pair 生成。令 weight 为 ground/pair 的 native constructor mass，decoration 为最大 residual exponent。对给定 \(m,M,d\)，令
\[
\operatorname{separator}(m,M,d):\mathrm{Fin}\ m\to\mathrm{Source}
\]
为按 native substitution iterates 构造的有限 tuple。

### 定理 58.2（bounded identity reflection）

若 \(A,B\) 的 weight 不超过 \(M\)，decoration 不超过 \(d\)，则
\[
\operatorname{eval}(\operatorname{separator}(m,M,d),A)
=
\operatorname{eval}(\operatorname{separator}(m,M,d),B)
\]
当且仅当
\[
\forall z:\mathrm{Fin}\ m\to\mathrm{Source},\quad
\operatorname{eval}(z,A)=\operatorname{eval}(z,B).
\]
本陈述对应来源中的 NativeUniformResidualRealization.bounded_identity_reflection（commit cdb23e4374）；来源链接见定理 58.3。

### 定理 58.3（rank instantiation 与统一有限分离）

对 RankedExpr(k,m)，instantiation 保持 native evaluation。对任意有限 pair-list \(L\)，同一个 uniformSeparator(L) 对所有无界 rank vectors \(n\) 同时满足：每个 pair 在 separator 下相等，当且仅当该 pair 在全部 residual valuations \(z\) 下相等。若列表中每个 pair 各自存在 residual valuation 使其不等，则同一个 separator 同时使所有 pair 不等。

对应来源条目为 instantiate_eval、uniform_residual_reflection、simultaneous_completion。上述陈述限于所指定的有界语法类；其中对无界 rank vectors 的量化不等于覆盖所有 source 或无限 rank 表达式，也不涉及物理读权限、资源最优性或 RH。来源：[Native Uniform Residual Realization](https://github.com/the-omega-institute/trureturing/blob/dev/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization.md)，dev commit cdb23e4374。

## 59. 最新外部研究锚点与管线位置

本节只记录外部研究对接口设计的支持，不把其模型假设转写为 Auric FIB 内部定理。

1. Zhang、Yamagata、Suzuki 的 2026 工作将 Petz 单调度量用于多参数 Bayesian 量子估计，支持把 §49 的 SLD 特例扩展为一族单调量子度量，但不替代 §49 的有限维证明，也不证明 FIB 参数是物理参数。参见 [arXiv:2607.01685](https://arxiv.org/abs/2607.01685)。

2. Movilla Miangolarra、Sabbagh、Kolchinsky 的 2026 工作把详细平衡 Markov 链和耗散 Lindblad 动力学放入 Wasserstein-2 自由能梯度流框架，并讨论含 Hamiltonian 项的广义度量。它为 §50 的 metric-measure 数据提供候选构造，但必须先给出状态空间、mobility、参考态和极限识别，不能从 \(QCD(K)\) 自动推出 Wasserstein 几何。参见 [arXiv:2606.00698](https://arxiv.org/abs/2606.00698)。

3. Inagaki 的 2025 结果在 Ricci 下界、体积下界、直径上界和非塌缩条件下建立随机图 Laplacian 的谱收敛，支持 §50 中 (G)、(K) 和非塌缩条件分开记录。参见 [arXiv:2506.07427](https://arxiv.org/abs/2506.07427)。

4. Chen 关于 pointed Gromov-Hausdorff 收敛下热核界稳定性的工作构造极限 Dirichlet 形式并沿子列得到 Mosco 收敛，支持 §50 的“空间紧性先于形式极限”顺序，但其假设不能被有限 FIB 数据默认满足。参见 [arXiv:2411.19047](https://arxiv.org/abs/2411.19047)。

因此，最新研究支持接口选择和假设分层，不能替代 Auric FIB 自己的有限层证明或 RH 谱识别定理。


## 60. 线性观察的自治闭合充要条件

### 定理 60.1（有限维线性观察的自治闭合）

令 \(V,W\) 为有限维实向量空间，令 \(P:V\to W\) 为满射，令 \(L:V\to V\) 为线性生成元。存在 \(G:W\to W\) 使
\[
P e^{tL}=e^{tG}P\qquad\text{对所有 }t\ge0
\]
当且仅当
\[
L(\ker P)\subseteq\ker P.
\]

#### 证明

若半群恒等式成立，取 \(v\in\ker P\)，则 \(P e^{tL}v=0\)。在 \(t=0\) 求导得到 \(PLv=0\)，即 \(Lv\in\ker P\)。

反之，若 \(L(\ker P)\subseteq\ker P\)，定义
\[
G(Pv)=PLv.
\]
若 \(Pv=Pv'\)，则 \(v-v'\in\ker P\)，故 \(P L(v-v')=0\)，所以 \(G\) 良定义。于是 \(PL=GP\)，逐项比较指数幂级数得到
\[
P e^{tL}=e^{tG}P.
\]
证毕。

### 推论 60.2（FIB 隐藏核与静态场）

离散更新族 \(F_a:V\to V\) 的观察商 \(P\) 具有自治闭合，当且仅当每个 \(F_a\) 保持 \(\ker P\) 所定义的等价关系；线性生成元版本是
\[
L(\ker P)\subseteq\ker P.
\]
因此 FIB 或三维 \(q\) 只有在 hidden kernel 对全部 transport、CPTP 或 Hamiltonian 更新不变时，才形成自治静态场。否则精确约化动力学必含记忆项。定理 51.2 的 \(t^2\) 压缩缺陷是这一充要条件失败的有限可计算证书。

该定理只涉及有限维线性代数和矩阵指数。它不把 \(P\) 解释为物理测量，也不推出引力或 RH。相关行为商的最大不动点版本见 dev 的 [COMPUTATIONAL BEHAVIOR REPRESENTATION THEORY](https://github.com/the-omega-institute/trureturing/blob/dev/docs/develop/theory/COMPUTATIONAL_BEHAVIOR_REPRESENTATION_THEORY.md)。


## 61. 五模式预测律几何及其适用范围

### 定义 61.1（预测律场）

对五模式载体 \(S=\{0,1,2,3,4\}\)，不把静态向量 \(p\in\Delta(S)\) 直接当作完整状态，而定义其 future-word profile
\[
\mathcal P_H(p)=\operatorname{Law}_p(X_1,\ldots,X_H)
\]
以及全时 profile \(\mathcal P_\infty(p)\)，其中允许性、startup 和 mixture law 均按 dev 的 Fin5 source/admissibility contract 给定。预测律场的等价关系是
\[
p\sim_{\mathrm{pred}}q
\iff
\mathcal P_\infty(p)=\mathcal P_\infty(q).
\]

### 定理 61.2（五模式的有限预测几何）

在该明确的 Fin5 source/admissibility 模型中，来源
[FiveModePredictiveLawGeometry](https://github.com/the-omega-institute/trureturing/blob/dev/Blueprint/D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.md)
给出的数学陈述为：

1. 对 coherent mixture law，有限 horizon 的总变差距离满足
   \[
   \operatorname{TV}_H
   =
   |x-z|\bigl(1-\min(a,b)^H\bigr),
   \]
   且 profileDistance 等于 \(|x-z|\)；
2. 不同 pure states 具有统一正分离下界 \(\kappa\)；
3. startup laws 的距离公式成立，startup length 映射是单射；
4. cutoff 满足
   \[
   N_2=
   \left\lceil
   \frac{\log((1-2\varepsilon)/(2\varepsilon))}
        {|\log\theta|}
   \right\rceil
   \]
   并有指数衰减；
5. 长度上限 \(L\ge2\) 时 exact predictive classes 有 \(L+5\) 个，加入 empty boundary 后为 \(L+6\)；
6. postread/initialized predictive-law image 可数且无限；
7. 总包装定理 five_mode_predictive_geometry 成立。

### 推论 61.3（五向量不是自动的完整动态场）

即使静态五态向量 \(p\) 只有五个坐标，预测律商
\[
\Delta(S)/{\sim_{\mathrm{pred}}}
\]
在该模型中可以具有可数无限多个类。因此
\[
\text{静态五向量}
\ne
\text{完整动态状态}
\]
除非另行证明读出对全部 future profiles 是完备的。该推论与定理 48.2 的最大预测商、定理 55.2 的 hidden-memory 缺陷以及定理 60.1 的自治闭合条件相接。

这些结论限于指定 Fin5 source/admissibility 条件，不能外推到一般五态量子网络、物理能级、引力或 RH。它们为“能级”提供的严格对象只是预测律商上的距离和有限截断谱，不是物理 Hamiltonian 能级。


---

## 62. 三层维数账本与不可约三体算术场

“二生三，三开始有无限可能”的数学解释需要把线性载体、概率流形和可见商分开。对未归一化五态向量空间 \(E=\mathbb R^\Sigma\)，可见投影 \(P:E\to\mathbb R^3\) 满秩，且

\[
\ker P=\operatorname{span}\{e_0,d\},
\qquad
\dim E=2+3=5.
\tag{62.1}
\]

这里 \(e_0\) 是离开总质量归一化超平面的方向，\(d\) 才是归一化概率场内部的真实隐藏纤维方向。令

\[
T_0=\left\{v\in\mathbb R^\Sigma:\sum_sv_s=0\right\}.
\]

则

\[
\dim T_0=4,\qquad
\ker(P|_{T_0})=\mathbb R d,\qquad
\dim\operatorname{im}(P|_{T_0})=3.
\tag{62.2}
\]

同一结构的严格维数账本是

\[
\underbrace{5}_{\text{未归一化坐标}}
\longrightarrow
\underbrace{4}_{\text{概率流形切空间}}
\longrightarrow
\underbrace{3}_{\text{可见投影}},
\]

同时保留一个真实的归一化隐藏方向。因此 \(2+3=5\) 是线性载体的秩零化关系，不是说概率单纯形本身有五个内禀维数。

### 定义 62.1（不可约三体局部势）

对三点模式 \(H\) 的任意子集 \(J\subseteq H\)，令

\[
\phi_J(\ell)
=
\log\frac{1-\nu_J(\ell)/\ell}
{(1-1/\ell)^{|J|}},
\qquad
\nu_J(\ell)=|\{-h\bmod\ell:h\in J\}|.
\]

用子集格 Möbius 反演定义三体不可约势

\[
I_H^{(3)}(\ell)
=
\sum_{J\subseteq H}
(-1)^{3-|J|}\phi_J(\ell).
\tag{62.3}
\]

由于空集和单点的归一化势为零，这等于三元局部势减去三个二元局部势。它量化三胞胎相互作用中不能由成对约束解释的部分。

### 命题 62.2（高阶尾项消去）

若 \(\ell\) 不整除任意偏移差，则对 \(j=|J|\) 有

\[
\phi_j(\ell)
=
-\sum_{m\ge2}
\frac{j^m-j}{m\ell^m}.
\tag{62.4}
\]

在 \(I_H^{(3)}\) 中，\(\ell^{-2}\) 项精确抵消，因而

\[
I_H^{(3)}(\ell)=O(\ell^{-3}).
\tag{62.5}
\]

证明：\(\ell^{-2}\) 项的系数是关于 \(j\) 的二次多项式；对三点子集作三阶有限差分后消失。总三元势通常只有 \(O(\ell^{-2})\)，所以不可约三体尾项具有更快衰减。证毕。

以 \(H=\{0,2,6\}\) 为例，异常模给出

\[
I_H^{(3)}(2)=-\log2,
\qquad
I_H^{(3)}(3)=\log\frac43,
\]

而 \(\ell\ge5\) 的尾项具有 \(O(\ell^{-3})\) 衰减。于是可以定义真正的三体场能量

\[
\mathscr E_{\rm 3body}(H)
=
\sum_{\ell}w_\ell\left|I_H^{(3)}(\ell)\right|^2,
\qquad
w_\ell\ge0,
\tag{62.6}
\]

或者沿素数尺度 \(Q_j=\prod_{i\le j}p_i\) 定义势轨迹

\[
V_j^{(3)}(H)=\sum_{i\le j}I_H^{(3)}(p_i),
\qquad
K_j^{(3)}=V_{j+1}^{(3)}-2V_j^{(3)}+V_{j-1}^{(3)}.
\tag{62.7}
\]

这些量精确表达了“第三阶出现新的自由度”：它们是三点模式超出所有 pairwise 局部势的不可约部分。不过这仍是 CRT 局部场，不是时空曲率，也不自动产生 zeta 零点。

### 有限数据边界

固定 \(N,Q,H\) 后，\(\mu_{H,q}^N\)、\(D_{H,q}^2\)、\(\Theta_{q'\to q}\)、\(V_j\) 和 \(K_j\) 只依赖有限区间内的素数指示值及有限剩余类坐标。任何在该截断之外修改的二值序列都保持这些量不变。因此它们是候选算术不变量和可复核数值证据，不能单独蕴含一个关于所有整数的 RH 命题。

要跨过这个边界，至少需要对所有模式、所有尺度建立统一控制，或者构造 prime-weighted 自伴算子并证明包含 Archimedean 因子的全局正规化行列式/迹公式。不可约三体能量提供了新的局部接口，但没有替代这个全局门槛。


---

## 63. RH 与四维概率场的严格接口

“RH 和 4 很接近”可以被拆成四个不同的数学事实。它们共享概率、正定性、对称和谱结构，但逻辑强度不同。

### 63.1 四维概率场与三维固定子流形

五态概率单纯形内点

\[
\Delta^\circ_5
=
\left\{
p_s>0:\sum_{s\in\Sigma}p_s=1
\right\}
\]

的仿射维数是 \(4\)。Fisher 度量平方根嵌入

\[
h(p)=(2\sqrt{p_s})_{s\in\Sigma}
\]

把它等距嵌入半径 \(2\) 的正球面片 \(S^4_+(2)\)，因为

\[
\sum_sh_s^2=4,
\qquad
\langle dh_p(a),dh_p(b)\rangle
=
\sum_s\frac{a_sb_s}{p_s}
=
g_p^F(a,b).
\tag{63.1}
\]

令 \(\tau\) 交换 \(2\) 与 \(5\)，固定 \(0,3,25\)。则

\[
\operatorname{Fix}(\tau)
=
\{p\in\Delta^\circ_5:p_2=p_5\}
\]

是三维子流形。反对称法向坐标可以取

\[
\eta(p)=\frac12\log\frac{p_2}{p_5},
\qquad
\eta(\tau p)=-\eta(p).
\tag{63.2}
\]

所以这里存在一个严格的

\[
4\text{ 维场}
\longrightarrow
3\text{ 维固定/可见流形}
+
1\text{ 维镜像法向缺陷}
\]

分解。当前 FIB 投影核 \(d\) 是镜像偶的隐藏纤维，不能直接当作这里的奇法向 \(\eta\)。后者是一个新的功能方程候选坐标。

### 63.2 RH 的 Poisson 概率场与 \(1/4\)

令

\[
\mathbb H_{1/2}=\{s:\operatorname{Re}s>1/2\},
\qquad
B=\{1/2+it:t\in\mathbb R\},
\]

并在半平面内取点 \(s_0=1\)。其边界 Poisson 概率测度为

\[
\mu_C(dt)
=
\frac{dt}{2\pi(t^2+1/4)}.
\tag{63.3}
\]

这里的 \(1/4\) 是点 \(s_0\) 到临界边界的距离平方 \((1/2)^2\)。令

\[
X(t)=\log|\zeta(1/2+it)|.
\]

Balazard–Saias–Yor 等价式可写成一个 Cauchy 概率场的缺陷能量：

\[
\mathcal D_{\rm RH}
=
\int_{\mathbb R}X(t)\,\mu_C(dt)
=
\sum_{\rho:\operatorname{Re}\rho>1/2}
\log\left|\frac{\rho}{1-\rho}\right|.
\tag{63.4}
\]

对 \(\rho=\frac12+\delta+i\gamma\)，

\[
\log\left|\frac{\rho}{1-\rho}\right|
=
\frac12\log
\frac{\gamma^2+\delta^2+\frac14+\delta}
{\gamma^2+\delta^2+\frac14-\delta}
=
\operatorname{artanh}
\frac{\delta}{\gamma^2+\delta^2+\frac14}
\ge0.
\tag{63.5}
\]

因此

\[
\mathcal D_{\rm RH}=0
\quad\Longleftrightarrow\quad
\delta=0\ \text{for every nontrivial zero}
\quad\Longleftrightarrow\quad
\mathrm{RH}.
\tag{63.6}
\]

这是真正的概率空间关系：RH 是 Poisson/Cauchy 加权零点法向缺陷的完全消失。Bui、Lester 和 Milinovich 对这一等价式及截断积分进行了研究，参见 [arXiv:1306.0856](https://arxiv.org/abs/1306.0856)。

### 63.3 RH 零点的单位圆坐标

对零点 \(\rho\) 定义

\[
z_\rho=1-\frac1\rho.
\]

功能方程反射 \(\rho\mapsto1-\overline\rho\) 对应

\[
z_\rho\mapsto\frac1{\overline{z_\rho}},
\]

而共轭对应 \(z_\rho\mapsto\overline{z_\rho}\)。写

\[
z_\rho=e^{u_\rho+i\theta_\rho},
\qquad
u_\rho=\log|z_\rho|.
\]

则

\[
\operatorname{Re}\rho=\frac12
\quad\Longleftrightarrow\quad
|z_\rho|=1
\quad\Longleftrightarrow\quad
u_\rho=0.
\tag{63.7}
\]

因此 RH 的几何意义是：所有零点的像都落在反射固定的单位圆上，\(u_\rho\) 是法向偏离量。这个结构与 (63.2) 同型：

\[
\eta\longleftrightarrow u_\rho,
\qquad
\tau:\eta\mapsto-\eta
\longleftrightarrow
u_\rho\mapsto-u_\rho.
\]

### 定理 63.4（条件性的场到 RH 固定子桥）

设 \(\mathcal Z\) 是非平凡零点多重集，存在映射

\[
\Phi:\mathcal Z\to\Delta^\circ_5
\]

满足：

\[
\Phi(1-\overline\rho)=\tau\Phi(\rho),
\tag{63.8}
\]

以及

\[
\eta(\Phi(\rho))
=
\log\left|1-\frac1\rho\right|.
\tag{63.9}
\]

则

\[
\mathrm{RH}
\quad\Longleftrightarrow\quad
\Phi(\mathcal Z)\subseteq\operatorname{Fix}(\tau).
\tag{63.10}
\]

证明：由 (63.7)，RH 等价于所有右端项为零；由 (63.2)，\(\eta=0\) 等价于 \(p_2=p_5\)，即属于 \(\operatorname{Fix}(\tau)\)。证毕。

该条件定理仍缺少从已有的 FIB、prime local field 或 Weil 二次型自然构造 $\Phi$ 的桥接；任意指定映射并不提供这种来源关系。

### 63.5 四阶矩是同一个场的另一种读出

令

\[
M_4(T)
=
\frac1T\int_0^T
|\zeta(1/2+it)|^4\,dt.
\]

Ingham 的经典结果给出

\[
M_4(T)
=
\frac{1}{2\pi^2}(\log T)^4
+
O((\log T)^3).
\tag{63.11}
\]

对固定 \(\sigma>1/2\)，长平均满足

\[
\lim_{T\to\infty}
\frac1T\int_0^T|\zeta(\sigma+it)|^4dt
=
\frac{\zeta(2\sigma)^4}{\zeta(4\sigma)}.
\tag{63.12}
\]

这里的四来自四腿乘法约束 \(mk=n\ell\)，本质是一个四阶相关或乘法能量。它与 (63.4) 共享随机场

\[
X(t)=\log|\zeta(1/2+it)|,
\]

但读出不同：

\[
\mathcal D_{\rm RH}
=
\mathbb E_{\mu_C}[X],
\qquad
M_4(T)
=
\mathbb E_{\lambda_T}[e^{4X}],
\]

其中 \(\lambda_T\) 是区间上的均匀概率测度。前者是 RH 等价的零缺陷泛函，后者是四阶统计量，不能单独推出 RH。

### 63.6 完成 zeta 的概率特征函数接口

Nakamura 定义

\[
\Xi_\sigma(t)
=
\frac{\xi(\sigma-it)}{\xi(\sigma)}.
\]

他证明 \(\Xi_\sigma\) 对任意实 \(\sigma\) 都是某个概率分布的特征函数，并证明 RH 等价于对所有 \(1/2<\sigma<1\)，这些特征函数具有其定义的 pretended-infinitely-divisible 结构。参见 [arXiv:1504.03438](https://arxiv.org/abs/1504.03438)。

这给出了比“观察到概率相似”更强的目标：

\[
\text{FIB 场}
\longrightarrow
\text{正定特征函数}
\longrightarrow
\text{无限可分性}
\longrightarrow
\mathrm{RH}.
\]

有限 Fisher 场、正定二次型、粗粒化和局部素数场尚未给出有限截断的 characteristic-function field；该桥还依赖其 Toeplitz moment matrix 的半正定性，以及截断到全局 $\Xi_\sigma$ 的极限关系。

### 63.7 与 Hilbert–Pólya 的 Cayley 连接

如果 \(D=D^*\) 是候选自伴算子，定义

\[
U=(D-iI)(D+iI)^{-1}.
\]

则 \(U\) 是 unitary。若 \(D\phi_\gamma=\gamma\phi_\gamma\)，则

\[
U\phi_\gamma
=
\frac{\gamma-i}{\gamma+i}\phi_\gamma.
\]

当 \(\rho=\frac12+i\gamma/2\) 时，

\[
z_\rho=1-\frac1\rho
=
\frac{2\gamma+i}{2\gamma-i},
\]

它与上述 Cayley 谱互为倒数，仍位于单位圆。于是 RH 的“零点在临界线”可以被转译成“Cayley 谱位于单位圆”，而 Li/Weil 正性可以转译成 unitary 谱的 Toeplitz/Gram 正性。

这仍然需要一个全局 \(D\)、正则化迹和完成 zeta 行列式。四维 Fisher 切空间只提供有限场的载体，不能自动产生这个 \(D\)。

### 63.8 外部研究锚点与本项目接口

本节的外部锚点是：

- Bui、Lester、Milinovich，Balazard–Saias–Yor 等价式；
- Nakamura，完整 Riemann zeta 概率分布与 RH；
- Connes 2026 年 RH 综述，其中把 Weil 二次型、信息论和从有限 Euler 乘积到零点极限的收敛问题放在同一框架中，参见 [arXiv:2602.04022](https://arxiv.org/abs/2602.04022)；
- 四阶矩的谱展开与 Motohashi 型 reciprocity，用来说明四阶读出具有真实谱结构，但其本身不是 RH 等价式。

本节不把任何外部工作转写成 Auric FIB 内部定理。当前真正的 bridge obligation 是：

\[
\text{FIB probability field}
\longrightarrow
\text{Weil/Poisson positive form}
\longrightarrow
\Xi_\sigma\text{ characteristic-function family}
\longrightarrow
\text{regularized global spectrum}.
\]

---

## 64. 四面体、四维概率金字塔与三维方金字塔

本节把“金字塔”“四面体”和“5 \(\to\) 4 \(\leftrightarrow\) 3”放入同一个仿射结构。先区分三种对象：

1. 三角形上的锥是四面体；
2. 五态概率律的全体是四维单纯形；
3. 五态概率律经过当前三坐标读出后是三维方金字塔。

因此这里的“四面体”和“金字塔”不是同一个对象的两个名称，而是同一个五态场在不同维数、不同读出下出现的单纯形图表和观察像。

### 64.1 五态概率载体是四维金字塔，四面体是它的三维面

令
\[
\Sigma=\{0,2,3,5,25\},
\qquad
\Delta^4
=
\left\{
p\in\mathbb R^\Sigma:
p_s\ge0,\ \sum_{s\in\Sigma}p_s=1
\right\}.
\]

\(\Delta^4\) 有五个顶点
\[
e_0,e_2,e_3,e_5,e_{25}.
\]
任选一个顶点作顶点外接点，剩余四个顶点张成一个三维四面体。例如以 \(e_{25}\) 为顶点，令
\[
F_{25}
=
\operatorname{conv}\{e_0,e_2,e_3,e_5\}
\cong\Delta^3.
\]
则
\[
\Delta^4
=
\operatorname{Cone}_{e_{25}}(F_{25})
=
\left\{
(1-t)q+t e_{25}:
q\in F_{25},\ 0\le t\le1
\right\}.
\tag{64.1}
\]

这给出一个精确的关系：
\[
\boxed{
\text{五态概率场 } \Delta^4
\text{ 是以四面体为底的四维金字塔。}
}
\]

更一般地，\(\Delta^4\) 有五个三维面
\[
F_s=\{p_s=0\}\cong\Delta^3,
\qquad s\in\Sigma,
\]
每一个面都是四面体。三角形上的锥关系
\[
\operatorname{Cone}(\Delta^2)\cong\Delta^3
\]
是上述关系的低一维版本。由此可见，四面体是单纯形层级中的三维局部单元，四维概率载体则是把它再加上一个状态顶点所得的金字塔。

这也说明“五态就是一个四面体”的说法少了一维。五态给出的是四维单纯形；四面体可以作为它的任一三维面，或者在选定三维读出后作为局部图表出现。

### 64.2 当前 FIB 读出的精确像是三维方金字塔

沿用本文的三坐标读出
\[
P(p)=(X,Y,Z)
=
(p_2+p_{25},\ p_5+p_{25},\ p_3),
\]
记
\[
\mathcal P=P(\Delta^4).
\]
五个状态顶点的像为
\[
\begin{array}{c|ccccc}
s & 0 & 2 & 5 & 25 & 3\\ \hline
P(e_s) & (0,0,0) & (1,0,0) & (0,1,0) & (1,1,0) & (0,0,1).
\end{array}
\tag{64.2}
\]

因此
\[
\mathcal P
=
\operatorname{conv}
\left\{
(0,0,0),(1,0,0),(0,1,0),(1,1,0),(0,0,1)
\right\}.
\tag{64.3}
\]
它的底面 \(Z=0\) 是单位正方形
\[
[0,1]^2\times\{0\},
\]
顶点是 \((0,0,1)\)。所以 \(\mathcal P\) 是一个三维方金字塔，而不是四面体。其不等式表示为
\[
X\ge0,\qquad
Y\ge0,\qquad
Z\ge0,\qquad
X+Z\le1,\qquad
Y+Z\le1.
\tag{64.4}
\]

这正是现有 Auric FIB ATOM “pyramid” 的仿射本体。状态 \(3\) 产生方金字塔的顶点，状态 \(0,2,5,25\) 产生方形底面。联合状态 \(25\) 位于底面对角的另一个端点，保留了 \(X\) 与 \(Y\) 同时取值的信息。

### 64.3 一维 \(\kappa\) 纤维是从四维场到三维金字塔的补充方向

令
\[
r=1-Z.
\]
给定 \((X,Y,Z)\in\mathcal P\)，所有具有该读出的五态概率律恰好写成
\[
p(\kappa;X,Y,Z)
=
(r-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\tag{64.5}
\]
其中坐标顺序为 \((p_0,p_2,p_3,p_5,p_{25})\)，并且
\[
\kappa_-(X,Y,Z)
=
\max(0,X+Y-r),
\qquad
\kappa_+(X,Y,Z)
=
\min(X,Y).
\tag{64.6}
\]
于是
\[
P^{-1}(X,Y,Z)\cap\Delta^4
=
\{p(\kappa;X,Y,Z):
\kappa_-\le\kappa\le\kappa_+\}.
\tag{64.7}
\]

这给出严格的维数关系
\[
\Delta^4
\ \xrightarrow[\text{一维线段纤维}]{\ P\ }\ 
\mathcal P^3_{\mathrm{square\ pyramid}}.
\tag{64.8}
\]
内点的纤维通常是线段，边界上部分纤维塌缩。因而三维方金字塔不是四维场的完整状态，而是把联合方向积分掉之后得到的观察商。

这个纤维也有一个纯仿射的来源。底面四边形的四个顶点满足唯一的 circuit 关系
\[
v_0-v_2-v_5+v_{25}=0,
\tag{64.9}
\]
其中
\[
v_0=(0,0,0),\quad
v_2=(1,0,0),\quad
v_5=(0,1,0),\quad
v_{25}=(1,1,0).
\]
正支撑为 \(\{v_0,v_{25}\}\)，负支撑为 \(\{v_2,v_5\}\)。同一个三维观察点因此拥有两套底面三角剖分，\(\kappa\) 正是在两套重心坐标之间记录接缝位置的变量。它不是坐标冗余，而是投影丢失的二阶联合方向。

### 64.4 两套四面体图表与方金字塔的关系

沿底面对角线 \(v_0v_{25}\) 剖分，方金字塔分解为两个四面体
\[
T_1=\operatorname{conv}(v_0,v_2,v_{25},v_3),
\qquad
T_2=\operatorname{conv}(v_0,v_5,v_{25},v_3).
\tag{64.10}
\]
沿另一条底面对角线 \(v_2v_5\) 剖分，则得到
\[
T_3=\operatorname{conv}(v_0,v_2,v_5,v_3),
\qquad
T_4=\operatorname{conv}(v_2,v_5,v_{25},v_3).
\tag{64.11}
\]

第一套剖分由纤维端点 \(\kappa=\kappa_+\) 选出，第二套剖分由端点 \(\kappa=\kappa_-\) 选出。每个四面体图表内重心坐标唯一；跨越公共三角面时必须满足 seam matching。保留两种剖分的整个方金字塔则允许 \(\kappa\) 在区间内连续变化。

因此，在当前理论中：

- 四面体是一个局部、单纯、坐标唯一的几何图表；
- 方金字塔是五个可见顶点及其全部凸组合；
- \(\kappa\) 是两个四面体图表之间的隐藏接缝坐标；
- circuit 关系是两种三角剖分和一维纤维同时出现的代数原因。

这也给出了与 CFMP 局部四面体单元的保守接口。CFMP 的四面体可继续携带四个顶点、六条边、Gram 数据和面间 gluing 约束；FIB 方金字塔只提供有限观察的顶点和接缝结构。把 \(T_i\) 直接赋予某个物理度量、双曲长度或引力曲率仍需另外的 metric bridge，当前结果只证明其组合与概率结构相容。

### 64.5 镜像固定切片本身是一个四面体

令
\[
\tau(p_0,p_2,p_3,p_5,p_{25})
=
(p_0,p_5,p_3,p_2,p_{25})
\]
交换 \(2\) 与 \(5\)。则固定集满足 \(p_2=p_5\)，并且
\[
\Delta^4_{\mathrm{mir}}
=
\Delta^4\cap\operatorname{Fix}(\tau)
=
\operatorname{conv}
\left\{
e_0,\ e_3,\ e_{25},\ \frac{e_2+e_5}{2}
\right\}
\cong\Delta^3.
\tag{64.12}
\]

所以这里出现两个不同的三维对象：

1. \(\mathcal P\) 是三维观察空间中的方金字塔，是 \(\Delta^4\) 的投影像；
2. \(\Delta^4_{\mathrm{mir}}\) 是四维概率空间中的三维四面体，是镜像固定切片。

二者都来自同一个五态场，却不能直接相互命名。前者表示可见事件的几何外形，后者表示镜像对称成立时的概率状态。上一节的 RH 候选法向
\[
\eta(p)=\frac12\log\frac{p_2}{p_5}
\]
垂直于这个四面体切片；当前投影的隐藏坐标 \(\kappa\) 则沿着另一条镜像偶方向。它们都是“4 维到 3 维”的降维，却承担不同信息：

\[
\begin{array}{c|c|c}
\text{分解} & \text{被删除或固定的方向} & \text{含义}\\ \hline
\Delta^4\to\mathcal P^3 & \kappa\text{ 纤维} & \text{联合事件的观察缺失}\\
\Delta^4\to\Delta^3_{\mathrm{mir}} & \eta\text{ 奇法向} & 2\leftrightarrow5\text{ 镜像缺陷}
\end{array}
\tag{64.13}
\]

RH 桥接若要把两者连接起来，必须构造一个自伴或正定的耦合，把 \(\kappa\) 与 \(\eta\) 的两个账本联系起来。仅仅因为二者都有 \(4\to3\) 形式，不能把它们当作同一个坐标。

### 64.6 “5 \(\to\) 4 \(\leftrightarrow\) 3”的严格解释

这条线可以写成
\[
\mathbb R^5
\ \xrightarrow{\ \sum p_s=1\ }\ 
\Delta^4
\ \xrightarrow{\ P\ }\ 
\mathcal P^3.
\tag{64.14}
\]

其中：

- \(5\) 是五个未归一化模式坐标；
- \(4\) 是归一化后概率场的仿射维数；
- \(3\) 是三坐标观察商；
- 从 \(4\) 回到 \(3\) 是投影，始终存在；
- 从 \(3\) 回到 \(4\) 需要选择一个截面
  \[
  s:\mathcal P\to\Delta^4,
  \qquad P\circ s=\operatorname{id}_{\mathcal P},
  \]
  也就是给出一条 \(\kappa(X,Y,Z)\)。

已有的最大熵规则、条件独立规则或给定的二阶缺陷都可以作为截面选择。例如定义
\[
\Delta_{\det}
=
p_0p_{25}-p_2p_5
=
(1-Z)\kappa-XY.
\tag{64.15}
\]
在 \(Z<1\) 时，
\[
\kappa
=
\frac{XY+\Delta_{\det}}{1-Z}.
\tag{64.16}
\]
因此
\[
(X,Y,Z,\Delta_{\det})
\longleftrightarrow
(p_0,p_2,p_3,p_5,p_{25})
\]
给出精确的四维完成坐标。这里新增的量正是函数代数中缺失的 \(xy\) 或联合生成元，也可解释为条件协方差或 seam 缺陷。

所以“四维来自五态，三维从四维逃逸”可以改写为一个严格命题：

> 四维是把五个模式归一化后留下的最小概率状态空间；三维是可见读出压缩后的商空间；四维能否被补充或消除，取决于是否给出截面，以及动力学是否保持这个商的自治性。

### 64.7 四维是否是“临时动态”：最小隐藏状态判据

令 \(L\) 是 \(\Delta^4\) 所在切空间上的线性生成元，令 \(u=Pp\)。存在三维自治生成元 \(G\) 使
\[
P e^{tL}=e^{tG}P
\qquad\text{对所有 }t\ge0
\]
当且仅当
\[
L(\ker P)\subseteq\ker P.
\tag{64.17}
\]

若条件成立，\(\kappa\) 只是一种可消去的坐标补充，三维方金字塔上的动力学闭合。若条件失败，则
\[
\dot u=P Lp
\]
依赖于同一观察点上的不同 \(\kappa\)，三维模型需要记忆核或额外隐藏状态。此时四维是使动力学恢复自治所需的最小状态增广。它可以被称为“临时动态”，但这个词应理解为模型约化意义上的临时，不是一个已证明的额外物理时空轴。

Fisher 度量还给出局部的几何信号。沿纤维方向
\[
\partial_\kappa p=(1,-1,0,-1,1),
\]
故
\[
g^F_{\kappa\kappa}
=
\frac1{p_0}+\frac1{p_2}+\frac1{p_5}+\frac1{p_{25}}.
\tag{64.18}
\]
当 \(\kappa\) 到达 \(\kappa_-\) 或 \(\kappa_+\) 时，至少一个概率趋于零，\(g^F_{\kappa\kappa}\) 发散。几何上，这表示隐藏纤维在概率边界塌缩，而接近塌缩面的变化具有无限 Fisher 刚性。四维补充因此不是平凡的 \(\mathcal P^3\times I\) 直积，而是带有变长纤维和连接项的分层场。

### 64.8 与 RH、能级和四面体几何的接口

本节给出的可检验接口是
\[
\boxed{
\Delta^4
\longrightarrow
\mathcal P^3_{\mathrm{square\ pyramid}},
\qquad
\Delta^4_{\mathrm{mir}}\cong\Delta^3_{\mathrm{tetrahedron}}.
}
\tag{64.19}
\]

它把前一节的 RH 固定集解释成一条双账本约束：

1. \(\kappa\) 账本记录观察投影遗漏的联合方向；
2. \(\eta\) 账本记录镜像反射的奇法向；
3. 四面体是镜像固定切片或局部 simplex chart；
4. 方金字塔是三维可见事件的全局凸包；
5. 四维概率场同时容纳两种账本。

若未来存在从零点场到五态场的等变映射 \(\Phi\)，则必须分别说明
\[
\eta(\Phi(\rho))
=
\log\left|1-\frac1\rho\right|
\]
如何表达 RH 法向缺陷，以及 \(\kappa(\Phi(\rho))\) 如何表达联合或记忆缺陷。只有当这两个坐标由同一个自伴场、正定二次型或可验证的迹公式耦合时，四面体、金字塔和 RH 能级才形成真正的统一结构。当前结果建立了有限仿射和 Fisher 几何接口，没有把它们升级为 RH 证明。

### 64.9 沿 \(\kappa\) 纤维的熵松弛：四维动态何时回填到三维

固定一个可见点 \((X,Y,Z)\)，在其纤维区间内把负熵写成
\[
\Phi(\kappa)
=
\sum_{s\in\Sigma}p_s(\kappa)\log p_s(\kappa).
\]
由
\[
\partial_\kappa p=(1,-1,0,-1,1)
\]
直接得到
\[
\Phi'(\kappa)
=
\log\frac{p_0p_{25}}{p_2p_5}
=
\log\frac{(r-X-Y+\kappa)\kappa}
{(X-\kappa)(Y-\kappa)},
\tag{64.20}
\]
以及
\[
\Phi''(\kappa)
=
\frac1{p_0}+\frac1{p_2}+\frac1{p_5}+\frac1{p_{25}}
=
g^F_{\kappa\kappa}>0.
\tag{64.21}
\]

因此每条非退化纤维上存在唯一临界点
\[
p_0p_{25}=p_2p_5,
\qquad
\Delta_{\det}=0,
\qquad
\kappa_*=\frac{XY}{1-Z},
\tag{64.22}
\]
这正是条件独立或最大熵补全。若沿隐藏方向取任意正 mobility \(m(X,Y,Z,\kappa)>0\) 的梯度流
\[
\dot\kappa=-m\,\Phi'(\kappa),
\tag{64.23}
\]
则
\[
\frac{d}{dt}\Phi(\kappa(t))
=
-m\,(\Phi'(\kappa(t)))^2
\le0.
\tag{64.24}
\]

这给出“临时动态”的严格版本。四维状态 \((X,Y,Z,\kappa)\) 是带隐藏联合坐标的增广状态；在熵松弛足够快且三维生成元满足自治闭合时，轨迹被吸引到 \(\Delta_{\det}=0\) 的三维截面，\(\kappa\) 可以被消去。若素数场或 RH 候选场持续驱动 \(\kappa\) 偏离该截面，则三维观察会留下记忆，四维增广状态不能被静态补全取代。

因此归一化与纤维回填的方向记为
\[
5\longrightarrow4\longleftarrow3:
\]
五态模式经归一化产生四维概率载体，三维观察只能通过一条非规范的 \(\kappa\) 纤维回填到四维。选 \(\kappa_*\)、选某个四面体端点 \(\kappa_\pm\)，或直接测量 \(\Delta_{\det}\)，都会给出不同的截面。只有动力学不变性、熵松弛或额外的二阶观测能够说明哪一种回填是稳定且有意义的。

这一区分保留了两条方向：

\[
\mathbb R^5\to\Delta^4
\quad\text{是归一化约束，}
\]
\[
\mathcal P^3\rightsquigarrow\Delta^4
\quad\text{是集合值纤维提升，}
\]
\[
\Delta^4\to\mathcal P^3
\quad\text{是确定性观察投影。}
\]

因此四维不是额外物理轴的声明，而是让三维观察恢复成自治五态动力所需的最小一维补充。它可以在满足快速松弛和 lumpability 时成为可消去的中间变量，也可以在隐藏方向被持续激发时成为不可省略的记忆状态。


## 65. 静态量子网络响应与熵时间账本

本节把“大场是静态量子信息网络，小场是局部节点或边，信息流产生宏观空间响应和时间账本”的直觉压缩为同一组有限网络数据上的两个派生量。空间候选量来自静态 Poisson 响应，时间候选量来自量子 Markov 半群的相对熵下降。两者共享网络拓扑、边参数和局部生成元。

### 定义 65.1（有限静态网络、势和响应度量）

令 \(G=(V,E)\) 为有限连通图，为每条边选定方向并令 \(q_e\in\mathbb R^V\) 为其关联向量。给定边容量 \(c_e>0\)，定义加权拉普拉斯
\[
L_c
=
\sum_{e\in E}c_e q_eq_e^{\mathsf T}.
\]
它满足
\[
L_c\mathbf1=0,
\qquad
L_c=L_c^{\mathsf T},
\qquad
L_c\succeq0,
\qquad
\ker L_c=\mathbb R\mathbf1.
\]

给定零和源 \(b\in\mathbf1^\perp\)，定义静态势
\[
\phi=L_c^+b,
\]
其中 \(L_c^+\) 是 Moore--Penrose 伪逆。边流和 Dirichlet 能量分别为
\[
I_e=c_e q_e^{\mathsf T}\phi,
\qquad
\mathcal E_c(b)
=
\frac12\sum_{e\in E}c_e(q_e^{\mathsf T}\phi)^2
=
\frac12 b^{\mathsf T}L_c^+b.
\]

对两个零和源 \(b_1,b_2\)，定义响应双线性型
\[
g_c(b_1,b_2)
=
b_1^{\mathsf T}L_c^+b_2.
\]
对节点 \(a,b\in V\)，定义有效响应距离
\[
R_c(a,b)
=
(\delta_a-\delta_b)^{\mathsf T}
L_c^+
(\delta_a-\delta_b).
\]

这些量完全由有限图和边容量决定。它们是静态网络几何对象，不预设连续流形或物理引力解释。

### 定理 65.2（边容量变化的响应变分公式）

设图保持连通，\(c_e(s)\) 对 \(s\) 可微，令
\[
L_s=\sum_ec_e(s)q_eq_e^{\mathsf T},
\qquad
\phi_s=L_s^+b.
\]
在 \(\mathbf1^\perp\) 上有
\[
\frac{d}{ds}L_s^+
=
-L_s^+L_s'L_s^+.
\]
因此
\[
\boxed{
\frac{d}{ds}R_s(a,b)
=
-\sum_{e\in E}
c_e'(s)
\bigl(q_e^{\mathsf T}\phi_s^{ab}\bigr)^2,
}
\]
其中
\[
\phi_s^{ab}
=
L_s^+(\delta_a-\delta_b).
\]
更一般地，
\[
\frac{d}{ds}g_s(b_1,b_2)
=
-b_1^{\mathsf T}L_s^+L_s'L_s^+b_2.
\]

#### 证明

在 \(\mathbf1^\perp\) 上 \(L_s\) 可逆。对恒等式
\[
L_sL_s^+=I_{\mathbf1^\perp}
\]
求导得
\[
L_s'L_s^++L_s\frac{d}{ds}L_s^+=0.
\]
左乘 \(L_s^+\) 即得
\[
\frac{d}{ds}L_s^+
=
-L_s^+L_s'L_s^+.
\]
又有
\[
L_s'
=
\sum_ec_e'(s)q_eq_e^{\mathsf T},
\]
代入 \(R_s=(\delta_a-\delta_b)^{\mathsf T}L_s^+(\delta_a-\delta_b)\) 即得。证毕。

### 定义 65.3（网络响应曲率）

对固定零和源 \(b\ne0\)，令
\[
R_s[b]=b^{\mathsf T}L_s^+b.
\]
定义响应曲率
\[
\kappa_s[b]
=
-\frac{d}{ds}\log R_s[b]
=
\frac{
\sum_ec_e'(s)(q_e^{\mathsf T}\phi_s)^2
}{
R_s[b]
}.
\]

若容量变化服从
\[
c_e'(s)=-\alpha_e\sigma_e(s),
\qquad
\alpha_e\ge0,\quad \sigma_e(s)\ge0,
\]
则
\[
\kappa_s[b]\le0,
\]
即边容量因局部耗散下降时，响应电阻沿该源方向增加。若 \(c_e'(s)=+\alpha_e\sigma_e(s)\)，则响应电阻沿该源方向收缩。

这里的 \(\kappa_s[b]\) 是有限网络的响应曲率候选。它控制静态源扰动如何改变网络几何响应，但尚未被证明等于 Ricci 曲率、Einstein 张量或任何连续时空曲率。要得到后者，仍需 §54 的 metric-measure/Mosco 极限、局部性和曲率稳定性条件。

### 定义 65.4（有限量子网络与局部生成元）

令
\[
\mathcal A=\bigotimes_{v\in V}M_{d_v}(\mathbb C)
\]
为有限量子网络代数，令 \(\sigma\succ0\) 为忠实参考态。对每条边给定一个 Schrödinger 表示的量子 Markov 生成元 \(\mathcal L_e\)，满足
\[
\mathcal L_e^\ast(I)=0,
\qquad
\mathcal L_e(\sigma)=0.
\]
令
\[
\mathcal L=\sum_{e\in E}\mathcal L_e,
\qquad
\rho_t=e^{t\mathcal L}\rho_0.
\]

每个 \(\mathcal L_e\) 表示一个局部小场对相邻节点的作用。总生成元 \(\mathcal L\) 是静态大场上的局部作用叠加。若进一步要求详细平衡，则可以把 §38、§53 的 GNS Dirichlet 和 SLD Fisher 结构接入同一个量子网络。

### 定理 65.5（熵生产与量子时间账本）

对
\[
D(\rho\Vert\sigma)
=
\operatorname{tr}\rho(\log\rho-\log\sigma)
\]
定义每条边的熵生产率
\[
\Sigma_e(\rho)
=
-\operatorname{tr}
\left[
\mathcal L_e(\rho)
(\log\rho-\log\sigma)
\right].
\]
在每个边半群保持 \(\sigma\) 且满足量子 Markov 单调性的条件下，
\[
\Sigma_e(\rho)\ge0.
\]
总熵生产率
\[
\Sigma(\rho)=\sum_{e\in E}\Sigma_e(\rho)
\]
满足
\[
\boxed{
\frac{d}{dt}D(\rho_t\Vert\sigma)
=
-\Sigma(\rho_t).
}
\]

定义热时间或熵时间
\[
\tau(t)
=
D(\rho_0\Vert\sigma)-D(\rho_t\Vert\sigma)
=
\int_0^t\Sigma(\rho_s)\,ds.
\]
则
\[
\tau(t)\ge0,
\qquad
\frac{d\tau}{dt}=\Sigma(\rho_t)\ge0.
\]
如果 \(\Sigma(\rho_t)>0\) 在几乎处处成立，则 \(\tau\) 严格递增，可以反解 \(t=t(\tau)\)。如果 \(\Sigma\equiv0\)，则热时间不推进，即网络处于相对熵守恒的可逆或平衡轨道。

#### 证明

由 \(\sigma\) 忠实且 \(\mathcal L\) 保持迹，
\[
\frac{d}{dt}D(\rho_t\Vert\sigma)
=
\operatorname{tr}
\left[
\mathcal L(\rho_t)
(\log\rho_t-\log\sigma)
\right].
\]
对 \(\mathcal L=\sum_e\mathcal L_e\) 分解，得到
\[
\frac{d}{dt}D(\rho_t\Vert\sigma)
=
-\sum_e\Sigma_e(\rho_t).
\]
每个 \(\Sigma_e\ge0\) 来自固定态量子 Markov 半群下相对熵的数据处理单调性。积分即得 \(\tau\) 的公式和单调性。证毕。

### 推论 65.6（离散量子时间的可加性）

若
\[
\rho_{n+1}=\Phi_n(\rho_n),
\qquad
\Phi_n(\sigma)=\sigma
\]
且每个 \(\Phi_n\) 为 CPTP，则
\[
\Delta\tau_n
=
D(\rho_n\Vert\sigma)
-
D(\rho_{n+1}\Vert\sigma)
\ge0,
\]
并且
\[
\tau_N
=
\sum_{n=0}^{N-1}\Delta\tau_n
=
D(\rho_0\Vert\sigma)-D(\rho_N\Vert\sigma).
\]

因此时间账本在离散网络更新中是严格可加的。每一步不需要预设外部时间变量，只需要记录相对熵下降。

### 推论 65.7（空间响应和时间账本的统一输入）

若边容量 \(c_e\) 由局部量子态或边熵生产率决定，例如
\[
c_e'=F_e(\Sigma_e),
\]
则定理 65.2 给出
\[
\frac{d}{ds}R_s[b]
=
-\sum_eF_e(\Sigma_e)
\bigl(q_e^{\mathsf T}\phi_s\bigr)^2.
\]

因此同一网络中的局部量子熵流同时产生两类派生量：

\[
\boxed{
\begin{aligned}
\text{静态空间响应}
&=
b^{\mathsf T}L_c^+b,\\
\text{热时间账本}
&=
D(\rho_0\Vert\sigma)-D(\rho_t\Vert\sigma).
\end{aligned}
}
\]

空间响应描述源扰动在网络中的几何传播，熵时间描述网络状态沿不可逆方向积累了多少信息损失。两者可以由同一组边局部量 \((c_e,\mathcal L_e,\Sigma_e)\) 联立计算。



### 推论 65.8（可逆参数时间与不可逆熵时间的分离）

若总生成元分解为
\[
\mathcal L
=
\mathcal L_{\mathrm{coh}}
+
\mathcal L_{\mathrm{diss}},
\qquad
\mathcal L_{\mathrm{coh}}(\rho)=-i[H,\rho],
\]
且
\[
[H,\sigma]=0,
\]
则相干部分保持参考态相对熵不变：
\[
D\!\left(
e^{t\mathcal L_{\mathrm{coh}}}\rho
\middle\Vert\sigma
\right)
=
D(\rho\Vert\sigma).
\]
因此外部参数 \(t\) 可以沿可逆相位轨道推进，而内部熵时间
\[
\tau(t)=D(\rho_0\Vert\sigma)-D(\rho_t\Vert\sigma)
\]
只记录耗散部分造成的不可逆信息损失。若
\[
\Sigma_{\mathrm{diss}}(\rho_t)>0
\]
几乎处处成立，则 \(\tau\) 可以作为 \(t\) 的单调重参数；若 \(\Sigma_{\mathrm{diss}}\equiv0\)，相干演化仍可存在，但熵时间不推进。

这给出静态大场上的两种时间参数：

\[
\boxed{
\text{可逆参数时间 }t
\quad\text{与}\quad
\text{不可逆熵时间 }\tau
}
\]

前者由 Hamiltonian 或其他可逆网络参数化，后者由局部量子耗散和相对熵账本定义。把观测者的岁月流逝解释为后者，需要额外证明观察过程只依赖 \(\tau\)，或至少对 \(t\) 和 \(\tau\) 给出可识别的映射。

### 证据边界

本节证明的是有限网络上的线性代数、伪逆变分公式、CPTP 相对熵单调性和有限量子 Markov 账本。要把
\[
R_s[b]
\]
识别为引力势或时空距离，需要连续非塌缩极限、局部性、曲率稳定性以及与某个几何张量的识别定理。要把
\[
\tau(t)
\]
识别为物理时间，需要证明该熵时间与实验时钟、因果序或某个规范不变量相容。当前理论只证明它是一个单调可加的内部账本。

这一结构与近期把量子网络、非局部时钟和曲率敏感读出结合起来的研究方向相容。相关工作提出通过分布式纠缠节点构造对曲率影响敏感的非局部时钟态，但其物理实现仍依赖具体时空模型和实验读出。参见 [Testing quantum theory on curved spacetime with quantum networks](https://journals.aps.org/prresearch/abstract/10.1103/PhysRevResearch.7.023192)。
## 追加锚（本行以下为增补区）
