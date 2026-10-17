# 六维第四个无偏基问题：理论续卷

本卷承接 [前卷](MUB_SIX_FOURTH_BASIS_THEORY.md)，保留其编号、基约定与参数支。前卷第 51 节给出了实际循环正交三元组的严格换位正性；本卷进一步使用同一组相位与两组 flatness，排除该正性区域内的零模平衡子层。

## 52. 实参数支上实际循环三元组的零模不平衡

### 52.1 定义与结论

沿用前卷第 46、51 节的实参数支。令 `-1<a<1`，取

```math
p=\frac{a-1+i(h+a/h)}2,\qquad
q=\frac{-a-1+i(h-a/h)}2,
\qquad h>1,\qquad s=h^2,\qquad
a^2=\frac{s(3-s)}{1+s}.
```

这里 `p,q` 是前卷所选的上半平面单位相位，`p+q=-1+ih`。记 `P=p-1,Q=q-1`、`A=J+PI,B=J+QI`，并固定

```math
H_0=\frac1{\sqrt6}
\begin{pmatrix}A&B\\\overline B&-\overline A\end{pmatrix},
\qquad Sx=(x_1,x_2,x_0).
```

`A,B` 对称，故此处的共轭也等于 adjoint。这个 paired-circulant 种子来自 Szöllősi 的已知构造，见 [arXiv:0811.3930，§2](https://arxiv.org/abs/0811.3930)，DOI `10.1090/S0002-9939-09-10102-8`；以下结论是对其实际循环三元组的额外限制。

**命题 52.1。** 设 `v=(x,y)/sqrt(6)`，其中 `x,y` 的六个分量均有模一。若 `H0v` 也 flat，且同一组实际向量 `v,Sv,S²v` 两两正交，则

```math
\boxed{\left|\sum_jx_j\right|^2\ne3,
\qquad\left|\sum_jy_j\right|^2\ne3.}
```

等价地，`alpha_x=sum_j conjugate(x_j)x_(j+1)` 的实部非零。循环正交给出两个零模能量之和为六，故任一等式成立就会同时成立。本命题只限制种子中指定的零模，不把另外两个 mode 与它交换。

### 52.2 平衡相位纤维的完整分支

反设 `|sum x|²=3`。循环正交给出 `alpha_x+alpha_y=0`，而 `|sum x|²=3+2 Re(alpha_x)`，所以 `alpha_x=in`，其中 `n` 为实数。

对任意单位相位三元组 `z`，相邻比值 `e_j=conjugate(z_j)z_(j+1)` 的积为一，并且恰为下述多项式的三个根，按重数计：

```math
t^3-\alpha_z t^2+\overline{\alpha_z}t-1.
```

由于 `alpha_y=-alpha_x=conjugate(alpha_x)`，`y` 的相邻比值是 `x` 的相邻比值的共轭的一种排列。三个比值的偶排列是循环置换，积分后得到 `y=gamma S^m conjugate(x)`；奇排列则得到 `y=gamma Rx`，其中 `R` 是一个坐标换位。积分只留下同一个单位相位 `gamma`。因此全部可能性为

```math
y=\gamma Rx\quad(R\text{ 为三个换位之一}),
\qquad
y=\gamma S^m\overline x\quad(m=0,1,2),
\qquad |\gamma|=1.
\tag{52.1}
```

该推理也包括有重复比值的情形。下面逐类排除，始终保留输入和输出中的同一个 `gamma`。

### 52.3 普通反射分支的正多项式证书

`H0` 与所有同步坐标置换交换，而坐标置换将 `S` 共轭为 `S` 或 `S²`。故普通反射分支只需处理 `y=gamma R01x`。乘公共相位后可设 `x2=1`，并置

```math
u=\frac{x_0+x_1}{2},\qquad b=|u|^2,\qquad w=\operatorname{Im}u,
\qquad\gamma=G+iH,\quad G,H\in\mathbb R.
```

两个 channel 的自相关互为共轭，循环正交使它们之和为零，故 `|1+2u|²=3`。于是

```math
\operatorname{Re}u=\frac12-b,
\qquad w^2=2b-b^2-\frac14,
\qquad 0\le b\le1.
\tag{52.2}
```

同时，`<v,R01v>=(4b-1)/3`。前卷第 51 节的严格换位正性因此给出 `b>1/4`。

定义 `Y=aH/h`。固定坐标二上的两个未归一化输出分量为

```math
z_+=p+2u+\gamma(q+2u),\qquad
z_-=\overline q+2u-\gamma(\overline p+2u).
```

令 `E±=|z±|²-6`。代入种子恒等式、`G²+H²=1` 和式 (52.2)，直接展开得到

```math
E_++E_-=4\bigl(2hw(G-Y)+6b-3\bigr),
```
```math
E_+-E_-=2\bigl((12b+s-3)G-(4b+s-1)Y+4hw\bigr).
```

实际 flatness 使两式为零。还须保留整个第一输出 channel 的范数。由

```math
A^\dagger A=(3-a)I+aJ,\quad B^\dagger B=(3+a)I-aJ,
\quad A^\dagger B=\overline P QI+(3+\overline P+Q)J
```

以及 `||x||²=|sum x|²=3`，有 `||Ax||²=||BR01x||²=9`。所以 `||Ax+gamma BR01x||²=18` 等价于 `Re(gamma Z)=0`，其中

```math
Z=\overline P Q(4b-1)+3(3+\overline P+Q)
=\frac{(s+3)(4b-1)}2+
\frac{ia}{2h}\bigl((s+3)(4b-1)-6\bigr).
```

这里用了 `bar(P)Q=(s+3)/2+ia(h+3/h)/2` 和 `3+bar(P)+Q=-ia/h`。合并三个实际方程，得到

```math
\begin{pmatrix}
2hw&-2hw&6b-3\\
12b+s-3&-(4b+s-1)&4hw\\
(s+3)(4b-1)&6-(s+3)(4b-1)&0
\end{pmatrix}
\begin{pmatrix}G\\Y\\1\end{pmatrix}=0.
\tag{52.3}
```

但左侧矩阵的行列式恰为 `-24F(b,s)`，其中

```math
F(b,s)=s b(8b^2-10b+5)+3(b-1)(4b-1)(2b-1).
```

这个多项式在 `1/4<b<=1,s>1` 上严格为正。首先

```math
8b^2-10b+5=8(b-5/8)^2+15/8>0.
```

当 `b<=1/2` 时，`F` 的第一项为正、第二项非负；当 `b>=1/2` 时，使用恒等式

```math
F(b,s)=(s-1)b(8b^2-10b+5)+8b(1-b)^2+3(2b-1)^3>0.
```

因此式 (52.3) 不可能湮灭非零向量 `(G,Y,1)`。这排除了所有普通反射分支，并且没有除以 `a`，所以包括 `a=0`。

### 52.4 未位移的共轭分支

若 `y=gamma conjugate(x)`，令 `z_j=(x_j,y_j)`、`r_jk=Re<z_j,z_k>`。其 Gram 矩阵是实矩阵、对角元为二，且秩至多二，因为 `<z_j,z_k>=2 Re(conjugate(x_j)x_k)`。循环正交给出 `r01+r12+r20=0`；严格换位正性给出 `p_jk=1+r_jk>0`。展开行列式得

```math
\det(\langle z_j,z_k\rangle)
=2\bigl(p_{01}p_{12}+p_{12}p_{20}+p_{20}p_{01}
       +p_{01}p_{12}p_{20}\bigr)>0,
```

与秩约束矛盾。

### 52.5 两个共轭位移与中心化相位坐标

同步坐标换位将 `m=1` 与 `m=2` 互换，并保持实际 flatness 和循环正交。因此只需排除 `y=gamma S conjugate(x)`。

此时每个 `r_jk` 是 `x` 的两个相邻比值实部之和，亦即第三个实部的负值，因为三个实部之和为零。若 `x` 有两个相同分量，就会有一个相邻比值为一，从而产生换位内积零，与前卷第 51 节矛盾。故 `x` 的三个分量互不相同。

乘公共相位后可设 `sum x=sqrt(3)`；共轭位移关系保持，只改变单位相位 `gamma`。置

```math
\xi=x_0x_1x_2,\qquad d=1-\sqrt3\xi,\qquad
u=x-\frac1{\sqrt3}\mathbf1,\qquad\alpha_x=in.
```

单位相位的对称多项式给出

```math
u^Tu=2d,\qquad u^\dagger u=2,\qquad u^\dagger Su=-1+in.
```

`u,conjugate(u)` 线性无关；否则三个不同的单位圆点 `x_j` 会落在同一条实仿射直线上，而直线与圆最多相交两次。因此 `e=1-|d|²>0`。利用
`u^T S conjugate(u)=-1-in`、`conjugate(u)^T S conjugate(u)=-conjugate(d)`，解出

```math
S\overline u=\frac{in\overline d}{2e}u+
\left(-\frac12-\frac{in}{2e}\right)\overline u.
```

`S` 在二维零和空间的行列式为一；上述表示及其共轭组成的矩阵行列式为 `1/4+n²/(4e)`。所以 `n²=3e`，特别地 `n!=0`，并有

```math
S\overline u=\frac{3i\overline d}{2n}u+
\left(-\frac12-\frac{3i}{2n}\right)\overline u,\qquad
S^2\overline u=-\frac{3i\overline d}{2n}u+
\left(-\frac12+\frac{3i}{2n}\right)\overline u.
\tag{52.4}
```

再由 `|xi|=1`，即 `|1-d|²=3`，得到

```math
d=-\frac{n^2+3}{6}+i\nu,\qquad
36\nu^2=27-18n^2-n^4,\qquad\nu\in\mathbb R.
\tag{52.5}
```

### 52.6 两组 flatness 的联合系数方程

写 `gamma=G+iH`。两个未归一化输出 channel 的分量为

```math
P x_j+\gamma Q\overline{x_{j+1}}+\sqrt3(1+\gamma),\qquad
\overline Qx_j-\gamma\overline P\overline{x_{j+1}}+\sqrt3(1-\gamma).
```

定义

```math
A_+=\sqrt3P(1+\overline\gamma),\quad B_+=\sqrt3Q(1+\gamma),\qquad
A_-=\sqrt3\overline Q(1-\overline\gamma),\quad B_-=\sqrt3\overline P(1-\gamma),\qquad
D=P\overline Q\overline\gamma\xi.
```

使用 `x_j x_(j+1)=xi conjugate(x_(j+2))`，两个输出平方模的非恒定部分分别为 `A+u+B+S conjugate(u)+D S² conjugate(u)` 和 `A-u+B-S conjugate(u)-D S² conjugate(u)` 的两倍实部。由式 (52.4) 与线性无关性，两组 flatness 必须同时满足

```math
\mathcal E(A_+,B_+,D)=0,\qquad\mathcal E(A_-,B_-,-D)=0,
```
```math
\mathcal E(A,B,D)=A-\frac{\overline B+\overline D}{2}
+\frac{3i}{2n}\bigl(\overline d(B-D)+\overline B-\overline D\bigr).
\tag{52.6}
```

令 `L=bar(P)+Q=-3-ia/h`、`M=bar(P)-Q=a-ih`、`z=gamma M`。相加式 (52.6)，再乘 `2n/sqrt(3)`，得到

```math
n\overline L+3n\overline z+
3i\bigl(\overline d(L-z)+\overline L-\overline z\bigr)=0.
\tag{52.7}
```

这是关于同一个 `G,H` 的两个实线性方程。用式 (52.5) 和种子关系化简，其系数行列式为 `-48h²n²/(s+1)!=0`，所以

```math
G=\frac{6a(s+1)\nu-h^3n^2+9h}{6h^2n},\qquad
H=\frac{a(s+1)n^2+6h^3\nu}{6h^2n}.
\tag{52.8}
```

把式 (52.8) 代回第一组方程，记 `A0=a(5s+3)`、`B0=h(s-1)>0`，展开得到

```math
\operatorname{Re}\frac{\mathcal E(A_+,B_+,D)}{\sqrt3}
=-\frac{2A_0(\nu-n)-B_0(n^2+9)}{8h^2n},
```
```math
\operatorname{Im}\frac{\mathcal E(A_+,B_+,D)}{\sqrt3}
=\frac{A_0(n^2-3)+18B_0(n+\nu)}{24h^2n}.
\tag{52.9}
```

式 (52.7)–(52.9) 在清去已证明非零的分母后都是多项式恒等式，仅用了 `a²=s(3-s)/(1+s)` 与式 (52.5)。它们没有放松任何一组相位。

### 52.7 非零行列式矛盾与实际基方向

实际 flatness 和式 (52.9) 强制

```math
\begin{pmatrix}2(\nu-n)&-(n^2+9)\\n^2-3&18(n+\nu)\end{pmatrix}
\binom{A_0}{B_0}=0.
```

然而由式 (52.5)，该矩阵行列式恰为

```math
36(\nu^2-n^2)+(n^2+9)(n^2-3)=-48n^2\ne0.
```

所以 `A0=B0=0`，与 `B0=h(s-1)>0` 矛盾。式 (52.1) 的所有分支均已排除，命题 52.1 得证。

对相对于 `(I,H0)` 的实际共同无偏归一化列 `f`，应令 `v=H0* f`。此时 `v` 和 `H0v=f` 都 flat；因为 `H0` 与 `S` 交换，`f,Sf,S²f` 的正交等价于输入三元组的正交。因此本命题排除的是 `sqrt(6) H0* f` 两个 channel 的零模平衡，不能省略此基方向。

特别地，若 `y=gamma Pi x`，其中 `Pi` 为任意坐标置换，则两个 channel 的零模能量相等，循环正交又使其和为六。因此命题 52.1 同时排除了全部这种 projectively permuted channels。

**命题 52.2（严格正性区域中的输入反例族）。** 在普通反射分支中，任取 `1/4<b<1`，取 `u=1/2-b+iw`、`w²=2b-b²-1/4`，并令

```math
x_2=1,\quad
x_0=u\left(1+i\sqrt{\frac{1-b}{b}}\right),\quad
x_1=u\left(1-i\sqrt{\frac{1-b}{b}}\right),\quad y=\gamma R_{01}x.
```

这些输入单位相位的循环平移正交，两个 channel Fourier transforms 都满支撑；其三个换位内积为 `(4b-1)/3,2(1-b)/3,2(1-b)/3`，全部严格为正。但没有任何同一个单位相位 `gamma` 能使实际输出 flat。

**证明。** 显式公式给出 `|x0|²=|x1|²=b(1+(1-b)/b)=1` 和 `|1+2u|²=3`；`y` 是 `x` 的相位倍反射，故两个循环自相关之和为零。满支撑由前卷 §51.5 的逐模总能量六与单模退化排除推出。直接代入得到所列三个换位内积，而式 (52.3) 的正多项式证书排除实际输出 flat。证毕。

实际循环三元组本已由前卷第 46、51 节具有满支撑和非零 `Delta`，故 canonical mode-local 射线不在本节候选域中。本节进一步排除了零模平衡子层，仍未分类或排除零模能量不相等的循环三元组、来自不同置换轨道的三元组或 residual quartet。

## 53. 配对 two-circulant 的 Fourier 交点及实际 cyclic completion 的两条边

本节沿用正文 §51 和上节的实际向量方向。先对任意复参数的配对
circulant 矩阵给出精确交点判据，再将它用于同时满足两组平坦性条件的
cyclic triple。这里的 Hadamard 等价始终允许任意左右单位模对角矩阵
与行列置换；Fourier union 指 Fourier family 及其转置族的等价类之并。

### 53.1 任意复参数的平方行列对判据

下标属于 \(\mathbb Z/3\mathbb Z\)。对 \(x,y\in\mathbb T^3\)，置
\[
\alpha(z)=\sum_{t=0}^2\overline{z_t}z_{t+1},\qquad
X_{ij}=x_{i-j},\quad Y_{ij}=y_{i-j},\qquad
M(x,y)=\begin{pmatrix}X&-Y^*\\Y&X^*\end{pmatrix}.
\]
称两个不同行或不同列构成**平方比例对**，是指两向量逐项平方后成比例。
因为所有条目非零，这等价于相应两个平方向量的全部 \(2\times2\) 子式为零。
比例常数必为单位模。左右 monomial 等价保持相应类型的平方比例对是否存在。

**命题 53.1。** 假设 \(\alpha(x)+\alpha(y)=0\)。则 \(MM^*=6I\)，且：

1. \(M\) 有平方比例行对，当且仅当存在 \(d\in\mathbb Z/3\mathbb Z\)、
   \(\gamma\in\mathbb T\)，使 \(y_{t+d}=\gamma x_t\) 对所有 \(t\) 成立。
2. \(M\) 有平方比例列对，当且仅当存在 \(c\in\mathbb Z/3\mathbb Z\)、
   \(\gamma\in\mathbb T\)，使 \(y_{c-t}=\gamma\overline{x_t}\) 对所有 \(t\) 成立。
3. \(M\) 属于 Fourier union，当且仅当 \(\alpha(x)=0\)。在该零参数处，
   两种平方比例对恰有一种存在，存在的一种恰有三对；非零参数处，
   十五个行对与十五个列对各自至少有一个非零平方子式。

**证明。** circulant 矩阵彼此交换且正规。块乘法给出
\[
MM^*=\operatorname{diag}(XX^*+YY^*,XX^*+YY^*).
\]
每个对角块的对角条目为 \(6\)，非对角条目为
\(\alpha(x)+\alpha(y)\) 或其共轭，故 \(M\) 为单位条目 Hadamard 矩阵。

先排除同一 channel 内的行对。比较上半块第 \(i\)、\(i+d\) 行，\(d\ne0\)。
若平方成比例，则存在 \(c\in\mathbb T\) 使
\[
x_t^2=cx_{t+d}^2,\qquad
\overline{y_{-t}}^{\,2}=c\overline{y_{-t-d}}^{\,2}.
\]
因此 \(x,y\) 都满足 \(z_{t+d}^2=c^{-1}z_t^2\)。遍乘三式得 \(c^3=1\)。
取唯一的三次单位根 \(\eta\) 满足 \(\eta^{2d}=c^{-1}\)，则
\[
x_t=u\eta^t\varepsilon_t,\qquad y_t=v\eta^t\delta_t,
\qquad \varepsilon_t,\delta_t\in\{1,-1\},\quad |u|=|v|=1.
\]
三个符号的相邻乘积之和，在符号全同时为 \(3\)，否则为 \(-1\)。于是
\[
\alpha(x),\alpha(y)\in\{3\eta,-\eta\},\qquad
\alpha(x)+\alpha(y)\in\{6\eta,2\eta,-2\eta\},
\]
不可能为零。下半块行对交换 \(x,y\) 并作共轭、反向下标后得到相同矛盾。
第一列块内的列对直接给出 \(x_{t+d}^2=cx_t^2\)、\(y_{t+d}^2=cy_t^2\)，
仍是同一个符号与三次单位根论证；第二列块内的列对经共轭、反向下标亦然。
这排除了全部十二个同 channel 的行对或列对。

再比较上半块第 \(i\) 行与下半块第 \(k\) 行，令 \(d=k-i\)。
前三列的平方比例条件为
\[
x_t^2=c y_{t+d}^2.
\]
后三列条件正是其共轭再重标下标，故等价于
\[
y_{t+d}=\gamma\varepsilon_t x_t,\qquad
\gamma^2=c^{-1},\quad\varepsilon_t\in\{1,-1\}.
\]
写 \(e_t=\overline{x_t}x_{t+1}\)，得到
\[
0=\alpha(x)+\alpha(y)
 =\sum_t(1+\varepsilon_t\varepsilon_{t+1})e_t. \tag{53.1}
\]
若符号不全同，三个相邻乘积恰有一个为 \(+1\)，另外两个为 \(-1\)，
右侧就是某个单位相位的两倍，不能为零。因此符号全同，可吸收到 \(\gamma\) 中。
这证明行对判据，并且 \(\alpha(y)=\alpha(x)\)，所以二者都为零。
反过来，\(y_{t+d}=\gamma x_t\) 直接给出相应的跨 channel 平方比例行对。

对于第一列块第 \(j\) 列与第二列块第 \(k\) 列，令 \(c_0=k-j\)。
上半块条件为
\[
x_t^2=c\overline{y_{c_0-t}}^{\,2},
\]
下半块条件仍是其共轭与重标下标。因此存在符号使
\[
y_{c_0-t}=\gamma\varepsilon_t\overline{x_t}.
\]
反向下标与共轭同时出现，故相邻比值之和满足
\[
\alpha(y)=\sum_t\varepsilon_t\varepsilon_{t+1}e_t.
\]
式 (53.1) 的符号论证再次强制符号全同，并推出 \(\alpha(x)=0\)。
无符号变化的关系也直接给出平方比例列对。前两项已证。

若 \(\alpha(x)=0\)，则 \(\alpha(y)=0\)。任一单位相位三元组的三个
相邻比值之积为一，其二次基本对称式为相邻比值之和的共轭，故它们是
\[
T^3-\alpha(z)T^2+\overline{\alpha(z)}T-1
\]
的根。在零参数处，这三个比值恰为 \(1,\omega,\omega^2\)，各出现一次。
于是 \(y\) 的比值列表是 \(x\) 的比值列表的一个置换。
偶置换是循环移位，积分相邻比值得到第一项的相位循环关系；奇置换是反向移位，
积分得到第二项的反向共轭关系。两类互斥，因为三个比值互异。
相应的位移唯一：若两个位移均成立，\(x\) 将是一个 Fourier 单模，
其三个相邻比值相同，与上述互异性矛盾。每个位移对应三个跨 channel 对，
故零参数处恰有一种类型、恰有三对。

最后应用 order-six Fourier recognition。平方比例行对经列相位归一化和
一个行相位调整变成全一行与符号行；正交性强制符号行中恰有三个 \(-1\)。
归一化首列仍保留此模式。Matszangosz–Szöllősi 的 Proposition 4、Theorem 5
及 Corollary 23 将这种归一化模式刻画为 transposed Fourier family；
转置后得到列对与 Fourier family 的对应。
反向成立，因为标准 transposed Fourier 矩阵有平方比例行对，而这一性质
在任意 monomial 等价下不变。结合前面的全部行列对分析即得第三项。证毕。

上述 recognition 使用
[Matszangosz–Szöllősi, *A characterization of complex Hadamard matrices appearing in families of MUB triplets* (2024)](https://doi.org/10.1007/s10623-024-01503-w)。
配对形式与 Szöllősi 的标准形式之间的精确关系是
\[
M(x,y)\operatorname{diag}(I,-I)
 =\begin{pmatrix}X&Y^*\\Y&-X^*\end{pmatrix}
 =\begin{pmatrix}A&B\\B^*&-A^*\end{pmatrix},\qquad A=X,\ B=Y^*.
\]
若 \(A\) 的首行为 \((a,b,c)=(x_0,x_2,x_1)\)，则其原文参数
\(a/b+b/c+c/a\) 恰为 \(\alpha(x)\)；\(B\) 的参数恰为 \(\alpha(y)\)。
因此命题覆盖所有容许复参数及其判别式为零的边界，没有实分支或根互异的
先验限制，也没有把任意四个 circulant 块自动当成这种配对形式。
[Szöllősi, *A two-parameter family of complex Hadamard matrices of order 6 induced by hypocycloids*](https://arxiv.org/html/0811.3930v2)
在 Lemma 3.1 给出零参数的 Fourier 交点，并在 Theorem 2.2 后提出仅此交点的预期。
命题 53.1 用平方行列对给出相应零参数判据；其中的 Fourier recognition 属于上述文献。

### 53.2 实际 cyclic completion 的输入边与输出边

**命题 53.2。** 取 §§51–52 的实分支 \(-1<a<1\)，
\[
H_0=\frac1{\sqrt6}\begin{pmatrix}A&B\\B^*&-A^*\end{pmatrix},
\qquad A=J+(p-1)I,\quad B=J+(q-1)I,
\]
其中 \(p,q\) 和分支方向与正文相同。设
\[
v=\frac1{\sqrt6}\binom{x}{y},\qquad x,y\in\mathbb T^3,
\]
满足 \(H_0v\) 平坦且 \(v,Sv,S^2v\) 正交归一。令
\[
K=\frac1{\sqrt6}M(x,y),\qquad C=H_0K.
\]
则 \(K\) 与 \(C\) 均不属于 Fourier union。
当 \(a\ne0\) 时，\(H_0\) 也不属于 Fourier union。
因此若这样的实际 cyclic triple 在 \(a\ne0\) 处存在，
\((I,H_0,C)\) 是三条相对 Hadamard 边均在该 union 之外的 MUB triplet。

**证明。** §51 的实际构造已经给出 \(K\) 与 \(H_0K\) 的平坦性及酉性。
写
\[
H_0v=\frac1{\sqrt6}\binom{u}{z},\qquad
u=\frac{Ax+By}{\sqrt6},\quad z=\frac{B^*x-A^*y}{\sqrt6}.
\]
于是 \(u,z\in\mathbb T^3\)。\(H_0\) 与所有同步坐标置换交换，
故输出的 cyclic triple 也正交归一，且
\[
\alpha(u)+\alpha(z)=0.
\]
对三种同步 transposition \(R_j\)，酉性、交换性及正文 §51 的严格正性给出
\[
\langle H_0v,R_jH_0v\rangle
 =\langle v,R_jv\rangle>0. \tag{53.2}
\]
这里严格正性只对原来的实际输入 \(v\) 使用；没有将 \(H_0^*\) 擅自代入
实分支定理作为新的 seed。

若单位相位三元组 \(t\) 满足 \(\alpha(t)=0\)，命题 53.1 证明中的根分析表明
它的相邻比值恰为 \(1,\omega,\omega^2\)。所以恰有两个坐标相等，
第三个坐标是共同值的 \(\omega\) 或 \(\omega^2\) 倍。
三种 transposition 的内积 \(\langle t,R_jt\rangle\) 因而恰为
\(3,0,0\) 的一个排列：交换相等坐标给出 \(3\)，另外两种给出
\(1+\omega+\omega^2=0\)。

若 \(\alpha(u)=0\)，则 \(\alpha(z)=0\)。每个 channel 的上述内积最多只在
一个 transposition 处非零，两个 channel 合起来仍留下至少一个 \(R_j\) 满足
\[
\langle H_0v,R_jH_0v\rangle
 =\frac{\langle u,R_ju\rangle+\langle z,R_jz\rangle}{6}=0,
\]
与式 (53.2) 矛盾。因此 \(\alpha(u)\ne0\)。相同论证也可用于输入；
上节还给出了更强的 \(\operatorname{Re}\alpha(x)\ne0\)。

令 \(U,Z\) 分别是以 \(u,z\) 为首列的 circulant 矩阵。
由 circulant 块交换及实际乘法，
\[
U=\frac{AX+BY}{\sqrt6},\qquad
Z=\frac{B^*X-A^*Y}{\sqrt6},
\]
\[
H_0K=\frac1{\sqrt6}\begin{pmatrix}U&Z^*\\Z&-U^*\end{pmatrix}
 =\frac1{\sqrt6}M(u,z)\operatorname{diag}(I,-I).
\]
分别对 \((x,y)\)、\((u,z)\) 应用命题 53.1，即知 \(K,C\) 均在 Fourier union
之外。实际列方向下，completion 是 \(C\)，它的两条边分别为
\(C\) 与 \(H_0^*C=K\)；因此两个结论没有互相替代。
最后 \(A\) 的首列是 \((p,1,1)\)，且
\[
\alpha(p,1,1)=1+2\operatorname{Re}p=a.
\]
同一判据在 \(a\ne0\) 时排除 \(H_0\) 的两个 Fourier 方向。证毕。

[Matolcsi–Matszangosz–Varga–Weiner, *Triplets of mutually unbiased bases* (2026)](https://doi.org/10.1007/s10801-026-01506-x)
的 §4 Conjecture 1 预测所有六维 MUB triplet 都属于具有 Fourier 边的已知构造。
命题 53.2 表明，本节实际 cyclic triple 若在 \(a\ne0\) 处存在，将落在该预测之外。
这保留了一个精确的存在性问题：本节没有构造这样的 triple，也没有用该猜想
代替非存在性证明；对一般不同轨道的 common-flat 向量及第四个基仍未给出排除。
