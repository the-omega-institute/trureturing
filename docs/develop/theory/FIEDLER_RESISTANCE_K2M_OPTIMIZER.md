# 全点对电阻固定的完全二部图 K₂,ₘ Fiedler 优化

## 1. 标号图、电导与全点对电阻

**定义 1.1（正电导的标号完全二部图）。** 对每个整数 $m\ge3$，置
$n=m+2$，令 $K_{2,m}$ 的顶点为 $u,v,x_1,\ldots,x_m$，边恰为
$\{u,x_i\},\{v,x_i\}$，其中 $1\le i\le m$。分别赋予这些边电导
$a_i,b_i$，并让

$$
(a_1,\ldots,a_m,b_1,\ldots,b_m)\in(0,\infty)^{2m}
$$

独立变化。置 $s_i=a_i+b_i$、$A=\sum_i a_i$、$B=\sum_i b_i$，
并用 $a,b$ 表示对应的列向量。普通未归一化 Laplacian 为

$$
L(a,b)=
\begin{pmatrix}
A&0&-a^{\mathsf T}\\
0&B&-b^{\mathsf T}\\
-a&-b&\operatorname{diag}(s_1,\ldots,s_m)
\end{pmatrix}.
$$

其特征值按重数排列为
$0=\lambda_1<\lambda_2\le\cdots\le\lambda_n$。
对不同顶点 $p,q$，令 $h$ 满足
$h_p=1$、$h_q=0$，且 $(Lh)_z=0$ 对所有 $z\notin\{p,q\}$ 成立。
有效电阻和总电阻定义为

$$
r(p,q)=\frac1{(Lh)_p},\qquad r(p,p)=0,\qquad
R(a,b)=\sum_{\{p,q\}\subseteq V,\ p\ne q}r(p,q).
$$

最后的和对每个无序不同点对恰计一次，包括非相邻点对。
正电导保证上述调和边值问题存在唯一解，且 $(Lh)_p>0$。
若把电导写成所有无序点对上的函数 $w$，则只有
$w(\{u,x_i\})=a_i$、$w(\{v,x_i\})=b_i$ 进入 $L$ 和 $R$；
非边上的任意取值均无影响。

上述定义采用 Cruz Ortega–Menéndez-Conde，
[*Maximal algebraic connectivity for paths with fixed total resistance*,
arXiv:2306.08187v1](https://arxiv.org/pdf/2306.08187v1)，§§2–4 的
Laplacian、Rayleigh 商、调和电流与全点对约定；§5 式 (3) 的约束是
$R(a,b)=R(K_{2,m};1)$。这里还允许任意给定的 $R_0>0$。
不对 $\sum_i(a_i+b_i)$ 施加约束，也不对竞争电导施加对称条件。

## 2. 无对称假设的尖锐乘积界

**定理 2.1（全部正电导上的乘积界与等号分类）。** 对定义 1.1 中每个
$m\ge3$ 和每组独立正电导，有

$$
\lambda_2(L(a,b))R(a,b)\le C_m,
\qquad C_m=(m+2)\left(m+\frac1m\right).
$$

等号成立当且仅当存在 $t>0$ 和一个共同的
$\varepsilon\in\{+1,-1\}$，使对每个 $1\le i\le m$ 均有

$$
a_i=\frac t2\left(1+\varepsilon\sqrt{\frac{m-2}{m+2}}\right),\qquad
b_i=\frac t2\left(1-\varepsilon\sqrt{\frac{m-2}{m+2}}\right).
$$

在任一等号情形，$\lambda_2=t$，完整谱为
$0$ 一次、$t$ 共 $m$ 次、$mt$ 一次，且 $R=C_m/t$。
因此乘积等号集恰为标号边电导空间中的这两条正射线。

**证明。** 先把调和定义与谱公式接合。对任意实向量 $z$，

$$
z^{\mathsf T}Lz=\sum_{i=1}^m
\left[a_i(z_u-z_{x_i})^2+b_i(z_v-z_{x_i})^2\right].
$$

所有电导严格为正，图连通，故 $\ker L=\mathbb R\mathbf1$，
且 $L$ 在 $\mathbf1^\perp$ 上正定。固定两个不同边界点后，
在其余坐标上的 Dirichlet 二次型正定：其零向量延拓为边界零值后，
若能量为零，就必须在整个连通图上恒为零。因此线性调和方程有唯一解。
对其解 $h$，由 $\mathbf1^{\mathsf T}Lh=0$ 得到

$$
Lh=I_{pq}(e_p-e_q),\qquad
I_{pq}=(Lh)_p=h^{\mathsf T}Lh>0.
$$

令 $L^+$ 为在 $\mathbf1^\perp$ 上等于 $L^{-1}$、在常数空间上为零的
Moore–Penrose 逆。作用 $L^+$ 后，取 $p,q$ 两坐标之差，得到

$$
1=I_{pq}(e_p-e_q)^{\mathsf T}L^+(e_p-e_q),\qquad
r(p,q)=(e_p-e_q)^{\mathsf T}L^+(e_p-e_q).
$$

这是经典有效电阻恒等式，见 Ghosh–Boyd–Saberi，
[*Minimizing Effective Resistance of a Graph*, SIAM Review 50(1), 37–66](https://web.stanford.edu/~boyd/papers/pdf/eff_res.pdf)，
[DOI:10.1137/050645452](https://doi.org/10.1137/050645452)，§2.4，式 (8)。
在此采用该文的电导矩阵 $G=L$、边电导 $g_{\{u,x_i\}}=a_i$、
$g_{\{v,x_i\}}=b_i$；该文的固定总电导最小化问题不作为这里的优化结论。

全点对求和使用经典的矩阵恒等式

$$
\sum_{\{p,q\}\subseteq V,\ p\ne q}
(e_p-e_q)(e_p-e_q)^{\mathsf T}
=nI-\mathbf1\mathbf1^{\mathsf T}.
$$

于是，由 $L^+\mathbf1=0$ 以及实对称矩阵的谱分解，

$$
R=n\operatorname{tr}(L^+)=n\sum_{j=2}^{n}\frac1{\lambda_j}.
\tag{2.1}
$$

这正是上述文献 §2.5 式 (13)–(15) 及 Cruz Ortega–Menéndez-Conde §4
全点对谱公式的系数；后者谱公式之后的文字将其称为迹时漏写了因子 $n$。
这里始终使用式 (2.1) 的全点对总和。

现在令 $t=\lambda_2(L)>0$，并考察叶差空间

$$
U=\left\{z\in\mathbb R^n:
 z_u=z_v=0,\ \sum_{i=1}^m z_{x_i}=0\right\}
 \subseteq\mathbf1^\perp.
$$

它的维数为 $m-1$。取任意正交标准基 $f_1,\ldots,f_{m-1}$。
在叶坐标上，$U$ 的正交投影为
$P_U=I_m-\mathbf1_m\mathbf1_m^{\mathsf T}/m$，所以

$$
\begin{aligned}
(m-1)t
&\le\sum_{k=1}^{m-1}f_k^{\mathsf T}Lf_k\\
&=\operatorname{tr}\!\left(
\operatorname{diag}(s_1,\ldots,s_m)P_U\right)
=\frac{m-1}{m}\sum_{i=1}^m s_i.
\end{aligned}
\tag{2.2}
$$

这里第一步逐项使用 $\mathbf1^\perp$ 上的 Rayleigh 下界，没有假定
$U$ 是 $L$ 的不变子空间。由于 $m-1>0$，式 (2.2) 给出
$\sum_i s_i\ge mt$。每条边对迹贡献两次，故

$$
\operatorname{tr}L=2\sum_i s_i\ge2mt.
\tag{2.3}
$$

对 $2\le j\le n$ 定义
$q_j=\lambda_j/t-1\ge0$，并置 $Q=\sum_{j=2}^n q_j$。
共有 $m+1$ 个这样的数，且式 (2.3) 给出

$$
Q=\frac{\operatorname{tr}L}{t}-(m+1)\ge m-1>0.
$$

逐项比较分母得到

$$
\sum_{j=2}^n\frac{q_j}{1+q_j}
\ge\sum_{j=2}^n\frac{q_j}{1+Q}
=\frac{Q}{1+Q}\ge\frac{m-1}{m}.
\tag{2.4}
$$

因此

$$
\begin{aligned}
\frac{tR}{n}
&=\sum_{j=2}^n\frac1{1+q_j}
=(m+1)-\sum_{j=2}^n\frac{q_j}{1+q_j}\\
&\le m+1-\frac{m-1}{m}=m+\frac1m,
\end{aligned}
$$

证明了对全部 $2m$ 个独立正电导的上界。

下面证明等号的必要性。式 (2.4) 中后一不等式等号当且仅当
$Q=m-1$，因为 $Q/(1+Q)$ 严格递增。前一不等式等号当且仅当
每个正的 $q_j$ 都等于 $Q$。由于 $Q>0$，这等价于恰有一个正的
$q_j$，其余全为零。因此乘积等号必然要求

$$
\operatorname{Spec}(L)=\{0,t\text{（重数 }m\text{）},mt\},\qquad
\sum_i s_i=mt.
\tag{2.5}
$$

式 (2.2) 此时也取等号。$L-tI$ 在 $\mathbf1^\perp$ 上半正定，
且 $\sum_k f_k^{\mathsf T}(L-tI)f_k=0$，所以每项都为零。
半正定实对称算子的零二次型向量在其核中，故
$Lf_k=tf_k$，进而 $Lz=tz$ 对每个 $z\in U$ 成立。
特别地，任取不同的 $i,j$，把这个等式用于 $z=e_{x_i}-e_{x_j}$。
两个枢纽坐标及第 $i,j$ 个叶坐标分别给出

$$
a_i-a_j=0,\qquad b_i-b_j=0,\qquad s_i=s_j=t.
$$

所以存在两个数 $a,b>0$，使所有 $a_i=a$、所有 $b_i=b$，且 $a+b=t$。
这是从等号推出的限制，不是对竞争者的预设。

对任意这样的叶置换不变电导，令 $s=a+b$。
$U$ 上的特征值为 $s$，重数 $m-1$。其正交补由
$e_u,e_v,m^{-1/2}\sum_i e_{x_i}$ 张成，且是不变子空间。
在这组正交标准基中的矩阵为

$$
H(a,b)=
\begin{pmatrix}
ma&0&-\sqrt m\,a\\
0&mb&-\sqrt m\,b\\
-\sqrt m\,a&-\sqrt m\,b&s
\end{pmatrix}.
$$

它有零特征值，迹为 $(m+1)s$，三个二阶主子式之和为
$m^2ab+mab+mab=m(m+2)ab$。因此

$$
\det(\mu I-H)=
\mu\bigl(\mu^2-(m+1)s\mu+m(m+2)ab\bigr).
\tag{2.6}
$$

在式 (2.5) 的等号情形，$s=t$，式 (2.6) 的两个非零根必须为
$t,mt$，从而 $m(m+2)ab=mt^2$，即

$$
a+b=t,\qquad ab=\frac{t^2}{m+2}.
$$

这个二次方程恰有两组有序解，正是定理中的共同符号公式。
$m\ge3$ 保证
$0<\sqrt{(m-2)/(m+2)}<1$，故两组解不同，且每个电导严格为正。

反过来，任取 $t>0$ 和一个共同符号，按定理公式赋予所有边电导。
则 $s=t$、$ab=t^2/(m+2)$。式 (2.6) 因而有根 $0,t,mt$，
连同 $U$ 上的 $m-1$ 个特征值 $t$，给出定理所述完整谱。
由于 $m>1$，最小正特征值确为 $t$。由式 (2.1)，

$$
R=\frac{m+2}{t}\left(m+\frac1m\right)=\frac{C_m}{t}.
$$

故这两条正射线上的每一点均取等号，且前面的必要性排除了其他标号边电导。
∎

## 3. 任意电阻水平上的最大值与非对称性

**定理 3.1（固定电阻的最大值及全部最大点）。** 对每个整数 $m\ge3$
及每个 $R_0>0$，定义 1.1 的全部正电导在约束 $R(a,b)=R_0$ 下满足

$$
\max\lambda_2(L(a,b))=\frac{C_m}{R_0}.
$$

令 $t=C_m/R_0$。恰有两组标号边电导达到这个最大值：对所有 $i$，

$$
a_i=\frac t2\left(1+\varepsilon\sqrt{\frac{m-2}{m+2}}\right),\qquad
b_i=\frac t2\left(1-\varepsilon\sqrt{\frac{m-2}{m+2}}\right),
\qquad \varepsilon\in\{+1,-1\}.
$$

两组由交换 $u,v$ 互换。若电导函数还定义在非边上，非边取值任意；
“两组”只指其在 $2m$ 条标号边上的限制。

**证明。** 定理 2.1 对每个可行点给出
$\lambda_2\le C_m/R_0$。取上式的 $t=C_m/R_0>0$，
定理 2.1 的充分性给出严格正电导、谱中 $\lambda_2=t$ 及
$R=C_m/t=R_0$，故上界被达到。若一个可行点达到该上界，
则其乘积等号成立，由定理 2.1 的必要性必在所列两条射线上，
且 $R=R_0$ 将射线参数唯一固定为 $C_m/R_0$。
共同符号仅有两种，并且两者不同，故不存在其余标号边最大点。
这个存在性由显式构造给出，不要求可行集紧致，也不允许边电导取零。∎

**定理 3.2（无权电阻归一化与 K₂,₃ 的数值）。** 对每个 $m\ge3$，令
$D_m=m^3+m^2+2m+4$。无权 $K_{2,m}$ 的总电阻及该电阻水平的最大值分别为

$$
R(K_{2,m};1)=\frac{D_m}{2m},\qquad
\max_{R=R(K_{2,m};1)}\lambda_2
=\frac{2(m+2)(m^2+1)}{D_m}>2.
$$

在这个电阻水平，全部图自同构下不变的可行边电导只有无权赋值，
其 $\lambda_2=2$，所以任一最大点均不在全部自同构下不变。
特别地，$m=3$ 时 $R_0=23/3$，最大值为 $50/23$，
两组最大边电导为所有 $i$ 上的

$$
(a_i,b_i)=
\left(\frac{25+5\sqrt5}{23},\frac{25-5\sqrt5}{23}\right)
\quad\text{或}\quad
\left(\frac{25-5\sqrt5}{23},\frac{25+5\sqrt5}{23}\right).
$$

**证明。** 在定理 2.1 的式 (2.6) 中取 $a=b=1$，有 $s=2$，
二次因子为
$\mu^2-2(m+1)\mu+m(m+2)=(\mu-m)(\mu-(m+2))$。
所以无权谱为 $0$、$2$（重数 $m-1$）、$m$、$m+2$。
式 (2.1) 给出

$$
\begin{aligned}
R(K_{2,m};1)
&=(m+2)\left(\frac{m-1}{2}+\frac1m+\frac1{m+2}\right)\\
&=\frac{m^3+m^2+2m+4}{2m}.
\end{aligned}
$$

代入定理 3.1 即得所述最大值；它超过 $2$ 的差为

$$
\frac{2(m+2)(m^2+1)}{D_m}-2
=\frac{2(m-2)(m+1)}{D_m}>0.
$$

叶置换与枢纽交换都是图自同构，且它们生成的作用在边上传递，
故在全部自同构下不变的边电导必须恒为同一个数 $c>0$。
由 $L(c\mathbf1)=cL(\mathbf1)$，所有正特征值乘以 $c$，
式 (2.1) 给出 $R(c\mathbf1)=R(\mathbf1)/c$。
约束 $R=R(\mathbf1)>0$ 因而强制 $c=1$，其 $\lambda_2=2$。
这同时说明两组最大点保留叶置换对称性而破坏枢纽交换对称性。

取 $m=3$ 有 $D_3=46$、$C_3=50/3$，于是
$R_0=23/3$、$t=50/23$，并且
$\sqrt{(m-2)/(m+2)}=1/\sqrt5$。
将它们代入定理 3.1，得到所列两组电导。

既有的 $K_{2,3}$ 可行点
$a_i=32/23$、$b_i=16/23$ 及其结论
$R=23/3$、$\lambda_2=48/23$
直接采用[既有反例的完整结论](../../../Blueprint/D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.md)。
其中的标号 $0,1,2,3,4$ 在这里对应 $u,v,x_1,x_2,x_3$，
边电导和全点对电阻约定完全相同。
该可行点仍以 $48/23>2$ 排除不变最优点，而
$48/23<50/23$ 表明它不达到本定理确定的最大值。∎

## 4. 后续的完全二部图问题

**问题 4.1（三个枢纽的精确优化）。** 对每个整数 $m\ge3$，
在实际标号图 $K_{3,m}$ 上令全部 $3m$ 个边电导独立遍历正实数，
仍采用普通未归一化 Laplacian 与所有无序不同点对的总电阻。确定

$$
M_{3,m}=\sup_{c\in(0,\infty)^{3m}}
\lambda_2(L(c))R(c),
$$

并判定该上确界是否达到及全部等号边电导。
等价地，对每个 $R_0>0$，确定约束 $R(c)=R_0$ 下
$\lambda_2$ 的上确界与全部最大点。
这里不预设任一侧的置换对称性；定理 2.1–3.2 只确定 $K_{2,m}$ 的答案。

## 追加锚（本行以下为增补区）
