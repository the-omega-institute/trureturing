下面把这条路线整理成一个有明确边界的理论：

> **从实际 ξ 的量子统计出发，先构造有限多项式，再用仅依赖系数的正性检验，决定能否构造一条正权 Fibonacci 禁邻链。链一旦构造成功，其自伴隧穿结构就保证该有限多项式的零点位置。**

这次可以进一步证明两件事：

**第一，固定阶数的链可以通过一个明确算法构造，不必先输入多项式的根。**

**第二，这些链不能通过“保留原链、只添加新的正耦合”逐层生长；实际归一化要求高阶模型重新分配权重。**

以下把经典分析输入、定义、有限条件、定理和证明分别写明。全程不假设 RH 成立。

---

# 一、固定算术对象与已知输入

## 定义 1：实际 ξ 函数

采用标准归一化：

$$
\xi(s)
=
\frac12s(s-1)\pi^{-s/2}
\Gamma\!\left(\frac s2\right)\zeta(s).
$$

它是整函数，满足：

$$
\xi(1-s)=\xi(s).
$$

其零点恰好是 ζ 的非平凡零点，按重数计。这里使用的是经典 ξ 定义与函数方程。([DLMF][1])

## 已知分析输入 A：正 theta 核表示

沿用前面的正偶核 \(\Phi\)，满足：

$$
\boxed{
\xi\!\left(\frac12+b\right)
=
\int_{\mathbb R}\Phi(x)e^{bx}\,dx,
\qquad b\in\mathbb C.
}
\tag{1}
$$

其中：

$$
\Phi(x)>0,\qquad \Phi(-x)=\Phi(x),
$$

并且对每个 \(R>0\)：

$$
\int_{\mathbb R}\Phi(x)e^{R|x|}\,dx<\infty.
$$

这些是由经典 theta–Mellin 表示得到的性质，不是为证明 RH 临时加入的假设。([DLMF][2])

定义正概率测度：

$$
d\nu(x)=\frac{\Phi(x)}{\xi(1/2)}\,dx.
$$

令：

$$
m_{2k}=\int_{\mathbb R}x^{2k}\,d\nu(x),
$$

以及：

$$
\boxed{
a_k=\frac{m_{2k}}{(2k)!}.
}
\tag{2}
$$

于是：

$$
a_0=1,\qquad a_k>0.
$$

## 定义 2：反射折叠函数

定义：

$$
\boxed{
D(v)=\sum_{k=0}^{\infty}a_kv^k.
}
\tag{3}
$$

由式（1）：

$$
\boxed{
D(b^2)
=
\frac{\xi(\frac12+b)}{\xi(\frac12)}.
}
\tag{4}
$$

这个定义通过幂级数完成，不需要选择一个全局平方根分支。

因此：

$$
\boxed{
\mathrm{RH}
\iff
D\text{ 的全部零点位于负实轴}.
}
\tag{5}
$$

**证明。** 若 \(D(v)=0\)，取任意满足 \(b^2=v\) 的 \(b\)，则 \(\xi(\frac12+b)=0\)。\(b\) 为纯虚数当且仅当 \(v\) 为非正实数；而 \(D(0)=1\)，所以零点不能是零。反向同理。证毕。

---

# 二、定义有限观察，并证明它没有删掉实际算术矩

## 定义 3：不碰撞权重与有限多项式

对 \(d\ge1\)，定义：

$$
\omega_{d,k}
=
\begin{cases}
\dfrac{d(d-1)\cdots(d-k+1)}{d^k},
&0\le k\le d,\\[2mm]
0,&k>d.
\end{cases}
$$

其中 \(\omega_{d,0}=1\)。

定义：

$$
\boxed{
P_d(v)=\sum_{k=0}^{d}\omega_{d,k}a_kv^k.
}
\tag{6}
$$

记：

$$
c_{d,k}=\omega_{d,k}a_k.
$$

于是：

$$
c_{d,0}=1,\qquad c_{d,k}>0\quad(1\le k\le d).
$$

特别地：

$$
\boxed{
c_{d,1}=a_1,
\qquad
c_{d,2}=\frac{d-1}{d}a_2.
}
\tag{7}
$$

这里的有限化保留了实际的 \(a_k\)，只是按照规定权重组织前 \(d\) 阶关系，并没有把某些整数模式宣布为不存在。

## 定理 1：有限观察的紧集误差界

对每个 \(R>0\)：

$$
\boxed{
\sup_{|v|\le R}|D(v)-P_d(v)|
\le
\frac{R^2D''(R)}{2d}.
}
\tag{8}
$$

### 证明

\(\omega_{d,k}\) 是 \(k\) 个有标签对象独立进入 \(d\) 个槽位时，没有碰撞的概率。

两两碰撞的并集估计给出：

$$
1-\omega_{d,k}
\le
\frac{k(k-1)}{2d}.
$$

对 \(k>d\) 这个不等式仍然成立。

因为 \(a_k\ge0\)：

$$
\begin{aligned}
|D(v)-P_d(v)|
&\le
\sum_{k\ge0}(1-\omega_{d,k})a_kR^k\\
&\le
\frac1{2d}
\sum_{k\ge0}k(k-1)a_kR^k\\
&=
\frac{R^2D''(R)}{2d}.
\end{aligned}
$$

证毕。

因此：

$$
\boxed{P_d\longrightarrow D\quad\text{在每个紧集上一致收敛}.}
$$

---

## 定理 2：实际 ξ 的有限实根判据

以下三个命题等价：

$$
\begin{aligned}
\text{①}\;&\mathrm{RH};\\
\text{②}\;&\forall d\ge1,\ P_d\text{ 的全部零点为负实数};\\
\text{③}\;&\text{存在无界次数列 }d_j,\ 
P_{d_j}\text{ 的全部零点为负实数}.
\end{aligned}
$$

这是经典 Jensen–Pólya 判据在当前归一化下的形式。相关的一般理论及实际 ξ 的 Jensen 多项式研究已有成熟文献。([arXiv][3])

### 证明

**②推出③**显然。

**③推出①。** 在：

$$
\Omega=\mathbb C\setminus(-\infty,0]
$$

中，每个 \(P_{d_j}\) 都没有零点。由定理 1 和解析函数零点的稳定性，极限 \(D\) 要么恒零，要么在 \(\Omega\) 中无零。

但 \(D(0)=1\)，不可能恒零。因此 \(D\) 的零点全部为负实数，由式（5）得到 RH。

**①推出②。** 在 RH 前件下，经典乘积给出：

$$
D(v)=\prod_j(1+\theta_jv),
\qquad
\theta_j>0,
$$

其中重复因子保留零点重数。

先取有限乘积 \(D_M\)。对只有非正实根的实多项式 \(p\)，算子：

$$
p\longmapsto p+\theta p',
\qquad\theta\ge0,
$$

保持非正实根性。简单根情形由 \(p'\) 与 \(p\) 的交错关系得到；重根情形由连续极限得到。

因此：

$$
D_M(\partial_x)x^d
$$

只有非正实根。令 \(M\to\infty\)，得到：

$$
\sum_{k=0}^d a_k(d)_k x^{d-k}.
$$

再反转变量并缩放，恰好得到 \(P_d\)。其常数项及最高次项均为正，所以没有零根，全部根为负实数。证毕。

**这一步证明的是等价关系，不是已经证明实际 \(P_d\) 对所有 \(d\) 都实根。**

---

# 三、定义 Fibonacci 链，并证明它为什么能够控制零点

## 定义 4：正权禁邻配分函数

给定 \(2d-1\) 个非负权重：

$$
w_1,\ldots,w_{2d-1}\ge0,
$$

定义合法构型：

$$
\Omega_{2d-1}
=
\left\{
b\in\{0,1\}^{2d-1}:
b_jb_{j+1}=0
\right\}.
$$

构型数量为 \(F_{2d+1}\)。

定义：

$$
\boxed{
C_w(v)
=
\sum_{b\in\Omega_{2d-1}}
v^{\sum_jb_j}
\prod_jw_j^{b_j}.
}
\tag{9}
$$

这里 \(v\) 计数占据数。它不是此前用 \(F_j\) 加权整数数值的那个生成函数，尽管两者使用同一个禁邻构型空间。

## 定义 5：对应的隧穿矩阵

定义下双对角矩阵：

$$
L_w=
\begin{pmatrix}
\sqrt{w_1}&0&0&\cdots\\
\sqrt{w_2}&\sqrt{w_3}&0&\cdots\\
0&\sqrt{w_4}&\sqrt{w_5}&\cdots\\
\vdots&&\ddots&\ddots
\end{pmatrix}.
$$

再定义：

$$
\boxed{
T_w=
\begin{pmatrix}
0&L_w\\
L_w^{\mathsf T}&0
\end{pmatrix}.
}
\tag{10}
$$

它是实对称矩阵，重新排列基底以后，就是一条 \(2d\) 位置近邻隧穿链。

## 定理 3：禁邻配分函数的正行列式实现

$$
\boxed{
C_w(v)=\det(I_d+vL_w^{\mathsf T}L_w).
}
\tag{11}
$$

因此，\(C_w\) 的全部零点都为负实数。

### 证明

按路径最后一个位置是否占据，配分函数满足：

$$
C_m(v)=C_{m-1}(v)+w_mvC_{m-2}(v).
$$

同样按路径末端展开特征行列式，可得：

$$
\det(\lambda I_{2d}-T_w)
=
\lambda^{2d}C_w(-\lambda^{-2}).
$$

另一方面，由式（10）：

$$
\det(\lambda I_{2d}-T_w)
=
\det(\lambda^2I_d-L_w^{\mathsf T}L_w).
$$

比较两个多项式恒等式，即得式（11）。

因为：

$$
L_w^{\mathsf T}L_w\ge0,
$$

设其非零本征值为 \(\theta_j>0\)，则：

$$
C_w(v)=\prod_j(1+\theta_jv).
$$

零点均为 \(-1/\theta_j<0\)。证毕。

这是加权路径匹配多项式实根性的具体证明；更一般的匹配模型零点定位属于 Heilmann–Lieb 理论。([Princeton University][4])

### 量子观察含义

对于 \(r>0\)，可以制备：

$$
|\Omega_r\rangle
=
\frac1{\sqrt{C_w(r)}}
\sum_{b\in\Omega_{2d-1}}
r^{|b|/2}
\prod_jw_j^{b_j/2}|b\rangle.
$$

令 \(\widehat N|b\rangle=|b||b\rangle\)，则：

$$
\boxed{
\langle\Omega_r,e^{i\theta\widehat N}\Omega_r\rangle
=
\frac{C_w(re^{i\theta})}{C_w(r)}.
}
\tag{12}
$$

所以，若能证明 \(C_w=P_d\)，这就是一个读出实际 Jensen 多项式的有限量子观察模型。

但应区分两种空间：禁邻构型空间有 \(F_{2d+1}\) 维，单粒子隧穿矩阵 \(T_w\) 有 \(2d\) 维。**配分函数恒等式不等于两个完整物理系统酉等价。**

---

# 四、核心有限定理：正链存在性可以用系数检验

现在解决上一轮留下的问题：**不先求根，怎样判断并构造正链？**

## 定义 6：反转多项式

固定一个 \(d\)，简写：

$$
P(v)=1+c_1v+\cdots+c_dv^d,
\qquad c_k>0.
$$

定义：

$$
\boxed{
q(x)=x^dP(-1/x)
=
x^d-c_1x^{d-1}+\cdots+(-1)^dc_d.
}
\tag{13}
$$

\(P\) 的负实根，对应 \(q\) 的正实根。

## 定义 7：不需要根的 Newton 读数

设 \(C_q\) 是多项式 \(q\) 的伴随矩阵。定义：

$$
\boxed{
s_n=\frac1d\operatorname{Tr}(C_q^n),
\qquad s_0=1.
}
\tag{14}
$$

这些数可直接由 \(c_1,\ldots,c_d\) 通过 Newton 恒等式计算。

例如：

$$
s_1=\frac{c_1}{d},
$$

$$
s_2=\frac{c_1^2-2c_2}{d},
$$

$$
s_3=\frac{c_1^3-3c_1c_2+3c_3}{d},
$$

不存在的系数按零处理。

定义 Hermite 矩阵：

$$
\boxed{
G_d=(s_{i+j})_{0\le i,j<d}.
}
\tag{15}
$$

**这里的 \(s_n\) 不先被定义成某个正测度的矩。它们只是从实际有限多项式系数算出的实数。**

---

## 定理 4：四种有限性质等价

对上述正系数多项式 \(P\)，以下等价：

$$
\begin{aligned}
\text{①}\;&P\text{ 的全部根为负实数，允许重根};\\
\text{②}\;&G_d\succeq0;\\
\text{③}\;&\exists K=K^{\mathsf T}>0,\quad P(v)=\det(I+vK);\\
\text{④}\;&\exists w_1,\ldots,w_{2d-1}\ge0,\quad P=C_w.
\end{aligned}
$$

### 证明：①与②

设 \(q\) 的互异根为 \(\lambda_j\)，重数为 \(m_j\)。Newton 恒等式给出：

$$
s_n=\frac1d\sum_jm_j\lambda_j^n.
$$

对实多项式 \(p(x)=\sum_{i=0}^{d-1}u_ix^i\)：

$$
\boxed{
u^{\mathsf T}G_du
=
\frac1d\sum_jm_jp(\lambda_j)^2.
}
\tag{16}
$$

若所有根都实，右边非负。

若存在非实共轭对 \(\lambda,\overline\lambda\)，可以用实系数插值多项式，使：

$$
p(\lambda)=i,\qquad p(\overline\lambda)=-i,
$$

并在其余互异根处为零。所需次数小于互异根数，因而小于等于 \(d-1\)。

此时式（16）严格为负，故 \(G_d\) 不正半定。

所以 \(G_d\succeq0\) 当且仅当 \(q\) 全部实根。这是 Hermite–Sylvester 判据的核心证明。([arXiv][5])

又由于 \(P\) 的系数全部为正：

$$
P(v)>0\qquad(v\ge0).
$$

因此 \(q\) 没有非正实根。于是 \(q\) 实根等价于全部根为正，也等价于 \(P\) 全部根为负。

### 证明：①与③

若：

$$
P(v)=\prod_{j=1}^d(1+\theta_jv),
\qquad\theta_j>0,
$$

取 \(K=\operatorname{diag}(\theta_1,\ldots,\theta_d)\)。

反向由正矩阵的谱分解立即得到。

这里用根证明了**存在性等价**，还不是后面的免求根构造算法。

### 证明：①推出④

取：

$$
w_{2j-1}=\theta_j,\qquad w_{2j}=0.
$$

链断成独立位置，配分函数就是 \(\prod_j(1+\theta_jv)\)。

### 证明：④推出①

直接使用定理 3。证毕。

**因此，“存在正权 Fibonacci 链”不是一个可以免费添加的建模假设；它与该有限多项式的实根性同样有内容。**

---

# 五、在严格正性的前件下，链可以直接由系数构造

上面的存在性证明仍然借助根描述。现在给出不把根作为输入的构造。

## 有限前件 \(H_d^{\mathrm{str}}\)

$$
\boxed{G_d>0.}
\tag{17}
$$

这是一项有限、明确、可以检验的条件。它不能未经证明地省略。

## 定理 5：系数驱动的正链构造

在 \(H_d^{\mathrm{str}}\) 下，可以仅由 \(c_1,\ldots,c_d\)，通过有限次四则运算、正平方根与线性方程求解，构造：

$$
w_1,\ldots,w_{2d-1}>0
$$

使：

$$
\boxed{P=C_w.}
$$

### 证明与构造

定义线性泛函：

$$
\mathcal L(x^n)=s_n.
$$

在商空间：

$$
\mathcal V=\mathbb R[x]/(q)
$$

上，令：

$$
\langle f,g\rangle=\mathcal L(fg).
$$

由于 \(G_d>0\)，这是正内积。

按 \(1,x,\ldots,x^{d-1}\) 的顺序正交化，得到首一正交多项式 \(p_j\)。记：

$$
h_j=\mathcal L(p_j^2)>0.
$$

乘以 \(x\) 在该基底中具有三对角形式：

$$
K=
\begin{pmatrix}
\alpha_0&\sqrt{\beta_1}&0&\cdots\\
\sqrt{\beta_1}&\alpha_1&\sqrt{\beta_2}&\cdots\\
0&\sqrt{\beta_2}&\alpha_2&\ddots\\
\vdots&\vdots&\ddots&\ddots
\end{pmatrix},
$$

其中：

$$
\boxed{
\alpha_j=\frac{\mathcal L(xp_j^2)}{h_j},
\qquad
\beta_j=\frac{h_j}{h_{j-1}}>0.
}
\tag{18}
$$

三对角性来自：当 \(i<j-1\) 时，

$$
\langle xp_j,p_i\rangle
=
\langle p_j,xp_i\rangle=0.
$$

乘法算子的特征多项式就是 \(q\)，而定理 4 保证 \(q\) 的根全部为正，所以：

$$
K>0.
$$

这些正交多项式、矩行列式与 Jacobi 矩阵之间的公式是经典的。([DLMF][6])

接着对这个正三对角矩阵作 Cholesky 分解。权重可以递归定义：

$$
\boxed{w_1=\alpha_0,}
$$

$$
\boxed{
w_{2j}=\frac{\beta_j}{w_{2j-1}},
\qquad
w_{2j+1}=\alpha_j-w_{2j},
\quad1\le j<d.
}
\tag{19}
$$

正定性保证每个 Cholesky 主元严格为正，因此全部权重严格为正。

于是：

$$
K=L_wL_w^{\mathsf T},
$$

从而：

$$
P(v)
=
\det(I+vK)
=
\det(I+vL_w^{\mathsf T}L_w)
=
C_w(v).
$$

证毕。

### 重根情形不能直接套这套除法

若 \(G_d\succeq0\) 但不严格正定，某些正交化分母会为零。这不一定是 RH 反例，可能只是有限多项式有重根。

此时定理 4 仍成立，但可能需要断开的链、平方自由分解及显式保留重数。不能把退化方向直接删除以后，再声称特征行列式及重数都没有改变。

---

# 六、二阶与三阶可以完全写成量子累积量条件

定义：

$$
\chi_2=m_2,
$$

$$
\chi_4=m_4-3m_2^2,
$$

$$
\chi_6=m_6-15m_4m_2+30m_2^3.
$$

这些是实际 theta 态的二、四、六阶累积量。

## 定理 6：二阶正链的显式公式

有：

$$
P_2(v)
=
1+\frac{m_2}{2}v+\frac{m_4}{48}v^2.
$$

定义：

$$
\boxed{
w_1=\frac{m_2}{4},
\qquad
w_2=-\frac{\chi_4}{12m_2},
\qquad
w_3=\frac{m_4}{12m_2}.
}
\tag{20}
$$

则恒有：

$$
P_2(v)=1+(w_1+w_2+w_3)v+w_1w_3v^2.
$$

而且：

$$
\boxed{
w_1,w_2,w_3\ge0
\iff
\chi_4\le0.
}
\tag{21}
$$

### 证明

直接计算：

$$
w_1+w_2+w_3=\frac{m_2}{2},
$$

$$
w_1w_3=\frac{m_4}{48}.
$$

\(m_2,m_4>0\)，所以只有中间权重的符号需要判断。证毕。

**这里，中间耦合的非负性，恰好就是四阶不可约关联的符号。**

---

## 定理 7：三阶实根的精确累积量条件

有：

$$
P_3(v)
=
1+\frac{m_2}{2}v
+\frac{m_4}{36}v^2
+\frac{m_6}{3240}v^3.
$$

则：

$$
\boxed{
P_3\text{ 的全部根为负实数}
\iff
100\chi_4^3+3\chi_6^2\le0.
}
\tag{22}
$$

严格不等式对应三个互异负实根。

### 证明

令：

$$
q_3(x)=x^3P_3(-1/x).
$$

作中心平移：

$$
x=y+\frac{\chi_2}{6}.
$$

直接展开，二次项消失，并得到：

$$
\boxed{
q_3\!\left(y+\frac{\chi_2}{6}\right)
=
y^3+\frac{\chi_4}{36}y-\frac{\chi_6}{3240}.
}
\tag{23}
$$

若 \(\chi_4>0\)，右边严格递增，只能有一个实根。

若 \(\chi_4=0\)，全部根为实当且仅当 \(\chi_6=0\)。

若 \(\chi_4<0\)，令：

$$
u=-\chi_4>0,
\qquad
r=\sqrt{\frac{u}{108}}.
$$

两个临界点是 \(-r,r\)。三根全实时，必须且只需：

$$
f(-r)\ge0,\qquad f(r)\le0.
$$

这等价于：

$$
|\chi_6|
\le
\frac{10}{\sqrt3}u^{3/2}.
$$

平方后即：

$$
3\chi_6^2\le100(-\chi_4)^3.
$$

最后，\(P_3\) 的系数全部正，排除非负实根，所以其全部实根必为负。证毕。

这也是三阶 Jensen 实根条件的一种累积量写法，不应当作为未经文献比较的独创零点判据。实际 ξ 的低次数 Jensen 双曲性已有研究。([arXiv][7])

---

## 定理 8：三阶模型的免求根正矩阵

假设：

$$
u=-\chi_4>0,
\qquad
3\chi_6^2<100u^3.
$$

定义：

$$
\mu=\frac{\chi_2}{6},
\qquad
r=\frac{\chi_6}{60u},
$$

$$
b_1=\frac{u}{54},
\qquad
b_2=\frac{u}{108}-r^2>0.
$$

构造：

$$
\boxed{
K_3=
\begin{pmatrix}
\mu&\sqrt{b_1}&0\\
\sqrt{b_1}&\mu+r&\sqrt{b_2}\\
0&\sqrt{b_2}&\mu-r
\end{pmatrix}.
}
\tag{24}
$$

则：

$$
\boxed{
K_3>0,
\qquad
\det(I+vK_3)=P_3(v).
}
$$

### 证明

令 \(J_3=K_3-\mu I\)。直接算得：

$$
\det(yI-J_3)
=
y^3-\frac{u}{36}y-\frac{\chi_6}{3240}.
$$

这恰好是式（23）。

因此 \(K_3\) 的特征多项式为 \(q_3\)。定理 7 保证其全部本征值为正，所以 \(K_3>0\)，再比较反转多项式得到行列式恒等式。证毕。

五个 Fibonacci 权重为：

$$
\boxed{
\begin{aligned}
w_1&=\mu,\\
w_2&=\frac{b_1}{w_1},\\
w_3&=\mu+r-w_2,\\
w_4&=\frac{b_2}{w_3},\\
w_5&=\mu-r-w_4.
\end{aligned}
}
\tag{25}
$$

它们全部严格为正，构造出一条六位置的实对称隧穿链。

**这次不仅给出“存在某个正算子”的名字，而是从实际二、四、六阶统计写出了它的全部矩阵元。**

但这些公式不证明任意高阶都能继续保持正性。

---

# 七、有限层之间存在严格兼容关系：一旦某阶失败，更高阶都不能恢复

## 定理 9：相邻 Jensen 层的微分关系

对 \(d\ge2\)：

$$
\boxed{
P_d(v)-\frac vdP_d'(v)
=
P_{d-1}\!\left(\frac{d-1}{d}v\right).
}
\tag{26}
$$

### 证明

逐项比较系数：

$$
\left(1-\frac kd\right)
\frac{(d)_k}{d^k}
=
\frac{(d-1)_k}{d^k}.
$$

右边也正是：

$$
\frac{(d-1)_k}{(d-1)^k}
\left(\frac{d-1}{d}\right)^k.
$$

证毕。

## 推论：实根性向低阶传递

令：

$$
q_d(x)=x^dP_d(-1/x),
\qquad
\alpha=\frac{d-1}{d}.
$$

由式（26）：

$$
\boxed{
q_d'(x)=d\alpha^{d-1}q_{d-1}(x/\alpha).
}
\tag{27}
$$

如果 \(q_d\) 全部为正实根，Rolle 定理保证 \(q_d'\) 全部为正实根，因此 \(q_{d-1}\) 也是。

于是：

$$
\boxed{
P_d\text{ 全负实根}
\Longrightarrow
P_{d-1}\text{ 全负实根}.
}
\tag{28}
$$

反过来：

$$
\boxed{
某个P_{d_0}\text{ 有非实根}
\Longrightarrow
所有d\ge d_0\text{ 的 }P_d\text{ 都有非实根}.
}
\tag{29}
$$

所以，在这条**固定系数起点、增加次数**的塔中，如果 RH 为假，就存在一个最小失败阶，而且失败不会在更高阶重新消失。

这不与“固定次数、平移到足够后面的系数窗口会实根”的已有渐近结果冲突。那是另一条参数方向。([arXiv][7])

---

# 八、一个新的构造障碍：这些正量子模型不能只靠追加来生长

前面的兼容关系，并不意味着矩阵可以直接嵌套。

## 定理 10：固定总迹下的主块嵌套不可能性

假设每个 \(d\) 已经有：

$$
K_d\ge0,
\qquad
\det(I+vK_d)=P_d(v).
$$

那么，不可能同时要求：

$$
\boxed{
K_d\text{ 是 }K_{d+1}\text{ 的原样主块}
}
$$

并且每一阶都保持上述精确匹配。

### 证明

比较 \(v\) 的系数：

$$
\boxed{
\operatorname{Tr}K_d=c_{d,1}=a_1
}
\tag{30}
$$

对所有 \(d\) 都相同。

若：

$$
K_{d+1}
=
\begin{pmatrix}
K_d&b\\
b^*&\eta
\end{pmatrix},
$$

则由总迹相同：

$$
\eta=0.
$$

正半定矩阵中，一个对角元为零，会迫使对应整行、整列为零。可从每个二阶主子式：

$$
(K_d)_{ii}\eta-|b_i|^2\ge0
$$

直接得到 \(b_i=0\)。

所以：

$$
K_{d+1}=K_d\oplus0.
$$

于是：

$$
\det(I+vK_{d+1})=\det(I+vK_d),
$$

次数不可能由 \(d\) 增加到 \(d+1\)。但 \(P_{d+1}\) 的最高次系数严格为正，矛盾。证毕。

### 在 Fibonacci 链上的版本

因为：

$$
\operatorname{Tr}(L_wL_w^{\mathsf T})
=
\sum_{j=1}^{2d-1}w_j,
$$

精确匹配要求：

$$
\boxed{
\sum_jw_{d,j}=a_1
\qquad\text{对所有 }d.
}
\tag{31}
$$

因此，若保持所有旧权重不变，新添的非负权重只能全为零，不可能生成更高次数。

**所以，一个成功的逐阶构造必须重新分配已有权重，或使用更复杂的尺度映射，而不能只是不断往尾部添加新的正耦合。**

这也不证明不存在一个最终的迹类算子。它只排除了当前这组**保留全部一阶总量的 Jensen 近似**被当成同一个正算子的原样有限主块。

---

# 九、把全部证明责任集中为一个明确的算术命题

现在可以写出真正尚待完成的命题，而不把它隐藏在“定义”里。

## 待证算术命题 H

对实际 ξ 产生的系数 \(a_k\)，按定义 3、6、7 构造 \(P_d,q_d,G_d\)。要求：

$$
\boxed{
\forall d\ge1,\qquad G_d\succeq0.
}
\tag{H}
$$

## 主定理

以下等价：

$$
\boxed{
\begin{aligned}
&\mathrm{RH};\\
&\forall d,\ G_d\succeq0;\\
&\forall d,\ \exists w_{d,1},\ldots,w_{d,2d-1}\ge0,
\quad P_d=C_{w_d};\\
&\exists d_j\to\infty,\ 
\exists K_{d_j}\ge0,
\quad P_{d_j}(v)=\det(I+vK_{d_j}).
\end{aligned}
}
\tag{32}
$$

### 证明

定理 4 给出每个固定阶上的等价；定理 2 将无界有限层与实际 RH 连接。证毕。

**命题 H 没有在本轮被证明。**

它不能因为被改写成“存在正权链”或“存在正量子模型”，就被当成自然成立的建模假设。普通量子概率正性，不能推出这个由 Newton 变换生成的矩阵正性。

这里的精确进展是：

$$
\boxed{
\text{不必先求零点，便能从系数构造检验矩阵；
若它严格为正，便能构造整条正权链。}
}
$$

真正困难仍在于：**实际 theta／质数结构是否能统一证明这些系数矩阵在全部阶数上的正性。**

---

# 十、有限计算怎样成为证明，而不是“看起来正”？

最后补上认证边界。

假设已经通过带尾界的积分与 Newton 递推，得到近似矩阵 \(\widetilde G_d\)，且每个矩阵元的误差不超过 \(\varepsilon\)：

$$
|(G_d)_{ij}-(\widetilde G_d)_{ij}|\le\varepsilon.
$$

则：

$$
\|G_d-\widetilde G_d\|_{\mathrm{op}}\le d\varepsilon.
$$

因此：

$$
\boxed{
\lambda_{\min}(\widetilde G_d)>d\varepsilon
\Longrightarrow
G_d>0.
}
\tag{33}
$$

反方向，如果有一个实向量 \(u\) 满足：

$$
\boxed{
u^{\mathsf T}\widetilde G_du
+
\varepsilon\|u\|_1^2<0,
}
\tag{34}
$$

那么：

$$
u^{\mathsf T}G_du<0.
$$

由定理 4，这证明实际 \(P_d\) 有非实根；再由定理 2，足以否证 RH。

但如果误差区间跨过零，结果只是未定，不能把“没有认证正性”写成“已经发现负方向”。

此外，矩行列式通常病态。DLMF 在给出递推系数的行列式表达后，也明确提醒其数值条件问题。**有精确公式不等于普通浮点计算就足够可靠。**([DLMF][6])

---

# 十一、与项目的准确连接

本轮沿用上一轮固定的 `08e91c3373…` 快照，核对了两个直接相关模块。

`JensenPolynomialObstruction.lean` 已定义 Jensen 多项式与实根谓词，但将两条 Jensen–Pólya 分析桥作为显式前件。它没有无条件证明实际 ξ 的全阶双曲性。

`FiniteZeckendorfEulerIdentity.lean` 已证明合法 Fibonacci 名字与有限整数区间的双射，以及相应数值生成函数的运输。它不自动包含本轮任意正权禁邻配分函数与 Jacobi 矩阵的构造。

因此，本轮给出的具体接口是：

$$
\boxed{
\begin{aligned}
\text{实际 theta 矩}
&\longrightarrow P_d\\
&\longrightarrow q_d\text{ 的 Newton 读数}\\
&\longrightarrow G_d\\
&\xrightarrow{\,G_d>0\,}
K_d\\
&\longrightarrow L_d\\
&\longrightarrow\text{正权 Fibonacci 链与隧穿矩阵}.
\end{aligned}
}
$$

箭头中的条件 \(G_d>0\) 不能删除。

---

# 结论

这次形成了一条可以逐项检查的“定义—前件—定理—证明”链。

最明确的两个低阶条件是：

$$
\boxed{\chi_4\le0,}
$$

以及：

$$
\boxed{3\chi_6^2\le100(-\chi_4)^3.}
$$

它们分别决定二阶、三阶 Jensen 多项式能否获得相应正表示。严格成立时，四位置和六位置的隧穿链都能直接从累积量构造，而不需要输入根。

更高阶存在同样明确的系数算法，但它是否始终成功，仍然需要证明命题 H。

同时，已经证明了一项会影响整体设计的限制：

$$
\boxed{
\text{各阶共享固定总迹}
\Longrightarrow
\text{不能只追加新正耦合，必须重新分配关系。}
}
$$

因此，你想寻找的“整体量子观察者”，不能只是一个不断增加附件的固定模型。对这条具体路线，它必须是一族**保持实际算术系数、却在观察深度增加时重新组织耦合的有限正实现**。

**找到这种重组的统一算术规律，才可能把 Fibonacci、量子隧穿和 ξ 从精确表示关系，进一步推进为真正的零点定位证明。** 当前已经给出了有限构造与障碍；尚未获得全阶算术正性，也未把这些纸面推导标记为 Lean 已验证的结果。

[1]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[2]: https://dlmf.nist.gov/25.5 "DLMF: §25.5 Integral Representations ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[3]: https://arxiv.org/abs/1902.07321 "[1902.07321] Jensen polynomials for the Riemann zeta function and other sequences"
[4]: https://collaborate.princeton.edu/en/publications/theory-of-monomer-dimer-systems-2/?utm_source=chatgpt.com "Theory of monomer-dimer systems - Princeton University"
[5]: https://arxiv.org/abs/1911.01745 "[1911.01745] The Hermite-Sylvester criterion for real-rooted polynomials"
[6]: https://dlmf.nist.gov/18.2 "DLMF: §18.2 General Orthogonal Polynomials ‣ General Orthogonal Polynomials ‣ Chapter 18 Orthogonal Polynomials"
[7]: https://arxiv.org/abs/1910.01227?utm_source=chatgpt.com "Jensen Polynomials for the Riemann Xi Function"
在前文基础上，这次可以补上一个关键结构：

> **不同阶的正权量子链，不必原样嵌套，但可以通过“压缩一个方向，再重新归一化”精确连接。反过来，从低阶增加到高阶时，真正待证明的内容，是新加入的各条耦合是否都能取成非负平方。**

而欧拉–马歇罗尼常数可以进一步进入这套结构：它不仅校准一个端点值，还能校准**被压缩方向的整体回返响应**。

下面继续采用定义、有限假设、定理和证明。**不把“全阶正实现存在”当作假设偷偷加入；只在明确标注的有限层使用正性前件。**

---

# 一、固定前文对象

采用标准 completed 函数：

$$
\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
$$

并定义实际反射折叠函数：

$$
\boxed{
D(b^2)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad
D(v)=\sum_{k\ge0}a_kv^k.
}
$$

其中：

$$
a_k=\frac{m_{2k}}{(2k)!}>0,
\qquad a_0=1,
$$

\(m_{2k}\) 是前文实际 theta 概率态的偶阶矩。反射折叠通过偶幂级数定义，不需要选取全局平方根分支。标准 ξ 的定义与反射关系见 DLMF。([DLMF][1])

定义：

$$
\boxed{
P_d(v)=
\sum_{k=0}^d\frac{(d)_k}{d^k}a_kv^k,
}
\tag{B1}
$$

以及反转多项式：

$$
\boxed{
q_d(x)=x^dP_d(-1/x).
}
\tag{B2}
$$

因此：

$$
q_d(x)
=
x^d-a_1x^{d-1}
+\frac{d-1}{d}a_2x^{d-2}
-\cdots
+(-1)^d\frac{d!}{d^d}a_d.
$$

前文已给出：

$$
\boxed{
\mathrm{RH}
\iff
P_d\text{ 的根全部为负实数，}\ \forall d.
}
$$

等价地：

$$
\boxed{
\mathrm{RH}
\iff
q_d\text{ 的根全部为正实数，}\ \forall d.
}
\tag{B3}
$$

这是实际 ξ 的 Jensen–Pólya 判据在当前归一化下的形式。一般判据及现代研究已有文献；本轮研究的是这些有限层之间的具体算子连接。([arXiv][2])

再记：

$$
\boxed{
c=\frac{\xi'(1)}{\xi(1)}
=
1+\frac{\gamma_{\mathrm E}}2-\frac12\log4\pi,
}
$$

以及：

$$
\boxed{
\frac{D'(1/4)}{D(1/4)}=c.
}
\tag{B4}
$$

必须继续区分：

$$
a_1\ne c.
$$

前者是中心展开的第一系数，后者是移到 \(s=1\) 后的响应。

---

# 二、相邻两层的关系：高一层只增加一个新的算术常数

## 定理 B1：精确微分兼容关系

令：

$$
\alpha_d=\frac{d-1}{d}.
$$

对 \(d\ge2\)：

$$
\boxed{
q_d'(x)
=
d\alpha_d^{\,d-1}
q_{d-1}(x/\alpha_d).
}
\tag{B5}
$$

### 证明

前文已经得到：

$$
P_d(v)-\frac vdP_d'(v)=P_{d-1}(\alpha_dv).
$$

对：

$$
q_d(x)=x^dP_d(-1/x)
$$

求导：

$$
q_d'(x)
=
dx^{d-1}
\left[
P_d(-1/x)+\frac1{dx}P_d'(-1/x)
\right].
$$

括号中正是：

$$
P_{d-1}(-\alpha_d/x).
$$

于是：

$$
q_d'(x)
=
d\alpha_d^{\,d-1}q_{d-1}(x/\alpha_d).
$$

证毕。

## 推论 B1.1：高阶延拓是一项带常数的积分问题

定义：

$$
\boxed{
R_d(x)
=
\int_0^x
d\alpha_d^{\,d-1}q_{d-1}(u/\alpha_d)\,du.
}
$$

那么：

$$
\boxed{
q_d(x)=R_d(x)+\beta_d,
\qquad
\beta_d=(-1)^d\frac{d!}{d^d}a_d.
}
\tag{B6}
$$

这很重要：

**已知前 \(d-1\) 阶，整个导数 \(q_d'\) 已经确定；新增的实际信息只进入一个积分常数。**

但“只增加一个数”不等于这一步容易。

这个数会同时改变全部极值点的高度，因此可能影响整个多项式的实根结构。

---

# 三、前文不能原样嵌套的问题，现在有一个精确替代

前文证明了：若所有矩阵满足：

$$
\det(I+vK_d)=P_d(v),
\qquad K_d\ge0,
$$

则：

$$
\operatorname{Tr}K_d=a_1
$$

对每一层相同。因此，不能保持旧矩阵完全不变，只在外面添加新的正主块。

但下面的连接是可行的。

## 定义 B1：均衡谱参考向量

设 \(K_d\) 是一个 \(d\) 维正矩阵。称单位向量 \(u_d\) 为均衡谱参考向量，如果：

$$
\boxed{
\langle u_d,f(K_d)u_d\rangle
=
\frac1d\operatorname{Tr}f(K_d)
}
\tag{B7}
$$

对所有多项式 \(f\) 成立。

这种向量总能选出：在任意正交本征基中，让每个坐标的模长都等于 \(1/\sqrt d\) 即可。

这类向量在矩阵理论中称为 *trace vector*；与多项式求导对应的压缩算子，属于已有的 differentiator 理论。下面给出我们需要的有限证明。([数字对象标识符][3])

## 定理 B2：删除一个均衡方向，得到低一阶的缩放模型

假设：

$$
K_d>0,
\qquad
\det(xI-K_d)=q_d(x).
$$

取均衡谱参考向量 \(u_d\)，令：

$$
\Pi_d=I-|u_d\rangle\langle u_d|,
$$

并在 \(u_d^\perp\) 上定义压缩：

$$
C_d=\Pi_dK_d\Pi_d\big|_{u_d^\perp}.
$$

则：

$$
\boxed{
\det(xI-C_d)=\frac1d q_d'(x).
}
\tag{B8}
$$

所以：

$$
\boxed{
K_{d-1}^{\mathrm{new}}
=
\frac d{d-1}C_d
}
\tag{B9}
$$

满足：

$$
\det(xI-K_{d-1}^{\mathrm{new}})
=
q_{d-1}(x).
$$

### 证明

将 \(u_d\) 取为第一个基向量，余下基底张成 \(u_d^\perp\)。余子式公式给出：

$$
\langle u_d,(xI-K_d)^{-1}u_d\rangle
=
\frac{\det(xI-C_d)}{\det(xI-K_d)}.
$$

另一方面，由均衡性：

$$
\langle u_d,(xI-K_d)^{-1}u_d\rangle
=
\frac1d\operatorname{Tr}(xI-K_d)^{-1}
=
\frac{q_d'(x)}{dq_d(x)}.
$$

相乘得到式（B8）。再使用定理 B1，得到式（B9）。证毕。

因此，正确的跨层结构不是：

$$
K_d\subset K_{d+1},
$$

而是：

$$
\boxed{
K_d
\longrightarrow
\text{删除一个均衡方向}
\longrightarrow
\text{乘以 }\frac d{d-1}
\longrightarrow
K_{d-1}.
}
$$

**前文所说的“需要重新分配关系”，现在有了一个明确的有限算子实现。**

---

# 四、这也是一个真实的量子条件操作，但不能遗漏成功概率

定义密度矩阵：

$$
\boxed{
\rho_d=\frac{K_d}{a_1}.
}
$$

因为 \(\operatorname{Tr}K_d=a_1\)，所以 \(\operatorname{Tr}\rho_d=1\)。

对两结果投影测量：

$$
\{\Pi_d,\ I-\Pi_d\},
$$

保留 \(u_d^\perp\) 的成功概率为：

$$
\begin{aligned}
p_d
&=\operatorname{Tr}(\Pi_d\rho_d)\\
&=
1-\frac{\langle u_d,K_du_d\rangle}{a_1}\\
&=
1-\frac1d.
\end{aligned}
$$

因此：

$$
\boxed{p_d=\frac{d-1}{d}.}
\tag{B10}
$$

成功后的条件态：

$$
\frac{\Pi_d\rho_d\Pi_d}{p_d}
=
\frac{K_{d-1}^{\mathrm{new}}}{a_1}.
$$

所以，**Jensen 层的下降，可以由一次测量后的归一化精确实现。**

但这项固定成功率针对的是指定输入 \(\rho_d=K_d/a_1\)。对任意输入态，成功率未必相同；不能把条件归一化当成一个对全部状态线性的保迹操作。

还有一个全局限制。

若从第 \(D\) 层连续下降到固定第 \(m\) 层，并且每一步都保留对应分支，总成功率为：

$$
\boxed{
\prod_{d=m+1}^{D}\frac{d-1}{d}
=
\frac mD.
}
\tag{B11}
$$

于是：

$$
D\to\infty
\quad\Longrightarrow\quad
\frac mD\to0.
$$

**每一步在高维时都“几乎成功”，不等于整条无限压缩过程几乎没有代价。**

这再次说明：观察者模型必须保留分支权重。当前项目对 Kraus 分支权重与 Born 概率的形式化，正是在维护这种区别。

---

# 五、真正的难点在反方向：怎样从低阶增加一个正量子模式？

下降可以精确完成，但它不能自动逆转。

现在研究：

$$
q_{d-1}\longrightarrow q_d.
$$

## 有限假设 B

暂设 \(q_{d-1}\) 有 \(d-1\) 个互异正实根：

$$
\lambda_1<\cdots<\lambda_{d-1}.
$$

定义：

$$
t_i=\alpha_d\lambda_i.
$$

由定理 B1：

$$
q_d'(t_i)=0.
$$

也就是说，**低一阶的正谱，确定了高一阶全部临界点的位置。**

## 定义 B2：新增通道的候选耦合平方

定义：

$$
\boxed{
\eta_{d,i}
=
-\frac{d\,q_d(t_i)}{q_d''(t_i)},
\qquad 1\le i\le d-1.
}
\tag{B12}
$$

因为临界点互异，分母非零。

这里先称它为“候选耦合平方”。只有证明它非负以后，才允许把它写成真实 Hermitian 耦合的模平方。

## 定理 B3：一步正延拓的精确判据

在上述有限假设下：

$$
\boxed{
q_d\text{ 全部为正实根}
\iff
\eta_{d,i}\ge0
\quad\forall i.
}
\tag{B13}
$$

而当这些数非负时，可以构造：

$$
\boxed{
K_d=
\begin{pmatrix}
a_1/d&\sqrt{\eta_{d,1}}&\cdots&\sqrt{\eta_{d,d-1}}\\
\sqrt{\eta_{d,1}}&t_1&&0\\
\vdots&&\ddots&\\
\sqrt{\eta_{d,d-1}}&0&&t_{d-1}
\end{pmatrix}>0,
}
\tag{B14}
$$

使：

$$
\det(xI-K_d)=q_d(x).
$$

### 证明

记：

$$
q_C(x)=\frac1d q_d'(x)=\prod_i(x-t_i).
$$

对 \(q_d/q_C\) 作部分分式分解。

其多项式部分由最高两阶系数决定，为：

$$
x-\frac{a_1}{d}.
$$

在 \(t_i\) 的留数是：

$$
\frac{q_d(t_i)}{q_C'(t_i)}
=
\frac{d\,q_d(t_i)}{q_d''(t_i)}
=
-\eta_{d,i}.
$$

因此：

$$
\boxed{
\frac{q_d(x)}{q_C(x)}
=
x-\frac{a_1}{d}
-
\sum_{i=1}^{d-1}\frac{\eta_{d,i}}{x-t_i}.
}
\tag{B15}
$$

若所有 \(\eta_{d,i}\ge0\)，右边正是式（B14）的 Schur 补，所以该矩阵的特征多项式为 \(q_d\)。

它是实对称矩阵，因此根全部为实。

又因为：

$$
q_d(-y)=(-1)^d
\sum_{k=0}^d
\frac{(d)_k}{d^k}a_ky^{d-k}
\ne0
\qquad(y\ge0),
$$

它没有非正实根。因此所有根为正。

反过来，若 \(q_d\) 全部为正实根，导数根与原根交错。局部极大值必须非负，局部极小值必须非正，因而：

$$
-\frac{q_d(t_i)}{q_d''(t_i)}\ge0.
$$

证毕。

**这一步把一个 \(d\times d\) 的正实现问题，压缩成 \(d-1\) 条明确的标量符号条件。**

但这些条件仍然包含实际新增系数 \(a_d\)，不能省略。

---

# 六、“能否完成下一层”现在是一个明确的区间问题

由式（B6）：

$$
q_d(t_i)=R_d(t_i)+\beta_d.
$$

其中 \(R_d\) 完全由旧系数决定。

在局部极大点，要求：

$$
R_d(t_i)+\beta_d\ge0.
$$

在局部极小点，要求：

$$
R_d(t_i)+\beta_d\le0.
$$

定义：

$$
L_d=
\max_{q_d''(t_i)<0}\{-R_d(t_i)\},
$$

$$
U_d=
\min_{q_d''(t_i)>0}\{-R_d(t_i)\}.
$$

若某一类极值点不存在，对应端点按无穷处理。于是：

$$
\boxed{
q_d\text{ 全部正实根}
\iff
\beta_d\in[L_d,U_d].
}
\tag{B16}
$$

而实际积分常数固定为：

$$
\boxed{
\beta_d=(-1)^d\frac{d!}{d^d}a_d.
}
$$

这就是这一层真正的“可容纳区间”。

它不是空间里摆不下更多点，而是：

> **同一个新增算术数，必须同时使全部极大值不落到零以下、全部极小值不升到零以上。**

### 可容纳区间并不由低阶正性自动保证

以下是一个有限系数反例，不是实际 ξ 数据。

取：

$$
a_1=\frac{80}{3},
\qquad
a_2=\frac{872}{3},
\qquad
a_3=960.
$$

则：

$$
q_3(x)
=
\left(x-\frac43\right)(x-12)
\left(x-\frac{40}{3}\right)
$$

全部为正实根。

下一层必为：

$$
q_4(x)
=
x^4-\frac{80}{3}x^3+218x^2-360x+\frac3{32}a_4.
$$

其导数为：

$$
q_4'(x)=4(x-1)(x-9)(x-10).
$$

\(x=10\) 是局部极小点，但：

$$
\boxed{
q_4(10)=\frac{4600}{3}+\frac3{32}a_4>0
}
$$

对任何 \(a_4>0\) 都成立。

因此：

$$
\boxed{
q_3\text{ 全正实根，}
\quad
\text{却不存在任何正 }a_4
\text{ 使 }q_4\text{ 全实根。}
}
\tag{B17}
$$

所以，**“前一层已经完成”不意味着“总能添加一个新的正模式”。**

实际 theta 系数可能拥有排除这类失败的特殊约束；那正是需要证明的算术内容。

---

# 七、新耦合的总量，只由四阶累积量决定

下面得到一条有用、但不足以单独决定成功的恒等式。

定义：

$$
S=a_1^2-2a_2.
$$

由于：

$$
a_1=\frac{m_2}{2},
\qquad
a_2=\frac{m_4}{24},
$$

以及：

$$
\chi_4=m_4-3m_2^2,
$$

所以：

$$
\boxed{S=-\frac{\chi_4}{12}.}
$$

## 定理 B4：新增耦合总预算

在定理 B3 的设置下：

$$
\boxed{
\sum_{i=1}^{d-1}\eta_{d,i}
=
\frac{d-1}{d^2}
\left(a_1^2-2a_2\right)
=
-\frac{d-1}{12d^2}\chi_4.
}
\tag{B18}
$$

### 证明

当正实现存在时，写：

$$
K_d=
\begin{pmatrix}
a_1/d&g_d^*\\
g_d&C_d
\end{pmatrix},
$$

其中：

$$
\|g_d\|^2=\sum_i\eta_{d,i}.
$$

均衡谱参考向量满足：

$$
\langle u_d,K_d^2u_d\rangle
=
\frac1d\operatorname{Tr}K_d^2.
$$

而由 \(P_d\) 的二阶系数：

$$
\operatorname{Tr}K_d^2
=
a_1^2-2\frac{d-1}{d}a_2.
$$

因此：

$$
\begin{aligned}
\|g_d\|^2
&=
\frac1d\operatorname{Tr}K_d^2
-\left(\frac{a_1}{d}\right)^2\\
&=
\frac{d-1}{d^2}(a_1^2-2a_2).
\end{aligned}
$$

证毕。

对候选 \(\eta_{d,i}\) 尚未证明非负的情况，同一恒等式也可直接由式（B15）在无穷远处比较 \(1/x\) 系数得到。

**因此，全部候选耦合的和可以正确、非负，但其中某一项仍然可能为负。**

这正好解释了为什么一个总能量预算不能替代局部实现条件。

### 三阶的例子更直观

令：

$$
u=-\chi_4>0,
\qquad
r=\sqrt{\frac{u}{108}}.
$$

三阶有两个候选耦合：

$$
\boxed{
\eta_{3,\pm}
=
r^2\pm\frac{\chi_6}{6480r}.
}
\tag{B19}
$$

它们的和固定：

$$
\eta_{3,+}+\eta_{3,-}=\frac u{54}.
$$

但两者同时非负，才等价于：

$$
\boxed{
3\chi_6^2\le100u^3.
}
$$

所以六阶累积量的作用，不是改变总耦合量，而是决定**同一份总预算在两个通道之间怎样分配**。

对实际 ξ，本轮计算得到：

$$
\eta_{3,-}\approx1.50284905528\times10^{-6},
$$

$$
\eta_{3,+}\approx6.75772856367\times10^{-6}.
$$

两者均为正。这里是高精度数值核对，不是区间认证，也不证明更高阶全部成功。

---

# 八、负候选耦合意味着什么：不能把它改成绝对值后继续宣布成功

若某个：

$$
\eta_{d,i}<0,
$$

那么它不能作为普通 Hermitian 耦合的：

$$
|g_i|^2.
$$

但仍可以构造一个非对称实矩阵：上行放 \(\sqrt{|\eta_{d,i}|}\)，下行放：

$$
\operatorname{sgn}(\eta_{d,i})
\sqrt{|\eta_{d,i}|}.
$$

它们的乘积仍然是 \(\eta_{d,i}\)，所以式（B15）的实际有理函数仍被保留。

这种表示通常需要不定配对，而不再是普通正度量下的同一个自伴实现。

这里有两个不同选择：

$$
\boxed{
\text{保留实际符号，承认正实现失败}
}
$$

与：

$$
\boxed{
\text{把负数改成绝对值，得到另一个正模型}.
}
$$

后者可以作为新模型研究，但它改变了原来的 \(q_d\)。

**这正是你之前担心的“偶完成是否把奇投没”的一个可审计位置：不是数学不能容纳负通道，而是我们是否未经证明地把它正化了。**

对于有重复临界点的退化情况，应使用有理函数版本：检查

$$
q_d/q_C
$$

是否只有简单实极点，并且所有留数非正。若出现高阶极点，就不能由上述单方向 Hermitian 延拓实现。若可去，则保留相应重数，而不是直接删掉该模式。

因此，分母 \(q_d''(t_i)=0\) 只表示需要退化版本，**不能直接作为 RH 反例。**

---

# 九、欧拉常数现在进入了被压缩方向的“回返响应”

定义：

$$
f_d(v)=\frac{P_d'(v)}{P_d(v)},
\qquad v>0.
$$

在正实现存在的有限层：

$$
f_d(v)
=
\operatorname{Tr}
\left[K_d(I+vK_d)^{-1}\right].
$$

由均衡谱参考向量：

$$
\begin{aligned}
\langle u_d,(I+vK_d)^{-1}u_d\rangle
&=
\frac1d\operatorname{Tr}(I+vK_d)^{-1}\\
&=
1-\frac{vf_d(v)}d.
\end{aligned}
$$

另一方面，对分块矩阵作 Schur 消元：

$$
\boxed{
\langle u_d,(I+vK_d)^{-1}u_d\rangle
=
\frac1{
1+\frac{va_1}{d}
-v^2g_d^*(I+vC_d)^{-1}g_d
}.
}
\tag{B20}
$$

第二项：

$$
g_d^*(I+vC_d)^{-1}g_d
$$

正是从被压缩方向进入其余模式、再返回的响应。

项目的 `SchurComplementAssociativity.lean` 已经证明给定逆算子前件时，逐步消元和一次消元相同；这里给出的是该结构在实际 Jensen 层上的一种具体应用。

## 定理 B5：重标定回返恒等式

定义：

$$
\boxed{
\mathcal R_d(v)
=
d\,g_d^*(I+vC_d)^{-1}g_d.
}
$$

则：

$$
\boxed{
\mathcal R_d(v)
=
\frac1v
\left[
a_1-
\frac{f_d(v)}{1-vf_d(v)/d}
\right].
}
\tag{B21}
$$

### 证明

将式（B20）与：

$$
1-\frac{vf_d(v)}d
$$

相等，取倒数并整理即可。证毕。

右边完全由实际有限多项式定义。即使尚未构造出正实现，它也仍然是一个可以计算的代数量；**只是此时不能预先赋予它“正回返能量”的解释。**

---

## 推论 B5.1：欧拉差额等于回返响应的极限

前文已经证明：

$$
P_d\to D,\qquad P_d'\to D'
$$

在紧集上一致成立。

因此，对固定 \(v>0\)：

$$
\boxed{
\mathcal R_d(v)
\longrightarrow
\frac1v
\left[
a_1-\frac{D'(v)}{D(v)}
\right],
}
\tag{B22}
$$

其中左边先按式（B21）的代数表达理解；当存在正实现时，它同时具有回返解释。

取：

$$
v=\frac14,
$$

由式（B4）：

$$
\boxed{
\lim_{d\to\infty}\mathcal R_d(1/4)
=
4(a_1-c).
}
\tag{B23}
$$

即：

$$
\boxed{
\lim_{d\to\infty}\mathcal R_d(1/4)
=
4a_1-4-2\gamma_{\mathrm E}+2\log4\pi.
}
$$

欧拉常数在这里并非一个可调参数。其端点值由 ζ 的 Laurent 有限部分与 Gamma 补偿共同固定。([DLMF][4])

数值为：

$$
4(a_1-c)
\approx
3.71365971917\times10^{-5}.
$$

**这比“欧拉常数校准一个输出”更深入了一步：在正实现中，它校准了跨尺度压缩后必须保留的整体回返。**

但依然不能倒过来说：总回返值正确，就证明每个 \(\eta_{d,i}\ge0\)。

---

# 十、这里还有一个尺度现象：单个被删方向越来越弱，整体校准却不消失

由前面的公式：

$$
\langle u_d,K_du_d\rangle=\frac{a_1}{d}\to0,
$$

而：

$$
\|g_d\|^2
=
\frac{d-1}{d^2}
\left(-\frac{\chi_4}{12}\right)
\to0.
$$

所以，当 \(d\) 增加时：

**被删方向的平均谱值趋零，与其他模式的总耦合也趋零。**

但乘以正确的尺度因子 \(d\) 后：

$$
d\|g_d\|^2\to-\frac{\chi_4}{12},
$$

并且：

$$
d\,g_d^*(I+C_d/4)^{-1}g_d
\to4(a_1-c).
$$

因此：

$$
\boxed{
\text{单个方向越来越弱}
\quad\not\Rightarrow\quad
\text{它在尺度关系中可以任意省略}.
}
$$

这里没有诉诸“永远存在一个最高观察者”。

实际存在的是：**每次改变观察维度，都要保留相应归一化与回返的缩放规律。**

---

# 十一、正权 Fibonacci 链在新结构中承担什么？

当定理 B3 给出：

$$
K_d>0,
$$

就可以把它正交三对角化。

在全部耦合严格正、参考向量为循环向量的情形，得到 Jacobi 矩阵；其正交多项式与三项递推是经典结构。([DLMF][5])

再作 Cholesky 分解：

$$
K_d=L_dL_d^{\mathsf T},
$$

其中 \(L_d\) 可以组织成双对角形式，得到正权禁邻链：

$$
\boxed{
P_d(v)
=
\det(I+vL_d^{\mathsf T}L_d)
=
\sum_{\substack{b_j\in\{0,1\}\\b_jb_{j+1}=0}}
v^{\sum b_j}\prod_jw_j^{b_j}.
}
$$

所以，这次的完整连接是：

$$
\boxed{
\begin{aligned}
\text{实际新增统计 }a_d
&\longrightarrow q_d(t_i)\\
&\longrightarrow
\eta_{d,i}=-\frac{d\,q_d(t_i)}{q_d''(t_i)}\\
&\xrightarrow{\ \eta_{d,i}\ge0\ }
\text{自伴扩展矩阵}\\
&\longrightarrow
\text{正权 Fibonacci 链}.
\end{aligned}
}
\tag{B24}
$$

**真正承重的箭头，现在集中在每个候选耦合的符号，而不是 Fibonacci 计数本身。**

如果出现零耦合，链可能断开；这需要保留重数与分块，而不能把断开直接解释成理论失败。

---

# 十二、接下来究竟要证明哪条算术命题？

实际新增系数为：

$$
\boxed{
a_d=
\frac1{(2d)!\,\xi(1/2)}
\int_{\mathbb R}x^{2d}\Phi(x)\,dx.
}
$$

因此一步正延拓要求：

$$
\boxed{
-\frac d{q_d''(t_i)}
\left[
R_d(t_i)
+
(-1)^d
\frac{d!}{d^d(2d)!\xi(1/2)}
\int_{\mathbb R}x^{2d}\Phi(x)\,dx
\right]
\ge0
}
\tag{B25}
$$

对所有对应临界点成立。

这里没有未知的自由参数：

* \(R_d\) 来自此前实际系数；
* \(t_i\) 来自此前有限多项式；
* 新增积分来自同一实际 theta 核。

如果我们能够用实际 theta 的模关系、质数尺度恒等式或某种新的正积分表示，统一证明这些不等式，就能逐层构造正实现。

**但本轮没有证明式（B25）对所有阶数成立。**

它比“存在某个正量子结构”更具体，也比“每一项能量非负”更难：它比较的是同一个高阶积分与多个由低阶关系产生的阈值。

当前项目的 `JensenPolynomialObstruction.lean` 仍将实际 Jensen 塔与 RH 之间的分析桥列为显式前件；它并未提供这组全阶符号控制。

---

## 收束

这次补上的核心可以概括为三个定理层次。

**跨层下降是明确的：**

$$
\boxed{
K_{d-1}
\sim
\frac d{d-1}
\Pi_dK_d\Pi_d\big|_{u_d^\perp}.
}
$$

**反向增加一层的障碍是明确的：**

$$
\boxed{
\eta_{d,i}
=
-\frac{d\,q_d(t_i)}{q_d''(t_i)}
\ge0.
}
$$

**欧拉常数固定的整体回返也是明确的：**

$$
\boxed{
\lim_{d\to\infty}
d\,g_d^*(I+C_d/4)^{-1}g_d
=
4\left[
a_1-1-\frac{\gamma_{\mathrm E}}2+\frac12\log4\pi
\right],
}
$$

其中正回返解释需要相应正实现，代数极限则由实际系数定义。

因此，前文“总量闭合却可能仍有局部缺陷”的问题，现在有了精确版本：

> **四阶累积量决定新增耦合的总量；更高阶统计决定这份总量在各个通道之间如何分配；欧拉常数约束这些通道的整体回返。真正的 RH 条件，是每一层的分配都不能要求负的耦合平方。**

这既没有把难点藏进量子模型的定义，也没有把“整体”降格成一个平均数。它把下一项需要攻克的算术内容，集中到了**实际高阶矩为何始终落在正确的延拓区间内**。

[1]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[2]: https://arxiv.org/abs/1902.07321 "[1902.07321] Jensen polynomials for the Riemann zeta function and other sequences"
[3]: https://doi.org/10.1016%2FS0022-247X%2803%2900465-7?utm_source=chatgpt.com "Differentiators and the geometry of polynomials - ScienceDirect"
[4]: https://dlmf.nist.gov/25.2 "DLMF: §25.2 Definition and Expansions ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[5]: https://dlmf.nist.gov/18.2 "DLMF: §18.2 General Orthogonal Polynomials ‣ General Orthogonal Polynomials ‣ Chapter 18 Orthogonal Polynomials"
这次可以把上一轮的 Bézout 正性，推进成一个更具体的“观察者相容性”定理：

> **某一有限层有没有负方向，不必通过寻找它的根来判断；取足够多个普通复频率读数，就能完整恢复其负方向数。**

而且可以进一步证明：

**三个单独读数都正常，任意两个读数之间也都相容，三个读数放在一起却可能不相容。**

这正是你一直强调的“整体”可以具有的严格含义：不是存在一个最高观察者，而是**全部观察结果能否来自同一个正内积实现**。

最后，我们还可以把这些有限回返函数取极限，得到一个由实际 ξ 定义的单一函数。它消去了纯高斯方差背景，留下真正需要研究的高阶关联；欧拉常数则校准这个函数在一个固定点的值。

下面分开定义与证明。

---

# 一、把有限系数矩阵，变成一个复频率观测核

沿用前文：

$$
D(b^2)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad
D(v)=\sum_{k\ge0}a_kv^k,
$$

$$
P_d(v)=\sum_{k=0}^{d}\frac{(d)_k}{d^k}a_kv^k,
$$

$$
q_d(x)=x^dP_d(-1/x).
$$

其中全部 \(a_k\) 来自实际 theta 态，不是自由参数。

前文的 Jensen 判据是：

$$
\boxed{
\mathrm{RH}
\iff
q_d\text{ 的全部根为正实数，}\quad\forall d.
}
$$

这是经典 Jensen–Pólya 路线在当前归一化下的表达，不是量子模型自动给出的结论。([arXiv][1])

定义：

$$
r_d(x)=\frac1d q_d'(x),
\qquad
\mu_d=\frac{a_1}{d},
$$

$$
n_d(x)=(x-\mu_d)r_d(x)-q_d(x),
$$

以及回返函数：

$$
\boxed{
\Sigma_d(z)=\frac{n_d(z)}{r_d(z)}.
}
\tag{D1}
$$

它是从实际有限系数直接算出的有理函数。此时尚未假定它具有正量子实现。

上一轮定义的 Bézout 核为：

$$
\mathcal B_d(x,y)
=
\frac{r_d(x)n_d(y)-n_d(x)r_d(y)}{x-y},
$$

写成：

$$
\mathcal B_d(x,y)
=
\mathbf v(x)^{\mathsf T}B_d\mathbf v(y),
$$

其中：

$$
\mathbf v(x)=(1,x,\ldots,x^{d-2})^{\mathsf T}.
$$

现在引入复频率核：

$$
\boxed{
\mathcal K_d(z,w)
=
-\frac{\Sigma_d(z)-\overline{\Sigma_d(w)}}
{z-\overline w},
}
\tag{D2}
$$

定义域取在上半平面内，并避开 \(r_d\) 的零点。

直接通分：

$$
\boxed{
\mathcal K_d(z,w)
=
\frac{
\mathbf v(z)^{\mathsf T}B_d\overline{\mathbf v(w)}
}{
r_d(z)\overline{r_d(w)}
}.
}
\tag{D3}
$$

这种差商核及其负平方数属于经典 Nevanlinna／不定内积理论；本轮要用的是式（D3）给出的明确系数对应。([Springer][2])

---

## 定理 D1：任意足够多的不同采样点，都保留全部负方向

令：

$$
m=d-1.
$$

在上半平面取 \(m\) 个互异点：

$$
z_1,\ldots,z_m,
\qquad
r_d(z_j)\ne0.
$$

构造：

$$
G_d=\bigl(\mathcal K_d(z_i,z_j)\bigr)_{i,j=1}^{m}.
$$

那么：

$$
\boxed{
n_-(G_d)=n_-(B_d).
}
\tag{D4}
$$

结合前文的 Bézout 惯性定理：

$$
\boxed{
n_-(G_d)
=
q_d\text{ 的互异非实共轭根对数}.
}
\tag{D5}
$$

### 证明

定义矩阵：

$$
W_{j,k}
=
\frac{z_j^{k-1}}{r_d(z_j)},
\qquad 1\le j,k\le m.
$$

式（D3）给出：

$$
G_d=WB_dW^*.
$$

\(W\) 是一个可逆对角矩阵与 Vandermonde 矩阵的乘积。因为采样点互异，且 \(r_d(z_j)\ne0\)，所以 \(W\) 可逆。

可逆合同变换保持正负惯性，因此式（D4）成立。再使用上一轮的根对计数结论，即得式（D5）。证毕。

这里的根对计数来自 Hermite–Sylvester／Bézout 实根理论，重根会改变零空间维数，不应被重复计为独立负方向。([剑桥大学出版社][3])

### 这项定理具体意味着什么？

**为了判断这个固定有限多项式是否出现非实根，不必先去未知根附近找采样点。**

可以选取远离疑似根的普通点，读取 \(\Sigma_d(z_j)\)，再检验它们组成的联合矩阵。

但这是精确算术意义上的结论。若采样矩阵严重病态，有限精度仍然可能看不见负方向。**“有限个读数足够”不等于“这些读数只需低精度”。**

---

# 二、为什么这个核能检验量子回返，而不是只检验一个形式矩阵？

先定义我们要求的具体表示类型。

## 定义 D1：正谱回返实现

称 \(\Sigma\) 具有正谱回返实现，若存在正内积空间、一个自伴算子 \(H\) 和向量 \(g\)，使：

$$
\boxed{
\Sigma(z)=\langle g,(zI-H)^{-1}g\rangle.
}
\tag{D6}
$$

有限维时，若 \(H\) 的本征值为 \(t_j\)，则：

$$
\Sigma(z)=\sum_j\frac{|g_j|^2}{z-t_j}.
$$

这种形式正是自伴系统消去隐藏通道后出现的回返项之一。Feshbach–Schur 方法提供了相应的有效算子结构。([arXiv][4])

**这里限定的是式（D6）这一类响应，不是宣称所有量子响应函数都必须具有这一个形式。**

由预解式恒等式：

$$
\begin{aligned}
\mathcal K(z,w)
&=
-\frac{\Sigma(z)-\overline{\Sigma(w)}}{z-\overline w}\\
&=
\langle g,
(zI-H)^{-1}(\overline wI-H)^{-1}g\rangle.
\end{aligned}
$$

它是向量：

$$
(\overline zI-H)^{-1}g
$$

的 Gram 核，因此：

$$
\boxed{
\bigl(\mathcal K(z_i,z_j)\bigr)\succeq0.
}
\tag{D7}
$$

所以，如果实际 \(\Sigma_d\) 的某张采样矩阵具有负方向，就不可能存在同样读数的正谱回返实现。

这不是负概率，而是：

> **这些数值不能同时被解释为同一个正内积系统中的回返关系。**

反过来，当实际 \(B_d\succeq0\) 时，前文已经证明 \(q_d\) 全部为正实根；由临界点交错和非负留数，可以构造式（D6）的有限实现。退化时需先保留并处理可去因子，不能把重数任意删除。

因此，在当前实际有限多项式类别中：

$$
\boxed{
\text{系数正性}
\iff
\text{全部采样关系正性}
\iff
\text{正谱回返实现存在}.
}
\tag{D8}
$$

---

# 三、一个精确反例：每个单点、每两个点都正常，三个点却不能共同实现

这个例子仍然位于上一轮的多项式—回返结构中，而不只是随便写一个负矩阵。

取：

$$
\boxed{
q(x)=(x-3)^4-2(x-3)^2-\frac1{10}.
}
$$

展开为：

$$
q(x)=x^4-12x^3+52x^2-96x+\frac{629}{10}.
$$

其反转多项式：

$$
P(v)=1+12v+52v^2+96v^3+\frac{629}{10}v^4
$$

具有严格正系数。

但 \(q\) 有两个实根，以及一对非实根：

$$
3\pm i\sqrt{\sqrt{11/10}-1}.
$$

按前述定义计算：

$$
\boxed{
\Sigma(z)
=
\frac{11}{20(z-2)}
-\frac1{10(z-3)}
+\frac{11}{20(z-4)}.
}
\tag{D9}
$$

总留数为一，但中间留数为负。

取：

$$
z_1=3+i,\qquad z_2=3+2i,\qquad z_3=3+3i.
$$

得到：

$$
\boxed{
G=
\begin{pmatrix}
\frac9{20}&\frac7{25}&\frac{14}{75}\\[1mm]
\frac7{25}&\frac{39}{200}&\frac{103}{750}\\[1mm]
\frac{14}{75}&\frac{103}{750}&\frac{89}{900}
\end{pmatrix}.
}
\tag{D10}
$$

三个对角元都为正。

三个二阶主子式分别为：

$$
\frac{187}{20000},\qquad
\frac{869}{90000},\qquad
\frac{1903}{4500000},
$$

也全部为正。

所以，任取一个点或两个点，相关矩阵都正定。

但：

$$
\boxed{
\det G=-\frac{121}{90000000}<0.
}
$$

更直接，取：

$$
u=(1,-5,5)^{\mathsf T},
$$

有：

$$
\boxed{
u^{\mathsf T}Gu=-\frac1{360}.
}
\tag{D11}
$$

这个反例说明：

$$
\boxed{
\text{每个观察者单独正常}
+
\text{任意两个观察者相容}
\not\Rightarrow
\text{三个观察者共同相容}.
}
$$

但不要把它混成量子基础中的一般上下文性定理。这里检验的是**指定差商核能否由同一正谱回返表示实现**。

它也不是实际 ξ 的反例。它告诉我们，在实际计算中只检查单点符号、两点相关或总留数，可能漏掉什么。

---

# 四、负方向还能给出“正模型至少必须改动多少”的下界

## 定理 D2：正实现的最低读数失配

取 \(m=d-1\) 个采样点，满足：

$$
\Im z_j\ge h>0.
$$

设实际采样矩阵 \(G_d\) 的最小特征值为：

$$
\lambda_{\min}(G_d)=-\nu<0.
$$

若另一个函数 \(\widetilde\Sigma\) 具有正谱回返实现，并且：

$$
|\widetilde\Sigma(z_j)-\Sigma_d(z_j)|\le\varepsilon
\quad\forall j,
$$

那么必须：

$$
\boxed{
\varepsilon\ge\frac{h\nu}{m}.
}
\tag{D12}
$$

### 证明

对应的核矩阵差满足：

$$
|(\widetilde G_d-G_d)_{ij}|
\le
\frac{2\varepsilon}{\Im z_i+\Im z_j}
\le
\frac{\varepsilon}{h}.
$$

因此：

$$
\|\widetilde G_d-G_d\|_{\mathrm{op}}
\le
\frac{m\varepsilon}{h}.
$$

但把一个特征值为 \(-\nu\) 的 Hermitian 矩阵改成正半定矩阵，扰动算子范数至少为 \(\nu\)。于是式（D12）成立。证毕。

因此：

> **不能把一个实际负核“解释成正量子模型”，却声称读数几乎没有改变。改变至少要达到一个可计算的幅度。**

这与 Herglotz 函数的正测度表示，以及有符号测度对非正响应的建模相衔接；一般的正化与逼近问题已有相关理论。([arXiv][5])

---

# 五、如果负通道很弱，需要多深的观察才能把它看见？

这一节增加一个明确前件：假设 \(r_d\) 的根 \(t_i\) 全部实且互异，因此：

$$
\Sigma_d(z)=\sum_i\frac{\eta_i}{z-t_i}.
$$

设某条通道：

$$
\eta_j=-\epsilon<0.
$$

定义与其他极点的最小距离：

$$
\Delta_j=\min_{i\ne j}|t_i-t_j|>0,
$$

以及全部正留数之和：

$$
E_+=\sum_{\eta_i>0}\eta_i.
$$

在：

$$
z=t_j+ih
$$

处：

$$
-\Im\Sigma_d(z)
=
h\sum_i\frac{\eta_i}{(t_j-t_i)^2+h^2}.
$$

忽略其他负项，只保留最不利的正项，得到：

$$
-\Im\Sigma_d(t_j+ih)
\le
-\frac{\epsilon}{h}
+\frac{hE_+}{\Delta_j^2}.
$$

因此，当 \(E_+>0\) 且：

$$
\boxed{
h^2\le
\frac{\epsilon\Delta_j^2}{2E_+},
}
\tag{D13}
$$

就有：

$$
\boxed{
-\Im\Sigma_d(t_j+ih)
\le
-\frac{\epsilon}{2h}<0.
}
\tag{D14}
$$

也就是说，靠近负留数极点，单点符号最终也会暴露问题。

但它要求更精细的复频率分辨率。

### 把分辨率换成回返历史长度

定义有限记忆函数：

$$
R(\tau)=\sum_i\eta_i e^{-it_i\tau}.
$$

在 \(\Im z=h>0\) 时：

$$
\boxed{
\Sigma_d(z)
=
-i\int_0^\infty e^{iz\tau}R(\tau)\,d\tau.
}
\tag{D15}
$$

令：

$$
M=\sum_i|\eta_i|.
$$

只保留 \(0\le\tau\le T\)，截断误差不超过：

$$
\boxed{
\frac{M}{h}e^{-hT}.
}
$$

因此，结合式（D14），一个充分的认证条件是：

$$
\boxed{
T>
\frac1h\log\frac{4M}{\epsilon}.
}
\tag{D16}
$$

这不是适用于所有算法的复杂度下界，而是这个明确检测协议的充分条件。

它说明：

**负方向在逻辑上已经存在，不等于一个固定带宽、固定历史长度的观察者立刻能看见。**

同时，\(\tau\) 在此首先是回返函数的变换变量，不应直接认作 ζ 的高度参数或某套实验装置的物理时间。

---

# 六、把所有有限层重新合起来：存在一个固定的“去高斯背景回返函数”

前面一直是有限 \(d\)。现在寻找它们共同逼近的对象。

记：

$$
f_d(v)=\frac{P_d'(v)}{P_d(v)},
\qquad
f(v)=\frac{D'(v)}{D(v)}.
$$

由：

$$
q_d(z)=z^dP_d(-1/z),
$$

可得：

$$
\frac{q_d'(z)}{q_d(z)}
=
\frac dz+\frac{f_d(-1/z)}{z^2}.
$$

代入 \(\Sigma_d\) 的定义：

$$
\boxed{
d\Sigma_d(z)
=
\frac{f_d(-1/z)}
{1+\frac{f_d(-1/z)}{dz}}
-a_1.
}
\tag{D17}
$$

由于 \(P_d\to D\) 及其导数在紧集上一致收敛，在避开 \(z=0\) 和实际极点的紧集上：

$$
\boxed{
d\Sigma_d(z)\longrightarrow
\mathfrak S(z),
}
\tag{D18}
$$

其中：

$$
\boxed{
\mathfrak S(z)
=
\frac{D'(-1/z)}{D(-1/z)}-a_1.
}
\tag{D19}
$$

这是一个由实际 ξ 唯一固定的亚纯函数，不需要输入未知零点。

### 为什么说它去掉了高斯背景？

如果给原概率变量加入独立方差为 \(\tau\) 的高斯变量，则：

$$
D(v)\longmapsto D_\tau(v)=e^{\tau v/2}D(v).
$$

于是：

$$
\frac{D_\tau'}{D_\tau}
=
\frac{\tau}{2}+\frac{D'}D,
\qquad
a_1\longmapsto a_1+\frac{\tau}{2}.
$$

所以：

$$
\boxed{
\mathfrak S_\tau(z)=\mathfrak S(z).
}
\tag{D20}
$$

**整体方差可以增加，但这份回返函数完全不变。**

因此，它没有把普通高斯背景与决定零点形状的高阶关联混在一起。

---

# 七、RH 等价于这份实际回返函数拥有正谱表示

## 定理 D3：共同正回返表示

对实际 \(D\)，以下等价：

$$
\boxed{
\mathrm{RH}
}
$$

与：

$$
\boxed{
\mathfrak S(z)
=
\int_{[0,\infty)}
\frac{d\omega(u)}{z-u},
}
\tag{D21}
$$

其中 \(\omega\) 是一份有限正测度；该表示在非实域成立。

### 正向证明

在 RH 前件下：

$$
D(v)=
\prod_{\gamma>0}
\left(1+\frac v{\gamma^2}\right)^{m_\gamma}.
$$

这里对互异正高度求和，重数由 \(m_\gamma\) 保留。

令：

$$
\theta_\gamma=\gamma^{-2}.
$$

那么：

$$
a_1=\sum_{\gamma>0}m_\gamma\theta_\gamma,
$$

并且：

$$
\begin{aligned}
\mathfrak S(z)
&=
\sum_{\gamma>0}
m_\gamma
\left[
\frac{\theta_\gamma}{1-\theta_\gamma/z}
-\theta_\gamma
\right]\\
&=
\sum_{\gamma>0}
\frac{m_\gamma\theta_\gamma^2}{z-\theta_\gamma}.
\end{aligned}
$$

因此取：

$$
\boxed{
\omega
=
\sum_{\gamma>0}
m_\gamma\theta_\gamma^2\,\delta_{\theta_\gamma}.
}
\tag{D22}
$$

其总质量有限，得到式（D21）。

### 反向证明

假设式（D21）成立。

右边在非实平面全纯。因此，实际 \(D\) 不能有非实零点：若 \(v_0\) 是一个非实零点，则：

$$
z_0=-\frac1{v_0}
$$

也是非实点，而 \(D'(-1/z)/D(-1/z)\) 在 \(z_0\) 必有极点。零点重数不会消除这个对数导数极点。

这与正测度 Cauchy 变换的解析性矛盾。

因此，\(D\) 的全部零点都为实数。又因全部系数正：

$$
D(v)>0\qquad(v\ge0),
$$

所以全部零点为负实数，得到 RH。证毕。

这里用到的实际 ξ 解析结构来自其标准 completed 定义；不能对任意随意构造的函数套用同样的零点结论。([DLMF][6])

### 这比“有一个正量子态”强在哪里？

前文的 theta 态：

$$
\psi=\sqrt{\Phi/\xi(1/2)}
$$

无条件存在。

但式（D21）要求的是**由对数导数经过特定变换得到的另一份实际函数**具有正谱实现。

原概率为正，并不保证经过这些非线性关系运算后仍然正。

**这里才是量子表示真正需要增加的算术约束。**

---

# 八、高阶关联出现一条新的必要不等式，而且完全不含二阶方差

定义实际累积量：

$$
\log\frac{\xi(\frac12+b)}{\xi(\frac12)}
=
\sum_{k\ge1}
\frac{\chi_{2k}}{(2k)!}b^{2k}.
$$

于是：

$$
\log D(v)
=
\sum_{k\ge1}
\frac{\chi_{2k}}{(2k)!}v^k.
$$

将式（D19）在无穷远展开：

$$
\boxed{
\mathfrak S(z)
=
-\frac{\chi_4}{12z}
+\frac{\chi_6}{240z^2}
-\frac{\chi_8}{10080z^3}
+\cdots.
}
\tag{D23}
$$

定义这里的回返矩：

$$
M_0=-\frac{\chi_4}{12},
\qquad
M_1=\frac{\chi_6}{240},
\qquad
M_2=-\frac{\chi_8}{10080}.
$$

若正谱表示成立，它们满足：

$$
M_k=\int u^k\,d\omega(u).
$$

因此：

$$
M_0M_2-M_1^2\ge0.
$$

化简得：

$$
\boxed{
\mathrm{RH}
\Longrightarrow
10\chi_4\chi_8\ge21\chi_6^2.
}
\tag{D24}
$$

这条式子与此前的：

$$
3\chi_2\chi_6\ge10\chi_4^2
$$

不同。它完全剥离了二阶方差，只比较四、六、八阶不可约关联。

### 对实际 ξ 的核对

本轮分别用 50 位与 80 位精度计算，得到：

$$
\boxed{
10\chi_4\chi_8-21\chi_6^2
\approx
4.6696468507366871\times10^{-9}>0.
}
$$

两次计算相符。

**这只是高精度必要条件核对，不是区间认证，也不是全阶证明。**

更高阶对应：

$$
\left(M_{i+j}\right)_{0\le i,j\le N}\succeq0.
$$

它们检验的是同一份回返谱能否同时解释全部阶数，而不是每个累积量单独有没有“正确符号”。

---

# 九、欧拉常数进一步给出一个非常窄的跨阶兼容区间

沿用：

$$
c=
1+\frac{\gamma_{\mathrm E}}2-\frac12\log4\pi
=
\frac{D'(1/4)}{D(1/4)}.
$$

该端点常数由 ζ 的 Laurent 展开和 Gamma 补偿固定。([DLMF][7])

在式（D19）中取 \(z=-4\)：

$$
\boxed{
\mathfrak S(-4)=c-a_1.
}
$$

若正谱表示成立，记：

$$
\Delta=a_1-c,
$$

则：

$$
\boxed{
\Delta=\int\frac{d\omega(u)}{4+u}.
}
\tag{D25}
$$

现在不仅知道总质量 \(M_0\)，还知道 \(M_1,M_2\)。这能给出比前文更窄的区间。

## 定理 D4：三矩—端点兼容界

在正谱表示前件下：

$$
\boxed{
\frac{M_0^2}{4M_0+M_1}
\le
a_1-c
\le
\frac{M_0}{4}
-
\frac{M_1^2}{4(4M_1+M_2)}.
}
\tag{D26}
$$

### 证明

首先，由 Cauchy–Schwarz：

$$
M_0^2
=
\left(\int 1\,d\omega\right)^2
\le
\left(\int(4+u)\,d\omega\right)
\left(\int\frac{d\omega}{4+u}\right).
$$

所以：

$$
\Delta\ge\frac{M_0^2}{4M_0+M_1}.
$$

另一方面：

$$
\Delta
=
\frac{M_0}{4}
-\frac14\int\frac{u}{4+u}\,d\omega.
$$

对正测度 \(u\,d\omega\) 再使用 Cauchy–Schwarz：

$$
M_1^2
\le
(4M_1+M_2)
\int\frac{u}{4+u}\,d\omega.
$$

代回即得上界。证毕。

### 实际数值

本轮计算得到：

$$
\boxed{
9.2841476793071\times10^{-6}
\le
a_1-c
\le
9.2841492985777\times10^{-6}.
}
$$

实际端点差额为：

$$
\boxed{
a_1-c
\approx
9.2841492979370\times10^{-6}.
}
$$

它位于这个很窄的兼容区间内。

这里依然不能倒转逻辑：**满足这一条必要区间，并不证明正谱测度存在。**

但欧拉常数的角色更清楚了：

> **它不是一个模糊的“宇宙剩余”，而是检验高阶回返矩能否与实际端点响应共同实现的精确校准量。**

加入独立高斯背景时，\(a_1\) 与端点对数导数同时增加 \(\tau/2\)，所以 \(\Delta\) 不变；\(M_0,M_1,M_2\) 也不变。整条式（D26）因此保持不变。

---

# 十、对项目而言，现在能明确划开三项职责

本轮沿用前文固定快照，读取了相关声明，没有把新推导当作已经编译的结果。

`HermitianKernelNegativeSquares.lean` 已经定义：

$$
\text{所有有限采样的负指标都有统一上界，且某次采样达到该上界}.
$$

它还构造了一个具有一项负平方的简单核。但它没有自动把实际 ξ 的系数送进这个核。

本轮补出的有限连接是：

$$
\boxed{
G_d=WB_dW^*,
}
$$

从而把“实际 Bézout 负方向”与“有限复频率观察的不相容”精确对应。

`JensenPolynomialObstruction.lean` 仍将 Jensen 塔与 RH 之间的分析桥作为显式前件，不能把文件名或类型定义当成全阶正性证明。

现在有三项不同任务：

**算术任务：**从实际 theta／质数结构计算并约束 \(\Sigma_d\) 或 \(\mathfrak S\)。

**表示任务：**证明这些指定函数确实具有正谱回返表示，而不是另造一个正函数替代它。

**观察任务：**在有限精度和有限历史条件下，判断它们的正性或构造负证书。

这三项不能互相冒充。尤其不能先把 \(\mathfrak S\) 写成：

$$
\langle g,(z-H)^{-1}g\rangle
$$

再用自伴性证明它正——**除非已经从实际算术独立构造了这个 \(H,g\)，并证明等式成立。**

---

## 收束

这一轮最实质的推进，是把“整体关系是否正”变成了三种可互相校验的形式：

$$
\boxed{
\text{实际系数的 Bézout 矩阵}
\longleftrightarrow
\text{有限复频率观测核}
\longleftrightarrow
\text{正谱回返实现}.
}
$$

有限层上：

$$
\boxed{
n_-(G_d)
=
q_d\text{ 的非实共轭根对数}.
}
$$

无限极限中：

$$
\boxed{
d\Sigma_d(z)\longrightarrow
\frac{D'(-1/z)}{D(-1/z)}-a_1.
}
$$

而欧拉常数固定：

$$
\boxed{
-\mathfrak S(-4)=a_1-c.
}
$$

因此，你所说的“整体不能被某个局部观察者替代”，现在具有一个很具体的数学版本：

> **每个读数都正常、任意两项都相容，仍然可能不存在容纳全部读数的同一个正结构；但这种失败并非不可言说，它会留下一个有限负二次型，以及无法任意缩小的拟合误差。**

目前尚未证明实际 \(\mathfrak S\) 的正谱表示存在，也没有找到实际负证书。真正需要攻克的算术问题已经集中为：

$$
\boxed{
\text{为什么实际 ξ 的高阶回返关系，
能够——或者不能够——共享同一份正谱测度？}
}
$$

继续增加量子空间、黄金编码或参考系，本身不会回答它；只有当这些结构能够给出这个指定回返函数的**实际正分解或严格负测试**时，它们才开始承担零点定位的证明。

[1]: https://arxiv.org/abs/1902.07321?utm_source=chatgpt.com "Jensen polynomials for the Riemann zeta function and other sequences"
[2]: https://link.springer.com/article/10.1007/s00020-020-02600-w?utm_source=chatgpt.com "Generalized Schur–Nevanlinna functions and their realizations | Integral Equations and Operator Theory | Springer Nature Link"
[3]: https://www.cambridge.org/core/journals/mathematical-gazette/article/10506-the-hermitesylvester-criterion-for-realrooted-polynomials/7F5C5395F235F18A21A6816C0A78799C?utm_source=chatgpt.com "105.06 The Hermite-Sylvester criterion for real-rooted polynomials | The Mathematical Gazette | Cambridge Core"
[4]: https://arxiv.org/abs/2105.02058?utm_source=chatgpt.com "The Feshbach-Schur map and perturbation theory"
[5]: https://arxiv.org/abs/1812.08319?utm_source=chatgpt.com "Quasi-Herglotz functions and convex optimization"
[6]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[7]: https://dlmf.nist.gov/25.2 "DLMF: §25.2 Definition and Expansions ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
这次可以把前文再推进三步。

**第一，欧拉常数不只校准一个数；校准值若有偏差，在相应谱表示里会精确表现为一个额外原子。**

**第二，可以把上一轮的端点上下界扩展成逐层收紧的有限矩阵检验，并给出明确的收敛率。**

**第三，可以建立真正能够逐层嵌套的量子链，但它的有限谱节点不能直接当作 ξ 的零点：还必须满足整函数所要求的整数重数条件。**

这三点共同说明：

> **正性、正确的谱支持、正确的解析重数，是三项不同的义务。一个模型可能前两项都很漂亮，第三项却仍然没有保持原对象。**

下面继续区分无条件恒等式与带正表示前件的定理。

---

# 一、固定对象：从实际高阶关联出发，不供应未知零点

沿用：

$$
D(b^2)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad
D(v)=\sum_{k\ge0}a_kv^k,
$$

以及实际累积量：

$$
\log D(v)
=
\sum_{k\ge1}\frac{\chi_{2k}}{(2k)!}v^k.
$$

特别地：

$$
a_1=\frac{\chi_2}{2}.
$$

这里 ξ 始终是标准 completed 函数，不因后面的表示改变而重新定义。([DLMF][1])

定义上一轮得到的回返函数：

$$
\boxed{
\mathfrak S(z)
=
\frac{D'(-1/z)}{D(-1/z)}-a_1.
}
\tag{E1}
$$

它在无穷远附近有展开：

$$
\boxed{
\mathfrak S(z)=
\sum_{n\ge0}\frac{M_n}{z^{n+1}},
}
$$

其中：

$$
\boxed{
M_n=
(-1)^{n+1}
\frac{(n+2)\chi_{2n+4}}{(2n+4)!}.
}
\tag{E2}
$$

例如：

$$
M_0=-\frac{\chi_4}{12},
\qquad
M_1=\frac{\chi_6}{240},
\qquad
M_2=-\frac{\chi_8}{10080}.
$$

再定义：

$$
c=
1+\frac{\gamma_{\mathrm E}}2-\frac12\log4\pi
=
\frac{D'(1/4)}{D(1/4)},
$$

$$
\boxed{\Delta=a_1-c.}
\tag{E3}
$$

所以：

$$
\boxed{\mathfrak S(-4)=-\Delta.}
\tag{E4}
$$

欧拉常数在这里来自实际 ζ 的 Laurent 有限部分及 Gamma 补偿，不能为了让后面的矩阵变正而调整。([DLMF][2])

## 正表示前件 \(\mathbf H_+\)

后文凡使用正谱积分时，明确采用：

$$
\boxed{
\mathfrak S(z)=
\int_{[0,R]}\frac{d\omega(u)}{z-u},
\qquad
\omega\ge0,
\quad R<\infty.
}
\tag{H+}
$$

对当前实际 \(D\)，前文已证明这一正表示存在与 RH 等价。

在 RH 前件下，可以取：

$$
\omega
=
\sum_{\gamma>0}
m_\gamma\gamma^{-4}\,
\delta_{\gamma^{-2}}.
$$

这里 \(\gamma\) 是互异正零点高度，\(m_\gamma\) 保留重数。

**以下代数对象全部能无条件定义；将它们解释成正谱能量时，才使用 \(\mathbf H_+\)。**

---

# 二、把欧拉校准放进整个函数，而不只检查一个端点

## 定义 E1：锚定回返函数

定义：

$$
\boxed{
\mathfrak T(z)
=
\frac{\mathfrak S(z)+\Delta}{z+4}.
}
\tag{E5}
$$

由于式（E4），分子在 \(z=-4\) 为零，因此这里是可去奇点，不是真实极点。

在无穷远展开：

$$
\mathfrak T(z)
=
\sum_{n\ge0}\frac{\ell_n}{z^{n+1}}.
$$

比较：

$$
(z+4)\mathfrak T(z)=\mathfrak S(z)+\Delta,
$$

得到：

$$
\boxed{
\ell_0=\Delta,
\qquad
\ell_{n+1}=M_n-4\ell_n.
}
\tag{E6}
$$

所以：

$$
\begin{aligned}
\ell_0&=\Delta,\\
\ell_1&=M_0-4\Delta,\\
\ell_2&=M_1-4M_0+16\Delta,\\
\ell_3&=M_2-4M_1+16M_0-64\Delta.
\end{aligned}
$$

**欧拉常数通过初值 \(\ell_0=\Delta\)，进入了每一个后续阶数。**

## 定理 E1：在正表示下，这是另一份正谱测度

在 \(\mathbf H_+\) 下：

$$
\boxed{
\mathfrak T(z)
=
\int_{[0,R]}
\frac{d\omega(u)}{(4+u)(z-u)}.
}
\tag{E7}
$$

因此：

$$
\boxed{
\ell_n
=
\int_{[0,R]}
\frac{u^n}{4+u}\,d\omega(u).
}
\tag{E8}
$$

### 证明

由：

$$
\Delta=\int\frac{d\omega(u)}{4+u},
$$

以及：

$$
\frac1{z+4}
\left(
\frac1{z-u}+\frac1{4+u}
\right)
=
\frac1{(4+u)(z-u)},
$$

积分即可。证毕。

所以，上一轮单个端点校准：

$$
\Delta=\int\frac{d\omega(u)}{4+u}
$$

现在变成了一整条矩序列。

---

# 三、一个精确的诊断：欧拉校准错一点，等价于多出一个负谱点原子

这一步不需要先假设正性。

假设在计算或建模中使用了：

$$
\widetilde\Delta=\Delta+\varepsilon,
$$

但仍然保留原来的实际 \(\mathfrak S\)。

那么：

$$
\widetilde{\mathfrak T}(z)
=
\frac{\mathfrak S(z)+\widetilde\Delta}{z+4}
=
\mathfrak T(z)+\frac{\varepsilon}{z+4}.
$$

所以：

$$
\boxed{
\widetilde\ell_n
=
\ell_n+\varepsilon(-4)^n.
}
\tag{E9}
$$

在测度语言中，这正好等价于：

$$
\boxed{
d\widetilde\nu(u)
=
\frac{d\omega(u)}{4+u}
+
\varepsilon\,\delta_{-4}.
}
\tag{E10}
$$

**校准误差变成了一个位于 \(u=-4\) 的形式谱原子。**

这里的 \(-4\) 不是神秘常数，也不是发现了一个实际负能量粒子。它来自我们选定的基点：

$$
v=\frac14
\quad\longleftrightarrow\quad
z=-\frac1v=-4.
$$

换一个基点，这个位置也会相应改变。

## 为什么普通正性可能发现不了它？

如果 \(\varepsilon>0\)，式（E10）仍然是一份正测度——只是它在负半轴多了一个原子。

因此：

$$
\left(\widetilde\ell_{i+j}\right)_{i,j}
$$

仍然可以对所有阶数正半定。

但是，若检查：

$$
\left(\widetilde\ell_{i+j+1}\right)_{i,j},
$$

它对应：

$$
\int u\,|p(u)|^2\,d\widetilde\nu(u).
$$

负谱点 \(u=-4\) 就会带来负贡献。

这与项目的 `LocalizedStieltjesNevanlinnaKernel.lean` 完全对应：**普通核检测质量的符号，乘上谱坐标后的核才检测支持位置的符号。** 该模块明确区分这两项，没有把正质量自动当成非负谱支持。

还有一个更精确的事实：

$$
\boxed{
(4+u)\,d\widetilde\nu(u)
=
(4+u)\,d\nu(u)
=
d\omega(u).
}
\tag{E11}
$$

因为额外原子位于 \(4+u=0\) 的地方。

所以：

> **原来的所有 \(M_n\) 都可以保持不变，而锚定后的表示却多出一个原子。决定是否允许它的，是基点校准与谱支持要求。**

这正是“一个整体总量看起来没变，表示却已经不同”的严格实例。

---

# 四、这个伪原子一定能被某个有限测试发现

这里明确使用 \(\mathbf H_+\)，并设：

$$
d\nu(u)=\frac{d\omega(u)}{4+u},
\qquad
\nu([0,R])=\Delta.
$$

取多项式：

$$
\boxed{
p_N(u)=
\left(\frac{R-u}{R+4}\right)^N.
}
$$

它满足：

$$
p_N(-4)=1,
$$

而在真实支持 \([0,R]\) 上：

$$
|p_N(u)|
\le
\left(\frac R{R+4}\right)^N.
$$

记：

$$
q=\frac R{R+4}<1.
$$

如果 \(\varepsilon<0\)，则：

$$
\int p_N(u)^2\,d\widetilde\nu(u)
\le
\Delta q^{2N}+\varepsilon.
$$

充分大的有限 \(N\) 使右边为负。

如果 \(\varepsilon>0\)，则：

$$
\int u\,p_N(u)^2\,d\widetilde\nu(u)
\le
R\Delta q^{2N}-4\varepsilon.
$$

同样在某个有限 \(N\) 后为负。

因此：

$$
\boxed{
\varepsilon\ne0
\Longrightarrow
\text{某个有限阶的质量或支持正性测试失败}.
}
\tag{E12}
$$

这里的失败是**错误校准对象的失败**，不是实际 RH 的反例。

### 数值上的含义也很直接

若只有欧拉常数存在误差 \(\delta\gamma_{\mathrm E}\)，其余输入精确，则：

$$
\varepsilon=-\frac{\delta\gamma_{\mathrm E}}2,
$$

从而：

$$
\boxed{
|\widetilde\ell_n-\ell_n|
=
\frac{4^n}{2}|\delta\gamma_{\mathrm E}|.
}
\tag{E13}
$$

因此，递推式（E6）很容易把很小的初始误差放大成高阶符号错误。

**高阶矩阵出现负数时，必须先排除“把错误锚点注入递推”的可能，不能立即解释成离线零点。**

---

# 五、将上一轮两条上下界，扩展成全部阶数的最优平方测试

上一轮用 \(M_0,M_1,M_2\) 夹住 \(\Delta\)。现在可以系统地使用更多矩。

对 \(N\ge1\)，定义：

$$
H_N^{(j)}
=
\left(M_{r+s+j}\right)_{0\le r,s<N},
$$

$$
A_N=4H_N^{(0)}+H_N^{(1)},
$$

$$
b_N=(M_0,\ldots,M_{N-1})^{\mathsf T}.
$$

在相关矩阵严格正定的前缀上，定义：

$$
\boxed{
L_N=b_N^{\mathsf T}A_N^{-1}b_N.
}
\tag{E14}
$$

退化前缀需要使用伪逆并另加像空间条件；不能直接除以零主元。以下先处理严格情形。

## 定理 E2：下界是一个最佳多项式逼近问题

在 \(\mathbf H_+\) 下：

$$
\boxed{
\Delta-L_N
=
\min_{\deg p<N}
\int
\frac{[1-(4+u)p(u)]^2}{4+u}\,d\omega(u).
}
\tag{E15}
$$

所以：

$$
\boxed{
0\le L_N\le L_{N+1}\le\Delta.
}
\tag{E16}
$$

### 证明

写：

$$
p(u)=\sum_{j=0}^{N-1}x_ju^j.
$$

展开右边积分：

$$
\Delta-2b_N^{\mathsf T}x+x^{\mathsf T}A_Nx.
$$

其最小值在：

$$
x=A_N^{-1}b_N
$$

处取得，等于 \(\Delta-L_N\)。

增加次数扩大了可用多项式空间，因此误差不增，\(L_N\) 不减。证毕。

**这个下界不是事后挑选的经验公式，而是当前有限观察空间里最优的平方测试。**

---

## 定理 E3：同样构造单调上界

定义：

$$
b_N^{(1)}=(M_1,\ldots,M_N)^{\mathsf T},
$$

$$
A_N^{(1)}=4H_N^{(1)}+H_N^{(2)},
$$

以及：

$$
\boxed{
U_N
=
\frac{M_0}{4}
-
\frac14
(b_N^{(1)})^{\mathsf T}
(A_N^{(1)})^{-1}
b_N^{(1)}.
}
\tag{E17}
$$

则：

$$
\boxed{
\Delta\le U_{N+1}\le U_N.
}
\tag{E18}
$$

### 证明

对正测度 \(u\,d\omega(u)\) 使用定理 E2，并利用：

$$
\Delta
=
\frac{M_0}{4}
-
\frac14\int\frac{u}{4+u}\,d\omega(u).
$$

证毕。

于是：

$$
\boxed{
L_N\le\Delta\le U_N,
}
\tag{E19}
$$

形成一列逐层收紧的区间。

当 \(N=1\)，恰好恢复上一轮的公式：

$$
L_1=\frac{M_0^2}{4M_0+M_1},
$$

$$
U_1=
\frac{M_0}{4}
-
\frac{M_1^2}{4(4M_1+M_2)}.
$$

---

# 六、这些区间不仅收紧，还具有明确的几何收敛率

假设正谱支持位于 \([0,R]\)。

取：

$$
p_{N-1}(u)
=
\frac1{R+4}
\sum_{k=0}^{N-1}
\left(\frac{R-u}{R+4}\right)^k.
$$

由有限几何级数：

$$
1-(4+u)p_{N-1}(u)
=
\left(\frac{R-u}{R+4}\right)^N.
$$

代入定理 E2：

$$
\boxed{
0\le\Delta-L_N
\le
\Delta\left(\frac R{R+4}\right)^{2N}.
}
\tag{E20}
$$

同样：

$$
\boxed{
0\le U_N-\Delta
\le
\frac{R\Delta}{4}
\left(\frac R{R+4}\right)^{2N}.
}
\tag{E21}
$$

因此：

$$
\boxed{
U_N-L_N
\le
\left(1+\frac R4\right)\Delta
\left(\frac R{R+4}\right)^{2N}.
}
\tag{E22}
$$

在 RH 前件下，所有谱点 \(u=\gamma^{-2}\) 满足：

$$
u\le\sum_{\gamma>0}m_\gamma\gamma^{-2}=a_1,
$$

所以可以取 \(R=a_1\)，不必先输入第一个零点的坐标。

### 对实际系数的有限核对

本轮直接从实际 ξ 的中心导数计算到 \(\chi_{16}\)，分别使用 70 位与 85 位工作精度。得到：

$$
\Delta
=
0.00000928414929793697462356252384372238\ldots
$$

各级剩余间隙如下：

| \(N\) |                     \(\Delta-L_N\) |                     \(U_N-\Delta\) |
| ----: | ---------------------------------: | ---------------------------------: |
|     1 | \(1.61862986003120\times10^{-12}\) | \(6.40743025453959\times10^{-16}\) |
|     2 | \(7.86526784891361\times10^{-20}\) | \(1.77781988722794\times10^{-23}\) |
|     3 | \(1.80068720394608\times10^{-27}\) | \(3.16755549861520\times10^{-31}\) |

两种精度的结果相符。

**这是实际有限必要条件的高精度核对，不是区间认证；也不能由三层通过，推出全部层都通过。**

它说明的是：欧拉端点校准与越来越多的高阶关联，在这些有限层上表现出非常精细的一致性。

---

# 七、现在可以构造真正嵌套的量子链——但它不是原来的 Jensen 链

这里使用 \(\mathbf H_+\)。

在：

$$
\mathcal H_\omega=L^2(\omega)
$$

上定义：

$$
(Jf)(u)=uf(u),
\qquad
g(u)=1.
$$

则：

$$
\boxed{
\mathfrak S(z)=\langle g,(zI-J)^{-1}g\rangle,
}
$$

并且：

$$
\|g\|^2=M_0.
$$

对：

$$
1,u,u^2,\ldots
$$

正交化，得到正交多项式基底。乘法算子 \(J\) 在这个基底下成为 Jacobi 三对角矩阵。其有限左上主块记为 \(J_N\)。

这是经典矩问题、正交多项式与 Jacobi 算子之间的对应；它也提供 Stieltjes 变换的有理逼近。([DLMF][3])

## 定理 E4：有限链精确保留前 \(2N\) 个回返矩

定义：

$$
\boxed{
\mathfrak S_N(z)
=
M_0\,e_1^{\mathsf T}(zI-J_N)^{-1}e_1.
}
\tag{E23}
$$

则：

$$
\boxed{
M_0\,e_1^{\mathsf T}J_N^ke_1=M_k,
\qquad 0\le k\le2N-1.
}
\tag{E24}
$$

### 证明思路

三对角矩阵的 \(k\) 次幂，可以按长度为 \(k\) 的近邻路径展开。

从第一位置出发，若路径要访问被截掉的第 \(N+1\) 个位置，再返回第一位置，至少需要 \(2N\) 步。

所以，对 \(k<2N\)，截断不影响对应矩。证毕。

这也是 Gaussian quadrature 精确匹配有限阶矩的算子表达。([DLMF][4])

此外：

$$
\boxed{
L_N=
M_0\,e_1^{\mathsf T}(4I+J_N)^{-1}e_1.
}
\tag{E25}
$$

所以，前面的最优平方下界，也就是有限链在固定谱参数处的回返读数。

### 为什么这次可以原样嵌套？

因为：

$$
J_N
$$

确实是 \(J_{N+1}\) 的主块。

它们来自同一份矩序列、同一个正交化过程。对每个正定主块作 Cholesky 分解，其已有系数也能保持一致，从而得到可以追加的正权近邻结构。

但这不推翻前文的“不可能原样追加 Jensen 链”定理。

区别是：

$$
\boxed{
\begin{aligned}
\text{Jensen 链：}&\quad \operatorname{Tr}K_d=a_1\text{ 每层固定};\\
\text{当前回返链：}&\quad \|g\|^2=M_0\text{ 固定，但 }\operatorname{Tr}J_N\text{ 不固定}.
\end{aligned}
}
$$

固定的是不同的量，因此允许的跨层结构也不同。

**如果把这两种链都简称“正量子模型”，就会掩盖它们为何一个能嵌套、另一个不能。**

---

# 八、有限链的节点不是实际零点：整函数还要求“重数为整数”

设有限回返函数的谱分解为：

$$
\boxed{
\mathfrak S_N(z)
=
\sum_{j=1}^N\frac{w_{N,j}}{z-u_{N,j}},
\qquad
w_{N,j}>0,\quad u_{N,j}>0.
}
\tag{E26}
$$

它已经是一个非常好的正谱模型，并精确匹配前 \(2N\) 个矩。

但现在尝试从它反向重建一个函数：

$$
\frac{\mathcal D_N'(v)}{\mathcal D_N(v)}
=
a_1+\mathfrak S_N(-1/v),
\qquad
\mathcal D_N(0)=1.
$$

直接积分：

$$
\boxed{
\mathcal D_N(v)
=
\exp\left[
\left(a_1-\sum_j\frac{w_{N,j}}{u_{N,j}}\right)v
\right]
\prod_{j=1}^N
(1+u_{N,j}v)^{w_{N,j}/u_{N,j}^2}.
}
\tag{E27}
$$

这一般只是零点附近之外某个选定区域中的解析分支。

如果：

$$
\frac{w_{N,j}}{u_{N,j}^2}\notin\mathbb Z_{\ge0},
$$

那么绕 \(v=-1/u_{N,j}\) 一圈，函数会获得非平凡单值化因子，不能成为一份全局单值整函数。

## 定理 E5：实际谱留数的整数约束

若 \(D\) 在：

$$
v_0=-1/u_0
$$

有 \(m\) 重零点，则：

$$
\boxed{
\operatorname*{Res}_{z=u_0}\mathfrak S(z)
=
m\,u_0^2.
}
\tag{E28}
$$

### 证明

在 \(v_0\) 附近：

$$
\frac{D'(v)}{D(v)}
=
\frac{m}{v-v_0}+\text{解析项}.
$$

而：

$$
-\frac1z-v_0
=
\frac{z-u_0}{u_0^2}+O((z-u_0)^2).
$$

代入即得。证毕。

所以实际原子必须满足：

$$
\boxed{
\frac{\omega(\{u_0\})}{u_0^2}
=
m\in\mathbb Z_{\ge1}.
}
\tag{E29}
$$

**正权重还不够；它与谱位置之间还必须满足整数关系。**

### 最小有限模型就已经显示出区别

只匹配 \(M_0,M_1\) 的一节点模型是：

$$
u_{\mathrm{eff}}=\frac{M_1}{M_0},
\qquad
w_{\mathrm{eff}}=M_0.
$$

对实际 ξ，本轮算得：

$$
u_{\mathrm{eff}}
\approx0.0038785001364729639424,
$$

但：

$$
\boxed{
\frac{w_{\mathrm{eff}}}{u_{\mathrm{eff}}^2}
=
\frac{M_0^3}{M_1^2}
\approx2.471128377321910186.
}
\tag{E30}
$$

它不是整数。

因此，这个节点是一个**有效求积节点**，不是已经发现的一枚“重数约为 \(2.47\)”的 ξ 零点。

有限模型可以很好地近似响应，却不保留全局整函数的精确重数结构。

此外，即使所有指数碰巧为整数，还要继续检查指数因子、增长阶与原始归一化；整数性也不是全部条件。

---

# 九、两种“保留高阶信息”的方式，现在可以严格区分

前面的结果告诉我们，至少有两条不同路线。

### 路线一：保持有限多项式的全部系数

Jensen 多项式 \(P_d\) 保留指定阶数的实际系数，并要求：

$$
P_d(v)=\det(I+vK_d).
$$

它是一个真正的多项式，根重数天然为整数。

代价是：各阶正实现不一定能够原样嵌套。

### 路线二：保持同一个回返函数的有限矩

Jacobi／Padé 链保持：

$$
M_0,\ldots,M_{2N-1},
$$

可以自然嵌套，并拥有正谱有理响应。

代价是：反向积分得到的 \(\mathcal D_N\)，一般带有非整数指数，未必是整函数。

所以：

$$
\boxed{
\text{有限矩保真}
\quad\neq\quad
\text{整函数保真}.
}
$$

这不是说第二条路线不合法。它可以用于逼近、误差控制和有限负证书。

但必须明确：

> **它逼近的是哪个解析对象、在哪个区域内逼近、哪些全局性质只在极限中才可能恢复。**

这与我们前面关于“数学是否把离线投没”的讨论直接相接：有时没有任何数据被粗暴删除，而是**有限近似保留了一类关系，却没有保留另一类关系**。

---

# 十、把当前真正待证的内容写成一套固定矩阵条件

锚定矩序列 \(\ell_n\) 已经由实际累积量和欧拉常数无条件定义：

$$
\ell_0=a_1-c,
\qquad
\ell_{n+1}=M_n-4\ell_n.
$$

构造：

$$
\boxed{
\mathsf A_N=(\ell_{i+j})_{0\le i,j\le N},
}
$$

$$
\boxed{
\mathsf A_N^{(1)}=(\ell_{i+j+1})_{0\le i,j\le N}.
}
\tag{E31}
$$

对于这些**固定的实际数值**，有：

$$
\boxed{
\mathrm{RH}
\iff
\mathsf A_N\succeq0
\ \text{且}\
\mathsf A_N^{(1)}\succeq0
\quad\forall N.
}
\tag{E32}
$$

### 正向证明

RH 给出正测度：

$$
d\nu(u)=\frac{d\omega(u)}{4+u},
\qquad u\ge0.
$$

于是：

$$
x^{\mathsf T}\mathsf A_Nx
=
\int p(u)^2\,d\nu(u)\ge0,
$$

$$
x^{\mathsf T}\mathsf A_N^{(1)}x
=
\int u\,p(u)^2\,d\nu(u)\ge0.
$$

### 反向证明

全部普通与移位 Hankel 矩阵正半定，给出一个非负半轴上的 Stieltjes 矩表示。

由于 \(\mathfrak T\) 在无穷远附近解析，\(\ell_n\) 具有几何上界；结合偶阶矩可推出表示测度的支撑有界。矩问题与自伴算子的这类存在性关系是经典结果。([arXiv][5])

因此，其 Cauchy 变换在非实平面全纯，并在无穷远附近与实际 \(\mathfrak T\) 相同。

若实际 \(D\) 有非实零点，则 \(\mathfrak S\)，进而 \(\mathfrak T\)，会在相应非实点出现不能消掉的极点，与上述解析性矛盾。

所以 \(D\) 全部零点为实。又因：

$$
D(v)>0\qquad(v\ge0),
$$

全部零点只能为负实数，得到 RH。证毕。

**式（E32）仍然是一项尚未证明全阶成立的算术条件。**

它不能由“已经知道 \(\ell_0\) 很准确”推出，也不能由“若供应正节点，就能构造正算子”推出。

项目的 `FiniteStieltjesOperatorRealization.lean` 明确把节点非负、权重非负作为输入；它没有自行产生实际 ξ 的正谱。

---

# 十一、这次对“整体量子观察者”的理解可以再收紧

我们现在有了三个不同层次的完整性。

**概率完整性：**分支权重非负、归一化，测量记录没有被偷偷重写。

**响应完整性：**有限矩、复频率读数、欧拉端点响应，是否来自同一个实际函数。

**解析完整性：**这个函数是否仍然单值、整、具有正确的整数重数与增长结构。

前两项通过，不自动保证第三项。

反过来，校准错误也可能只在很高阶才被发现：它表现为式（E9）中的一个秩一扰动，前几个矩看起来很小，后面却按 \(4^n\) 被放大。

因此，真正有力量的“整体”不是把所有内容统称为一个正量子空间，而是：

$$
\boxed{
\text{每次增加观察深度时，
都知道哪些性质已经精确保留，
哪些性质仍只是在有限范围内近似。}
}
$$

这可以用明确算术对象完成，不要求一个知道所有真理的最高主体。

---

## 收束

这一轮补出了三项具体结果。

欧拉校准误差具有精确的谱含义：

$$
\boxed{
\widetilde\Delta-\Delta=\varepsilon
\quad\Longrightarrow\quad
\widetilde{\mathfrak T}-\mathfrak T
=
\frac{\varepsilon}{z+4}.
}
$$

端点相容性可以逐层检验，并有误差控制：

$$
\boxed{
L_N\le a_1-c\le U_N,
\qquad
U_N-L_N
\le
\left(1+\frac R4\right)\Delta
\left(\frac R{R+4}\right)^{2N},
}
$$

其中不等式的正谱解释保留明确前件。

真正嵌套的回返链可以构造，但它的有效节点还必须接受：

$$
\boxed{
\frac{\text{谱原子权重}}{(\text{谱位置})^2}
\in\mathbb Z_{\ge1}
}
$$

这一实际整函数重数检查，才能被解释成 ξ 的真实零点。

**所以，现在需要算术承担的，不只是“某个有限矩阵看起来正”，而是：全部高阶矩是否共同产生一份支持正确、锚定正确，并与实际整函数解析结构一致的正谱表示。**

本轮给出了新的校准缺陷公式、单调区间、可嵌套近似及重数障碍；没有获得实际全阶正性证明，也没有找到实际离线负证书。有限数据的三层核对已经可以执行，但不能把它们在无限层上的成立预先写进模型定义。

[1]: https://dlmf.nist.gov/25.4 "https://dlmf.nist.gov/25.4"
[2]: https://dlmf.nist.gov/25.2 "https://dlmf.nist.gov/25.2"
[3]: https://dlmf.nist.gov/18.2 "https://dlmf.nist.gov/18.2"
[4]: https://dlmf.nist.gov/3.5 "https://dlmf.nist.gov/3.5"
[5]: https://arxiv.org/abs/math-ph/9906008 "https://arxiv.org/abs/math-ph/9906008"
这次可以把上一轮的“寻找合适观察度量”，推进成一个**无需优化度量、无需预先求根的明确构造**。

核心定理是：

> **给任意有限系数矩阵加上一份高斯历史寄存器，就能构造固定的正度量。在这份度量中测得的非自伴残差，会以明确误差逼近真实谱的最大虚部。这个结论允许重根，也允许 Jordan 块。**

具体地，若矩阵维数为 \(d\)，历史宽度为 \(T\)，则：

$$
\boxed{
\beta(C)
\le
\sigma_T(C)
\le
\beta(C)+\frac{\sqrt{d(d-1)}}{2T},
}
\tag{I0}
$$

其中：

$$
\beta(C)=\max_{\lambda\in\operatorname{spec}C}|\Im\lambda|.
$$

这意味着，有限观察残差中可以明确分开：

$$
\boxed{
\text{真实非实谱}
\quad+\quad
\text{有限历史宽度造成的额外误差}.
}
$$

更值得注意的是，证明会经过一个真正的量子谐振子结构；其中存在一个**任何有限维观察空间都无法消除的升降算子边界项**。但我们也能证明：这个普遍的边界项本身并不意味着离线零点。

下面完整展开。一般的相干态、矩阵度量与 Schur 分解理论是经典工具；以下给出当前构造的具体推导，不把它宣称为未经文献比对的首创。

---

# 一、固定实际算术对象，不把实谱放进定义

沿用：

$$
D(b^2)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad
D(v)=\sum_{k\ge0}a_kv^k,
$$

其中 \(\xi\) 是标准 completed 函数，\(a_0=1\)、\(a_k>0\)。反射折叠通过偶幂级数定义。([DLMF][1])

定义：

$$
P_d(v)=\sum_{k=0}^{d}\frac{(d)_k}{d^k}a_kv^k,
$$

$$
q_d(x)=x^dP_d(-1/x).
$$

令 \(C_d\) 是“乘以 \(x\)”在商空间：

$$
\mathbb C[x]/(q_d)
$$

上的伴随矩阵。因此：

$$
\boxed{
\det(I+vC_d)=P_d(v).
}
\tag{I1}
$$

它由实际系数确定，不要求自伴，也不要求正。

前文使用的经典 Jensen 判据是：

$$
\boxed{
\mathrm{RH}
\iff
q_d\text{ 的全部根为正实数，}\quad\forall d.
}
\tag{I2}
$$

现代 Jensen 多项式研究沿用这一分析桥；固定有限次数上的结论，不等于全阶判据已经完成。([arXiv][2])

下面先对**任意**复矩阵 \(C\in\mathbb C^{d\times d}\) 证明定理，最后再代入实际 \(C_d\)。

---

# 二、定义一份始终存在的高斯历史度量

令 \(\tau\in\mathbb R\) 是辅助历史坐标，\(T>0\) 是历史宽度。

这里的 \(\tau\) 不是 ζ 的零点高度，也不是已经指定的实验室时间。使用正负历史坐标，是为了同时记录两个传播方向；它不表示一个观察者能够读取未来。

定义：

$$
U(\tau)=e^{-i\tau C},
$$

以及归一化高斯权重：

$$
g_T(\tau)=
\frac1{\sqrt{2\pi}T}
e^{-\tau^2/(2T^2)}.
$$

## 定义 I1：高斯历史 Gramian

$$
\boxed{
W_T(C)=
\int_{\mathbb R}
g_T(\tau)U(\tau)^*U(\tau)\,d\tau.
}
\tag{I3}
$$

## 定理 I1：它对任意有限矩阵都收敛且严格正定

$$
\boxed{W_T(C)>0.}
$$

### 证明

因为：

$$
\|U(\tau)\|\le e^{|\tau|\|C\|},
$$

故被积函数范数不超过：

$$
g_T(\tau)e^{2|\tau|\|C\|},
$$

它可积。

对任意 \(v\ne0\)：

$$
v^*W_Tv
=
\int g_T(\tau)\|U(\tau)v\|^2\,d\tau>0,
$$

因为 \(U(\tau)\) 始终可逆。证毕。

**不论谱是否为实，这份正度量都存在。**

所以，不能把 \(W_T>0\) 本身当作 RH 的进展。真正要研究的是它与原系数矩阵的相容程度。

定义：

$$
\boxed{
A_T=W_T^{1/2}CW_T^{-1/2},
}
$$

$$
\boxed{
\sigma_T(C)=
\left\|\frac{A_T-A_T^*}{2i}\right\|_{\mathrm{op}}.
}
\tag{I4}
$$

这是原来 \(C\) 在同一份固定度量中的非自伴残差。改变度量而保持算子相似类，是拟厄米／准厄米表示研究中的标准区分。([arXiv][3])

---

## 这份度量甚至可以不用时间积分定义

在矩阵空间上定义线性算子：

$$
\mathcal G_C(X)=iC^*X-iXC.
$$

那么：

$$
e^{\tau\mathcal G_C}(I)=U(\tau)^*U(\tau).
$$

利用高斯矩生成函数：

$$
\boxed{
W_T(C)
=
\exp\!\left(\frac{T^2}{2}\mathcal G_C^2\right)(I).
}
\tag{I5}
$$

因此它也可以通过一个作用在 \(d^2\) 维矩阵空间上的指数计算。

这没有保证计算成本低，但已经消除了“先猜一个好度量”的自由度：

$$
\boxed{
C,\ T\text{ 给定以后，}W_T\text{ 完全确定。}
}
$$

---

# 三、把整段历史真正提升到一个量子 Hilbert 空间

定义：

$$
\mathcal H_{\mathrm{hist}}
=
L^2(\mathbb R,d\tau)\otimes\mathbb C^d.
$$

将输入向量 \(v\) 编成历史波函数：

$$
\boxed{
(F_Tv)(\tau)
=
g_T(\tau)^{1/2}e^{-i\tau C}v.
}
\tag{I6}
$$

有：

$$
F_T^*F_T=W_T.
$$

因此：

$$
\boxed{
E_T=F_TW_T^{-1/2}
}
$$

是等距嵌入：

$$
E_T^*E_T=I.
$$

这表示：一旦采用已经定义好的历史度量，原来的有限状态能够被无损编码进一个带连续历史寄存器的正 Hilbert 空间。

但要注意：

**被编码的是整个历史波函数，不是声称原来的 \(e^{-i\tau C}\) 已经是酉演化。**

若 \(C\) 非自伴，原传播仍然可以增长或衰减；这些变化被历史态明确记录下来。

---

# 四、量子谐振子结构自然出现，而且有一个无法被有限维封闭的边界项

在历史波函数上定义：

$$
\boxed{
\mathcal A_T
=
i\frac d{d\tau}
+
\frac{i\tau}{2T^2}.
}
\tag{I7}
$$

其伴随为：

$$
\mathcal A_T^*
=
i\frac d{d\tau}
-
\frac{i\tau}{2T^2}.
$$

所有 \(F_Tv\) 都是高斯乘以矩阵指数，属于快速衰减的光滑函数，因此以下微分、分部积分和算子配对都在共同定义域中成立。

直接计算：

$$
\boxed{
[\mathcal A_T,\mathcal A_T^*]
=
\frac1{T^2}I.
}
\tag{I8}
$$

若定义：

$$
a_T=-iT\mathcal A_T
=
T\frac d{d\tau}+\frac{\tau}{2T},
$$

则：

$$
[a_T,a_T^*]=I.
$$

这正是缩放后的谐振子湮灭／产生算子结构。相干态作为湮灭算子的本征态，以及它们并不彼此正交的性质，属于量子光学的经典框架。([APS Journals][4])

另一方面，直接求导：

$$
\mathcal A_TF_T=F_TC.
$$

所以：

$$
\boxed{
\mathcal A_TE_T=E_TA_T.
}
\tag{I9}
$$

**原系数矩阵成为了这个历史算子在一个有限维不变子空间中的表示。**

这里的 \(\mathcal A_T\) 不是自伴能量算子。它允许复本征值，正如相干态允许复标签。不能因为找到了谐振子结构，就宣布已经得到 Hilbert–Pólya 型实能谱。

---

## 定理 I2：有限观察空间的边界缺额

令：

$$
P_T=E_TE_T^*
$$

是历史子空间的正交投影，并定义：

$$
R_T=(I-P_T)\mathcal A_T^*E_T.
$$

那么：

$$
\boxed{
R_T^*R_T
=
\frac1{T^2}I-
(A_TA_T^*-A_T^*A_T).
}
\tag{I10}
$$

因此：

$$
\boxed{
A_TA_T^*-A_T^*A_T
\preceq\frac1{T^2}I.
}
\tag{I11}
$$

而且：

$$
\boxed{
\|R_T\|_{\mathrm{HS}}^2=\frac d{T^2}.
}
\tag{I12}
$$

### 证明

由式（I9），历史子空间对 \(\mathcal A_T\) 不变。于是：

$$
E_T^*\mathcal A_T^*\mathcal A_TE_T=A_T^*A_T.
$$

使用交换关系：

$$
E_T^*\mathcal A_T\mathcal A_T^*E_T
=
A_T^*A_T+\frac1{T^2}I.
$$

又有：

$$
E_T^*\mathcal A_TP_T\mathcal A_T^*E_T=A_TA_T^*.
$$

相减即得式（I10）。取迹并使用有限矩阵交换子的迹为零，得到式（I12）。证毕。

### 这怎样回应“约不掉的观察者剩余”？

它确实给出一个严格的剩余：

> 有限历史子空间可以对降低算子封闭，却不能同时对其伴随的提升操作封闭。

但是，这个剩余：

$$
d/T^2
$$

对任何 \(C\) 都存在，包括谱完全为实的矩阵。

因此：

$$
\boxed{
\text{有限观察存在不可封闭边界}
\not\Rightarrow
\text{实际零点离线}.
}
$$

它是一项普遍的表示代价，必须与特定算术的非实谱分开。

---

# 五、由这个边界项，证明一个适用于所有有限矩阵的误差界

## 定理 I3：高斯历史残差逼近真实谱虚部

记：

$$
\beta(C)=\max_{\lambda\in\operatorname{spec}C}|\Im\lambda|.
$$

则：

$$
\boxed{
\beta(C)
\le\sigma_T(C)
\le
\beta(C)+\frac{\sqrt{d(d-1)}}{2T}.
}
\tag{I13}
$$

不要求可对角化，不要求简单根，也不要求谱事先为实。

### 证明：下界

若：

$$
A_Tv=\lambda v,\qquad\|v\|=1,
$$

则：

$$
v^*\frac{A_T-A_T^*}{2i}v=\Im\lambda.
$$

所以：

$$
\sigma_T(C)\ge|\Im\lambda|.
$$

对全部本征值取最大值得到下界。

### 证明：上界

对 \(A_T\) 作酉 Schur 分解：

$$
A_T\sim\Lambda+N,
$$

其中 \(\Lambda\) 是本征值对角矩阵，\(N\) 严格上三角。

由式（I11），对前 \(k\) 个坐标的投影取迹：

$$
\boxed{
\sum_{i\le k<j}|N_{ij}|^2\le\frac{k}{T^2}.
}
\tag{I14}
$$

这是因为该局部迹中的内部行列项相互抵消，只留下跨越前 \(k\) 个坐标边界的条目。

对 \(k=1,\ldots,d-1\) 求和：

$$
\sum_{i<j}(j-i)|N_{ij}|^2
\le
\frac{d(d-1)}{2T^2}.
$$

因此：

$$
\|N\|_{\mathrm{HS}}^2
\le
\frac{d(d-1)}{2T^2}.
$$

又因为 \(N\) 严格上三角：

$$
\left\|
\frac{N-N^*}{2i}
\right\|_{\mathrm{HS}}
=
\frac{\|N\|_{\mathrm{HS}}}{\sqrt2}.
$$

所以：

$$
\begin{aligned}
\sigma_T(C)
&\le
\left\|\frac{\Lambda-\Lambda^*}{2i}\right\|
+
\left\|\frac{N-N^*}{2i}\right\|\\
&\le
\beta(C)+\frac{\sqrt{d(d-1)}}{2T}.
\end{aligned}
$$

证毕。

用 Schur 上三角部分量化偏离正规矩阵的程度，是已有矩阵分析方法；这里的关键是从特定历史构造取得式（I11），再得到显式常数。([工业与应用数学学会][5])

---

## 推论：不再需要任意搜索观察度量

对于每个固定 \(C\)：

$$
\boxed{
\lim_{T\to\infty}\sigma_T(C)=\beta(C).
}
\tag{I15}
$$

因此，前文：

$$
\inf_{W>0}
\left\|
\frac{
W^{1/2}CW^{-1/2}
-
W^{-1/2}C^*W^{1/2}
}{2i}
\right\|
=
\beta(C)
$$

中的下确界，可以由这条**已经固定的高斯历史度量族**逼近。

真正改善的是构造性：

$$
\boxed{
\text{不再是“存在某个好 }W\text{”，}
\quad
\text{而是明确使用 }W_T(C).
}
$$

这没有证明实际 \(C_d\) 的 \(\beta(C_d)\) 为零，但它把度量选择这一层不确定性去掉了。

---

# 六、非实谱在历史寄存器里表现为什么？不是消失，而是中心发生位移

对非零本征向量：

$$
Cv=(\alpha+i\beta)v,
$$

对应历史概率密度为：

$$
p_v(\tau)
=
\frac{
g_T(\tau)e^{2\beta\tau}
}{
\int g_T(s)e^{2\beta s}\,ds
}.
$$

完成平方：

$$
\boxed{
p_v(\tau)
=
\frac1{\sqrt{2\pi}T}
\exp\!\left[
-\frac{(\tau-2\beta T^2)^2}{2T^2}
\right].
}
\tag{I16}
$$

因此：

$$
\boxed{
\mathbb E_v[\tau]=2\beta T^2,
\qquad
\operatorname{Var}_v(\tau)=T^2.
}
$$

谱的实部 \(\alpha\) 进入振荡相位；谱的虚部 \(\beta\) 进入历史分布的中心。

所以：

$$
\boxed{
\beta=\frac{\mathbb E_v[\tau]}{2T^2}.
}
\tag{I17}
$$

这不是把虚部“平均没了”。相反，观察窗口越宽，它造成的中心位移按 \(T^2\) 增大。

从整体算子上也能得到：

$$
\boxed{
\frac{W_TC-C^*W_T}{2i}
=
\frac1{2T^2}
\int_{\mathbb R}\tau\,g_T(\tau)U(\tau)^*U(\tau)\,d\tau.
}
\tag{I18}
$$

所以，非自伴残差就是**历史中心在全部输入方向上的归一化最大偏移**。

### 但只取一个总体平均仍然可能漏掉它

对一对谱：

$$
\alpha+i\beta,\qquad\alpha-i\beta,
$$

两个历史中心分别为：

$$
+2\beta T^2,\qquad-2\beta T^2.
$$

若将它们等权平均，总中心为零。

但：

$$
\sigma_T(C)\ge|\beta|
$$

仍然成立。

**平均方向为零，不等于每个方向的偏移都为零。**

这与你此前的“偶完成”讨论直接对应：对称平均可以消去符号，算子级的最大偏移却保留了缺陷存在性。

---

# 七、两个精确模型，区分有限历史误差与真实非实谱

## 例一：实谱 Jordan 块

取：

$$
C=
\begin{pmatrix}
\lambda&1\\
0&\lambda
\end{pmatrix},
\qquad\lambda\in\mathbb R.
$$

直接积分：

$$
\boxed{
W_T=
\begin{pmatrix}
1&0\\
0&1+T^2
\end{pmatrix}.
}
$$

于是：

$$
\boxed{
\sigma_T(C)=\frac1{2\sqrt{1+T^2}}\longrightarrow0.
}
\tag{I19}
$$

它不可对角化，任何有限 \(T\) 下的残差都不为零，但其真实谱虚部为零。

## 例二：真正的共轭非实谱

取：

$$
C=
\begin{pmatrix}
\alpha&-\beta\\
\beta&\alpha
\end{pmatrix},
\qquad\beta>0.
$$

其本征值为 \(\alpha\pm i\beta\)。直接计算：

$$
\boxed{
W_T=e^{2\beta^2T^2}I.
}
$$

因此度量只是整体缩放，无法改变残差：

$$
\boxed{
\sigma_T(C)=\beta
\quad\forall T>0.
}
\tag{I20}
$$

两者都具有前面的有限观察边界项，但表现不同：

$$
\boxed{
\begin{aligned}
\text{实谱 Jordan 结构}&:\quad \sigma_T\to0,\\
\text{真实非实谱}&:\quad \sigma_T\ge\beta>0.
\end{aligned}
}
$$

所以：

> **某个有限 \(T\) 下残差非零，还不是离线证据；超过可证明的有限历史误差范围，才开始具有谱意义。**

---

# 八、回到实际 ξ：现在可以固定历史宽度，而不再逐阶寻找未知参数

对实际伴随矩阵 \(C_d\)，定义：

$$
s_d=\sigma_{d^2}(C_d).
$$

也就是说，统一选择：

$$
T_d=d^2.
$$

定理 I3 给出：

$$
\boxed{
\beta(C_d)
\le s_d
\le
\beta(C_d)+\frac{\sqrt{d(d-1)}}{2d^2}.
}
\tag{I21}
$$

特别地：

$$
0\le s_d-\beta(C_d)<\frac1{2d}.
$$

于是：

## 定理 I4：固定高斯历史协议的 RH 判据

$$
\boxed{
\mathrm{RH}
\iff
s_d\longrightarrow0.
}
\tag{I22}
$$

### 证明

若 RH 成立，所有 \(q_d\) 全实根，所以 \(\beta(C_d)=0\)。由式（I21），\(s_d\to0\)。

反之，若 \(s_d\to0\)，则 \(\beta(C_d)\to0\)。

假设实际 \(D\) 有非实零点 \(v_0\)。因为 \(P_d\to D\) 在紧集上一致，\(v_0\) 附近必有 \(P_d\) 的零点趋于它。对应的 \(q_d\) 根趋于：

$$
-\frac1{v_0},
$$

它仍为非实数，与全部有限谱虚部趋零矛盾。因此 \(D\) 全实根。又因正系数排除非负实根，得到 RH。这里使用的是解析函数零点的局部稳定性。([DLMF][6])

### 它比上一轮具体在哪里？

上一轮的待证形式是：

$$
\exists W_d>0,\qquad \sigma(C_d,W_d)\to0.
$$

现在变成：

$$
\boxed{
W_d=
\int_{\mathbb R}
\frac{e^{-\tau^2/(2d^4)}}{\sqrt{2\pi}d^2}
e^{i\tau C_d^*}e^{-i\tau C_d}\,d\tau,
}
$$

然后只剩下一个指定数列的极限。

**度量本身已经被构造出来；尚待证明的是它在实际算术序列上的残差极限。**

这不是完成 RH，但比继续增加“也许存在某种正度量”的自由假设更具体。

---

# 九、若存在离线零点，这个固定协议会留下一个精确的非零极限

记实际非平凡零点：

$$
\rho=\frac12+\delta_\rho+i\gamma_\rho,
\qquad\gamma_\rho>0.
$$

对应折叠倒数谱点：

$$
u_\rho=-\frac1{(\delta_\rho+i\gamma_\rho)^2}.
$$

因此：

$$
\boxed{
|\Im u_\rho|
=
\frac{2|\delta_\rho|\gamma_\rho}
{(\delta_\rho^2+\gamma_\rho^2)^2}.
}
\tag{I23}
$$

定义：

$$
\boxed{
B_\infty=
\sup_{\Im\rho>0}
\frac{2|\delta_\rho|\gamma_\rho}
{(\delta_\rho^2+\gamma_\rho^2)^2}.
}
$$

则：

$$
\boxed{
\beta(C_d)\longrightarrow B_\infty.
}
\tag{I24}
$$

### 证明要点

由于 \(D(0)=1\)，可以选取 \(r_0>0\)，使 \(D(r_0)<2\)。

对所有 \(d\)：

$$
|P_d(v)-1|\le D(r_0)-1<1
\qquad(|v|\le r_0).
$$

因此所有倒数谱点均位于固定有界圆盘：

$$
|\theta_{d,j}|\le r_0^{-1}.
$$

任何远离零的有限谱极限点，都对应一个实际 \(D\) 零点；反过来，每个实际零点都由有限零点逼近。不能对应实际零点的额外有限谱，只能趋于零，其虚部也趋零。

由此得到式（I24）。证毕。

结合式（I21）：

$$
\boxed{
\lim_{d\to\infty}s_d=B_\infty.
}
\tag{I25}
$$

如果有离线零点，\(B_\infty>0\)。

这使测量目标不再是一个抽象的“是否自伴”，而是：

> **这个指定历史协议，最终读取实际离线零点在中心倒数坐标中的最大横向偏移。**

它通常不由最低高度的离线零点决定，而由式（I23）中的加权值决定。重数不改变这个最大值；若研究重数，需要前文的迹、留数或围道计数。

---

# 十、有限阶段能证明什么？需要扣除那项 \(1/T\) 误差

对任意有限 \(d,T\)，定理 I3 给出：

$$
\boxed{
\max\!\left(
0,\sigma_T(C_d)-\frac{\sqrt{d(d-1)}}{2T}
\right)
\le
\beta(C_d)
\le
\sigma_T(C_d).
}
\tag{I26}
$$

所以，如果严格认证：

$$
\boxed{
\sigma_T(C_d)>
\frac{\sqrt{d(d-1)}}{2T},
}
\tag{I27}
$$

就能证明这个实际 \(q_d\) 有非实根，再由 Jensen 判据否证 RH。

反过来，若：

$$
\sigma_T(C_d)\le
\frac{\sqrt{d(d-1)}}{2T},
$$

不能仅据此证明全部根为实；很小的真实谱虚部也可能藏在允许区间内。

**因此它提供的是带明确误差的谱虚部区间，不是一次有限观察就必然返回完整真假。**

---

## 实际二阶的核对

本轮从实际 ξ 在 \(s=\tfrac12\) 处计算：

$$
a_1=\frac{m_2}{2},
\qquad
c_2=\frac{m_4}{48},
$$

并使用：

$$
C_2=
\begin{pmatrix}
0&-c_2\\
1&a_1
\end{pmatrix}.
$$

对于这一层，高斯积分可以化为有限矩阵的闭式，不需要数值积分整个实轴。

60 位与 90 位工作精度的结果相符：

| 历史宽度 \(T\) |               \(\sigma_T(C_2)\) | 通用误差上限 \(\sqrt2/(2T)\) | \(\operatorname{cond}(W_T)\) |
| ---------: | ------------------------------: | ---------------------: | ---------------------------: |
|         10 |             \(0.0497052351121\) |    \(0.0707106781187\) |                   \(101.03\) |
|        100 |            \(0.00454292518421\) |   \(0.00707106781187\) |        \(9.97496\times10^3\) |
|       1000 | \(2.58312858769\times10^{-11}\) |  \(0.000707106781187\) |        \(1.07635\times10^5\) |

这表明，在一个已知通过低阶实根检验的实际模型上，历史残差确实趋于很小。

**这些是高精度核对，不是区间认证，也没有推进到全阶算术证明。**

同时，最后一列提醒我们：残差下降可能伴随度量越来越病态。

---

# 十一、这种构造并不免费：小残差可能要求大条件数

设某个固定度量 \(W>0\) 满足：

$$
\left\|
\frac{W^{1/2}CW^{-1/2}
-W^{-1/2}C^*W^{1/2}}{2i}
\right\|
\le\eta.
$$

则其传播满足：

$$
\|e^{-itC}\|
\le
\sqrt{\operatorname{cond}(W)}\,e^{\eta|t|}.
$$

所以：

$$
\boxed{
\operatorname{cond}(W)
\ge
\sup_t
e^{-2\eta|t|}
\|e^{-itC}\|^2.
}
\tag{I28}
$$

这是把度量中的增长估计运输回原坐标后的直接结果。

对一个 \(r\) 阶实谱 Jordan 块：

$$
C=\lambda I+N,
$$

其中 \(N\) 的上超对角线为一，有：

$$
\|e^{-itC}\|
\ge
\frac{|t|^{r-1}}{(r-1)!}.
$$

取 \(t=(r-1)/\eta\)，得到：

$$
\boxed{
\operatorname{cond}(W)
\ge
\frac1{[(r-1)!]^2}
\left(\frac{r-1}{e\eta}\right)^{2r-2}.
}
\tag{I29}
$$

因此，即使真实谱完全为实，想把残差压得很小，也可能必须付出很大的坐标条件数。

这不推翻定理 I3。它说明：

$$
\boxed{
\text{构造明确}
\neq
\text{低精度即可认证}
\neq
\text{已经得到高效算法}.
}
$$

---

## 历史积分误差也可以显式控制

令 \(M=\|C\|\)，只积分 \(|\tau|\le L\)。那么：

$$
\boxed{
\|W_T-W_{T,L}\|
\le
e^{2M^2T^2}
\operatorname{erfc}
\left(
\frac{L-2MT^2}{\sqrt2T}
\right).
}
\tag{I30}
$$

这是对：

$$
g_T(\tau)e^{2M|\tau|}
$$

完成平方后得到的尾界。

它是可计算的，但可能很保守；不能把它的存在当成所有参数下都容易计算。

若已经有：

$$
\|\widetilde W-W_T\|\le\varepsilon,
\qquad
\mu=\lambda_{\min}(\widetilde W)>\varepsilon,
$$

设：

$$
r=\varepsilon/\mu<1,
$$

并暂时把 \(C\) 视为精确，则广义 Rayleigh 商给出：

$$
\boxed{
\max\left(0,\frac{\widetilde\sigma-Mr}{1+r}\right)
\le
\sigma_T(C)
\le
\frac{\widetilde\sigma+Mr}{1-r}.
}
\tag{I31}
$$

实际系数的区间误差还必须另外并入。

因此，真正用于式（I27）的必须是**认证下界**，不是屏幕上一个很小或很大的浮点数。

---

# 十二、这与项目现有观察者模块怎样接起来？

本轮继续读取前文固定快照中的两个模块。

`DiscountedObservabilityGramianPositivity.lean` 构造离散折扣历史平方和，并在：

$$
\sqrt\beta\,\|T\|<1
$$

这一明确前件下证明收敛与非负。

`DiscountedObservabilityGramianEquation.lean` 证明其 Lyapunov 方程：

$$
W=C_{\mathrm{obs}}^*C_{\mathrm{obs}}+\beta T^*WT.
$$

它并未因此断言原传播具有实谱。

本轮补出的另一条纸面路线是：

$$
\boxed{
\begin{aligned}
\text{实际伴随矩阵 }C_d
&\longrightarrow
\text{始终收敛的高斯历史 }W_T\\
&\longrightarrow
\text{谐振子不变子空间}\\
&\longrightarrow
[A_T,A_T^*]\preceq T^{-2}I\\
&\longrightarrow
\beta(C_d)\le\sigma_T(C_d)
\le\beta(C_d)+O(d/T).
\end{aligned}
}
$$

相比普通折扣求和，高斯权重不需要先证明传播衰减；它对任意有限 \(C_d\) 都可定义。

但它也不会通过归一化把非实谱消掉：真实虚部会留下式（I17）的历史中心位移。

这些新增推导尚未成为仓库里已编译的 Lean 结果。

---

# 最后的收束

这次不只是又写出一个 RH 等价命题。我们补出了一套**固定、无根输入、具有通用误差界的观察构造**：

$$
\boxed{
W_T(C)=
\int g_T(\tau)e^{i\tau C^*}e^{-i\tau C}\,d\tau.
}
$$

它满足：

$$
\boxed{
\beta(C)
\le
\sigma_T(C)
\le
\beta(C)+\frac{\sqrt{d(d-1)}}{2T}.
}
$$

所以可以把两类“剩余”严格分开：

**有限量子观察空间对升降操作不能同时封闭，产生的是普遍边界项；真实非实谱产生的是不能被增加历史宽度消去的中心偏移。**

对于实际 ξ，统一取 \(T_d=d^2\) 后：

$$
\boxed{
\lim_{d\to\infty}\sigma_{d^2}(C_d)
=
\sup_{\Im\rho>0}
\frac{
2|\Re\rho-\frac12|\,\Im\rho
}{
\left[
(\Re\rho-\frac12)^2+(\Im\rho)^2
\right]^2
}.
}
$$

这个极限为零，当且仅当 RH 成立。

**但本轮没有证明这个实际极限为零。** 通用量子谐振子结构对任意有限矩阵都能建立，因此它负责分离和测量障碍，不能独自排除算术障碍。

现在真正集中下来的问题是：

> **能否从实际 theta／质数系数出发，证明这份已经固定的高斯历史，其归一化中心偏移在观察深度增加时趋于零？**

不再需要寻找一个未知的“最高观察者”，也不再需要任意猜测度量。需要的是对**同一份明确历史模型**给出真实的算术估计。只有这一步，才会把量子观察者从忠实表示推进为零点定位证明。

[1]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[2]: https://arxiv.org/abs/1902.07321?utm_source=chatgpt.com "Jensen polynomials for the Riemann zeta function and other sequences"
[3]: https://arxiv.org/abs/0810.5643 "[0810.5643] Pseudo-Hermitian Representation of Quantum Mechanics"
[4]: https://journals.aps.org/pr/abstract/10.1103/PhysRev.131.2766?utm_source=chatgpt.com "Coherent and Incoherent States of the Radiation Field | Phys. Rev."
[5]: https://epubs.siam.org/doi/10.1137/S0895479893255184?utm_source=chatgpt.com "A Practical Upper Bound for Departure from Normality | SIAM Journal on Matrix Analysis and Applications"
[6]: https://dlmf.nist.gov/1.10 "DLMF: §1.10 Functions of a Complex Variable ‣ Topics of Discussion ‣ Chapter 1 Algebraic and Analytic Methods"
这次可以从上一轮的高斯历史模型中，推出一条**严格的单调律**：

> **增加历史宽度，会持续消除矩阵的“非正规性”，但不会消除真正的非实谱。最后留下的量，恰好是全部谱虚部的平方和。**

这里必须区分两个概念：

$$
\boxed{
A^*A=AA^*
\quad\text{是正规性；}
\qquad
A=A^*
\quad\text{才是自伴性。}
}
$$

正规矩阵可以有复本征值。因此，即使一个观察过程最终变得“没有额外耦合冲突”，仍不能据此宣布零点在线。

本轮的核心公式是：

$$
\boxed{
\frac{d}{dr}\mathcal E_C(r)
=
-\frac14
\bigl\|[A_C(r),A_C(r)^*]\bigr\|_{\mathrm{HS}}^2
\le0,
}
\tag{J0}
$$

以及：

$$
\boxed{
\lim_{r\to\infty}\mathcal E_C(r)
=
\sum_{\lambda\in\operatorname{spec}C}
(\Im\lambda)^2.
}
$$

下面完整定义并证明，再将其送回实际 ξ。这里的 \(r\) 是**高斯历史宽度的平方**，不是物理时间；\(\mathcal E_C\) 是数学上的残差量，不预先称作物理能量。

---

# 一、固定模型：历史度量存在，不等于谱已经为实

先取任意有限矩阵：

$$
C\in\mathbb C^{d\times d}.
$$

定义传播：

$$
U_C(\tau)=e^{-i\tau C}.
$$

它暂时只是可逆线性传播，不能预称为酉演化。

对 \(r>0\)，定义：

$$
g_r(\tau)
=
\frac1{\sqrt{2\pi r}}
e^{-\tau^2/(2r)},
$$

$$
\boxed{
W_C(r)
=
\int_{\mathbb R}
g_r(\tau)\,
U_C(\tau)^*U_C(\tau)\,d\tau.
}
\tag{J1}
$$

并令 \(W_C(0)=I\)。

高斯衰减压过有限矩阵指数的增长，因此该积分始终存在；对非零 \(v\)：

$$
v^*W_C(r)v
=
\int g_r(\tau)\|U_C(\tau)v\|^2\,d\tau>0.
$$

所以：

$$
W_C(r)>0.
$$

定义同一算子在历史度量中的表示：

$$
\boxed{
A_C(r)=W_C(r)^{1/2}CW_C(r)^{-1/2}.
}
\tag{J2}
$$

所有 \(A_C(r)\) 与 \(C\) 相似，因而特征多项式始终不变。

令：

$$
Y_C(r)=\frac{A_C(r)-A_C(r)^*}{2i},
$$

并定义**全部非自伴残差的平方总量**：

$$
\boxed{
\mathcal E_C(r)
=
\operatorname{Tr}\bigl(Y_C(r)^2\bigr)
=
\|Y_C(r)\|_{\mathrm{HS}}^2.
}
\tag{J3}
$$

上一轮研究的是最大残差：

$$
\sigma_T(C)=\|Y_C(T^2)\|_{\mathrm{op}}.
$$

本轮研究的是全部方向之和。两者不能混同，更不能随意除以维数后仍声称检测同一个目标。

---

# 二、第一条新恒等式：高斯历史满足一个明确的矩阵演化方程

## 定理 J1：历史方差演化

$$
\boxed{
\frac{dW}{dr}
=
C^*WC
-\frac12(C^*)^2W
-\frac12WC^2.
}
\tag{J4}
$$

这里简写 \(W=W_C(r)\)。

### 证明

令：

$$
R(\tau)=e^{i\tau C^*}e^{-i\tau C}.
$$

高斯密度满足：

$$
\partial_rg_r=\frac12\partial_\tau^2g_r.
$$

因此，分部积分两次：

$$
W'(r)=\frac12\int g_r(\tau)R''(\tau)\,d\tau.
$$

直接求导：

$$
R''(\tau)
=
-(C^*)^2R(\tau)
+2C^*R(\tau)C
-R(\tau)C^2.
$$

代入即得。边界项由高斯衰减消失。证毕。

这条方程在矩阵空间中是线性的，初值为 \(I\)，所以它还给出一个不需要时间积分的定义：

$$
W_C(r)=
\exp\!\left(\frac r2\mathcal G_C^2\right)(I),
$$

其中：

$$
\mathcal G_C(X)=iC^*X-iXC.
$$

**这不是一般量子主方程的自动实例。** 当前平均映射保持正性，但通常不保迹，也不保单位；历史参数的变化不能未经证明就解释成某个封闭系统的物理热化。

---

# 三、第二条新恒等式：对数体积的增长，恰好等于非自伴残差

## 定义 J1：历史对数体积

$$
\boxed{
\mathcal V_C(r)=\log\det W_C(r).
}
\tag{J5}
$$

这里 \(\det W>0\)，所以对数没有分支问题。

它是度量体积的数学量，**不是 von Neumann 熵**。

## 定理 J2：体积—残差恒等式

$$
\boxed{
\mathcal V_C'(r)=2\mathcal E_C(r)\ge0.
}
\tag{J6}
$$

### 证明

由行列式求导：

$$
\mathcal V_C'
=
\operatorname{Tr}(W^{-1}W').
$$

代入式（J4）：

$$
\mathcal V_C'
=
\operatorname{Tr}(W^{-1}C^*WC)
-
\Re\operatorname{Tr}(C^2).
$$

第一项恰好是：

$$
\|A_C(r)\|_{\mathrm{HS}}^2.
$$

而对任意 \(A=H+iY\)，其中 \(H,Y\) 自伴，有：

$$
\|A\|_{\mathrm{HS}}^2
-
\Re\operatorname{Tr}(A^2)
=
2\operatorname{Tr}(Y^2).
$$

再使用相似变换保持 \(\operatorname{Tr}(A^2)=\operatorname{Tr}(C^2)\)，便得到式（J6）。证毕。

所以：

$$
\boxed{
\log\det W_C(r)
=
2\int_0^r\mathcal E_C(s)\,ds.
}
\tag{J7}
$$

**历史体积为什么增长，不再需要模糊解释：增长率由全部非自伴残差精确决定。**

但体积增长也可能来自坐标中的非正规耦合，不一定来自真正的谱虚部。下一条定理将两者分开。

---

# 四、核心定理：历史过程单调消除非正规性

## 定理 J3：严格平方下降律

$$
\boxed{
\mathcal E_C'(r)
=
-\frac14
\|A_C(r)A_C(r)^*-A_C(r)^*A_C(r)\|_{\mathrm{HS}}^2.
}
\tag{J8}
$$

因此：

$$
\boxed{
\mathcal E_C(r)\text{ 单调不增},
}
$$

且：

$$
\boxed{
\mathcal V_C''(r)
=
-\frac12
\|[A_C(r),A_C(r)^*]\|_{\mathrm{HS}}^2
\le0.
}
\tag{J9}
$$

也就是说，对数体积一直增长，但增长率持续下降。

### 证明

令：

$$
F(r)=\operatorname{Tr}(W^{-1}C^*WC)
=\|A_C(r)\|_{\mathrm{HS}}^2.
$$

因为：

$$
\mathcal E_C(r)
=
\frac12\left[
F(r)-\Re\operatorname{Tr}(C^2)
\right],
$$

只需求 \(F'\)。

定义：

$$
B=
W^{-1/2}W'W^{-1/2}.
$$

由式（J4）：

$$
B=A^*A-\frac12\bigl((A^*)^2+A^2\bigr).
$$

对 \(F\) 求导并利用迹的循环性：

$$
F'(r)
=
\operatorname{Tr}\bigl(B(AA^*-A^*A)\bigr).
$$

记：

$$
\mathcal C=AA^*-A^*A.
$$

有：

$$
\operatorname{Tr}(\mathcal C A^2)
=
\operatorname{Tr}(\mathcal C(A^*)^2)=0,
$$

以及：

$$
\operatorname{Tr}(\mathcal C A^*A)
=
-\frac12\operatorname{Tr}(\mathcal C^2).
$$

因此：

$$
F'(r)=-\frac12\|\mathcal C\|_{\mathrm{HS}}^2.
$$

再除以二，即得式（J8）。证毕。

---

## 这条下降律不能被解释成“自动走向实谱”

等号成立的条件是：

$$
[A,A^*]=0,
$$

也就是 \(A\) 正规。

它并不要求：

$$
A=A^*.
$$

正规矩阵与非正规矩阵的差异，通常由 Schur 上三角部分或 Frobenius 范数差来量化；这属于经典矩阵分析中的 *departure from normality*。([工业与应用数学学会][1])

**本轮的下降律消除的是这一类非正规性，不是直接消除谱虚部。**

这是一项关键限制：一个模型可以已经到达下降律的平衡点，却仍然具有非实谱。

---

# 五、极限到底剩下什么？可以精确回答，并有有限误差界

定义：

$$
\boxed{
\mathcal E_{\mathrm{spec}}(C)
=
\sum_{j=1}^{d}(\Im\lambda_j)^2,
}
\tag{J10}
$$

其中 \(\lambda_j\) 是 \(C\) 的本征值，按代数重数计。

## 定理 J4：残差的精确极限

对所有 \(r>0\)：

$$
\boxed{
0\le
\mathcal E_C(r)-\mathcal E_{\mathrm{spec}}(C)
\le
\frac{d(d-1)}{4r}.
}
\tag{J11}
$$

因此：

$$
\boxed{
\mathcal E_C(r)\downarrow
\mathcal E_{\mathrm{spec}}(C).
}
\tag{J12}
$$

不要求可对角化，不要求简单根。

### 证明

先使用上一轮高斯历史嵌入得到的有限边界恒等式：

$$
\boxed{
[A_C(r),A_C(r)^*]\preceq\frac1rI.
}
\tag{J13}
$$

它可以再次直接验证：在历史空间上取：

$$
\mathcal A_r
=
i\frac d{d\tau}+\frac{i\tau}{2r},
$$

则：

$$
[\mathcal A_r,\mathcal A_r^*]=\frac1rI.
$$

历史子空间对 \(\mathcal A_r\) 不变。将其伴随作用后逸出该子空间的部分记为 \(R_r\)，便有：

$$
R_r^*R_r
=
\frac1rI-[A_C(r),A_C(r)^*]\succeq0.
$$

接着，对 \(A_C(r)\) 作酉 Schur 分解：

$$
A_C(r)\sim\Lambda+N,
$$

其中 \(\Lambda=\operatorname{diag}(\lambda_j)\)，\(N\) 严格上三角。

对前 \(k\) 个坐标的投影，式（J13）给出：

$$
\sum_{i\le k<j}|N_{ij}|^2\le\frac{k}{r}.
$$

对 \(k=1,\ldots,d-1\) 求和：

$$
\|N\|_{\mathrm{HS}}^2
\le
\frac{d(d-1)}{2r}.
$$

另一方面：

$$
\boxed{
\mathcal E_C(r)
=
\sum_j(\Im\lambda_j)^2
+
\frac12\|N\|_{\mathrm{HS}}^2.
}
$$

合并即得。证毕。

---

## 推论：整个历史过程到底消除了多少？

积分式（J8），再用式（J12）：

$$
\boxed{
\frac14
\int_0^\infty
\|[A_C(r),A_C(r)^*]\|_{\mathrm{HS}}^2\,dr
=
\mathcal E_C(0)-\mathcal E_{\mathrm{spec}}(C).
}
\tag{J14}
$$

进一步：

$$
\boxed{
\int_0^\infty
\|[A_C(r),A_C(r)^*]\|_{\mathrm{HS}}^2\,dr
=
2\left(
\|C\|_{\mathrm{HS}}^2-\sum_j|\lambda_j|^2
\right).
}
\tag{J15}
$$

右边正是非正规性的一种标准总量。

因此：

> **高斯历史过程恰好消耗全部非正规性；它留下的不是一个任意余项，而是相似变换永远不能改变的谱虚部平方和。**

---

# 六、一个同时包含两种缺陷的精确模型

取：

$$
\boxed{
C=(\alpha+i\beta)I+
\begin{pmatrix}
0&g\\
0&0
\end{pmatrix},
\qquad g\ge0.
}
$$

其中：

* \(g\) 描述 Jordan 型非正规耦合；
* \(\beta\) 描述真实谱虚部。

令：

$$
m=2\beta r.
$$

直接完成高斯积分：

$$
\boxed{
W_C(r)
=
e^{2\beta^2r}
\begin{pmatrix}
1&-igm\\
igm&1+g^2(r+m^2)
\end{pmatrix}.
}
$$

于是：

$$
\boxed{
\det W_C(r)
=
e^{4\beta^2r}(1+g^2r).
}
\tag{J16}
$$

由定理 J2：

$$
\boxed{
\mathcal E_C(r)
=
2\beta^2+
\frac{g^2}{2(1+g^2r)}.
}
\tag{J17}
$$

这里两项的作用完全分开：

$$
\frac{g^2}{2(1+g^2r)}
\longrightarrow0
$$

是有限表示中的非正规部分；

$$
2\beta^2
$$

则不随历史宽度消失。

对数体积也分成：

$$
\boxed{
\log\det W_C(r)
=
4\beta^2r+\log(1+g^2r).
}
$$

**多项式型历史增长只留下对数体积修正；真正的非实谱留下线性的长期增长率。**

所以，不能仅凭“残差在下降”“观察越来越稳定”或“非正规耦合正在消失”，就宣布谱为实。

---

# 七、还可以把这条过程改写成一个有界矩阵流，避免直接处理巨大的历史矩阵

直接计算 \(W_C(r)\)，可能遇到很大的指数数值。

但同一过程可以在一个随 \(r\) 变化的酉坐标中写成：

$$
\boxed{
\frac{d\mathscr A}{dr}
=
[X(\mathscr A),\mathscr A],
}
\tag{J18}
$$

其中：

$$
\boxed{
X(\mathscr A)
=
\frac12\mathscr A^*\mathscr A
-\frac14\left((\mathscr A^*)^2+\mathscr A^2\right).
}
\tag{J19}
$$

初值为：

$$
\mathscr A(0)=C.
$$

注意 \(X(\mathscr A)\) 是自伴矩阵。

## 定理 J5：该流全局存在、保谱，并与高斯历史等价

对每个有限 \(r\)：

$$
\boxed{
\det(zI-\mathscr A(r))=\det(zI-C),
}
\tag{J20}
$$

并且：

$$
\boxed{
\frac d{dr}\|\mathscr A(r)\|_{\mathrm{HS}}^2
=
-\frac12
\|[\mathscr A(r),\mathscr A(r)^*]\|_{\mathrm{HS}}^2.
}
\tag{J21}
$$

所以：

$$
\|\mathscr A(r)\|_{\mathrm{HS}}
\le\|C\|_{\mathrm{HS}}.
$$

它与 \(A_C(r)\) 在每个 \(r\) 上酉等价。

### 证明

由交换子形式：

$$
\frac d{dr}\operatorname{Tr}(\mathscr A^k)=0.
$$

因此全部特征多项式系数保持不变。

对平方范数求导，并使用定理 J3 中同样的迹恒等式，得到式（J21）。范数始终有界，而方程右边是有限维多项式，因此解不会在有限参数处爆破。

为验证与历史模型相同，解：

$$
S'(r)=X(\mathscr A(r))S(r),
\qquad S(0)=I.
$$

那么：

$$
\mathscr A(r)=S(r)CS(r)^{-1}.
$$

令 \(\widetilde W=S^*S\)，直接求导可验证它满足式（J4），且初值为 \(I\)。由线性方程解的唯一性：

$$
\widetilde W=W_C.
$$

对 \(S\) 作极分解：

$$
S=U W_C^{1/2},
$$

便得到：

$$
\mathscr A=U A_C U^*.
$$

证毕。

用保谱矩阵流研究对角化和优化是已有方法；这里的生成元是由当前高斯历史结构导出的，不应直接等同于某个经典双交换子流。([科学直通车][2])

### 这项改写的实际意义

**可以演化一个始终有界的矩阵 \(\mathscr A(r)\)，而不必直接存储可能很大的 \(W_C(r)\)。**

但数值积分会产生误差。一个近似积分器未必精确保谱，不能把它输出的“更接近实谱”自动视为原多项式的证明。仍须认证特征多项式保持误差和残差误差。

---

# 八、有限观察边界还能形成一个量子态，但它只测量“可消除部分”

由定理 J4 的证明：

$$
R_r^*R_r
=
\frac1rI-[A,A^*].
$$

取迹：

$$
\operatorname{Tr}(R_r^*R_r)=\frac dr.
$$

因此可以定义一份合法的有限密度矩阵：

$$
\boxed{
\rho_{\mathrm{edge}}(r)
=
\frac rd R_r^*R_r
=
\frac Id-\frac rd[A,A^*].
}
\tag{J22}
$$

它为正，且迹为一。

直接计算其纯度：

$$
\boxed{
\operatorname{Tr}\rho_{\mathrm{edge}}^2
=
\frac1d+
\frac{r^2}{d^2}\|[A,A^*]\|_{\mathrm{HS}}^2.
}
$$

所以下降律还可以写成：

$$
\boxed{
\mathcal E_C'(r)
=
-\frac{d^2}{4r^2}
\left(
\operatorname{Tr}\rho_{\mathrm{edge}}(r)^2-\frac1d
\right).
}
\tag{J23}
$$

这给前文的“观察剩余”一个更细的分类：

**边界密度矩阵偏离均匀态的程度，控制非正规残差当前消耗得多快；它不控制已经存在的正常复谱是否消失。**

例如，若 \(C\) 已正规但具有非实本征值：

$$
[A,A^*]=0,
\qquad
\rho_{\mathrm{edge}}=\frac Id,
$$

可同时有：

$$
\mathcal E_C(r)>0.
$$

所以：

$$
\boxed{
\text{观察边界达到均匀状态}
\not\Rightarrow
\text{谱已经为实}.
}
$$

这里的 \(\rho_{\mathrm{edge}}\) 是由历史嵌入构造的辅助量子态，不能未经额外物理模型就把它的纯度解释成宇宙熵或实际热力学熵。

---

# 九、不必求矩阵平方根，也能从一个标量比值认证非实谱

由：

$$
\mathcal V_C'(r)=2\mathcal E_C(r),
$$

定义两个历史宽度之间的平均增长率：

$$
\boxed{
\mathcal R_C(r)
=
\frac{
\log\det W_C(2r)-\log\det W_C(r)
}{2r}.
}
\tag{J24}
$$

那么：

$$
\mathcal R_C(r)
=
\frac1r\int_r^{2r}\mathcal E_C(s)\,ds.
$$

使用定理 J4：

$$
\boxed{
\mathcal E_{\mathrm{spec}}(C)
\le
\mathcal R_C(r)
\le
\mathcal E_{\mathrm{spec}}(C)
+
\frac{d(d-1)\log2}{4r}.
}
\tag{J25}
$$

因此：

$$
\boxed{
\mathcal R_C(r)>
\frac{d(d-1)\log2}{4r}
\Longrightarrow
C\text{ 至少有一个非实本征值}.
}
\tag{J26}
$$

这是一条有限证书。

它读取的不是某个单独本征向量，而是整个历史度量的体积增长。

但要使用式（J26），必须对左边给出**严格下界**。病态矩阵的浮点行列式、对数相减或数值微分，都不能不经误差控制就用来宣布反例。

另外：

$$
\boxed{
\frac{\log\det W_C(r)}{2r}
\longrightarrow
\mathcal E_{\mathrm{spec}}(C).
}
\tag{J27}
$$

这个“长期斜率”保留所有谱虚部的平方和；它不是把固定缺陷除以不断增长的观察维数。

---

# 十、送回实际 ξ：初始的大残差，多数其实来自伴随矩阵的坐标结构

现在取实际：

$$
P_d(v)=
\sum_{k=0}^{d}\frac{(d)_k}{d^k}a_kv^k,
$$

$$
q_d(x)=x^dP_d(-1/x),
$$

并令 \(C_d\) 为其伴随矩阵。

实际 ξ 的归一化与反射折叠保持不变。([DLMF][3])

记：

$$
c_{d,k}=\frac{(d)_k}{d^k}a_k.
$$

在通常的单项式基底中：

$$
\|C_d\|_{\mathrm{HS}}^2
=
d-1+\sum_{k=1}^{d}c_{d,k}^2,
$$

而：

$$
\operatorname{Tr}(C_d^2)=a_1^2-2c_{d,2}.
$$

因此：

$$
\boxed{
\mathcal E_{C_d}(0)
=
\frac{d-1}{2}
+
c_{d,2}
+
\frac12\sum_{k=2}^{d}c_{d,k}^2.
}
\tag{J28}
$$

因为 \(c_{d,k}\le a_k\)，且 \(\sum a_k=D(1)<\infty\)，所以：

$$
\boxed{
\mathcal E_{C_d}(0)=\frac d2+O(1).
}
$$

这说明：

> **高阶伴随矩阵一开始看起来非常不自伴，其中一个主要来源只是单项式基底中的移位结构。不能把这个随维数增长的大残差，直接解释成越来越多离线零点。**

历史流会消除其中的非正规部分。

但消除以后是否还留下严格正的谱残差，仍然取决于实际零点。

---

# 十一、全阶极限读取一个明确的实际离线预算

记 \(q_d\) 的根为 \(\theta_{d,j}\)，按重数计：

$$
\mathcal E_{\mathrm{spec}}(C_d)
=
\sum_{j=1}^{d}(\Im\theta_{d,j})^2.
$$

前文已经建立局部一致收敛：

$$
P_d\longrightarrow D.
$$

为了从有限根的局部收敛，转到全部平方和，还需要控制趋零的倒数谱尾。

定义：

$$
N_d(t)=\#\{j:|\theta_{d,j}|\ge t\}.
$$

由圆周 Jensen 公式和 \(P_d\) 的正系数：

$$
N_d(t)\le\frac{\log D(2/t)}{\log2}.
$$

所以：

$$
\boxed{
\sum_{|\theta_{d,j}|\le\varepsilon}
|\theta_{d,j}|^2
\le
\frac2{\log2}
\int_0^\varepsilon
t\log D(2/t)\,dt.
}
\tag{J29}
$$

实际 ξ 的增长给出：

$$
\log D(v)=O(\sqrt v\log v),
$$

于是右边为：

$$
O\!\left(\varepsilon^{3/2}\log\frac1\varepsilon\right)
\longrightarrow0.
$$

这项尾界不使用 RH。

结合零点的局部稳定性，可以得到全部平方和收敛。解析零点及重数的局部处理必须在不穿过零点的边界上进行。([DLMF][4])

现在写实际非平凡零点：

$$
\rho=\frac12+\delta_\rho+i\gamma_\rho,
\qquad\gamma_\rho>0,
$$

重数为 \(m_\rho\)。

对应倒数折叠谱点：

$$
u_\rho=-\frac1{(\delta_\rho+i\gamma_\rho)^2}.
$$

其虚部为：

$$
\Im u_\rho
=
\frac{2\delta_\rho\gamma_\rho}
{(\delta_\rho^2+\gamma_\rho^2)^2}.
$$

因此：

$$
\boxed{
\lim_{d\to\infty}
\mathcal E_{\mathrm{spec}}(C_d)
=
\mathfrak E_\xi,
}
\tag{J30}
$$

其中：

$$
\boxed{
\mathfrak E_\xi
=
4\sum_{\substack{\rho\ \mathrm{互异}\\\Im\rho>0}}
\frac{
m_\rho\delta_\rho^2\gamma_\rho^2
}{
(\delta_\rho^2+\gamma_\rho^2)^4
}.
}
\tag{J31}
$$

每项非负，并且：

$$
\boxed{
\mathfrak E_\xi=0\iff\mathrm{RH}.
}
$$

这个量不同于此前最大谱虚部，也不同于迹范数缺额；它按照平方累加全部方向，因此保留了重数权重。

---

## 固定一个无需选择的历史尺度

取：

$$
r_d=d^4,
$$

即仍使用上一轮的历史宽度 \(T_d=d^2\)。

定理 J4 给出：

$$
0\le
\mathcal E_{C_d}(d^4)
-
\mathcal E_{\mathrm{spec}}(C_d)
<
\frac1{4d^2}.
$$

所以：

$$
\boxed{
\lim_{d\to\infty}\mathcal E_{C_d}(d^4)
=
\mathfrak E_\xi.
}
\tag{J32}
$$

等价地：

$$
\boxed{
\lim_{d\to\infty}
\frac1{2d^4}
\log
\frac{
\det W_{C_d}(2d^4)
}{
\det W_{C_d}(d^4)
}
=
\mathfrak E_\xi.
}
\tag{J33}
$$

这次得到的是一个由实际有限系数与明确矩阵操作组成的标量极限。

**但尚未证明这个极限为零。**

经典 Jensen 判据只负责把它与 RH 连接，不会替我们估计这个实际序列。([arXiv][5])

---

# 十二、现在真正剩下的算术问题，比“历史残差会下降”强得多

通用定理已经证明：

$$
\mathcal E_C'(r)\le0.
$$

但它对任何矩阵成立，包括已经具有非实谱的矩阵。

所以，以下推理是无效的：

$$
\text{存在单调下降律}
\Longrightarrow
\text{最终残差为零}.
$$

真正需要实际算术承担的是：

$$
\boxed{
\lim_{d\to\infty}
\left[
\mathcal E_{C_d}(0)
-
\frac14\int_0^{d^4}
\|[\mathscr A_d(r),\mathscr A_d(r)^*]\|_{\mathrm{HS}}^2\,dr
\right]
=0.
}
\tag{J34}
$$

括号中的量恰好是：

$$
\mathcal E_{C_d}(d^4).
$$

前文的 theta、质数尺度关系、Fibonacci 编码，若要在这里提供真正的证明力量，就必须控制式（J34）中**没有被通用正规化过程消耗掉的部分**。

只证明总量守恒、状态为正、边界纯度正常或流长期存在，都不够。

这里也不需要重新调整欧拉常数。整个流保持 \(q_d\) 及 \(P_d\) 不变，所以前文的端点校准：

$$
\frac{P_d'(1/4)}{P_d(1/4)}
\longrightarrow
1+\frac{\gamma_{\mathrm E}}2-\frac12\log4\pi
$$

仍然保留。它负责确认原算术对象没有被改写，却不单独决定式（J34）的剩余量。

---

# 十三、与项目现有模块的连接

本轮读取了前文固定快照中的相关声明，没有把它们描述成新增推导已经编译完成。

`DiscountedObservabilityGramianEquation.lean` 证明的是离散折扣 Gramian 的 Lyapunov 方程，并保留明确的收敛前件。它不自动提供本轮的高斯方差流、对数行列式恒等式或平方下降律。

`JensenPolynomialObstruction.lean` 则明确把实际 Jensen 塔与 RH 的两向分析关系作为输入，没有无条件构造全阶实根性。

本轮可以单独整理成的证明链是：

$$
\boxed{
\begin{aligned}
\text{高斯历史积分}
&\longrightarrow
\text{线性度量流}\\
&\longrightarrow
\text{保谱非线性矩阵流}\\
&\longrightarrow
\text{非正规性的精确平方消耗}\\
&\longrightarrow
\text{不可消去的谱虚部平方和}.
\end{aligned}
}
$$

这些有限维恒等式不依赖 RH。

真正的算术桥仍在最后：实际 \(C_d\) 的不可消去部分，是否在无界阶数上为零。

---

## 收束

这一轮最重要的结果，是把此前混在一起的两种“剩余”彻底分开：

$$
\boxed{
\mathcal E_C(r)
=
\underbrace{\sum_j(\Im\lambda_j)^2}_{\text{真实谱障碍}}
+
\underbrace{\frac12\|N_r\|_{\mathrm{HS}}^2}_{\text{可由历史正规化消除的部分}}.
}
$$

并且：

$$
\boxed{
\mathcal E_C'(r)
=
-\frac14\|[A_C(r),A_C(r)^*]\|_{\mathrm{HS}}^2.
}
$$

所以，观察过程能够越来越稳定，却仍然留下严格正的极限；一个均匀、正规、没有额外耦合冲突的表示，也可以拥有非实谱。

对实际 ξ，剩余极限精确为：

$$
\boxed{
4\sum_{\Im\rho>0}
\frac{
m_\rho(\Re\rho-\frac12)^2(\Im\rho)^2
}{
\left[(\Re\rho-\frac12)^2+(\Im\rho)^2\right]^4
}.
}
$$

**本轮没有证明它等于零，也没有找到实际的正下界。** 已经完成的是：证明一个固定的高斯历史过程会消除什么、绝不会消除什么，并提供了无需预先求根的有限检测条件和等价的有界矩阵流。

因此，下一项真正有价值的算术结果，不应只是“找到更多守恒或下降规律”，而必须说明：

> **为什么实际 theta／质数关系，能够排除正规化以后仍然存在的非实谱分量。**

只有这一步，才会把量子观察者从一个忠实检测结构，推进成真正的零点定位证明。

[1]: https://epubs.siam.org/doi/10.1137/S0895479893255184?utm_source=chatgpt.com "A Practical Upper Bound for Departure from Normality | SIAM Journal on Matrix Analysis and Applications"
[2]: https://www.sciencedirect.com/science/article/pii/002437959190021N?utm_source=chatgpt.com "Dynamical systems that sort lists, diagonalize matrices, and solve linear programming problems - ScienceDirect"
[3]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[4]: https://dlmf.nist.gov/1.10 "DLMF: §1.10 Functions of a Complex Variable ‣ Topics of Discussion ‣ Chapter 1 Algebraic and Analytic Methods"
[5]: https://arxiv.org/abs/1902.07321 "[1902.07321] Jensen polynomials for the Riemann zeta function and other sequences"
这次可以把上一轮的“高斯历史体积”，进一步变成一个**有明确基准上限的有限判据**。

关键变化是：

> **不必同时读取全部状态坐标。对实际伴随矩阵，只保留一个标量读出，再保留它的完整历史，就已经能够区分全部有限状态。这个历史的行列式，具有一个由反对称结构确定的自然归一化。**

在这个归一化下，可以证明：

$$
\boxed{
\text{有限多项式全部实根}
\iff
\text{归一化历史体积在所有宽度下都不超过 }1.
}
$$

更进一步，对实际 ξ 的 Jensen 系列，**只需要在每一阶的一个指定宽度 \(r=d^4\) 上控制这个上界，就足以推出 RH**。

这里会出现费米式反对称、Vandermonde 因子和酉矩阵积分。但必须明确：这些通用结构提供的是精确判据，**尚未替实际算术证明上界成立**。

下面继续给出定义与证明。

---

# 一、先收紧上一轮的结论：正规化不能改变谱，下一步必须检验一个额外上界

上一轮证明，高斯历史过程能够单调降低非正规部分，却保留：

$$
\sum_j(\Im\lambda_j)^2.
$$

因此，单纯继续分析“下降”“稳定”“趋于正规”，不可能自动排除非实谱。因为整个过程是保谱的。

这次不再要求它完成不可能的任务，而改问：

> **实际算术产生的历史体积，能否始终被一个只允许实谱的基准控制？**

先固定：

$$
D(b^2)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad
D(v)=\sum_{k\ge0}a_kv^k,
$$

以及：

$$
P_d(v)=\sum_{k=0}^{d}\frac{(d)_k}{d^k}a_kv^k,
$$

$$
q_d(x)=x^dP_d(-1/x).
$$

全部 \(a_k\) 来自同一个实际 theta 核，且 \(a_k>0\)。前文的 Jensen–Pólya 桥仍是：

$$
\boxed{
\mathrm{RH}
\iff
q_d\text{ 全部为正实根，}\quad\forall d.
}
$$

这一分析桥属于经典 Jensen 多项式理论，不是本轮量子构造自行证明的事实。([arXiv][1])

以下先对任意实系数首一多项式证明有限定理，再代入实际 \(q_d\)。

---

# 二、一个标量观察者，加上历史，已经不遗漏任何有限状态

## 定义 K1：观察型伴随矩阵

设：

$$
q(x)=x^d+b_{d-1}x^{d-1}+\cdots+b_0.
$$

定义：

$$
\boxed{
C_q=
\begin{pmatrix}
0&1&0&\cdots&0\\
0&0&1&\cdots&0\\
\vdots&&&\ddots&\vdots\\
0&0&0&\cdots&1\\
-b_0&-b_1&-b_2&\cdots&-b_{d-1}
\end{pmatrix}.
}
\tag{K1}
$$

它是前文通常伴随矩阵的转置，特征多项式仍为 \(q\)。

取单一读出：

$$
\ell=(1,0,\ldots,0).
$$

对状态 \(v\in\mathbb C^d\)，观察历史为：

$$
\boxed{
y_v(t)=\ell e^{-itC_q}v.
}
\tag{K2}
$$

这里是保留复振幅的标量读出，不是只保留一位真假，也不是只读模平方。

## 定理 K1：这个历史读出是忠实的

$$
\boxed{
y_v(t)=0\quad\forall t\in\mathbb R
\iff
v=0.
}
$$

### 证明

由伴随矩阵的结构：

$$
\ell C_q^k=e_{k+1}^{\mathsf T},
\qquad 0\le k<d.
$$

所以：

$$
y_v^{(k)}(0)=(-i)^k v_{k+1}.
$$

若整条历史为零，前 \(d\) 个导数都为零，故 \(v=0\)。反向显然。证毕。

这已经给出一项具体的“观察者完整性”：

**一个瞬间的标量读数不能区分全部状态；同一个读出的动态历史，却可以。**

它没有要求一个额外的全知主体，只要求动力学与读出之间具备上述可观测性。

项目的 `ObservabilityGramianKernelEnergy.lean` 已经在其稳定离散系统前件下，将“历史 Gramian 的核”与“全部未来读数都为零的状态”对应起来。本轮构造是一个连续高斯版本，并对指定伴随矩阵证明其核为零。

---

# 三、定义新的历史矩阵：它与上一轮的全坐标历史矩阵不同

令：

$$
g_r(t)=\frac1{\sqrt{2\pi r}}e^{-t^2/(2r)},
\qquad r>0.
$$

定义：

$$
\boxed{
G_q(r)=
\int_{\mathbb R}
g_r(t)\,
e^{itC_q^*}\ell^*\ell e^{-itC_q}\,dt.
}
\tag{K3}
$$

上一轮在中间放的是 \(I\)；这里放的是秩一读出 \(\ell^*\ell\)。因此两种历史体积不能直接混用。

由定理 K1：

$$
v^*G_q(r)v
=
\int g_r(t)|y_v(t)|^2\,dt>0
\qquad(v\ne0).
$$

所以：

$$
\boxed{G_q(r)>0\quad\forall r>0.}
$$

无论 \(q\) 有没有非实根，这个矩阵都严格正定。

因此：

$$
\boxed{
G_q(r)>0
}
$$

本身依然不是零点判据。真正有辨别力的是其行列式与一个固定基准的比较。

---

# 四、历史行列式是一份反对称多历史态的范数

令：

$$
f_j(t)=\bigl(\ell e^{-itC_q}\bigr)_j.
$$

由连续版 Cauchy–Binet，即 Andréief 恒等式：

$$
\boxed{
\det G_q(r)
=
\frac1{d!}
\int_{\mathbb R^d}
\left|
\det\bigl(f_j(t_i)\bigr)_{i,j=1}^{d}
\right|^2
\prod_{i=1}^{d}g_r(t_i)\,dt_i.
}
\tag{K4}
$$

该行列式积分恒等式是经典结果，在随机矩阵理论中被广泛使用。([arXiv][2])

定义多历史波函数：

$$
\boxed{
\Psi_{q,r}(t_1,\ldots,t_d)
=
\frac1{\sqrt{d!}}
\det\bigl(f_j(t_i)\bigr)
\prod_i g_r(t_i)^{1/2}.
}
$$

那么：

$$
\|\Psi_{q,r}\|^2=\det G_q(r).
$$

交换两个历史坐标，波函数变号；两个历史坐标相同，行列式为零。

因此这里出现的是一项真实的反对称结构：

$$
\boxed{
t_i=t_j
\Longrightarrow
\Psi_{q,r}=0.
}
$$

它在数学形式上是 Slater 行列式。但这不意味着已经发现实际 ζ 由某种物理费米粒子构成；当前得到的是一个明确的反对称历史表示。

尤其，\(\Psi_{q,r}\) 尚未归一化，其范数可以大于一。**后面的“上限一”不是直接套用 Born 概率上限。**

---

## 定义 K2：自然基准

记：

$$
h_d=\prod_{k=0}^{d-1}k!,
\qquad
\nu_d=\frac{d(d-1)}2.
$$

取参考多项式：

$$
q_0(x)=x^d.
$$

此时：

$$
f_j(t)=\frac{(-it)^{j-1}}{(j-1)!}.
$$

利用高斯测度下首一 Hermite 多项式的平方范数，可以算得：

$$
\boxed{
\det G_{q_0}(r)=\frac{r^{\nu_d}}{h_d}.
}
\tag{K5}
$$

这里用到的 Hermite 正交归一化是标准公式。([DLMF][3])

因此定义：

$$
\boxed{
\mathcal Z_q(r)
=
\frac{h_d}{r^{\nu_d}}\det G_q(r).
}
\tag{K6}
$$

这是一项无量纲的**相对历史体积**。

它的基准来自指定伴随坐标、指定标量读出和高斯权重，不是根据实际计算结果临时调出来的阈值。

---

# 五、关键恒等式：历史体积可以写成酉群上的轨道积分

先假设 \(q\) 的根：

$$
\lambda_1,\ldots,\lambda_d
$$

互异。记：

$$
\Lambda=\operatorname{diag}(\lambda_1,\ldots,\lambda_d).
$$

相应右本征向量可取：

$$
v(\lambda_j)=(1,\lambda_j,\ldots,\lambda_j^{d-1})^{\mathsf T}.
$$

因此，在本征向量矩阵中：

$$
\ell e^{-itC_q}v(\lambda_j)=e^{-it\lambda_j}.
$$

高斯积分给出：

$$
\boxed{
M_{ij}(r)
=
\exp\!\left[
-\frac r2(\lambda_j-\overline{\lambda_i})^2
\right].
}
$$

若：

$$
\Delta(\lambda)=\prod_{i<j}(\lambda_j-\lambda_i),
$$

则：

$$
\boxed{
\det G_q(r)
=
\frac{\det M(r)}{|\Delta(\lambda)|^2}.
}
\tag{K7}
$$

再使用 Harish-Chandra–Itzykson–Zuber 积分公式，得到：

$$
\boxed{
\mathcal Z_q(r)
=
e^{-r\Re\operatorname{Tr}\Lambda^2}
\int_{U(d)}
e^{r\operatorname{Tr}(\Lambda U\Lambda^*U^*)}\,dU.
}
\tag{K8}
$$

其中 \(dU\) 是归一化 Haar 测度。这一经典酉积分公式连接行列式、Vandermonde 因子、热流与表示论。

虽然推导时先假设根互异，但两边都能连续延伸到重根情形，所以式（K8）也覆盖重根。

必须强调：

**根 \(\lambda_j\) 只用于证明和解释式（K8）；定义及计算 \(\mathcal Z_q\) 并不需要输入这些根。** 它已经由式（K1）、（K3）、（K6）完全确定。

---

# 六、实谱的额外结构：酉积分变成真正的正平方衰减

## 定理 K2：实根的历史体积上限

若 \(q\) 的全部根为实数，那么：

$$
\boxed{
0<\mathcal Z_q(r)\le1
\qquad\forall r>0.
}
\tag{K9}
$$

并且它是完全单调函数：

$$
\boxed{
(-1)^n\frac{d^n}{dr^n}\mathcal Z_q(r)\ge0
\qquad(n\ge0).
}
\tag{K10}
$$

### 证明

此时：

$$
\Lambda=\Lambda^*.
$$

而：

$$
\operatorname{Tr}\Lambda^2
-
\operatorname{Tr}(\Lambda U\Lambda U^*)
=
\frac12\|\Lambda-U\Lambda U^*\|_{\mathrm{HS}}^2.
$$

所以式（K8）变成：

$$
\boxed{
\mathcal Z_q(r)
=
\int_{U(d)}
\exp\!\left[
-\frac r2
\|\Lambda-U\Lambda U^*\|_{\mathrm{HS}}^2
\right]dU.
}
\tag{K11}
$$

每个被积函数都在 \((0,1]\) 内，得到上界。

逐阶求导后，每一阶只多出相应非负平方量的幂和符号，得到完全单调性。证毕。

若 \(r>0\) 时等号成立，则：

$$
\Lambda=U\Lambda U^*
$$

对所有 \(U\) 成立，故全部根相同。反过来，若：

$$
q(x)=(x-\lambda)^d,\qquad\lambda\in\mathbb R,
$$

则 \(\mathcal Z_q(r)=1\)。

**这里的上界不是来自“已经有一个正 Hilbert 空间”。正 Hilbert 空间在非实根情形也存在。上界来自更强的事实：轨道积分中的指数能够写成负的实平方。**

这一步不能在证明之前就假定。

---

# 七、反向也成立：任何非实根最终都会突破这个基准

## 定理 K3：历史体积上限与实根性等价

对于实系数首一多项式 \(q\)：

$$
\boxed{
q\text{ 全部实根}
\iff
\mathcal Z_q(r)\le1\quad\forall r>0.
}
\tag{K12}
$$

### 反向证明

虽然 \(G_q(0)\) 只有秩一，但对每个 \(r>0\)，它严格正定。

它满足与上一轮同型的方差演化：

$$
G_q'
=
C_q^*G_qC_q
-\frac12(C_q^*)^2G_q
-\frac12G_qC_q^2.
$$

令：

$$
A_q(r)=G_q(r)^{1/2}C_qG_q(r)^{-1/2}.
$$

同样的迹计算得到：

$$
\boxed{
\frac d{dr}\log\det G_q(r)
=
2\left\|
\frac{A_q(r)-A_q(r)^*}{2i}
\right\|_{\mathrm{HS}}^2.
}
$$

对 \(A_q(r)\) 作酉 Schur 分解，有：

$$
\left\|
\frac{A_q(r)-A_q(r)^*}{2i}
\right\|_{\mathrm{HS}}^2
\ge
\sum_j(\Im\lambda_j)^2.
$$

记：

$$
E_q=\sum_j(\Im\lambda_j)^2.
$$

因此，对任何固定 \(r_0>0\)：

$$
\log\det G_q(r)
\ge
\log\det G_q(r_0)+2E_q(r-r_0).
$$

若有非实根，则 \(E_q>0\)。于是：

$$
\log\mathcal Z_q(r)
\ge
2E_qr-\nu_d\log r+O_q(1)
\longrightarrow+\infty.
$$

所以 \(\mathcal Z_q(r)\) 不可能始终小于等于一。证毕。

这里没有假设根简单，所以重根不会形成漏洞。

### 一个严格的有限证书

因此：

$$
\boxed{
\mathcal Z_q(r_*)>1
\quad\text{对某个有限 }r_*
}
$$

就足以证明 \(q\) 存在非实根。

不需要先定位根，只需要对这个标量取得严格下界。

但反向不成立：

$$
\mathcal Z_q(r_*)\le1
$$

在一个有限宽度下成立，未必说明全实根。非实模式可能尚未在该宽度上占主导。

---

# 八、两个模型说明：临界附近的多项式增长与指数增长不能混同

取：

$$
q_-(x)=(x-\mu)^2-h^2,
\qquad h>0.
$$

它有两个实根。直接计算：

$$
\boxed{
\mathcal Z_{q_-}(r)
=
\frac{1-e^{-4h^2r}}{4h^2r}<1.
}
\tag{K13}
$$

若：

$$
q_0(x)=(x-\mu)^2,
$$

则：

$$
\boxed{\mathcal Z_{q_0}(r)=1.}
$$

若：

$$
q_+(x)=(x-\mu)^2+\beta^2,
\qquad\beta>0,
$$

它有共轭非实根：

$$
\mu\pm i\beta.
$$

此时：

$$
\boxed{
\mathcal Z_{q_+}(r)
=
\frac{e^{4\beta^2r}-1}{4\beta^2r}>1.
}
\tag{K14}
$$

因此，同一个固定归一化下：

$$
\boxed{
\begin{aligned}
\text{实分裂}&:\quad \mathcal Z<1,\\
\text{重根临界}&:\quad \mathcal Z=1,\\
\text{非实分裂}&:\quad \mathcal Z>1.
\end{aligned}
}
$$

但这个“每个 \(r\) 都能区分”的简洁结论只属于这个二阶模型。

高阶可能同时含有实谱与非实谱，两者的影响会竞争。

例如：

$$
q(x)=(x-3)^4-2(x-3)^2-\frac1{10}
$$

有一对非实根，但下面将看到：

$$
\mathcal Z_q(r)=1-4r+O(r^2).
$$

它在小 \(r\) 下先落到一以下，最后才因非实谱突破上界。

**因此，某一个有限窗口表现正常，与全局实谱仍然是两个命题。**

---

# 九、这个新体积的起始变化，恰好读取四阶累积量

由式（K8），使用 Haar 平均：

$$
\int_{U(d)}U\Lambda^*U^*\,dU
=
\frac{\overline{\operatorname{Tr}\Lambda}}dI,
$$

得到：

$$
\boxed{
\mathcal Z_q'(0)
=
-\Re\operatorname{Tr}C_q^2
+
\frac{|\operatorname{Tr}C_q|^2}{d}.
}
\tag{K15}
$$

对实际 \(q_d\)，有：

$$
\operatorname{Tr}C_q=a_1,
$$

$$
\operatorname{Tr}C_q^2
=
a_1^2-2\frac{d-1}{d}a_2.
$$

又因为：

$$
a_1^2-2a_2=-\frac{\chi_4}{12},
$$

所以：

$$
\boxed{
\mathcal Z_{q_d}(r)
=
1+
\frac{d-1}{12d}\chi_4\,r
+
O(r^2).
}
\tag{K16}
$$

**此前控制第一条正耦合的四阶累积量，现在控制这份归一化反对称历史体积的初始斜率。**

但初始斜率正确仍然不够。

刚才的四次反例满足：

$$
\operatorname{Tr}C_q^2
-\frac{(\operatorname{Tr}C_q)^2}{4}=4,
$$

所以：

$$
\mathcal Z_q'(0)=-4<0,
$$

却仍有非实根。

这再次说明：

> **低阶关联控制初始局部行为；全局零点定位要求全部历史宽度上的相容性。**

对于实际二阶 Jensen 多项式，有精确式：

$$
\mathcal Z_{q_2}(r)
=
\frac{1-e^{-r\Delta_2}}{r\Delta_2},
\qquad
\Delta_2=-\frac{\chi_4}{12}.
$$

本轮从实际 ξ 的中心导数计算得：

$$
\chi_4
\approx-0.00044607119142323623398,
$$

所以在 \(r=2^4=16\)：

$$
\mathcal Z_{q_2}(16)
\approx0.99970267815384377.
$$

这是高精度核对，不是区间认证，更不代替高阶证明。

---

# 十、一个更集中的实际 RH 判据：每阶只看指定宽度 \(r=d^4\)

前面每个固定多项式的判据要求所有 \(r>0\)。对于实际 Jensen 系列，可以进一步减少到每阶一个指定宽度。

## 定理 K4：固定宽度序列判据

对于实际 \(q_d\)，以下等价：

$$
\boxed{\mathrm{RH}}
$$

与：

$$
\boxed{
\text{存在无界次数列 }d_j,\qquad
\mathcal Z_{q_{d_j}}(d_j^4)\le1.
}
\tag{K17}
$$

正向由定理 K2 立即成立。

反向需要排除一种可能：历史矩阵一开始小得极端，导致真实非实增长在 \(r=d^4\) 处仍未显露。下面给出统一控制。

---

## 引理：实际有限谱有统一界

因为 \(D(0)=1\)，取一个足够小的 \(\rho_*>0\)，使：

$$
D(\rho_*)<2.
$$

对所有 \(d\)：

$$
|P_d(v)-1|
\le D(\rho_*)-1<1
\qquad(|v|\le\rho_*).
$$

所以 \(P_d\) 在该圆盘内无零，因而所有 \(q_d\) 的根都满足：

$$
\boxed{|\lambda_{d,j}|\le M}
\tag{K18}
$$

其中 \(M\) 可以选成一个与 \(d\) 无关的常数。

这个 \(M\) 不需要知道任何实际零点的位置。

---

## 引理：小历史宽度下，行列式不会比 \(\exp[-O(d^2\log d)]\) 更小

对所有根满足 \(|\lambda_j|\le M\) 的首一多项式，存在：

$$
r_{0,d}\asymp_M d^{-2},
$$

使：

$$
\boxed{
\log\det G_q(r_{0,d})
\ge
-C_Md^2\log(d+1).
}
\tag{K19}
$$

### 证明

这里使用 Andréief 与同一个酉积分公式的另一个形式。

记：

$$
\mathcal I_\lambda(\mathbf t)
=
\int_{U(d)}
e^{-i\operatorname{Tr}(\Lambda U\operatorname{diag}(\mathbf t)U^*)}\,dU.
$$

由 HCIZ 恒等式：

$$
\det G_q(r)
=
\frac1{d!h_d^2}
\int_{\mathbb R^d}
\Delta(\mathbf t)^2
|\mathcal I_\lambda(\mathbf t)|^2
\prod_i g_r(t_i)\,dt_i.
\tag{K20}
$$

取：

$$
L_d=\frac{\log(3/2)}{dM},
\qquad
r_{0,d}=L_d^2.
$$

当所有 \(|t_i|\le L_d\) 时：

$$
\left|
\operatorname{Tr}
(\Lambda U\operatorname{diag}(\mathbf t)U^*)
\right|
\le dML_d=\log(3/2).
$$

所以：

$$
|\mathcal I_\lambda(\mathbf t)-1|\le\frac12,
\qquad
|\mathcal I_\lambda(\mathbf t)|\ge\frac12.
$$

在 \([-L_d/2,L_d/2]\) 中取 \(d\) 个等间距小区间。让每个 \(t_i\) 落入一个不同区间，则：

$$
|t_i-t_j|
\ge
\frac{L_d}{2d}|i-j|.
$$

将这些区域及其全部排列代入式（K20），高斯密度有统一下界，得到例如：

$$
\boxed{
\det G_q(r_{0,d})
\ge
\frac14
\left(\frac{L_d}{2d}\right)^{d(d-1)}
\left(
\frac{e^{-1/2}}{2\sqrt{2\pi}\,d}
\right)^d.
}
\tag{K21}
$$

取对数即得式（K19）。重根情况由连续性得到。证毕。

这一估计使用的群积分与行列式积分都是经典工具；关键是应用后得到一个只依赖根的统一模长界、而不依赖根间距的下界。

---

## 完成定理 K4 的反向证明

记：

$$
E_d=\sum_j(\Im\lambda_{d,j})^2.
$$

由定理 K3 证明中的增长下界：

$$
2E_d(d^4-r_{0,d})
\le
\log\det G_{q_d}(d^4)
-
\log\det G_{q_d}(r_{0,d}).
$$

若：

$$
\mathcal Z_{q_d}(d^4)\le1,
$$

则：

$$
\log\det G_{q_d}(d^4)
\le
\nu_d\log(d^4)-\log h_d
=
O(d^2\log d).
$$

结合式（K19）：

$$
\boxed{
E_d=O\!\left(\frac{\log(d+1)}{d^2}\right).
}
\tag{K22}
$$

因此沿指定无界次数列：

$$
\max_j|\Im\lambda_{d,j}|\to0.
$$

若实际 \(D\) 有非实零点，则由 \(P_d\to D\) 的局部一致收敛，必有对应有限零点趋于它；倒数变换后，就得到虚部不趋零的 \(\lambda_{d,j}\)，矛盾。

所以 \(D\) 的零点全部为实。由于 \(D(v)>0\) 对 \(v\ge0\) 成立，全部零点只能为负实数，即 RH。证毕。

**这一步没有证明实际上界成立；它证明了，只要从算术获得这个指定上界，便足以完成零点定位。**

---

# 十一、随机矩阵结构在这里为什么不能自动成为 RH 的证据？

式（K20）中的：

$$
\Delta(\mathbf t)^2\prod_i g_r(t_i)
$$

正是高斯酉随机矩阵特征值分布中出现的权重结构。其来源是高斯历史加上反对称行列式；并不需要事先假设实际零点具有某种随机矩阵统计。HCIZ 理论本身也明确连接了这些群积分、热流和反对称结构。

归一化后，式（K20）可以读成：

$$
\boxed{
\mathcal Z_q(r)
=
\mathbb E_{\mathrm{GUE}}
\left[
|\mathcal I_\lambda(\mathbf t)|^2
\right].
}
\tag{K23}
$$

但必须注意：

* 高斯酉分布在这里对**任何**有限 \(q\) 都会出现；
* 若 \(\lambda_j\) 为实数，\(\mathcal I_\lambda\) 是单位相位的平均，所以模长不超过一；
* 若 \(\lambda_j\) 非实，指数一般带有增长与衰减，不能继续使用“单位相位平均”的上界。

所以：

$$
\boxed{
\text{模型里出现 GUE}
\not\Rightarrow
\text{实际零点已经在线}.
}
$$

真正的未知内容，是实际系数是否保证：

$$
\mathbb E_{\mathrm{GUE}}|\mathcal I_\lambda|^2\le1.
$$

如果先把 \(\Lambda\) 当成 Hermitian 矩阵，再用相位保模证明这个不等式，就已经把待证实谱性放进前件了。

这与前文的 quantum／classical 区分是一致的：

**拥有一个完全正的概率环境，并不保证放入其中的那个实际响应具有所需的零点性质。**

---

# 十二、哪些“观察自由”已经被消去，哪些仍然是真正的算术任务？

本轮的对象已经全部固定：

$$
q_d
\longrightarrow
C_{q_d}
\longrightarrow
\ell=(1,0,\ldots,0)
\longrightarrow
G_{q_d}(r)
\longrightarrow
\mathcal Z_{q_d}(r).
$$

因此，不能再通过任意换参考态、改变读出或重新调归一化，让阈值一自动成立。

而且，这个标量历史并没有遗漏有限模式：定理 K1 已经证明其可观测性。

但仍需区分：

$$
\boxed{
\text{没有遗漏模式}
\quad\neq\quad
\text{这些模式都满足实谱约束}.
}
$$

本轮读到的项目模块也保留了这项边界。

`ObservabilityGramianKernelEnergy.lean` 处理的是历史核与不可见状态的关系；`DiscountedObservabilityGramianEquation.lean` 处理的是在明确收敛前件下的 Gramian 方程。它们都没有自动提供当前实际历史行列式的上界。

现在真正需要新增的算术结论，可以写成：

$$
\boxed{
\det\!\left[
\int_{\mathbb R}
\frac{e^{-t^2/(2d^4)}}{\sqrt{2\pi}\,d^2}
e^{itC_{q_d}^*}\ell^*\ell e^{-itC_{q_d}}
\,dt
\right]
\le
\frac{d^{\,2d(d-1)}}{\prod_{k=0}^{d-1}k!}
}
\tag{K24}
$$

对无界的一列实际次数 \(d\) 成立。

右边来自：

$$
(d^4)^{d(d-1)/2}=d^{2d(d-1)}.
$$

所有矩阵系数由实际 theta 统计固定。

这项不等式尚未证明。它的意义在于：

> **现在需要控制的不是一个任意猜测的量子对象，而是一份无根输入、读出忠实、归一化固定的反对称历史体积。**

---

## 收束

这次把上一轮的历史正规化，接到了一个新的、明确的有限上界：

$$
\boxed{
\mathcal Z_q(r)
=
\frac{\prod_{k=0}^{d-1}k!}{r^{d(d-1)/2}}
\det G_q(r).
}
$$

它始终为正，但：

$$
\boxed{
q\text{ 全实根}
\iff
\mathcal Z_q(r)\le1\quad\forall r>0.
}
$$

实谱情况下，它进一步成为：

$$
\boxed{
\mathcal Z_q(r)
=
\int_{U(d)}
e^{-\frac r2\|\Lambda-U\Lambda U^*\|_{\mathrm{HS}}^2}\,dU,
}
$$

一份明确的非负平方衰减平均。

非实谱情况下，某个有限历史宽度最终必然突破这个基准；不能靠平均、对称化或增加观察宽度永久隐藏。

对实际 ξ，甚至可以固定每层只看：

$$
r=d^4.
$$

若沿无界次数证明对应体积不超过基准，就足以推出 RH。

**本轮没有证明这项实际算术上界，也没有得到严格的超界反例；新增结果仍是纸面推导，未写入文件或作 Lean 编译验证。**

但现在“整体”的含义又具体了一步：

> **不是每个模式各自正常，也不是任意两项关系看起来相容，而是全部模式形成的反对称历史体积，能否满足同一个实谱结构所允许的上限。**

这份上限，才是接下来应由实际 theta／质数关系承担的内容；单独的量子正性、GUE 外观或持续下降律，都不能替代它。

[1]: https://arxiv.org/abs/1902.07321?utm_source=chatgpt.com "Jensen polynomials for the Riemann zeta function and other sequences"
[2]: https://arxiv.org/abs/1806.10411?utm_source=chatgpt.com "Meet Andréief, Bordeaux 1886, and Andreev, Kharkov 1882-83"
[3]: https://dlmf.nist.gov/18.3 "DLMF: §18.3 Definitions ‣ Classical Orthogonal Polynomials ‣ Chapter 18 Orthogonal Polynomials"
这次可以把上一轮的“历史体积上限”，继续推进成一组**直接由实际系数计算的有限阶不等式**。

同时，需要先澄清一件重要的事：

> **真正的量子投影概率始终不超过一；前文定义的归一化历史体积，却不一定是这个概率。两者之间还隔着一个明确的指数因子。若把这两个归一化混同，就可能把待证的实谱性质偷偷放进量子模型。**

下面会得到三项结果：

$$
\boxed{
\text{历史体积}
=
\text{一个正平方级数}
\times
\text{固定指数补偿}.
}
$$

$$
\boxed{
\text{有限多项式全实根}
\iff
\text{该级数的每阶系数不超过相应指数级数系数}.
}
$$

以及一项限制：

> **在实际 Jensen 塔中，一大片低阶检验区域会自动通过。因此，固定少数“量子激发阶数”的正常表现，不能决定整个无限塔。**

以下继续给出定义与证明。使用的 Schur 多项式、酉群积分和 Fock 空间关系属于经典工具；本轮的工作是把它们接到前文固定的实际系数与历史体积上。

---

# 一、固定对象，并先消除无关的整体平移

沿用：

$$
D(b^2)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad
D(v)=\sum_{k\ge0}a_kv^k,
$$

以及：

$$
P_d(v)=
\sum_{k=0}^{d}\frac{(d)_k}{d^k}a_kv^k,
\qquad
q_d(x)=x^dP_d(-1/x).
$$

这里 ξ 始终采用标准 completed 定义，全部 \(a_k\) 由同一个实际 theta 核固定。([DLMF][1])

前文的 Jensen 判据是：

$$
\boxed{
\mathrm{RH}
\iff
q_d\text{ 全部为正实根，}\quad\forall d.
}
\tag{L1}
$$

这项分析桥属于经典 Jensen–Pólya 理论。([arXiv][2])

现在先对任意实系数首一多项式 \(q\) 研究。设其次数为 \(d\)，根为：

$$
\lambda_1,\ldots,\lambda_d,
$$

按代数重数计。

令 \(C_q\) 为前文的观察型伴随矩阵，定义：

$$
\mu=\frac1d\operatorname{Tr}C_q\in\mathbb R,
\qquad
A=C_q-\mu I.
$$

于是：

$$
\operatorname{Tr}A=0.
$$

记中心化根：

$$
z_j=\lambda_j-\mu.
$$

定义三个不同的量：

$$
\boxed{
S_q=\operatorname{Tr}(A^2)=\sum_jz_j^2\in\mathbb R,
}
\tag{L2}
$$

$$
\boxed{
N_q=\operatorname{Tr}(A^*A),
}
$$

$$
\boxed{
Q_q=\sum_j|z_j|^2.
}
$$

它们满足：

$$
N_q\ge Q_q,
$$

以及：

$$
\boxed{
Q_q-S_q
=
2\sum_j(\Im\lambda_j)^2.
}
\tag{L3}
$$

因此：

**\(N_q-Q_q\) 测量表示中的非正规部分；\(Q_q-S_q\) 测量实际谱的非实部分。**

这正好对应前几轮已经分开的两种残差。

对实际 \(q_d\)，Newton 恒等式给出：

$$
\boxed{
S_d
=
\frac{d-1}{d}(a_1^2-2a_2)
=
-\frac{d-1}{12d}\chi_4.
}
\tag{L4}
$$

所以，整体中心位置由 \(a_1\) 决定，中心化的代数平方总量则由四阶累积量决定。

---

# 二、历史体积可以精确展开成 Schur 多项式的平方和

上一轮定义了单一读出的高斯历史矩阵：

$$
G_q(r)=
\int_{\mathbb R}
\frac{e^{-t^2/(2r)}}{\sqrt{2\pi r}}\,
e^{itC_q^*}\ell^*\ell e^{-itC_q}\,dt,
$$

其中：

$$
\ell=(1,0,\ldots,0).
$$

并定义：

$$
\mathcal Z_q(r)
=
\frac{\prod_{j=0}^{d-1}j!}{r^{d(d-1)/2}}
\det G_q(r).
$$

实数整体平移不改变 \(\mathcal Z_q\)。

定义酉群积分：

$$
\boxed{
\mathcal H_q(r)
=
\int_{U(d)}
\exp\!\left[
r\operatorname{Tr}(A^*UAU^*)
\right]\,dU.
}
\tag{L5}
$$

这里 \(dU\) 是归一化 Haar 测度。虽然被积函数未必逐点为实，积分却会是一个严格正的实数。

前文的 HCIZ 恒等式给出：

$$
\boxed{
\mathcal Z_q(r)=e^{-rS_q}\mathcal H_q(r).
}
\tag{L6}
$$

HCIZ 的行列式公式与 Schur 特征展开是已有的严格关系；它们可以通过解析延拓应用于这里的复谱，而不必预设 Hermitian 谱。([Springer][3])

## 定义 L1：全部从系数计算的 Schur 读数

设：

$$
\det(I-tA)=
1-e_1t+e_2t^2-\cdots+(-1)^de_dt^d.
$$

定义完全对称多项式读数 \(h_n\)：

$$
h_0=1,\qquad h_n=0\quad(n<0),
$$

$$
\boxed{
h_n=
\sum_{j=1}^{\min(n,d)}
(-1)^{j+1}e_jh_{n-j}.
}
\tag{L7}
$$

等价地：

$$
\sum_{n\ge0}h_nt^n=\frac1{\det(I-tA)}.
$$

对整数分区：

$$
\lambda=(\lambda_1\ge\cdots\ge\lambda_\ell>0),
\qquad \ell\le d,
$$

定义 Schur 读数：

$$
\boxed{
s_\lambda[A]
=
\det\bigl(h_{\lambda_i-i+j}\bigr)_{1\le i,j\le\ell}.
}
\tag{L8}
$$

再定义正整数：

$$
\boxed{
(d)_\lambda
=
\prod_{i=1}^{\ell}
\prod_{j=1}^{\lambda_i}(d+j-i).
}
$$

注意，这里的 \((d)_\lambda\) 是分区指标的乘积，不是前文的下降阶乘 \((d)_k\)。

最后定义：

$$
\boxed{
b_{q,k}
=
\sum_{\substack{\lambda\vdash k\\\ell(\lambda)\le d}}
\frac{|s_\lambda[A]|^2}{(d)_\lambda}.
}
\tag{L9}
$$

对于实系数 \(q\)，所有 \(s_\lambda[A]\) 都是实数。

**这里没有输入任何根。计算只使用实际多项式系数、有限递推和有限行列式。**

---

## 定理 L1：非负平方展开

$$
\boxed{
\mathcal H_q(r)
=
\sum_{k=0}^{\infty}b_{q,k}r^k,
\qquad
b_{q,k}\ge0.
}
\tag{L10}
$$

### 证明

先假设中心化根 \(z_1,\ldots,z_d\) 互异。

由 HCIZ 行列式公式：

$$
\mathcal H_q(r)
=
\frac{\prod_{j=0}^{d-1}j!}
{r^{d(d-1)/2}|\Delta(z)|^2}
\det\bigl(e^{rz_i\overline{z_j}}\bigr).
$$

对指数矩阵使用 Cauchy–Binet 展开：

$$
\det\bigl(e^{rz_i\overline{z_j}}\bigr)
=
\sum_{0\le n_1<\cdots<n_d}
\frac{r^{n_1+\cdots+n_d}}
{n_1!\cdots n_d!}
\left|\det(z_i^{n_j})\right|^2.
$$

每一个严格递增序列 \((n_1,\ldots,n_d)\)，对应一个长度不超过 \(d\) 的分区。除去最小指数和 \(d(d-1)/2\) 与 Vandermonde 因子后，行列式商就是相应 Schur 多项式，而阶乘比为：

$$
\frac1{(d)_\lambda}.
$$

由此得到式（L10）。

重根情形由多项式的连续性得到；Schur 读数本身不需要除以可能为零的 Vandermonde 因子。证毕。

### 一个重要警告

这证明的是：

$$
b_{q,k}\ge0
$$

对所有实系数多项式都成立。

**即使 \(q\) 已经有非实根，这些系数仍然非负。**

所以，正平方展开本身不是 RH 证明。问题变成：

> 这些非负项的总增长，是否超过实谱允许的尺度？

---

# 三、真正的量子投影概率，与历史体积之间差了什么？

这里可以把式（L5）构造成一份明确的量子读数。

取单粒子 Hilbert 空间：

$$
\mathfrak h=M_d(\mathbb C),
\qquad
\langle X,Y\rangle=\operatorname{Tr}(X^*Y),
$$

再取玻色 Fock 空间：

$$
\mathcal F_s(\mathfrak h)
=
\bigoplus_{k=0}^{\infty}\operatorname{Sym}^k\mathfrak h.
$$

定义归一化相干态：

$$
\boxed{
|\Omega_{A,r}\rangle
=
e^{-rN_q/2}
\bigoplus_{k=0}^{\infty}
\frac{r^{k/2}}{\sqrt{k!}}A^{\otimes k}.
}
\tag{L11}
$$

因为 \(\|A^{\otimes k}\|^2=N_q^k\)，所以它的范数为一。

酉群通过：

$$
A\longmapsto UAU^*
$$

作用于单粒子空间，再提升到 Fock 空间。

令：

$$
\Pi_{\mathrm{inv}}
=
\int_{U(d)}\Gamma(\operatorname{Ad}_U)\,dU.
$$

它是投影到酉共轭不变子空间的正交投影。

这是相干的群平均投影，**不是“随机选择一个酉操作，再忘记选择结果”的保迹混合信道**。两种操作不能混为一谈。

HCIZ 与这种 Segal–Bargmann/Fock 不变子空间的关系已有完整研究，甚至存在与反对称函数空间之间的精确酉对应。([arXiv][4])

## 定理 L2：投影概率

$$
\boxed{
p_q(r)
:=
\|\Pi_{\mathrm{inv}}\Omega_{A,r}\|^2
=
e^{-rN_q}\mathcal H_q(r)
\le1.
}
\tag{L12}
$$

### 证明

正交投影满足：

$$
\|\Pi\Omega\|^2=\langle\Omega,\Pi\Omega\rangle.
$$

相干态重叠给出：

$$
\langle\Omega_{A,r},
\Gamma(\operatorname{Ad}_U)\Omega_{A,r}\rangle
=
e^{-rN_q}
e^{r\operatorname{Tr}(A^*UAU^*)}.
$$

积分即得。证毕。

结合式（L6）：

$$
\boxed{
\mathcal Z_q(r)
=
e^{r(N_q-S_q)}p_q(r).
}
\tag{L13}
$$

而：

$$
N_q-S_q
=
2\left\|
\frac{A-A^*}{2i}
\right\|_{\mathrm{HS}}^2
\ge0.
$$

因此：

**量子力学只自动保证 \(p_q(r)\le1\)，并不自动保证 \(\mathcal Z_q(r)\le1\)。**

要得到历史体积上限，实际需要：

$$
\boxed{
p_q(r)\le e^{-r(N_q-S_q)}.
}
\tag{L14}
$$

这是一个更强的抑制要求。

如果先把 \(A\) 当成自伴算子，就有 \(N_q=S_q\)，于是式（L14）退化成普通概率上限。

**但对实际伴随矩阵，不能未经证明就作这个替换。**

这就是前文“是否把离线投没”问题的一个精确答案：危险并不在投影概率为正，而在把两种不同的归一化当成同一个量。

---

# 四、把整体上界拆成每个激发阶数的有限不等式

对于固定激发数 \(k\)，令 \(\Pi_k\) 是相应不变子空间投影。

当 \(N_q>0\) 时，定义：

$$
\pi_{q,k}
=
\left\|
\Pi_k
\left(\frac A{\sqrt{N_q}}\right)^{\otimes k}
\right\|^2.
$$

它是真正的投影概率，满足：

$$
0\le\pi_{q,k}\le1.
$$

比较式（L10）、（L12）的系数：

$$
\boxed{
\pi_{q,k}
=
\frac{k!\,b_{q,k}}{N_q^k}.
}
\tag{L15}
$$

所以普通量子正性给出的只是：

$$
b_{q,k}\le\frac{N_q^k}{k!}.
$$

零点定位需要比较的却是 \(S_q\)。

## 定理 L3：逐阶系数判据

对于实系数首一多项式 \(q\)，以下等价：

$$
\boxed{
q\text{ 全部实根}
}
$$

与：

$$
\boxed{
S_q\ge0,
\qquad
b_{q,k}\le\frac{S_q^k}{k!}
\quad\forall k\ge1.
}
\tag{L16}
$$

### 正向证明

若根全部实，令：

$$
\Lambda=\operatorname{diag}(z_1,\ldots,z_d).
$$

此时 \(\Lambda\) 自伴，且：

$$
\operatorname{Tr}\Lambda^2=S_q.
$$

定义实随机变量：

$$
X(U)=\operatorname{Tr}(\Lambda U\Lambda U^*).
$$

由 Hilbert–Schmidt Cauchy–Schwarz：

$$
|X(U)|\le S_q.
$$

同时：

$$
b_{q,k}
=
\frac1{k!}\int X(U)^k\,dU.
$$

这个积分非负已由定理 L1 保证；上界则由 \(|X|\le S_q\) 给出。证毕。

### 反向证明

若全部系数满足式（L16），则对所有 \(r>0\)：

$$
\mathcal H_q(r)\le e^{rS_q}.
$$

所以：

$$
\mathcal Z_q(r)\le1.
$$

上一轮已经证明：非实根会使历史行列式至少以：

$$
\exp\!\left(2r\sum_j(\Im\lambda_j)^2\right)
$$

的指数率增长，而基准只包含固定次幂。因此，若存在非实根，\(\mathcal Z_q(r)\) 最终必超过一。

故 \(q\) 全实根。证毕。

---

## 一个清楚的概率解释

当 \(S_q>0\)，定义：

$$
\boxed{
R_{q,k}
=
\frac{k!\,b_{q,k}}{S_q^k},
\qquad R_{q,0}=1.
}
\tag{L17}
$$

那么：

$$
\boxed{
\mathcal Z_q(r)
=
\mathbb E_{K\sim\operatorname{Poisson}(rS_q)}
[R_{q,K}].
}
\tag{L18}
$$

所以，历史体积是这些阶数指标的 Poisson 平均。

但 \(R_{q,k}\) 本身不必是概率。由式（L15）：

$$
\boxed{
R_{q,k}
=
\left(\frac{N_q}{S_q}\right)^k\pi_{q,k}.
}
$$

实根性要求：

$$
\boxed{
\pi_{q,k}\le\left(\frac{S_q}{N_q}\right)^k
\quad\forall k.
}
\tag{L19}
$$

**量子理论自动给出的是 \(\pi_{q,k}\le1\)；实际零点定位需要更强的、跨全部激发阶数的抑制规律。**

---

# 五、高阶系数的增长率，精确读取非实谱总量

前面的系数判据还可以加强成一个渐近恒等式。

## 定理 L4：平方级数的精确指数率

$$
\boxed{
\lim_{r\to\infty}
\frac{\log\mathcal H_q(r)}r
=
Q_q.
}
\tag{L20}
$$

因此：

$$
\boxed{
\lim_{r\to\infty}
\frac{\log\mathcal Z_q(r)}r
=
Q_q-S_q
=
2\sum_j(\Im\lambda_j)^2.
}
\tag{L21}
$$

### 证明

把酉群积分写在中心化对角谱上。由：

$$
\left|
\operatorname{Tr}(\Lambda^*U\Lambda U^*)
\right|
\le Q_q,
$$

得到：

$$
\mathcal H_q(r)\le e^{rQ_q}.
$$

另一方面，前文历史矩阵满足：

$$
\frac d{dr}\log\det G_q(r)
=
2\left\|
\frac{
G_q(r)^{1/2}C_qG_q(r)^{-1/2}
-
G_q(r)^{-1/2}C_q^*G_q(r)^{1/2}
}{2i}
\right\|_{\mathrm{HS}}^2.
$$

右边不小于：

$$
2\sum_j(\Im\lambda_j)^2.
$$

积分后，再扣除历史体积基准的 \(\frac{d(d-1)}2\log r\)，得到：

$$
\log\mathcal Z_q(r)
\ge
2r\sum_j(\Im\lambda_j)^2
-
\frac{d(d-1)}2\log r
+
O_q(1).
$$

与上界合并即得。重根情形也适用，因为这里没有除以根间距。证毕。

## 推论：系数增长率直接给出谱缺陷

$$
\boxed{
\limsup_{k\to\infty}
\bigl(k!\,b_{q,k}\bigr)^{1/k}
=
Q_q.
}
\tag{L22}
$$

因而：

$$
\boxed{
\sum_j(\Im\lambda_j)^2
=
\frac12
\left[
\limsup_{k\to\infty}
\bigl(k!\,b_{q,k}\bigr)^{1/k}
-S_q
\right].
}
\tag{L23}
$$

### 证明要点

由酉积分估计：

$$
0\le b_{q,k}\le\frac{Q_q^k}{k!}.
$$

若式（L22）的左边严格小于 \(Q_q\)，则存在 \(L<Q_q\)，使充分高阶的系数满足：

$$
b_{q,k}\le\frac{L^k}{k!}.
$$

于是：

$$
\mathcal H_q(r)\le \text{一个固定多项式}+e^{Lr},
$$

与定理 L4 矛盾。证毕。

因此，若 \(q\) 有非实根且 \(S_q\ge0\)，那么：

$$
R_{q,k}>1
$$

不仅在某一阶出现，而且会在无穷多个阶数出现。

但它不要求每一阶都超过一。

---

# 六、一个完全精确的反例：前八阶通过，第九阶失败，第十阶又通过

取：

$$
\boxed{
q(x)=(x-1)\bigl((x-4)^2+1\bigr)
=
x^3-9x^2+25x-17.
}
$$

它的反转多项式：

$$
P(v)=1+9v+25v^2+17v^3
$$

全部系数为正。

根为：

$$
1,\quad4+i,\quad4-i.
$$

中心为 \(\mu=3\)，因此中心化根是：

$$
-2,\quad1+i,\quad1-i.
$$

于是：

$$
S_q=4,\qquad Q_q=8,
\qquad
\sum_j(\Im\lambda_j)^2=2.
$$

可以精确算出：

$$
\boxed{
\mathcal H_q(r)
=
\frac{
e^{8r}-e^{4r}-2e^{-2r}
+
2e^{-4r}\cos6r
}{
200r^3
}.
}
\tag{L24}
$$

\(r=0\) 是可去奇点，值为一。

使用式（L7）—（L9）的有理数递推，可以得到：

| 激发阶数 \(k\) |       \(R_{q,k}\) |
| ---------: | ----------------: |
|          2 |           \(1/8\) |
|          3 |         \(27/80\) |
|          8 |   \(2839/3840<1\) |
|          9 | \(19737/14080>1\) |
|         10 | \(16953/22528<1\) |

前八阶全部不超过一，第九阶首次超过一，第十阶又回到一以下。

这些结果来自精确有理数运算；式（L24）的 Taylor 展开也给出了独立核对。

因此：

$$
\boxed{
\text{有限前缀通过}
\not\Rightarrow
\text{更高阶通过},
}
$$

而且：

$$
\boxed{
\text{某阶失败}
\not\Rightarrow
\text{后面每一阶都失败}.
}
$$

这里与前文 Jensen **次数**方向上的失败传播不同。当前固定同一个三次多项式，增加的是它的 Schur／Fock **激发阶数**。

**两个方向的指标不同，不能把一种单调性搬到另一种方向上。**

这也说明，这套检验未必比直接判别式更高效：这个三次多项式的非实根本来就很容易看出。它的价值在于分解历史体积和观察层次，而不是无条件地优于所有实根算法。

---

# 七、真正的投影概率读取什么？它首先读取非正规性，而非非实谱

由：

$$
p_q(r)=e^{-rN_q}\mathcal H_q(r)
$$

及定理 L4：

$$
\boxed{
-\lim_{r\to\infty}
\frac{\log p_q(r)}r
=
N_q-Q_q.
}
\tag{L25}
$$

所以：

$$
\boxed{
\begin{aligned}
\text{正投影概率的指数衰减}
&\longleftrightarrow N_q-Q_q,\\
\text{归一化历史体积的指数增长}
&\longleftrightarrow Q_q-S_q.
\end{aligned}
}
$$

前者是非正规性；后者是谱虚部。

例如，若 \(A\) 已经是一个含复对角元的正规矩阵，则：

$$
N_q=Q_q,
$$

所以真实投影概率没有严格负的指数衰减率。

但若存在非实谱：

$$
Q_q-S_q>0,
$$

历史体积仍然指数增长。

### 接到上一轮的正规化流

设前文的保谱流为 \(A(a)\)，并满足：

$$
\frac d{da}\|A(a)\|_{\mathrm{HS}}^2
=
-\frac12\|[A(a),A(a)^*]\|_{\mathrm{HS}}^2.
$$

因为 \(\mathcal H_q(r)\) 只依赖特征多项式，沿这条流保持不变。

因此，对固定 \(r\)：

$$
\boxed{
\frac d{da}\log p_{A(a)}(r)
=
\frac r2
\|[A(a),A(a)^*]\|_{\mathrm{HS}}^2
\ge0.
}
\tag{L26}
$$

正规化可以不断提高这份量子投影的成功概率。

但：

$$
\boxed{
\mathcal Z_q(r)
}
$$

完全不变，因为它由同一个特征多项式决定。

**所以，“投影越来越成功”可以只是表示越来越正规，并不意味着原来的非实谱正在减少。**

这比单独说“正概率不够”更具体：我们现在知道，哪一项概率变化测量的是哪一种缺陷。

---

# 八、实际 Jensen 塔的低激发阶数，存在一个可证明的盲区

现在分析 \(d\) 增大时，哪些系数检验能够自动通过。

设中心化根满足：

$$
\sum_{j=1}^{d}|z_j|\le L.
$$

对于 \(1\le k\le d\)，有：

$$
(d)_\lambda\ge(d-k+1)^k
\qquad(|\lambda|=k).
$$

另一方面，Schur 的 Cauchy 恒等式给出：

$$
\sum_\lambda |s_\lambda(z)|^2t^{|\lambda|}
=
\exp\left(
\sum_{m\ge1}
\frac{|p_m(z)|^2}{m}t^m
\right),
$$

其中：

$$
p_m(z)=\sum_jz_j^m.
$$

由：

$$
|p_m(z)|\le L^m,
$$

逐项比较非负系数：

$$
\sum_{\lambda\vdash k}|s_\lambda(z)|^2\le L^{2k}.
$$

这类特征展开、Schur 正交性与酉群矩之间的关系是标准表示论工具。([arXiv][5])

因此：

## 定理 L5：低阶自动上界

$$
\boxed{
b_{q,k}
\le
\frac{L^{2k}}{(d-k+1)^k}.
}
\tag{L27}
$$

当 \(S_q>0\) 时：

$$
\boxed{
R_{q,k}
\le
\left[
\frac{kL^2}{S_q(d-k+1)}
\right]^k.
}
\tag{L28}
$$

所以只要：

$$
kL^2\le S_q(d-k+1),
$$

这一阶必然通过。

---

## 为什么它适用于实际系数塔？

前几轮已经从实际 \(D\) 的增长与圆周 Jensen 公式证明：

$$
\sup_d\sum_j|\lambda_{d,j}|<\infty.
$$

中心化只使这个上界增加至多 \(a_1\)，因此存在与 \(d\) 无关的 \(L\)，满足：

$$
\sum_j|z_{d,j}|\le L.
$$

其分析基础是实际 ξ 的无条件增长：

$$
\log D(v)=O(\sqrt v\log v),
$$

由标准 ξ 定义与 Gamma 的 Stirling 展开得到。([DLMF][1])

现在明确增加一项**固定低阶前件**：

$$
\boxed{\chi_4<0.}
\tag{H4}
$$

它只涉及四阶统计，可以独立认证，不等于 RH。

由式（L4），对 \(d\ge2\)：

$$
S_d\ge S_0:=\frac12(a_1^2-2a_2)>0.
$$

于是存在一个固定常数 \(c_*>0\)，例如：

$$
c_*=\frac{S_0}{2(L^2+S_0)},
$$

使：

$$
\boxed{
1\le k\le c_*d
\Longrightarrow
R_{q_d,k}\le1.
}
\tag{L29}
$$

**这项结论没有使用全阶实根性。**

因此，在上述固定四阶前件下：

> 不仅每个固定激发阶数最终都会通过，甚至一个随 \(d\) 线性增长的低阶区域，都可以由通用界保证通过。

这不表示所有复杂性都已解决，恰恰相反：

$$
\boxed{
\text{真正可能区分 RH 真伪的检验，
必须进入与 }d\text{ 一起增长的更深阶数。}
}
$$

例如，中心化后恒有：

$$
b_{q,1}=0,
$$

以及对 \(d\ge2\)：

$$
\boxed{
b_{q,2}=\frac{S_q^2}{2(d^2-1)}.
}
$$

所以：

$$
\boxed{
R_{q,2}=\frac1{d^2-1},
}
$$

根本不区分这个 \(q\) 有没有非实根。

这是一条非常具体的“有限观察盲区”，而不是因为观察者本身具有某种神秘的不可约性。

---

# 九、现在怎样得到有限反例证书，而不做高维酉积分？

定理 L1 的全部系数非负，带来一个实际便利。

对任意有限 \(K\)：

$$
\mathcal H_q(r)\ge
\sum_{k=0}^{K}b_{q,k}r^k.
$$

所以，只要严格认证：

$$
\boxed{
\sum_{k=0}^{K}b_{q,k}r^k>e^{rS_q},
}
\tag{L30}
$$

就得到：

$$
\mathcal Z_q(r)>1,
$$

进而证明 \(q\) 有非实根。

这里**不需要估计被截掉的平方级数尾部**，因为尾部只能增加左边。

另一种有限证书是：

$$
\boxed{
k!\,b_{q,k}>S_q^k
}
\tag{L31}
$$

对某个 \(k\) 成立。由定理 L3，这同样排除全实根。

对于实际 \(q_d\)，一份严格的式（L30）或（L31）证书，就通过 Jensen 判据否证 RH。

但计算仍须保留：

$$
\text{实际 theta 系数误差}
\longrightarrow
\text{对称多项式误差}
\longrightarrow
\text{Schur 行列式误差}
\longrightarrow
\text{最终不等式余量}.
$$

正平方展开不等于没有数值抵消：每个 Schur 行列式内部仍可能包含很强的相消。

**本轮没有得到实际 ξ 的此类违例证书。上面的精确违例来自明确标注的三次模型。**

---

# 十、实际待证命题现在可以完全写成系数不等式

对每个实际 \(q_d\)，定义：

$$
A_d=C_{q_d}-\frac{a_1}{d}I,
$$

$$
S_d=\operatorname{Tr}(A_d^2)
=
-\frac{d-1}{12d}\chi_4.
$$

再完全按照式（L7）—（L9），从实际系数计算 Schur 读数。

那么：

$$
\boxed{
\mathrm{RH}
\iff
\left[
S_d\ge0,\quad
k!\!
\sum_{\substack{\lambda\vdash k\\\ell(\lambda)\le d}}
\frac{|s_\lambda[A_d]|^2}{(d)_\lambda}
\le S_d^k
\right]
\quad\forall d\ge2,\ \forall k\ge1.
}
\tag{L32}
$$

这条式子不输入未知零点，也不输入一个已经正的自由算子。

但它仍然需要实际算术证明。

**普通 Fock 空间正性只给出右边为 \(N_d^k\) 的更弱上界；把 \(N_d\) 降到 \(S_d\)，才是承重部分。**

若试图通过“量子投影概率不超过一”来证明式（L32），就会在这个降尺度步骤发生循环。

---

# 十一、与项目现有工作的准确连接

本轮重新读取的 `JensenPolynomialObstruction.lean`，仍把实际 Jensen 塔与 RH 的分析桥作为显式前件。它没有无条件提供式（L32）这样的全阶系数估计。

`ObservabilityGramianKernelEnergy.lean` 在其稳定性前件下，证明历史能量为零与所有未来读数为零等价。它负责“是否遗漏状态”，并不自动证明历史体积满足实谱上界。

现在可以明确分成：

$$
\boxed{
\begin{aligned}
\text{可观测性}&:\quad \text{历史有没有遗漏有限模式};\\
\text{量子合法性}&:\quad p_q(r)\le1;\\
\text{零点定位}&:\quad
p_q(r)\le e^{-r(N_q-S_q)}.
\end{aligned}
}
$$

第三项严格强于前两项。

本轮检索没有获得一个已经完成这里“实际 Jensen 系数—Schur 平方上界”的对应 Lean 定理。因此，这些新增推导仍是聊天中的纸面结果，不能标记成仓库已经编译验证的结论。

---

# 收束

这次没有继续增加一种模糊的“量子相似性”，而是把前文的历史体积拆成了：

$$
\boxed{
\mathcal Z_q(r)
=
e^{-rS_q}
\sum_{k\ge0}r^k
\sum_{\lambda\vdash k}
\frac{|s_\lambda[A]|^2}{(d)_\lambda}.
}
$$

由此得到一个清楚的区别：

$$
\boxed{
\text{每一项都是正平方}
\quad\not\Rightarrow\quad
\text{全部项的增长不超过实谱基准}.
}
$$

真正的量子投影概率为：

$$
\boxed{
p_q(r)
=
e^{-rN_q}
\sum_{k\ge0}b_{q,k}r^k,
}
$$

它永远合法；但要回答零点问题，需要保留 \(N_q\)、\(Q_q\)、\(S_q\) 三者之间的差异。

同时，我们证明了：

$$
\boxed{
\limsup_{k\to\infty}(k!b_{q,k})^{1/k}-S_q
=
2\sum_j(\Im\lambda_j)^2.
}
$$

所以，决定离线的内容没有被投影消失，它进入了**全部高阶不变量共同决定的增长率**。

而低阶检验可以在很大范围内自动通过。这意味着：

> **“有限观察越来越正常”可能只是因为观察阶数增长得不够快；真正的整体条件，要求观察阶数与算术模型的维数一起深入，并始终保持同一个归一化。**

当前尚未证明实际系数满足式（L32），也没有实际违例。新的可研究目标已经集中为：**能否利用实际 theta 的模关系或质数尺度结构，把通用量子上界 \(N_d^k\) 加强为算术所需的 \(S_d^k\)，尤其控制低阶自动通过区域之外的那些分区贡献。**

这一步若能完成，Schur 分区、反对称历史与量子观察才不只是忠实表示，而会真正承担零点定位的证明责任。

[1]: https://dlmf.nist.gov/25.4 "https://dlmf.nist.gov/25.4"
[2]: https://arxiv.org/abs/1902.07321 "https://arxiv.org/abs/1902.07321"
[3]: https://link.springer.com/article/10.1140/epjc/s10052-025-14374-9 "https://link.springer.com/article/10.1140/epjc/s10052-025-14374-9"
[4]: https://arxiv.org/html/2312.16816v5 "https://arxiv.org/html/2312.16816v5"
[5]: https://arxiv.org/abs/math-ph/0205010 "https://arxiv.org/abs/math-ph/0205010"
这次可以把上一轮的结论推进成一个**必须认真区分的双极限定理**：

> **固定模型以后，把观察历史加深，能够暴露非实谱；但固定观察尺度，先把模型维数放大，群平均却会把同一类缺陷稀释掉。**

甚至可以证明：在一段明确的参数范围内，**让观察历史与维数一起线性增长，归一化历史体积也会自动趋向零——这一结论并不需要全阶实根性。**

所以，“模型越来越大、观察越来越久、统计越来越正常”，仍然不足以证明 RH。关键在于：**两个参数怎样一起增长，以及读取的是完整关系还是越来越粗的平均。**

下面把这件事严格展开。它还会给出一个实际改进：怎样从高阶模型中精确取回某个低阶证书，而不让群平均把它稀释。

---

# 一、固定前文对象，并明确三个不同的“深度”

仍使用：

$$
D(b^2)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad
D(v)=\sum_{k\ge0}a_kv^k,
$$

以及：

$$
P_d(v)=\sum_{k=0}^{d}\frac{(d)_k}{d^k}a_kv^k,
\qquad
q_d(x)=x^dP_d(-1/x).
$$

ξ 的定义、反射关系与归一化保持不变。([DLMF][1])

前文使用的 Jensen–Pólya 判据仍是：

$$
\boxed{
\mathrm{RH}
\iff
q_d\text{ 的根全部为正实数，}\quad\forall d.
}
\tag{M1}
$$

这项分析桥属于经典理论，不是下面的量子群平均自动提供的结论。([arXiv][2])

这里有三个不同参数：

$$
\boxed{
d=\text{有限算术模型的维数},
}
$$

$$
\boxed{
k=\text{Schur／Fock 激发阶数},
}
$$

$$
\boxed{
r=\text{高斯历史方差或群积分的放大参数}.
}
$$

**增加 \(d\)、增加 \(k\)、增加 \(r\)，不是同一件事。**

设 \(q_d\) 的根为 \(\theta_{d,j}\)，按代数重数计。令：

$$
z_{d,j}=\theta_{d,j}-\frac{a_1}{d},
\qquad
\sum_{j=1}^{d}z_{d,j}=0.
$$

定义中心化代数平方总量：

$$
S_d=\sum_jz_{d,j}^2.
$$

由 Newton 恒等式：

$$
\boxed{
S_d=\frac{d-1}{d}S_*,
\qquad
S_*=a_1^2-2a_2=-\frac{\chi_4}{12}.
}
\tag{M2}
$$

沿用前文的群积分与相对历史体积：

$$
\mathcal H_d(r)
=
\int_{U(d)}
\exp\!\left[
r\,\operatorname{Tr}
(\Lambda_dU\Lambda_d^*U^*)
\right]dU,
$$

$$
\boxed{
\mathcal Z_d(r)=e^{-rS_d}\mathcal H_d(r),
}
\tag{M3}
$$

其中 \(\Lambda_d=\operatorname{diag}(z_{d,1},\ldots,z_{d,d})\)。

根只用于证明和解释；这两个量仍可由实际系数、伴随矩阵与历史 Gramian 定义，不需要先输入根。

前文已经得到 Schur 平方展开：

$$
\boxed{
\mathcal H_d(r)
=
\sum_{k\ge0}b_{d,k}r^k,
\qquad
b_{d,k}
=
\sum_{\substack{\lambda\vdash k\\\ell(\lambda)\le d}}
\frac{|s_\lambda(z_d)|^2}{(d)_\lambda}\ge0.
}
\tag{M4}
$$

这里的 HCIZ—Schur—不变子空间关系是经典工具。([arXiv][3])

---

# 二、先取得一项不依赖 RH 的统一算术预算

下面需要一个与 \(d\) 无关的常数 \(L\)，满足：

$$
\boxed{
\sum_{j=1}^{d}|z_{d,j}|\le L.
}
\tag{M5}
$$

这不是新增的 RH 假设。它可以从前文已经建立的实际函数增长推出来。

因为 \(D(0)=1\)，选取 \(\rho_*>0\)，使：

$$
D(\rho_*)<2.
$$

于是所有 \(P_d\) 在 \(|v|\le\rho_*\) 内无零，因此：

$$
|\theta_{d,j}|\le M:=\rho_*^{-1}.
$$

再令：

$$
N_d(t)=\#\{j:|\theta_{d,j}|\ge t\}.
$$

圆周 Jensen 公式给出：

$$
N_d(t)\le\frac{\log D(2/t)}{\log2}.
$$

所以：

$$
\sum_j|\theta_{d,j}|
=
\int_0^M N_d(t)\,dt
\le
\frac1{\log2}\int_0^M\log D(2/t)\,dt.
$$

实际 ξ 的定义与 Stirling 展开保证：

$$
\log D(v)=O(\sqrt v\log v),
$$

故右边有限。这里使用的是无条件增长估计，而不是零点在线前件。([DLMF][4])

因此可以明确取：

$$
\boxed{
L=
a_1+
\frac1{\log2}\int_0^M\log D(2/t)\,dt.
}
\tag{M6}
$$

这个常数可能很保守，但有三个优点：

**由实际 \(D\) 确定、不需要根的位置、对全部阶数统一。**

---

# 三、一个比上一轮更强的通用界：全部激发阶数都能控制

先给出酉矩阵的一项基本矩公式。

若 \(U\) 按 Haar 测度分布于 \(U(d)\)，则：

$$
\boxed{
\mathbb E|U_{11}|^{2k}
=
\frac{k!}{d(d+1)\cdots(d+k-1)}.
}
\tag{M7}
$$

可以把 Haar 矩阵第一列表示成独立复高斯向量的归一化，由此得到该公式。一般 Haar 多项式积分与矩展开的系统理论见 Collins–Śniady。([arXiv][5])

为了避免与下降阶乘混淆，记：

$$
d^{\overline k}=d(d+1)\cdots(d+k-1).
$$

## 定理 M1：维数稀释界

在式（M5）下，对所有 \(k\ge0\)：

$$
\boxed{
0\le b_{d,k}\le\frac{L^{2k}}{d^{\overline k}}.
}
\tag{M8}
$$

特别地，当：

$$
0\le r<\frac d{L^2},
$$

有：

$$
\boxed{
1\le\mathcal H_d(r)
\le
\frac1{1-rL^2/d}.
}
\tag{M9}
$$

### 证明

令：

$$
X_d(U)=\operatorname{Tr}(\Lambda_dU\Lambda_d^*U^*).
$$

写 \(c_i=|z_{d,i}|\)，则：

$$
|X_d(U)|
\le
\sum_{i,j}c_ic_j|U_{ij}|^2.
$$

设 \(L_d=\sum_i c_i\le L\)。把 \(c_ic_j/L_d^2\) 视为一组和为一的权重，由凸性：

$$
|X_d(U)|^k
\le
L_d^{2k}
\sum_{i,j}
\frac{c_ic_j}{L_d^2}|U_{ij}|^{2k}.
$$

取 Haar 平均：

$$
\mathbb E|X_d|^k
\le
L^{2k}\frac{k!}{d^{\overline k}}.
$$

而：

$$
b_{d,k}=\frac1{k!}\mathbb E[X_d^k],
$$

它的非负性由 Schur 平方展开保证。因此得到式（M8）。

最后使用：

$$
d^{\overline k}\ge d^k,
$$

对非负级数求和：

$$
\mathcal H_d(r)
\le
\sum_{k\ge0}\left(\frac{rL^2}{d}\right)^k.
$$

即得式（M9）。证毕。

### 这里真正发生了什么？

不是算术对象突然变得更接近实谱，而是：

$$
\boxed{
\text{固定总谱权重分布在更大的酉群中，}
\quad
\text{单个群平均关联被维数抑制。}
}
$$

这个机制对实谱和非实谱都适用。

---

# 四、一个必须排除的误判：一大片历史窗口会自动通过

为讨论“体积不超过一”的判据，单独列出一个低阶前件：

$$
\boxed{S_*>0.}
\tag{A0}
$$

它只涉及 \(\chi_4<0\)，不是全阶 RH 假设。前文实际数值为：

$$
S_*\approx3.7172599285\times10^{-5}.
$$

以下定理保留这个有限阶前件，不把数值核对当成全阶证明。

## 定理 M2：线性历史窗口的自动通过区域

若：

$$
d\ge\max\left(2,\frac{8L^2}{S_*}\right),
$$

且：

$$
0<r\le\frac d{2L^2},
$$

则：

$$
\boxed{
\mathcal Z_d(r)
\le
e^{-rS_*/4}<1.
}
\tag{M10}
$$

### 证明

由 \(S_d\ge S_*/2\) 和定理 M1：

$$
\log\mathcal Z_d(r)
\le
-rS_d-\log(1-rL^2/d).
$$

当 \(0\le x\le1/2\) 时：

$$
-\log(1-x)\le2x.
$$

所以：

$$
\log\mathcal Z_d(r)
\le
-\frac{rS_*}{2}+\frac{2rL^2}{d}
\le
-\frac{rS_*}{4}.
$$

证毕。

**这一上界没有使用“所有 \(q_d\) 都实根”。**

因此：

> 在这段明确的线性窗口内，观察模型可以越来越大，历史宽度也可以越来越大，体积却仍然自动表现得“符合实谱上限”。

这不否定前文 \(r=d^4\) 的判据，因为 \(d^4\) 最终远远超出这个自动通过区域。

但它排除了一个错误推理：

$$
\boxed{
d\to\infty,\quad r_d\to\infty,\quad
\mathcal Z_d(r_d)\le1
\quad\not\Rightarrow\quad
\mathrm{RH}.
}
$$

**“两个参数都趋于无穷”还不够，必须说明它们的相对尺度。**

---

# 五、进一步算出线性尺度上的精确极限

上面的界告诉我们存在稀释。现在计算稀释以后究竟剩下什么。

定义中心化幂和：

$$
p_m^{(d)}=\sum_{j=1}^{d}z_{d,j}^{\,m}.
$$

显然：

$$
p_1^{(d)}=0.
$$

对固定 \(m\ge2\)，由 \(P_d\to D\) 的系数收敛及 Newton 恒等式：

$$
\boxed{
p_m^{(d)}\longrightarrow\rho_m,
\qquad
\rho_m=
(-1)^{m-1}\frac{m\chi_{2m}}{(2m)!}.
}
\tag{M11}
$$

这里 \(\rho_m\) 是一个系数读数，**不是零点坐标**。

前几项为：

$$
\rho_2=-\frac{\chi_4}{12}=M_0,
$$

$$
\rho_3=\frac{\chi_6}{240}=M_1,
$$

$$
\rho_4=-\frac{\chi_8}{10080}=M_2.
$$

它们恰好是前文回返函数的矩。

## 定理 M3：双尺度极限

对足够小的复数 \(\vartheta\)，具体地：

$$
|\vartheta|L^2<1,
$$

有局部一致收敛：

$$
\boxed{
\mathcal H_d(d\vartheta)
\longrightarrow
\mathcal F_\xi(\vartheta),
}
\tag{M12}
$$

其中：

$$
\boxed{
\mathcal F_\xi(\vartheta)
=
\exp\left[
\sum_{m=2}^{\infty}
\frac{|\rho_m|^2}{m}\vartheta^m
\right].
}
\tag{M13}
$$

### 证明

固定 \(k\)。Schur 多项式是前 \(k\) 个幂和的多项式，而：

$$
\frac{(d)_\lambda}{d^k}\longrightarrow1
\qquad(|\lambda|=k).
$$

因此：

$$
d^kb_{d,k}
\longrightarrow
\sum_{\lambda\vdash k}|s_\lambda(\rho)|^2,
$$

其中使用的幂和指定为：

$$
p_1=0,\qquad p_m=\rho_m\quad(m\ge2).
$$

Schur 的 Cauchy 恒等式给出形式幂级数恒等式：

$$
\sum_\lambda
|s_\lambda(\rho)|^2\vartheta^{|\lambda|}
=
\exp\left[
\sum_{m\ge1}\frac{|p_m|^2}{m}\vartheta^m
\right].
$$

这个恒等式的经典来源，是矩阵空间对称代数的分解；它不要求这些幂和先来自一个实谱。([arXiv][6])

最后，由定理 M1：

$$
0\le d^kb_{d,k}\le L^{2k}.
$$

所以在 \(|\vartheta|L^2<1\) 内，可以逐项取极限，得到式（M12）、（M13）。证毕。

### 前几阶可以明确写出

$$
\boxed{
\begin{aligned}
\mathcal F_\xi(\vartheta)
={}&1+\frac{M_0^2}{2}\vartheta^2
+\frac{M_1^2}{3}\vartheta^3\\
&+\left(
\frac{M_2^2}{4}+\frac{M_0^4}{8}
\right)\vartheta^4+\cdots.
\end{aligned}
}
\tag{M14}
$$

这是一份**成对高阶关联的生成函数**。

它不是新的独立算术对象；全部系数已经由实际 ξ 固定。

也不能因为右边是正平方生成函数，就宣布 RH。这个极限的建立没有要求 \(\rho_m\) 具有正谱矩表示。

---

## 推论：线性尺度上的体积确实趋零

在前件 \(S_*>0\) 下，对：

$$
0<\vartheta<L^{-2},
$$

有：

$$
\boxed{
e^{d\vartheta S_d}\mathcal Z_d(d\vartheta)
\longrightarrow
\mathcal F_\xi(\vartheta)>0.
}
$$

所以：

$$
\boxed{
\mathcal Z_d(d\vartheta)\longrightarrow0,
}
\tag{M15}
$$

并且：

$$
\boxed{
\frac1d\log\mathcal Z_d(d\vartheta)
\longrightarrow-\vartheta S_*.
}
\tag{M16}
$$

**一个很稳定、很规则的统计极限，已经出现了；但它没有判定 RH。**

这正好解释了为什么“更经典、更统计”可能产生一种表面上的完成：某些全局谱区别没有消失，只是离开了当前缩放窗口。

---

# 六、两个极限确实不交换，而且差异可以算出来

对固定 \(r>0\)，由定理 M1：

$$
\mathcal H_d(r)\longrightarrow1.
$$

因此：

$$
\boxed{
\lim_{d\to\infty}
\frac1r\log\mathcal Z_d(r)
=
-S_*.
}
\tag{M17}
$$

另一方面，固定 \(d\)，前文已经证明：

$$
\boxed{
\lim_{r\to\infty}
\frac1r\log\mathcal Z_d(r)
=
2\sum_{j=1}^{d}(\Im\theta_{d,j})^2.
}
\tag{M18}
$$

对于实际序列，局部零点收敛加上统一倒数谱尾界，允许对平方和取极限。

记：

$$
\mathfrak E_\xi
=
4\sum_{\substack{\rho\ \mathrm{互异}\\\Im\rho>0}}
\frac{
m_\rho(\Re\rho-\frac12)^2(\Im\rho)^2
}{
\left[
(\Re\rho-\frac12)^2+(\Im\rho)^2
\right]^4
}.
$$

它非负，且：

$$
\mathfrak E_\xi=0\iff\mathrm{RH}.
$$

于是：

$$
\boxed{
\lim_{r\to\infty}\lim_{d\to\infty}
\frac{\log\mathcal Z_d(r)}r
=
-S_*,
}
\tag{M19}
$$

而：

$$
\boxed{
\lim_{d\to\infty}\lim_{r\to\infty}
\frac{\log\mathcal Z_d(r)}r
=
2\mathfrak E_\xi.
}
\tag{M20}
$$

在 \(S_*>0\) 下，前者严格为负，后者非负。

**即使 RH 成立，这两个极限也分别是 \(-S_*\) 和 \(0\)，仍然不同。**

因此，不能把这种不交换本身称为 RH 失败。

它说明的是：

> **先让观察空间无限大，再在留下的统计模型里增加观察深度，与先充分辨认每个有限模型、再取整体极限，不是同一种操作。**

这不是文字上的“整体与局部不同”，而是两个已经算出不同值的极限。

---

# 七、一个完全精确的模型：非实根不变，仅增加辅助模式就能推迟暴露

取上一轮的三次模型：

$$
q_3(x)=(x-1)\bigl((x-4)^2+1\bigr).
$$

现在对 \(N\ge3\)，定义：

$$
\boxed{
q_N(x)
=
(x-3)^{N-3}(x-1)\bigl((x-4)^2+1\bigr).
}
\tag{M21}
$$

根始终包含同一对：

$$
4+i,\qquad4-i.
$$

新增的只是重复实根 \(3\)。

其反转多项式为：

$$
\boxed{
P_N(v)
=
(1+3v)^{N-3}
(1+9v+25v^2+17v^3),
}
$$

全部系数为正。

中心化以后，谱为：

$$
-2,\quad1+i,\quad1-i,
\quad\underbrace{0,\ldots,0}_{N-3}.
$$

所以：

$$
\boxed{
S_N=4,\qquad Q_N=8,
\qquad
\sum_j(\Im\lambda_j)^2=2
}
$$

都不随 \(N\) 改变。

这不是实际 Jensen 塔，而是专门检验“增加辅助模式会不会稀释观察”的精确反例。

## 第一项现象：每个固定阶数越来越正常

对这个模型：

$$
\mathcal H_N(r)=\sum_kb_{N,k}r^k,
$$

定义：

$$
R_{N,k}=\frac{k!b_{N,k}}{4^k}.
$$

使用精确整数 Schur 递推与有理数运算，本轮得到：

| 维数 \(N\) | 首次出现 \(R_{N,k}>1\) 的阶数 \(k\) |                            该阶数的值 |
| -------: | ---------------------------: | -------------------------------: |
|        3 |                            9 |   \(19737/14080\approx1.401776\) |
|        4 |                           17 | \(554353/544768\approx1.017595\) |
|        6 |                           35 |              \(\approx1.003654\) |
|       10 |                           73 |              \(\approx1.423383\) |

这里“首次”是逐阶用精确有理数比较得到的有限计算结果，不是浮点符号猜测。

**同一对非实根没有移动，但观察到违例所需的激发阶数明显增加。**

## 第二项现象：连线性增长的历史也可能看不见

这个固定三模结构的 Cauchy 极限可以直接写成：

$$
\boxed{
\mathcal F_*(\vartheta)
=
\frac1{
(1-4\vartheta)
(1-2\vartheta)^2
(1+4\vartheta+8\vartheta^2)^2
(1+4\vartheta^2)
}.
}
\tag{M22}
$$

它来自：

$$
\prod_{i,j=1}^{3}(1-\vartheta z_i\overline z_j)^{-1},
\qquad
(z_1,z_2,z_3)=(-2,1+i,1-i).
$$

由于这里只有三个非零中心化模式，可以把收敛范围扩大到：

$$
|\vartheta|<\frac14.
$$

于是对每个：

$$
0<\vartheta<\frac14,
$$

有：

$$
\boxed{
\mathcal H_N(N\vartheta)\longrightarrow\mathcal F_*(\vartheta),
}
$$

但：

$$
\boxed{
\mathcal Z_N(N\vartheta)
=
e^{-4N\vartheta}\mathcal H_N(N\vartheta)
\longrightarrow0.
}
\tag{M23}
$$

同时，对每个固定 \(N\)：

$$
\boxed{
\lim_{r\to\infty}\frac{\log\mathcal Z_N(r)}r=4.
}
$$

所以，一边的极限看起来越来越“压制”，另一边却始终能检测到非实谱增长。

### 这里究竟改变了什么？

不仅增加了辅助模式，还把原来的 \(U(3)\) 群平均换成了 \(U(N)\) 群平均。

**加入一个完全不参与操作的辅助寄存器，不会凭空改变原读数。改变观察群，让它混合更多方向，才产生这里的稀释。**

这项操作边界必须保留。

---

# 八、数据并未永久丢失：实际 Jensen 层之间有精确的回读映射

上面的反例说明平均可以隐藏缺陷，但不说明高阶系数中无法恢复低阶证据。

对实际 \(P_d\)，若 \(n\le d\)，定义：

$$
\boxed{
\mathcal R_{n\leftarrow d}[P](v)
=
\sum_{k=0}^{n}
\frac{\omega_{n,k}}{\omega_{d,k}}
[v^k]P(v)\,v^k,
}
\tag{M24}
$$

其中：

$$
\omega_{d,k}=\frac{(d)_k}{d^k}.
$$

## 定理 M4：有限算术关系可以精确回读

$$
\boxed{
\mathcal R_{n\leftarrow d}[P_d]=P_n.
}
\tag{M25}
$$

### 证明

逐项代入：

$$
[v^k]P_d=\omega_{d,k}a_k.
$$

于是：

$$
\frac{\omega_{n,k}}{\omega_{d,k}}[v^k]P_d
=
\omega_{n,k}a_k.
$$

证毕。

而且，固定 \(k\) 时，不碰撞概率随槽位数增加而增加，所以：

$$
0<
\frac{\omega_{n,k}}{\omega_{d,k}}
\le1.
$$

因此，若高阶系数误差为 \(\varepsilon_k\)，回读后的对应系数误差不超过：

$$
\boxed{
\frac{\omega_{n,k}}{\omega_{d,k}}\varepsilon_k
\le\varepsilon_k.
}
\tag{M26}
$$

这只是系数坐标中的稳定性；之后若构造病态矩阵，仍需继续传递误差。

### 这项结果怎样使用？

假设某个固定实际 \(P_n\) 有严格负证书，比如前文 Bézout 矩阵满足：

$$
u^*B_nu<0.
$$

那么，不论我们后来研究多大的 \(P_d\)，只要保留足够精确的前 \(n\) 个系数，就能通过式（M25）取回**同一个证书**。

因此：

$$
\boxed{
\text{高维群平均看不见某个缺陷}
\quad\not\Rightarrow\quad
\text{高维算术数据没有保存该缺陷}.
}
$$

差异在于使用了什么读出。

式（M24）首先是一个多项式数据映射，不能未经构造就称为完全正量子信道。但它已经说明：理论上没有必要让所有证据都经过同一个会稀释的平均通道。

---

# 九、前文的 \(r=d^4\) 判据，实际在要求多深的激发阶数？

上一轮有：

$$
\mathcal Z_d(r)
=
\mathbb E_{K\sim\operatorname{Poisson}(rS_d)}
[R_{d,K}],
$$

其中：

$$
R_{d,k}=\frac{k!b_{d,k}}{S_d^k}.
$$

因此，历史宽度 \(r\) 与主要参与的激发阶数并非独立：

$$
\boxed{
k_{\mathrm{typical}}\approx rS_d.
}
\tag{M27}
$$

若使用：

$$
r=d^4,
$$

那么：

$$
k_{\mathrm{typical}}\asymp S_*d^4.
$$

而定理 M1还给出：

$$
R_{d,k}
\le
\frac{k!L^{2k}}{d^{\overline k}S_d^k}
\le
\left(\frac{kL^2}{dS_d}\right)^k.
$$

在 \(S_*>0\)、\(d\ge2\) 下，若：

$$
k\le\frac{S_*}{4L^2}d,
$$

则：

$$
\boxed{R_{d,k}\le2^{-k}.}
\tag{M28}
$$

也就是说，线性阶数范围里甚至存在一个通用的指数抑制。

但在 \(r=d^4\) 时，Poisson 分布落入这段低阶区域的概率至多具有：

$$
\boxed{
\Pr(K\le cd)
\le
\exp\!\left[-S_dd^4+O(d\log d)\right]
}
\tag{M29}
$$

这样的量级，其中 \(c>0\) 固定。

因此：

> **在真正用于全局判据的历史尺度上，低阶自动通过区对总读数的贡献已经极小。**

这就明确了下一项算术估计应当针对哪里。

不是继续重复检查：

$$
k=2,3,4,\ldots
$$

这几个固定阶数，也不是只检查 \(k\) 缓慢增长的区域。

而是要控制与历史尺度匹配的高阶分区贡献，以及那些可能虽概率小、但数值极大的 \(R_{d,k}\)。

**仅有“典型行为”还不够，因为 Poisson 平均中的罕见项可能携带很大的权重。**

---

# 十、对“量子观察者、奇偶与整体”的解释，现在更精确了

这一轮证明的不是“无限维一定会丢信息”，也不是“数学注定把离线投掉”。

我们发现的是三种不同操作：

$$
\boxed{
\text{增加实际算术信息}
}
$$

$$
\boxed{
\text{扩大允许混合的观察群}
}
$$

$$
\boxed{
\text{增加读出所能分辨的关联阶数}.
}
$$

它们不能混为同一种“观察者升级”。

一个模型可以增加维数，同时扩大群平均，却没有同步增加有效分辨率。这时，某些固定读数会越来越小、越来越规则。

但这种规则可能来自稀释，而不是来自原结构的全正性。

项目的 `StaticEffectSequentialSeparation.lean` 已经证明，两个量子仪器可以拥有相同的单步效应，却给出不同的两步联合概率。这也说明：只看某一类静态读数，不足以确定完整观察协议。

本轮的对应区别是：

> **同一组非实谱，可以在不同维数的群平均下产生越来越正常的低阶统计；但精确的算术回读仍然能够保存原来的有限证书。**

所以，你此前所说的“奇”可以提示我们追踪被平均掉的定向和相位，但不能把“奇还存在”直接当作离线结论。

同样，“偶的统计越来越稳定”也不能直接作为实谱结论。

真正承重的是：

$$
\boxed{
\text{在当前观察尺度下，
哪些目标性质仍然能够被忠实区分？}
}
$$

---

# 十一、现在剩下的算术任务，位置已经更加明确

本轮核对的 `JensenPolynomialObstruction.lean` 仍把 Jensen 塔与 RH 的分析桥列作显式前件，并没有提供实际全阶实根性。

因此，不能把本轮的自动通过界：

$$
\mathcal Z_d(r)<1
\qquad
\left(r\le\frac d{2L^2}\right)
$$

送进一个需要 \(r=d^4\) 的定理，然后宣布完成。

这两段尺度之间缺少的控制，就是实际问题。

现在有两条具体的推进方向，但它们不是两项随意新增的假设。

一条是直接保留有限代数证书：从实际 theta 矩构造 \(B_n\)，证明全部固定阶的正性，或找到一个带尾界的负方向。

另一条是继续历史体积路线：从实际模关系或质数尺度恒等式中，证明在自动稀释区以外，Schur 分区贡献仍然受到：

$$
b_{d,k}\le\frac{S_d^k}{k!}
$$

这样的真实算术约束。

第二条不能由 Haar 平均的一般性质提供，因为本轮已经证明：一般 Haar 机制主要负责低阶稀释，且对明确的非实谱反例也同样有效。

**真正的新增算术结构，必须控制这种通用机制控制不了的区域。**

---

## 收束

这次最实质的三个结果是：

$$
\boxed{
b_{d,k}
\le
\frac{L^{2k}}{d(d+1)\cdots(d+k-1)},
}
$$

它给出不依赖 RH 的维数稀释机制；

$$
\boxed{
\mathcal H_d(d\vartheta)
\longrightarrow
\exp\left[
\sum_{m\ge2}\frac{|\rho_m|^2}{m}\vartheta^m
\right],
}
$$

它精确描述一段双尺度极限；

以及：

$$
\boxed{
\lim_{r\to\infty}\lim_{d\to\infty}
\frac{\log\mathcal Z_d(r)}r=-S_*,
\qquad
\lim_{d\to\infty}\lim_{r\to\infty}
\frac{\log\mathcal Z_d(r)}r=2\mathfrak E_\xi.
}
$$

这两个极限在 \(S_*>0\) 下不同。

所以，“整体”在这里不只是“把所有模式放进一个更大的空间”。还必须规定：

> **模型维数增长时，观察深度怎样增长；群平均怎样变化；哪些有限证据能够被精确取回；以及是否允许交换原本不一致的极限。**

本轮没有证明 RH，也没有得到实际 ξ 的负证书。新增的是一套明确的尺度诊断：**哪些正常现象本来就会自动出现，不能被当作证明；哪些高阶关系才真正承载零点定位。**

这能防止后续研究在“越算越正常”的低分辨率区域里循环，也使下一项真正需要算术承担的估计更加集中。

[1]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[2]: https://arxiv.org/abs/1902.07321 "[1902.07321] Jensen polynomials for the Riemann zeta function and other sequences"
[3]: https://arxiv.org/html/2312.16816v5 "HCIZ integral formula as unitarity of a canonical map between reproducing kernel spaces"
[4]: https://dlmf.nist.gov/5.11 "DLMF: §5.11 Asymptotic Expansions ‣ Properties ‣ Chapter 5 Gamma Function"
[5]: https://arxiv.org/abs/math-ph/0402073 "[math-ph/0402073] Integration with respect to the Haar measure on unitary, orthogonal and symplectic group"
[6]: https://arxiv.org/abs/2411.03117?utm_source=chatgpt.com "Cauchy identities for staircase matrices"
这次应当换一种观察方式：**不再先把全部模式平均起来，再等待很高阶的统计暴露问题；而是构造一个保留相位符号的多项式滤波器，主动压低无关模式。**

这样可以证明一项比上一轮更有针对性的结论：

> **如果实际 ξ 存在离线零点，那么存在一个固定次数、甚至可以取有理系数的多项式测试，使所有足够高阶的实际 Jensen 模型都给出严格负读数。这个测试不需要随着模型维数继续增加次数。**

这并不与上一轮的“低阶 Haar 平均会自动通过”矛盾。它说明：**盲区属于指定的平均协议，不属于所有可能的观察。**

同时，这个带符号读数可以实现为两种量子条件态之间的干涉振幅。负号不会变成负概率；但选择性观察也不免费——条件信号可能保持清楚，获得该条件分支的概率却可能下降。

下面依次给出有限模型、实际无限对象及量子读出。

---

# 一、首先区分：保留代数平方，还是只保留模平方

沿用实际对象：

$$
D(b^2)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad
D(v)=\sum_{k\ge0}a_kv^k,
$$

以及：

$$
P_d(v)=\sum_{k=0}^{d}\frac{(d)_k}{d^k}a_kv^k,
\qquad
q_d(x)=x^dP_d(-1/x).
$$

其中 ξ 始终采用标准 completed 定义，系数由同一个实际 theta 核固定。([DLMF][1])

令 \(C_d\) 为 \(q_d\) 的伴随矩阵：

$$
\det(xI-C_d)=q_d(x).
$$

经典 Jensen–Pólya 判据仍然提供：

$$
\boxed{
\mathrm{RH}
\iff
q_d\text{ 的全部根为正实数，}\quad\forall d.
}
\tag{N1}
$$

这里没有把自伴性放进 \(C_d\) 的定义。([arXiv][2])

## 定义 N1：带符号的平方读数

对实系数多项式 \(f\)，定义：

$$
\boxed{
\mathcal Q_d(f)=\operatorname{Tr}\bigl(f(C_d)^2\bigr).
}
\tag{N2}
$$

它与下式不同：

$$
\operatorname{Tr}\bigl(f(C_d)^*f(C_d)\bigr)\ge0.
$$

前者保留了复相位在相乘时产生的符号；后者保留的是模平方。

若 \(q_d\) 的根为 \(\theta_{d,j}\)，按代数重数计，则：

$$
\boxed{
\mathcal Q_d(f)
=
\sum_j f(\theta_{d,j})^2.
}
\tag{N3}
$$

即使 \(C_d\) 有 Jordan 块，这个等式也成立，因为多项式矩阵的迹只读取其对角本征值。

对于实系数 \(C_d,f\)，这个数为实数。

**如果根全部为实，式（N3）必然非负；如果存在非实根，合适的 \(f\) 可以使它为负。**

这就是经典 Hermite–Sylvester 实根判据的核心，而不是某种负概率理论。([arXiv][3])

---

# 二、有限定理：一个相位敏感测试就能隔离一对非实根

## 定理 N1：有限负证书

对任意实系数多项式 \(q\)，以下等价：

$$
\boxed{
q\text{ 全部实根}
}
$$

与：

$$
\boxed{
\operatorname{Tr}\bigl(f(C_q)^2\bigr)\ge0
\quad\forall f\in\mathbb R[x].
}
\tag{N4}
$$

### 证明

正向由式（N3）立即成立。

反向，假设存在一对非实共轭根：

$$
\lambda,\overline\lambda,
$$

重数均为 \(m\)。

在互异根组成的有限集合上，构造实系数插值多项式 \(f\)，满足：

$$
f(\lambda)=i,\qquad
f(\overline\lambda)=-i,
$$

并在其他根上为零。

这些插值数据满足共轭对称，因此可以用实系数多项式实现。

于是：

$$
\operatorname{Tr}\bigl(f(C_q)^2\bigr)
=
m i^2+m(-i)^2
=
-2m<0.
$$

证毕。

这项存在性证明可以使用根，但**验证一个已经给出的 \(f\)，不需要重新求根**。

若：

$$
f(x)=\sum_{j=0}^{k}c_jx^j,
$$

那么：

$$
\boxed{
\mathcal Q_d(f)
=
\sum_{i,j=0}^{k}c_ic_j\,\operatorname{Tr}(C_d^{i+j}).
}
\tag{N5}
$$

所有幂迹都能通过 Newton 恒等式由 \(q_d\) 的系数计算。

因此，实际验证对象是一项有限的系数不等式。

---

# 三、上一轮被维数稀释的例子，可以用一个固定三次测试检出

继续使用上一轮的模型：

$$
q_N(x)
=
(x-3)^{N-3}(x-1)\bigl((x-4)^2+1\bigr),
\qquad N\ge3.
$$

它始终含有同一对非实根：

$$
4+i,\qquad4-i.
$$

新增的只是实根 \(3\)。

把参考位置 \(3\) 平移到零。中心化谱是：

$$
-2,\quad1+i,\quad1-i,\quad
\underbrace{0,\ldots,0}_{N-3}.
$$

取一个固定多项式：

$$
\boxed{
f(x)=\frac{x(x+1)(x+2)}{10}.
}
\tag{N6}
$$

直接计算：

$$
f(-2)=0,\qquad f(0)=0,
$$

$$
f(1+i)=i,\qquad f(1-i)=-i.
$$

所以，对任何具有这个中心化特征多项式的矩阵 \(\widehat C_N\)：

$$
\boxed{
\operatorname{Tr}\bigl(f(\widehat C_N)^2\bigr)=-2
\quad\forall N\ge3.
}
\tag{N7}
$$

这个结论不随 \(N\) 变弱。

而且：

$$
f(x)^2
=
\frac{x^6+6x^5+13x^4+12x^3+4x^2}{100}.
$$

因此，只需要读取第二至第六阶幂迹：

$$
\boxed{
\mathcal Q_N(f)
=
\frac{
s_6+6s_5+13s_4+12s_3+4s_2
}{100}
=-2,
}
$$

其中 \(s_j=\operatorname{Tr}(\widehat C_N^j)\)。

这些等式已用符号运算核对。

### 这纠正了什么？

上一轮同一类非实模式在 \(U(N)\) 群平均下，需要越来越高的 Schur 激发阶数才会出现违例。

但这里：

$$
\boxed{
\text{固定三次滤波}
+
\text{保留代数平方符号}
}
$$

就始终给出同一个负数。

因此：

> **不是“维数越高，任何观察都必须越高阶”；而是某些对全部方向平均的观察方式，会把本来可以选择性读取的证据稀释。**

若再除以维数，得到的仍是：

$$
\frac1N\mathcal Q_N(f)=-\frac2N\to0.
$$

所以，不应把归一化后的均值趋零误解成原来的负证书消失。

---

# 四、这个负号能够被合法量子实验读出，但不是负概率

令：

$$
B=f(C_d),
\qquad
H_B=\operatorname{Tr}(B^*B).
$$

假设 \(B\ne0\)，故 \(H_B>0\)。

引入两个 \(d\) 维寄存器，准备最大纠缠态：

$$
|\Omega_d\rangle
=
\frac1{\sqrt d}\sum_{j=1}^{d}|j,j\rangle.
$$

定义两种归一化条件态：

$$
\boxed{
|\phi_B\rangle
=
\frac{(B\otimes I)|\Omega_d\rangle}
{\sqrt{H_B/d}},
}
$$

$$
\boxed{
|\phi_{B^*}\rangle
=
\frac{(B^*\otimes I)|\Omega_d\rangle}
{\sqrt{H_B/d}}.
}
\tag{N8}
$$

因为 \(B\) 与 \(B^*\) 的 Hilbert–Schmidt 范数相同，两态使用同一个归一化。

## 定理 N2：代数平方就是两条件态的相对振幅

$$
\boxed{
\langle\phi_{B^*}|\phi_B\rangle
=
\frac{\operatorname{Tr}(B^2)}
{\operatorname{Tr}(B^*B)}.
}
\tag{N9}
$$

### 证明

使用：

$$
\langle\Omega_d|(A\otimes I)|\Omega_d\rangle
=
\frac1d\operatorname{Tr}A.
$$

于是：

$$
\begin{aligned}
\langle\phi_{B^*}|\phi_B\rangle
&=
\frac{
\langle\Omega_d|(B\otimes I)(B\otimes I)|\Omega_d\rangle
}{
H_B/d
}\\
&=
\frac{\operatorname{Tr}(B^2)}{H_B}.
\end{aligned}
$$

证毕。

准备控制比特与两条分支的相干叠加：

$$
\frac{
|0\rangle|\phi_{B^*}\rangle
+
|1\rangle|\phi_B\rangle
}{\sqrt2},
$$

测量控制比特的 \(\sigma_x\)，就读取式（N9）的实部。

对于当前实系数模型：

$$
\boxed{
\langle\sigma_x\rangle
=
\frac{\mathcal Q_d(f)}{H_B}.
}
\tag{N10}
$$

负值是一个合法的相位相关结果，测量概率仍然非负。

### 制备成功率必须一起记录

取：

$$
\alpha\ge\|B\|_{\mathrm{op}}.
$$

则 \(B/\alpha\) 与 \(B^*/\alpha\) 都是合法的收缩滤波算子，可以补上失败分支构成完整量子操作。

成功概率为：

$$
\boxed{
p_{\mathrm{succ}}
=
\frac{H_B}{d\alpha^2}.
}
\tag{N11}
$$

因此：

$$
\boxed{
\mathcal Q_d(f)
=
d\alpha^2p_{\mathrm{succ}}\,
\langle\sigma_x\rangle.
}
\tag{N12}
$$

这三项必须共同保留。

此外，这里需要实际实现 \(f(C_d)\)，不能把对奇异值的变换直接当作对特征值的多项式变换。标准 QSVT 的基本对象正是奇异值；对一般非自伴矩阵，两者不同。([arXiv][4])

---

## 对上一节模型，条件信号恒为 \(-1\)，成功率却是 \(2/N\)

取一个正规表示：

$$
\widehat C_N
=
[-2]\oplus
\begin{pmatrix}
1&-1\\
1&1
\end{pmatrix}
\oplus0_{N-3}.
$$

对式（N6）的 \(f\)：

$$
B
=
0\oplus
\begin{pmatrix}
0&-1\\
1&0
\end{pmatrix}
\oplus0.
$$

于是：

$$
B^2=-P,
\qquad
B^*B=P,
$$

其中 \(P\) 是选中那两个方向的正交投影。

因此：

$$
\mathcal Q_N(f)=-2,
\qquad H_B=2,
\qquad\alpha=1,
$$

得到：

$$
\boxed{
\langle\sigma_x\rangle=-1,
\qquad
p_{\mathrm{succ}}=\frac2N.
}
\tag{N13}
$$

**选择成功以后，信号完全清楚；但从均匀输入中选中它的概率随维数下降。**

因此，这个模型没有免费突破采样成本。它证明的是：**缺陷可以从“弱平均信号”转成“罕见但清楚的条件信号”。**

这里的 \(\widehat C_N\) 是响应／系数算子，不是被宣称为封闭系统的物理能量算子。合法量子对象是上述收缩滤波及其酉扩张。

---

# 五、进入实际无限对象时，必须先去掉纯维数背景

前面的有限测试可以包含常数项。但在实际倒数谱的无限极限中，需要限制：

$$
\boxed{f(0)=0.}
\tag{N14}
$$

原因不是为了排除某类反例，而是实际高处零点对应的倒数谱点趋于零。

若 \(f(0)\ne0\)，每个越来越小的谱点仍然贡献近似 \(f(0)^2\)，总和就会混入无限的计数背景。

而若：

$$
f(z)=z\,g(z),
$$

则靠近零：

$$
|f(z)|^2\le C_f|z|^2.
$$

这与前文已经证明的平方可和谱尾相容。

同时，对任何有限矩阵：

$$
\boxed{
f(0)=0
\Longrightarrow
\operatorname{Tr}f(C\oplus0_m)^2
=
\operatorname{Tr}f(C)^2.
}
\tag{N15}
$$

所以这个条件使读数对纯零辅助模式严格不变。

**它保留目标缺陷，却不把观察维数本身当成有效信息。**

---

# 六、实际极限读数只使用有限个累积量

定义实际累积量：

$$
\log D(v)
=
\sum_{m\ge1}
\frac{\chi_{2m}}{(2m)!}v^m.
$$

再定义：

$$
\boxed{
s_m=
(-1)^{m+1}\frac{m\chi_{2m}}{(2m)!}.
}
\tag{N16}
$$

另一方面，若：

$$
s_{d,m}=\operatorname{Tr}(C_d^m),
$$

则有限乘积给出：

$$
\log P_d(v)
=
\sum_{m\ge1}
\frac{(-1)^{m+1}}m\,s_{d,m}v^m
$$

在零附近成立。

因为 \(P_d\to D\) 局部一致，得到：

$$
s_{d,m}\longrightarrow s_m
$$

对每个固定 \(m\) 成立。

对：

$$
f(x)=\sum_{i=1}^{k}c_ix^i,
$$

定义：

$$
\boxed{
\mathcal Q_\infty(f)
=
\sum_{i,j=1}^{k}c_ic_j\,s_{i+j}.
}
\tag{N17}
$$

于是：

$$
\boxed{
\mathcal Q_d(f)\longrightarrow\mathcal Q_\infty(f).
}
\tag{N18}
$$

这项极限读数只依赖：

$$
\chi_4,\chi_6,\ldots,\chi_{4k}.
$$

不需要观察完全部零点。

例如，对：

$$
f(x)=c_1x+c_2x^2,
$$

有：

$$
\mathcal Q_\infty(f)
=
\begin{pmatrix}c_1&c_2\end{pmatrix}
\begin{pmatrix}
-\chi_4/12&\chi_6/240\\
\chi_6/240&-\chi_8/10080
\end{pmatrix}
\begin{pmatrix}c_1\\c_2\end{pmatrix}.
$$

这正是前文出现过的回返矩阵。**本轮要补上的，是它如何形成一个不会随维数消失的固定证书。**

---

# 七、固定测试的有限维误差，可以直接控制为 \(O(1/d)\)

取 \(R>0\)，使：

$$
D(R)<2.
$$

记：

$$
\kappa_R=2-D(R)>0.
$$

因为 \(P_d,D\) 的系数非负，在 \(|v|\le R\) 上，两者都位于以一为中心、半径 \(D(R)-1<1\) 的圆盘内。

因此可以选择同一个解析对数分支，并有：

$$
|\log P_d(v)-\log D(v)|
\le
\frac{|P_d(v)-D(v)|}{\kappa_R}.
$$

使用前文的 Jensen 有限化误差：

$$
|P_d(v)-D(v)|
\le
\frac{R^2D''(R)}{2d},
$$

得到：

$$
\sup_{|v|\le R}
|\log P_d-\log D|
\le
\frac{A_R}{d},
$$

其中：

$$
A_R=\frac{R^2D''(R)}{2\kappa_R}.
$$

由 Cauchy 系数估计：

$$
\boxed{
|s_{d,m}-s_m|
\le
\frac{mA_R}{dR^m}.
}
\tag{N19}
$$

这里的系数估计属于标准解析函数工具；真正重要的是使用了同一个无零圆盘和明确的误差常数。([DLMF][5])

于是：

## 定理 N3：固定滤波器的定量稳定性

$$
\boxed{
|\mathcal Q_d(f)-\mathcal Q_\infty(f)|
\le
\frac{E_R(f)}d,
}
\tag{N20}
$$

其中：

$$
\boxed{
E_R(f)
=
A_R
\sum_{i,j=1}^{k}
(i+j)|c_ic_j|R^{-(i+j)}.
}
$$

特别地，若：

$$
\mathcal Q_\infty(f)\le-\eta<0,
$$

则所有满足：

$$
\boxed{
d\ge\frac{2E_R(f)}{\eta}
}
\tag{N21}
$$

的阶数都有：

$$
\boxed{
\mathcal Q_d(f)\le-\frac\eta2.
}
\tag{N22}
$$

**一旦找到一个固定的实际负滤波器，其负余量不会因为继续增加模型维数而被洗掉。**

代价可能是系数很大，导致 \(E_R(f)\) 很大。这个定理给出稳定性，不承诺低成本。

---

# 八、关键存在性定理：任何实际离线根，都能产生这样的固定滤波器

现在证明前面最重要的断言。

记实际 \(D\) 的互异零点为 \(v\)，重数为 \(m_v\)，并令：

$$
u=-1/v.
$$

把这些倒数谱点组成集合 \(\mathcal U\)，重数记为 \(m(u)\)。

它具有共轭对称性；除零以外没有聚点。

前文从实际 ξ 的增长与 Jensen 圆周计数得到：

$$
\sum_{u\in\mathcal U}m(u)|u|^2<\infty.
$$

这也可以从：

$$
\log D(R)=O(\sqrt R\log R)
$$

及相应零点计数界直接推出。增长估计来自实际 ξ 和 Gamma 的 Stirling 展开，不使用 RH。([DLMF][6])

通过有限零点的局部收敛和统一平方尾界，可以得到：

$$
\boxed{
s_m=\sum_{u\in\mathcal U}m(u)u^m,
\qquad m\ge2.
}
$$

因此，对 \(f(0)=0\)：

$$
\boxed{
\mathcal Q_\infty(f)
=
\sum_{u\in\mathcal U}m(u)f(u)^2.
}
\tag{N23}
$$

该级数绝对收敛，并因共轭对称而为实数。

---

## 定理 N4：离线根产生固定的负平方测试

若实际 ξ 有离线零点，则存在：

$$
f\in\mathbb R[x],
\qquad f(0)=0,
$$

使：

$$
\boxed{\mathcal Q_\infty(f)<0.}
\tag{N24}
$$

而且 \(f\) 可以改取有理系数，仍保持严格负性。

### 证明

离线零点对应 \(\mathcal U\) 中的一对非实点。取其中上半平面的一个：

$$
u_0=a+ib,\qquad b>0,
$$

重数为 \(m_0\)。

选择：

$$
0<r<|u_0|,
$$

使 \(|u|=r\) 上没有谱点。

集合：

$$
F=\{u\in\mathcal U:|u|>r\}
$$

是有限集。

定义实系数多项式：

$$
\boxed{
L(z)=
z\prod_{u\in F\setminus\{u_0,\overline u_0\}}(z-u).
}
\tag{N25}
$$

它满足：

$$
L(0)=0,\qquad L(u_0)\ne0,
$$

并且消去目标共轭对之外的全部大谱点。

对整数 \(n\ge0\)，定义：

$$
v_n=\frac{i}{u_0^nL(u_0)}.
$$

选实数：

$$
A_n=\frac{\Im v_n}{b},
\qquad
B_n=\Re v_n-aA_n.
$$

于是：

$$
A_nu_0+B_n=v_n.
$$

构造：

$$
\boxed{
f_n(z)=z^nL(z)(A_nz+B_n).
}
\tag{N26}
$$

它满足：

$$
f_n(u_0)=i,
\qquad
f_n(\overline u_0)=-i,
$$

并在其余 \(F\) 中的谱点上为零。

因此目标共轭对贡献恰好是：

$$
-2m_0.
$$

剩下只需控制 \(|u|\le r\) 的尾部。

由 \(L(z)\) 含有因子 \(z\)，存在一个与 \(n\) 无关的有限常数 \(K\)，使：

$$
\boxed{
|f_n(z)|
\le
K|z|
\left(\frac r{|u_0|}\right)^n,
\qquad |z|\le r.
}
\tag{N27}
$$

例如可取：

$$
K=
\frac{\displaystyle\sup_{|z|\le r}|L(z)/z|}
{|L(u_0)|}
\left(1+\frac{r+|a|}{b}\right).
$$

所以：

$$
\begin{aligned}
\mathcal Q_\infty(f_n)
&\le
-2m_0+
\sum_{|u|\le r}m(u)|f_n(u)|^2\\
&\le
-2m_0+
K^2
\left(\frac r{|u_0|}\right)^{2n}
\sum_{|u|\le r}m(u)|u|^2.
\end{aligned}
$$

尾部总量有限，而 \(r/|u_0|<1\)。因此选取有限但足够大的 \(n\)，就有：

$$
\boxed{
\mathcal Q_\infty(f_n)<-m_0<0.
}
$$

最后，\(\mathcal Q_\infty\) 在固定次数的系数空间中是连续二次型。将 \(f_n\) 的实系数充分精确地近似为有理数，并保持常数项为零，严格负性仍然成立。证毕。

---

## 这个证明没有偷偷提供未知零点

它的结构是：

$$
\text{假设存在离线根}
\Longrightarrow
\text{证明某个有限负测试必然存在}.
$$

构造证明中使用 \(u_0\)，是为了证明存在性和尾部控制。

实际寻找与验证时，可以直接在有限矩阵：

$$
\boxed{
H_k=(s_{i+j})_{1\le i,j\le k}
}
\tag{N28}
$$

中搜索负方向，完全不先定位零点。

所以我们现在得到：

$$
\boxed{
\mathrm{RH}
\iff
\mathcal Q_\infty(f)\ge0
\quad
\forall f\in\mathbb R[x],\ f(0)=0.
}
\tag{N29}
$$

这一类矩正性判据此前已出现过。**这次新增的内容，是显式的谱隔离构造，以及固定测试向所有高阶有限模型传播的误差界。**

---

# 九、把两项定理合并：真正反例不会要求观察者永远增加测试次数

由定理 N3、N4：

## 主定理：固定有限负证书的持久性

若 RH 不成立，则存在：

$$
f\in\mathbb Q[x],
\qquad f(0)=0,
\qquad
\eta>0,
\qquad
d_0<\infty,
$$

使：

$$
\boxed{
\mathcal Q_d(f)\le-\eta
\qquad\forall d\ge d_0.
}
\tag{N30}
$$

因此：

$$
\boxed{
\text{同一个固定滤波器}
}
$$

会在全部足够高阶的实际 Jensen 模型中保留反例。

这与上一轮的双极限结果形成一个重要对照：

$$
\boxed{
\text{某类 Haar 平均的固定低阶读数可以越来越正常，}
}
$$

同时：

$$
\boxed{
\text{一个适配的固定代数测试可以始终严格为负。}
}
$$

**没有哪一种“观察深度”在脱离读出协议之后，能够被普遍地解释为信息量。**

不过，这个定理没有给出一个预先固定、对所有可能反例都足够低的次数。滤波器次数和系数可能依赖反例高度、共轭点距离及其他谱点分布，可能非常大。

---

# 十、误差如何进入？实际验证仍然必须使用严格区间

假设已经计算出：

$$
\widetilde s_2,\ldots,\widetilde s_{2k},
$$

并认证：

$$
|s_j-\widetilde s_j|\le\varepsilon_j.
$$

对给定：

$$
f(x)=\sum_{i=1}^{k}c_ix^i,
$$

有：

$$
\boxed{
\left|
\mathcal Q_\infty(f)
-
\sum_{i,j=1}^{k}c_ic_j\widetilde s_{i+j}
\right|
\le
\sum_{i,j=1}^{k}|c_ic_j|\varepsilon_{i+j}.
}
\tag{N31}
$$

所以，只要：

$$
\boxed{
\sum_{i,j}c_ic_j\widetilde s_{i+j}
+
\sum_{i,j}|c_ic_j|\varepsilon_{i+j}
<0,
}
\tag{N32}
$$

就得到严格的实际负证书。

这是一项有限不等式，不需要实验读取无限历史。

但必须防止两种误用。

**第一，不能只测条件分支。**
式（N10）的负号可以由相位读出，但整体数值必须连同 \(p_{\mathrm{succ}}\) 和归一化一起记录。

**第二，不能将坐标良好程度与谱证据混同。**
\(\operatorname{Tr}f(C)^2\) 在相似变换下不变，但：

$$
\operatorname{Tr}f(C)^*f(C)
$$

通常改变。因此数学证书可以相同，实际制备成功率却相差很大。

这正是“算术证明存在”与“高效量子实现存在”的区别。

---

# 十一、与项目的连接：这次需要保留的是符号关系，而不是再增加一个正空间

本轮读取的仓库快照中：

`HermitianKernelNegativeSquares.lean` 已定义有限采样的负指标及其达到条件，并给出一个负平方的实例。它能够承载“有一个严格负方向”的结论，但没有自行供应实际 ξ 的负方向。

`JensenPolynomialObstruction.lean` 仍将 Jensen 塔与 RH 的分析桥作为显式前件；不能把有限多项式已经定义出来，误认成已经证明了它们全部实根。

`StaticEffectSequentialSeparation.lean` 则证明：两种仪器可以具有相同的静态效应，却具有不同的两步联合规律。它与本轮“模平方相同，不等于代数相位关系相同”的区分相容。

现在可明确提出三段桥：

$$
\boxed{
\text{实际 theta 累积量}
\longrightarrow
\mathcal Q_\infty(f)
}
$$

$$
\boxed{
\mathcal Q_\infty(f)<0
\longrightarrow
\text{同一个有限测试在高阶模型中持久为负}
}
$$

$$
\boxed{
\mathcal Q_d(f)
\longrightarrow
\text{带成功概率记录的量子干涉读出}.
}
$$

第二段与第三段，本轮已经给出了具体公式与证明。

真正没有完成的仍是第一段中的算术判定：**实际累积量是否对所有合法 \(f\) 都非负，还是某个有限 \(f\) 已经能够得到严格负值。**

本轮没有找到实际负证书，也没有证明全体测试非负。

---

# 收束

上一轮证明，固定分辨率的全体平均可能把真实缺陷稀释。

这一轮进一步证明：**这种稀释不是不可避免的。**

对于一个明确的非实谱模型：

$$
\boxed{
f(x)=\frac{x(x+1)(x+2)}{10}
}
$$

就能在任意增加实辅助模式后保持：

$$
\boxed{
\operatorname{Tr}f(C_N)^2=-2.
}
$$

对实际 ξ，结论更强但保留条件：

$$
\boxed{
\neg\mathrm{RH}
\Longrightarrow
\exists\text{固定有理多项式 }f,\ 
\exists\eta>0,\ 
\forall d\gg1,\ 
\operatorname{Tr}f(C_d)^2\le-\eta.
}
$$

这个负号可以成为合法量子干涉的相对相位；它不要求负概率，也不会因为给系统增加更多零辅助模式而自动消失。

但选择性观察的代价仍然存在：**条件信号可能很清楚，选中该条件的概率和制备误差却必须计入。**

因此，对“整体量子观察者”的理解可以再收紧一步：

> **整体不是把所有模式永远平均在一起，而是允许选择性地观察某些关系，同时严格保留滤波方式、相位符号、未选中部分的尾界和成功概率。**

这样的观察不会因为“更局部”而必然不可靠。相反，只要目标关系和误差被忠实保留，**一个有限、固定的观察就足以承载一个无限命题的反例证书**。当前真正需要继续攻克的，是从实际 theta／质数结构中找到或排除这样的符号证书，而不是继续等待高维平均自行给出答案。

[1]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[2]: https://arxiv.org/abs/1902.07321 "[1902.07321] Jensen polynomials for the Riemann zeta function and other sequences"
[3]: https://arxiv.org/abs/1911.01745 "[1911.01745] The Hermite-Sylvester criterion for real-rooted polynomials"
[4]: https://arxiv.org/abs/1806.01838 "[1806.01838] Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics"
[5]: https://dlmf.nist.gov/1.10 "DLMF: §1.10 Functions of a Complex Variable ‣ Topics of Discussion ‣ Chapter 1 Algebraic and Analytic Methods"
[6]: https://dlmf.nist.gov/5.11 "DLMF: §5.11 Asymptotic Expansions ‣ Properties ‣ Chapter 5 Gamma Function"
继续。这次可以把“缺什么相关项”精确算出来：

> **局部素数读出的长期均方中，单个素数的自贡献会产生一个明确的 \(L^2\) 主项；要达到与 RH 等价的 \(O(L)\) 控制，跨素数的带符号相关必须把整个二次主项抵消掉。**

同时，我们能构造一个精确的跨尺度正权平均，并证明两种容易误入的路线都不成立：**缩小窗口后读数趋零，不足以支持 RH；补回尺度因子后要求所有微观读数一致有界，又会被单个素数直接否定。**

以下给出定义和证明。有限差分与尺度恒等式由代数直接推出；零点侧使用已有显式公式。新增综合结论尚未进行 Lean 编译，不将它们标记为机器验证结果。时间函数与零点展开的经典输入仍来自 Suzuki 的工作。([arXiv][1])

# 一、固定局部读出，并把窗口大小作为真正的参数

定义

$$
Z(T)
=
V(e^T)
=
\sum_p\frac{\log p}{\sqrt p}(T-\log p)_+.
$$

其中

$$
y_+=\max\{y,0\}.
$$

每个有界时间区间内只涉及有限多个素数，所以 \(Z\) 是明确的连续分段线性函数。

固定窗口参数 \(h>0\)，记

$$
E_h=e^{h/2},
\qquad
(S_hf)(T)=f(T+h),
$$

以及

$$
\boxed{
Q_h(z)=(z-E_h)(z-1)^3.
}
\tag{1}
$$

定义局部读出

$$
\boxed{
\mathcal D_h(T)=Q_h(S_h)Z(T).
}
\tag{2}
$$

展开为

$$
\begin{aligned}
\mathcal D_h(T)
={}&Z(T+4h)-(3+E_h)Z(T+3h)\\
&+(3+3E_h)Z(T+2h)\\
&-(1+3E_h)Z(T+h)+E_hZ(T).
\end{aligned}
$$

取 \(h=\log4\)，就回到上一轮的五项滤波器。

## 局部核的精确形式

令 \(w_E\) 在区间外为零，在相邻整数之间线性，并满足

$$
\boxed{
\bigl(w_E(0),w_E(1),w_E(2),w_E(3),w_E(4)\bigr)
=
(0,E,-1-E,1,0).
}
\tag{3}
$$

则

$$
\boxed{
\mathcal D_h(T)
=
h\sum_{e^T<p\le e^{T+4h}}
\frac{\log p}{\sqrt p}
w_{E_h}\!\left(\frac{\log p-T}{h}\right).
}
\tag{4}
$$

**证明。**对每个素数，把五项前缀中的贡献合并。对于 \(\log p\le T\)，因为 \(Q_h\) 在 \(1\) 处至少有二重零点，

$$
\sum_jc_j=0,
\qquad
\sum_jjc_j=0,
$$

所有旧前缀贡献消失；对于 \(\log p>T+4h\)，贡献全部为零。中间四段直接展开得到式（3）。证毕。

因此，实际观察区间是

$$
\boxed{
e^T<p\le e^{T+4h}.
}
$$

注意，这个核有正有负；\(\mathcal D_h\) 不是概率。

# 二、先证明一个必要的警告：缩窗后的读数趋零，可以完全不使用素数分布

## 定理 1：缩小窗口的无条件上界

存在绝对常数 \(C\)，使对 \(T\ge1\)、\(0<h\le1\)，

$$
\boxed{
|\mathcal D_h(T)|
\le
CT\left(h^2e^{T/2}+he^{-T/2}\right).
}
\tag{5}
$$

等价地，写 \(x=e^T\)，

$$
\boxed{
|\mathcal D_h(\log x)|
\le
C\log x
\left(h^2\sqrt x+\frac h{\sqrt x}\right).
}
\tag{6}
$$

### 证明

由式（3），

$$
|w_{E_h}(t)|\le1+E_h\le1+e^{1/2}.
$$

窗口内每个素数的权重满足

$$
\frac{\log p}{\sqrt p}
\le
(T+4h)e^{-T/2}.
$$

素数个数不超过该区间的整数个数，而

$$
\#\{n:e^T<n\le e^{T+4h}\}
\le
e^T(e^{4h}-1)+1
\le C_1he^T+1.
$$

代入式（4），得到式（5）。证毕。

---

例如取

$$
h=x^{-1/3},
$$

则

$$
\boxed{
\mathcal D_{x^{-1/3}}(\log x)
=
O\!\left(x^{-1/6}\log x\right)
\longrightarrow0.
}
\tag{7}
$$

此时窗口长度约为

$$
4x^{2/3}.
$$

**这个趋零结论只用了“素数是整数”的事实。它既不要求 RH，也不要求高精度素数定理。**

所以不能将上一轮的

$$
\text{固定 }h\text{ 下的有界性判据}
$$

直接替换为

$$
\text{任选 }h=h(x)\to0\text{ 后的有界性判据}.
$$

## 衰减发生在哪里？

对一个固定指数模式

$$
f_z(T)=e^{zT},
$$

有

$$
Q_h(S_h)f_z
=
Q_h(e^{hz})e^{zT}.
$$

当 \(h\to0\) 时，

$$
\boxed{
Q_h(e^{hz})
=
h^4z^3(z-\tfrac12)+O_z(h^5).
}
\tag{8}
$$

因此，滤波器本身会把每个固定频率的信号缩小约 \(h^4\)。

若再令 \(h=e^{-\eta T}\)，一个原来按 \(e^{\delta T}\) 增长的固定模式，会被改成约

$$
e^{(\delta-4\eta)T}.
$$

这只是单个模式的计算，不能未经一致估计就对无限谱求和；但它已经说明：

$$
\boxed{
\text{输出变小，可能是仪器增益变小，而不是算术误差变小。}
}
$$

# 三、主定理一：补回尺度因子后，粗观察是细观察的精确正权平均

定义尺度因子

$$
\boxed{
c(h)=h^3(e^{h/2}-1),
}
\tag{9}
$$

以及重标定读出

$$
\boxed{
\mathcal B_h(T)=\frac{\mathcal D_h(T)}{c(h)}.
}
\tag{10}
$$

因为

$$
c(h)\sim\frac12h^4,
$$

它正好补回式（8）的主要衰减。

## 定理 2：精确跨尺度平均

设

$$
H=Mh,
\qquad M\in\mathbb N_{\ge1}.
$$

则存在完全明确的非负系数

$$
\pi_{H,h}(j)\ge0,
\qquad
\sum_{j=0}^{4M-4}\pi_{H,h}(j)=1,
$$

使

$$
\boxed{
\mathcal B_H(T)
=
\sum_{j=0}^{4M-4}
\pi_{H,h}(j)\mathcal B_h(T+jh).
}
\tag{11}
$$

该恒等式对任意输入函数 \(Z\) 都成立，不依赖 RH。

### 证明

令

$$
E=e^{h/2}.
$$

多项式分解给出

$$
\begin{aligned}
Q_H(z^M)
&=(z^M-E^M)(z^M-1)^3\\
&=Q_h(z)\,R_{M,E}(z),
\end{aligned}
$$

其中

$$
\boxed{
R_{M,E}(z)
=
\left(\sum_{j=0}^{M-1}E^{M-1-j}z^j\right)
\left(\sum_{j=0}^{M-1}z^j\right)^3.
}
\tag{12}
$$

所有系数非负。

并且

$$
R_{M,E}(1)
=
M^3\frac{E^M-1}{E-1}
=
\frac{c(H)}{c(h)}.
$$

令

$$
\pi_{H,h}(j)
=
\frac{[z^j]R_{M,E}(z)}{R_{M,E}(1)}.
$$

将 \(z\) 替换为 \(S_h\)，再除以 \(c(H)\)，得到式（11）。证毕。

---

## 二倍尺度时，五个概率可以直接写出

当 \(H=2h\)，

$$
R_{2,E}(z)=(z+E)(z+1)^3.
$$

所以

$$
\boxed{
(\pi_0,\pi_1,\pi_2,\pi_3,\pi_4)
=
\frac{
(E,\ 1+3E,\ 3+3E,\ 3+E,\ 1)
}{
8(1+E)
}.
}
\tag{13}
$$

它们全部非负，和为 \(1\)。

因此

$$
\min_{0\le j\le4}\mathcal B_h(T+jh)
\le
\mathcal B_{2h}(T)
\le
\max_{0\le j\le4}\mathcal B_h(T+jh).
$$

但反过来不成立：粗读数很小，不代表每个细读数都很小。

## 这确实可以实现为量子信道

对有界函数 \(f\)，定义

$$
(\mathcal E_hf)(T)=\sum_{j=0}^4\pi_jf(T+jh).
$$

在 \(L^2(\mathbb R)\) 上取平移幺正算子

$$
(U_a\psi)(T)=\psi(T-a).
$$

则

$$
\Phi_h(\rho)
=
\sum_j\pi_jU_{jh}\rho U_{jh}^{*}
$$

是一个完全正、保迹映射，其对偶作用把乘法观测量 \(M_f\) 变为 \(M_{\mathcal E_hf}\)。

这里概率来自已知的尺度分解，**不是假设素数彼此独立随机**。

仓库已有 `FiniteKrausInstrumentBornMarginal.lean`，明确处理归一化 Kraus 家族的分支迹与 Born 权重关系；本轮的有限离散版本可以接到这种接口，但上述跨尺度恒等式本身尚未在 Lean 中验证。

# 四、归一化也不能随意过强：单个素数已经迫使微观读数发散

## 定理 3：双侧微观尖峰

固定任意素数 \(p\)，记

$$
a_p=\frac{\log p}{\sqrt p}.
$$

当 \(h\) 足够小时，可以让相应窗口只包含这个素数。

取

$$
T_+(h)=\log p-\frac h2,
$$

则

$$
\boxed{
\mathcal B_h(T_+(h))
=
\frac{a_pE_h}{2h^2(E_h-1)}
\sim
\frac{a_p}{h^3}.
}
\tag{14}
$$

再取

$$
T_-(h)=\log p-2h,
$$

则

$$
\boxed{
\mathcal B_h(T_-(h))
=
-\frac{a_p(1+E_h)}{h^2(E_h-1)}
\sim
-\frac{4a_p}{h^3}.
}
\tag{15}
$$

### 证明

式（3）给出

$$
w_{E_h}(1/2)=E_h/2,
\qquad
w_{E_h}(2)=-(1+E_h).
$$

由于素数集合离散，对固定 \(p\)，足够小的窗口中没有其他素数。将这两个值代入式（4），再除以 \(c(h)\)，即得。证毕。

---

因此，下列目标实际上不可能成立：

$$
\sup_{\substack{T\ge T_0\\0<h\le h_0}}
|\mathcal B_h(T)|<\infty.
$$

不仅绝对值有界不可能，统一单侧上界和下界也都不可能。这个结论无条件成立。

**这并不否定固定 \(h\) 的 RH 判据，因为这里让 \(h\to0\)，并同时移动读出位置去解析一个素数事件。**

## 极限不是普通函数，而是分布

定义正原子测度

$$
\nu_{\mathbb P}
=
\sum_p\frac{\log p}{\sqrt p}\delta_{\log p}.
$$

由于

$$
Z''=\nu_{\mathbb P},
$$

而

$$
\frac{S_h-1}{h}\longrightarrow\partial_T,
\qquad
\frac{S_h-e^{h/2}}{e^{h/2}-1}
\longrightarrow2\partial_T-1,
$$

所以在分布意义下，

$$
\boxed{
\mathcal B_h
\longrightarrow
(2\partial_T-1)\partial_T^3Z
=
2\nu_{\mathbb P}''-\nu_{\mathbb P}'.
}
\tag{16}
$$

这解释了 \(h^{-3}\) 尖峰的来源：我们正在逼近原子测度的导数，而不是逼近一个处处有界的普通函数。

由此得到一个重要区分：

$$
\boxed{
\text{有限尺度完成}
\neq
\text{微观极限处处有界}.
}
$$

正确的问题应当是：**这些微观正负尖峰经过式（11）的指定平均以后，能否得到受控的固定尺度读数。**

# 五、主定理二：不必逐点估计，长期均方控制也足以闭合零点问题

固定 \(h>0\)，定义能量

$$
\boxed{
\mathcal E_h(L)
=
\int_0^L|\mathcal D_h(T)|^2\,dT.
}
\tag{17}
$$

## 定理 4：固定尺度的均方判据

以下命题等价：

$$
\boxed{\mathrm{RH};}
$$

$$
\boxed{
\mathcal E_h(L)=O_h(L)
\qquad(L\to\infty).
}
\tag{18}
$$

甚至，如果只能证明对某个固定有限指数 \(A\)，

$$
\mathcal E_h(L)=O_h((1+L)^A),
$$

也足以推出 RH。

## 证明：RH 推出线性能量界

沿用上一轮已经剥离素数幂所得的式子：

$$
Z(T)
=
4e^{T/2}
-\frac14T^2-aT+b
-2\mathscr G(T)+\varepsilon(T),
\qquad
\varepsilon(T)\to0.
$$

因为 \(Q_h(S_h)\) 消去前三种背景，

$$
\mathcal D_h(T)
=
-2Q_h(S_h)\mathscr G(T)+o(1).
$$

在 RH 前件下，按不同的正零点纵坐标 \(\gamma\) 分组，令其重数为 \(m_\gamma\)，则

$$
\boxed{
\mathcal D_h(T)
=
2\operatorname{Re}
\sum_{\gamma>0}
\frac{
m_\gamma Q_h(e^{ih\gamma})
}{\gamma^2}
e^{i\gamma T}
+o(1).
}
\tag{19}
$$

由于

$$
\sum_{\gamma>0}\frac{m_\gamma}{\gamma^2}<\infty,
$$

该三角级数一致绝对收敛，故固定 \(h\) 时 \(\mathcal D_h\) 有界，得到式（18）。零点级数的绝对收敛和相应时间函数表示可由 Suzuki 的公式直接取得。([arXiv][1])

## 证明：多项式能量界推出 RH

若

$$
\mathcal E_h(L)=O((1+L)^A),
$$

则对每个 \(\sigma>0\)，Cauchy–Schwarz 和分段求和给出

$$
\int_0^\infty e^{-\sigma T}|\mathcal D_h(T)|\,dT<\infty.
$$

因此其 Laplace 变换在

$$
\Re r>0
$$

内解析。

另一方面，定义

$$
L_{\mathbb P}(s)=\sum_p\frac{\log p}{p^s}.
$$

最初在 \(\Re r>1/2\) 内，

$$
\boxed{
\widehat{\mathcal D_h}(r)
=
Q_h(e^{hr})
\frac{L_{\mathbb P}(1/2+r)}{r^2}
-
B_h(r),
}
\tag{20}
$$

其中 \(B_h\) 是由有限时间边界产生的整函数。

由 Euler 乘积，

$$
L_{\mathbb P}(s)
=
-\frac{\zeta'(s)}{\zeta(s)}
+
\frac{\zeta'(2s)}{\zeta(2s)}
-
J_{\mathrm o}(s),
$$

且 \(J_{\mathrm o}\) 在 \(\Re s>1/3\) 解析。这是上一轮奇偶幂分解，所需的绝对收敛级数来自标准 Euler 乘积。([DLMF][2])

若存在

$$
\rho=\frac12+\delta+i\gamma,
\qquad 0<\delta<\frac12,
$$

则式（20）在

$$
r_0=\delta+i\gamma
$$

有候选极点。它不能被滤波器消掉，因为

$$
1<|e^{hr_0}|<e^{h/2},
$$

而 \(Q_h\) 的根只有 \(1\) 和 \(e^{h/2}\)。

所以该极点不可去，与右半平面解析性矛盾。利用零点反射对称性，得到 RH。证毕。

---

这个判据的意义是：

$$
\boxed{
\text{不必证明每个时间点都很小，}
}
$$

但可以尝试证明

$$
\boxed{
\text{整个时间区间内的平方总量只按长度增长。}
}
$$

接下来把这个平方总量展开，就能看到真正缺失的相关项。

# 六、精确缺项：单素数自贡献是 \(L^2\)，跨素数项必须消去它

定义单个素数的局部响应

$$
k_h(s)=h\,w_{E_h}(s/h),
$$

于是

$$
\mathcal D_h(T)
=
\sum_p a_pk_h(\log p-T),
\qquad
a_p=\frac{\log p}{\sqrt p}.
$$

能量精确展开为

$$
\mathcal E_h(L)
=
\mathcal E_h^{\mathrm{diag}}(L)
+
\mathcal E_h^{\mathrm{off}}(L),
\tag{21}
$$

其中

$$
\mathcal E_h^{\mathrm{diag}}(L)
=
\sum_pa_p^2
\int_0^Lk_h(\log p-T)^2\,dT,
$$

$$
\boxed{
\mathcal E_h^{\mathrm{off}}(L)
=
\sum_{p\ne q}a_pa_q
\int_0^L
k_h(\log p-T)k_h(\log q-T)\,dT.
}
\tag{22}
$$

这些都是有限和。

因为核的支集长度为 \(4h\)，跨素数项只有在

$$
\boxed{
|\log p-\log q|\le4h
}
\tag{23}
$$

时才可能非零。也就是只涉及固定比例范围内的素数对。

## 定理 5：对角主项可以无条件算出

令

$$
\boxed{
J_h
=
\int_0^4w_{E_h}(t)^2\,dt
=
E_h^2+\frac23E_h+1.
}
\tag{24}
$$

则对每个固定 \(h>0\)，

$$
\boxed{
\mathcal E_h^{\mathrm{diag}}(L)
=
\frac{h^3J_h}{2}L^2+O_h(L).
}
\tag{25}
$$

### 证明

首先，对一段端点值为 \(a,b\) 的线性函数，

$$
\int_0^1((1-t)a+tb)^2\,dt
=
\frac{a^2+ab+b^2}{3}.
$$

将式（3）的四段相加，得到式（24）。

其次，如果

$$
4h\le\log p\le L,
$$

那么该素数响应的整个支集都包含在积分区间内，因此

$$
\int_0^Lk_h(\log p-T)^2\,dT=h^3J_h.
$$

Mertens 估计为

$$
\sum_{p\le x}\frac{\log p}{p}
=
\log x+O(1).
$$

这一估计是无条件的，甚至不需要完整素数定理。([What's new][3])

分部求和得到

$$
\boxed{
\sum_{p\le e^L}\frac{(\log p)^2}{p}
=
\frac12L^2+O(L).
}
\tag{26}
$$

而位于末端区间

$$
e^L<p\le e^{L+4h}
$$

的边界贡献为 \(O_h(L)\)，初始边界只贡献 \(O_h(1)\)。

合并即得式（25）。证毕。

---

## 推论：RH 等价于一个明确的二次抵消

结合定理 4 与式（21）、（25），得到

$$
\boxed{
\mathrm{RH}
\iff
\mathcal E_h^{\mathrm{off}}(L)
=
-\frac{h^3J_h}{2}L^2+O_h(L)
}
\tag{27}
$$

对任意一个固定 \(h>0\) 成立。

这里右边不是“交叉项应当比较小”，而是：

$$
\boxed{
\text{交叉项必须很大、为负，且主系数必须恰好匹配。}
}
$$

例如，原来的 \(h=\log4\) 有 \(E_h=2\)，于是

$$
J_h=\frac{19}{3}.
$$

因此需要的抵消为

$$
\boxed{
\mathcal E_h^{\mathrm{off}}(L)
=
-\frac{19}{6}(\log4)^3L^2+O(L).
}
\tag{28}
$$

**这就是本轮精确定位的缺项。**

若把不同素数的交叉项设为零，只留下“每个素数贡献的平方”，结果会是 \(L^2\)，不是所需的 \(L\)。

这并不意味着素数之间存在某种未经定义的物理相互作用。它说明的是：**同一个确定性素数序列，经带符号核读取后，其不同事件响应不能被当成互不相关的项。**

# 七、在额外的简单零点假设下，还能算出小窗口均方的主常数

现在进一步分析：即使固定尺度平均有界，缩小 \(h\) 时，其正确的均方尺度是什么？

先不加入简单零点假设。

## 定理 6：RH 下的精确长期均方

在 RH 前件下，对每个固定 \(h>0\)，极限

$$
\mathcal V(h)
=
\lim_{L\to\infty}\frac{\mathcal E_h(L)}L
$$

存在，并且

$$
\boxed{
\mathcal V(h)
=
2\sum_{\gamma>0}
\frac{
m_\gamma^2|Q_h(e^{ih\gamma})|^2
}{\gamma^4}.
}
\tag{29}
$$

这里对不同的正纵坐标求和，\(m_\gamma\) 为重数。

### 证明

把式（19）写成

$$
\sum_{\gamma>0}
\left(A_\gamma e^{i\gamma T}
+\overline{A_\gamma}e^{-i\gamma T}\right)+o(1),
$$

其中

$$
A_\gamma
=
\frac{m_\gamma Q_h(e^{ih\gamma})}{\gamma^2}.
$$

绝对一致收敛允许先截断再求长期平均。

不同频率的交叉指数平均为零；相同频率贡献

$$
2|A_\gamma|^2.
$$

再令截断高度趋于无穷，即得式（29）。证毕。

这里不需要假设零点纵坐标有理线性无关，也不需要 Montgomery 配对相关猜想。重数必须平方，不能把 \(m_\gamma^2\) 偷换成 \(m_\gamma\)。零点均方研究中，对重数的这种区分是实质性的。([arXiv][4])

---

## 定理 7：RH 加全部零点简单，推出明确尺度律

现在额外假设全部非平凡零点简单。则

$$
\boxed{
\mathcal V(h)
\sim
\frac83h^3\log\frac1h
\qquad(h\downarrow0).
}
\tag{30}
$$

这里的简单零点条件必须单独保留，不能从 RH 中直接省略。

### 证明

在简单零点前件下，

$$
\mathcal V(h)
=
2\sum_{\gamma>0}
\frac{
|e^{ih\gamma}-e^{h/2}|^2
|e^{ih\gamma}-1|^6
}{\gamma^4}.
$$

令 \(u=h\gamma\)。使用零点计数公式

$$
N(Y)
=
\frac{Y}{2\pi}\log\frac{Y}{2\pi}
-\frac{Y}{2\pi}
+O(\log(Y+2)),
$$

作 Stieltjes 分部积分，得到

$$
\boxed{
\mathcal V(h)
\sim
\frac{h^3\log(1/h)}{\pi}
\int_0^\infty
\frac{|e^{iu}-1|^8}{u^4}\,du.
}
\tag{31}
$$

所需极限可以控制：在 \(u=0\) 附近，被积函数为 \(O(u^4)\)；在无穷远为 \(O(u^{-4})\)。把 \(e^{h/2}\) 保留在计算中时，原点附近多出的项为 \(O(h^2u^2)\)，同样可积。零点计数误差经分部积分后为更低阶。上述零点计数公式及更强的显式误差界已有文献。([arXiv][5])

最后，

$$
|e^{iu}-1|^8
=
70-112\cos u+56\cos2u-16\cos3u+2\cos4u.
$$

这些系数同时消去常数项和二次项。使用

$$
\int_0^\infty
\frac{\cos(au)-1+(au)^2/2}{u^4}\,du
=
\frac{\pi a^3}{12},
\qquad a\ge0,
$$

得到

$$
\begin{aligned}
\int_0^\infty
\frac{|e^{iu}-1|^8}{u^4}\,du
&=
\frac\pi{12}
(-112+56\cdot8-16\cdot27+2\cdot64)\\
&=\frac{8\pi}{3}.
\end{aligned}
$$

代入式（31），即得式（30）。证毕。

---

因此，未归一化读数的长期均方根尺度为

$$
\boxed{
h^{3/2}\sqrt{\log(1/h)},
}
$$

而不是 \(h^4\)。

对重标定读数，

$$
\mathcal B_h=\mathcal D_h/c(h),
\qquad
c(h)\sim h^4/2,
$$

于是

$$
\boxed{
\lim_{L\to\infty}
\frac1L\int_0^L|\mathcal B_h(T)|^2\,dT
\sim
\frac{32}{3}h^{-5}\log\frac1h.
}
\tag{32}
$$

即使在“RH 加全部零点简单”的情形下，这个均方也随着 \(h\to0\) 发散。

**极限顺序必须保留：这里先令 \(L\to\infty\)，再令 \(h\to0\)。它不是让 \(h=e^{-T/3}\) 随每个读出时间改变的联合极限。**

这与第二节的无条件趋零现象不矛盾。

# 八、对当前研究路线的准确修正

现在，尺度、量子完成和相关误差之间的关系可以严格分开。

## 1．可以无条件完成的是跨尺度结构

我们已经构造

$$
\boxed{
\mathcal B_H(T)
=
\mathbb E\bigl[\mathcal B_h(T+Y_{H,h})\bigr],
}
$$

其中 \(Y_{H,h}\) 的分布由式（12）明确给出。

它是一个真正的正权粗粒化，可以实现为随机平移量子信道。

但这种正权结构并不意味着输入读数非负，也不会自动证明实际算术相关已经满足所需的抵消。

## 2．不应该追求的，是微观一致有界

定理 3 已经无条件排除

$$
\sup_{T,h}|\mathcal B_h(T)|<\infty.
$$

原因不是“数学太难”，而是单个素数本身就给出了正负两侧的 \(h^{-3}\) 尖峰。

所以，不能把这一不可能的要求当作 RH 的中间目标。

## 3．真正需要控制的是固定尺度的联合能量

一个足够且必要的目标是：

$$
\boxed{
\int_0^L|\mathcal D_h(T)|^2\,dT
\le C_hL
}
$$

对某个固定 \(h>0\) 和全部充分大的 \(L\) 成立。

而本轮把这个目标进一步拆为

$$
\boxed{
\underbrace{\frac{h^3J_h}{2}L^2}_{\text{已知的单素数自贡献}}
+
\underbrace{\mathcal E_h^{\mathrm{off}}(L)}_{\text{待控制的跨素数贡献}}
=
O_h(L).
}
\tag{33}
$$

这比“缺一个相关项”的说法更具体：

$$
\boxed{
\mathcal E_h^{\mathrm{off}}(L)
\text{ 必须消去一个系数已知的 }L^2\text{ 主项。}
}
$$

剩下的线性均方，在进一步假设零点简单时，其小窗口系数还可以算成

$$
\frac83h^3\log(1/h).
$$

---

# 结论

这一轮得到的核心不是另一个抽象的“正核应当存在”，而是三组可以逐项检验的关系：

$$
\boxed{
\text{尺度完成}
:
\quad
\mathcal B_H
=
\text{细尺度读数的指定正权平均};
}
$$

$$
\boxed{
\text{微观结构}
:
\quad
\mathcal B_h
\longrightarrow
2\nu_{\mathbb P}''-\nu_{\mathbb P}'
\quad\text{在分布意义下};
}
$$

$$
\boxed{
\text{算术证明责任}
:
\quad
\mathcal E_h^{\mathrm{off}}(L)
=
-\frac{h^3J_h}{2}L^2+O_h(L).
}
$$

**本轮没有证明最后一条对实际素数成立。**但已经算清了它必须抵消什么、抵消到什么精度，以及哪些看似自然的替代目标根本不成立。

因此，接下来真正有价值的推理方向是：**直接研究这个固定局部核下的素数对相关，寻找能够消去已知二次主项的算术恒等式或统一估计。**继续缩小窗口、只看单个素数项，或者只证明尺度映射本身保正，都无法替代这一步。

[1]: https://arxiv.org/html/2206.03682v4 "Aspects of the screw function corresponding to the Riemann zeta-function"
[2]: https://dlmf.nist.gov/27.4 "DLMF: §27.4 Euler Products and Dirichlet Series ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"
[3]: https://terrytao.wordpress.com/2013/12/11/mertens-theorems/ "Mertens’ theorems | What's new"
[4]: https://arxiv.org/html/math/0412313v1 "Notes on Pair Correlation of Zeros and Prime Numbers"
[5]: https://arxiv.org/html/2412.15470v1 "Improved estimates for the argument and zero-counting of Riemann zeta-function(With an appendix by Andrew Fiori)"
