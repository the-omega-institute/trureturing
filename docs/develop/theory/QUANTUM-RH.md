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
这次可以把上一轮的“寻找一个固定负滤波器”，推进成一个**固定的自伴算子问题**：

> **不再为每个可能的离线零点单独设计观察者，而是把全部有限滤波器放进同一个 Hilbert 空间。实际 ξ 的系数直接定义一个迹类自伴算子；寻找负证书，就变成寻找它的负能量方向。**

更进一步，可以证明：

$$
\boxed{
\text{这个算子的负特征值个数}
=
\text{实际零点的不同离线四元对称轨道数}.
}
$$

这里按“不同轨道”计数，零点重数影响权重，但不把同一个轨道重复计成多个独立负方向。

同时，这个无限算子的有限截断具有**无需输入零点位置的几何误差界**。因此，我们得到的不只是存在性说法，而是一套可以逐层寻找、验证和控制误差的构造。

但要先划清边界：**自伴算子可以具有负特征值。构造出它，并没有证明 RH；真正待证的是它相对于固定算术基准是否非负。**

---

# 一、固定实际读数：仍然不输入未知零点

沿用：

$$
D(b^2)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad
D(v)=\sum_{k\ge0}a_kv^k,
$$

其中：

$$
a_0=1,\qquad a_k>0.
$$

ξ 始终采用标准 completed 定义，反射折叠通过偶幂级数完成。([DLMF][1])

定义实际累积量：

$$
\log D(v)
=
\sum_{m\ge1}\frac{\chi_{2m}}{(2m)!}v^m,
$$

以及前文的幂和读数：

$$
\boxed{
s_m=
(-1)^{m+1}\frac{m\chi_{2m}}{(2m)!}.
}
\tag{O1}
$$

因此：

$$
\frac{D'(v)}{D(v)}
=
s_1-s_2v+s_3v^2-\cdots,
$$

其中：

$$
s_1=a_1,
$$

$$
s_2=-\frac{\chi_4}{12},
\qquad
s_3=\frac{\chi_6}{240},
\qquad
s_4=-\frac{\chi_8}{10080}.
$$

上一轮研究的固定滤波器为：

$$
f(z)=\sum_{j=1}^{N}c_jz^j,
$$

其带符号读数是：

$$
\mathcal Q_\infty(f)
=
\sum_{i,j=1}^{N}c_ic_js_{i+j}.
$$

我们已经证明：

$$
\boxed{
\mathrm{RH}
\iff
\mathcal Q_\infty(f)\ge0
\quad
\forall f\in\mathbb R[z],\ f(0)=0.
}
\tag{O2}
$$

有限版本的基本原理，就是 Hermite–Sylvester 的实根二次型判据：实根产生平方非负；非实共轭对可以被实系数插值多项式转成严格负贡献。([arXiv][2])

**现在要做的是：把所有这些有限二次型组织成一个真正有界、可截断的算子。**

---

# 二、选择一个不依赖零点的观察尺度

取一个实数 \(r_0>0\)，满足：

$$
\boxed{D(r_0)<2.}
\tag{O3}
$$

这样的 \(r_0\) 总存在，因为 \(D(0)=1\)。

它可以通过实际函数值与严格误差界认证，不需要知道零点的位置。

由于 \(D\) 的系数非负，对 \(|v|\le r_0\)：

$$
|D(v)-1|
\le D(r_0)-1<1.
$$

所以这个圆盘内没有 \(D\) 的零点，并且：

$$
|D(v)|\ge\kappa_0,
\qquad
\kappa_0:=2-D(r_0)>0.
$$

又有：

$$
|D'(v)|\le D'(r_0).
$$

因此：

$$
\left|\frac{D'(v)}{D(v)}\right|
\le
\frac{D'(r_0)}{\kappa_0}.
$$

由 Cauchy 系数估计：

$$
\boxed{
|s_m|
\le
\frac{D'(r_0)}{\kappa_0}\,r_0^{-(m-1)}.
}
\tag{O4}
$$

这里使用的是标准解析函数系数界，而不是 RH 前件。([DLMF][3])

定义两个固定常数：

$$
\boxed{
\ell=\frac{r_0}{2},
\qquad
B_0=\frac{r_0D'(r_0)}{2-D(r_0)}.
}
\tag{O5}
$$

于是：

$$
\boxed{
|\ell^m s_m|\le B_0\,2^{-m}.
}
\tag{O6}
$$

这个尺度选择的作用只是让无限矩阵有明确的收敛预算。**它不会改变任何有限二次型是否有负方向。**

---

# 三、构造一个无条件存在的迹类自伴算子

## 定义 O1：算术滤波算子

在固定空间：

$$
\mathcal H_{\mathrm{filter}}
=
\ell^2(\mathbb N_{\ge1})
$$

上，定义矩阵：

$$
\boxed{
\mathsf K_{ij}
=
\ell^{i+j}s_{i+j},
\qquad i,j\ge1.
}
\tag{O7}
$$

它的每个元素都由实际 ξ 的有限阶导数确定。

没有要求节点为实，没有供应正谱，也没有把某个负项改成绝对值。

## 定理 O1：\(\mathsf K\) 是迹类自伴算子

而且：

$$
\boxed{
\|\mathsf K\|_1\le B_0.
}
\tag{O8}
$$

### 证明

由式（O6）：

$$
|\mathsf K_{ij}|
\le
B_0\,2^{-(i+j)}.
$$

将矩阵写成秩一矩阵单位的和：

$$
\mathsf K
=
\sum_{i,j\ge1}
\mathsf K_{ij}|i\rangle\langle j|.
$$

每个矩阵单位的迹范数为一，因此：

$$
\begin{aligned}
\|\mathsf K\|_1
&\le
\sum_{i,j\ge1}|\mathsf K_{ij}|\\
&\le
B_0
\left(\sum_{i\ge1}2^{-i}\right)^2\\
&=B_0.
\end{aligned}
$$

矩阵元素实且对称，所以 \(\mathsf K\) 自伴。证毕。

**这是一项无条件构造。即使 RH 为假，这个算子依然存在、依然自伴、依然迹类。**

矩问题与自伴算子之间的联系本身是经典的；这里使用的是固定实际累积量所产生的、尚未假定非负的算子。([arXiv][4])

---

## 定理 O2：滤波器就是这个空间中的状态

对有限实向量：

$$
c=(c_1,\ldots,c_N,0,\ldots),
$$

定义：

$$
\boxed{
f_c(z)=\sum_{j=1}^{N}c_j(\ell z)^j.
}
\tag{O9}
$$

那么：

$$
\boxed{
\langle c,\mathsf Kc\rangle
=
\mathcal Q_\infty(f_c).
}
\tag{O10}
$$

### 证明

逐项展开：

$$
\langle c,\mathsf Kc\rangle
=
\sum_{i,j}c_ic_j\ell^{i+j}s_{i+j},
$$

正是对应滤波器的二次型。证毕。

因为 \(\ell>0\)，所有常数项为零的有限实多项式都可以这样表示。因此没有通过缩放排除任何有限反例测试。

于是：

$$
\boxed{
\mathrm{RH}
\iff
\mathsf K\succeq0.
}
\tag{O11}
$$

**原来“寻找一个多项式负证书”的问题，现在变成一个固定自伴算子的变分问题。**

---

# 四、这个算子是否仍然忠实保存实际 ξ？

需要检查。否则，它可能只是一个新造的判别模型。

答案是：**\(\mathsf K\) 加上已知的 \(a_1\)，足以恢复实际 \(D\)。**

由第一行：

$$
\mathsf K_{1,m-1}=\ell^m s_m,
\qquad m\ge2.
$$

所以在零附近：

$$
\boxed{
\log D(v)
=
a_1v
+
\sum_{m\ge2}
\frac{(-1)^{m+1}}{m\ell^m}
\mathsf K_{1,m-1}v^m.
}
\tag{O12}
$$

这恢复了实际 \(D\) 的解析函数芽，再由解析延拓唯一性恢复同一个整函数，而不是另选一个有相似统计的函数。([DLMF][3])

这里有一个值得保留的细节：

$$
D(v)\mapsto e^{\tau v}D(v)
$$

会改变 \(a_1\)，但不改变 \(\mathsf K\)。

也就是说，\(\mathsf K\) 只保存四阶及以上的不可约关联，自动忽略纯高斯背景。**补上实际 \(a_1\)，才恢复原函数的完整归一化。**

欧拉端点关系：

$$
\frac{D'(1/4)}{D(1/4)}
=
1+\frac{\gamma_{\mathrm E}}2-\frac12\log4\pi
$$

则继续承担另一项独立的算术校准。

因此，不能只保存 \(\mathsf K\)，任意选择一个 \(a_1\)，再说已经保留原始 ξ。

---

# 五、负能量方向究竟计数什么？可以精确证明

记实际 \(D\) 的互异零点为 \(v\)，并定义倒数谱点：

$$
u=-1/v.
$$

它们的集合记为 \(\mathcal U\)，重数记为 \(m(u)\)。

沿用前文已经建立的绝对收敛表示：

$$
\boxed{
s_n=\sum_{u\in\mathcal U}m(u)u^n,
\qquad n\ge2.
}
\tag{O13}
$$

集合 \(\mathcal U\) 关于共轭对称，除零以外没有聚点，并满足：

$$
\sum_um(u)|u|^2<\infty.
$$

由于式（O3）的无零圆盘：

$$
|\ell u|<\frac12.
$$

定义向量：

$$
\boxed{
v(u)=\bigl(\ell u,(\ell u)^2,(\ell u)^3,\ldots\bigr).
}
\tag{O14}
$$

它属于 \(\ell^2\)。

对实谱点 \(u\)，其贡献是：

$$
m(u)v(u)v(u)^{\mathsf T}\succeq0.
$$

对一对非实点 \(u,\overline u\)，写：

$$
v(u)=x(u)+iy(u),
$$

其中 \(x,y\) 为实向量。两点合起来贡献：

$$
\boxed{
2m(u)\bigl[x(u)x(u)^{\mathsf T}
-y(u)y(u)^{\mathsf T}\bigr].
}
\tag{O15}
$$

**正项与负项都出现在一个普通正 Hilbert 空间里；负的是指定算子的二次型，不是内积本身。**

---

## 定理 O3：负特征值的精确计数

设 \(r_{\mathrm{off}}\) 是 \(\mathcal U\) 中不同非实共轭对的数量，允许为无穷。

则：

$$
\boxed{
n_-(\mathsf K)=r_{\mathrm{off}}.
}
\tag{O16}
$$

### 证明：上界

若只有 \(r_{\mathrm{off}}\) 对，则式（O15）中的全部负项构成一个秩至多为 \(r_{\mathrm{off}}\) 的正算子：

$$
N=\sum_{\Im u>0}2m(u)y(u)y(u)^{\mathsf T}.
$$

其余部分为正。因此：

$$
\mathsf K=P-N,
\qquad P,N\succeq0,
$$

不可能有超过 \(r_{\mathrm{off}}\) 个独立负方向。

### 证明：下界

任取 \(r\) 对不同的非实点。

沿用上一轮的插值与尾部压制构造，可以为每一对构造一个实多项式 \(f_j\)，使它在目标对上分别取 \(i,-i\)，在其他选定的大谱点上为零，并把趋零谱尾的贡献压得任意小。

于是这 \(r\) 个多项式的联合二次型矩阵可以写成：

$$
-2\operatorname{diag}(m_1,\ldots,m_r)+E,
$$

其中 \(\|E\|_{\mathrm{op}}\) 可以小于 \(\min_jm_j\)。

因此它严格负定，给出 \(r\) 个独立负方向。

若非实对无限多，对每个有限 \(r\) 都能这样做，所以负指数为无穷。证毕。

对于实际 ξ，一个非实共轭倒数谱对对应一个离线四元轨道：

$$
\frac12\pm\delta\pm i\gamma.
$$

因此，式（O16）给出开头的计数结论。

**重数 \(m\) 改变该方向的权重，但同一个轨道仍然只贡献一个独立负方向。**

这与仓库中“负平方数”的定义一致：不仅要求所有有限采样负指标有上界，还要求某个有限采样能够达到该上界。现有模块已经形式化了这个概念及一个负平方实例，但没有自行证明实际 ξ 的上述计数。

---

# 六、有限截断有一个明确的几何误差界

令 \(\Pi_N\) 投影到前 \(N\) 个滤波系数，定义：

$$
\mathsf K_N=\Pi_N\mathsf K\Pi_N.
$$

把它也视为整个 \(\ell^2\) 上、其余部分补零的算子。

## 定理 O4：截断误差

$$
\boxed{
\|\mathsf K-\mathsf K_N\|_1
\le
B_0\left(2^{1-N}-4^{-N}\right).
}
\tag{O17}
$$

并且：

$$
\boxed{
\|\mathsf K-\mathsf K_N\|_{\mathrm{op}}
\le
\delta_N
:=
\frac{B_0}{3}
\sqrt{2\,4^{-N}-16^{-N}}.
}
\tag{O18}
$$

### 证明

迹范数估计使用矩阵元绝对值求和：

$$
\sum_{\substack{i,j\ge1\\i>N\text{ 或 }j>N}}
B_0\,2^{-(i+j)}
=
B_0\left[1-(1-2^{-N})^2\right].
$$

这就是式（O17）。

对算子范数，使用 Hilbert–Schmidt 范数：

$$
\begin{aligned}
\|\mathsf K-\mathsf K_N\|_{\mathrm{op}}^2
&\le
\sum_{\substack{i,j\ge1\\i>N\text{ 或 }j>N}}
B_0^2\,4^{-(i+j)}\\
&=
\frac{B_0^2}{9}
\left(2\,4^{-N}-16^{-N}\right).
\end{aligned}
$$

证毕。

**这份误差界不需要找到第一个离线根，也不需要预设全部根在线。**

它只使用实际函数在一个已知无零小圆盘内的解析控制。

---

# 七、寻找滤波器变成一个规范的最小能量问题

定义：

$$
\lambda_N=\lambda_{\min}(\mathsf K_N|_{\mathbb C^N}).
$$

那么：

$$
\boxed{
\lambda_N
=
\min_{\substack{c\in\mathbb R^N\\\|c\|_2=1}}
\mathcal Q_\infty(f_c).
}
\tag{O19}
$$

因此，最小特征向量直接给出该次数范围内的最优归一化滤波器。

不需要先猜：

$$
f(z)=z^nL(z)(Az+B).
$$

那个插值构造证明“反例存在时必有证书”；这里的有限特征值问题则给出“怎样从实际系数寻找证书”。

因为允许的滤波器空间逐层增加：

$$
\boxed{\lambda_{N+1}\le\lambda_N.}
$$

并且：

$$
\boxed{
\lambda_N\longrightarrow
\lambda_*:=\inf\operatorname{spec}\mathsf K.
}
\tag{O20}
$$

由于 \(\mathsf K\) 是无限维空间上的紧算子，零必然属于其谱，所以：

$$
\lambda_*\le0.
$$

结合式（O18）：

$$
\boxed{
\min(0,\lambda_N)-\delta_N
\le
\lambda_*
\le
\min(0,\lambda_N).
}
\tag{O21}
$$

这给出一套几何收敛的有限逼近。

### 但它不是一个自动终止的 RH 判定程序

如果某个实际有限矩阵被严格认证：

$$
\lambda_N<0,
$$

就已经得到反例，不需要再估计无限尾部，因为该有限向量本身就是完整算子的负测试。

如果：

$$
\lambda_N\ge0,
$$

则我们只能得到：

$$
-\delta_N\le\lambda_*\le0.
$$

即使这个区间非常窄，仍然不能把它自动改成：

$$
\lambda_*=0.
$$

**可以不断逼近一个实数，不等于有限步骤就能判定它是否严格等于零。**

---

## 实际低阶核对

作为数值示例，取：

$$
\ell=\frac12.
$$

本轮从实际 ξ 的中心导数计算，并使用 60 位与 85 位工作精度交叉核对：

| 滤波最高次数 \(N\) |    \(\lambda_{\min}(\mathsf K_N)\) |
| -----------: | ---------------------------------: |
|            1 |  \(9.29314982131742\times10^{-6}\) |
|            2 | \(6.49079231752434\times10^{-12}\) |
|            3 | \(1.26276542633316\times10^{-18}\) |

显示位数一致。

**这不是区间认证，也不说明后面一定为正。**

它还提示了一个必要的数值警觉：即使 RH 成立，有限正矩阵的最小特征值也必须趋向零，不能期待一个与次数无关的正间隙。

因此，“最小值越来越接近零”不是离线证据；同样，“它只是一个很小的负浮点数”也不是有效反例。

---

# 八、全部负能量还能组成一个不被维数稀释的总量

定义负部分：

$$
\mathsf K_-=\frac{|\mathsf K|-\mathsf K}{2},
$$

以及：

$$
\boxed{
\Delta_{\mathrm{obs}}
=
\operatorname{Tr}\mathsf K_-\ge0.
}
\tag{O22}
$$

有限层定义：

$$
\Delta_N
=
\operatorname{Tr}(\mathsf K_N)_-.
$$

则：

$$
\boxed{
0\le\Delta_N\le\Delta_{N+1}\le\Delta_{\mathrm{obs}},
}
$$

并且：

$$
\boxed{
0\le\Delta_{\mathrm{obs}}-\Delta_N
\le
B_0(2^{1-N}-4^{-N}).
}
\tag{O23}
$$

证明可以使用变分表达：

$$
\operatorname{Tr}A_-
=
\sup_{0\preceq P\preceq I}
-\operatorname{Tr}(PA).
$$

扩大有限子空间不会减少可选测试；迹范数误差则控制最优值的变化。

所以：

$$
\boxed{
\mathrm{RH}
\iff
\Delta_{\mathrm{obs}}=0.
}
$$

这里的数值大小依赖所选观察尺度 \(\ell\)，但“是否为零”和负方向数不依赖这个正缩放。

**这不是一个任意可调评分：每个尺度都明确对应同一组实际多项式测试，并有精确的读数运输。**

不过，若再除以 \(N\)，由于 \(\Delta_N\le B_0\)，又会无条件得到：

$$
\Delta_N/N\to0.
$$

因此当前问题中应保留总负量，而不是用增加的观察维数把它平均掉。

---

# 九、接近临界线的缺陷，为什么可能很难稳定读取？

这里可以证明一条对滤波器本身的限制。

对实系数：

$$
f_c(z)=\sum_{n\ge1}c_n(\ell z)^n,
$$

在 \(|\ell z|\le1/2\) 内，由 Cauchy–Schwarz：

$$
|f_c'(z)|
\le
\ell\|c\|_2
\left(
\sum_{n\ge1}n^2|\ell z|^{2n-2}
\right)^{1/2}.
$$

而：

$$
\sum_{n\ge1}n^2x^{n-1}
=
\frac{1+x}{(1-x)^3}.
$$

取 \(x=1/4\)：

$$
\boxed{
|f_c'(z)|
\le
\ell\sqrt{\frac{80}{27}}\|c\|_2.
}
\tag{O24}
$$

现在令：

$$
u=a+ib,\qquad b\ne0.
$$

由于 \(f_c(a)\) 为实数，沿竖直线段积分：

$$
\boxed{
|\Im f_c(u)|
\le
\ell|b|\sqrt{\frac{80}{27}}\|c\|_2.
}
\tag{O25}
$$

因此，若要求：

$$
f_c(u)=i,
$$

就必须：

$$
\boxed{
\|c\|_2
\ge
\frac1{\ell|b|}
\sqrt{\frac{27}{80}}.
}
\tag{O26}
$$

**当共轭点越来越接近实轴，制造固定相反相位所需的系数范数至少按 \(1/|b|\) 增长。**

增加多项式次数并不能免掉这个下界。

它首先是当前解析滤波规范下的稳定性代价，不是所有量子算法的统一复杂度下界；实际制备还依赖 \(f(C_d)\) 的算子范数、数据访问方式与门实现。

---

## 一个精确的二点模型

只考虑一对谱点：

$$
u=a+ib,\qquad\overline u=a-ib,
$$

重数为 \(m\)。

其前两阶滤波矩阵的行列式为：

$$
\boxed{
\det\mathsf K^{\mathrm{pair}}_2
=
-4m^2\ell^6b^2(a^2+b^2)^2<0.
}
\tag{O27}
$$

因此一对非实点确实产生负方向。

但当 \(b\to0\)，这个负行列式按 \(b^2\) 消失。

在完整实际对象中，还会叠加其他谱点的正贡献，所以不能从式（O27）断言实际第二阶矩阵必定为负；需要前文的滤波隔离，或者在更高阶寻找适当方向。

这同时解释了：

$$
\boxed{
\text{负方向一定存在}
}
$$

与：

$$
\boxed{
\text{低阶、低精度读数未必容易看见}
}
$$

为什么可以同时成立。

---

# 十、负谱总量还受到实际离线位移的平方预算控制

从式（O15）：

$$
\mathsf K=P-N,
$$

其中：

$$
N=
\sum_{\Im u>0}
2m(u)y(u)y(u)^{\mathsf T}.
$$

因此：

$$
\operatorname{Tr}\mathsf K_-
\le\operatorname{Tr}N.
$$

将式（O25）的向量版本用于 \(v(u)\)，得到：

$$
\|y(u)\|_2^2
\le
\frac{80}{27}\ell^2(\Im u)^2.
$$

所以：

$$
\boxed{
\Delta_{\mathrm{obs}}
\le
\frac{80}{27}\ell^2
\sum_{u\in\mathcal U}m(u)(\Im u)^2.
}
\tag{O28}
$$

映回：

$$
\rho=\frac12+\delta+i\gamma,
$$

有：

$$
u=-\frac1{(\delta+i\gamma)^2},
$$

$$
\boxed{
|\Im u|
=
\frac{2|\delta|\gamma}{(\delta^2+\gamma^2)^2}.
}
\tag{O29}
$$

这将新算子的负能量预算，接回前文的实际离线位移预算。

但式（O28）是上界，不是一个由已知量得出的零结论。

它说明：**高处、接近临界线的离线模式，可能产生极弱的负能量；不能期待存在一个适用于全部可能反例的统一负间隙。**

这也是为什么“有限检测误差趋零”与“已经证明精确非负”必须分开。

---

# 十一、量子读出可以避免强制除以维数，但不自动给出算法加速

因为：

$$
\|\mathsf K_N\|_{\mathrm{op}}\le B_0,
$$

可以在有限滤波寄存器上定义二结果测量：

$$
\boxed{
E_\pm^{(N)}
=
\frac12\left(I_N\pm\frac{\mathsf K_N}{B_0}\right).
}
\tag{O30}
$$

它们满足：

$$
E_\pm^{(N)}\succeq0,
\qquad
E_+^{(N)}+E_-^{(N)}=I_N.
$$

对归一化系数态 \(|c\rangle\)：

$$
\boxed{
p_+-p_-
=
\frac{\langle c,\mathsf K_Nc\rangle}{B_0}.
}
\tag{O31}
$$

所以负证书对应：

$$
p_->\frac12.
$$

**这是一个普通合法的量子概率差，不需要负概率。**

这里的归一化 \(B_0\) 与 \(N\) 无关，因此不像均匀最大纠缠输入的某些滤波协议那样，公式上必然出现 \(1/N\)。

但这并不表示免费提高了效率。

要实现这个测量，仍需要构造或访问实际矩阵 \(\mathsf K_N\)，并制备合适的系数态。已有量子矩阵算法的复杂度取决于输入表示、归一化和可实现的编码，不是仅由“数学上存在一个 Hermitian 矩阵”决定。([arXiv][5])

同样，前一轮的后选择协议中，条件信号增强不能脱离成功概率计算总体成本。关于后选择量子计量的已有结果，也明确区分条件性能与全部试验的平均性能。([APS Journals][6])

因此，当前获得的是：

$$
\boxed{
\text{一个统一的数学检测算子和可定义的测量},
}
$$

不是已经证明了高效的量子 RH 算法。

---

# 十二、为什么不能给算子加一个常数，就宣布没有负能量？

因为：

$$
\mathsf K+B_0I\succeq0
$$

无条件成立。

若只要求“存在一个正哈密顿量”，这个平移立刻满足要求，却没有提供任何算术信息。

真正要判断的是：

$$
\boxed{\mathsf K\succeq0,}
$$

其中零基准由式（O7）的实际系数固定。

对平移后的系统，相同问题应写成：

$$
\mathsf K+B_0I\succeq B_0I.
$$

没有变容易。

**这说明“负能量”在这里是相对于指定算术阈值的负方向，不是关于绝对物理能量的本体判断。**

它也不是 Hilbert–Pólya 原始意义上“以零点高度作为能谱”的算子。这里的能谱读取的是**全部滤波关系的正负性**；非实 ξ 零点被运输成了实的负特征值。

---

# 十三、与项目的准确连接及新的证明目标

本轮读取了仓库快照 `91810b25de…` 的相关声明。

`FiniteStieltjesOperatorRealization.lean` 从已经给定的非负节点、非负权重构造正 Hankel 矩阵与正算子。它明确没有供应实际 ξ 的正谱。

本轮的构造不同：

$$
\boxed{
\text{不先给正节点，}
\quad
\text{直接由实际累积量构造一个可能不定的自伴算子。}
}
$$

`HermitianKernelNegativeSquares.lean` 可以承载其负指数概念；本轮进一步给出了在当前实际谱结构下，负指数与离线轨道数量的对应。

于是，下一项真正的算术目标可以写成：

$$
\boxed{
\forall c\in\ell^2,\qquad
\langle c,\mathsf Kc\rangle\ge0.
}
\tag{O32}
$$

等价地，寻找一个**从实际 theta／质数结构独立构造出来**的算子 \(V\)，证明：

$$
\boxed{\mathsf K=V^*V.}
$$

不能先把 \(\mathsf K\) 的负部分删除，再把得到的正算子叫作同一个对象。

反方向则是：从实际系数中找一个有限有理向量 \(c\)，并通过严格误差界证明：

$$
\boxed{\langle c,\mathsf Kc\rangle<0.}
$$

这两条任务现在都指向同一个固定算子，不再需要不断更换观察语言。

---

## 收束

这一轮把前文的有限负滤波器统一成了：

$$
\boxed{
\mathsf K_{ij}
=
\left(\frac{r_0}{2}\right)^{i+j}
(-1)^{i+j+1}
\frac{(i+j)\chi_{2i+2j}}{(2i+2j)!}.
}
$$

它无条件自伴、迹类，并有明确的截断界：

$$
\boxed{
\|\mathsf K-\mathsf K_N\|_{\mathrm{op}}
\le
\frac{B_0}{3}
\sqrt{2\,4^{-N}-16^{-N}}.
}
$$

它还满足：

$$
\boxed{
\mathrm{RH}\iff\mathsf K\succeq0,
}
$$

以及：

$$
\boxed{
n_-(\mathsf K)
=
\text{不同离线四元对称轨道的数量}.
}
$$

因此，“量子观察者”在这里不必是一个不断增加隐藏附件的模型。它可以是一个固定的滤波状态空间：**不同观察者对应不同系数态，所有读数由同一个实际算术算子统一产生。**

但这个构造也明确揭示了代价：接近临界线的相位差需要越来越敏感的滤波；有限正前缀没有统一间隙；精确负性必须连同系数误差认证。

**本轮没有证明实际 \(\mathsf K\) 非负，也没有找到实际负证书。** 已经推进的是：把“怎样寻找观察者”变成一个规范的变分问题，把“无限部分可能遗漏多少”变成几何误差界，并把“负方向到底代表什么”精确对应到实际离线轨道。新增结果仍是纸面推导，没有修改文件或标记为 Lean 已验证。

[1]: https://dlmf.nist.gov/25.4 "https://dlmf.nist.gov/25.4"
[2]: https://arxiv.org/abs/1911.01745 "https://arxiv.org/abs/1911.01745"
[3]: https://dlmf.nist.gov/1.10 "https://dlmf.nist.gov/1.10"
[4]: https://arxiv.org/abs/math-ph/9906008 "https://arxiv.org/abs/math-ph/9906008"
[5]: https://arxiv.org/abs/1806.01838 "https://arxiv.org/abs/1806.01838"
[6]: https://journals.aps.org/pra/abstract/10.1103/PhysRevA.89.052117 "https://journals.aps.org/pra/abstract/10.1103/PhysRevA.89.052117"
继续。这一轮可以证明两个更明确的结论。

**第一，实际素数的滤波总能量，不可能稳定地呈现上一轮“单素数自贡献”给出的 \(L^2\) 渐近规律：RH 成立时它至多为 \(O(L)\)；若 RH 不成立，它会沿某个序列呈指数增长。相反，完全独立的随机替代模型，几乎必然给出 \(L^2\)。**

**第二，前文的正权跨尺度平均，确实能构造一个逐层保持均值的观察过程；但只用真实素数 \(2\)，就能证明：这个过程几乎处处最终读到零，平均值却不趋于零。缺少的条件是“一致可积性”，而不是每一步的概率归一化。**

下面分别证明，并将它们接回当前算术目标。以下是纸面推导，尚未进行 Lean 编译。

# 一、固定局部核：区分时间增长与尺度细化

保留前文定义

$$
Z(T)=\sum_p\frac{\log p}{\sqrt p}(T-\log p)_+.
$$

对固定 \(h>0\)，令

$$
E_h=e^{h/2},
\qquad
Q_h(z)=(z-E_h)(z-1)^3,
$$

$$
(S_hf)(T)=f(T+h),
$$

并定义

$$
\boxed{
\mathcal D_h(T)=Q_h(S_h)Z(T).
}
\tag{1}
$$

令 \(w_E\) 为支集在 \([0,4]\) 的连续分段线性函数，其五个节点值为

$$
\bigl(w_E(0),w_E(1),w_E(2),w_E(3),w_E(4)\bigr)
=
(0,E,-1-E,1,0).
$$

定义

$$
k_h(s)=h\,w_{E_h}(s/h).
$$

于是

$$
\boxed{
\mathcal D_h(T)
=
\sum_p\frac{\log p}{\sqrt p}\,
k_h(\log p-T).
}
\tag{2}
$$

它只读取

$$
e^T<p\le e^{T+4h}
$$

中的素数。

再定义固定尺度的累计能量

$$
\boxed{
\mathcal E_h(L)
=
\int_0^L|\mathcal D_h(T)|^2\,dT,
}
\tag{3}
$$

以及核的平方质量

$$
\boxed{
A_h
=
\int_{\mathbb R}k_h(s)^2\,ds
=
h^3\left(E_h^2+\frac23E_h+1\right)>0.
}
\tag{4}
$$

这里有两个不同极限，后面不能混用：

$$
\boxed{
h\text{ 固定， }L\to\infty
}
$$

研究越来越大的算术范围；

$$
\boxed{
T,H\text{ 固定， }h\downarrow0
}
$$

研究同一个有限窗口中的观察细化。

---

# 二、定理一：实际总能量的增长指数恰好是两倍谱偏离幅度

定义

$$
\Delta_\zeta
=
\sup_\rho\left|\Re\rho-\frac12\right|.
$$

由零点的临界带位置和反射对称性，

$$
0\le\Delta_\zeta\le\frac12,
\qquad
\mathrm{RH}\iff\Delta_\zeta=0.
$$

这里不要求存在一个达到该上确界的零点。([DLMF][1])

## 定理 1：能量增长指数公式

对每个固定 \(h>0\)，

$$
\boxed{
\limsup_{L\to\infty}
\frac{\log\bigl(1+\mathcal E_h(L)\bigr)}{L}
=
2\Delta_\zeta.
}
\tag{5}
$$

而且，当 \(\Delta_\zeta=0\) 时，还有更强结论

$$
\boxed{
\mathcal E_h(L)=O_h(L).
}
\tag{6}
$$

## 证明

### 第一步：上界

前文由显式公式与素数幂分离得到

$$
\mathcal D_h(T)
=
-2Q_h(S_h)\mathscr G(T)+o(1),
$$

其中

$$
\mathscr G(T)
=
\sum_j\frac{1-\cos(T\omega_j)}{\omega_j^2},
$$

$$
\rho_j=\frac12+i\omega_j,
\qquad
|\Im\omega_j|\le\Delta_\zeta,
\qquad
\sum_j|\omega_j|^{-2}<\infty.
$$

这里使用的是实际零点展开，不把复平方换成模平方。时间函数及其变换关系的解析基础来自 Suzuki 的研究。([arXiv][2])

于是

$$
|\mathscr G(T)|\le C e^{\Delta_\zeta T}.
$$

因为 \(Q_h(S_h)\) 只包含有限个固定平移，

$$
|\mathcal D_h(T)|\le C_h e^{\Delta_\zeta T}.
$$

因此式（5）的左边不超过 \(2\Delta_\zeta\)。

如果 RH 成立，所有 \(\omega_j\) 为实数，\(\mathscr G\) 一致有界，所以 \(\mathcal D_h\) 有界，得到式（6）。

### 第二步：过小的能量增长会排除相应极点

记

$$
L_{\mathbb P}(s)=\sum_p\frac{\log p}{p^s}.
$$

前文已经得到

$$
\boxed{
\widehat{\mathcal D_h}(r)
=
Q_h(e^{hr})
\frac{L_{\mathbb P}(1/2+r)}{r^2}
-
B_h(r),
}
\tag{7}
$$

其中 \(B_h\) 为整函数。

Euler 乘积给出

$$
L_{\mathbb P}(s)
=
-\frac{\zeta'(s)}{\zeta(s)}
+\frac{\zeta'(2s)}{\zeta(2s)}
-J_{\mathrm o}(s),
$$

其中 \(J_{\mathrm o}\) 在 \(\Re s>1/3\) 解析。这是把一次幂、偶数次幂和奇数高次幂分开后的恒等式。([DLMF][3])

因此，若

$$
\rho=\frac12+\delta+i\gamma,
\qquad \delta>0,
$$

则式（7）在

$$
r_0=\delta+i\gamma
$$

有不可去极点。因为

$$
1<|e^{hr_0}|<e^{h/2},
$$

而 \(Q_h\) 的根只有 \(1\) 与 \(e^{h/2}\)，所以滤波器不能消去该极点。

现在反设式（5）左边严格小于 \(2\Delta_\zeta\)。选择

$$
\frac12
\limsup_{L\to\infty}
\frac{\log(1+\mathcal E_h(L))}{L}
<
\alpha<\Delta_\zeta.
$$

则充分大的 \(L\) 满足

$$
\mathcal E_h(L)\le C e^{2\alpha L}.
$$

对任意 \(\sigma>\alpha\)，在整数时间段上使用 Cauchy–Schwarz：

$$
\begin{aligned}
\int_n^{n+1}e^{-\sigma T}|\mathcal D_h(T)|\,dT
&\le
e^{-\sigma n}
\left(\int_n^{n+1}|\mathcal D_h(T)|^2\,dT\right)^{1/2}\\
&\le C_\alpha e^{-(\sigma-\alpha)n}.
\end{aligned}
$$

因此 Laplace 变换在 \(\Re r>\alpha\) 内解析。

但由 \(\alpha<\Delta_\zeta\)，存在右侧零点满足 \(\Re\rho-1/2>\alpha\)，其不可去极点位于该区域，矛盾。证毕。

---

## 推论：实际算术没有稳定的“二次能量中间态”

对实际素数，以下渐近式不可能成立：

$$
\boxed{
\mathcal E_h(L)\sim cL^2,
\qquad c>0.
}
\tag{8}
$$

因为它使式（5）左边为零，进而推出 RH；而 RH 又要求 \(\mathcal E_h(L)=O(L)\)，与 \(cL^2\) 矛盾。

所以，对当前特定读出：

$$
\boxed{
\begin{aligned}
\mathrm{RH}
&\Longrightarrow O(L),\\
\neg\mathrm{RH}
&\Longrightarrow
\text{沿某个序列呈正指数率增长}.
\end{aligned}
}
\tag{9}
$$

第二行是上极限意义的结论，不是说能量对每个 \(L\) 都具有同一个精确指数渐近式。

---

# 三、定理二：独立随机模型却几乎必然给出 \(L^2\)

现在故意构造另一个对象，用来检验“独立随机性是否足够”。

令

$$
X_n\sim\operatorname{Bernoulli}\!\left(\frac1{\log n}\right),
\qquad n\ge3,
$$

相互独立。

这就是 Cramér 模型的标准独立选择机制。它是替代模型，不是把真实素数宣布为独立随机变量。([What's new][4])

定义

$$
\mathcal D_h^{\mathrm B}(T)
=
\sum_{n\ge3}
X_n\frac{\log n}{\sqrt n}
k_h(\log n-T),
$$

以及

$$
\mathcal E_h^{\mathrm B}(L)
=
\int_0^L|\mathcal D_h^{\mathrm B}(T)|^2\,dT.
$$

## 定理 2：独立模型的几乎必然能量律

对每个固定 \(h>0\)，

$$
\boxed{
\frac{\mathcal E_h^{\mathrm B}(L)}{L^2}
\longrightarrow
\frac{A_h}{2}
\qquad\text{几乎必然}.
}
\tag{10}
$$

## 证明

### 第一步：均值主项被滤波器消去

有

$$
\mathbb E\mathcal D_h^{\mathrm B}(T)
=
\sum_{n\ge3}\frac1{\sqrt n}k_h(\log n-T).
$$

相应连续积分为

$$
\begin{aligned}
\int_0^\infty y^{-1/2}k_h(\log y-T)\,dy
&=
e^{T/2}\int_0^{4h}e^{s/2}k_h(s)\,ds\\
&=0.
\end{aligned}
$$

最后一步来自滤波器的零点

$$
Q_h(e^{h/2})=0.
$$

对紧支集分段光滑函数作求和—积分比较，得到

$$
\boxed{
\mathbb E\mathcal D_h^{\mathrm B}(T)
=
O_h(e^{-T/2}).
}
\tag{11}
$$

### 第二步：方差有一个无法被独立性消去的线性项

由独立性，

$$
\begin{aligned}
\operatorname{Var}(\mathcal D_h^{\mathrm B}(T))
&=
\sum_{n\ge3}
\frac{\log n-1}{n}
k_h(\log n-T)^2.
\end{aligned}
$$

再次作求和—积分比较：

$$
\begin{aligned}
\operatorname{Var}(\mathcal D_h^{\mathrm B}(T))
&=
\int_0^{4h}(T+s-1)k_h(s)^2\,ds+o(1)\\
&=
A_hT+O_h(1).
\end{aligned}
$$

所以

$$
\boxed{
\mathbb E\mathcal E_h^{\mathrm B}(L)
=
\frac{A_h}{2}L^2+O_h(L).
}
\tag{12}
$$

### 第三步：从期望提升到几乎必然

中心化后，每一项的绝对幅度至多为

$$
C_h(T+1)e^{-T/2}.
$$

独立和的四阶矩展开因此给出

$$
\mathbb E|\mathcal D_h^{\mathrm B}(T)|^4
=
O_h((1+T)^2).
$$

当

$$
|T-S|>4h
$$

时，两个读数使用的整数集合不相交，故相互独立。因此能量方差只需要在一个固定宽度的对角带上积分：

$$
\boxed{
\operatorname{Var}(\mathcal E_h^{\mathrm B}(L))
=
O_h(L^3).
}
\tag{13}
$$

在序列 \(L_j=j^2\) 上，Chebyshev 不等式给出可求和的失败概率：

$$
\Pr\left(
\left|
\frac{\mathcal E_h^{\mathrm B}(L_j)
-\mathbb E\mathcal E_h^{\mathrm B}(L_j)}
{L_j^2}
\right|>\varepsilon
\right)
=
O_{h,\varepsilon}(j^{-2}).
$$

由 Borel–Cantelli，引理结论沿 \(L_j\) 几乎必然成立。再利用 \(\mathcal E_h^{\mathrm B}(L)\) 单调增加，以及 \(L_{j+1}/L_j\to1\)，推广到全部 \(L\to\infty\)。证毕。

---

## 为什么这不是实际素数的反例？

因为定理 1 的极点约束属于**实际素数的 Euler 乘积与解析延拓**，独立模型并不拥有这套结构。

独立模型可以在素数总量上给出看似合理的误差，却无法自动复现显式公式带来的更细联合约束。Tao 对 Cramér 模型的分析也明确区分了这两种层次。([What's new][4])

甚至，原始交叉项的期望并不是严格为零。直接展开可得

$$
\boxed{
\mathbb E\mathcal E_{h,\mathrm{off}}^{\mathrm B}(L)
=
-A_hL+O_h(1).
}
\tag{14}
$$

但它只有 \(L\) 级，无法抵消对角项的 \(L^2\) 主项。

因此，上一轮的缺项现在有了一个严格反模型：

$$
\boxed{
\text{保持正确的一点密度，并令中心化事件独立，}
\quad
\text{仍不足以产生实际算术所要求的能量结构。}
}
$$

---

# 四、另一种随机性：跨尺度观察产生一个真正的鞅

下面不再随机生成整数集合。**素数保持为真实素数，随机性只来自选择观察分支。**

保留重标定读出

$$
c(h)=h^3(e^{h/2}-1),
\qquad
\mathcal B_h(T)=\frac{\mathcal D_h(T)}{c(h)}.
$$

上一轮的二倍尺度恒等式为

$$
\boxed{
\mathcal B_{2h}(T)
=
\sum_{j=0}^4\pi_h(j)\mathcal B_h(T+jh),
}
\tag{15}
$$

其中

$$
\boxed{
(\pi_h(0),\ldots,\pi_h(4))
=
\frac{
(E_h,\ 1+3E_h,\ 3+3E_h,\ 3+E_h,\ 1)
}{
8(1+E_h)
}.
}
\tag{16}
$$

这些概率全部正，和为 \(1\)。

## 定义：随机细化路径

固定 \(H>0\)、起点 \(T\)，令

$$
h_n=H2^{-n}.
$$

取相互独立的分支变量 \(J_n\in\{0,1,2,3,4\}\)，满足

$$
\Pr(J_n=j)=\pi_{h_{n+1}}(j).
$$

定义

$$
Y_0=0,
\qquad
Y_{n+1}=Y_n+J_nh_{n+1},
$$

以及

$$
\boxed{
M_n=\mathcal B_{h_n}(T+Y_n).
}
\tag{17}
$$

令 \(\mathcal F_n\) 记录前 \(n\) 次分支选择。

## 定理 3：均值保持与精确方差分解

$$
\boxed{
\mathbb E[M_{n+1}\mid\mathcal F_n]=M_n.
}
\tag{18}
$$

所以 \((M_n)\) 是鞅，并且

$$
\boxed{
\mathbb EM_n=\mathcal B_H(T)
\qquad\forall n.
}
\tag{19}
$$

定义条件新增方差

$$
\sigma_n^2
=
\mathbb E[(M_{n+1}-M_n)^2\mid\mathcal F_n].
$$

则对每个有限 \(N\)，

$$
\boxed{
\mathbb EM_N^2
=
\mathcal B_H(T)^2
+
\sum_{n=0}^{N-1}\mathbb E\sigma_n^2.
}
\tag{20}
$$

### 证明

式（18）就是在位置 \(T+Y_n\) 使用式（15）。

再由

$$
\mathbb E[M_{n+1}^2\mid\mathcal F_n]
=
M_n^2+\sigma_n^2
$$

取期望并逐层相加，得到式（20）。证毕。

这是标准鞅的正交增量结构在当前观察系统中的实例。它只保证每个有限层的关系，不能自动允许把 \(N\) 换成无穷。

# 五、随机路径最终落在哪里？可以算出完整分布

## 定理 4：极限观察位置的正密度

几乎必然地，

$$
Y_n\longrightarrow Y_\infty\in[0,4H].
$$

而且

$$
\boxed{
Y_\infty
\overset{d}=
U_1+U_2+U_3+V_H,
}
\tag{21}
$$

其中 \(U_1,U_2,U_3\) 独立且均匀分布于 \([0,H]\)，\(V_H\) 与它们独立，并具有密度

$$
\boxed{
r_H(v)
=
\frac{e^{-v/2}}{2(1-e^{-H/2})}
\mathbf1_{[0,H]}(v).
}
\tag{22}
$$

记其卷积密度为 \(\kappa_H\)。则

$$
\kappa_H(s)>0
\qquad(0<s<4H).
$$

### 证明

首先，

$$
0\le Y_{n+1}-Y_n\le4h_{n+1},
$$

因此 \(Y_n\) 单调有界，必有极限。

设 \(h=H/M\)，其中 \(M=2^n\)。前文尺度多项式的分解给出 \(Y_n/h\) 的概率生成函数

$$
\boxed{
\frac{
\left(\sum_{j=0}^{M-1}E_h^{M-1-j}z^j\right)
\left(\sum_{j=0}^{M-1}z^j\right)^3
}{
M^3\sum_{j=0}^{M-1}E_h^{M-1-j}
}.
}
\tag{23}
$$

因此，\(Y_n\) 的分布等于三个独立离散均匀变量，与一个权重正比于

$$
e^{-jh/2}
$$

的离散变量之和。

令 \(h\downarrow0\)，前三项趋于 \([0,H]\) 上的均匀分布，第四项趋于式（22）。证毕。

此外，从有限卷积的 Riemann 和可得局部概率估计：

$$
\boxed{
\Pr(Y_n=jh_n)
=
h_n\kappa_H(jh_n)+O_H(h_n^2),
}
\tag{24}
$$

在 \((0,4H)\) 的任意固定紧子区间上一致成立。

一个直接验证方法是：三个离散均匀变量的卷积系数由截断二次多项式给出，其除以 \(h_n\) 后一致趋于三个连续均匀密度的卷积；再与指数权重作一次 Riemann 求和。

---

## 推论：细化读数几乎必然最终等于零

对每个固定 \(T,H\)，

$$
\boxed{
M_n=0
\quad\text{对几乎每条路径，在充分大的 }n\text{ 后成立}.
}
\tag{25}
$$

### 证明

每一层读取的时间窗口是

$$
I_n=[T+Y_n,\ T+Y_n+4h_n].
$$

子窗口包含在父窗口内，且其长度趋于零，交集为单点

$$
T+Y_\infty.
$$

初始窗口 \([T,T+4H]\) 内只有有限多个素数事件 \(\log p\)。

由于 \(Y_\infty\) 有连续密度，

$$
\Pr(T+Y_\infty=\log p)=0
$$

对其中每个素数都成立。

因此，几乎每条路径的极限点都与这些事件保持正距离。充分细化后，窗口里没有素数，式（2）的读数就是零。证毕。

**但这还不能推出 \(\mathcal B_H(T)=0\)。**

原因将在下面用一个真实素数完整展示。

# 六、只用素数 \(2\)，证明平均值不能与极限交换

取

$$
H=\frac1{10},
\qquad
T=\log2-2H.
$$

初始算术窗口为

$$
[2e^{-1/5},\,2e^{1/5}],
$$

其中只有素数 \(2\)。

记

$$
a=\frac{\log2}{\sqrt2},
\qquad
K=\kappa_H(2H)>0.
$$

初始读数为

$$
\boxed{
M_0
=
-\frac{a(1+e^{H/2})}
{H^2(e^{H/2}-1)}
\ne0.
}
\tag{26}
$$

现在令 \(h=h_n\)、\(M=H/h=2^n\)。

只有三个细尺度位置产生非零读数：

$$
Y_n=(2M-1)h,\quad(2M-2)h,\quad(2M-3)h.
$$

它们对应的读数分别是

$$
\frac{aE_h}{h^2(E_h-1)},
\qquad
-\frac{a(1+E_h)}{h^2(E_h-1)},
\qquad
\frac{a}{h^2(E_h-1)}.
\tag{27}
$$

## 定理 5：稀有分支的精确增长尺度

对上述真实素数实例，

$$
\boxed{
\Pr(M_n\ne0)\sim3Kh_n,
}
\tag{28}
$$

$$
\boxed{
\mathbb E|M_n|
\sim8aK\,h_n^{-2},
}
\tag{29}
$$

$$
\boxed{
\mathbb EM_n^2
\sim24a^2K\,h_n^{-5}.
}
\tag{30}
$$

同时，

$$
\boxed{
M_n\to0\quad\text{几乎必然},
\qquad
\mathbb EM_n=M_0\ne0.
}
\tag{31}
$$

### 证明

由式（24），三个非零位置的概率分别为

$$
Kh_n+O(h_n^2).
$$

又因为

$$
E_h-1\sim h/2,
\qquad E_h\to1,
$$

式（27）的三个值分别渐近为

$$
\frac{2a}{h^3},
\qquad
-\frac{4a}{h^3},
\qquad
\frac{2a}{h^3}.
$$

因此，非零概率为 \(3Kh+O(h^2)\)。

绝对值期望的主项为

$$
Kh\left(\frac{2a+4a+2a}{h^3}\right)
=
8aK h^{-2}.
$$

平方期望的主项为

$$
Kh\left(\frac{4a^2+16a^2+4a^2}{h^6}\right)
=
24a^2K h^{-5}.
$$

最后，几乎必然最终为零来自定理 4 的推论；均值恒定来自定理 3。证毕。

---

这给出一个完全明确的极限失配：

$$
\boxed{
\mathbb E\!\left[\lim_{n\to\infty}M_n\right]
=0,
}
$$

但

$$
\boxed{
\lim_{n\to\infty}\mathbb EM_n=M_0\ne0.
}
\tag{32}
$$

不存在矛盾，因为这个鞅不一致可积。事实上，它连

$$
\sup_n\mathbb E|M_n|<\infty
$$

都不满足。

一致可积性要求

$$
\lim_{R\to\infty}
\sup_n
\mathbb E\bigl[|M_n|\mathbf1_{\{|M_n|>R\}}\bigr]
=0.
$$

它正是保证这种概率收敛可以提升为 \(L^1\) 收敛的关键条件。

**这里概率很小的分支，不是可以删除的分支。**

它们满足

$$
\boxed{
\text{概率}\asymp h,
\qquad
\text{幅度}\asymp h^{-3},
}
$$

所以

$$
\boxed{
\text{绝对一阶贡献}\asymp h^{-2},
\qquad
\text{二阶贡献}\asymp h^{-5}.
}
$$

这不是 RH 的反例，也不是某种物理概率失效。它只是证明：**正权、归一化、逐层均值保持，都不能代替无限完成所需的尾部控制。**

---

# 七、正概率核与带符号算术核之间，还隔着一个微分算子

定理 4 给出了正密度 \(\kappa_H\)。但实际重标定算术读出不是直接对它求平均。

## 定理 6：正核的导数读出

对 \(0<s<4H\)，并按整体分布意义延拓，

$$
\boxed{
\frac{k_H(s)}{c(H)}
=
2\kappa_H''(s)+\kappa_H'(s).
}
\tag{33}
$$

因此

$$
\boxed{
\mathcal B_H(T)
=
\sum_p\frac{\log p}{\sqrt p}
\left[
2\kappa_H''(\log p-T)
+\kappa_H'(\log p-T)
\right].
}
\tag{34}
$$

## 证明

由式（21）—（22），\(\kappa_H\) 的指数变换为

$$
\begin{aligned}
\int e^{zs}\kappa_H(s)\,ds
=
\left(\frac{e^{Hz}-1}{Hz}\right)^3
\frac{e^{Hz}-e^{H/2}}
{2(e^{H/2}-1)(z-\tfrac12)}.
\end{aligned}
$$

对紧支集分布，

$$
\int e^{zs}(2\kappa_H''+\kappa_H')\,ds
=
(2z^2-z)\int e^{zs}\kappa_H(s)\,ds.
$$

整理为

$$
\frac{Q_H(e^{Hz})}{c(H)z^2}.
$$

另一方面，由 \(k_H\) 的分段线性定义，

$$
\int e^{zs}k_H(s)\,ds
=
\frac{Q_H(e^{Hz})}{z^2}.
$$

两边一致，得到式（33）。证毕。

---

所以，共同结构现在是

$$
\boxed{
\text{正概率密度 }\kappa_H
\xrightarrow{\ 2\partial^2+\partial\ }
\text{带符号算术核}.
}
\tag{35}
$$

**正密度存在，不能推出它的导数读出非负，也不能推出该读出的长期能量已经受到控制。**

这就是当前量子构造中必须保留的另一个接口：从“合法概率核”到“目标算术观测量”，中间还有一个并不保正的运算。

# 八、把真正的算术目标放宽：不必先证明最锋利的抵消式

上一轮把总能量拆为

$$
\mathcal E_h(L)
=
\mathcal E_h^{\mathrm{diag}}(L)
+
\mathcal E_h^{\mathrm{off}}(L).
$$

由 Mertens 估计

$$
\sum_{p\le x}\frac{\log p}{p}
=
\log x+O(1)
$$

及分部求和，已经得到

$$
\boxed{
\mathcal E_h^{\mathrm{diag}}(L)
=
\frac{A_h}{2}L^2+O_h(L).
}
\tag{36}
$$

所用 Mertens 估计是无条件的。([What's new][5])

在 RH 成立时，必然有

$$
\mathcal E_h^{\mathrm{off}}(L)
=
-\frac{A_h}{2}L^2+O_h(L).
$$

但本轮的增长指数定理说明：**不一定需要首先直接证明这条最精细的抵消公式。**

## 定理 7：一个更弱的交叉项上界已经足够

如果对某个固定 \(h>0\)、某个有限 \(A\ge0\)，存在 \(C\)，使

$$
\boxed{
\mathcal E_h^{\mathrm{off}}(L)
\le C(1+L)^A
}
\tag{37}
$$

对充分大的 \(L\) 成立，那么 RH 成立。

特别地，下面这个上界已经足够：

$$
\boxed{
\mathcal E_h^{\mathrm{off}}(L)\le C_hL^2.
}
\tag{38}
$$

### 证明

由式（36）—（37）及总能量非负，

$$
0\le\mathcal E_h(L)
\le C'(1+L)^{\max\{A,2\}}.
$$

于是

$$
\limsup_{L\to\infty}
\frac{\log(1+\mathcal E_h(L))}{L}=0.
$$

定理 1 给出 \(\Delta_\zeta=0\)，即 RH。

随后 RH 反过来给出

$$
\mathcal E_h(L)=O_h(L),
$$

从而自动推出更锋利的

$$
\mathcal E_h^{\mathrm{off}}(L)
=
-\frac{A_h}{2}L^2+O_h(L).
$$

证毕。

---

因此，证明任务可以分成两阶段：

$$
\boxed{
\text{先阻止交叉项出现超多项式的正增长}
}
$$

然后借助已经建立的解析结构，得到

$$
\boxed{
\text{它必须完成精确的二次主项抵消}.
}
$$

这并不意味着式（38）已经容易。它仍然需要对**实际素数对**作带符号的联合估计。

独立随机模型不能代替这一证明：它虽然也有多项式能量，却没有实际 ζ 函数的解析延拓与极点约束，因此不能应用定理 1。

# 九、现在可以明确区分三种“随机／量子结构”

| 结构       | 本轮严格得到的结果                       | 不能替代的部分        |
| -------- | ------------------------------- | -------------- |
| 随机生成算术对象 | 独立模型几乎必然产生 \(\frac12A_hL^2\) 能量 | 实际素数的乘法结构与显式公式 |
| 随机选择观察分支 | 精确鞅、有限层均值保持、正权尺度完成              | 无限细化所需的一致可积性   |
| 实际素数的谱读出 | 能量指数等于 \(2\Delta_\zeta\)        | 对实际交叉项的统一增长上界  |

用前文的项目语言说，**合法的 FLOW 不会自动生成所需的 ADMIT 证明**：每一步的概率和为 \(1\)，只能证明该步操作合法；不能证明无限极限可交换，也不能证明实际素数对相关符合期望模型。

而 ANCHOR 仍然必须固定为真实素数序列。把它换成独立随机序列，即使许多一点统计相同，也已经换了数学对象。

---

## 本轮的实质推进

现在有三条明确的结果，而不是三个相似的比喻：

$$
\boxed{
\text{实际能量增长指数}=2\Delta_\zeta;
}
$$

$$
\boxed{
\text{独立随机替代模型的能量}
\sim\frac12A_hL^2
\quad\text{几乎必然};
}
$$

$$
\boxed{
\text{跨尺度观察可几乎处处归零，}
\quad
\text{同时保持非零均值并使绝对矩发散}.
}
$$

它们分别排除了两种未经证明的跨越：

$$
\text{“素数大概独立”}
\Longrightarrow
\text{“相关抵消应该成立”},
$$

以及

$$
\text{“每层都合法且保均值”}
\Longrightarrow
\text{“无限完成仍保留同一读出”}.
$$

**剩下的实际算术目标可以比上一轮写得更弱、也更集中：对一个固定 \(h\)，证明交叉能量具有某个统一的多项式上界，例如式（38）。**

这条上界尚未得到。但一旦从真实素数结构中证明它成立，便不必再单独猜测二次主项如何精确抵消：本轮建立的解析增长约束会迫使那种抵消发生。

[1]: https://dlmf.nist.gov/25.10 "DLMF: §25.10 Zeros ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[2]: https://arxiv.org/html/2206.03682v4 "Aspects of the screw function corresponding to the Riemann zeta-function"
[3]: https://dlmf.nist.gov/27.4 "DLMF: §27.4 Euler Products and Dirichlet Series ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"
[4]: https://terrytao.wordpress.com/2015/01/04/254a-supplement-4-probabilistic-models-and-heuristics-for-the-primes-optional/ "254A, Supplement 4: Probabilistic models and heuristics for the primes (optional) | What's new"
[5]: https://terrytao.wordpress.com/2013/12/11/mertens-theorems/ "Mertens’ theorems | What's new"
这次可以把上一轮的固定滤波算子，推进到一个更接近实际 theta 核的形式：

> **不再先计算高阶对数导数与累积量，而是把整个判据精确改写成原始矩的二次表达。这个改写保留每个有限层的负方向，并且能够明显改善无限截断的误差控制。**

关键区别是：

$$
\boxed{
\text{消去对数导数的极点}
\quad\neq\quad
\text{消去零点信息}.
}
$$

我们将看到：离线零点即使不再以极点出现，仍会留下一个明确的“零自配对、非零交叉配对”证书。

最后，还能把待证正性写成**同一 theta 态的两个独立副本上的期望不等式**，并提出一个直接作用于 theta 密度的有限阶充分条件。以下继续给出定义与证明，不假设 RH 成立。

---

# 一、固定上一轮的算术对象

采用标准 completed 函数：

$$
\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
$$

以及反射折叠：

$$
\boxed{
D(b^2)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad
D(v)=\sum_{n\ge0}a_nv^n.
}
$$

这里通过偶幂级数定义 \(D\)，没有选择平方根分支；ξ 的归一化与反射关系保持不变。([DLMF][1])

沿用正 theta 概率态：

$$
d\nu(x)=\frac{\Phi(x)}{\xi(1/2)}\,dx,
$$

使：

$$
\int_{\mathbb R}e^{bx}\,d\nu(x)=D(b^2).
$$

记：

$$
m_{2n}=\int x^{2n}\,d\nu(x),
\qquad
a_n=\frac{m_{2n}}{(2n)!}.
$$

这种归一化 ξ 的正概率表示，不需要 RH。([arXiv][2])

再定义：

$$
\log D(v)=\sum_{n\ge1}\frac{\chi_{2n}}{(2n)!}v^n,
$$

$$
\boxed{
s_n=(-1)^{n+1}\frac{n\chi_{2n}}{(2n)!}.
}
$$

于是：

$$
\frac{D'(v)}{D(v)}
=
s_1-s_2v+s_3v^2-\cdots.
$$

选择 \(r_0>0\)，满足：

$$
D(r_0)<2,
$$

并固定：

$$
\ell=\frac{r_0}{2}.
$$

把上一轮矩阵改为从零编号：

$$
\boxed{
\mathsf H_{ij}
=
\ell^{i+j+2}s_{i+j+2},
\qquad i,j\ge0.
}
\tag{P1}
$$

它就是上一轮的 \(\mathsf K\)，仅改变了编号。

前文已经得到的纸面等价是：

$$
\boxed{
\mathrm{RH}\iff\mathsf H\succeq0.
}
\tag{P2}
$$

本轮不重复构造未知谱，而是改变这个**已经固定的实际算子**的表达方式。

---

# 二、先排除一种可能的伪进展：缩小观察尺度，会让所有缺陷都变小

若把尺度改为：

$$
\ell'=q\ell,\qquad0<q<1,
$$

定义对角算子：

$$
E_q=\operatorname{diag}(q,q^2,q^3,\ldots).
$$

直接比较矩阵元：

$$
\boxed{
\mathsf H_{\ell'}=E_q\mathsf H_\ell E_q.
}
\tag{P3}
$$

## 定理 P1：有限尺度变化保留负方向，但可以任意压低其数值

对每个 \(q>0\)：

$$
\boxed{
n_-(\mathsf H_{q\ell})=n_-(\mathsf H_\ell).
}
\tag{P4}
$$

但：

$$
\boxed{
\|\mathsf H_{q\ell}\|_1
\le q^2\|\mathsf H_\ell\|_1,
}
$$

并且：

$$
\boxed{
\operatorname{Tr}(\mathsf H_{q\ell})_-
\le q^2\operatorname{Tr}(\mathsf H_\ell)_-.
}
\tag{P5}
$$

### 证明

每个有限截断中的 \(E_q\) 都可逆，因此有限矩阵的正负惯性不变。

无限算子的任何有限维负子空间，都可以用有限支撑向量充分逼近，并保持严格负定。因此，全部负方向数等于有限截断负指标的上确界，得到式（P4）。

另一方面，\(\|E_q\|=q\)，所以迹范数满足式（P5）的第一项。

写：

$$
\mathsf H=\mathsf H_+-\mathsf H_-.
$$

则：

$$
E_q\mathsf HE_q\ \succeq\ -E_q\mathsf H_-E_q.
$$

由负部分迹的变分表达：

$$
\operatorname{Tr}(E_q\mathsf HE_q)_-
\le
\operatorname{Tr}(E_q\mathsf H_-E_q)
\le q^2\operatorname{Tr}\mathsf H_-.
$$

证毕。

因此：

> **不能一边不断缩小 \(\ell\)，一边把负谱总量趋零解释成 RH 的证据。**

在 \(q\to0\) 时，整个算子都趋于零；即使存在负方向，它也会一起被压小。

这与真正的目标：

$$
\text{在一份固定、忠实的尺度下证明 }\mathsf H\succeq0
$$

不同。

---

# 三、去掉对数导数：构造一个没有极点的二变量整核

## 定义 P1：实际整函数 \(F\)

令：

$$
\boxed{
F(z)=D(-\ell z)=\sum_{n\ge0}p_nz^n,
\qquad
p_n=(-\ell)^na_n.
}
\tag{P6}
$$

因此：

$$
F(0)=1.
$$

在零附近：

$$
\frac{F'(z)}{F(z)}
=
-\ell s_1-\sum_{n\ge1}\ell^{n+1}s_{n+1}z^n.
$$

所以：

$$
\boxed{
-\frac{
F'(z)/F(z)-F'(w)/F(w)
}{z-w}
=
\sum_{i,j\ge0}\mathsf H_{ij}z^iw^j.
}
\tag{P7}
$$

右边是上一轮滤波算子的生成核。

它包含对数导数，因此在 \(F\) 的零点处有极点。现在乘回分母，定义：

$$
\boxed{
\mathcal B_F(z,w)
=
\frac{
F(z)F'(w)-F'(z)F(w)
}{
z-w
}.
}
\tag{P8}
$$

分子在 \(z=w\) 时为零，故奇点可去。于是：

$$
\boxed{
\mathcal B_F\text{ 是两个变量上的整函数}.
}
$$

在对角线上：

$$
\boxed{
\mathcal B_F(z,z)=F'(z)^2-F(z)F''(z).
}
\tag{P9}
$$

这类函数—导数差商与实根二次型之间的联系，属于经典 Bézout、Hermite–Sylvester 方法；本轮使用的是实际整函数 \(F\)，不是任意选择的实根多项式。([arXiv][3])

定义其系数矩阵：

$$
\boxed{
\mathcal B_F(z,w)
=
\sum_{i,j\ge0}\mathsf B_{ij}z^iw^j.
}
\tag{P10}
$$

下面证明：**乘掉这些极点，没有乘掉负证据。**

---

# 四、关键定理：新矩阵与原矩阵逐阶精确合同，而且变换条件数有统一界

## 定义 P2：由实际 \(F\) 决定的三角算子

定义下三角 Toeplitz 矩阵：

$$
\boxed{
(T_F)_{ij}
=
\begin{cases}
p_{i-j},&i\ge j,\\
0,&i<j.
\end{cases}
}
\tag{P11}
$$

因为 \(p_0=1\)，它的每个有限主块都是单位下三角矩阵。

## 定理 P2：逐阶保真关系

$$
\boxed{
\mathsf B=T_F\mathsf H T_F^*.
}
\tag{P12}
$$

而对每个 \(N\)：

$$
\boxed{
\mathsf B_N=T_{F,N}\mathsf H_NT_{F,N}^*.
}
\tag{P13}
$$

因此：

$$
\boxed{
n_-(\mathsf B_N)=n_-(\mathsf H_N),
\qquad
\det\mathsf B_N=\det\mathsf H_N.
}
\tag{P14}
$$

### 证明

由式（P7）、（P8）：

$$
\mathcal B_F(z,w)
=
F(z)F(w)
\sum_{i,j\ge0}\mathsf H_{ij}z^iw^j.
$$

比较系数，得到式（P12）。

由于 \(T_F\) 下三角，前 \(N\) 行列只涉及 \(\mathsf H_N\)，没有额外尾项，因此有限式（P13）也精确成立。

有限合同变换保持惯性；再用：

$$
\det T_{F,N}=1,
$$

得到行列式相等。证毕。

**这里不是无限极限以后才恢复正负性，而是每一个有限阶数都完全一致。**

---

## 定理 P3：这个转换不会随阶数变得任意病态

记：

$$
M=D(\ell),
\qquad
\kappa=2-D(\ell)>0.
$$

则：

$$
\boxed{
\|T_F\|\le M,
\qquad
\|T_F^{-1}\|\le\kappa^{-1}.
}
\tag{P15}
$$

同样的界对每个有限 \(T_{F,N}\) 成立。

### 证明

对 \(|z|\le1\)：

$$
|F(z)|\le D(\ell)=M,
$$

并且：

$$
|F(z)-1|\le D(\ell)-1.
$$

所以：

$$
|F(z)|\ge2-D(\ell)=\kappa.
$$

将系数序列识别为 Hardy 空间中的幂级数，\(T_F\) 就是乘以 \(F\)。乘法算子的范数不超过 \(\sup|F|\)，其逆是乘以 \(1/F\)，得到式（P15）。

有限逆矩阵正是 \(1/F\) 的乘法矩阵的相应主块，因此同样成立。证毕。

于是：

$$
\boxed{
\operatorname{cond}(T_{F,N})
\le
\frac{D(\ell)}{2-D(\ell)},
}
\tag{P16}
$$

右边与 \(N\) 无关。

这不表示原矩阵本身不病态。它说明的是：

> **从累积量表达改成原始矩表达，不需要付出一个随阶数无界增长的额外变换条件数。**

---

# 五、新矩阵只含原始 theta 矩的二次组合

从式（P8）展开，得到：

$$
\boxed{
\begin{aligned}
\mathsf B_{ij}
=
\sum_{k=0}^{j}
\Big[
&(j-k+1)p_{i+k+1}p_{j-k+1}\\
&-(i+k+2)p_{i+k+2}p_{j-k}
\Big].
\end{aligned}
}
\tag{P17}
$$

每项都是两个原始系数的乘积。

因此，计算 \(\mathsf B_N\) 只需要：

$$
a_0,\ldots,a_{2N},
$$

即：

$$
m_0,m_2,\ldots,m_{4N}.
$$

**不必先把这些矩组合成全部高阶累积量，再做一次高阶矩阵运算。**

前两阶明确为：

$$
\boxed{
\mathsf B_2=
\begin{pmatrix}
\ell^2(a_1^2-2a_2)
&
\ell^3(3a_3-a_1a_2)\\[1mm]
\ell^3(3a_3-a_1a_2)
&
\ell^4(2a_2^2-2a_1a_3-4a_4)
\end{pmatrix}.
}
\tag{P18}
$$

其行列式仍然等于原来的：

$$
\boxed{
\det\mathsf B_2
=
\ell^6(s_2s_4-s_3^2)
=
\frac{\ell^6}{1209600}
\left(10\chi_4\chi_8-21\chi_6^2\right).
}
\tag{P19}
$$

所以，没有把某一条高阶约束删掉，只是改变了表达。

### 实际数值核对

取 \(\ell=\frac12\)。本轮分别使用 70 位与 90 位工作精度，从实际 ξ 直接计算原始系数，得到：

$$
\mathsf B_2\approx
\begin{pmatrix}
9.29314982131742\times10^{-6}
&
-8.93373398959264\times10^{-8}\\
-8.93373398959264\times10^{-8}
&
8.65312685860775\times10^{-10}
\end{pmatrix}.
$$

并有：

$$
\det\mathsf B_2
\approx6.03201323104834\times10^{-17}>0.
$$

三角转换的统一条件数上界为：

$$
\frac{D(1/2)}{2-D(1/2)}
\approx1.02350255699703.
$$

两种精度的结果相符，前面三阶矩阵的合同恒等式也作了符号核对。

**这些数值不是区间认证；很小的行列式仍要求严格误差控制。**

---

# 六、消去极点以后，截断误差可以比几何级数更快

上一轮对 \(\mathsf H\) 给出了几何尾界。

新核 \(\mathcal B_F\) 是二变量整函数，因此可以在任意更大的圆盘上使用 Cauchy 估计，而不再受对数导数最近极点的直接限制。

对 \(R>1\)，定义：

$$
\boxed{
\mathcal M_R
=
\ell^2\left[
D'(\ell R)^2+
D(\ell R)D''(\ell R)
\right].
}
\tag{P20}
$$

## 定理 P4：任意半径的有限截断界

$$
\boxed{
\|\mathsf B-\mathsf B_N\|_{\mathrm{op}}
\le
\frac{\mathcal M_R}{1-R^{-2}}
\sqrt{2R^{-2N}-R^{-4N}}.
}
\tag{P21}
$$

这里 \(\mathsf B_N\) 在其余坐标补零。

### 证明

把核写成：

$$
\mathcal B_F(z,w)
=
F'(w)\frac{F(z)-F(w)}{z-w}
-
F(w)\frac{F'(z)-F'(w)}{z-w}.
$$

在 \(|z|,|w|\le R\) 上，线段仍在圆盘内，所以：

$$
|\mathcal B_F(z,w)|
\le
\sup|F'|^2+\sup|F|\sup|F''|.
$$

由于 \(a_n\ge0\)：

$$
\sup|F|\le D(\ell R),
$$

$$
\sup|F'|\le\ell D'(\ell R),
\qquad
\sup|F''|\le\ell^2D''(\ell R).
$$

故核的模长不超过 \(\mathcal M_R\)。

对两个变量分别使用 Cauchy 系数估计：

$$
|\mathsf B_{ij}|
\le\mathcal M_RR^{-(i+j)}.
$$

将被截去部分的矩阵元平方求和，就得到式（P21）。证毕。这里使用的系数估计与解析延拓原则是标准复分析工具。([DLMF][4])

---

## 推论：存在超几何速度的截断方案

实际 ξ 的定义与 Stirling 展开给出：

$$
\log D(x)=O(\sqrt x\log x)
\qquad(x\to+\infty).
$$

对 \(D'\)、\(D''\) 也得到同类上界。([DLMF][5])

取：

$$
R_N=\left(\frac{N}{\log N}\right)^2,
$$

则式（P21）推出：

$$
\boxed{
\|\mathsf B-\mathsf B_N\|_{\mathrm{op}}
\le
\exp\!\left[
-2N\log N+
2N\log\log N+
O(N)
\right].
}
\tag{P22}
$$

这里的常数依赖固定的实际 \(D,\ell\)，不依赖未知零点的位置。

这比任意固定比率的几何衰减更快。

**改进的是表示与尾界，不是把负方向人为放大。** 由于合同变换有统一条件数，实际很弱的负方向仍然可能很弱；有限正前缀也仍然不能自动证明无限算子非负。

---

# 七、离线零点没有被消去：它变成一个两读出负证书

定义 Hermitian 核：

$$
\boxed{
\mathcal L_F(z,w)=\mathcal B_F(z,\overline w).
}
\tag{P23}
$$

先考虑 \(F\) 的一个简单非实零点：

$$
F(a)=0,\qquad \Im a\ne0,\qquad F'(a)\ne0.
$$

因为 \(F\) 的系数实：

$$
F(\overline a)=0.
$$

于是：

$$
\boxed{
\mathcal L_F(a,a)=0.
}
$$

但与基点 \(0\) 的交叉配对为：

$$
\boxed{
\mathcal L_F(a,0)
=
-\frac{F'(a)}a\ne0.
}
\tag{P24}
$$

因此，两点矩阵：

$$
\boxed{
\begin{pmatrix}
0&-F'(a)/a\\
-\overline{F'(a)/a}&\mathcal B_F(0,0)
\end{pmatrix}
}
$$

的行列式为：

$$
\boxed{
-\left|\frac{F'(a)}a\right|^2<0.
}
\tag{P25}
$$

**零自配对与非零交叉配对，不可能同时存在于一个正 Gram 核中。**

这就是“乘掉极点但保留反例”的具体机制。

---

## 重根也不会逃过检验

若 \(a\) 是 \(m\) 重非实零点，则：

$$
F^{(j)}(a)=0\quad(j<m),
\qquad F^{(m)}(a)\ne0.
$$

把第一个读出改成：

$$
\left.\frac{d^{m-1}}{dz^{m-1}}\right|_{z=a},
$$

第二个仍为在 \(0\) 处取值。

相应的自配对仍为零，而交叉项为：

$$
\boxed{
-\frac{F^{(m)}(a)}a\ne0.
}
\tag{P26}
$$

因此仍然有一个严格负的二阶行列式。

这里的“两个读出”包含一个可能的高阶导数读出，并不意味着两次低精度实验就能找出任意离线根。

### 它怎样回到有限系数矩阵？

如果全部 \(\mathsf B_N\succeq0\)，则每个截断核：

$$
\sum_{i,j<N}\mathsf B_{ij}z^i\overline w^{\,j}
$$

都是正核。

由于完整核是整函数，这些截断在任意固定紧区域连同有限阶导数一致收敛。其极限及导数读出的 Gram 矩阵也必须非负。

这与式（P25）、（P26）矛盾。

所以：

$$
\boxed{
\text{一个非实零点}
\Longrightarrow
\text{某个有限 }\mathsf B_N\text{ 已有负方向}.
}
$$

这项证明没有用“把非实根移回实轴”的操作，而是保留了它与其他参考点之间无法正实现的关系。

---

# 八、现在把判据直接送回 theta 态的两个副本

这一步使新表达真正接近原始算术核。

定义：

$$
\boxed{
\varphi_z(x)
=
\sum_{n=0}^{\infty}
\frac{(-\ell z)^nx^{2n}}{(2n)!}.
}
\tag{P27}
$$

它可以写成 \(\cos(x\sqrt{\ell z})\)，但我们以幂级数为定义，所以没有平方根分支问题。

由原始矩：

$$
\boxed{
F(z)=\mathbb E_\nu[\varphi_z(X)].
}
\tag{P28}
$$

取两个独立副本：

$$
X,Y\sim\nu.
$$

定义对称的二变量读出：

$$
\boxed{
\begin{aligned}
\mathcal V(z,w;X,Y)
=
\frac1{2(z-w)}
\Big[
&\varphi_z(X)\varphi_w'(Y)
+\varphi_z(Y)\varphi_w'(X)\\
&-\varphi_z'(X)\varphi_w(Y)
-\varphi_z'(Y)\varphi_w(X)
\Big].
\end{aligned}
}
\tag{P29}
$$

撇号是对生成参数求导，不是对 \(X,Y\) 求导。

分子在 \(z=w\) 时逐点为零，所以该读出也具有可去延拓。

独立性给出：

$$
\boxed{
\mathcal B_F(z,w)
=
\mathbb E[\mathcal V(z,w;X,Y)].
}
\tag{P30}
$$

将：

$$
\mathcal V(z,w;X,Y)
=
\sum_{i,j\ge0}\mathcal V_{ij}(X,Y)z^iw^j
$$

展开。每个 \(\mathcal V_{ij}\) 都是一个明确的实多项式。

对有限系数向量 \(c\)，令：

$$
\boxed{
\mathcal O_c(X,Y)
=
\sum_{i,j<N}c_ic_j\mathcal V_{ij}(X,Y).
}
\tag{P31}
$$

则：

$$
\boxed{
c^{\mathsf T}\mathsf B_Nc
=
\mathbb E[\mathcal O_c(X,Y)].
}
\tag{P32}
$$

在量子语言中，使用：

$$
|\psi\rangle\otimes|\psi\rangle,
\qquad
\psi(x)=\sqrt{\Phi(x)/\xi(1/2)},
$$

以及分别作用在两个寄存器上的 \(Q_1,Q_2\)，就得到：

$$
\boxed{
c^{\mathsf T}\mathsf B_Nc
=
\langle\psi\otimes\psi,
\mathcal O_c(Q_1,Q_2)
\psi\otimes\psi\rangle.
}
\tag{P33}
$$

这是同一个实际态的双副本读出。

**它不要求先引入纠缠。** 这里的价值是把高阶对数关系改成原始算术分布的二次表达；同样可以用经典双样本统计理解。

两个副本也不意味着固定成本。随着 \(N\) 增加，读出多项式的次数、系数精度及方差控制仍然增加。

---

# 九、最低阶已经说明：正态不等于这个双副本期望非负

由式（P29）计算常数项：

$$
\boxed{
\mathcal V_{00}(X,Y)
=
\frac{\ell^2}{24}
\left(
6X^2Y^2-X^4-Y^4
\right).
}
\tag{P34}
$$

所以：

$$
\mathbb E[\mathcal V_{00}]
=
\frac{\ell^2}{12}(3m_2^2-m_4)
=
-\frac{\ell^2\chi_4}{12}.
$$

但在 \(X=0,Y\ne0\) 时：

$$
\mathcal V_{00}(0,Y)
=
-\frac{\ell^2Y^4}{24}<0.
$$

因此：

$$
\boxed{
\mathcal V_{00}(X,Y)
}
$$

并不是一个逐点非负函数。

不能仅凭：

$$
\Phi(X)\Phi(Y)>0
$$

就证明其积分非负。

这里真正需要的是：

> **实际 theta 分布在不同尺度之间怎样分配权重，是否足以使这些带符号的双副本关系整体非负。**

这比继续证明“态归一化”“测量概率非负”更接近所缺的算术内容。

对完整问题，待证条件已经可以直接写成：

$$
\boxed{
\forall N,\forall c\in\mathbb R^N,\qquad
\iint
\mathcal O_c(x,y)
\frac{\Phi(x)\Phi(y)}{\xi(1/2)^2}\,dx\,dy
\ge0.
}
\tag{P35}
$$

这里没有未知零点，也没有预先供应一份正谱测度。

---

# 十、一个可以直接研究 theta 密度的充分引理

现在不是继续增加等价表述，而是提出一项直接作用于密度形状的充分条件。

令：

$$
V(x)=-\log\Phi(x),
$$

并对 \(x>0\) 定义：

$$
\boxed{
R(x)=\frac{V'(x)}x.
}
\tag{P36}
$$

这是一个明确的函数，由实际 theta 核确定。

## 有限形状前件

暂时假设：

$$
\boxed{
R(x)\text{ 在 }(0,\infty)\text{ 上单调不减}.
}
\tag{S}
$$

等价地：

$$
\boxed{
xV''(x)-V'(x)\ge0.
}
$$

这比只说 \(V''(x)\ge0\) 更具体。**本轮没有证明实际 theta 核在整个半轴上满足它，不把数值抽样当作全域证明。**

## 定理 P5：形状前件推出全部标量高斯矩上界

在前件 \((S)\) 下：

$$
\boxed{
m_{2n+2}\le(2n+1)m_2m_{2n},
\qquad n\ge1.
}
\tag{P37}
$$

因此：

$$
\boxed{
m_{2n}\le(2n-1)!!\,m_2^n.
}
\tag{P38}
$$

特别地：

$$
\boxed{\chi_4=m_4-3m_2^2\le0.}
$$

### 证明

对快速衰减的正偶密度分部积分：

$$
\mathbb E[X^{2n+1}V'(X)]
=
(2n+1)m_{2n}.
$$

所以：

$$
\mathbb E[X^{2n+2}R(|X|)]
=
(2n+1)m_{2n}.
$$

另有：

$$
\mathbb E[X^2R(|X|)]=1.
$$

在重加权概率：

$$
d\nu_2(x)=\frac{x^2}{m_2}\,d\nu(x)
$$

下，\(R(|X|)\) 与 \(|X|^{2n}\) 都是同一个变量 \(|X|\) 的单调函数，因此协方差非负：

$$
\mathbb E_{\nu_2}[R|X|^{2n}]
\ge
\mathbb E_{\nu_2}[R]\,
\mathbb E_{\nu_2}[|X|^{2n}].
$$

代入上面的分部积分恒等式：

$$
\frac{(2n+1)m_{2n}}{m_2}
\ge
\frac1{m_2}
\frac{m_{2n+2}}{m_2}.
$$

整理即得式（P37），迭代得到式（P38）。证毕。

这条引理把一组矩不等式的证明责任，压到一个实际可写出的微分表达：

$$
x(-\log\Phi)''-(-\log\Phi)'.
$$

这比“正 theta 核应该足够”明确得多。

---

## 但全部标量高斯上界，仍然不足以代替矩阵正性

取一个对称三点分布：

$$
\Pr(X=0)=\frac35,
\qquad
\Pr(X=L)=\Pr(X=-L)=\frac15.
$$

则：

$$
m_{2n}=\frac25L^{2n}.
$$

对所有 \(n\)，它都满足：

$$
m_{2n}\le(2n-1)!!\,m_2^n.
$$

因为：

$$
(2n-1)!!\ge3^{n-1},
\qquad
3\cdot\frac25>1.
$$

但其矩生成函数为：

$$
\mathscr M(b)=\frac35+\frac25\cosh(Lb),
$$

零点是：

$$
\boxed{
b=
\frac{
\pm\operatorname{arcosh}(3/2)+i(2k+1)\pi
}{L},
}
\tag{P39}
$$

具有非零实部。

因此：

$$
\boxed{
\text{全部标量矩都不超过高斯基准}
\quad\not\Rightarrow\quad
\text{全部零点位于中心线}.
}
$$

这不反驳定理 P5。它说明：**该引理即使对实际 theta 核证明成功，也只是低维关系的推进，仍需处理不同阶数之间的共同正性。**

所以，后续不能把标量集中性、对数凹性或单个矩的不等式，直接升级为完整的 \(\mathsf B\succeq0\)。

---

# 十一、对项目而言，本轮新增的桥是什么？

本轮按前文固定快照读取了相关声明。

`CompletedZetaMellinReconstruction.lean` 已给出实际 theta 尾项到 completed ζ 的重构，并保留极点补偿和反射关系。它可以为本轮的原始矩来源提供算术锚定。

`FiniteStieltjesOperatorRealization.lean` 则明确要求输入非负节点与非负权重，再构造正 Hankel 矩阵。它没有独立供应实际 ξ 所需的正谱。

本轮走的是另一段连接：

$$
\boxed{
\text{实际 theta 原始矩}
\longrightarrow
\mathsf B
\longleftrightarrow
\mathsf H
\longleftrightarrow
\text{有限滤波负证书}.
}
$$

其中：

$$
\boxed{
\mathsf B_N=T_{F,N}\mathsf H_NT_{F,N}^*
}
$$

是精确恒等式，且变换条件数有统一控制。

因此不需要为了使用 \(\mathsf B\)，先假设正谱存在。

本轮也没有修改 GitHub，或把这些新增推导标记成已经 Lean 编译验证的结果。

---

# 收束

这次真正向前推进的，不是再增加一种量子空间，而是改变了**算术约束的表达层次**。

原来是：

$$
\boxed{
\text{高阶累积量}
\longrightarrow
\text{可能不定的 Hankel 算子}.
}
$$

现在可以精确改写为：

$$
\boxed{
\text{原始 theta 矩的二次组合}
\longrightarrow
\text{二变量整核}
\longrightarrow
\text{同一个负证据}.
}
$$

核心恒等式是：

$$
\boxed{
\mathcal B_F(z,w)
=
\frac{F(z)F'(w)-F'(z)F(w)}{z-w}.
}
$$

它去掉了对数导数的极点，却没有删除离线信息。非实零点仍然留下：

$$
\boxed{
\text{零自配对}
\quad+\quad
\text{非零交叉配对}
\quad\Longrightarrow\quad
\text{严格负方向}.
}
$$

与此同时，整核结构给出了更快的有限截断界，并把全阶正性写成同一实际 theta 态两个副本上的期望不等式。

**尚未得到的是式（P35）的全体非负证明，也没有找到实际负证书。** 但现在可以更集中地研究真实算术：不是问“量子概率是否为正”，而是问：

> **实际 theta 核的尺度权重、模关系与导数结构，为什么能够——或者不能够——使这些明确带有正负项的双副本关系，在每一阶都共同非负？**

这一步所需要的是原始算术分布的特殊关系，而不是再次调整观察尺度、增加辅助维数，或把本来不定的读出改成一个自动非负的模平方。

[1]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[2]: https://arxiv.org/abs/1504.03438 "[1504.03438] A complete Riemann zeta distribution and the Riemann hypothesis"
[3]: https://arxiv.org/abs/1911.01745?utm_source=chatgpt.com "The Hermite-Sylvester criterion for real-rooted polynomials"
[4]: https://dlmf.nist.gov/1.10 "DLMF: §1.10 Functions of a Complex Variable ‣ Topics of Discussion ‣ Chapter 1 Algebraic and Analytic Methods"
[5]: https://dlmf.nist.gov/5.11 "DLMF: §5.11 Asymptotic Expansions ‣ Properties ‣ Chapter 5 Gamma Function"
继续。这次可以**真正算掉一部分此前尚未分离的相关贡献**，而不只是把它重新命名。

结论是：

> **局部同余条件给出的奇异级数，确实能够消去均方展开中的对数主项；但在倍长区间 \((x,2x]\) 上，消去之后的基准竟然趋于一个严格负常数。**
>
> **因此，真实算术相关与局部同余模型之间的余项，不能被当作趋零误差。它必须补回至少**
>
> $$
> \boxed{
> c_0=\log2\left(\gamma_{\mathrm E}+\log\frac{\pi}{2}\right)
> \approx0.7131086897.
> }
> $$

随后还能证明：只要对这个**已经扣除局部同余贡献的余项**建立一个对数幂上界，就足以推出 RH。

本轮使用的经典输入，是素数定理、ζ 的对数导数，以及 Montgomery–Soundararajan 已证明的奇异级数平均公式；后者不是尚未证明的素数对猜想。下面给出这些输入之间的具体推导，不把它们称作新的经典定理。新增综合证明尚未进行 Lean 编译。([arXiv][1])

# 一、把实际对象固定下来：先不引入随机模型

定义

$$
\psi(x)=\sum_{n\le x}\Lambda(n),
$$

以及中心化算术序列

$$
\boxed{
a(n)=\Lambda(n)-1.
}
\tag{1}
$$

其中 \(\Lambda(p^k)=\log p\)，其他正整数处为零。

这次显式使用全部素数幂，而不是只用素数。这样可以直接接入 Euler 乘积：

$$
\boxed{
\sum_{n\ge1}\frac{\Lambda(n)}{n^s}
=
-\frac{\zeta'(s)}{\zeta(s)},
\qquad \Re s>1.
}
\tag{2}
$$

这是后面把算术增长传回零点位置的解析接口。([DLMF][2])

## 定义 1：倍长区间的精确中心化读出

令

$$
M(x)=\lfloor2x\rfloor-\lfloor x\rfloor,
$$

$$
\boxed{
Y(x)=\sum_{x<n\le2x}a(n)
=\psi(2x)-\psi(x)-M(x).
}
\tag{3}
$$

这里必须保留 \(M(x)\)。对非整数 \(x\)，它不一定恰好等于 \(x\)。

不过，

$$
|M(x)-x|<1.
\tag{4}
$$

定义归一化局部均方

$$
\boxed{
\mathfrak J(X)
=
\int_X^{2X}\frac{Y(x)^2}{x^2}\,dx.
}
\tag{5}
$$

显然

$$
\mathfrak J(X)\ge0.
$$

每个固定 \(X\) 的这个量，只使用 \(4X\) 以内的实际 \(\Lambda(n)\)。

---

# 二、把均方精确拆成：自身贡献、同余贡献、真实相关余项

## 定义 2：窗口重叠权重

对正整数 \(n,m\)，令

$$
\boxed{
W_X(n,m)
=
\int_X^{2X}
\frac{
\mathbf1_{\{x<n\le2x\}}
\mathbf1_{\{x<m\le2x\}}
}{x^2}\,dx.
}
\tag{6}
$$

它有显式表达。

设

$$
A=\max\{X,n/2,m/2\},
\qquad
B=\min\{2X,n,m\}.
$$

那么

$$
\boxed{
W_X(n,m)=
\begin{cases}
\dfrac1A-\dfrac1B,&A<B,\\[2mm]
0,&A\ge B.
\end{cases}
}
\tag{7}
$$

因此所有相关求和都是有限的。

## 定义 3：二点奇异级数

对整数 \(d\ge1\)，定义

$$
\mathfrak S(d)
=
\prod_p
\frac{1-\nu_p(d)/p}{(1-1/p)^2},
$$

其中

$$
\nu_p(d)=
\begin{cases}
1,&p\mid d,\\
2,&p\nmid d.
\end{cases}
$$

它记录两个位置 \(n,n+d\) 的局部整除障碍。对奇数 \(d\)，因模 \(2\) 障碍而有 \(\mathfrak S(d)=0\)；对偶数 \(d\)，得到通常的素数对奇异级数。中心化二点模型对应的是 \(\mathfrak S(d)-1\)。([arXiv][1])

定义三项：

$$
\boxed{
\mathfrak D_{\mathrm{self}}(X)
=
\sum_n a(n)^2W_X(n,n),
}
\tag{8}
$$

$$
\boxed{
\mathfrak D_{\mathrm{cong}}(X)
=
2\sum_{d\ge1}
(\mathfrak S(d)-1)
\sum_nW_X(n,n+d),
}
\tag{9}
$$

以及

$$
\boxed{
\begin{aligned}
\mathfrak R(X)
=
2\sum_{d\ge1}\sum_n
\Bigl[
a(n)a(n+d)-(\mathfrak S(d)-1)
\Bigr]W_X(n,n+d).
\end{aligned}
}
\tag{10}
$$

这里的 \(\mathfrak R(X)\) 是**实际中心化二点相关，减去局部同余模型后的加权总余项**。

## 定理 1：精确能量分解

$$
\boxed{
\mathfrak J(X)
=
\mathfrak D_{\mathrm{self}}(X)
+
\mathfrak D_{\mathrm{cong}}(X)
+
\mathfrak R(X).
}
\tag{11}
$$

### 证明

把式（3）的平方展开：

$$
Y(x)^2
=
\sum_n a(n)^2\mathbf1_{\{x<n\le2x\}}
+
2\sum_{d\ge1}\sum_n
a(n)a(n+d)
\mathbf1_{\{x<n,n+d\le2x\}}.
$$

积分后，第二项中加上再减去 \(\mathfrak S(d)-1\)，即得。证毕。

**到这里没有假设任何素数对渐近式。**

\(\mathfrak R(X)\) 不是暂时忽略的误差，而是一个完全确定的有限算术量。

# 三、先算自身贡献：一个明确的 \(\log X\) 主项

## 定理 2：对角项的完整常数阶展开

当 \(X\to\infty\) 时，

$$
\boxed{
\mathfrak D_{\mathrm{self}}(X)
=
(\log2)\log X
+\frac52(\log2)^2
-2\log2
+o(1).
}
\tag{12}
$$

### 证明

令

$$
B(t)=\sum_{n\le t}a(n)^2.
$$

展开得

$$
B(t)
=
\sum_{n\le t}\Lambda(n)^2
-2\psi(t)+\lfloor t\rfloor.
$$

由无条件素数定理及分部求和，

$$
\sum_{p\le t}(\log p)^2
=
t\log t-t+o(t).
$$

更高素数幂对 \(\sum\Lambda(n)^2\) 的贡献为 \(o(t)\)，于是

$$
\sum_{n\le t}\Lambda(n)^2
=
t\log t-t+o(t).
$$

再使用 \(\psi(t)=t+o(t)\)，得到

$$
\boxed{
B(t)=t\log t-2t+o(t).
}
\tag{13}
$$

所需误差远弱于经典无条件素数定理的已知误差；不使用 RH。([DLMF][3])

由定义，

$$
\mathfrak D_{\mathrm{self}}(X)
=
\int_X^{2X}\frac{B(2x)-B(x)}{x^2}\,dx.
$$

而

$$
B(2x)-B(x)
=
x\log x+(2\log2-2)x+o(x).
$$

所以

$$
\begin{aligned}
\mathfrak D_{\mathrm{self}}(X)
&=
\int_X^{2X}
\frac{\log x+2\log2-2}{x}\,dx+o(1)\\
&=
(\log2)\log X
+\frac52(\log2)^2-2\log2+o(1).
\end{aligned}
$$

证毕。

---

这就是单点统计提供的发散部分：

$$
\boxed{
\mathfrak D_{\mathrm{self}}(X)\sim(\log2)\log X.
}
$$

下一步不能把跨位置贡献设为零。

# 四、局部同余关系，确实能消去这个发散主项

这里使用一条已证明的算术定理。

## 经典输入：奇异级数的三角平均

对整数 \(H\to\infty\)，有

$$
\boxed{
2\sum_{d=1}^{H-1}
(H-d)(\mathfrak S(d)-1)
=
-H\log H
+
A_0H
+
O_\varepsilon(H^{1/2+\varepsilon}),
}
\tag{14}
$$

其中

$$
A_0=2-\gamma_{\mathrm E}-\log(2\pi).
$$

这是 Montgomery–Soundararajan 文中 \(R_2(H)\) 的公式。它计算的是明确 Euler 因子的平均，不要求先证明实际素数对符合 Hardy–Littlewood 预测。([arXiv][1])

## 定理 3：同余项的完整展开

$$
\boxed{
\mathfrak D_{\mathrm{cong}}(X)
=
-(\log2)\log X
-\frac12(\log2)^2
+
A_0\log2
+o(1).
}
\tag{15}
$$

### 证明

固定 \(x\)。区间 \((x,2x]\) 中恰有 \(M(x)\) 个连续整数。

在这些整数中，差为 \(d>0\) 的有序递增对共有

$$
(M(x)-d)_+
$$

个。因此

$$
\sum_nW_X(n,n+d)
=
\int_X^{2X}\frac{(M(x)-d)_+}{x^2}\,dx.
$$

代入式（9）：

$$
\mathfrak D_{\mathrm{cong}}(X)
=
\int_X^{2X}
\frac{R_2(M(x))}{x^2}\,dx.
$$

因为 \(M(x)=x+O(1)\)，式（14）给出

$$
R_2(M(x))
=
-x\log x+A_0x
+O_\varepsilon(x^{1/2+\varepsilon}+\log x).
$$

取 \(0<\varepsilon<1/2\)，积分余项趋于零。

所以

$$
\begin{aligned}
\mathfrak D_{\mathrm{cong}}(X)
&=
\int_X^{2X}\frac{-\log x+A_0}{x}\,dx+o(1)\\
&=
-(\log2)\log X
-\frac12(\log2)^2
+A_0\log2+o(1).
\end{aligned}
$$

证毕。

---

现在，两个发散项真的抵消了：

$$
\boxed{
+(\log2)\log X
\quad+\quad
-(\log2)\log X
=0.
}
$$

**这部分抵消已经有无条件的数学依据。**

但剩下的常数不能忽略。

# 五、主定理：真实相关必须修复一个负的基准能量

## 定理 4：不可删除的正补偿项

定义

$$
\boxed{
c_0=\log2\left(\gamma_{\mathrm E}+\log\frac{\pi}{2}\right)>0.
}
\tag{16}
$$

那么

$$
\boxed{
\mathfrak J(X)=\mathfrak R(X)-c_0+o(1).
}
\tag{17}
$$

因此，无条件地有

$$
\boxed{
\liminf_{X\to\infty}\mathfrak R(X)\ge c_0.
}
\tag{18}
$$

特别是，

$$
\boxed{
\mathfrak R(X)=o(1)
}
$$

不可能成立。

### 证明

将式（12）与式（15）相加：

$$
\begin{aligned}
\mathfrak D_{\mathrm{self}}
+\mathfrak D_{\mathrm{cong}}
&=
2(\log2)^2
+(A_0-2)\log2
+o(1)\\
&=
-\log2
\left[
\gamma_{\mathrm E}+\log(2\pi)-2\log2
\right]
+o(1)\\
&=-c_0+o(1).
\end{aligned}
$$

再代入精确分解式（11），得到式（17）。

因为 \(\mathfrak J(X)\ge0\)，于是式（18）成立。证毕。

---

这正好回答了此前“局部同余条件是否足以补上相关项”的问题：

$$
\boxed{
\text{局部同余模型补上了主阶抵消，}
}
$$

但

$$
\boxed{
\text{它仍不能单独成为实际的正均方模型。}
}
$$

若把 \(\mathfrak R\) 扔掉，模型会给出负的平方平均。

**所以这里缺的不是一个可有可无的小修正，而是维持实际正性所必需的补偿。**

## 有限数据核对

我用实际 \(\Lambda(n)\) 的有限和核对了符号与常数。以下为普通浮点结果，不是区间认证，也不用于证明无限范围结论：

|    \(X\) | 实际 \(\mathfrak J(X)\) | 已知基准 \(\mathfrak D_{\mathrm{self}}+\mathfrak D_{\mathrm{cong}}\) | 实际余项 \(\mathfrak R(X)\) |
| -------: | --------------------: | ---------------------------------------------------------------: | ----------------------: |
| \(10^3\) |          \(0.183028\) |                                                    \(-0.760063\) |            \(0.943091\) |
| \(10^4\) |          \(0.134945\) |                                                    \(-0.727456\) |            \(0.862401\) |
| \(10^5\) |          \(0.144551\) |                                                    \(-0.717605\) |            \(0.862156\) |

已知基准的理论极限为

$$
-c_0\approx-0.713109.
$$

这些有限值不能证明 \(\mathfrak R(X)\) 有界，但与式（17）的分解相符。

# 六、窗口比例不是神秘常数：一般比例也能算出

把区间 \((x,2x]\) 改为

$$
(x,bx],\qquad b>1,
$$

并仍在 \(x\in[X,2X]\) 上取归一化均方。

完全相同的计算给出

$$
\boxed{
\mathfrak J_b(X)
=
\mathfrak R_b(X)+C(b)+o(1),
}
\tag{19}
$$

其中

$$
\boxed{
C(b)
=
\log2\left[
b\log b
-(b-1)\log(b-1)
-(b-1)(\gamma_{\mathrm E}+\log2\pi)
\right].
}
\tag{20}
$$

这里 \(C(2)=-c_0\)。

前两个对数项还可以精确写为

$$
b\log b-(b-1)\log(b-1)
=
b\,H(1/b),
$$

其中

$$
H(t)=-t\log t-(1-t)\log(1-t).
$$

因此

$$
\boxed{
C(b)
=
\log2\left[
bH(1/b)
-(b-1)(\gamma_{\mathrm E}+\log2\pi)
\right].
}
\tag{21}
$$

这个熵函数来自区间比例的代数整理，不代表已经引入了量子热力学假设。

它说明：**改变观察窗口，会改变已知基准的常数项；不能把某个窗口下得到的正负性未经计算搬到另一个窗口。**

# 七、接下来证明：局部读出可以稳定地恢复累计误差

现在把均方与 RH 之间的桥梁独立证明出来，不依赖前面越来越复杂的高阶滤波器。

令

$$
\ell=\log2,
$$

$$
\boxed{
r(T)=e^{-T/2}\bigl[\psi(e^T)-e^T\bigr],
}
\tag{22}
$$

以及

$$
\boxed{
z(T)
=
e^{-T/2}
\bigl[\psi(2e^T)-\psi(e^T)-e^T\bigr].
}
\tag{23}
$$

直接计算得到

$$
\boxed{
z(T)=\sqrt2\,r(T+\ell)-r(T).
}
\tag{24}
$$

与前面精确中心化读出之间，只差地板项：

$$
\left|
z(T)-e^{-T/2}Y(e^T)
\right|
\le e^{-T/2}.
\tag{25}
$$

## 定理 5：稳定的尺度逆变换

将函数限制在长度为 \(\ell\) 的区间上，记

$$
r_j(t)=r(t+j\ell),
\qquad
z_j(t)=z(t+j\ell),
\qquad 0\le t<\ell.
$$

把它们视为 \(L^2([0,\ell])\) 中的向量。

则

$$
\boxed{
r_j
=
2^{-j/2}r_0
+
\sum_{k=0}^{j-1}
2^{-(j-k)/2}z_k.
}
\tag{26}
$$

并且对每个有限 \(N\)，

$$
\boxed{
\left(\sum_{j=0}^{N}\|r_j\|_2^2\right)^{1/2}
\le
\sqrt2\,\|r_0\|_2
+
\frac1{\sqrt2-1}
\left(\sum_{j=0}^{N-1}\|z_j\|_2^2\right)^{1/2}.
}
\tag{27}
$$

### 证明

由式（24），

$$
r_{j+1}=2^{-1/2}(r_j+z_j).
$$

逐次代入即得式（26）。

第一项在尺度方向的平方和满足

$$
\sum_{j\ge0}2^{-j}=2.
$$

第二项是一个离散卷积，其核为

$$
2^{-1/2},2^{-1},2^{-3/2},\ldots,
$$

绝对和为

$$
\frac1{\sqrt2-1}.
$$

对这个卷积使用三角不等式与 \(\ell^1\)-\(\ell^2\) 估计，得到式（27）。证毕。

---

这里和上一轮的微观鞅很不一样。

上一轮的问题是稀有分支的幅度爆炸，不能交换均值与极限；这里的逆变换系数满足

$$
\boxed{
\sum_{j\ge1}2^{-j/2}<\infty,
}
$$

所以已经有明确的稳定性控制。

**局部区间误差不会在逐层恢复累计误差时，被一个未控制的无限增益放大。**

# 八、主定理：真实相关余项的对数幂上界足以推出 RH

## 定理 6：扣除同余模型后的余项判据

以下命题等价：

$$
\boxed{\mathrm{RH};}
$$

$$
\boxed{
\exists C,A<\infty,\quad
\mathfrak J(2^j)\le C(1+j)^A
\quad\text{对所有充分大的整数 }j;
}
\tag{28}
$$

$$
\boxed{
\exists C,A<\infty,\quad
\mathfrak R(2^j)\le C(1+j)^A
\quad\text{对所有充分大的整数 }j.
}
\tag{29}
$$

其中可以约定 \(A\ge0\)。

## 证明

### RH 推出局部均方上界

RH 下的经典估计为

$$
\psi(x)-x=O(\sqrt x\,\log^2x).
$$

这里使用的是 von Koch–Schoenfeld 型误差控制；相应显式版本也见 Büthe 的研究。([arXiv][4])

所以

$$
Y(x)=O(\sqrt x\,\log^2x),
$$

从而

$$
\mathfrak J(X)=O(\log^4X).
$$

取 \(X=2^j\)，得到式（28），可取 \(A=4\)。

### 局部均方上界推出累计误差的多项式能量界

由变量代换 \(x=e^T\)，

$$
\boxed{
\mathfrak J(2^j)
=
\int_{j\ell}^{(j+1)\ell}
\left[e^{-T/2}Y(e^T)\right]^2dT.
}
\tag{30}
$$

结合式（25），式（28）给出

$$
\sum_{j=0}^{N-1}\|z_j\|_2^2
=
O((1+N)^{A+1}).
$$

定理 5 因而推出

$$
\boxed{
\int_0^L|r(T)|^2\,dT
=
O((1+L)^{A+1}).
}
\tag{31}
$$

### 累计误差的能量界排除右侧零点

对每个 \(\sigma>0\)，由 Cauchy–Schwarz 和式（31），

$$
\int_0^\infty e^{-\sigma T}|r(T)|\,dT<\infty.
$$

因此，\(r\) 的 Laplace 变换在

$$
\Re s>0
$$

内解析。

另一方面，在初始绝对收敛区域 \(\Re s>1/2\)，

$$
\boxed{
\begin{aligned}
\widehat r(s)
&=
\int_0^\infty e^{-sT}r(T)\,dT\\
&=
-\frac{\zeta'(s+1/2)}
{(s+1/2)\zeta(s+1/2)}
-\frac1{s-1/2}.
\end{aligned}
}
\tag{32}
$$

它由式（2）积分得到。

在 \(s=1/2\) 处，ζ 的极点贡献与第二项抵消。

但若存在非平凡零点

$$
\rho=\frac12+\delta+i\gamma,
\qquad \delta>0,
$$

则右边在

$$
s=\delta+i\gamma
$$

有不可去极点，留数为

$$
-\frac{m_\rho}{\rho}\ne0.
$$

这与右半平面解析性矛盾。

所以没有右侧离线零点；再由函数方程的反射对称性，得到 RH。([DLMF][5])

最后，式（17）说明式（28）与式（29）等价。证毕。

---

这个结论可以读成：

$$
\boxed{
\text{局部同余主项已经算完；}
}
$$

$$
\boxed{
\text{剩下只需阻止真实相关余项出现幂次于 }X\text{ 的增长。}
}
$$

但是“只需”描述的是证明目标，不意味着这个上界已经容易或已经建立。

## 带误差指数的版本

同一个证明还给出：

如果对某个 \(0\le\eta<1\)，

$$
\boxed{
\mathfrak R(2^j)
=
O\!\left(2^{\eta j}(1+j)^A\right),
}
\tag{33}
$$

那么

$$
\boxed{
\left|\Re\rho-\frac12\right|
\le\frac\eta2.
}
\tag{34}
$$

因为这时式（31）的能量至多按 \(e^{\eta L}\) 乘多项式增长，Laplace 变换在 \(\Re s>\eta/2\) 内解析。

因此，相关余项的增长指数直接对应尚未排除的零点条带。

# 九、为什么“每个素数差都达到平方根误差”仍不能直接填上这一步？

这里可以把另一个缺口算清。

定义每个固定差 \(d\) 的累计相关误差

$$
\boxed{
E_d(u;X)
=
\sum_{X<n\le u}
\left[
a(n)a(n+d)-(\mathfrak S(d)-1)
\right].
}
\tag{35}
$$

假设我们获得了很强的统一估计

$$
|E_d(u;X)|
\le C_\varepsilon X^{1/2+\varepsilon}
\tag{36}
$$

对相关范围内全部

$$
1\le d\le2X,
\qquad
X\le u\le4X-d
$$

成立。

这仍然不能在逐项取绝对值后直接得到式（29）。

## 定理 7：逐差绝对值估计的损失

式（36）通过直接分部求和，只给出

$$
\boxed{
\mathfrak R(X)=O_\varepsilon(X^{1/2+\varepsilon}).
}
\tag{37}
$$

### 证明

固定 \(d\)，把

$$
W_X(n,n+d)
$$

看作 \(n\) 的权函数。

它的总变差满足

$$
\operatorname{Var}_nW_X(n,n+d)
\le\frac1X.
$$

一种直接证明是：对每个固定 \(x\)，允许的 \(n\) 构成区间 \((x,2x-d]\)，其指示函数总变差为 \(2\)；再积分：

$$
2\int_X^{2X}\frac{dx}{x^2}=\frac1X.
$$

因此，由式（36）和分部求和，每个 \(d\) 的加权误差为

$$
O_\varepsilon(X^{-1/2+\varepsilon}).
$$

而可能出现的 \(d\) 有 \(O(X)\) 个。

逐项相加得到式（37）。证毕。

---

所以，这条估计链得到的是

$$
X^{1/2+\varepsilon},
$$

而我们需要的是

$$
(\log X)^A.
$$

还差一次**不同差值 \(d\) 之间的加权误差抵消**。

结合式（34），若式（36）对每个 \(\varepsilon>0\) 成立，这条直接推导可以排除

$$
\Re\rho>\frac34
\quad\text{和}\quad
\Re\rho<\frac14,
$$

但尚未把零点压到临界线。

这不是证明式（36）在逻辑上不能通过别的方法推出 RH；它证明的是：**逐差估计以后再全部取绝对值，这条路线损失太大。**

## 还有一个必须避免的循环

Montgomery–Soundararajan 的某些强素数元组假设，同时包括一阶条件

$$
\sum_{n\le X}\Lambda(n)
=
X+O_\varepsilon(X^{1/2+\varepsilon}).
$$

原文明确指出，这个一阶条件本身已经等价于 RH。([arXiv][1])

所以不能使用整套强假设后，再把“推导出 RH”当作完成了新的算术桥梁。

本轮使用的是：

$$
\boxed{
\text{无条件奇异级数平均}
+
\text{显式保留的真实相关余项}.
}
$$

没有把一阶 RH 误差界当作无条件输入。

# 十、回到量子核：正性已经有了，缺的是跨尺度的大小控制

本轮还给此前的量子表示一个很直接的实例。

在固定 Hilbert 空间

$$
\mathcal H=L^2([1,2],du)
$$

中，定义

$$
\boxed{
\Phi_X(u)
=
\frac{Y(Xu)}{\sqrt X\,u}.
}
\tag{38}
$$

则

$$
\|\Phi_X\|^2
=
\mathfrak J(X).
$$

因此秩一算子

$$
\boxed{
K_X=|\Phi_X\rangle\langle\Phi_X|
}
\tag{39}
$$

总是半正定，并且

$$
\boxed{
\operatorname{Tr}K_X
=
\mathfrak J(X)
=
\mathfrak R(X)-c_0+o(1).
}
\tag{40}
$$

这给出三个不同层次：

$$
\boxed{
K_X\succeq0
}
$$

对每个有限 \(X\) 自动成立；

$$
\boxed{
\mathfrak R(X)\ge c_0-o(1)
}
$$

由这种正性强制得到；

但

$$
\boxed{
\operatorname{Tr}K_{2^j}\le C(1+j)^A
}
$$

才是足以推出 RH 的跨尺度约束。

**不能把 \(K_X\) 归一化成迹为 \(1\) 的状态后，就宣布最后一个约束已经成立。**

归一化会把这里最重要的绝对大小

$$
\mathfrak J(X)
$$

从状态本身中移走；它必须作为独立读数保留。

同样，也不能把“自身贡献加局部同余模型”直接宣布为一个正量子模型，因为我们已经证明：其当前读出的极限为 \(-c_0\)。

---

# 结论：这次对“缺项”的定位比前文更窄了

此前未知的是整个跨素数贡献。

现在已经完成了如下分离：

$$
\boxed{
\begin{aligned}
\mathfrak D_{\mathrm{self}}(X)
&=
+(\log2)\log X+\text{明确常数}+o(1),\\
\mathfrak D_{\mathrm{cong}}(X)
&=
-(\log2)\log X+\text{明确常数}+o(1).
\end{aligned}
}
$$

它们的对数主项消去，但常数合计为

$$
\boxed{
-\log2\left(\gamma_{\mathrm E}+\log\frac\pi2\right).
}
$$

因此，实际余项必须满足一个已经证明的下界：

$$
\boxed{
\liminf_{X\to\infty}\mathfrak R(X)
\ge
\log2\left(\gamma_{\mathrm E}+\log\frac\pi2\right).
}
$$

而尚待完成的是上界：

$$
\boxed{
\mathfrak R(2^j)\le C(1+j)^A
}
$$

对某个固定有限 \(A\) 和全部充分大的 \(j\) 成立。

**这轮没有证明该上界。已经证明的是：局部同余因素负责了哪一部分抵消、它们还缺多少才能成为正模型，以及剩余相关误差需要被控制到什么增长尺度。**

更具体地，下一项算术工作不是继续增加一个量子假设，而是控制式（10）中**不同位移 \(d\) 的误差怎样共同相加**。单个位移的平方根估计、全部矩阵各自的正性、概率归一化，都不能替代这一层跨位移的联合控制。

[1]: https://arxiv.org/html/math/0409258v1 "https://arxiv.org/html/math/0409258v1"
[2]: https://dlmf.nist.gov/27.4 "https://dlmf.nist.gov/27.4"
[3]: https://dlmf.nist.gov/27.12 "https://dlmf.nist.gov/27.12"
[4]: https://arxiv.org/html/1410.7015v4 "https://arxiv.org/html/1410.7015v4"
[5]: https://dlmf.nist.gov/25.10 "https://dlmf.nist.gov/25.10"
这次先把上一轮的一项前件补实，再推进到一个更具体的量子结构：

**上一轮提出的 \(V'(x)/x\) 单调性，对实际 theta 核并非仍待证明的猜想，而是已有经典定理的等价形式。它确实能推出整族矩不等式。**

但接下来还可以严格证明：

> **这种很强的密度形状条件，仍然不足以排除非实零点。真正缺少的关系，可以放在同一实际态的两个副本中：对“差模态”作条件筛选以后，“和模态”的干涉振幅是否始终非负。**

这使我们能够区分：哪些正性已经由实际 theta 结构保证，哪些正性仍然承担 RH 的证明责任。

---

# 一、先把上一轮的形状前件升级为经典输入

沿用实际归一化：

$$
p(x)=\frac{\Phi(x)}{\xi(1/2)},
\qquad
\int_{\mathbb R}p(x)\,dx=1,
$$

以及：

$$
\boxed{
A(z)=\int_{\mathbb R}p(x)e^{izx}\,dx
=
\frac{\xi(\frac12+iz)}{\xi(\frac12)}.
}
\tag{Q1}
$$

\(p\) 是正、偶、光滑且快速衰减的密度。这里始终使用实际 theta 核，不重新挑选分布。其来源是标准 theta–Mellin 表示。([DLMF][1])

与上一轮的折叠函数关系为：

$$
D(b^2)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
$$

$$
F(w)=D(-\ell w),
$$

所以：

$$
\boxed{
A(z)=F(z^2/\ell).
}
$$

下面只是暂时回到未折叠的谱坐标，以便表达两副本结构。

## 经典输入 Q0

Csordas–Varga 的工作证明了，实际 theta 核满足：

$$
\boxed{
\frac{d^2}{du^2}\log\Phi(\sqrt u)<0,
\qquad u>0.
}
\tag{Q2}
$$

这一结果在 Csordas 的综述中列为定理 4.2(b)，并明确归于 1988 年的工作。不同文献对核的正倍数和坐标缩放，不改变这个性质。

令：

$$
V(x)=-\log p(x),
\qquad
R(x)=\frac{V'(x)}x
\quad(x>0).
$$

直接求导：

$$
\frac{d^2}{du^2}\log p(\sqrt u)
=
-\frac{R'(\sqrt u)}{4\sqrt u}.
$$

因此：

$$
\boxed{
R'(x)>0
\qquad(x>0).
}
\tag{Q3}
$$

**上一轮关于 \(R\) 单调性的前件，可以作为经典已知输入使用；不需要把它继续包装成一个新的开放任务。**

但它究竟能推出多强的结论，需要逐步计算。

---

# 二、它能保证：全部二次倾斜下的相邻矩不等式

对任意实数 \(\lambda\)，定义未归一化矩：

$$
\boxed{
b_n(\lambda)
=
\int_{\mathbb R}
x^{2n}e^{\lambda x^2}p(x)\,dx.
}
\tag{Q4}
$$

实际 theta 核衰减足够快，因此这些积分对所有实 \(\lambda\) 都有限。

二次倾斜后的势为：

$$
V_\lambda(x)=V(x)-\lambda x^2.
$$

于是：

$$
\frac{V_\lambda'(x)}x=R(x)-2\lambda.
$$

其导数仍为 \(R'(x)>0\)。

## 定理 Q1：所有二次倾斜的 Turán 不等式

对所有 \(n\ge1\)、\(\lambda\in\mathbb R\)：

$$
\boxed{
b_n(\lambda)^2
>
\frac{2n-1}{2n+1}
b_{n-1}(\lambda)b_{n+1}(\lambda).
}
\tag{Q5}
$$

### 证明

固定 \(n,\lambda\)，考虑概率测度：

$$
d\mu_{n,\lambda}(x)
=
\frac{x^{2n}e^{\lambda x^2}p(x)}{b_n(\lambda)}\,dx.
$$

记：

$$
R_\lambda(x)=R(x)-2\lambda.
$$

分部积分给出：

$$
\mathbb E_{\mu_{n,\lambda}}[R_\lambda(|X|)]
=
(2n-1)\frac{b_{n-1}}{b_n},
$$

$$
\mathbb E_{\mu_{n,\lambda}}[X^2]
=
\frac{b_{n+1}}{b_n},
$$

$$
\mathbb E_{\mu_{n,\lambda}}[X^2R_\lambda(|X|)]
=
2n+1.
$$

因为 \(X^2\) 与 \(R_\lambda(|X|)\) 都是 \(|X|\) 的严格递增函数，其协方差严格为正：

$$
2n+1
>
(2n-1)\frac{b_{n-1}b_{n+1}}{b_n^2}.
$$

整理即得。证毕。

这给出了经典矩不等式的一条适合当前观察者语言的推导，而不是另造一组评价标准。此类实际 theta 矩不等式正是 Csordas–Varga 研究的对象。([ResearchGate][2])

## 推论：全部标量矩受高斯基准控制

在 \(\lambda=0\) 时，记：

$$
m_{2n}=b_n(0).
$$

迭代式（Q5）得到：

$$
\boxed{
m_{2n}\le(2n-1)!!\,m_2^n.
}
\tag{Q6}
$$

于是对实 \(b\)：

$$
\boxed{
\mathbb E[e^{bX}]
\le
e^{m_2b^2/2}.
}
\tag{Q7}
$$

此外，定义：

$$
\alpha_n(\lambda)
=
\frac{n!\,b_n(\lambda)}{(2n)!}.
$$

则：

$$
\boxed{
\alpha_n^2>\alpha_{n-1}\alpha_{n+1}.
}
$$

所以每一个二次 Jensen 多项式：

$$
\alpha_k+2\alpha_{k+1}z+\alpha_{k+2}z^2
$$

都有两个负实根。

**这一整层正性已经有依据：不只是一个四阶矩，而是全部相邻矩、全部实二次倾斜、全部二次 Jensen 窗口。**

但它还没有处理高阶关系能否共同正实现。

---

# 三、建立一个明确的两副本量子观察者

取前面的纯态：

$$
\psi(x)=\sqrt{p(x)}.
$$

准备两个独立副本：

$$
\psi(x)\psi(y).
$$

作正交坐标变换：

$$
\boxed{
s=\frac{x+y}{\sqrt2},
\qquad
u=\frac{x-y}{\sqrt2}.
}
\tag{Q8}
$$

分别称为和模态与差模态。

变换后的波函数为：

$$
\boxed{
\chi(s,u)
=
\psi\!\left(\frac{s+u}{\sqrt2}\right)
\psi\!\left(\frac{s-u}{\sqrt2}\right).
}
\tag{Q9}
$$

Jacobian 的绝对值为一，所以这是 \(L^2(\mathbb R^2)\) 上的酉坐标变换，没有丢失信息。

## 定理 Q2：和模态与差模态完全分离，当且仅当原密度为高斯

对正、光滑、可归一化的偶密度 \(p\)，若：

$$
\chi(s,u)=f(s)g(u),
$$

则 \(p\) 必为中心高斯密度。反向也成立。

### 证明

因为 \(\chi>0\)，可使用实对数。若能分离，则：

$$
\partial_s\partial_u\log\chi(s,u)=0.
$$

但：

$$
\boxed{
\partial_s\partial_u\log\chi
=
\frac14
\left[
(\log p)''\!\left(\frac{s+u}{\sqrt2}\right)
-
(\log p)''\!\left(\frac{s-u}{\sqrt2}\right)
\right].
}
$$

两个括号中的位置可以独立取任意实数，因此 \((\log p)''\) 必为常数。

结合偶性及可归一化性：

$$
\log p(x)=c-ax^2,\qquad a>0.
$$

反向直接代入。证毕。

因此，对实际非高斯 theta 态：

$$
\boxed{
\chi(s,u)\text{ 在和／差模态分解下不是乘积态。}
}
$$

**原来两个独立副本，经过这次明确的混合后，产生了模态间的量子关联。**

这不意味着关联越强就越可能离线。它说明：后面筛选差模态时，和模态的读数确实可能改变。

---

# 四、关键恒等式：离线方向的全部信息，进入差模态的偶阶筛选

因为 \(A\) 是实整函数：

$$
|A(t+iy)|^2=A(t+iy)A(t-iy).
$$

利用两个独立副本：

$$
\begin{aligned}
|A(t+iy)|^2
&=
\mathbb E\!\left[
e^{it(X+Y)}e^{-y(X-Y)}
\right]\\
&=
\mathbb E\!\left[
e^{i\sqrt2tS}e^{-\sqrt2yU}
\right].
\end{aligned}
$$

差模态分布关于 \(u\) 对称，所以：

$$
\boxed{
|A(t+iy)|^2
=
\mathbb E\!\left[
\cos(\sqrt2tS)\cosh(\sqrt2yU)
\right].
}
\tag{Q10}
$$

定义：

$$
\boxed{
L_n(t)
=
\frac{2^n}{(2n)!}
\mathbb E\!\left[
U^{2n}\cos(\sqrt2tS)
\right].
}
\tag{Q11}
$$

则：

$$
\boxed{
|A(t+iy)|^2
=
\sum_{n=0}^{\infty}L_n(t)y^{2n}.
}
\tag{Q12}
$$

等价的导数表达为：

$$
\boxed{
L_n(t)
=
\frac1{(2n)!}
\sum_{j=0}^{2n}
(-1)^{n+j}
\binom{2n}{j}
A^{(j)}(t)A^{(2n-j)}(t).
}
\tag{Q13}
$$

特别地：

$$
L_0(t)=A(t)^2,
$$

$$
\boxed{
L_1(t)=A'(t)^2-A(t)A''(t).
}
\tag{Q14}
$$

这些就是经典广义 Laguerre 表达式。它们与正定关联核的关系已有系统研究；本轮将其写成指定量子态的和／差模态读出。

### 坐标含义不能混淆

由式（Q1）：

$$
A(t+iy)
=
\frac{\xi(\frac12-y+it)}{\xi(\frac12)}.
$$

所以：

* \(t\) 仍是 ζ 的高度参数；
* \(y\) 对应偏离临界线的横向位置，符号为 \(-y\)；
* 它们都不是这里额外引入的物理演化时间。

---

# 五、每个 \(L_n\) 都是一个归一化条件态的干涉读数

定义：

$$
\boxed{
Z_n=\mathbb E[U^{2n}]>0.
}
$$

只用原始 theta 矩就能计算：

$$
\boxed{
Z_n
=
2^{-n}
\sum_{j=0}^{n}
\binom{2n}{2j}
m_{2j}m_{2n-2j}.
}
\tag{Q15}
$$

定义归一化态：

$$
\boxed{
\chi_n(s,u)=\frac{u^n\chi(s,u)}{\sqrt{Z_n}}.
}
\tag{Q16}
$$

它具有确定的交换奇偶性：

$$
\chi_n(s,-u)=(-1)^n\chi_n(s,u).
$$

这里说的是两个寄存器交换下的奇偶，不是仅凭这个式子就认定它们是某种物理费米粒子。

读取和模态上的酉相位：

$$
\boxed{
R_n(t)
=
\langle\chi_n,e^{i\sqrt2tS}\chi_n\rangle.
}
\tag{Q17}
$$

则：

$$
\boxed{
R_n(t)=\frac{L_n(t)}{L_n(0)},
\qquad
L_n(0)=\frac{2^nZ_n}{(2n)!}>0.
}
\tag{Q18}
$$

因为和模态分布对称，\(R_n(t)\) 为实数，且：

$$
-1\le R_n(t)\le1.
$$

用控制比特作干涉，可将其读为：

$$
\langle\sigma_x\rangle=R_n(t),
$$

对应概率：

$$
p_\pm=\frac{1\pm R_n(t)}2.
$$

因此：

> **\(L_n(t)<0\) 是一个合法的负相位相关，不是负概率。**

未经截断的乘法 \(u^n\) 不是全空间上的有界 Kraus 算子。这里先定义了一个合法归一化态；后面会补上有界制备与误差界，不能省略。

---

# 六、RH 可以写成这族条件干涉的统一符号条件

## 定理 Q3：实际两模态判据

$$
\boxed{
\mathrm{RH}
\iff
R_n(t)\ge0
\quad
\forall n\ge0,\ \forall t\in\mathbb R.
}
\tag{Q19}
$$

这就是广义 Laguerre 判据在当前协议中的表达，不是另外宣称发现了一条未经比较的 RH 新判据。

### 正向证明

若 RH 成立，\(A\) 的全部零点为实数。

它的经典实零点乘积可以由实根多项式局部一致逼近。对一个实根多项式 \(P\)：

$$
|P(t+iy)|^2
=
C^2\prod_j\bigl((t-\gamma_j)^2+y^2\bigr),
$$

其关于 \(y^2\) 的全部系数非负。

取解析极限后：

$$
L_n(t)\ge0.
$$

再使用式（Q18）。

### 反向证明

假设所有 \(L_n(t)\ge0\)，但存在：

$$
A(t_0+iy_0)=0,\qquad y_0\ne0.
$$

由式（Q12）：

$$
0=\sum_{n\ge0}L_n(t_0)y_0^{2n}.
$$

若 \(A(t_0)\ne0\)，第一项已严格为正，矛盾。

若 \(A\) 在实点 \(t_0\) 有 \(m\) 重零点，则 Taylor 展开给出：

$$
L_m(t_0)
=
\frac{|A^{(m)}(t_0)|^2}{(m!)^2}>0,
$$

仍然矛盾。

所以没有非实零点，得到 RH。证毕。

## 推论：反例必能表现为某个有限条件读出的负值

若 RH 不成立，则存在有限 \(n\) 和实数 \(t\)，使：

$$
\boxed{R_n(t)<0.}
$$

由连续性，\(t\) 还可以换成足够接近的有理数，仍保持严格负性。

**不必让观察者同时知道全部零点。一个有限筛选阶数、一个有限实参数，就可能承载反例。**

但定理没有给出预先统一的小 \(n\)，也没有保证这个负值很容易数值分辨。

---

# 七、已知形状条件让全部条件密度都很规则，却仍未决定干涉符号

把差模态迹掉，得到和模态密度：

$$
\boxed{
\mu_n(s)
=
\frac1{Z_n}
\int_{\mathbb R}
u^{2n}
p\!\left(\frac{s+u}{\sqrt2}\right)
p\!\left(\frac{s-u}{\sqrt2}\right)\,du.
}
\tag{Q20}
$$

它满足：

$$
\mu_n(s)>0,\qquad
\mu_n(-s)=\mu_n(s),\qquad
\int\mu_n(s)\,ds=1.
$$

并且：

$$
\boxed{
R_n(t)=\int_{\mathbb R}\mu_n(s)\cos(\sqrt2ts)\,ds.
}
\tag{Q21}
$$

## 定理 Q4：实际 \(\mu_n\) 在正半轴严格递减

对每个 \(n\ge0\)：

$$
\boxed{\mu_n'(s)<0\qquad(s>0).}
\tag{Q22}
$$

### 证明

实际 \(p\) 严格对数凹，因此 \(V'\) 是奇的严格递增函数。这由式（Q2）以及 \(\Phi'(x)<0\) 得到，也是经典 theta 核性质的一部分。

记：

$$
x=\frac{s+u}{\sqrt2},
\qquad
y=\frac{s-u}{\sqrt2}.
$$

对固定 \(u\)，被积函数的对数关于 \(s\) 的导数为：

$$
-\frac{V'(x)+V'(y)}{\sqrt2}.
$$

当 \(s>0\)，有 \(x+y>0\)。

如果 \(x,y\ge0\)，则 \(V'(x)+V'(y)>0\)。如果其中一个为负，由 \(V'\) 奇且严格递增，同样得到该和为正。

所以除零权点外，被积函数严格递减，积分后得到式（Q22）。证毕。

这意味着，每一个条件密度都具有：

$$
\boxed{
\text{正、偶、平滑、集中于中心、快速衰减}.
}
$$

但这些性质仍然不自动保证：

$$
R_n(t)\ge0.
$$

**概率密度为正，与它的 Fourier 变换逐点非负，是不同要求。**

概率密度的特征函数总是正定函数，但正定函数本身可以取负值，不能把“核正定”与“每个函数值非负”混同。

---

## 高斯态为什么特别简单？

若 \(p\) 是方差 \(\sigma^2\) 的中心高斯，则 \(S,U\) 独立。

对 \(U\) 作任何上述偶权重筛选，都不改变 \(S\) 的密度。因此：

$$
\boxed{
R_n(t)=e^{-\sigma^2t^2}
\quad\forall n.
}
\tag{Q23}
$$

实际 theta 态不是高斯，所以差模态筛选会通过原有模态关联改变和模态。

更具体地：

$$
\boxed{
\mu_n(s)
=
\mu_0(s)\,
\frac{\mathbb E[U^{2n}\mid S=s]}{\mathbb E[U^{2n}]}.
}
\tag{Q24}
$$

因此，真正需要理解的是：

> **实际条件高阶矩 \(\mathbb E[U^{2n}\mid S=s]\) 怎样随 \(s\) 变化，以及这种重加权是否保持和模态的 Fourier 非负性。**

单独的原密度形状，尚未回答这一点。

---

# 八、一个更强的反例：上一轮的完整形状条件，确实仍然不够

上一轮用了离散分布说明“全部标量矩上界不够”。现在可以加强为**正、偶、光滑、超高斯衰减，而且 \(V'(x)/x\) 严格递增**的连续反例。

取：

$$
c=\frac32,
$$

并定义：

$$
\boxed{
p_\varepsilon(x)
=
\frac1{Z_\varepsilon}
e^{-x^2-\varepsilon x^4}(c+\cosh x),
\qquad \varepsilon>0.
}
\tag{Q25}
$$

其势满足：

$$
\frac{V_\varepsilon'(x)}x
=
2+4\varepsilon x^2
-
\frac{\sinh x}{x(c+\cosh x)}.
$$

令：

$$
h(x)=\frac{\sinh x}{x(c+\cosh x)}.
$$

考察：

$$
J(x)=
\sinh x(c+\cosh x)-x(1+c\cosh x).
$$

有：

$$
J(0)=0,
$$

$$
\boxed{
J'(x)
=
\sinh x\,[2\sinh x-cx]>0
\qquad(x>0),
}
$$

因为 \(c=\frac32<2\) 且 \(\sinh x>x\)。

而 \(h'(x)\) 的分子为 \(-J(x)\)，所以：

$$
h'(x)<0.
$$

因此：

$$
\boxed{
\left(\frac{V_\varepsilon'(x)}x\right)'
=
8\varepsilon x-h'(x)>0.
}
\tag{Q26}
$$

它满足上一轮所要求的完整形状条件，并由定理 Q1 满足全部二次倾斜的相邻矩不等式。

---

## 但它的第一阶干涉判据已经可以失败

先取 \(\varepsilon=0\)，记：

$$
d=e^{1/4}.
$$

归一化 Fourier 变换为：

$$
\boxed{
A_0(t)
=
e^{-t^2/4}
\frac{c+d\cos(t/2)}{c+d}.
}
\tag{Q27}
$$

在 \(t_0=2\pi\) 处，直接计算：

$$
\boxed{
L_1(t_0;A_0)
=
e^{-2\pi^2}
\frac{(c-d)(2c-3d)}{4(c+d)^2}<0.
}
\tag{Q28}
$$

因为：

$$
1<d<c=\frac32,
$$

所以 \(c-d>0\)，而 \(2c-3d=3(1-d)<0\)。

当 \(\varepsilon\downarrow0\)，\(A_\varepsilon\) 及其前两阶导数在固定紧集上一致收敛到 \(A_0\)。因此，对所有足够小但严格为正的 \(\varepsilon\)：

$$
\boxed{
L_1(2\pi;A_\varepsilon)<0.
}
\tag{Q29}
$$

这一步不是仅凭数值连续性猜测。令未归一化变换为：

$$
F_\varepsilon(t)=
\int e^{-x^2-\varepsilon x^4}(c+\cosh x)e^{itx}\,dx.
$$

则对 \(k=0,1,2\)：

$$
|F_\varepsilon^{(k)}(t_0)-F_0^{(k)}(t_0)|
\le
\varepsilon
\int |x|^{k+4}e^{-x^2}(c+\cosh x)\,dx.
$$

右边是明确有限的高斯矩，因此能给出保持式（Q28）严格负性的正 \(\varepsilon\) 范围。

对于这样的 \(\varepsilon>0\)，核具有超高斯衰减，其 Fourier 变换属于适用实根乘积判据的整函数类别。式（Q29）排除了全部零点为实的可能。

于是：

$$
\boxed{
\begin{gathered}
p>0,\quad p\text{ 偶、光滑、快速衰减},\\
\left(V'(x)/x\right)'>0,\\
\text{全部二次倾斜的相邻矩不等式成立}
\end{gathered}
\quad\not\Rightarrow\quad
\text{Fourier 变换全部实根}.
}
\tag{Q30}
$$

**这个反例不是实际 ξ。它严格说明：即使补实了上一轮的形状前件，仍然不能把它当成完整 RH 正性。**

缺少的确实是更深的两模态关联约束，而不是还没把普通集中性证明得足够强。

---

# 九、把理想差模态筛选改成合法的有界操作

回到实际 theta 态。

未经截断的 \(u^n\) 是无界乘法，因此不能直接把它称作对任意状态都合法的成功分支。

取 \(L>0\)，定义：

$$
\boxed{
M_{n,L}
=
\left(\frac UL\right)^n
\mathbf1_{\{|U|\le L\}}.
}
\tag{Q31}
$$

则：

$$
M_{n,L}^*M_{n,L}\le I.
$$

补上：

$$
N_{n,L}=\sqrt{I-M_{n,L}^*M_{n,L}},
$$

得到完整的两结果量子操作。

成功概率为：

$$
\boxed{
p_{n,L}
=
L^{-2n}
\mathbb E[U^{2n}\mathbf1_{\{|U|\le L\}}].
}
\tag{Q32}
$$

设成功后的和模态振幅为 \(R_{n,L}(t)\)，再定义尾量：

$$
\tau_n(L)
=
\mathbb E[U^{2n}\mathbf1_{\{|U|>L\}}].
$$

## 定理 Q5：条件读出的统一误差界

$$
\boxed{
\sup_{t\in\mathbb R}
|R_n(t)-R_{n,L}(t)|
\le
\frac{2\tau_n(L)}{Z_n}.
}
\tag{Q33}
$$

### 证明

理想条件分布是截断内、截断外两个条件分布的加权混合。

截断外的权重为 \(\tau_n(L)/Z_n\)，两种特征函数的模长均不超过一，所以差不超过该权重的两倍。证毕。

对任意整数 \(j\ge1\)：

$$
\boxed{
\tau_n(L)\le L^{-2j}Z_{n+j}.
}
\tag{Q34}
$$

而由已经补实的高斯矩上界：

$$
Z_m
\le
(2m-1)!!\,m_2^m.
$$

因此：

$$
\boxed{
\tau_n(L)
\le
L^{-2j}
(2n+2j-1)!!\,m_2^{n+j}.
}
\tag{Q35}
$$

这份尾界只使用实际矩，不输入未知零点。

所以，若能严格认证：

$$
R_{n,L}(t)+\frac{2\tau_n(L)}{Z_n}<0,
$$

就能推出实际：

$$
R_n(t)<0.
$$

但成功概率式（Q32）仍须计入。增大 \(L\) 会改善截断误差，却可能降低该有界滤波方案的成功率。

**有限观察可以承载严格证书，但不能把条件信号清楚误认成总体成本很低。**

---

# 十、现在真正需要证明的算术内容是什么？

我们已经知道实际 \(\mu_n\) 全部是正、偶、严格递减的概率密度。

还需要证明的是：

$$
\boxed{
\int_{\mathbb R}
\mu_n(s)\cos(\sqrt2ts)\,ds\ge0
\quad\forall n,t.
}
\tag{Q36}
$$

等价地，这些具体的 \(\mu_n\) 还必须自身具有正定性，而不只是作为概率密度逐点为正。实际关联核与这种 Fourier 正性之间的关系，正是经典广义 Laguerre 研究中的核心区分。([arXiv][3])

一种足够强的证明方式是，从实际 theta 结构独立构造 \(h_n\)，使：

$$
\boxed{
\mu_n(s)
=
\int_{\mathbb R}
h_n(x+s)\overline{h_n(x)}\,dx.
}
\tag{Q37}
$$

那么 Fourier 变换就是：

$$
|\widehat h_n|^2\ge0.
$$

但不能先假设 \(\widehat\mu_n\ge0\)，定义：

$$
\widehat h_n=\sqrt{\widehat\mu_n},
$$

再宣布证明了正性。那只是循环。

对于 \(n=0\)，原始两副本的卷积结构已经给出：

$$
R_0(t)=A(t)^2\ge0.
$$

**真正需要新算术的是 \(n\ge1\)：差模态的条件高阶权重，为什么不会破坏和模态 Fourier 非负性？**

式（Q30）的连续反例证明，这不能仅靠径向对数凹性回答。

---

# 十一、与项目的准确连接

本轮读取的 `CompletedZetaMellinReconstruction.lean` 保留了实际 theta 尾项、Mellin 重构、极点补偿和反射关系。它能为这里的原始态提供算术来源，但并未自动提供式（Q36）的全阶 Fourier 非负性。

`StaticEffectSequentialSeparation.lean` 证明，相同静态效应可以对应不同的两步联合规律。它也提醒我们：差模态筛选、成功概率、和模态干涉必须作为同一个协议保留，不能只保留一个最终的正概率。

因此，这次的链条是：

$$
\boxed{
\begin{aligned}
\text{实际 theta 密度}
&\longrightarrow
\text{两个独立副本}\\
&\longrightarrow
\text{和／差模态混合}\\
&\longrightarrow
\text{差模态有限阶筛选}\\
&\longrightarrow
\text{和模态干涉符号}\\
&\longleftrightarrow
\text{广义 Laguerre 零点判据}.
\end{aligned}
}
$$

其中，密度形状已知能承担矩估计和截断控制；**它尚未承担最后一项统一符号约束。**

---

## 收束

这一轮补实了一项实际已有的输入：

$$
\boxed{
\left(\frac{V'(x)}x\right)'>0,
}
$$

并从中推出了全部二次倾斜的相邻矩不等式。

但也构造了一个严格的连续反例，说明：

$$
\boxed{
\text{同样强的形状条件}
\not\Rightarrow
\text{全部零点在线}.
}
$$

随后，我们把真正缺少的条件放进一个明确的量子结构：

$$
\boxed{
R_n(t)
=
\frac{
\mathbb E[U^{2n}\cos(\sqrt2tS)]
}{
\mathbb E[U^{2n}]
}.
}
$$

它是合法条件态的干涉振幅，并满足：

$$
\boxed{
\mathrm{RH}\iff R_n(t)\ge0\quad\forall n,t.
}
$$

所以，整体问题现在不再是“有没有更高一层的观察者”，而是：

> **同一个实际 theta 态，在和模态与差模态之间具有怎样的条件关联；为什么对差模态作任意有限阶筛选以后，和模态的相位读数仍然不会进入负区间？**

高斯态因为模态独立而自动做到这一点。实际 theta 态不是高斯；一般严格对数凹态也做不到。**真正可能产生突破的，必须是 theta 的特殊模关系或算术结构，而不是普通量子正性或一般集中性。**

本轮没有证明式（Q36）的全体非负，也没有找到实际 ξ 的负证书。已经完成的是：补实上一轮的形状输入、证明其能力边界、构造相应的两副本读出，并给出不省略失败分支的有限制备误差界。新增量子协议与推导仍是聊天中的纸面结果，未修改文件或标记为 Lean 已验证。

[1]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[2]: https://www.researchgate.net/publication/226983979_Moment_inequalities_and_the_Riemann_hypothesis?utm_source=chatgpt.com "(PDF) Moment inequalities and the Riemann hypothesis"
[3]: https://arxiv.org/pdf/1309.0055 "arXiv:1309.0055v2  [math.CV]  21 Feb 2014"
继续。这次可以把两个问题同时推进：

**第一，上一轮对真实相关余项提出的“对数幂上界”，可以进一步明确为一个与 RH 等价的常数级有界条件。**

**第二，可以构造一族明确的算术正核：它的所有矩阵元都以 \(O(X^{-1})\) 趋于零，但在长度为 \(X\) 的观察窗口上，联合贡献却趋于一个严格正的常数。重标定后，这族核收敛到一个固定频带上的量子重叠核。**

第二个结论直接回答此前的疑问：

$$
\boxed{
\text{每个相关分量都很小，为什么仍然不能删掉它们？}
}
$$

因为观察窗口也在增长，相关分量可以保持相干，累积成常数级贡献。

不过，必须区分：**下面构造的是一个来自同余结构的明确正核，不是已经证明它等于实际素数的相关余项。**两者之间的算术连接仍须单独证明。以下给出纸面定理与证明，未进行 Lean 编译。

# 一、保留上一轮已经分离出的实际余项

令

$$
a(n)=\Lambda(n)-1,
$$

$$
M(x)=\lfloor2x\rfloor-\lfloor x\rfloor,
$$

$$
Y(x)=\sum_{x<n\le2x}a(n)
=\psi(2x)-\psi(x)-M(x),
$$

并定义

$$
\boxed{
\mathfrak J(X)=
\int_X^{2X}\frac{Y(x)^2}{x^2}\,dx.
}
\tag{1}
$$

记窗口重叠权重

$$
W_X(n,m)=
\int_X^{2X}
\frac{
\mathbf1_{\{x<n\le2x\}}
\mathbf1_{\{x<m\le2x\}}
}{x^2}\,dx.
$$

沿用二点奇异级数 \(\mathfrak S(d)\)，定义真实相关余项

$$
\boxed{
\mathfrak R(X)
=
\sum_{n\ne m}
\left[
a(n)a(m)-\bigl(\mathfrak S(|n-m|)-1\bigr)
\right]W_X(n,m).
}
\tag{2}
$$

这些都是有限求和。

上一轮得到

$$
\boxed{
\mathfrak J(X)=\mathfrak R(X)-c_0+o(1),
}
\tag{3}
$$

其中

$$
\boxed{
c_0=
\log2\left(\gamma_{\mathrm E}+\log\frac{\pi}{2}\right)>0.
}
\tag{4}
$$

这里使用的关键经典输入确实是

$$
2\sum_{d=1}^{H-1}
(H-d)(\mathfrak S(d)-1)
=
-H\log H+
(2-\gamma_{\mathrm E}-\log2\pi)H
+O_\varepsilon(H^{1/2+\varepsilon}),
$$

这是已经证明的奇异级数平均公式，不是尚未证明的素数对渐近式。([arXiv][1])

因此

$$
\liminf_{X\to\infty}\mathfrak R(X)\ge c_0.
$$

这说明真实余项不能趋零。但它是否必须增长？下面给出更准确的答案。

# 二、定理一：正确的目标实际上可以是常数级有界

## 定理 1：有界余项判据

以下三个命题等价：

$$
\boxed{\mathrm{RH};}
$$

$$
\boxed{\mathfrak J(X)=O(1);}
$$

$$
\boxed{\mathfrak R(X)=O(1).}
\tag{5}
$$

反向推导甚至只需在 \(X=2^j\) 上有统一上界：

$$
\boxed{
\sup_{j\ge j_0}\mathfrak R(2^j)<\infty
\Longrightarrow
\mathrm{RH}.
}
\tag{6}
$$

### 证明：RH 推出常数级均方界

令

$$
E(x)=\psi(x)-x,
\qquad
I(X)=\int_X^{2X}E(x)^2\,dx.
$$

RH 下，经典的 Cramér 均方估计给出

$$
I(X)=O(X^2).
$$

这比直接使用逐点估计 \(E(x)=O(\sqrt x\log^2x)\) 强；后者不能直接产生这个均方界。Brent、Platt、Trudgian 进一步证明了

$$
\limsup_{X\to\infty}\frac{I(X)}{X^2}\le0.8603
$$

这一显式版本。([arXiv][2])

现在

$$
Y(x)=E(2x)-E(x)+x-M(x),
$$

且

$$
|x-M(x)|<1.
$$

由加权 \(L^2\) 三角不等式，

$$
\begin{aligned}
\sqrt{\mathfrak J(X)}
\le{}&
\left(\int_X^{2X}\frac{E(2x)^2}{x^2}\,dx\right)^{1/2}\\
&+
\left(\int_X^{2X}\frac{E(x)^2}{x^2}\,dx\right)^{1/2}
+O(X^{-1/2}).
\end{aligned}
$$

而

$$
\int_X^{2X}\frac{E(2x)^2}{x^2}\,dx
\le\frac{I(2X)}{2X^2},
$$

$$
\int_X^{2X}\frac{E(x)^2}{x^2}\,dx
\le\frac{I(X)}{X^2}.
$$

所以 RH 推出 \(\mathfrak J(X)=O(1)\)，并且

$$
\boxed{
\limsup_{X\to\infty}\mathfrak J(X)
\le
0.8603(1+\sqrt2)^2.
}
\tag{7}
$$

结合式（3），得到 \(\mathfrak R(X)=O(1)\)。

### 证明：有界局部均方推出 RH

令

$$
r(T)=e^{-T/2}E(e^T),
$$

$$
z(T)=e^{-T/2}
\left[\psi(2e^T)-\psi(e^T)-e^T\right].
$$

有精确关系

$$
z(T)=\sqrt2\,r(T+\log2)-r(T).
$$

把函数分成长度为 \(\log2\) 的区块，记为 \(r_j,z_j\)。于是

$$
r_j
=
2^{-j/2}r_0
+
\sum_{k=0}^{j-1}2^{-(j-k)/2}z_k.
\tag{8}
$$

若 \(\mathfrak J(2^j)\) 一致有界，地板函数修正只产生衰减误差，所以 \(\|z_j\|_2\) 一致有界。

由于

$$
\sum_{k\ge1}2^{-k/2}<\infty,
$$

式（8）推出 \(\|r_j\|_2\) 一致有界。因此

$$
\int_0^L|r(T)|^2\,dT=O(L).
$$

这保证 \(r\) 的 Laplace 变换在 \(\Re s>0\) 内解析。

另一方面，在初始收敛区域，

$$
\boxed{
\widehat r(s)
=
-\frac{\zeta'(s+1/2)}
{(s+1/2)\zeta(s+1/2)}
-\frac1{s-1/2}.
}
\tag{9}
$$

该式直接来自 von Mangoldt 狄利克雷级数。([DLMF][3])

若存在右侧离线零点

$$
\rho=\frac12+\delta+i\gamma,
\qquad \delta>0,
$$

右边就在 \(s=\delta+i\gamma\) 有不可去极点，矛盾。结合零点反射对称性，得到 RH。

最后，式（3）连接 \(\mathfrak J\) 与 \(\mathfrak R\)。证毕。

---

因此，我们现在知道真实余项的预期尺度应该是：

$$
\boxed{
c_0-o(1)\le\mathfrak R(X)\le C
}
$$

而不是趋于零。

**这里的 \(O(1)\) 不意味着一定收敛到一个常数。**有界振荡与存在极限仍是不同命题。

# 三、把“局部同余模型”构造成真正的有限正核

接下来研究：怎样在不预设 RH 的条件下，从同余结构产生一个合法正核？

记

$$
e(t)=e^{2\pi it}.
$$

定义 Ramanujan 和

$$
c_q(d)=
\sum_{\substack{1\le a\le q\\(a,q)=1}}
e(ad/q).
$$

这是标准的周期数论函数；它的乘法性使其能够表达奇异级数。([DLMF][4])

## 定义 1：有限同余核

对 \(Q\ge2\)，定义

$$
\boxed{
\mathscr K_Q(n,m)
=
\sum_{2\le q\le Q}
\frac{\mu(q)^2}{\varphi(q)^2}
c_q(n-m).
}
\tag{10}
$$

这里 \(\mu\) 是 Möbius 函数，\(\varphi\) 是 Euler 函数。

## 定理 2：有限同余核始终半正定

对任意有限复向量 \((z_n)\)，

$$
\boxed{
\sum_{n,m}\overline{z_n}z_m\mathscr K_Q(n,m)
=
\sum_{2\le q\le Q}
\frac{\mu(q)^2}{\varphi(q)^2}
\sum_{\substack{a\bmod q\\(a,q)=1}}
\left|\sum_nz_ne(-an/q)\right|^2
\ge0.
}
\tag{11}
$$

### 证明

把 Ramanujan 和展开，再交换有限求和，直接得到平方和。证毕。

所以，\(\mathscr K_Q\) 是一个实际构造出来的 Gram 核，而不是先写“假设某个正核存在”。

## 但是，固定位置极限与整体模型极限并不相同

对固定 \(d\ne0\)，有绝对收敛恒等式

$$
\boxed{
\mathfrak S(d)-1
=
\sum_{q\ge2}
\frac{\mu(q)^2}{\varphi(q)^2}c_q(d).
}
\tag{12}
$$

证明可逐素数展开：

$$
c_p(d)=
\begin{cases}
p-1,&p\mid d,\\
-1,&p\nmid d,
\end{cases}
$$

从而 Euler 因子正好是二点奇异级数的局部因子。对不整除固定 \(d\) 的素数，绝对值贡献为 \(O(p^{-2})\)，故绝对收敛。这也正是奇异级数平均中使用的 Ramanujan 展开结构。([arXiv][1])

然而在对角线上，

$$
\mathscr K_Q(n,n)
=
\sum_{2\le q\le Q}\frac{\mu(q)^2}{\varphi(q)}
\longrightarrow\infty.
\tag{13}
$$

因此：

$$
\boxed{
\text{固定非对角位置存在极限，}
\quad
\text{不等于整个有限窗口的协方差已经完成。}
}
$$

尤其不能把极限化的非对角项，与另一套给定的对角项拼在一起后，自动认为所得模型仍然正定。

上一轮出现的负基准常数，正是在警告这种拼接需要额外的完成项；它不是对奇异级数平均公式的否定。

# 四、一个可计算的 Euler 平均常数

为了研究随窗口一起移动的模数，定义

$$
\boxed{
\alpha(q)=
\mu(q)^2\left(\frac q{\varphi(q)}\right)^2.
}
\tag{14}
$$

## 引理 1：平均权重

有

$$
\boxed{
\sum_{q\le Y}\alpha(q)
=
\mathfrak a\,Y+o(Y),
}
\tag{15}
$$

其中

$$
\boxed{
\mathfrak a
=
\prod_p\left(1+\frac1{p(p-1)}\right)
=
\frac{\zeta(2)\zeta(3)}{\zeta(6)}.
}
\tag{16}
$$

这个结论不使用 RH。

### 证明

令 \(g=\alpha*\mu\)，则

$$
\alpha(n)=\sum_{d\mid n}g(d).
$$

局部值为

$$
g(p)=\frac{p^2}{(p-1)^2}-1=O(p^{-1}),
$$

$$
g(p^2)=-\frac{p^2}{(p-1)^2},
$$

$$
g(p^k)=0\qquad(k\ge3).
$$

因此

$$
\sum_{d\ge1}\frac{|g(d)|}{d}<\infty.
$$

于是由支配收敛，

$$
\begin{aligned}
\frac1Y\sum_{q\le Y}\alpha(q)
&=
\sum_{d\le Y}g(d)\frac{\lfloor Y/d\rfloor}{Y}\\
&\longrightarrow
\sum_{d\ge1}\frac{g(d)}d.
\end{aligned}
$$

其 Euler 因子为

$$
\begin{aligned}
1+\frac{g(p)}p+\frac{g(p^2)}{p^2}
&=
\left(1-\frac1p\right)
\left(1+\frac{p}{(p-1)^2}\right)\\
&=
1+\frac1{p(p-1)}.
\end{aligned}
$$

最后利用

$$
1+\frac1{p(p-1)}
=
\frac{1-p^{-6}}{(1-p^{-2})(1-p^{-3})}
$$

得到式（16）。证毕。

# 五、主定理：矩阵元全部趋零，却留下一个固定量子核

现在令 \(X\) 为正整数，只保留

$$
4X<q\le8X
$$

中的两个共轭频率

$$
a=1,\qquad a=q-1.
$$

## 定义 2：移动模数带核

定义

$$
\boxed{
\mathscr P_X(n,m)
=
2\sum_{4X<q\le8X}
\frac{\mu(q)^2}{\varphi(q)^2}
\cos\frac{2\pi(n-m)}q.
}
\tag{17}
$$

它是 \(\mathscr K_{8X}-\mathscr K_{4X}\) 中保留部分 Gram 坐标后得到的核，因此

$$
\mathscr P_X\succeq0.
$$

这组选取不是从未知零点倒填出来的；它只使用 \(\mu,\varphi\) 与明确的有理频率。

## 定理 3：逐项消失与连续正核极限

首先，

$$
\boxed{
\sup_{n,m}|\mathscr P_X(n,m)|=O(X^{-1}).
}
\tag{18}
$$

但是，对固定实数 \(s,t\)，

$$
\boxed{
X\,\mathscr P_X(\lfloor Xs\rfloor,\lfloor Xt\rfloor)
\longrightarrow
\Gamma(s,t),
}
\tag{19}
$$

其中

$$
\boxed{
\Gamma(s,t)
=
2\mathfrak a
\int_{1/8}^{1/4}
\cos\bigl(2\pi(s-t)\xi\bigr)\,d\xi.
}
\tag{20}
$$

收敛在 \(s,t\) 的固定紧集上一致。

当 \(s\ne t\) 时，

$$
\boxed{
\Gamma(s,t)
=
\mathfrak a\,
\frac{
\sin\bigl(\frac{\pi}{2}(s-t)\bigr)
-
\sin\bigl(\frac{\pi}{4}(s-t)\bigr)
}{
\pi(s-t)
}.
}
\tag{21}
$$

对角值为

$$
\Gamma(s,s)=\frac{\mathfrak a}{4}.
$$

### 证明

由引理 1，

$$
\sum_{4X<q\le8X}\alpha(q)=O(X).
$$

所以

$$
|\mathscr P_X(n,m)|
\le
2\sum_{4X<q\le8X}\frac{\alpha(q)}{q^2}
=O(X^{-1}),
$$

证明式（18）。

再写成

$$
\begin{aligned}
&X\mathscr P_X(\lfloor Xs\rfloor,\lfloor Xt\rfloor)\\
&\quad=
\frac2X
\sum_{4X<q\le8X}
\frac{\alpha(q)}{(q/X)^2}
\cos\left(
2\pi\frac{(\lfloor Xs\rfloor-\lfloor Xt\rfloor)/X}{q/X}
\right).
\end{aligned}
$$

由式（15），加权测度

$$
\frac1X\sum_{4X<q\le8X}\alpha(q)\delta_{q/X}
$$

弱收敛到

$$
\mathfrak a\,\mathbf1_{[4,8]}(v)\,dv.
$$

于是极限为

$$
2\mathfrak a\int_4^8
\frac{\cos(2\pi(s-t)/v)}{v^2}\,dv.
$$

令 \(\xi=1/v\)，得到式（20）。

被积函数在固定紧参数集上构成一致有界、等度连续族，因此收敛也在该参数集上一致。证毕。

---

## 这个极限本身就是一个归一化量子重叠核

令频带

$$
\mathcal B=
[-1/4,-1/8]\cup[1/8,1/4].
$$

它的长度为 \(1/4\)。

在 Hilbert 空间

$$
\mathcal H=L^2(\mathcal B,4\,d\xi)
$$

中定义单位向量

$$
v_s(\xi)=e^{-2\pi is\xi}.
$$

于是

$$
\boxed{
\langle v_s,v_t\rangle
=
\frac4{\mathfrak a}\Gamma(s,t).
}
\tag{22}
$$

其生成元可以取为有界自伴乘法算子

$$
(Hf)(\xi)=2\pi\xi f(\xi).
$$

因此，同一构造有两种精确读出：

$$
\boxed{
\begin{aligned}
\text{有限算术面}
&:\ q\asymp X\text{ 的有理相位};\\
\text{重标定连续面}
&:\ \text{固定频带上的量子重叠核}.
\end{aligned}
}
$$

这里的 \(s\) 首先是缩放后的整数坐标，不自动等同于现实物理时间。

# 六、定理四：这些逐项消失的通道，确实贡献一个正的常数级观察量

定义与实际均方使用相同窗口的模型读出：

$$
\boxed{
\mathfrak B(X)
=
\int_X^{2X}
\frac1{x^2}
\sum_{\substack{x<n\le2x\\x<m\le2x}}
\mathscr P_X(n,m)\,dx.
}
\tag{23}
$$

因为 \(\mathscr P_X\succeq0\)，有 \(\mathfrak B(X)\ge0\)。

## 定理 4：非消失联合贡献

存在明确常数 \(C_{\mathrm{band}}>0\)，使

$$
\boxed{
\mathfrak B(X)\longrightarrow C_{\mathrm{band}}.
}
\tag{24}
$$

其中

$$
\boxed{
C_{\mathrm{band}}
=
\mathfrak a
\int_{\mathcal B}\int_1^2
\frac{
\left|\displaystyle\int_u^{2u}e^{2\pi i\xi s}\,ds\right|^2
}{u^2}
\,du\,d\xi.
}
\tag{25}
$$

并且具有显式上下界

$$
\boxed{
\frac{\mathfrak a}{\pi^2}
\le C_{\mathrm{band}}
\le\frac{\mathfrak a}{4}.
}
\tag{26}
$$

### 证明

作缩放 \(x=Xu\)，并使用定理 3 的一致核收敛。窗口内的双重和变成 Riemann 和，得到

$$
\begin{aligned}
\mathfrak B(X)
&\longrightarrow
\int_1^2\frac1{u^2}
\int_u^{2u}\int_u^{2u}
\Gamma(s,t)\,ds\,dt\,du.
\end{aligned}
$$

代入式（20），即得式（25）。

对于上界，

$$
\left|\int_u^{2u}e^{2\pi i\xi s}\,ds\right|
\le u.
$$

所以

$$
C_{\mathrm{band}}
\le
\mathfrak a\,|\mathcal B|
=\frac{\mathfrak a}{4}.
$$

对于下界，

$$
\left|\int_u^{2u}e^{2\pi i\xi s}\,ds\right|
=
\frac{|\sin(\pi u\xi)|}{\pi|\xi|}.
$$

在当前积分范围内，

$$
\frac18\le u|\xi|\le\frac12.
$$

使用

$$
\sin(\pi y)\ge2y
\qquad(0\le y\le1/2),
$$

得到

$$
\left|\int_u^{2u}e^{2\pi i\xi s}\,ds\right|^2
\ge\frac{4u^2}{\pi^2}.
$$

积分后即得下界。证毕。

---

现在有一个完整反例，反对如下推理：

$$
\text{“每个矩阵元趋零，所以这一部分可以删掉。”}
$$

实际情况是

$$
\boxed{
\sup_{n,m}|\mathscr P_X(n,m)|=O(X^{-1}),
}
$$

但

$$
\boxed{
\mathfrak B(X)\longrightarrow C_{\mathrm{band}}>0.
}
\tag{27}
$$

原因不是抽象的“无限维神秘效应”，而是：

$$
\boxed{
O(X^{-1})\text{ 的相关量}
\times
O(X^2)\text{ 个状态对}
\times
O(X^{-1})\text{ 的积分归一化}
=
O(1).
}
$$

而这些相位在整个窗口内并未随机抵消，平方和结构保留了它们的相干贡献。

**但 \(C_{\mathrm{band}}\) 不是前文的 \(c_0\)。**当前没有证明这组模数通道恰好等于实际余项的补偿；我们证明的是，它们能够产生一个此前逐项极限看不到的、明确非零的常数级贡献。

# 七、截断模数应该增长多快？也可以精确回答

上面选择了 \(q\asymp X\)。再考虑只保留两个共轭频率的尾核

$$
\mathscr P_{>Q}(n,m)
=
2\sum_{q>Q}
\frac{\mu(q)^2}{\varphi(q)^2}
\cos\frac{2\pi(n-m)}q.
$$

这个级数绝对收敛，并且仍是正核。

定义相应窗口读出

$$
\mathfrak B(X,Q)
=
\int_X^{2X}
\frac1{x^2}
\sum_{x<n,m\le2x}
\mathscr P_{>Q}(n,m)\,dx.
$$

## 定理 5：尾部可忽略的尺度条件

若

$$
X\to\infty,
\qquad
\frac QX\to\infty,
$$

则

$$
\boxed{
\mathfrak B(X,Q)
\sim
2\mathfrak a\,\frac XQ.
}
\tag{28}
$$

相反，如果 \(Q/X\) 沿某个子序列保持有界，那么这些尾部读出不能沿该子序列趋零。

### 证明

窗口含有 \(M(x)\) 个连续整数，所以

$$
\left|
\sum_{x<n\le2x}e(n/q)
\right|^2
=
\frac{\sin^2(\pi M(x)/q)}{\sin^2(\pi/q)}.
$$

当 \(q>Q\gg X\) 时，一致地有

$$
\frac{\sin^2(\pi M(x)/q)}{\sin^2(\pi/q)}
=
M(x)^2
\left[1+O\!\left(\frac{X^2}{q^2}\right)\right].
$$

由引理 1 的分部求和，

$$
\sum_{q>Q}\frac{\alpha(q)}{q^2}
=
\frac{\mathfrak a}{Q}+o(Q^{-1}),
$$

以及

$$
\sum_{q>Q}\frac{\alpha(q)}{q^4}=O(Q^{-3}).
$$

又因为

$$
\int_X^{2X}\frac{M(x)^2}{x^2}\,dx
=
X+O(1),
$$

得到

$$
\mathfrak B(X,Q)
=
2\mathfrak a\frac XQ(1+o(1))
+
O\!\left(\frac{X^3}{Q^3}\right).
$$

即式（28）。

反之，若 \(Q\le CX\)，就在 \(Q\) 以上选择一个固定比例模数带

$$
AX<q\le2AX,
\qquad A>C.
$$

定理 3—4 的同样证明给出该模数带的严格正极限。而整个尾部是它再加上其他正核，所以整体读出不可能趋零。证毕。

---

因此，对这一明确的相干通道族，

$$
\boxed{
\text{要把模数尾部作为整体删掉，需要 }Q/X\to\infty.
}
\tag{29}
$$

只知道 \(Q\to\infty\)，甚至只取 \(Q\) 与窗口 \(X\) 同阶，都不够。

这个结论只针对这里保留的两个原始频率通道；**不能未经进一步估计，就宣称它已经控制完整 Ramanujan 核的全部频率尾部。**

# 八、把误差预算写成观察者真正需要的形式

对有限矩阵误差 \(E_X(n,m)\)，定义观察误差

$$
\delta_X(E_X)
=
\left|
\sum_{n,m}W_X(n,m)E_X(n,m)
\right|.
$$

因为 \(W_X(n,m)\ge0\)，并且

$$
\begin{aligned}
\sum_{n,m}W_X(n,m)
&=
\int_X^{2X}\frac{M(x)^2}{x^2}\,dx\\
&=X+O(1),
\end{aligned}
$$

所以

$$
\boxed{
\sup_{n,m}|E_X(n,m)|\le\varepsilon_X
\Longrightarrow
\delta_X(E_X)
\le
\varepsilon_X\,[X+O(1)].
}
\tag{30}
$$

于是：

$$
\boxed{
\varepsilon_X=o(1)
}
$$

并不足以保证观察误差趋零。

通过这种逐项估计路线，至少需要

$$
\boxed{
\varepsilon_X=o(X^{-1}).
}
\tag{31}
$$

本轮的 \(\mathscr P_X\) 恰好位于临界尺度：

$$
\varepsilon_X=O(X^{-1}),
$$

并且它真的留下了非零常数贡献，而不是上界估计虚构出来的可能性。

这给“信息逃逸”一个更准确的表达：

> **一个通道在每个固定状态对上的读出都消失，不代表它在随尺度增长的联合观察中消失。需要控制的是观察误差，而不仅是逐项误差。**

# 九、现在还缺哪一步，才算真的接回实际素数？

目前已经有两类不同的对象。

实际算术对象是

$$
a(n)a(m)
=
(\Lambda(n)-1)(\Lambda(m)-1).
$$

同余正核对象是

$$
\mathscr K_Q(n,m),
$$

以及我们从中提取的

$$
\mathscr P_X(n,m).
$$

第二类对象已经有明确的 Gram 表示、正性、尺度极限和尾界。

但还没有证明：

$$
\boxed{
\text{实际二点相关}
\quad\text{能以足够小的观察误差由这些正模态重建。}
}
\tag{32}
$$

这一步不能从正核的存在性自动得到。

尤其不能因为我们已经构造了

$$
\Gamma(s,t)=\mathfrak a\int_{\mathcal B}e^{2\pi i(s-t)\xi}\,d\xi
$$

就宣布实际素数的相关余项已经有界。那会把一个具有正确局部结构的候选模型，替换成实际算术锚。

当前有价值的桥接形式应当是：

$$
\boxed{
\text{真实相关}
=
\text{有限同余模态}
+
\text{可控的联合误差},
}
$$

其中“可控”必须体现在

$$
\delta_X(E_X)
$$

或者更强的算子估计上，而不是只说每个固定差值的误差趋零。

---

## 本轮的实质推进

现在可以留下三条更强、也更具体的结论。

首先，实际目标可以明确为

$$
\boxed{
\mathrm{RH}\iff\mathfrak R(X)=O(1),
}
$$

而不是要求余项趋零。它必须保留至少 \(c_0\) 的正补偿，同时在正确理论下保持常数级大小。

其次，已经构造了一个完全明确的算术正核，使

$$
\boxed{
\mathscr P_X(n,m)=O(X^{-1})
}
$$

对所有位置成立，但

$$
\boxed{
\sum_{n,m}W_X(n,m)\mathscr P_X(n,m)
\longrightarrow C_{\mathrm{band}}>0.
}
$$

最后，这个看似消失的核在正确缩放下，收敛为

$$
\boxed{
\text{固定频带上的归一化量子重叠核}.
}
$$

所以，前文“缺一个常数级相关补偿”的问题，现在有了一个具体机制：

$$
\boxed{
\text{模数与窗口一起增长}
\longrightarrow
\text{单个相关分量趋零}
\longrightarrow
\text{联合相干贡献仍然存活}.
}
$$

**尚未完成的是证明实际素数恰好以受控方式实现这些模态，而不是这些模态是否能够被构造出来。**本轮把这个区别变成了可以计算的阈值：逐项 \(o(1)\) 不够，窗口尺度上的联合误差才是决定性对象。

[1]: https://arxiv.org/html/math/0409258v1 "Primes in short intervals"
[2]: https://arxiv.org/html/2008.06140v1 "The mean square of the error term in the prime number theorem"
[3]: https://dlmf.nist.gov/27.4 "DLMF: §27.4 Euler Products and Dirichlet Series ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"
[4]: https://dlmf.nist.gov/27.10 "DLMF: §27.10 Periodic Number-Theoretic Functions ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"
这次可以从**实际 theta 核**推出一项更具体的结果，而不只是再增加一个 RH 等价表述：

> **随着差模态筛选阶数 \(n\) 增大，和模态会被压缩到越来越窄的区域。固定频率的干涉读数因此自动趋向 \(1\)；在正确放大的频率尺度上，它趋向一个高斯函数。这个结论不需要 RH。**

但与此同时：

> **相邻两个筛选态始终严格正交；使读数越来越规则的筛选，其能量代价反而持续增长。**

因此，“读数越来越经典、越来越高斯”与“底层量子态之间的差异消失”，完全不是同一件事。

下面把这几项联系写成定义、定理和证明。核心的新尺度为：

$$
\boxed{
\Omega_n
=
2\sqrt{\frac{n}{W_0(n/\pi)}}
\asymp
\sqrt{\frac n{\log n}},
}
$$

其中 \(W_0\) 是 Lambert \(W\) 函数的实主支。

---

# 一、固定前文的两副本模型

仍取实际概率密度：

$$
p(x)=\frac{\Phi(x)}{\xi(1/2)},
$$

使：

$$
\boxed{
A(z)
=
\int_{\mathbb R}p(x)e^{izx}\,dx
=
\frac{\xi(\frac12+iz)}{\xi(\frac12)}.
}
\tag{R1}
$$

ξ 的归一化与反射关系保持标准约定。([DLMF][1])

取独立副本 \(X,Y\sim p\)，定义：

$$
S=\frac{X+Y}{\sqrt2},
\qquad
U=\frac{X-Y}{\sqrt2}.
$$

原始两模态波函数为：

$$
\chi(s,u)
=
\sqrt{
p\!\left(\frac{s+u}{\sqrt2}\right)
p\!\left(\frac{s-u}{\sqrt2}\right)
}.
$$

对 \(n\ge0\)，定义：

$$
Z_n=\mathbb E[U^{2n}],
$$

以及归一化筛选态：

$$
\boxed{
\chi_n(s,u)=\frac{u^n\chi(s,u)}{\sqrt{Z_n}}.
}
\tag{R2}
$$

对应概率律记为 \(\mathbb P_n\)，期望记为 \(\mathbb E_n\)。它就是：

$$
d\mathbb P_n
=
\frac{U^{2n}}{Z_n}\,d\mathbb P_0.
$$

读取和模态相位：

$$
\boxed{
R_n(t)
=
\langle\chi_n,e^{i\sqrt2tS}\chi_n\rangle
=
\mathbb E_n[\cos(\sqrt2tS)].
}
\tag{R3}
$$

这里 \(t\) 是相位控制参数，也对应 ξ 的高度坐标，不是另行假定的物理演化时间。

前文已将它接到广义 Laguerre 表达式：

$$
L_n(t)
=
\frac{2^n Z_n}{(2n)!}R_n(t),
$$

以及：

$$
|A(t+iy)|^2
=
\sum_{n\ge0}L_n(t)y^{2n}.
$$

因此：

$$
\boxed{
\mathrm{RH}
\iff
R_n(t)\ge0
\quad\forall n\ge0,\ \forall t\in\mathbb R.
}
\tag{R4}
$$

广义 Laguerre 表达式与两副本关联核的这条联系属于经典理论；这里研究的是指定条件态的尺度行为。([arXiv][2])

---

# 二、首先得到一个不涉及零点的有限正值区间

## 定义 R1：筛选后的和模态方差

由于 \(\mathbb P_n\) 关于 \(S\) 对称：

$$
\mathbb E_n[S]=0.
$$

定义：

$$
\boxed{
v_n=\mathbb E_n[S^2]
=
\frac{\mathbb E[S^2U^{2n}]}{Z_n}.
}
\tag{R5}
$$

## 定理 R1：方差控制低频干涉

对所有实数 \(t\)：

$$
\boxed{
1-t^2v_n\le R_n(t)\le1.
}
\tag{R6}
$$

特别地：

$$
\boxed{
|t|<v_n^{-1/2}
\Longrightarrow
R_n(t)>0.
}
\tag{R7}
$$

### 证明

使用：

$$
0\le1-\cos x\le\frac{x^2}{2}.
$$

于是：

$$
\begin{aligned}
0\le1-R_n(t)
&=
\mathbb E_n[1-\cos(\sqrt2tS)]\\
&\le t^2\mathbb E_n[S^2]\\
&=t^2v_n.
\end{aligned}
$$

证毕。

这已经说明：**只要和模态变窄，固定频率上的正读数就可能自动出现。**

但“和模态是否真的越来越窄”，还需要从实际算术核证明。

---

## 这些方差可以直接由原始 theta 矩计算

记：

$$
m_{2j}=\mathbb E[X^{2j}],
\qquad m_0=1.
$$

则：

$$
\boxed{
Z_n
=
2^{-n}
\sum_{j=0}^{n}
\binom{2n}{2j}
m_{2j}m_{2n-2j}.
}
\tag{R8}
$$

又由：

$$
S^2=U^2+2XY,
$$

得到：

$$
\boxed{
\begin{aligned}
\mathbb E[S^2U^{2n}]
={}&Z_{n+1}\\
&-2^{1-n}
\sum_{j=0}^{n-1}
\binom{2n}{2j+1}
m_{2j+2}m_{2n-2j}.
\end{aligned}
}
\tag{R9}
$$

\(n=0\) 时第二个和为空。

例如：

$$
v_0=m_2,
$$

$$
\boxed{
v_1=\frac{m_4-m_2^2}{2m_2}.
}
$$

因此，每一阶的有限正值区间都可以从实际原始矩计算，**不需要输入任何未知零点的位置**。

---

# 三、实际 theta 尾部决定了一个 Lambert \(W\) 尺度

在本对话固定的坐标中，对 \(x\ge0\)：

$$
\Phi(x)
=
\sum_{j\ge1}
\left(
4\pi^2j^4e^{9x/2}
-
6\pi j^2e^{5x/2}
\right)e^{-\pi j^2e^{2x}}.
$$

第一项控制 \(x\to+\infty\) 的渐近，其余项具有更快的指数衰减。因此：

$$
\boxed{
p(x)
=
C_\theta
e^{\frac92x-\pi e^{2x}}
\left[1+O(e^{-2x})\right],
\qquad
C_\theta=\frac{4\pi^2}{\xi(1/2)}.
}
\tag{R10}
$$

相应的有限阶导数也可逐项控制。

此外，实际 \(p\) 严格对数凹：

$$
V(x):=-\log p(x)
$$

是凸函数。上一轮已经核对了这一性质的经典来源；它比普通“密度为正”强，但仍不等于 Fourier 非负性。([arXiv][2])

现在考虑筛选后的联合密度。在 \(U>0\) 一侧，令：

$$
x=\frac{U}{\sqrt2}>0.
$$

保留和模态坐标 \(s=S\)。忽略归一化常数，密度为：

$$
\boxed{
q_n(x,s)
=
x^{2n}
p\!\left(x+\frac{s}{\sqrt2}\right)
p\!\left(x-\frac{s}{\sqrt2}\right).
}
\tag{R11}
$$

由于原密度偶对称，这也描述 \((|U|/\sqrt2,S)\) 的分布。

在 \(x\) 很大、\(s\) 有界时：

$$
\boxed{
\log q_n(x,s)
=
2n\log x+9x
-2\pi e^{2x}\cosh(\sqrt2s)
+\text{常数}+O(e^{-2x}).
}
\tag{R12}
$$

在 \(s=0\) 附近，主导平衡为：

$$
\frac{2n}{x}=4\pi e^{2x}.
$$

也就是：

$$
(2x)e^{2x}=\frac n\pi.
$$

定义：

$$
\boxed{
w_n=W_0(n/\pi),
\qquad
h_n=\frac{w_n}{2}.
}
\tag{R13}
$$

Lambert 函数满足：

$$
W_0(z)e^{W_0(z)}=z,
$$

且：

$$
W_0(z)=\log z-\log\log z+o(1)
\qquad(z\to+\infty).
$$

所以：

$$
h_n\sim\frac12\log n.
$$

这些定义与渐近是标准 Lambert \(W\) 性质。([DLMF][3])

**高阶筛选不是只让分布更集中：它首先把差模态推向越来越远的尾部。**

具体而言：

$$
|U|\approx\frac{w_n}{\sqrt2}.
$$

---

# 四、核心渐近定理：差模态向外移动，和模态同时变窄

定义两个局部尺度：

$$
\boxed{
\varepsilon_n
=
\frac{w_n}{\sqrt{8n(w_n+1)}},
}
$$

$$
\boxed{
\sigma_n
=
\sqrt{\frac{w_n}{4n}}.
}
\tag{R14}
$$

## 定理 R2：实际两模态的局部高斯极限

在筛选概率 \(\mathbb P_n\) 下：

$$
\boxed{
\left(
\frac{|U|/\sqrt2-h_n}{\varepsilon_n},
\frac{S}{\sigma_n}
\right)
\ \Longrightarrow\
N(0,1)\otimes N(0,1).
}
\tag{R15}
$$

并且所有固定阶多项式矩随之收敛。

特别地：

$$
\boxed{
v_n\sim\sigma_n^2
=
\frac{W_0(n/\pi)}{4n}.
}
\tag{R16}
$$

这个结论不使用 RH。

### 证明：局部二次展开

在式（R12）中代入：

$$
x=h_n+\varepsilon_n a,
\qquad
s=\sigma_n b.
$$

由：

$$
e^{2h_n}=\frac{n}{\pi w_n},
$$

可得主导对数密度在 \((h_n,0)\) 的二阶导数：

$$
\partial_x^2\log q_n
=
-\frac{8n(w_n+1)}{w_n^2}+o(n/w_n),
$$

$$
\partial_s^2\log q_n
=
-\frac{4n}{w_n}+o(n/w_n),
$$

以及：

$$
\partial_x\partial_s\log q_n=0
\quad(s=0).
$$

一阶径向项在这个中心处为 \(9+o(1)\)，乘以 \(\varepsilon_n\) 后趋零。

因此，对每个固定紧集：

$$
\boxed{
\log
\frac{
q_n(h_n+\varepsilon_na,\sigma_nb)
}{
q_n(h_n,0)
}
\longrightarrow
-\frac{a^2+b^2}{2}
}
\tag{R17}
$$

一致成立。三阶及更高阶的局部余项趋零，尺度来自：

$$
\sqrt{\frac{w_n}{n}}\longrightarrow0.
$$

### 证明：为什么不能只停在局部展开？

需要控制远处尾部，否则局部高斯并不保证归一化后的分布收敛。

这里实际核的对数凹性提供了控制。

在 \(x>0\) 上：

$$
\log q_n(x,s)
=
2n\log x
-
V\!\left(x+\frac{s}{\sqrt2}\right)
-
V\!\left(x-\frac{s}{\sqrt2}\right)
$$

是二维凹函数。

缩放后的定义域会覆盖任何固定紧集。由式（R17），在任意固定半径 \(R\) 的圆周上，充分大的 \(n\) 满足：

$$
\log\frac{q_n}{q_n(h_n,0)}
\le-\frac{R^2}{4}.
$$

沿射线使用凹性，对半径 \(r\ge R\)：

$$
\boxed{
\log\frac{q_n}{q_n(h_n,0)}
\le-\frac R4r.
}
$$

因此得到统一指数尾界。它既控制归一化积分，也控制任意固定阶多项式矩。

局部展开加上这个尾界，完成式（R15）、（R16）的证明。

这种 Lambert \(W\) 鞍点分析与已有 ξ 高阶系数渐近中的方法相呼应；这里推导的是两个条件模态的联合分布，而不是直接把单变量系数定理当作联合结论。([arXiv][4])

---

# 五、条件干涉的正确频率尺度出现了

定义：

$$
\boxed{
\Omega_n=\sigma_n^{-1}
=
2\sqrt{\frac{n}{W_0(n/\pi)}}.
}
\tag{R18}
$$

由定理 R2：

$$
\begin{aligned}
R_n(\Omega_nt)
&=
\mathbb E_n\!\left[
\cos\left(\sqrt2t\frac S{\sigma_n}\right)
\right]\\
&\longrightarrow e^{-t^2}.
\end{aligned}
$$

因此：

## 定理 R3：放大后的干涉极限

$$
\boxed{
R_n(\Omega_nt)\longrightarrow e^{-t^2}.
}
\tag{R19}
$$

收敛在每个固定实紧区间上一致成立。

前面证明中的指数尾控制还可以任意加强：先选择更大的固定圆周，再利用凹性。因此它也提供固定复紧集所需的指数矩控制，使式（R19）在复平面紧集上局部一致成立。

### 第一个推论：固定频率一定越来越正常

$$
\boxed{
R_n(t)\longrightarrow1
\qquad(n\to\infty)
}
\tag{R20}
$$

对每个固定实数 \(t\) 成立。

更强地，对每个固定 \(T<\infty\)：

$$
\boxed{
\sup_{|t|\le T}|R_n(t)-1|\longrightarrow0.
}
$$

所以存在 \(N(T)\)，使：

$$
\boxed{
n\ge N(T),\quad |t|\le T
\Longrightarrow R_n(t)>0.
}
\tag{R21}
$$

**这段正性可以由实际 theta 尾部和凸性直接得到，而不需要证明 RH。**

### 第二个推论：负读数必须逃离每个固定的放大窗口

对每个固定 \(M>0\)，因为：

$$
\min_{|t|\le M}e^{-t^2}=e^{-M^2}>0,
$$

式（R19）给出：

$$
\boxed{
R_n(t)>0
\quad\text{当}\quad |t|\le M\Omega_n,\ n\text{ 足够大}.
}
\tag{R22}
$$

因此，若存在一列负读数：

$$
n_j\to\infty,\qquad R_{n_j}(t_j)<0,
$$

则必须：

$$
\boxed{
\frac{|t_j|}{\Omega_{n_j}}\longrightarrow\infty.
}
\tag{R23}
$$

这没有证明负读数不存在。它定位了高阶反例不能停留的区域。

---

# 六、两个极限再次不交换，但这一次来自实际条件态的压缩

对每个固定 \(n\)，和模态密度 \(\mu_n\) 可积，所以 Fourier 变换满足：

$$
R_n(t)\longrightarrow0
\qquad(|t|\to\infty).
$$

另一方面，式（R20）给出固定 \(t\) 时 \(R_n(t)\to1\)。

于是：

$$
\boxed{
\lim_{n\to\infty}\lim_{|t|\to\infty}R_n(t)=0,
}
$$

而：

$$
\boxed{
\lim_{|t|\to\infty}\lim_{n\to\infty}R_n(t)=1.
}
\tag{R24}
$$

这里没有把某个模式删掉，也没有改变 ξ 的定义。发生的是：

**筛选阶数改变了条件态本身，使其和模态宽度趋零；而探测这个越来越窄的分布，需要越来越大的频率。**

因此：

> **“高阶筛选后，所有已经检查的频率都呈现正值”，可能只是探测尺度没有跟上条件态的变化。**

这与前文群平均中的维数稀释不是同一个机制。那边是扩大平均空间；这里是条件筛选引发的实际空间压缩。

---

# 七、最有意思的奇偶结果：读数趋同，态却始终正交

因为原始 \(\chi(s,u)\) 关于 \(u\) 为偶函数：

$$
\chi_n(s,-u)=(-1)^n\chi_n(s,u).
$$

令差模态反射算子：

$$
(\mathcal P_Uf)(s,u)=f(s,-u).
$$

则：

$$
\boxed{
\mathcal P_U\chi_n=(-1)^n\chi_n.
}
\tag{R25}
$$

## 定理 R4：相邻态严格正交

$$
\boxed{
\langle\chi_n,\chi_{n+1}\rangle=0
\qquad\forall n.
}
\tag{R26}
$$

### 证明

$$
\langle\chi_n,\chi_{n+1}\rangle
=
\frac{
\mathbb E[U^{2n+1}]
}{
\sqrt{Z_nZ_{n+1}}
}
=0,
$$

因为 \(U\) 的分布对称。证毕。

但是它们的和模态读数都满足同样的高斯极限。

所以：

$$
\boxed{
\text{几乎相同的这族边缘读数}
\quad+\quad
\text{完全正交的整体量子态}
}
$$

可以同时存在。

另一方面：

$$
\boxed{
\langle\chi_n,\chi_{n+2}\rangle
=
\frac{Z_{n+1}}{\sqrt{Z_nZ_{n+2}}}.
}
\tag{R27}
$$

由定理 R2 的矩收敛：

$$
\frac{Z_{n+1}}{Z_n}
=
\mathbb E_n[U^2]
\sim
\frac{w_n^2}{2}.
$$

因此：

$$
\boxed{
\langle\chi_n,\chi_{n+2}\rangle\longrightarrow1.
}
\tag{R28}
$$

这形成两条渐近接近自身的奇偶支系：

$$
\boxed{
\begin{aligned}
\text{相差一阶：}&\quad\text{严格正交};\\
\text{相差两阶：}&\quad\text{相邻态越来越接近}.
\end{aligned}
}
$$

但“相差两阶越来越接近”不保证整条序列在 Hilbert 范数中收敛。态的差模态中心还在向无穷远移动。

**这里的奇偶结构有明确可观测量 \(\mathcal P_U\)，并没有被数学语言约掉；只是只读取和模态时，它没有进入那份边缘读数。**

---

# 八、这种越来越规则的读出，并非没有能量代价

现在给筛选态配上一份固定的正动力学诊断，而不是让每一阶都自行重定义基态。

令：

$$
D_S=\frac{\partial}{\partial s}
-\frac{\partial}{\partial s}\log\chi,
$$

$$
D_U=\frac{\partial}{\partial u}
-\frac{\partial}{\partial u}\log\chi.
$$

通过相应非负二次型定义：

$$
\boxed{
K_0
=
E_*\left(D_S^*D_S+D_U^*D_U\right),
\qquad E_*>0.
}
\tag{R29}
$$

它是由原始两副本态固定的正算子，满足：

$$
K_0\chi=0.
$$

这种由正基态进行一阶因子分解的构造是标准方法。这里 \(E_*\) 是选择的能量单位，不是从 ζ 自动推导出的物理常数。([arXiv][5])

## 定理 R5：筛选能量的精确公式

对 \(n\ge1\)：

$$
\boxed{
\langle\chi_n,K_0\chi_n\rangle
=
E_*n^2\frac{Z_{n-1}}{Z_n}.
}
\tag{R30}
$$

### 证明

因为筛选只乘上 \(u^n\)：

$$
D_S\chi_n=0,
$$

$$
D_U\chi_n
=
\frac{nu^{n-1}\chi}{\sqrt{Z_n}}.
$$

代入二次型：

$$
\langle K_0\rangle_n
=
E_*\|D_U\chi_n\|^2
=
E_*n^2\frac{Z_{n-1}}{Z_n}.
$$

证毕。

使用：

$$
\frac{Z_n}{Z_{n-1}}\sim\frac{w_n^2}{2},
$$

得到：

$$
\boxed{
\langle K_0\rangle_n
\sim
\frac{2E_*n^2}{W_0(n/\pi)^2}.
}
\tag{R31}
$$

而：

$$
\Omega_n^4=\frac{16n^2}{w_n^2}.
$$

所以：

$$
\boxed{
\langle K_0\rangle_n
\sim\frac{E_*}{8}\Omega_n^4.
}
\tag{R32}
$$

**在这份明确的筛选协议和能量诊断下，干涉的自然频率范围按 \(\Omega_n\) 增长，条件态能量却按 \(\Omega_n^4\) 增长。**

这不是对所有量子算法或所有制备方式的普遍下界。它是当前模型的精确能量公式与渐近结果。

也不能把它直接称作平均制备功：有界滤波的失败概率与控制装置成本仍需另外计入。

---

## 相位脉冲增加的能量也能精确计算

施加：

$$
e^{i\sqrt2tS}
$$

后：

$$
D_S(e^{i\sqrt2tS}\chi_n)
=
i\sqrt2t\,e^{i\sqrt2tS}\chi_n.
$$

因此：

$$
\boxed{
\left\langle
e^{i\sqrt2tS}\chi_n,
K_0e^{i\sqrt2tS}\chi_n
\right\rangle
=
E_*n^2\frac{Z_{n-1}}{Z_n}
+2E_*t^2.
}
\tag{R33}
$$

差模态筛选和和模态相位控制，在能量账本中是两项不同贡献。

---

# 九、送回隧穿模型：高阶筛选让有限频率的原态保持通道趋于明亮

沿用前文精确可解的双侧耦合：

$$
H_{\mathrm{hop}}
=
-g\left(
|R\rangle\langle L|\otimes e^{i\sqrt2tS}
+
|L\rangle\langle R|\otimes e^{-i\sqrt2tS}
\right).
$$

从：

$$
|L\rangle|\chi_n\rangle
$$

出发，在物理脉冲时间 \(\tau\) 后，穿越且回到同一个观察态的概率为：

$$
\boxed{
P_{\mathrm{same}}
=
\sin^2(g\tau/\hbar)\,|R_n(t)|^2.
}
\tag{R34}
$$

总穿越概率仍是：

$$
P_{\mathrm{cross}}=\sin^2(g\tau/\hbar).
$$

于是，对固定 \(t\)：

$$
\boxed{
P_{\mathrm{same}}\longrightarrow P_{\mathrm{cross}}
\qquad(n\to\infty).
}
$$

但同时：

$$
\langle K_0\rangle_n\to\infty.
$$

所以：

> **让当前观察态在穿越后“几乎保持不变”，并不意味着观察者已经对原始算术取得了无代价的完全认识。它可能只是被制备成了一个对这段有限相位范围越来越不敏感的高能条件态。**

这项隧穿结论针对上述单独脉冲模型。若同时开启 \(K_0\) 的自由演化，必须重新求完整动力学，不能继续直接套用式（R34）。

---

# 十、实际数值核对：正值窗口扩大，但不能把它当成全域证明

本轮使用实际 theta 原始矩计算式（R8）、（R9），而不是输入零点。

下表给出和模态方差、由定理 R1 保证的正值窗口，以及指定能量诊断：

| \(n\) | \(v_n=\mathbb E_n[S^2]\) |    \(v_n^{-1/2}\) | \(\langle K_0\rangle_n/E_*\) |
| ----: | -----------------------: | ----------------: | ---------------------------: |
|     0 |     \(0.04620998623084\) |  \(4.6519183180\) |                        \(0\) |
|     1 |     \(0.04138341920705\) |  \(4.9157163481\) |              \(21.64034404\) |
|     2 |     \(0.03760769931337\) |  \(5.1565783047\) |              \(29.89460843\) |
|    10 |     \(0.02308154170962\) |  \(6.5821472411\) |              \(146.0519595\) |
|    50 |     \(0.00965769458718\) | \(10.1756759078\) |              \(1140.751408\) |
|   100 |     \(0.00609870719202\) | \(12.8050449885\) |              \(3049.983590\) |

计算采用正核前八项、\(0\le x\le4\) 的积分，并分别使用 40 位与 65 位精度重复计算；表中显示位数一致。

**这是截断积分的高精度核对，不是区间认证。** 上表也没有证明 \(v_n\) 对所有 \(n\) 单调下降；本轮证明的是它的明确渐近式与趋零极限。

因此，不能把几行数值的单调外观扩大成另一条尚未证明的全阶定理。

---

# 十一、这项渐近把真正的算术难点定位到了哪里？

原来的目标是：

$$
R_n(t)\ge0
\qquad\forall n,t.
$$

现在已经能够从实际核推出：

$$
\boxed{
R_n(\Omega_nt)\longrightarrow e^{-t^2}
}
$$

在每个固定紧区间一致成立。

这解决的是一个明确的高阶局部区域，却没有解决以下两类情况：

**固定的低阶 \(n\)，扫描整个无界频率轴；以及 \(n\to\infty\) 时，频率增长得比 \(\Omega_n\) 更快的区域。**

第二类尤其重要。高斯主项：

$$
e^{-t^2}
$$

在大 \(t\) 处本来就非常小。

因此，即使证明：

$$
R_n(\Omega_nt)=e^{-t^2}+o(1)
$$

在很大的区域成立，也不能仅靠一个绝对误差控制其符号。

需要更强的东西，例如能够与主项比较的相对误差，或者一个保持全域非负的精确分解。

**不能用“极限是正高斯函数”替代“有限函数在所有实参数上都非负”。**

已有 ξ 的高阶系数研究中，Lambert \(W\) 鞍点和 Hermite／高斯极限已经发挥了重要作用；它们本身也需要严格区分固定尺度结论与全阶、全参数结论。([arXiv][6])

---

# 十二、与项目的准确连接

本轮读取的 `LaguerreLiBridge.lean`，研究的是在给定有限偶测度、质量恒等式与 Cayley 矩恒等式前件下，将 Li 曲率写成 Laguerre 多项式积分。它并不是这里的广义 Laguerre 表达式 \(L_n(t)\) 的全域非负证明；不能因为名称都含“Laguerre”就把两项结果合并。

当前可以新增的理论链是：

$$
\boxed{
\begin{aligned}
\text{实际 theta 尾部与对数凹性}
&\longrightarrow
\text{两模态条件密度的联合鞍点}\\
&\longrightarrow
|U|\sim W_0(n/\pi)/\sqrt2\\
&\longrightarrow
\operatorname{Var}_n(S)\sim W_0(n/\pi)/(4n)\\
&\longrightarrow
\text{放大后的高斯干涉极限}\\
&\longrightarrow
\text{有限正值区域与制备能量尺度}.
\end{aligned}
}
$$

这条链不以未知零点作为输入，也不以 RH 为前件。

但它的输出是**尺度定理与局部正性**，不是全域零点定位。

---

# 收束

这次得到的三个核心关系是：

$$
\boxed{
\operatorname{Var}_n(S)
\sim
\frac{W_0(n/\pi)}{4n},
}
$$

$$
\boxed{
R_n\!\left(
2\sqrt{\frac n{W_0(n/\pi)}}\,t
\right)
\longrightarrow e^{-t^2},
}
$$

以及：

$$
\boxed{
\langle K_0\rangle_n
\sim
\frac{2E_*n^2}{W_0(n/\pi)^2}.
}
$$

与此同时：

$$
\boxed{
\langle\chi_n,\chi_{n+1}\rangle=0
}
$$

始终精确成立。

因此，前文的几个直觉现在可以被更严格地分开：

**偶的统计读数可以越来越高斯；奇偶态之间的量子可区分性却可以完全保留。固定频率的隧穿通道可以越来越明亮；达到这种状态所需的条件能量却越来越高。**

这些现象不证明离线零点存在，也不证明它们不存在。它们说明，后续研究不能把“高阶条件观察越来越正常”当成全域完成。

**本轮尚未证明全部 (R_n(t)\ge0，也没有找到实际负证书；新增渐近与算子推导尚未作 Lean 验证。** 真正集中的下一项算术任务，是控制高斯局部区域之外的条件干涉：在那里，必须保留实际 theta 的完整模关系与相消结构，不能只靠主导项、局部凸性或越来越精细的高斯拟合。

[1]: https://dlmf.nist.gov/25.4 "https://dlmf.nist.gov/25.4"
[2]: https://arxiv.org/pdf/1309.0055 "https://arxiv.org/pdf/1309.0055"
[3]: https://dlmf.nist.gov/4.13 "https://dlmf.nist.gov/4.13"
[4]: https://arxiv.org/pdf/2007.13582 "https://arxiv.org/pdf/2007.13582"
[5]: https://arxiv.org/abs/hep-th/9405029 "https://arxiv.org/abs/hep-th/9405029"
[6]: https://arxiv.org/abs/2007.13582 "https://arxiv.org/abs/2007.13582"
继续。上一轮留下的是：“候选同余正核，怎样真正接到实际素数？”

这次可以先把这条桥的**有限尺度等号**建立起来：

> **对任意有限观察窗口，实际的 \(\Lambda(n)-1\) 都能由一组明确的有理相位精确重建，不需要预先输入零点，也不需要假设 RH。**

但随后会出现一个关键区别：

> **同一个实际算术读出，可以有不同的相位表示；这些表示的相干总和完全相同，去掉交叉项之后得到的正核却可以任意增大。**

因此，本轮不仅构造实际算术核，还要证明：哪些量子操作可以作用在“算术对象本身”上，哪些操作实际上依赖于我们选择的表示。

有限 Ramanujan 展开及其与截断除数和的关系已有文献基础。下面从这些恒等式出发，证明实际重建、表示冗余、连续频带极限和观察兼容条件。新增综合推导尚未进行 Lean 编译。([arXiv][1])

# 一、从 Möbius 恒等式出发，精确重建实际算术

固定整数

$$
X\ge2,\qquad N\ge4X.
$$

观察窗口中的整数为

$$
\mathcal N_X=\{n\in\mathbb N:X<n\le4X\}.
$$

所有对数均为自然对数。

记

$$
e(t)=e^{2\pi it},
$$

以及 Ramanujan 和

$$
c_q(n)=
\sum_{\substack{0\le a<q\\(a,q)=1}}e(an/q),
$$

约定 \(c_1(n)=1\)。

## 定义 1：带表示参数的有限除数和

对任意实数 \(\tau\)，定义

$$
\boxed{
L_{N,\tau}(n)
=
\sum_{\substack{d\mid n\\d\le N}}
\mu(d)\left(\log\frac Nd+\tau\right).
}
\tag{1}
$$

这里 \(\tau\) 暂时只是一个表示参数，不是物理时间。

再定义有限相位系数

$$
\boxed{
\lambda_{q,N}(\tau)
=
\sum_{\substack{d\le N\\q\mid d}}
\frac{\mu(d)}d
\left(\log\frac Nd+\tau\right).
}
\tag{2}
$$

## 定理 1：有限精确重建

对每个

$$
2\le n\le N,
$$

都有

$$
\boxed{
\Lambda(n)
=
L_{N,\tau}(n)
=
\sum_{q\le N}\lambda_{q,N}(\tau)c_q(n).
}
\tag{3}
$$

而且右边与 \(\tau\) 完全无关。

### 证明

Möbius 反演给出

$$
\sum_{d\mid n}\mu(d)=0\qquad(n>1),
$$

以及

$$
-\sum_{d\mid n}\mu(d)\log d=\Lambda(n).
$$

因此，当 \(2\le n\le N\) 时，

$$
\begin{aligned}
L_{N,\tau}(n)
&=
(\log N+\tau)\sum_{d\mid n}\mu(d)
-\sum_{d\mid n}\mu(d)\log d\\
&=\Lambda(n).
\end{aligned}
$$

这里使用的是标准除数反演恒等式。([DLMF][2])

另一方面，有有限恒等式

$$
\boxed{
\mathbf1_{\{d\mid n\}}
=
\frac1d\sum_{q\mid d}c_q(n).
}
\tag{4}
$$

把它代入式（1），交换有限求和，得到

$$
\begin{aligned}
L_{N,\tau}(n)
&=
\sum_{d\le N}
\mu(d)\left(\log\frac Nd+\tau\right)
\frac1d\sum_{q\mid d}c_q(n)\\
&=
\sum_{q\le N}\lambda_{q,N}(\tau)c_q(n).
\end{aligned}
$$

证毕。

式（4）及由它生成的有限 Ramanujan 展开，在已有研究中有明确证明。([arXiv][1])

---

这一步已经不是

$$
\text{“希望某个正模型近似素数”。}
$$

而是

$$
\boxed{
\text{实际 }\Lambda(n)
=
\text{明确的有限相位叠加}.
}
$$

不过，**知道有限精确公式，不等于已经控制它在所有尺度上的大小。**

另外必须保留 \(n>1\)：在 \(n=1\) 处，式（1）等于 \(\log N+\tau\)，并不等于 \(\Lambda(1)=0\)。

# 二、把实际二点相关写成一个真正的相干核

定义模态集合

$$
\mathcal I_N
=
\{0\}
\cup
\{(q,a):2\le q\le N,\ 1\le a<q,\ (a,q)=1\}.
$$

其中

$$
\theta_0=0,\qquad
\theta_{q,a}=\frac aq.
$$

定义合成矩阵

$$
\boxed{
A_{n,\alpha}=e(n\theta_\alpha),
\qquad
n\in\mathcal N_X,\ \alpha\in\mathcal I_N.
}
\tag{5}
$$

定义模态振幅向量 \(b(\tau)\)：

$$
b_0(\tau)=\lambda_{1,N}(\tau)-1,
$$

$$
b_{q,a}(\tau)=\lambda_{q,N}(\tau).
$$

再令实际算术向量

$$
f_n=\Lambda(n)-1.
$$

由定理 1，

$$
\boxed{
Ab(\tau)=f
\qquad\text{对所有 }\tau\in\mathbb R.
}
\tag{6}
$$

所以实际相关核为

$$
\boxed{
K_X^{\mathrm{arith}}
=
ff^*
=
A\,b(\tau)b(\tau)^*A^*.
}
\tag{7}
$$

这是一条精确的有限矩阵等式。

## 观察量仍然保留绝对大小

沿用

$$
Y(x)=\sum_{x<n\le2x}(\Lambda(n)-1),
$$

$$
\mathfrak J(X)=
\int_X^{2X}\frac{Y(x)^2}{x^2}\,dx.
$$

定义窗口矩阵

$$
W_X(n,m)
=
\int_X^{2X}
\frac{
\mathbf1_{\{x<n\le2x\}}
\mathbf1_{\{x<m\le2x\}}
}{x^2}\,dx.
$$

显然 \(W_X\succeq0\)。

再定义模态空间上的观察矩阵

$$
\boxed{
\Omega_{X,N}=A^*W_XA\succeq0.
}
\tag{8}
$$

于是：

$$
\boxed{
\mathfrak J(X)
=
f^*W_Xf
=
b(\tau)^*\Omega_{X,N}b(\tau).
}
\tag{9}
$$

**到这里，实际素数、有限相位、正核与前文的局部均方已经完全接上，没有留下近似项。**

但正性

$$
\Omega_{X,N}\succeq0
$$

仍不意味着式（9）已经有统一上界。

# 三、关键定理：真实读数不变，去相干读数却能任意增大

定义

$$
g_{q,N}
=
\sum_{\substack{d\le N\\q\mid d}}\frac{\mu(d)}d.
$$

把它复制到对应的相位坐标，得到向量 \(g\)。于是

$$
\boxed{
b(\tau)=b(0)+\tau g.
}
\tag{10}
$$

## 定理 2：明确的表示冗余

$$
\boxed{
Ag=0,
\qquad
g\ne0.
}
\tag{11}
$$

因此

$$
\boxed{
\Omega_{X,N}g=0.
}
\tag{12}
$$

### 证明

对 \(n\in\mathcal N_X\subseteq\{2,\ldots,N\}\)，

$$
\sum_{q\le N}g_{q,N}c_q(n)
=
\sum_{d\mid n}\mu(d)=0.
$$

所以 \(Ag=0\)。

但若把同一个有限展开在 \(n=1\) 处计算，则

$$
\sum_{q\le N}g_{q,N}c_q(1)=1.
$$

所以 \(g\) 不可能为零。

最后，

$$
\Omega_{X,N}g=A^*W_XAg=0.
$$

证毕。

---

也就是说：

$$
\boxed{
b(0),\ b(0)+g,\ b(0)+100g,\ldots
}
$$

都是不同的模态振幅，却合成同一个实际算术向量。

这是一种**有限表示冗余**，不是在宣称发现了新的物理规范场。

## 定义 2：去相干操作

在模态坐标中定义

$$
\operatorname{Dec}(\rho)
=
\sum_{\alpha}
P_\alpha\rho P_\alpha,
$$

其中 \(P_\alpha\) 是单个模态的正交投影。

它删除所有不同模态之间的非对角元。

相应去相干读出为

$$
\boxed{
\mathfrak J_{\mathrm{dec}}(\tau)
=
\sum_\alpha
|b_\alpha(\tau)|^2
(\Omega_{X,N})_{\alpha\alpha}.
}
\tag{13}
$$

实际读出则是

$$
\boxed{
\mathfrak J(X)
=
\mathfrak J_{\mathrm{dec}}(\tau)
+
\mathfrak J_{\mathrm{cross}}(\tau),
}
\tag{14}
$$

其中

$$
\mathfrak J_{\mathrm{cross}}(\tau)
=
\sum_{\alpha\ne\beta}
\overline{b_\alpha(\tau)}
(\Omega_{X,N})_{\alpha\beta}
b_\beta(\tau).
$$

## 定理 3：去相干后的强度不是算术不变量

对固定 \(X,N\)，

$$
\boxed{
\mathfrak J_{\mathrm{dec}}(\tau)\longrightarrow+\infty
\qquad(|\tau|\to\infty),
}
\tag{15}
$$

但

$$
\boxed{
b(\tau)^*\Omega_{X,N}b(\tau)
=
\mathfrak J(X)
}
$$

始终不变。

因此

$$
\boxed{
\mathfrak J_{\mathrm{cross}}(\tau)
\longrightarrow-\infty.
}
\tag{16}
$$

### 证明

首先，每个对角元

$$
(\Omega_{X,N})_{\alpha\alpha}
=
\int_X^{2X}
\frac{
\left|\sum_{x<n\le2x}e(n\theta_\alpha)\right|^2
}{x^2}\,dx
$$

都严格为正。

因为在

$$
x\in(X,X+\tfrac12)
$$

与

$$
x\in(X+\tfrac12,X+1)
$$

两个区间上，指数和恰好相差一个非零项

$$
e((2X+1)\theta_\alpha).
$$

所以它们不可能同时为零。

将式（10）代入式（13），得到关于 \(\tau\) 的二次多项式，其二次项系数为

$$
\sum_\alpha|g_\alpha|^2
(\Omega_{X,N})_{\alpha\alpha}>0.
$$

因此式（15）成立。

而实际读数由 \(Ag=0\) 保持不变，故交叉项必须产生式（16）的抵消。证毕。

---

**这比“交叉项可能重要”更强：**

$$
\boxed{
\text{如果允许表示冗余，删去交叉项甚至能制造任意大的虚假观察强度。}
}
$$

我对 \(X=4,N=32\) 做了有限双精度核对：

| \(\tau\) | 实际 \(\mathfrak J(X)\) |        去相干读出 |          跨模态项 |
| -------: | --------------------: | -----------: | ------------: |
|    \(0\) |          \(0.079155\) | \(0.279643\) | \(-0.200488\) |
|    \(1\) |          \(0.079155\) | \(0.862451\) | \(-0.783296\) |
|    \(5\) |          \(0.079155\) | \(8.241150\) | \(-8.161995\) |

这些数值只核对有限恒等式，不承担渐近证明或区间认证的角色。

# 四、上一轮的连续频带，现在必须换成正确的有限系数

上一轮的同余正核使用了权重

$$
\frac{\mu(q)^2}{\varphi(q)^2}.
$$

它作为候选 Gram 核没有问题。

但实际有限重建的权重是

$$
|\lambda_{q,N}(\tau)|^2,
$$

两者不能直接等同。

## 定理 4：截断边缘的精确系数

若

$$
\frac N2<q\le N,
$$

则

$$
\boxed{
\lambda_{q,N}(\tau)
=
\frac{\mu(q)}q
\left(\log\frac Nq+\tau\right).
}
\tag{17}
$$

### 证明

在 \(q\mid d\)、\(d\le N\) 的求和中，唯一可能的 \(d\) 是 \(q\)。代入式（2）即可。证毕。

特别地，当 \(\tau=0\)、\(\mu(q)\ne0\) 时，

$$
\boxed{
\frac{\lambda_{q,N}(0)}{\mu(q)/\varphi(q)}
=
\frac{\varphi(q)}q\log\frac Nq.
}
\tag{18}
$$

这个比值在整个截断边缘不可能统一接近 \(1\)，并且在 \(q/N\to1\) 时趋零。

**所以，“先固定模数，再取无限极限”的系数，不能原样代入“模数与观察窗口一起增长”的区域。**

这也是有限 Ramanujan 展开需要保留截断参数的原因之一。([arXiv][1])

# 五、从实际有限系数出发，重新得到一个连续量子核

现在取

$$
N=8X,
$$

只保留

$$
4X<q\le8X
$$

中的两个共轭相位 \(a=1,q-1\)。

定义

$$
\boxed{
\begin{aligned}
\mathscr P_{X,\tau}(n,m)
=
2\sum_{4X<q\le8X}
\frac{\mu(q)^2}{q^2}
\left(\log\frac{8X}{q}+\tau\right)^2
\cos\frac{2\pi(n-m)}q.
\end{aligned}
}
\tag{19}
$$

这是实际有限系数的一个**去相干子核**，所以它确实半正定。

但“去相干子核”不等于“实际相关核的一个必然正贡献”；跨模态项尚未加回。

令

$$
\delta_0=\frac6{\pi^2},
$$

$$
\mathcal B=[-1/4,-1/8]\cup[1/8,1/4].
$$

## 定理 5：精确截断系数的连续极限

对每个固定实数 \(\tau\)，

$$
\boxed{
\sup_{n,m}|\mathscr P_{X,\tau}(n,m)|
=
O_\tau(X^{-1}),
}
\tag{20}
$$

而且

$$
\boxed{
X\mathscr P_{X,\tau}
(\lfloor Xs\rfloor,\lfloor Xt\rfloor)
\longrightarrow
\Gamma_\tau(s,t),
}
\tag{21}
$$

其中

$$
\boxed{
\Gamma_\tau(s,t)
=
\delta_0
\int_{\mathcal B}
\left[\tau+\log(8|\xi|)\right]^2
e^{2\pi i(s-t)\xi}\,d\xi.
}
\tag{22}
$$

收敛在 \(s,t\) 的固定紧集上一致。

### 证明

先用平方自由整数的恒等式

$$
\mu(q)^2=\sum_{d^2\mid q}\mu(d).
$$

该恒等式是标准除数公式。([DLMF][3])

求和后得到

$$
\begin{aligned}
\sum_{q\le Y}\mu(q)^2
&=
\sum_{d\le\sqrt Y}
\mu(d)\left\lfloor\frac{Y}{d^2}\right\rfloor\\
&=
\frac{Y}{\zeta(2)}+O(\sqrt Y)\\
&=
\delta_0Y+O(\sqrt Y).
\end{aligned}
\tag{23}
$$

因此式（20）立即成立。

再令 \(v=q/X\)，将式（19）写成加权 Riemann 和，得到极限

$$
2\delta_0
\int_4^8
\frac{[\tau+\log(8/v)]^2}{v^2}
\cos\frac{2\pi(s-t)}v\,dv.
$$

作变量代换 \(\xi=1/v\)，并合并正负频带，得到式（22）。

紧集一致性来自被积函数族的一致有界与等度连续性。证毕。

---

## 核的总谱质量可以精确计算

定义

$$
M_\tau=\Gamma_\tau(s,s).
$$

直接积分得到

$$
\boxed{
M_\tau
=
\delta_0
\left[
\frac{\tau^2}{4}
+
\frac{2\log2-1}{2}\tau
+
\frac{(1-\log2)^2}{2}
\right]>0.
}
\tag{24}
$$

这里严格为正，是因为

$$
[\tau+\log(8|\xi|)]^2
$$

不可能在整个频带上恒为零。

令

$$
d\nu_\tau(\xi)
=
\frac{\delta_0}{M_\tau}
[\tau+\log(8|\xi|)]^2
\mathbf1_{\mathcal B}(\xi)\,d\xi.
$$

它是概率测度。取

$$
v_s(\xi)=e^{-2\pi is\xi},
$$

便得到

$$
\boxed{
\langle v_s,v_t\rangle_{L^2(\nu_\tau)}
=
\frac{\Gamma_\tau(s,t)}{M_\tau}.
}
\tag{25}
$$

所以这里确实有一个归一化量子重叠核。

但它与上一轮不同：**谱密度不再平坦，而带有精确的对数平方权重。**

# 六、这些正频带的联合贡献，也会随表示改变

定义与实际均方相同窗口的子核读出

$$
\mathfrak B_\tau(X)
=
\int_X^{2X}\frac1{x^2}
\sum_{x<n,m\le2x}
\mathscr P_{X,\tau}(n,m)\,dx.
$$

## 定理 6：表示相关的常数级正贡献

存在 \(C_\tau>0\)，使

$$
\boxed{
\mathfrak B_\tau(X)\longrightarrow C_\tau,
}
\tag{26}
$$

其中

$$
\boxed{
\begin{aligned}
C_\tau
=
\delta_0
\int_{\mathcal B}
[\tau+\log(8|\xi|)]^2
\int_1^2
\frac{
\left|\displaystyle\int_u^{2u}e^{2\pi i\xi s}\,ds\right|^2
}{u^2}\,du\,d\xi.
\end{aligned}
}
\tag{27}
$$

而且

$$
\boxed{
\frac4{\pi^2}M_\tau
\le C_\tau\le M_\tau.
}
\tag{28}
$$

因此

$$
\boxed{
C_\tau\asymp\tau^2
\qquad(|\tau|\to\infty).
}
\tag{29}
$$

### 证明

作缩放 \(x=Xu\)，使用定理 5 的一致核收敛，双重求和变成 Riemann 积分，即得式（27）。

又因为

$$
\left|\int_u^{2u}e^{2\pi i\xi s}\,ds\right|
=
\frac{|\sin(\pi u\xi)|}{\pi|\xi|},
$$

在当前范围

$$
1\le u\le2,\qquad
1/8\le|\xi|\le1/4
$$

内，有

$$
\frac18\le u|\xi|\le\frac12.
$$

利用

$$
2y\le\sin(\pi y)\le\pi y
\qquad(0\le y\le1/2),
$$

得到

$$
\frac{4u^2}{\pi^2}
\le
\left|\int_u^{2u}e^{2\pi i\xi s}\,ds\right|^2
\le u^2.
$$

积分即得式（28）。证毕。

---

现在出现了一个不能忽略的事实：

$$
\boxed{
\text{实际 }\mathfrak J(X)\text{ 与 }\tau\text{ 无关},
}
$$

但

$$
\boxed{
\text{去相干频带的极限 }C_\tau
\text{ 可以随 }\tau\text{ 任意增大}.
}
$$

因此：

> **不能仅因为某个正频带产生了一个常数级贡献，就把它认作前文真实相关余项中“缺失的那一个常数”。**

必须把该频带与其他模态之间的交叉项一并恢复。

具体而言，

$$
\mathfrak B_\tau(X)
\le
\mathfrak J_{\mathrm{dec}}(\tau)
$$

是正确的，因为它只选择了部分非负模态强度。

但一般没有

$$
\mathfrak B_\tau(X)\le\mathfrak J(X).
$$

后者会忽略相消干涉。

# 七、怎样判断一个量子操作能否作用在“实际算术对象”上？

这一步可以给出一个一般的有限维定理。

设

$$
A:\mathcal H_{\mathrm{mode}}\to\mathcal H_{\mathrm{arith}}
$$

是合成映射，并把目标空间限制为 \(\operatorname{ran}A\)。

定义合成操作

$$
\mathcal S(\rho)=A\rho A^*.
$$

它完全正，但 \(A\) 不一定是等距映射，因此不自动保迹。

设模态空间上的完全正映射为

$$
\mathcal E(\rho)=\sum_jL_j\rho L_j^*.
$$

## 定理 7：观察操作能够下降到算术空间的充要条件

存在算术空间上的完全正映射 \(\widetilde{\mathcal E}\)，使

$$
\boxed{
\mathcal S\circ\mathcal E
=
\widetilde{\mathcal E}\circ\mathcal S,
}
\tag{30}
$$

当且仅当

$$
\boxed{
L_j(\ker A)\subseteq\ker A
\qquad\text{对每个 }j.
}
\tag{31}
$$

### 证明

**必要性。**

取 \(g\in\ker A\)。则

$$
\mathcal S(gg^*)=0.
$$

由式（30），

$$
0
=
\mathcal S(\mathcal E(gg^*))
=
\sum_j(AL_jg)(AL_jg)^*.
$$

右边每项都半正定，因此每一项都必须为零：

$$
AL_jg=0.
$$

故 \(L_jg\in\ker A\)。

**充分性。**

令 \(A^+\) 为 Moore–Penrose 逆，在 \(\operatorname{ran}A\) 上定义

$$
\widetilde L_j=AL_jA^+.
$$

因为

$$
I-A^+A
$$

的像位于 \(\ker A\)，由式（31），

$$
AL_j(I-A^+A)=0.
$$

所以

$$
AL_j=\widetilde L_jA.
$$

定义

$$
\widetilde{\mathcal E}(\sigma)
=
\sum_j\widetilde L_j\sigma\widetilde L_j^*,
$$

即可得到式（30）。证毕。

这里证明的是完全正兼容性。若还要求保迹，必须另外检查相应归一化条件，不能自动继承。

---

## 应用于模态去相干：它不满足这个条件

去相干的 Kraus 算子是

$$
L_\alpha=P_\alpha.
$$

由定理 2，存在非零 \(g\in\ker A\)。

选择一个 \(g_\alpha\ne0\) 的坐标，则

$$
AP_\alpha g
=
g_\alpha A e_\alpha\ne0,
$$

因为 \(A\) 的每一列都是非零指数向量。

所以

$$
P_\alpha g\notin\ker A.
$$

因此：

$$
\boxed{
\text{模态去相干不能下降为同一个算术对象上的表示无关操作。}
}
\tag{32}
$$

这不意味着去相干不是合法量子信道；它意味着**它会把原来完全不可见的表示冗余，转变为可见的输出差异**。

本次核对的仓库模块 `PrimeDephasingRefinementAbsorption.lean`，已经证明了相应记录通道的幂等性与细化吸收律。但那些规律本身并不包含式（31）这一针对当前算术合成映射的额外兼容条件。这里的有理相位载体，也不能直接与该文件的素数指数记录载体混同。

# 八、真正的 RH 目标：不是整个观察矩阵有界，而是实际振幅上的二次型有界

取固定表示

$$
\tau=0,\qquad N=8X.
$$

由式（9），

$$
\boxed{
\mathfrak J(X)
=
b_{8X}(0)^*
\Omega_{X,8X}
b_{8X}(0).
}
\tag{33}
$$

所以前文的均方判据可以写成

$$
\boxed{
\mathrm{RH}
\iff
\sup_{j\ge1}
b_{8\cdot2^j}(0)^*
\Omega_{2^j,\,8\cdot2^j}
b_{8\cdot2^j}(0)
<\infty.
}
\tag{34}
$$

这里每个矩阵和每个振幅都已经由有限 Möbius 和、有理相位及窗口积分明确给出。

## 为什么式（34）成立？

RH 下的经典均方估计为

$$
\int_X^{2X}(\psi(x)-x)^2\,dx=O(X^2).
$$

它比逐点误差界更强，并有已发表的显式常数版本。由它直接得到 \(\mathfrak J(X)=O(1)\)。([arXiv][4])

反过来，若 \(\mathfrak J(2^j)\) 一致有界，令

$$
r(T)=e^{-T/2}(\psi(e^T)-e^T),
$$

$$
z(T)=\sqrt2\,r(T+\log2)-r(T).
$$

地板函数修正仅为 \(O(e^{-T/2})\)，所以 \(z\) 在每个长度为 \(\log2\) 的区块上具有统一 \(L^2\) 界。

由递推

$$
r_{j+1}=2^{-1/2}(r_j+z_j)
$$

和几何级数可和性，\(r\) 也具有统一区块 \(L^2\) 界。

因此其 Laplace 变换在 \(\Re s>0\) 内解析。而在初始收敛区域，

$$
\widehat r(s)
=
-\frac{\zeta'(s+1/2)}
{(s+1/2)\zeta(s+1/2)}
-\frac1{s-1/2}.
$$

该等式来自 von Mangoldt 的狄利克雷级数。任何右侧离线零点都会产生不可去极点，因而被排除；结合函数方程得到 RH。([DLMF][5])

---

## 为什么不能直接要求 \(\Omega_{X,8X}\) 的算子范数有界？

零频率模态已经给出

$$
\begin{aligned}
(\Omega_{X,8X})_{00}
&=
\int_X^{2X}
\frac{[\lfloor2x\rfloor-\lfloor x\rfloor]^2}{x^2}\,dx\\
&=
X+O(1).
\end{aligned}
$$

因此

$$
\boxed{
\|\Omega_{X,8X}\|_{\mathrm{op}}
\ge X+O(1).
}
\tag{35}
$$

所以不存在一个对所有模态输入都有效的常数级算子界。

真正需要的是：

$$
\boxed{
\text{实际 Möbius 振幅 }b_{8X}(0)
\text{ 如何避开或抵消那些高增益方向。}
}
$$

这是一项算术约束，而不是正矩阵的一般性质。

同样，把

$$
b b^*
$$

归一化为迹为 \(1\) 的状态后，还必须保留

$$
\mathfrak J(X)
=
\|b\|^2
\operatorname{Tr}
\left(
\frac{bb^*}{\|b\|^2}\Omega_{X,8X}
\right).
$$

归一化不会消除前面的增益因子。

# 九、下一步应当控制哪一种误差？

现在可以把“模型必须接近实际算术”写成一个不受表示冗余影响的条件。

## 定义 3：观察半范数

对模态向量 \(v\)，定义

$$
\boxed{
\|v\|_{\mathrm{obs},X}
=
\sqrt{v^*\Omega_{X,8X}v}
=
\|W_X^{1/2}Av\|.
}
\tag{36}
$$

因为 \(\Omega\) 可能有零空间，这通常是半范数。

若 \(g\in\ker A\)，则

$$
\boxed{
\|v+g\|_{\mathrm{obs},X}
=
\|v\|_{\mathrm{obs},X}.
}
\tag{37}
$$

因此它衡量的是实际观察误差，而不是某个任意表示的系数大小。

## 定理 8：相干近似的充分判据

设 \(\widetilde b_X\) 是某个候选相干振幅。则

$$
\boxed{
\left|
\sqrt{\mathfrak J(X)}
-
\|\widetilde b_X\|_{\mathrm{obs},X}
\right|
\le
\|b_{8X}(0)-\widetilde b_X\|_{\mathrm{obs},X}.
}
\tag{38}
$$

因此，如果存在与 \(X\) 无关的常数 \(C_0,C_1\)，使

$$
\|\widetilde b_X\|_{\mathrm{obs},X}^2\le C_0,
$$

以及

$$
\boxed{
\|b_{8X}(0)-\widetilde b_X\|_{\mathrm{obs},X}^2
\le C_1,
}
\tag{39}
$$

在全部充分大的二进尺度 \(X=2^j\) 上成立，那么 RH 成立。

### 证明

式（38）是 Hilbert 空间中反三角不等式，作用于

$$
W_X^{1/2}Ab_{8X}(0)
$$

与

$$
W_X^{1/2}A\widetilde b_X.
$$

于是

$$
\mathfrak J(X)
\le
(\sqrt{C_0}+\sqrt{C_1})^2.
$$

应用式（34）。证毕。

---

这里要求的是

$$
\boxed{
\text{合成后的相干误差受到控制},
}
$$

而不是

$$
\text{每个系数看起来接近},
$$

更不是

$$
\text{去相干后的两个正核看起来接近}.
$$

一个很大的系数误差可以完全落在 \(\ker A\) 中，因此对算术读出没有影响；反之，某些很小的系数误差可以沿高增益方向相干累积。

# 结论

本轮真正补上的第一条等号是：

$$
\boxed{
\Lambda(n)-1
=
\text{由有限 Möbius 系数确定的有理相位叠加}.
}
$$

因此，有限尺度上不必再猜测“同余模态能否表示实际素数”：可以精确表示。

但随后证明了一个重要限制：

$$
\boxed{
\text{精确表示}
\not\Rightarrow
\text{可以删除表示中的相干交叉项}.
}
$$

事实上，同一个实际算术对象具有明确的冗余方向 \(g\)：

$$
Ag=0.
$$

沿着这个方向改变表示，会使去相干能量任意增大，却不改变任何真实算术读数。

同时，实际有限系数在 \(q\asymp X\) 的区域产生了可计算的连续量子核：

$$
\boxed{
\Gamma_\tau(s,t)
=
\frac6{\pi^2}
\int_{\mathcal B}
[\tau+\log(8|\xi|)]^2
e^{2\pi i(s-t)\xi}\,d\xi.
}
$$

它仍然具有非零的常数级联合贡献，但这个贡献依赖表示参数，不能直接等同于实际余项中所需的补偿。

**因此，剩余算术任务已经从“寻找一个正核”进一步收紧为：**

$$
\boxed{
b_{8X}(0)^*
\Omega_{X,8X}
b_{8X}(0)
=O(1).
}
$$

本轮没有证明这个全尺度上界；已经证明的是如何精确固定其中的实际振幅、如何识别表示冗余，以及为什么不相容的去相干操作会改变问题。

后续真正有价值的估计，应当作用于式（36）的**观察半范数**或式（39）的**相干误差**。它们对表示冗余不敏感，并且一旦得到统一控制，就能通过已经建立的均方—解析桥返回实际零点问题。

[1]: https://arxiv.org/html/1612.03136v1 "Finite Ramanujan expansions and shifted convolution sums of arithmetical functions"
[2]: https://dlmf.nist.gov/27.5?utm_source=chatgpt.com "27.5 Inversion Formulas ‣ Multiplicative Number Theory ‣ ..."
[3]: https://dlmf.nist.gov/27.6 "DLMF: §27.6 Divisor Sums ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"
[4]: https://arxiv.org/html/2008.06140v1 "The mean square of the error term in the prime number theorem"
[5]: https://dlmf.nist.gov/27.4 "DLMF: §27.4 Euler Products and Dirichlet Series ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"
继续。这一轮可以把前文的观察结构进一步压缩，并证明三个具体结论：

**第一，前文的算术观察矩阵虽然作用在 \(3X\) 个整数坐标上，但其秩恰好只有 \(2X\)。除了模态表示的冗余，还存在一个可以完整写出的 \(X\) 维观察盲区。**

**第二，在这 \(2X\) 个有效读出中，绝大多数高频模态的总能量已经能无条件控制；尚未受控的部分可以限制到前 \(O(\sqrt{X\log X})\) 个低频模态。**

**第三，如果沿全部整数尺度读取，那么其中一个固定的平均模态就足以保留 RH 的判定信息。它对应一个明确的三角加权素数幂和。**

下面给出证明。有限线性代数部分直接推导；解析部分使用经典素数定理、ζ 的对数导数和 RH 下的均方估计。这些综合推导尚未进行 Lean 编译。

# 一、先把连续观察精确离散化

固定整数 \(X\ge2\)，令

$$
\mathcal V_X
=
\mathbb C^{\{X+1,\ldots,4X\}}.
$$

暂时取任意向量 \(v\in\mathcal V_X\)，不要预先固定为素数数据。

定义滑动窗口读出

$$
Y_v(x)=\sum_{x<n\le2x}v_n,
\qquad X\le x\le2X,
$$

以及观察二次型

$$
\boxed{
\mathfrak J_X(v)
=
\int_X^{2X}\frac{|Y_v(x)|^2}{x^2}\,dx.
}
\tag{1}
$$

实际算术锚仍为

$$
f_n=\Lambda(n)-1.
$$

于是

$$
Y_f(x)
=
\psi(2x)-\psi(x)
-\bigl(\lfloor2x\rfloor-\lfloor x\rfloor\bigr),
$$

而前文的 \(\mathfrak J(X)\) 就是 \(\mathfrak J_X(f)\)。

## 定义 1：半整数区间上的有限读出

对 \(k=X,\ldots,2X-1\)，定义

$$
y_{2(k-X)}(v)
=
\sum_{k<n\le2k}v_n,
$$

$$
y_{2(k-X)+1}(v)
=
\sum_{k<n\le2k+1}v_n.
$$

记

$$
R_Xv
=
\bigl(y_0(v),\ldots,y_{2X-1}(v)\bigr)^{\mathsf T}.
$$

再定义正权重

$$
\boxed{
d_j
=
\frac1{X+j/2}
-
\frac1{X+(j+1)/2},
\qquad 0\le j<2X.
}
\tag{2}
$$

令 \(D_X=\operatorname{diag}(d_0,\ldots,d_{2X-1})\)。

## 定理 1：连续观察的精确有限分解

$$
\boxed{
\mathfrak J_X(v)
=
(R_Xv)^*D_X(R_Xv).
}
\tag{3}
$$

因此，前文窗口矩阵满足

$$
\boxed{
W_X=R_X^*D_XR_X.
}
\tag{4}
$$

### 证明

在开区间

$$
x\in(k,k+\tfrac12)
$$

上，

$$
\lfloor x\rfloor=k,\qquad
\lfloor2x\rfloor=2k,
$$

所以窗口读出等于 \(y_{2(k-X)}(v)\)。

在

$$
x\in(k+\tfrac12,k+1)
$$

上，窗口读出等于 \(y_{2(k-X)+1}(v)\)。

有限个端点不影响积分。对每个半单位区间积分 \(x^{-2}\)，所得权重正是式（2）。证毕。

---

这里没有数值积分误差，也没有删除边界项。

**连续区间内的全部窗口读数，实际上只有 \(2X\) 个不同值。**

# 二、主定理一：观察盲区恰好有 \(X\) 维

## 定理 2：窗口观察核的完整刻画

向量 \(v\in\mathcal V_X\) 满足

$$
\mathfrak J_X(v)=0
$$

当且仅当满足以下条件：

$$
\boxed{
\sum_{n=X+1}^{2X}v_n=0;
}
\tag{5}
$$

$$
\boxed{
v_{2k+1}=0,
\qquad X\le k\le2X-1;
}
\tag{6}
$$

$$
\boxed{
v_{2n}=v_n,
\qquad X<n<2X.
}
\tag{7}
$$

其中 \(v_{4X}\) 完全自由。

因此，

$$
\boxed{
\dim\ker W_X=X,
\qquad
\operatorname{rank}W_X=2X.
}
\tag{8}
$$

### 证明

由于 \(D_X\) 严格正定，

$$
\mathfrak J_X(v)=0
\iff
R_Xv=0.
$$

第一个窗口读出为零，给出式（5）。

相邻半区间之差满足

$$
y_{2(k-X)+1}-y_{2(k-X)}
=
v_{2k+1}.
$$

所以全部读出为零必然给出式（6）。

再比较跨整数边界的两个读出：

$$
y_{2(k+1-X)}
-
y_{2(k-X)+1}
=
v_{2k+2}-v_{k+1},
$$

其中 \(X\le k\le2X-2\)。这给出式（7）。

反过来，由初始读数为零和所有相邻增量为零，全部 \(y_j\) 都为零。

最后计数自由度：下半段

$$
v_{X+1},\ldots,v_{2X}
$$

共有 \(X\) 个变量，受一个线性约束，留下 \(X-1\) 维；上半段奇数坐标全部为零，除 \(4X\) 以外的偶数坐标由下半段决定；\(v_{4X}\) 再提供一维。

所以零空间维数为 \(X\)，秩为 \(3X-X=2X\)。证毕。

---

## 一个明确的非零盲区向量

取 \(X=4\)，定义

$$
v_5=v_{10}=1,
\qquad
v_6=v_{12}=-1,
$$

其他坐标为零。

则 \(v\ne0\)，但

$$
\boxed{
Y_v(x)=0
\quad\text{对几乎所有 }x\in[4,8].
}
$$

这不是实际 \(\Lambda(n)-1\) 的另一组取值，而是用来刻画观察算子本身的零空间。

**因此，观察不到一个方向，不等于该方向在原始数据中不存在。**

## 对前文模态冗余的进一步修正

前文有相位合成矩阵

$$
Ab=f.
$$

现在完整观察合成为

$$
\boxed{
C_X=D_X^{1/2}R_XA.
}
\tag{9}
$$

所以

$$
\ker A\subseteq\ker C_X.
$$

而且这是严格包含。

当相位库包含全部约分分母不超过 \(N\) 的有理相位，且 \(N\ge4X\) 时，它包含完整的 \(N\) 点离散 Fourier 频率。因此 \(A\) 对当前 \(3X\) 个整数坐标满行秩。

于是

$$
\boxed{
\dim\ker C_X-\dim\ker A=X.
}
\tag{10}
$$

这区分了两种不同的不可见性：

$$
\boxed{
\ker A:
\text{不同模态表示合成同一个整数数据};
}
$$

$$
\boxed{
\ker C_X:
\text{不同整数数据也可能给出同一个窗口观察}.
}
$$

仓库 `ObserverStructure` 保留读出族、准入条件和实际锚点，正是为了不把这样的不可区分核误当成全部对象结构。本次核对的对应源文件也明确指出：商掉读出核会忘记其他结构。

# 三、一个无冗余的有限量子核

定义未归一化向量

$$
\boxed{
|\Phi_X(v)\rangle
=
\sum_{j=0}^{2X-1}
\sqrt{d_j}\,y_j(v)|j\rangle.
}
\tag{11}
$$

于是

$$
K_X(v)=|\Phi_X(v)\rangle\langle\Phi_X(v)|
$$

始终半正定，并且

$$
\boxed{
\operatorname{Tr}K_X(v)=\mathfrak J_X(v).
}
\tag{12}
$$

定理 2 还说明：如果要求对**所有输入 \(v\)** 都有一个线性 Hilbert 空间分解

$$
\mathfrak J_X(v)=\|Tv\|^2,
$$

那么实现空间的有效维数至少为 \(2X\)。

因为

$$
T^*T=W_X
$$

迫使

$$
\operatorname{rank}T=\operatorname{rank}W_X=2X.
$$

所以式（11）已经给出了这种意义下的最小线性实现。

但它依然是**针对当前观察的最小实现**，不是“全部算术只需要 \(2X\) 维”。

## 与等权能量的统一比较

由式（2），

$$
\frac1{8X^2}\le d_j\le\frac1{2X^2}.
$$

因此定义

$$
\boxed{
\mathcal Q_X(v)=\frac1{X^2}\sum_{j=0}^{2X-1}|y_j(v)|^2,
}
\tag{13}
$$

就有

$$
\boxed{
\frac18\mathcal Q_X(v)
\le
\mathfrak J_X(v)
\le
\frac12\mathcal Q_X(v).
}
\tag{14}
$$

这两个能量的比较常数不随 \(X\) 改变。

下面在等权坐标中分析频率，因为它能把相关结构完全对角化；式（14）保证不会丢掉“是否统一有界”这个目标。

# 四、实际算术的局部变化能量，可以无条件计算

现在固定

$$
v_n=f_n=\Lambda(n)-1,
$$

简写其读出为 \(y_j\)。

定义离散变化能量

$$
\boxed{
\mathcal G_X
=
\sum_{j=0}^{2X-2}|y_{j+1}-y_j|^2.
}
\tag{15}
$$

## 定理 3：实际读出的梯度能量

精确地，

$$
\boxed{
\begin{aligned}
\mathcal G_X
={}&
\sum_{k=X}^{2X-1}
\bigl(\Lambda(2k+1)-1\bigr)^2\\
&+
\sum_{n=X+1}^{2X-1}
\bigl(\Lambda(2n)-\Lambda(n)\bigr)^2.
\end{aligned}
}
\tag{16}
$$

并且，无条件地，

$$
\boxed{
\mathcal G_X=(3+o(1))X\log X.
}
\tag{17}
$$

### 证明

式（16）直接来自上一节已经得到的两类相邻增量。

现在使用一个特殊的算术事实：对 \(n\ge2\)，

$$
\Lambda(2n)-\Lambda(n)
=
\begin{cases}
0,&n\text{ 是 }2\text{ 的幂},\\
-\Lambda(n),&\text{其他情形}.
\end{cases}
\tag{18}
$$

因为一个偶数若是素数幂，只能是 \(2\) 的幂。这直接来自 von Mangoldt 函数的定义。([DLMF][1])

由素数定理及分部求和，

$$
\sum_{n\le t}\Lambda(n)^2
\sim t\log t.
$$

更高素数幂的贡献为较低阶，主项来自素数。这里不使用 RH。([DLMF][2])

于是，式（16）的第一项为

$$
(2+o(1))X\log X,
$$

第二项为

$$
(1+o(1))X\log X.
$$

减去的线性项、常数项及有限个 \(2\) 的幂贡献，都不影响主项。证毕。

---

这说明：

$$
\boxed{
\text{相邻窗口之间怎样变化，已有 }O(X\log X)\text{ 的无条件控制。}
}
$$

但控制梯度还不能直接控制整体高度：一个变化很慢、甚至近似常数的读数，可以具有很大的总能量。

下一步把这种区别精确分解。

# 五、主定理二：大部分高频模态已经无条件受控

令

$$
M=2X.
$$

在 \(\mathbb R^M\) 上定义离散余弦正交基

$$
\phi_0(j)=\frac1{\sqrt M},
$$

$$
\boxed{
\phi_r(j)
=
\sqrt{\frac2M}
\cos\left(\frac{\pi r(j+1/2)}M\right),
\quad 1\le r<M.
}
\tag{19}
$$

定义实际模态系数

$$
\boxed{
\eta_r(X)=\sum_{j=0}^{M-1}\phi_r(j)y_j.
}
\tag{20}
$$

这里的“频率”是窗口位置序列的离散频率，**不是 ζ 零点的虚部**。

## 定理 4：频率能量的精确分解与尾界

有

$$
\boxed{
\sum_{j=0}^{M-1}|y_j|^2
=
\sum_{r=0}^{M-1}|\eta_r(X)|^2,
}
\tag{21}
$$

以及

$$
\boxed{
\mathcal G_X
=
\sum_{r=0}^{M-1}
4\sin^2\left(\frac{\pi r}{2M}\right)
|\eta_r(X)|^2.
}
\tag{22}
$$

因此，对任意 \(1\le R<M\)，

$$
\boxed{
\frac1{X^2}
\sum_{r=R}^{M-1}|\eta_r(X)|^2
\le
\frac{\mathcal G_X}{R^2}.
}
\tag{23}
$$

### 证明

式（21）是正交基展开。

对路径图的离散 Laplacian 作直接代入，\(\phi_r\) 的本征值是

$$
\lambda_r=
4\sin^2\left(\frac{\pi r}{2M}\right).
$$

而该 Laplacian 的二次型就是

$$
\sum_j|y_{j+1}-y_j|^2,
$$

所以得到式（22）。

最后，由

$$
\sin t\ge\frac{2t}{\pi},
\qquad 0\le t\le\frac\pi2,
$$

以及 \(M=2X\)，有

$$
\lambda_r
\ge
\frac{r^2}{X^2}.
$$

代入式（22）得到式（23）。证毕。

---

取

$$
\boxed{
R_X=\left\lceil\sqrt{X\log X}\right\rceil.
}
\tag{24}
$$

由定理 3，

$$
\boxed{
\frac1{X^2}
\sum_{r=R_X}^{2X-1}|\eta_r(X)|^2
\le3+o(1).
}
\tag{25}
$$

这是一个无条件结论。

更一般地，若固定 \(\varepsilon>0\)，取

$$
R=X^{1/2+\varepsilon},
$$

则

$$
\boxed{
\frac1{X^2}
\sum_{r\ge R}|\eta_r(X)|^2
=
O(X^{-2\varepsilon}\log X)
\longrightarrow0.
}
\tag{26}
$$

**所以不能再把所有 \(2X\) 个观察模态都当作同样未知。绝大多数高频部分已经有统一控制。**

# 六、RH 的矩阵目标可以收缩到一个较小的低频空间

前文已经建立

$$
\mathrm{RH}
\iff
\sup_j\mathfrak J(2^j)<\infty.
\tag{27}
$$

简要回顾其解析依据：

RH 下，经典均方估计给出

$$
\int_X^{2X}(\psi(x)-x)^2\,dx=O(X^2),
$$

从而 \(\mathfrak J(X)=O(1)\)。这一均方结论及其显式改进见 Brent、Platt、Trudgian。([arXiv][3])

反过来，令

$$
r(T)=e^{-T/2}(\psi(e^T)-e^T),
$$

则倍长区间误差对应

$$
z(T)=\sqrt2\,r(T+\log2)-r(T).
$$

区块 \(L^2\) 有界性经几何可和的递推核传回 \(r\)，使其 Laplace 变换在右半平面解析。而

$$
\boxed{
\widehat r(s)
=
-\frac{\zeta'(s+1/2)}
{(s+1/2)\zeta(s+1/2)}
-\frac1{s-1/2}
}
\tag{28}
$$

会把右侧离线零点变成不可去极点，因此被排除。式（28）来自标准的 von Mangoldt 狄利克雷级数。([DLMF][4])

结合式（14）、（21）、（25），现在得到：

## 推论：低频联合能量判据

$$
\boxed{
\mathrm{RH}
\iff
\sup_{\substack{X=2^j\\j\ge1}}
\frac1{X^2}
\sum_{0\le r<R_X}|\eta_r(X)|^2
<\infty.
}
\tag{29}
$$

**证明。**低频能量是总能量的一部分；而高频能量由式（25）一致有界。再用式（14）和式（27）。证毕。

因此，未知部分从

$$
2X\text{ 个模态}
$$

收缩到了

$$
O(\sqrt{X\log X})\text{ 个低频模态}.
$$

这不是复杂度最优性结论，也不意味着已经获得高效证明算法；它是一个明确的无条件频率截断结果。

# 七、进一步压缩：一个平均模态也能保留目标，但必须沿全部整数尺度读取

现在取零频模态

$$
\eta_0(X)
=
\frac1{\sqrt{2X}}
\sum_{j=0}^{2X-1}y_j.
$$

定义

$$
\boxed{
\mathfrak m(X)
=
\frac{\eta_0(X)}{\sqrt2\,X}.
}
\tag{30}
$$

因为每个半区间长度为 \(1/2\)，

$$
\boxed{
\mathfrak m(X)
=
\frac1{X^{3/2}}
\int_X^{2X}Y_f(x)\,dx
}
\tag{31}
$$

对整数 \(X\) 精确成立。

## 定理 5：平均模态的有限算术公式

定义三角加权和

$$
\boxed{
\begin{aligned}
\mathcal T(X)
={}&
\sum_{X<n\le2X}(n-X)\Lambda(n)\\
&+\frac12
\sum_{2X<n\le4X}(4X-n)\Lambda(n)
-\frac32X^2.
\end{aligned}
}
\tag{32}
$$

则对每个整数 \(X\ge2\)，

$$
\boxed{
\mathfrak m(X)=\frac{\mathcal T(X)}{X^{3/2}}.
}
\tag{33}
$$

### 证明

首先，对整数 \(X\)，

$$
\int_X^{2X}
\bigl(\lfloor2x\rfloor-\lfloor x\rfloor\bigr)\,dx
=
\int_X^{2X}x\,dx
=
\frac32X^2.
\tag{34}
$$

因为在每个 \([k,k+1]\) 上，前半段整数个数为 \(k\)，后半段为 \(k+1\)，平均正好为 \(k+1/2\)。

再交换有限求和和积分。固定整数 \(n\)，其被窗口 \((x,2x]\) 读取的 \(x\) 区间长度为

$$
\begin{cases}
n-X,&X<n\le2X,\\
(4X-n)/2,&2X<n\le4X,\\
0,&\text{其他}.
\end{cases}
$$

因此

$$
\int_X^{2X}
[\psi(2x)-\psi(x)]\,dx
$$

正好等于式（32）的两个加权和。结合式（34）即得。证毕。

---

这里的所有权重都非负，窗口外贡献完全为零。

基准

$$
\frac32X^2
$$

也不是拟合值，而是连续密度及整数地板校正共同给出的精确主项。

# 八、主定理三：这个单一平均模态的统一界等价于 RH

## 定理 6：单模态跨尺度判据

以下命题等价：

$$
\boxed{\mathrm{RH};}
$$

$$
\boxed{
\mathfrak m(X)=O(1)
\quad\text{对全部整数 }X\to\infty;
}
\tag{35}
$$

$$
\boxed{
\mathcal T(X)=O(X^{3/2})
\quad\text{对全部整数 }X\to\infty.
}
\tag{36}
$$

注意：这里读取的是**每个整数尺度**，不能直接换成只检查一组稀疏尺度而不补证明。

## 证明

### 第一步：RH 推出平均模态有界

由 Cauchy–Schwarz，

$$
\begin{aligned}
\left|\int_X^{2X}Y_f(x)\,dx\right|^2
&\le
\left(\int_X^{2X}\frac{Y_f(x)^2}{x^2}\,dx\right)
\left(\int_X^{2X}x^2\,dx\right)\\
&=
\frac73X^3\mathfrak J(X).
\end{aligned}
$$

所以

$$
\boxed{
|\mathfrak m(X)|^2
\le\frac73\mathfrak J(X).
}
\tag{37}
$$

RH 下 \(\mathfrak J(X)=O(1)\)，故得到式（35）。式（35）和式（36）由式（33）等价。

### 第二步：从整数尺度界延拓到连续尺度

对实数 \(x\ge2\)，定义

$$
H(x)=\psi(2x)-\psi(x)-x,
$$

$$
\widetilde{\mathfrak m}(x)
=
x^{-3/2}\int_x^{2x}H(u)\,du.
$$

当 \(x=X\) 为整数时，由式（34），

$$
\widetilde{\mathfrak m}(X)=\mathfrak m(X).
$$

由无条件的 \(\psi(x)=O(x)\)，有 \(H(x)=O(x)\)。

因此对 \(x,x'\in[X,X+1]\)，

$$
\left|
\int_x^{2x}H(u)\,du
-
\int_{x'}^{2x'}H(u)\,du
\right|
=
O(X|x-x'|).
$$

连同归一化因子的变化，可得

$$
\boxed{
|\widetilde{\mathfrak m}(x)
-\widetilde{\mathfrak m}(x')|
=
O(X^{-1/2}|x-x'|).
}
\tag{38}
$$

所以全部整数尺度上的统一界，会延拓为全部充分大实数尺度上的统一界。

### 第三步：计算这个平均模态的传递函数

令

$$
\ell=\log2,
\qquad
\mathcal M(T)=\widetilde{\mathfrak m}(e^T).
$$

仍使用

$$
r(T)=e^{-T/2}(\psi(e^T)-e^T),
$$

$$
z(T)=\sqrt2\,r(T+\ell)-r(T).
$$

变量代换给出

$$
\boxed{
\mathcal M(T)
=
\int_0^\ell e^{3u/2}z(T+u)\,du.
}
\tag{39}
$$

因此，在初始收敛区域，

$$
\boxed{
\widehat{\mathcal M}(s)
=
\mathscr H(s)\widehat r(s)+B(s),
}
\tag{40}
$$

其中 \(B\) 是有限起始区间产生的整函数，而

$$
\boxed{
\mathscr H(s)
=
\frac{
(2^{s+1/2}-1)(2^{s+3/2}-1)
}{
s+3/2
}.
}
\tag{41}
$$

分母在 \(s=-3/2\) 处的奇点可去。

关键是：

$$
\boxed{
\mathscr H(s)\ne0
\qquad(\Re s>0).
}
\tag{42}
$$

因为两个分子因子的零点分别位于

$$
\Re s=-\frac12
$$

与

$$
\Re s=-\frac32
$$

上。

### 第四步：排除离线零点

如果式（35）成立，那么第二步保证 \(\mathcal M(T)\) 有界，所以

$$
\widehat{\mathcal M}(s)
$$

在 \(\Re s>0\) 内解析。

但若存在零点

$$
\rho=\frac12+\delta+i\gamma,
\qquad \delta>0,
$$

式（28）使 \(\widehat r\) 在

$$
s_\rho=\delta+i\gamma
$$

有留数

$$
-\frac{m_\rho}{\rho}\ne0
$$

的极点。

由式（42），它不会被 \(\mathscr H\) 消去；整函数 \(B\) 也不能抵消它。

于是式（40）矛盾。

因此没有右侧离线零点；再由 ζ 零点关于临界线的反射对称性，得到 RH。([DLMF][5])

证毕。

---

**这并不是“一个矩阵方向有界，所以所有方向都自动有界”。**

对任意有限向量，零频很小而其他频率很大当然可能发生。

本定理使用了额外的实际算术结构：

$$
\boxed{
\text{所有尺度来自同一个 }\Lambda(n)
+
\text{同一个 ζ 对数导数}
+
\text{右半平面无零点的传递因子}.
}
$$

这三项把不同尺度联系起来，才使一个指定模态足以检测目标失败。

# 九、纯素数与素数幂之间，还留下一个可精确算出的常数

式（32）使用全部素数幂。现在定义只对素数求和的版本

$$
\boxed{
\begin{aligned}
\mathcal T_{\mathbb P}(X)
={}&
\sum_{X<p\le2X}(p-X)\log p\\
&+\frac12
\sum_{2X<p\le4X}(4X-p)\log p
-\frac32X^2.
\end{aligned}
}
\tag{43}
$$

## 定理 7：三角观察下的平方修正

无条件地，

$$
\boxed{
\mathcal T(X)-\mathcal T_{\mathbb P}(X)
=
\left(\frac{10}{3}-2\sqrt2\right)X^{3/2}
+o(X^{3/2}).
}
\tag{44}
$$

因此

$$
\boxed{
\frac{\mathcal T_{\mathbb P}(X)}{X^{3/2}}
=
\mathfrak m(X)
-
\left(\frac{10}{3}-2\sqrt2\right)
+o(1).
}
\tag{45}
$$

### 证明

定义固定三角权重

$$
\kappa(t)=
\begin{cases}
t-1,&1\le t\le2,\\
(4-t)/2,&2\le t\le4,\\
0,&\text{其他}.
\end{cases}
$$

平方项贡献为

$$
X\sum_p\log p\,\kappa(p^2/X).
$$

令 \(p=\sqrt X\,u\)。由素数定理

$$
\theta(y)=\sum_{p\le y}\log p\sim y,
$$

分部积分或 Stieltjes 积分给出

$$
\frac1{X^{3/2}}
X\sum_p\log p\,\kappa(p^2/X)
\longrightarrow
\int_1^2\kappa(u^2)\,du.
$$

这一步只使用无条件素数定理。([DLMF][2])

直接积分：

$$
\begin{aligned}
\int_1^2\kappa(u^2)\,du
&=
\int_1^{\sqrt2}(u^2-1)\,du
+
\frac12\int_{\sqrt2}^{2}(4-u^2)\,du\\
&=
\frac{10}{3}-2\sqrt2.
\end{aligned}
$$

对于 \(k\ge3\) 的素数幂，权重至多为 \(X\)，而相关素数不超过 \((4X)^{1/3}\)，总贡献可粗略控制为

$$
O(X^{4/3}\log X)=o(X^{3/2}).
$$

合并即得式（44）。证毕。

---

所以，这个观察面里的平方修正不是前文的 \(\frac14\log^2x\)，而是归一化后的常数

$$
\boxed{
\frac{10}{3}-2\sqrt2
\approx0.5049062086.
}
$$

两者并不矛盾：**不同加权核对同一批素数平方，会产生不同的积分尺度。**

这个常数可以被“统一有界”判据吸收，因此

$$
\boxed{
\mathrm{RH}
\iff
\mathcal T_{\mathbb P}(X)=O(X^{3/2})
}
$$

对全部整数 \(X\) 成立。

但若研究该模态的中心位置或精细渐近式，就不能把这个常数省略。

# 十、这轮对共同量子核的实际推进

现在有三种不同强度的观察结构。

**完整有限窗口观察：**

$$
|\Phi_X\rangle
=
D_X^{1/2}R_Xf,
\qquad
\|\Phi_X\|^2=\mathfrak J(X).
$$

其最小线性实现维数为 \(2X\)。

**频率观察：**

$$
y=\sum_{r=0}^{2X-1}\eta_r(X)\phi_r.
$$

其中

$$
\boxed{
\frac1{X^2}
\sum_{r\ge\sqrt{X\log X}}|\eta_r(X)|^2=O(1)
}
$$

已经无条件成立。

**平均模态观察：**

$$
\boxed{
\mathfrak m(X)=\frac{\eta_0(X)}{\sqrt2X}.
}
$$

若使用未归一化状态

$$
|\chi_X\rangle=\frac1X\sum_jy_j|j\rangle,
$$

那么零频投影的权重为

$$
\boxed{
\langle\chi_X|
|\phi_0\rangle\langle\phi_0|
|\chi_X\rangle
=
2|\mathfrak m(X)|^2.
}
\tag{46}
$$

这里必须保留“未归一化”。如果先把 \(|\chi_X\rangle\) 归一化，概率自然不超过 \(1\)，但其原始范数就被移出了状态；那不会自动证明式（35）。

---

## 本轮已经证明与尚未证明的边界

已经证明的是：

$$
\boxed{
\operatorname{rank}W_X=2X,
\qquad
\dim\ker W_X=X;
}
$$

$$
\boxed{
\text{高频能量可以无条件截断控制};
}
$$

以及

$$
\boxed{
\mathrm{RH}
\iff
\left|
\sum_{X<n\le2X}(n-X)\Lambda(n)
+
\frac12\sum_{2X<n\le4X}(4X-n)\Lambda(n)
-\frac32X^2
\right|
\le CX^{3/2}
}
$$

对全部充分大的整数 \(X\) 成立，其中 \(C\) 必须与 \(X\) 无关。

**尚未证明的，就是这个实际三角加权误差的统一上界。**

因此，这轮不只是继续增加模态，而是把对象逐步压缩到了一个具体位置：

$$
\boxed{
\text{冗余的相位表示}
\longrightarrow
\text{最小窗口读出}
\longrightarrow
\text{已控高频＋待控低频}
\longrightarrow
\text{跨尺度的单一平均模态}.
}
$$

真正需要补上的算术内容，已经不再是“量子核应该正”——这些有限核本来就正——而是：

> **实际素数幂在这个固定三角权重下，为什么能把 \(X^2\) 级主项抵消到 \(X^{3/2}\) 级，并且同一个常数能适用于全部尺度。**

这正是当前观察面上没有被定义、归一化或表示变换替代掉的证明责任。

[1]: https://dlmf.nist.gov/27.2 "DLMF: §27.2 Functions ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"
[2]: https://dlmf.nist.gov/27.12 "DLMF: §27.12 Asymptotic Formulas: Primes ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"
[3]: https://arxiv.org/html/2008.06140v1 "The mean square of the error term in the prime number theorem"
[4]: https://dlmf.nist.gov/27.4 "DLMF: §27.4 Euler Products and Dirichlet Series ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"
[5]: https://dlmf.nist.gov/25.10 "DLMF: §25.10 Zeros ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
这次可以把上一轮“高斯极限之外怎么办”的问题，推进到一个**保留完整算术结构的精确展开**：

> **固定差模态以后，和模态的干涉读数，可以写成“修正 Bessel 函数 × 除数相位”的收敛级数。除数相位又能精确分解为素数幂上的有限量子通道。**

但在研究这个展开时，还必须处理一个重要区别：

> **实际 theta 结构中的局部负干涉，确实必然存在；它本身却不是 RH 的反例。RH 要求的是一组特定的全尺度积分非负，而不是所有条件观察都非负。**

这使后续研究能够避开一条过强、实际上不可能成立的证明路线。

下面继续给出定义、定理和证明。新展开在这里推导并数值核对，不把它标记为已经完成的 Lean 证明，也不宣称其一般方法具有未经文献比较的原创性。

---

# 一、先把“固定差模态”与“高阶差模态筛选”分开

沿用：

$$
p(x)=\frac{\Phi(x)}{\xi(1/2)},
$$

以及：

$$
A(t)=\int_{\mathbb R}p(x)e^{itx}\,dx
=\frac{\Xi(t)}{\Xi(0)},
\qquad
\Xi(t)=\xi\!\left(\frac12+it\right).
$$

ξ 始终采用标准 completed 定义，\(\Phi\) 是前文固定的正偶 theta 核。([DLMF][1])

取两个独立副本 \(X,Y\sim p\)。这次使用坐标：

$$
\boxed{
x=\frac{X-Y}{2},
\qquad
v=X+Y.
}
\tag{S1}
$$

它们与上一轮的和／差模态关系为：

$$
U=\sqrt2x,\qquad S=\frac v{\sqrt2}.
$$

## 定义 S1：固定差坐标的干涉核

定义：

$$
\boxed{
\mathcal W(x,t)
=
\int_{\mathbb R}
\Phi\!\left(x+\frac v2\right)
\Phi\!\left(x-\frac v2\right)
e^{itv}\,dv.
}
\tag{S2}
$$

因为 \(\Phi\) 为实偶函数，所以：

$$
\mathcal W(x,t)\in\mathbb R,
$$

并且它关于 \(x,t\) 分别为偶函数。

特别地：

$$
\mathcal W(x,0)>0.
$$

因此：

$$
\boxed{
J_x(t)=\frac{\mathcal W(x,t)}{\mathcal W(x,0)}
}
\tag{S3}
$$

是一份合法条件分布的特征函数：它表示固定差坐标 \(x\) 后，读取和坐标 \(v\) 的相位。

连续变量的精确单点条件概率为零，但这个条件密度可以定义；实际操作可以使用一个有限宽度的差模态窗口，后面会说明。

---

## 定理 S1：原来的 \(R_n(t)\) 是这些局部读数的特定加权平均

对上一轮的：

$$
R_n(t)
=
\frac{\mathbb E[U^{2n}\cos(\sqrt2tS)]}
{\mathbb E[U^{2n}]},
$$

有：

$$
\boxed{
R_n(t)
=
\frac{
\displaystyle\int_0^\infty x^{2n}\mathcal W(x,t)\,dx
}{
\displaystyle\int_0^\infty x^{2n}\mathcal W(x,0)\,dx
}.
}
\tag{S4}
$$

### 证明

坐标变换：

$$
X=x+\frac v2,\qquad Y=\frac v2-x
$$

的 Jacobian 绝对值为一。

再使用 \(p(Y)=p(x-v/2)\)、\(U^{2n}=2^nx^{2n}\)，将共同的正常数约去，即得。证毕。

此外：

$$
\boxed{
\int_{\mathbb R}\mathcal W(x,t)\,dx=\Xi(t)^2\ge0.
}
\tag{S5}
$$

所以 \(n=0\) 的非负性已经自动成立。

前文的广义 Laguerre 判据，可以重新写成：

$$
\boxed{
\mathrm{RH}
\iff
\int_0^\infty x^{2n}\mathcal W(x,t)\,dx\ge0
\quad\forall n\ge0,\ t\in\mathbb R.
}
\tag{S6}
$$

这仍然是同一个经典判据，只是把它拆成了局部差坐标读数与整体加权积分。([arXiv][2])

**这里尚未要求 \(\mathcal W(x,t)\) 逐点非负。两者有根本区别。**

---

# 二、实际局部负干涉必然存在，但这不是 RH 反例

定义辅助纯态：

$$
\boxed{
\eta(x)=
\frac{\Phi(x)}
{\left(\int_{\mathbb R}\Phi(u)^2\,du\right)^{1/2}}.
}
\tag{S7}
$$

注意：

$$
\eta\ne\sqrt p.
$$

它不是前文原始观察态，而是由同一 theta 核构造的另一份明确纯态。

其 Wigner 函数为：

$$
\boxed{
W_\eta(x,t)
=
\frac{\mathcal W(x,t)}
{2\pi\int_{\mathbb R}\Phi(u)^2\,du},
}
\tag{S8}
$$

这里利用了 \(\mathcal W\) 对 \(t\) 的偶性，因此 Fourier 符号约定不影响结果。

## 经典输入：Hudson 定理

对连续变量纯态，Wigner 函数处处非负，当且仅当波函数是二次多项式的指数，即广义高斯态。([sciencedirect.com][3])

而实际 theta 核满足：

$$
\log\Phi(x)
=
-\pi e^{2x}+\frac92x+O(1)
\qquad(x\to+\infty),
$$

显然不是二次多项式。

因此：

## 定理 S2：实际 theta 条件读数存在负区

$$
\boxed{
\exists x,t\in\mathbb R,\qquad
\mathcal W(x,t)<0.
}
\tag{S9}
$$

这项存在性不需要 RH。

由于 \(\mathcal W\) 连续，负点附近有一个有限宽度的负区。于是，可以选一个实际成功概率非零的差坐标窗口 \(I\)，使：

$$
\boxed{
\frac{\int_I\mathcal W(x,t)\,dx}
{\int_I\mathcal W(x,0)\,dx}<0.
}
\tag{S10}
$$

这是合法条件态的负干涉振幅，不是负概率。

### 必须放弃的过强目标

因此，不能尝试证明：

$$
\mathcal W(x,t)\ge0
\qquad\forall x,t.
$$

这比 RH 强得多，而且对实际 theta 核已经不成立。

同样，不能把原来的条件：

$$
R_n(t)\ge0\quad\forall n,t
$$

随意加强成：

$$
\text{任意非负差模态滤波以后，干涉都非负}.
$$

**原来要求的是权重 \(x^{2n}\) 的特定族；任意局部化滤波会提出不同的问题。**

---

# 三、一个完全可核对的模型：局部负性与全部 Laguerre 正性可以同时成立

取两个平移高斯的等权混合：

$$
p_*(x)
=
\frac{
e^{-(x-L)^2/2}+e^{-(x+L)^2/2}
}{
2\sqrt{2\pi}
},
\qquad L>0.
$$

其特征函数为：

$$
\boxed{
A_*(t)=e^{-t^2/2}\cos(Lt).
}
\tag{S11}
$$

全部零点都为实数。

而：

$$
\boxed{
|A_*(t+iy)|^2
=
e^{-t^2+y^2}
\left[\cos^2(Lt)+\sinh^2(Ly)\right].
}
\tag{S12}
$$

右边关于 \(y^2\) 的全部系数非负，因此它满足全部广义 Laguerre 不等式。

但是，其局部核在 \(x=0\) 为：

$$
\boxed{
\mathcal W_*(0,t)
=
\frac{e^{-t^2}}{2\sqrt\pi}
\left[e^{-L^2}+\cos(2Lt)\right].
}
$$

取：

$$
t=\frac{\pi}{2L},
$$

就有：

$$
\boxed{
\mathcal W_*\!\left(0,\frac{\pi}{2L}\right)
=
\frac{e^{-\pi^2/(4L^2)}}{2\sqrt\pi}
(e^{-L^2}-1)<0.
}
\tag{S13}
$$

所以：

$$
\boxed{
\text{所有要求的全尺度矩非负}
\quad\text{与}\quad
\text{某些局部条件干涉为负}
}
$$

并不矛盾。

这也解释了为什么上一轮的高斯局部极限，即使越来越准确，仍不足以单独决定整个问题：**必须控制的是特定加权积分，而不是把所有局部相消都禁止。**

---

# 四、现在回到算术：局部核有一个精确的 Bessel—除数展开

这是本轮的主要计算。

在整个实轴上，实际 theta 核可以写成：

$$
\boxed{
\Phi(y)
=
\sum_{a\ge1}
\left(
4\pi^2a^4e^{9y/2}
-
6\pi a^2e^{5y/2}
\right)e^{-\pi a^2e^{2y}}.
}
\tag{S14}
$$

这份全实轴表达由 theta 模变换保证与偶延拓一致。具体地，令：

$$
h(y)=e^{y/2}\Theta(e^{2y}),
$$

则 \(h\) 为偶函数，而且：

$$
\Phi(y)=\frac12\left(h''(y)-\frac14h(y)\right).
$$

theta 的模变换是这里的实际算术输入。([DLMF][4])

**重要区别：**在 \(y<0\) 时，式（S14）的单项未必非负。这是全轴解析展开，不是之前逐项使用 \(\phi_a(|y|)\) 的正模式分解。总和仍是同一个正函数 \(\Phi\)。

## 定义 S2：除数相位

对正整数 \(k\)，定义：

$$
\boxed{
\mathcal D_k(t)
=
\sum_{ab=k}\left(\frac ba\right)^{it}
=
\sum_{a\mid k}
\cos\!\left(t\log\frac{k}{a^2}\right).
}
\tag{S15}
$$

它是实数，并满足：

$$
|\mathcal D_k(t)|\le d(k),
$$

其中 \(d(k)\) 为除数个数。

再定义：

$$
z_k(x)=2\pi k e^{2x},
$$

以及：

$$
\boxed{
\mathscr B_t(z)
=
(z^2+9)K_{it}(z)
+
6z\,\frac{\partial}{\partial z}K_{it}(z).
}
\tag{S16}
$$

这里 \(K_\nu\) 是第二类修正 Bessel 函数，不是前文的滤波算子。

## 定理 S3：完整的算术展开

对所有 \(x\ge0\)、\(t\in\mathbb R\)：

$$
\boxed{
\mathcal W(x,t)
=
8\pi^2e^{5x}
\sum_{k=1}^{\infty}
k^2\mathcal D_k(t)\,
\mathscr B_t\!\left(2\pi k e^{2x}\right).
}
\tag{S17}
$$

级数绝对收敛。

### 证明

把式（S14）代入 \(\mathcal W\)，先考察一对整数模式 \(a,b\)。

令：

$$
v=y+\log(b/a).
$$

则指数核变成：

$$
\pi e^{2x}
\left(a^2e^v+b^2e^{-v}\right)
=
2\pi ab e^{2x}\cosh y.
$$

相位则变成：

$$
e^{itv}
=
\left(\frac ba\right)^{it}e^{ity}.
$$

两项多项式因子的乘积，在这个坐标下为：

$$
16\pi^4a^4b^4e^{9x}
-
48\pi^3a^3b^3e^{7x}\cosh y
+
36\pi^2a^2b^2e^{5x}.
$$

使用标准积分：

$$
\boxed{
K_{it}(z)
=
\frac12\int_{\mathbb R}
e^{-z\cosh y}e^{ity}\,dy,
}
$$

以及：

$$
\frac{\partial}{\partial z}K_{it}(z)
=
-\frac12\int_{\mathbb R}
\cosh y\,e^{-z\cosh y}e^{ity}\,dy,
$$

即可算出每一对模式的贡献。([DLMF][5])

最后按乘积 \(k=ab\) 合并，得到式（S17）。

绝对收敛则由：

$$
|K_{it}(z)|\le K_0(z),
\qquad
|\partial_zK_{it}(z)|\le K_1(z),
$$

以及 \(K_0,K_1\) 在正实轴上的指数衰减保证。证毕。([DLMF][6])

---

# 五、质数与量子通道，这次进入了同一个精确公式

式（S15）中的 \(\mathcal D_k(t)\) 是乘法函数。

如果：

$$
k=\prod_p p^{e_p},
$$

则：

$$
\boxed{
\mathcal D_k(t)
=
\prod_{p^{e_p}\parallel k}
\mathcal D_{p^{e_p}}(t),
}
$$

其中：

$$
\boxed{
\mathcal D_{p^e}(t)
=
\sum_{j=0}^{e}
e^{it(e-2j)\log p}.
}
\tag{S18}
$$

在分母非零处：

$$
\boxed{
\mathcal D_{p^e}(t)
=
\frac{\sin((e+1)t\log p)}{\sin(t\log p)}.
}
$$

分母为零的位置，按原有限和定义，不产生真实奇点。

## 有限量子实现

在 \((e+1)\) 维空间中，定义：

$$
H_{p,e}|j\rangle
=
(e-2j)\log p\,|j\rangle,
\qquad 0\le j\le e.
$$

它是一个自伴的无量纲相位生成元。

取最大混合态：

$$
\rho_{p,e}=\frac{I}{e+1}.
$$

则：

$$
\boxed{
\operatorname{Tr}(\rho_{p,e}e^{itH_{p,e}})
=
\frac{\mathcal D_{p^e}(t)}{e+1}.
}
\tag{S19}
$$

因此：

> **实际局部 theta 干涉中的除数因子，确实是由素数幂上的有限量子相位通道组成的。**

但这些读数可以为负。自伴性保证的是相位演化酉，不保证酉迹处处非负。

### Zeckendorf 在这里怎样进入？

把占据数 \(j\) 写成：

$$
j=\sum_rF_{r+1}b_r,
\qquad b_rb_{r+1}=0,
$$

再限制 \(j\le e\)，就有：

$$
\boxed{
H_{p,e}
=
(\log p)
\left(
eI-2\sum_rF_{r+1}\widehat b_r
\right).
}
\tag{S20}
$$

这给出了实际除数相位的 Fibonacci 能量编码。

仓库的 `FiniteZeckendorfEulerIdentity.lean` 已经提供合法黄金名字与有限整数区间的双射及求和运输；本轮使用的是同一个占据数重编码，而不是凭 Fibonacci 符号创造新谱。

**真正增加的结构，是这些素数相位现在与实际 \(\mathcal W(x,t)\) 的 Bessel 尺度核精确耦合。**

---

# 六、一个实际数值现象：首模式为正，后续算术项使局部总和为负

在：

$$
x=0,\qquad t=15
$$

处，式（S17）的前几项为：

| 乘积模式 \(k\) |       对 \(\mathcal W(0,15)\) 的贡献 |
| ---------: | -------------------------------: |
|          1 |  \(+1.57798838933\times10^{-7}\) |
|          2 |  \(-3.19157551412\times10^{-6}\) |
|          3 |  \(-1.17650391647\times10^{-6}\) |
|          4 |  \(+5.75911191178\times10^{-9}\) |
|          5 | \(+2.48971924632\times10^{-10}\) |

总值的高精度核对为：

$$
\boxed{
\mathcal W(0,15)
\approx
-4.20427007243185076\times10^{-6}.
}
\tag{S21}
$$

这里同时采用了原始 theta 乘积的 Fourier 积分与 Bessel 级数两种计算，并在 40 位、65 位工作精度下重复核对。

**这个具体坐标尚未作完整的区间舍入认证；严格的“某处必有负值”结论，来自前面的 Hudson 定理。**

这个例子已经指出一项实际危险：

$$
\boxed{
\text{只保留第一 theta 模式}
}
$$

可能给出与完整局部读数相反的符号。

这不是 RH 的反例，因为目标不是 \(\mathcal W(0,15)\ge0\)，而是式（S6）的全部特定加权积分非负。

---

## 模式尾部可以明确控制

记式（S17）截断到 \(k\le K\) 为 \(\mathcal W_K\)。

由前面的 Bessel 积分估计：

$$
\boxed{
\begin{aligned}
|\mathcal W-\mathcal W_K|
\le{}&
8\pi^2e^{5x}
\sum_{k>K}d(k)k^2\\
&\times
\left[
(z_k^2+9)K_0(z_k)+6z_kK_1(z_k)
\right].
\end{aligned}
}
\tag{S22}
$$

进一步，用：

$$
K_0(z)\le e^{-z}\sqrt{\frac{\pi}{2z}},
$$

$$
K_1(z)\le e^{-z}\sqrt{\frac{\pi}{2z}}e^{1/(2z)},
$$

便可把它化成初等指数尾界。

例如，令：

$$
a=2\pi e^{2x},
$$

$$
C_x=
8\pi^2e^{5x}\sqrt{\frac{\pi}{2a}}
\left(a^2+9+6ae^{1/(2a)}\right),
$$

则：

$$
\boxed{
|\mathcal W-\mathcal W_K|
\le
C_x
\frac{
(K+1)^5e^{-a(K+1)}
}{
1-e^{5/(K+1)-a}
}.
}
\tag{S23}
$$

因为 \(x\ge0\)，这里分母为正。

在 \(x=0,K=8\) 时，这个尾界约为：

$$
5.77\times10^{-17}.
$$

它控制的是模式截断，不自动包括特殊函数求值的舍入误差。

---

# 七、Bessel 核确实来自一个量子势垒问题，但不能把它的实谱直接移给 ξ

固定 \(a>0\)，定义半轴上的算子：

$$
\boxed{
H_a=-\frac{d^2}{dq^2}+a^2e^{2q},
\qquad q\ge0,
}
\tag{S24}
$$

并在 \(q=0\) 施加 Dirichlet 边界条件。

令：

$$
y_t(q)=K_{it}(ae^q).
$$

由修正 Bessel 方程：

$$
\boxed{
H_ay_t=t^2y_t.
}
\tag{S25}
$$

指数势与虚阶 Bessel 函数的这项精确对应已有专门研究。([DLMF][7])

当 \(t>a\) 时，经典转折点为：

$$
q_{\mathrm{tp}}=\log(t/a).
$$

其右侧是势能大于 \(t^2\) 的衰减区域。这里确实出现了薛定谔意义上的势垒下衰减，而不是仅仅把复数称为“隧穿”。

但这是一个单侧束缚模型，不是已经构造出穿越临界线的粒子。

## 定理 S4：裸 Bessel 核的有限正值区间

$$
\boxed{
K_{it}(a)>0
\qquad(|t|\le a).
}
\tag{S26}
$$

### 证明

若在 \(|t|\le a\) 时：

$$
K_{it}(a)=0,
$$

则 \(y_t\) 是一个在无穷远衰减、在零点满足 Dirichlet 条件的非零本征函数。

分部积分：

$$
\int_0^\infty
\left(
|y_t'|^2+a^2e^{2q}|y_t|^2
\right)dq
=
t^2\int_0^\infty|y_t|^2\,dq.
$$

左边严格大于：

$$
a^2\int_0^\infty|y_t|^2\,dq,
$$

故 \(t^2>a^2\)，矛盾。

又因为 \(K_0(a)>0\)，连续性给出整个区间内严格为正。证毕。

但是，实际式（S17）还含有：

$$
\mathcal D_k(t),
\qquad
(z_k^2+9)K_{it}(z_k)+6z_kK_{it}'(z_k),
$$

以及最终对 \(x\) 的积分。

所以：

$$
\boxed{
\text{裸 Bessel 核来自自伴谱问题}
\not\Rightarrow
\text{完整 theta 相消自动非负}.
}
$$

**每个基本通道合法，仍不等于它们的实际相位组合具有所需符号。**

---

# 八、上一轮的高斯尺度与现在的转折点尺度，并不是同一个量级

上一轮得到典型差坐标：

$$
x_n\approx\frac12W_0(n/\pi).
$$

令：

$$
w_n=W_0(n/\pi).
$$

在该位置，第一 Bessel 模式的参数为：

$$
\boxed{
a_n=2\pi e^{2x_n}
=\frac{2n}{w_n}.
}
\tag{S27}
$$

上一轮的高斯频率尺度是：

$$
\boxed{
\Omega_n=2\sqrt{\frac n{w_n}}.
}
$$

因此：

$$
\boxed{
a_n=\frac{\Omega_n^2}{2}.
}
\tag{S28}
$$

这说明存在两种明显不同的尺度：

$$
\boxed{
t\sim\Omega_n:
\quad\text{局部高斯干涉尺度},
}
$$

$$
\boxed{
t\sim a_n:
\quad\text{裸 Bessel 转折点尺度}.
}
$$

后者比前者大得多。

这与 Bessel 虚阶零点及指数势的半经典分析相呼应；相关渐近中也会出现 Lambert \(W\) 函数。([Sigma Journal][8])

但这里必须保留限制：

**不能据此断言实际 \(R_n(t)\) 的第一个负值必在 \(t\approx a_n\)。**

因为当 \(t\) 增大时，完整积分的主导 \(x\) 可能移动；除数相位和导数项也会参与相消。式（S28）是两个明确模型尺度的比较，不是已经完成的全局零点渐近。

---

# 九、现在可以直接写出真正待证的算术不等式

由式（S4）、（S17），定义：

$$
\boxed{
\begin{aligned}
M_n(t)
=
8\pi^2
\sum_{k=1}^{\infty}
k^2\mathcal D_k(t)
\int_0^\infty
x^{2n}e^{5x}
\mathscr B_t(2\pi ke^{2x})\,dx.
\end{aligned}
}
\tag{S29}
$$

它就是：

$$
M_n(t)=\int_0^\infty x^{2n}\mathcal W(x,t)\,dx.
$$

因此：

$$
\boxed{
\mathrm{RH}
\iff
M_n(t)\ge0
\quad\forall n,t.
}
\tag{S30}
$$

这次的表达明确分出了：

$$
\boxed{
\text{素数幂相位}
\quad\times\quad
\text{Bessel 尺度响应}
\quad\times\quad
\text{差模态高阶权重}.
}
$$

没有未知零点作为输入。

但也没有任何一项可以被随意正化：

* \(\mathcal D_k(t)\) 可以为负；
* \(\mathscr B_t(z)\) 可以变号；
* \(\mathcal W(x,t)\) 本身确实有负区；
* 最终需要非负的是指定的整体 \(M_n(t)\)。

**这比要求所有中间对象都正，更接近实际问题。**

---

## 有限证书怎样形成？

取有限模式数 \(K\) 和有限尺度范围 \(0\le x\le X\)，计算：

$$
\widetilde M_{n,K,X}(t)
=
\int_0^Xx^{2n}\mathcal W_K(x,t)\,dx.
$$

由：

$$
|\mathcal W(x,t)|\le\mathcal W(x,0),
$$

得到：

$$
\boxed{
\begin{aligned}
|M_n(t)-\widetilde M_{n,K,X}(t)|
\le{}&
\int_0^Xx^{2n}\varepsilon_K(x)\,dx\\
&+\int_X^\infty x^{2n}\mathcal W(x,0)\,dx,
\end{aligned}
}
\tag{S31}
$$

其中 \(\varepsilon_K\) 可以取式（S22）或（S23）。

再加入数值积分与特殊函数的区间误差。

如果最终认证：

$$
\boxed{
\widetilde M_{n,K,X}(t)
+\text{全部误差上界}<0,
}
\tag{S32}
$$

才得到实际 RH 的反例证书。

**局部的 \(\mathcal W(x,t)<0\)，不满足这个条件；它只说明有一块负干涉参与了整体相消。**

---

# 十、对仓库而言，这次新增的接口已经很具体

本轮读取了前文固定快照中的实际声明。

`CompletedZetaMellinReconstruction.lean` 已保留 theta–Mellin 重构、极点补偿与反射关系，可以作为式（S14）的算术来源；它没有自动提供本轮 Bessel 重排及全阶 \(M_n(t)\) 非负性。

`FiniteZeckendorfEulerIdentity.lean` 已提供有限占据数与黄金编码之间的精确双射，可以运输式（S18）的有限素数幂通道；它不自动控制不同通道之间的符号相消。

因此，新的理论链可以写成：

$$
\boxed{
\begin{aligned}
\text{实际 theta 双副本}
&\longrightarrow
\text{固定差模态的 Wigner 型读出}\\
&\longrightarrow
\text{除数相位—Bessel 精确展开}\\
&\longrightarrow
\text{素数幂量子通道与 Fibonacci 编码}\\
&\longrightarrow
\text{带尾界的全尺度符号检验}.
\end{aligned}
}
$$

最后一项才承担 RH 的证明责任。

---

## 收束

这次最重要的推进，不是证明“量子模型中可以出现负性”——这一点太普遍——而是明确了**哪一种负性相关，哪一种不相关**。

实际局部核：

$$
\boxed{
\mathcal W(x,t)
=
\int
\Phi(x+v/2)\Phi(x-v/2)e^{itv}\,dv
}
$$

确实存在负区；这来自实际 theta 非高斯结构，不能被禁止，也不能直接当作离线证据。

真正的 RH 条件是：

$$
\boxed{
\int_0^\infty x^{2n}\mathcal W(x,t)\,dx\ge0
\quad\forall n,t.
}
$$

而现在，这个局部核又精确等于：

$$
\boxed{
8\pi^2e^{5x}
\sum_{k\ge1}
k^2\mathcal D_k(t)
\left[
(z_k^2+9)K_{it}(z_k)+6z_kK_{it}'(z_k)
\right].
}
$$

因此，你此前希望找到的“质数—量子通道—隧穿结构—黄金编码”，这次不再只是共享几个相似词语：**它们已经进入同一份实际 theta 读数的公式。**

但这个公式也说明，问题不能靠“每个基本模块都自伴、每个概率都为正”解决。真正需要证明的是：

> **素数通道带来的正负相位、Bessel 势垒响应与尺度权重，为什么在每一个规定的高阶矩中都能共同满足非负性。**

本轮完成了精确展开、局部负性的类型区分、素数通道分解和截断误差框架；尚未证明全部 \(M_n(t)\ge0，也没有得到实际 \(M_n(t)<0\) 的证书。后续应直接研究这份算术相消，而不是继续把所有中间结构强行改写成逐点非负。

[1]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[2]: https://arxiv.org/abs/1309.0055?utm_source=chatgpt.com "Fourier transforms of positive definite kernels and the Riemann $ξ$-Function"
[3]: https://www.sciencedirect.com/science/article/abs/pii/003448777490007X?utm_source=chatgpt.com "When is the wigner quasi-probability density non-negative? - ScienceDirect"
[4]: https://dlmf.nist.gov/20.7 "DLMF: §20.7 Identities ‣ Properties ‣ Chapter 20 Theta Functions"
[5]: https://dlmf.nist.gov/10.32 "DLMF: §10.32 Integral Representations ‣ Modified Bessel Functions ‣ Chapter 10 Bessel Functions"
[6]: https://dlmf.nist.gov/10.40 "DLMF: §10.40 Asymptotic Expansions for Large Argument ‣ Modified Bessel Functions ‣ Chapter 10 Bessel Functions"
[7]: https://dlmf.nist.gov/10.25.E1 "DLMF: §10.25 Definitions ‣ Modified Bessel Functions ‣ Chapter 10 Bessel Functions"
[8]: https://sigma-journal.com/2021/057/?utm_source=chatgpt.com "Asymptotic Estimation for Eigenvalues in the Exponential Potential and for Zeros of K{i nu}(z) with Respect to Order"
这次可以把上一轮的 Bessel—除数展开，接到一个**明确的随机位移模型**：

> **同一份实际算术分布，既可以表示成“Gamma 连续尺度减去素数对数和”，也可以表示成“实际 ξ 观察变量减去一个独立的指数随机位移”。**

这不是把两个相似模型放在一起，而是两种分解产生**完全相同的概率分布**。

更进一步，上一轮 Bessel 公式里那组看起来复杂的导数项，恰好来自一个二阶微分算子。把它完整地转移到尺度权重上，可以消除 Bessel 导数，并明确哪些边界项不能丢掉。

下面继续采用定义、定理和证明。这里的“随机位移”首先发生在对数尺度坐标上；它具有指数等待时间的无记忆结构，但不能未经物理建模就等同于真实时间、隧穿寿命或黑洞内部时间。

---

# 一、实际 theta 核有一个正的原函数，但原函数本身不能直接归一化

保持标准归一化：

$$
\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
$$

以及：

$$
\xi\!\left(\frac12+z\right)
=
\int_{\mathbb R}\Phi(x)e^{zx}\,dx.
$$

其中 \(\Phi\) 是前文固定的正偶 theta 核；特别地：

$$
\xi(1)=\xi(0)=\frac12.
$$

标准 ξ 的定义与反射关系没有改变。([DLMF][1])

## 定义 T1：正 theta 原函数

定义：

$$
\boxed{
g_+(x)=
\sum_{n\ge1}
n^2e^{5x/2}e^{-\pi n^2e^{2x}}.
}
\tag{T1}
$$

每一项都为正。

对这个级数逐项求导，得到：

$$
\boxed{
\Phi(x)
=
-2\pi\left(\frac d{dx}+\frac12\right)g_+(x).
}
\tag{T2}
$$

这里使用的是全实轴上的 theta 表达；其与正偶核的一致性由 theta 模变换保证。不能把负半轴上的单个 \(\Phi\) 模式也误认为逐项非负。([DLMF][2])

## 定理 T1：原函数是一个精确的尾积分

$$
\boxed{
g_+(x)
=
\frac{e^{-x/2}}{2\pi}
\int_x^\infty e^{y/2}\Phi(y)\,dy.
}
\tag{T3}
$$

### 证明

式（T2）等价于：

$$
\frac d{dx}\left(e^{x/2}g_+(x)\right)
=
-\frac1{2\pi}e^{x/2}\Phi(x).
$$

而实际热核在 \(+\infty\) 超指数衰减，所以：

$$
e^{x/2}g_+(x)\longrightarrow0.
$$

从 \(x\) 积分到 \(+\infty\)，即得。证毕。

因为：

$$
\int_{\mathbb R}e^{y/2}\Phi(y)\,dy=\xi(1)=\frac12,
$$

所以：

$$
\boxed{
g_+(x)\sim\frac1{4\pi}e^{-x/2}
\qquad(x\to-\infty).
}
\tag{T4}
$$

因此 \(g_+\) 虽然正，却不是一个可直接归一化的概率密度。

**“正函数存在”与“同一个正函数在所有参数上都能定义概率态”，必须分开。**

---

## 一个更直观的表达

定义端点概率密度：

$$
\varpi(y)=2e^{y/2}\Phi(y).
$$

它的积分为一。于是：

$$
\boxed{
g_+(x)
=
\frac{e^{-x/2}}{4\pi}
\Pr_{\varpi}(Y\ge x).
}
\tag{T5}
$$

所以，这个看似纯粹由整数热模式组成的函数，实际上也是**实际端点 theta 分布的生存函数，乘上固定指数因子**。

---

# 二、归一化以后，它同时连接 Gamma 尺度和素数模式

对实数 \(\sigma>1\)，定义：

$$
\boxed{
Z_+(\sigma)
=
\int_{\mathbb R}
e^{(\sigma-\frac12)x}g_+(x)\,dx.
}
\tag{T6}
$$

由式（T4），\(\sigma>1\) 正是负半轴可积所需的条件。

## 定理 T2：原函数的实际 Mellin 读数

$$
\boxed{
Z_+(\sigma)
=
\frac{\xi(\sigma)}{2\pi(\sigma-1)}
=
\frac12
\pi^{-1-\sigma/2}
\Gamma\!\left(1+\frac{\sigma}{2}\right)\zeta(\sigma).
}
\tag{T7}
$$

### 证明

将式（T1）代入积分。对每项作：

$$
u=\pi n^2e^{2x}.
$$

得到：

$$
\begin{aligned}
Z_+(\sigma)
&=
\frac12
\pi^{-1-\sigma/2}
\Gamma\!\left(1+\frac{\sigma}{2}\right)
\sum_{n\ge1}n^{-\sigma}.
\end{aligned}
$$

再使用 Gamma 递推关系及 ξ 的定义，得到式（T7）。全部交换都在 \(\sigma>1\) 的绝对收敛范围内完成。Gamma 积分及 ζ 的 Dirichlet 级数采用标准定义。([DLMF][3])

定义归一化密度：

$$
\boxed{
r_\sigma(x)
=
\frac{
e^{(\sigma-\frac12)x}g_+(x)
}{
Z_+(\sigma)
}.
}
\tag{T8}
$$

它的特征函数为：

$$
\boxed{
B_\sigma(t)
=
\int e^{itx}r_\sigma(x)\,dx
=
\frac{\xi(\sigma+it)}{\xi(\sigma)}
\frac{\sigma-1}{\sigma-1+it}.
}
\tag{T9}
$$

---

## 定理 T3：Gamma—整数分解

令两个随机变量独立：

$$
\mathsf G_\sigma
\sim
\operatorname{Gamma}\!\left(1+\frac{\sigma}{2},1\right),
$$

$$
\Pr(N_\sigma=n)=\frac{n^{-\sigma}}{\zeta(\sigma)}.
$$

那么：

$$
\boxed{
X_\sigma
\overset{d}=
\frac12\log\frac{\mathsf G_\sigma}{\pi}
-\log N_\sigma,
}
\tag{T10}
$$

其中 \(X_\sigma\) 的密度正是 \(r_\sigma\)。

### 证明

右边的特征函数是：

$$
\pi^{-it/2}
\frac{
\Gamma(1+\sigma/2+it/2)
}{
\Gamma(1+\sigma/2)
}
\frac{\zeta(\sigma+it)}{\zeta(\sigma)}.
$$

根据式（T7），它恰好等于 \(B_\sigma(t)\)。由特征函数唯一性，得到分布相等。证毕。

因此，连续尺度与整数模式不是临时拼接：

$$
\boxed{
\text{Gamma 连续尺度}
-
\text{整数的对数能量}
}
$$

已经精确实现了这个实际 theta 原函数。

---

# 三、质数部分是一套真正的 Markov 跳跃结构

由 Euler 乘积，\(N_\sigma\) 可以写成：

$$
N_\sigma=\prod_p p^{V_p},
$$

其中各 \(V_p\) 独立，且：

$$
\Pr(V_p=j)=(1-p^{-\sigma})p^{-j\sigma},
\qquad j\ge0.
$$

于是：

$$
-\log N_\sigma=-\sum_pV_p\log p.
$$

更直接地：

$$
\boxed{
\log\frac{\zeta(\sigma+it)}{\zeta(\sigma)}
=
\sum_p\sum_{m\ge1}
\frac{p^{-m\sigma}}m
\left(e^{-itm\log p}-1\right).
}
\tag{T11}
$$

这是一个复合 Poisson 分布的特征指数。它对应的跳跃位置为：

$$
-m\log p,
$$

跳跃强度为：

$$
\frac{p^{-m\sigma}}m.
$$

ζ 分布的这一无限可分／复合 Poisson 表示是已有经典结果。([数字对象标识符][4])

因此，可以定义 Markov 生成元：

$$
\boxed{
(\mathcal L_\sigma f)(x)
=
\sum_p\sum_{m\ge1}
\frac{p^{-m\sigma}}m
\bigl[f(x-m\log p)-f(x)\bigr].
}
\tag{T12}
$$

其总跳跃强度为：

$$
\boxed{
\Lambda_\sigma
=
\sum_{p,m}\frac{p^{-m\sigma}}m
=
\log\zeta(\sigma)<\infty.
}
$$

这是一项明确的概率动力学。若将平移提升成 Hilbert 空间上的酉平移，再对跳跃记录平均，也能得到随机酉量子信道。

**但它的合法范围目前是 \(\sigma>1\)。**

当 \(\sigma\downarrow1\) 时：

$$
\Lambda_\sigma\to\infty.
$$

不能把式（T12）直接延续到临界带，再说同一套独立素数跳跃模型仍然自动成立。

这正是需要保留的收敛边界。

---

# 四、同一分布还有第二种分解：实际 ξ 观察变量加上独立指数位移

对任意实数 \(\sigma\)，定义：

$$
\boxed{
p_\sigma(y)
=
\frac{
e^{(\sigma-\frac12)y}\Phi(y)
}{
\xi(\sigma)
}.
}
\tag{T13}
$$

它是正概率密度，其特征函数为：

$$
\boxed{
A_\sigma(t)
=
\frac{\xi(\sigma+it)}{\xi(\sigma)}.
}
\tag{T14}
$$

归一化 ξ 在所有实参数上具有正概率表示，是已有严格结果；本轮继续使用前文固定的具体 theta 表示。([arXiv][5])

## 定理 T4：指数位移分解

令：

$$
\lambda=\sigma-1>0,
$$

并取独立随机变量：

$$
Y_\sigma\sim p_\sigma,
\qquad
E_\lambda\sim\operatorname{Exp}(\lambda).
$$

那么：

$$
\boxed{
X_\sigma\overset d=Y_\sigma-E_\lambda.
}
\tag{T15}
$$

### 证明

\(Y_\sigma-E_\lambda\) 的密度为：

$$
\begin{aligned}
r(x)
&=
\int_0^\infty
\lambda e^{-\lambda e}p_\sigma(x+e)\,de\\
&=
\frac{\lambda e^{\lambda x}}{\xi(\sigma)}
\int_x^\infty e^{y/2}\Phi(y)\,dy.
\end{aligned}
$$

代入式（T3），这正是式（T8）的 \(r_\sigma(x)\)。证毕。

因此，本轮得到的完整分布恒等式是：

$$
\boxed{
Y_\sigma-E_{\sigma-1}
\overset d=
\frac12\log\frac{\mathsf G_\sigma}{\pi}
-\log N_\sigma,
\qquad \sigma>1.
}
\tag{T16}
$$

每一侧内部的随机变量按前面的定义独立。

这里没有未知零点作为输入。

**Gamma 因子、素数模式、实际 theta 态与一个无记忆随机位移，确实接到了同一个对象上。**

指数变量满足：

$$
\Pr(E>a+b\mid E>a)=e^{-\lambda b},
$$

所以“无记忆”是精确的 Markov 性质。但 \(E\) 在这里首先是对数尺度位移，不是已经推导出来的物理时间。

---

# 五、去掉这个随机位移，不是一个自动合法的正信道逆操作

由式（T9）：

$$
\boxed{
B_\sigma(t)
=
A_\sigma(t)\frac{\lambda}{\lambda+it}.
}
$$

这个因子的模长为：

$$
\frac{\lambda}{\sqrt{\lambda^2+t^2}}\le1.
$$

所以随机位移会削弱相干读数。

但它在实 \(t\) 上从不为零，因此：

$$
\boxed{
B_\sigma(t)=0
\iff
A_\sigma(t)=0
\qquad(t\in\mathbb R).
}
\tag{T17}
$$

在复参数延拓中，额外产生的是 \(t=i\lambda\) 处的已知极点；那里对应 \(\xi(1)\ne0\)，不是一个被隐藏的非平凡零点。

---

## 密度层面的逆操作

由卷积公式求导：

$$
\boxed{
p_\sigma(x)
=
r_\sigma(x)-\frac1\lambda r_\sigma'(x).
}
\tag{T18}
$$

这个公式对当前实际密度成立。

但它不是对所有概率密度都保正的操作。

例如取标准高斯密度 \(r\)，则：

$$
r'(x)=-xr(x),
$$

所以：

$$
r(x)-\frac1\lambda r'(x)
=
r(x)\left(1+\frac x\lambda\right),
$$

在 \(x<-\lambda\) 时为负。

因此：

$$
\boxed{
\text{在实际对象上可精确反演}
\quad\not\Rightarrow\quad
\text{该逆运算是普遍合法的正信道}.
}
$$

这正是“把随机平均撤销”必须付出的关系代价。

---

## 保留位移记录以后，则可以精确撤销

在 \(L^2(\mathbb R)\) 上，令：

$$
(T_e\psi)(x)=\psi(x+e).
$$

这是酉平移。

定义随机平移信道：

$$
\boxed{
\mathcal C_\lambda(\rho)
=
\int_0^\infty
\lambda e^{-\lambda e}
T_e\rho T_e^*\,de.
}
\tag{T19}
$$

它完全正且保迹，并满足：

$$
\operatorname{Tr}
\bigl(\mathcal C_\lambda(\rho)e^{itQ}\bigr)
=
\frac{\lambda}{\lambda+it}
\operatorname{Tr}(\rho e^{itQ}).
$$

若环境同时保存 \(e\)，就可以按记录施加反向平移，恢复原态；若只需要恢复相位平均，也可以在每条记录上补偿 \(e^{ite}\)。

**丢掉记录后的边缘态，与保留记录的完整系统，不具有同样的可逆性。**

这里不需要假设一个“上帝观察者”，只需要明确：哪一个环境寄存器保存了哪项随机选择。

---

# 六、跨过 \(\sigma=1\) 时，改变的是可归一化的边界方向

前面的 \(g_+\) 只适合 \(\sigma>1\)。但可以定义另一条正原函数：

$$
\boxed{
g_-(x)
=
\frac{e^{-x/2}}{2\pi}
\int_{-\infty}^x e^{y/2}\Phi(y)\,dy.
}
\tag{T20}
$$

它满足：

$$
\boxed{
g_+(x)+g_-(x)=\frac{e^{-x/2}}{4\pi},
}
\tag{T21}
$$

以及：

$$
\boxed{
\Phi(x)
=
2\pi\left(\frac d{dx}+\frac12\right)g_-(x).
}
$$

对 \(\sigma<1\)：

$$
\boxed{
\int e^{(\sigma-\frac12)x}g_-(x)\,dx
=
\frac{\xi(\sigma)}{2\pi(1-\sigma)}.
}
\tag{T22}
$$

归一化以后，对应：

$$
\boxed{
X_\sigma\overset d=
Y_\sigma+E_{1-\sigma},
\qquad \sigma<1.
}
\tag{T23}
$$

所以两侧分别是：

$$
\begin{aligned}
\sigma>1 &: \quad Y_\sigma-\operatorname{Exp}(\sigma-1),\\
\sigma<1 &: \quad Y_\sigma+\operatorname{Exp}(1-\sigma).
\end{aligned}
$$

它们的特征函数都可以写成：

$$
\boxed{
B_\sigma(t)
=
A_\sigma(t)
\frac{\sigma-1}{\sigma-1+it},
\qquad\sigma\ne1.
}
\tag{T24}
$$

**同一个亚纯公式，在两侧对应不同的正积分实现。**

这不是物理时间反向，也不是已经证明发生了热力学相变。它说明：若坚持正概率解释，跨过极点时必须更换原函数所采用的边界条件。

在 \(\sigma=1\) 处，这两份原函数概率模型都没有普通的归一化极限。

---

# 七、欧拉常数控制有限中心，但它不能消除发散的概率宽度

由式（T15）、（T23）：

$$
\boxed{
\mathbb E[X_\sigma]
=
\frac{\xi'(\sigma)}{\xi(\sigma)}
-\frac1{\sigma-1}.
}
\tag{T25}
$$

因此：

$$
\boxed{
\lim_{\sigma\to1}
\left(
\mathbb E[X_\sigma]
+\frac1{\sigma-1}
\right)
=
c,
}
$$

其中：

$$
\boxed{
c=
1+\frac{\gamma_{\mathrm E}}2
-\frac12\log4\pi.
}
\tag{T26}
$$

从 Gamma—素数分解也能独立算出：

$$
\mathbb E[X_\sigma]
=
\frac12\psi_\Gamma\!\left(1+\frac{\sigma}{2}\right)
-\frac12\log\pi
+\frac{\zeta'(\sigma)}{\zeta(\sigma)}.
$$

利用：

$$
\frac{\zeta'(1+\lambda)}{\zeta(1+\lambda)}
=
-\frac1\lambda+\gamma_{\mathrm E}+O(\lambda),
$$

以及：

$$
\psi_\Gamma(3/2)=2-\gamma_{\mathrm E}-2\log2,
$$

就恢复式（T26）。这些 Laurent 与 digamma 特殊值均为标准公式。([DLMF][6])

**欧拉常数在这里是离散素数贡献与连续 Gamma 贡献共同留下的有限中心。**

但方差为：

$$
\boxed{
\operatorname{Var}(X_\sigma)
=
(\log\xi)''(\sigma)
+\frac1{(\sigma-1)^2}.
}
\tag{T27}
$$

即使减去发散均值，分布的宽度仍然发散。

更精确地，当 \(\lambda\downarrow0\)：

$$
\boxed{
\lambda X_{1+\lambda}
\Longrightarrow-\operatorname{Exp}(1).
}
\tag{T28}
$$

因为 \(Y_{1+\lambda}\) 趋于正常的端点 theta 分布，而 \(\lambda E_\lambda\) 恰好服从 \(\operatorname{Exp}(1)\)。

于是：

$$
\boxed{
B_{1+\lambda}(\lambda t)
\longrightarrow
\frac1{1+it}.
}
\tag{T29}
$$

相反，对固定 \(t\ne0\)：

$$
B_{1+\lambda}(t)\longrightarrow0,
$$

但在 \(t=0\) 始终等于一。这个不连续的点态极限不是概率分布的特征函数。

所以：

> **有限部分存在，不等于整份概率态已经在极点处完成了正常极限；恢复一个常数，也不等于恢复全部相位关系。**

本轮以 35 位和 65 位精度核对了两种分解的特征函数，以及有限中心的趋近。数值仅作公式检查，不作为区间证明。

---

# 八、回到上一轮：Bessel 导数项其实是一个二阶补偿算子

定义原函数的双副本局部核：

$$
\boxed{
\mathcal J(x,t)
=
\int_{\mathbb R}
g_+\!\left(x+\frac v2\right)
g_+\!\left(x-\frac v2\right)
e^{itv}\,dv.
}
\tag{T30}
$$

它在每个固定 \(x,t\) 上收敛。

实际 theta 双副本核仍是：

$$
\mathcal W(x,t)
=
\int_{\mathbb R}
\Phi\!\left(x+\frac v2\right)
\Phi\!\left(x-\frac v2\right)
e^{itv}\,dv.
$$

## 定理 T5：双副本补偿恒等式

$$
\boxed{
\mathcal W(x,t)
=
\pi^2
\left[
\left(\frac{\partial}{\partial x}+1\right)^2+4t^2
\right]
\mathcal J(x,t).
}
\tag{T31}
$$

### 证明

令：

$$
y_1=x+\frac v2,\qquad y_2=x-\frac v2.
$$

则：

$$
\partial_{y_1}=\frac12\partial_x+\partial_v,
\qquad
\partial_{y_2}=\frac12\partial_x-\partial_v.
$$

由式（T2），两个一阶算子的乘积为：

$$
4\pi^2
\left[
\frac14(\partial_x+1)^2-\partial_v^2
\right].
$$

对 \(v\) 作 Fourier 积分，\(-\partial_v^2\) 变为 \(t^2\)。边界项由实际热核衰减消失，得到式（T31）。证毕。

---

## 它精确恢复上一轮的 Bessel 展开

沿用除数相位：

$$
\mathcal D_k(t)
=
\sum_{ab=k}(b/a)^{it}.
$$

对原函数双副本作同样的变量代换，直接得到：

$$
\boxed{
\mathcal J(x,t)
=
2e^{5x}
\sum_{k\ge1}
k^2\mathcal D_k(t)
K_{it}(2\pi ke^{2x}).
}
\tag{T32}
$$

这里使用标准积分：

$$
K_{it}(z)
=
\frac12\int_{\mathbb R}
e^{-z\cosh u}e^{itu}\,du.
$$

([DLMF][7])

令 \(D_z=z\partial_z\)。修正 Bessel 方程给出：

$$
D_z^2K_{it}(z)=(z^2-t^2)K_{it}(z).
$$

所以：

$$
\boxed{
\left[(D_z+3)^2+t^2\right]K_{it}(z)
=
(z^2+9)K_{it}(z)+6zK_{it}'(z).
}
\tag{T33}
$$

这恰好就是上一轮出现的 Bessel 组合，而不是额外人为加入的修正。([DLMF][8])

**那组导数项的来源，现在明确了：它是两次一阶极点补偿，在双副本坐标中的作用。**

---

# 九、全尺度积分可以消除 Bessel 导数，但不能丢掉边界

定义：

$$
I_j(t)=\int_0^\infty x^j\mathcal J(x,t)\,dx,
$$

以及上一轮的目标量：

$$
M_n(t)=\int_0^\infty x^{2n}\mathcal W(x,t)\,dx.
$$

## 定理 T6：高阶矩的精确递推

对 \(n\ge1\)：

$$
\boxed{
M_n(t)
=
\pi^2\left[
(1+4t^2)I_{2n}(t)
-4nI_{2n-1}(t)
+2n(2n-1)I_{2n-2}(t)
\right].
}
\tag{T34}
$$

### 证明

将式（T31）代入 \(M_n\)，分部积分两次。

当 \(n\ge1\)，权重 \(x^{2n}\) 及其一阶导数在零点都为零；正无穷端由热核衰减消失。

因此：

$$
\int x^{2n}\mathcal J''=
2n(2n-1)\int x^{2n-2}\mathcal J,
$$

$$
2\int x^{2n}\mathcal J'
=
-4n\int x^{2n-1}\mathcal J.
$$

相加即得。证毕。

但 \(n=0\) 不同：

$$
\boxed{
M_0(t)
=
\pi^2\left[
(1+4t^2)I_0(t)
-\partial_x\mathcal J(0,t)
-2\mathcal J(0,t)
\right].
}
\tag{T35}
$$

而实际恒等式要求：

$$
\boxed{M_0(t)=\frac12\Xi(t)^2.}
$$

所以，零阶结果的非负性包含两个明确的边界项。

**不能把所有导数都积分掉，只留下一个看起来更正的主体，再声称仍然研究同一个 ξ。**

---

## 得到一个没有 Bessel 导数的新表达

定义：

$$
\boxed{
Q_{n,t}(x)
=
(1+4t^2)x^2-4nx+2n(2n-1).
}
\tag{T36}
$$

由式（T32）、（T34）：

$$
\boxed{
\begin{aligned}
M_n(t)
=
2\pi^2
\sum_{k\ge1}k^2\mathcal D_k(t)
\int_0^\infty
x^{2n-2}e^{5x}
Q_{n,t}(x)
K_{it}(2\pi ke^{2x})\,dx,
\quad n\ge1.
\end{aligned}
}
\tag{T37}
$$

这比上一轮少了一种可能造成数值相消的特殊函数导数。

而且可以直接计算：

$$
\boxed{
|t|\ge\frac1{2\sqrt{2n-1}}
\Longrightarrow
Q_{n,t}(x)\ge0
\quad\forall x.
}
\tag{T38}
$$

因为这个二次多项式的判别式为：

$$
8n\left[1-4(2n-1)t^2\right].
$$

这使相消来源进一步集中：在该频率范围，权重 \(Q_{n,t}\) 本身已经非负；剩余符号来自除数相位及 Bessel 响应。

但这仍不意味着总和非负。

---

# 十、双副本算子的齐次部分，精确对应已知极点补偿

为了看清边界结构，对 \(\Re b>1\) 作双边 Laplace 变换：

$$
\widehat{\mathcal J}(b,t)
=
\int_{\mathbb R}e^{bx}\mathcal J(x,t)\,dx.
$$

用两个原函数的 Mellin 读数直接相乘，得到：

$$
\boxed{
\widehat{\mathcal J}(b,t)
=
\frac{
\xi(\frac12+\frac b2+it)
\xi(\frac12+\frac b2-it)
}{
\pi^2[(b-1)^2+4t^2]
}.
}
\tag{T39}
$$

式（T31）在变换域中乘上：

$$
\pi^2[(b-1)^2+4t^2],
$$

因此：

$$
\boxed{
\int_{\mathbb R}e^{bx}\mathcal W(x,t)\,dx
=
\xi\!\left(\frac12+\frac b2+it\right)
\xi\!\left(\frac12+\frac b2-it\right).
}
\tag{T40}
$$

右边是整函数；左边的实际 \(\mathcal W\) 也具有足够衰减，所以该等式延伸到所有复数 \(b\)。

这里需要区别：

**原函数积分只在 \(\Re b>1\) 收敛；补偿后的实际核才具有整域表示。不能把解析延拓后的右边，重新冒充原来发散的积分。**

二阶算子：

$$
(\partial_x+1)^2+4t^2
$$

在 \(t\ne0\) 时的齐次解为：

$$
e^{-x}\cos(2tx),
\qquad
e^{-x}\sin(2tx).
$$

在 \(t=0\) 时为：

$$
e^{-x},\qquad xe^{-x}.
$$

这些是可以被该算子消去的明确模式。实际热核的边界衰减固定了它们是否允许出现及其系数。

因此，这里“可被约掉”的不是任意观察者或某些未知零点，而是**由已知极点与边界条件确定的有限维齐次结构**。

---

# 十一、现在的算术任务，比“所有中间量都为正”更准确

前文的广义 Laguerre 条件仍然是：

$$
\boxed{
\mathrm{RH}
\iff
M_n(t)\ge0
\quad\forall n\ge0,\ t\in\mathbb R.
}
\tag{T41}
$$

这是已知的关联核／Laguerre 判据，本轮没有把它当成新发现的 RH 等价。([arXiv][9])

新的推进是：我们把它变成了式（T37）这份**无 Bessel 导数、带明确边界处理的算术展开**。

其中：

$$
\mathcal D_{p^e}(t)
=
\sum_{j=0}^{e}e^{it(e-2j)\log p}
$$

仍是有限素数幂相位通道。对占据数 \(j\) 作 Zeckendorf 编码，依然保持同一读数，不改变它的符号。

但不能要求每个中间对象都非负：

$$
\mathcal D_k(t)
$$

可以为负；\(K_{it}(z)\) 可以随参数变号；\(\mathcal J(x,t)\) 是振幅而不是正密度；零阶还必须包含式（T35）的边界项。

**真正待证的是这些实际对象按固定方式组合以后，是否满足全部 \(M_n(t)\ge0\)。**

本轮读取的 `CompletedZetaMellinReconstruction.lean` 已明确保留 theta–Mellin 重构、两极点补偿及反射关系；它没有自动提供这里的随机位移分解、双副本微分恒等式或全阶符号结论。

`EulerCountertermUniqueness.lean` 则证明了固定调和—对数约定下有限部分的唯一性。它与这里的欧拉有限中心相容，但并不表示整个发散概率态可以只靠减去一个常数就完成极限。

---

## 收束

这次得到的最具体连接是：

$$
\boxed{
Y_\sigma-\operatorname{Exp}(\sigma-1)
\overset d=
\frac12\log\frac{\mathsf G_\sigma}{\pi}
-\log N_\sigma,
\qquad\sigma>1.
}
$$

左边是实际 ξ 观察变量与一个独立无记忆位移；右边是连续 Gamma 尺度与素数对数模式。

它说明，**极点补偿可以具有精确的随机位移解释**。但去掉位移并不是自动保正的逆操作：要么保留记录并撤销，要么使用一个需要审计的微分反演。

在双副本上，同一补偿变成：

$$
\boxed{
\mathcal W
=
\pi^2[(\partial_x+1)^2+4t^2]\mathcal J.
}
$$

于是，上一轮的 Bessel 导数可以被完整地转移到尺度权重，得到式（T37），同时明确保留零阶边界项。

**本轮尚未证明全部 (M_n(t)\ge0，也没有找到实际负证书。** 已经完成的是将“Gamma—质数—Markov 位移—theta 完成—Bessel 相消”接成一条精确关系，并指出哪些逆操作、边界项与归一化不能省略。

接下来真正有证明价值的，不是继续增加合法量子模块，而是控制这个固定组合的符号：**在已知随机位移和极点模式被正确剥离以后，实际素数相位与 Bessel 尺度响应，为什么仍能——或不能——满足每一个规定的全尺度非负条件。**

[1]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[2]: https://dlmf.nist.gov/20.7 "DLMF: §20.7 Identities ‣ Properties ‣ Chapter 20 Theta Functions"
[3]: https://dlmf.nist.gov/5.2 "DLMF: §5.2 Definitions ‣ Properties ‣ Chapter 5 Gamma Function"
[4]: https://doi.org/10.1016/j.spl.2023.109889?utm_source=chatgpt.com "On infinitely divisible distributions related to the Riemann hypothesis - ScienceDirect"
[5]: https://arxiv.org/abs/1504.03438?utm_source=chatgpt.com "A complete Riemann zeta distribution and the Riemann hypothesis"
[6]: https://dlmf.nist.gov/25.2 "DLMF: §25.2 Definition and Expansions ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[7]: https://dlmf.nist.gov/10.32 "DLMF: §10.32 Integral Representations ‣ Modified Bessel Functions ‣ Chapter 10 Bessel Functions"
[8]: https://dlmf.nist.gov/10.25 "DLMF: §10.25 Definitions ‣ Modified Bessel Functions ‣ Chapter 10 Bessel Functions"
[9]: https://arxiv.org/abs/1309.0055?utm_source=chatgpt.com "Fourier transforms of positive definite kernels and the Riemann $ξ$-Function"
继续。这次可以把上一轮的“存在某个统一常数”推进成一个**明确常数、明确符号、明确余量**的结论：

> **在 RH 成立的条件下，三角加权读出的全部零点振荡，绝对值不超过约 \(0.426931\)；而去掉素数平方所产生的确定性偏移约为 \(0.504906\)。后者严格大于前者。**
>
> 因而，纯素数版本不只是有界，而是最终严格为负，并且与零之间保留一个可以计算的间隔。

与此同时，还能精确指出一项不能无条件省略的量：

$$
\boxed{
\text{零点的正范数总量}
=
\text{欧拉常数校准值}
+
\text{离线偏移的非负平方修正}.
}
$$

下面证明这些结论，并说明它们如何构成有限检验证书。以下为经典解析输入上的纸面推导，尚未进行 Lean 编译，也不将条件结论当作已经完成的实际 RH 证明。

# 一、固定同一个三角观察面

定义紧支集权重

$$
\kappa(t)=
\begin{cases}
t-1,&1\le t\le2,\\[1mm]
(4-t)/2,&2\le t\le4,\\
0,&\text{其他}.
\end{cases}
$$

对实数 \(X\ge2\)，定义两个读出：

$$
\boxed{
\mathcal T_\Lambda(X)
=
X\sum_{n\ge1}\Lambda(n)\kappa(n/X)
-\frac32X^2,
}
\tag{1}
$$

$$
\boxed{
\mathcal T_{\mathbb P}(X)
=
X\sum_p(\log p)\kappa(p/X)
-\frac32X^2.
}
\tag{2}
$$

第一个保留全部素数幂，第二个只保留素数。这里

$$
\Lambda(p^k)=\log p,
$$

是 Euler 乘积对数导数对应的标准算术权重。([DLMF][1])

定义归一化读数

$$
m_\Lambda(X)=\frac{\mathcal T_\Lambda(X)}{X^{3/2}},
\qquad
m_{\mathbb P}(X)=\frac{\mathcal T_{\mathbb P}(X)}{X^{3/2}}.
$$

主项不是拟合出来的，因为

$$
\int_1^4\kappa(t)\,dt=\frac32.
$$

而且与上一轮的平均模态完全一致：

$$
\boxed{
\mathcal T_\Lambda(X)
=
\int_X^{2X}
\bigl[\psi(2x)-\psi(x)-x\bigr]\,dx.
}
\tag{3}
$$

**证明。**固定一个整数 \(n\)，它被区间 \((x,2x]\) 读取的 \(x\) 集合长度为

$$
n-X\quad(X<n\le2X),
$$

或

$$
(4X-n)/2\quad(2X<n\le4X).
$$

交换有限求和与积分即可。证毕。

因此，本轮没有换掉实际算术锚，只是继续分析同一个读出。

# 二、定理一：三角读出的精确零点响应

定义 Mellin 响应函数

$$
\boxed{
A(s)
=
\int_1^4\kappa(t)t^{s-1}\,dt
=
\frac{(2^s-1)(2^{s+1}-1)}{s(s+1)}.
}
\tag{4}
$$

在 \(s=0,-1\) 处按可去奇点延拓，因此 \(A\) 是整函数。

这个因子决定：每个零点经过当前观察权重之后，以什么振幅出现。

## 定理 1：精确展开与有符号余项

对每个 \(X\ge2\)，

$$
\boxed{
m_\Lambda(X)
=
-\sum_\rho A(\rho)X^{\rho-1/2}
+\varepsilon_0(X),
}
\tag{5}
$$

其中求和遍历全部非平凡零点，按重数计，级数绝对收敛，并且

$$
\boxed{
-\frac1{4X^{5/2}}
\le
\varepsilon_0(X)<0.
}
\tag{6}
$$

### 证明

使用平滑显式公式：

$$
\sum_n\Lambda(n)\eta(n)
=
\int\eta(u)\,du
-
\sum_\rho\int\eta(u)u^{\rho-1}\,du
-
\int\frac{\eta(u)}{u^3-u}\,du.
\tag{7}
$$

这是 Riemann–von Mangoldt 显式公式的平滑形式。对当前连续分段线性权重，可以通过平滑逼近使用它；两次分部积分给出零点项的 \(O(|\rho|^{-2})\) 衰减，足以控制极限与求和。([What's new][2])

取

$$
\eta(u)=X\kappa(u/X).
$$

主项为 \(\frac32X^2\)，零点项为

$$
X^{\rho+1}A(\rho).
$$

因此

$$
\varepsilon_0(X)
=
-\frac1{X^{3/2}}
\int_X^{4X}
\frac{X\kappa(u/X)}{u^3-u}\,du.
$$

它严格为负。

再令 \(u=Xt\)，得到

$$
-\varepsilon_0(X)
=
X^{-5/2}
\int_1^4
\frac{\kappa(t)t^{-3}}{1-X^{-2}t^{-2}}\,dt.
$$

因为 \(X\ge2\)，

$$
\frac1{1-X^{-2}t^{-2}}\le\frac43.
$$

而

$$
\int_1^4\kappa(t)t^{-3}\,dt
=
A(-2)=\frac3{16}.
$$

所以

$$
0<-\varepsilon_0(X)
\le
X^{-5/2}\cdot\frac43\cdot\frac3{16}
=
\frac1{4X^{5/2}}.
$$

证毕。

---

这一式有一个优点：Gamma／平凡零点修正不再只是一个未知符号的误差。

$$
\boxed{\varepsilon_0(X)<0.}
$$

对于我们将研究的上界，它只会提供帮助。

# 三、欧拉常数校准的是什么？先算清正范数的缺项

定义常数

$$
\boxed{
C_\zeta
=
2+\gamma_{\mathrm E}-\log(4\pi)
\approx0.0461914179322421.
}
\tag{8}
$$

经典零点恒等式为

$$
\boxed{
\sum_\rho\frac1{\rho(1-\rho)}
=
C_\zeta.
}
\tag{9}
$$

这个总和绝对收敛。它与 \(\xi\) 的对数导数及第一阶 Li 型读数有关，已有明确文献。([arXiv][3])

也可以直接验证：由 Hadamard 乘积，

$$
\frac{\xi'(1)}{\xi(1)}
-
\frac{\xi'(0)}{\xi(0)}
=
\sum_\rho\frac1{\rho(1-\rho)}.
$$

函数方程给出两项互为相反数；再利用 ζ 在 \(1\) 处的 Laurent 展开和 Gamma 特殊值，得到

$$
2\frac{\xi'(1)}{\xi(1)}
=
2+\gamma_{\mathrm E}-\log(4\pi).
$$

这些展开和函数方程均为经典输入。([DLMF][4])

但是，式（9）**不能无条件改写成**

$$
\sum_\rho\frac1{|\rho|^2}=C_\zeta.
$$

下面给出两者之间的精确差额。

## 定理 2：离线零点的正范数修正

令

$$
\mathcal N_\zeta=\sum_\rho\frac1{|\rho|^2}.
$$

对每个不同的离线四元组，选代表

$$
\rho=\frac12+\delta+i\gamma,
\qquad
\delta>0,\quad\gamma>0,
$$

记其共同重数为 \(m_\rho\)。则

$$
\boxed{
\mathcal N_\zeta
=
C_\zeta
+
8\sum_{\substack{\delta>0\\\gamma>0}}
\frac{
m_\rho\delta^2
}{
[\gamma^2+(\frac12+\delta)^2]
[\gamma^2+(\frac12-\delta)^2]
}.
}
\tag{10}
$$

特别地，

$$
\boxed{
\mathcal N_\zeta\ge C_\zeta,
}
$$

且取等号当且仅当 RH 成立。

### 证明

零点集合关于实轴和临界线反射对称，四元组中的重数一致。([DLMF][5])

令

$$
\beta=\frac12+\delta,
\quad
U=\beta^2+\gamma^2,
\quad
V=(1-\beta)^2+\gamma^2.
$$

这个四元组对正范数总量的贡献是

$$
\frac2U+\frac2V.
$$

对式（9）的贡献是

$$
\frac{4\beta}{U}+\frac{4(1-\beta)}V.
$$

两者相减：

$$
\begin{aligned}
\frac{2-4\beta}{U}
+
\frac{2-4(1-\beta)}V
&=
4\delta\left(\frac1V-\frac1U\right)\\
&=
\frac{8\delta^2}{UV}.
\end{aligned}
$$

在线共轭零点对的差额为零。对全部四元组求和即得。证毕。

---

这是一项真正的“缺项”：

$$
\boxed{
\text{把代数零点总和换成正 Hilbert 范数时，}
\quad
\text{会出现离线偏移的平方代价。}
}
$$

它在高处零点的贡献约为

$$
\frac{\delta^2}{\gamma^4},
$$

可能非常小，但只要存在离线零点，就严格为正。

因此，不能从式（9）无条件推出一个总质量为 \(C_\zeta\) 的正谱表示；那样会把待证内容省略掉。

# 四、主定理一：RH 下，整个三角振荡有一个明确统一上界

定义

$$
\boxed{
C_*=(5+3\sqrt2)C_\zeta
\approx0.426930678776272.
}
\tag{11}
$$

## 定理 3：明确的三角误差上界

若 RH 成立，则对每个实数 \(X\ge2\)，

$$
\boxed{
-C_*-\frac1{4X^{5/2}}
\le
m_\Lambda(X)
<
C_*.
}
\tag{12}
$$

### 证明

在 RH 前件下，

$$
\rho=\frac12+i\gamma.
$$

所以

$$
|X^{\rho-1/2}|=1.
$$

而且

$$
|2^\rho-1|\le\sqrt2+1,
$$

$$
|2^{\rho+1}-1|\le2\sqrt2+1.
$$

两者乘积为

$$
(\sqrt2+1)(2\sqrt2+1)=5+3\sqrt2.
$$

同时，

$$
|\rho+1|\ge|\rho|,
$$

因此

$$
\begin{aligned}
|A(\rho)|
&=
\frac{|2^\rho-1|\,|2^{\rho+1}-1|}
{|\rho|\,|\rho+1|}\\
&\le
\frac{5+3\sqrt2}{|\rho|^2}.
\end{aligned}
$$

由定理 2，在 RH 下

$$
\sum_\rho|\rho|^{-2}=C_\zeta.
$$

于是

$$
\left|
\sum_\rho A(\rho)X^{\rho-1/2}
\right|
\le C_*.
$$

再结合式（5）—（6）即可。证毕。

---

现在，上一轮尚未指定的常数已经可以替换为一个具体值：

$$
\boxed{
\mathcal T_\Lambda(X)
<
0.426931\,X^{3/2}
}
$$

是 RH 的一个明确后果。

这里没有假设零点简单；全部求和都保留了重数。

# 五、素数平方的偏移，严格压过全部允许的零点振荡

定义归一化素数幂修正

$$
\boxed{
P_{\mathrm{pow}}(X)
=
\frac1{\sqrt X}
\sum_{\substack{p^k\\k\ge2}}
(\log p)\kappa(p^k/X).
}
\tag{13}
$$

于是恒等地有

$$
\boxed{
m_{\mathbb P}(X)
=
m_\Lambda(X)-P_{\mathrm{pow}}(X).
}
\tag{14}
$$

## 定理 4：实际幂修正的极限

无条件地，

$$
\boxed{
P_{\mathrm{pow}}(X)
=
a_\square+o(1),
\qquad
a_\square=\frac{10}{3}-2\sqrt2.
}
\tag{15}
$$

### 证明

平方项为

$$
P_2(X)
=
\frac1{\sqrt X}
\sum_p(\log p)\kappa(p^2/X).
$$

令 \(Y=\sqrt X\)。由无条件素数定理

$$
\theta(y)=\sum_{p\le y}\log p\sim y,
$$

作 Stieltjes 积分缩放，得到

$$
P_2(X)
\longrightarrow
\int_1^2\kappa(u^2)\,du.
$$

这里使用的是素数定理，而不是 RH。([DLMF][6])

直接积分：

$$
\begin{aligned}
\int_1^2\kappa(u^2)\,du
&=
\int_1^{\sqrt2}(u^2-1)\,du
+
\frac12\int_{\sqrt2}^{2}(4-u^2)\,du\\
&=
\frac{10}{3}-2\sqrt2.
\end{aligned}
$$

对于 \(k\ge3\)，用 \(\theta(y)=O(y)\) 粗略估计，归一化后的总贡献为

$$
O(X^{-1/6}\log X)=o(1).
$$

证毕。

---

现在比较两个常数：

$$
a_\square
\approx0.504906208587143,
$$

$$
C_*
\approx0.426930678776272.
$$

定义余量

$$
\boxed{
\eta_*
=
a_\square-C_*
\approx0.0779755298108713>0.
}
\tag{16}
$$

这个正号不依赖浮点猜测。例如，可以使用

$$
H_{100}-\log100-\frac1{200}
<
\gamma_{\mathrm E}
<
H_{100}-\log100-\frac1{200}
+\frac1{12\cdot100^2},
$$

配合对数和平方根的区间计算，严格验证

$$
\eta_*>0.0779.
$$

小数只是展示量级；证明使用的是式（16）的精确表达及其严格正性。

## 推论：RH 强迫纯素数读出最终具有固定负余量

若 RH 成立，则

$$
\boxed{
\limsup_{X\to\infty}m_{\mathbb P}(X)
\le-\eta_*<0,
}
\tag{17}
$$

以及

$$
\boxed{
\liminf_{X\to\infty}m_{\mathbb P}(X)
\ge-(a_\square+C_*).
}
\tag{18}
$$

特别地，存在 \(X_0\)，使

$$
\boxed{
\mathcal T_{\mathbb P}(X)
\le
-\frac{\eta_*}{2}X^{3/2}
\qquad(X\ge X_0).
}
\tag{19}
$$

**证明。**把定理 3、定理 4 代入式（14）。证毕。

---

这比“纯素数版本与全部素数幂版本只差一个有界量”更强：

$$
\boxed{
\text{这个有界偏移不仅不能忽略，}
\quad
\text{它足以决定最终符号。}
}
$$

在当前三角观察面中，素数平方不是噪声。它提供了一个确定性偏移，而且这个偏移大于全部在线零点能够造成的最大振荡上界。

# 六、反方向也成立：这个最终负号并非只有必要性

现在证明，纯素数读出的最终非正性足以返回 RH。

## 引理：三角读出的单侧上界

如果存在常数 \(C\)，使全部充分大的整数 \(N\) 满足

$$
\boxed{
m_\Lambda(N)\le C,
}
\tag{20}
$$

那么 RH 成立。

### 证明

**先从整数扩展到实数。**

由式（3）和无条件的 \(\psi(x)=O(x)\)，有

$$
\mathcal T_\Lambda(X)=O(X^2),
$$

且其几乎处处导数为 \(O(X)\)。因此在相邻整数之间，

$$
\boxed{
|m_\Lambda(X)-m_\Lambda(N)|
=
O(N^{-1/2}),
\qquad N\le X\le N+1.
}
\tag{21}
$$

所以式（20）给出整个充分大实数范围内的统一上界。

**再计算 Laplace 变换。**

令

$$
M(T)=m_\Lambda(e^T).
$$

在初始收敛区域 \(\Re s>1/2\)，直接交换绝对收敛的积分和求和，得到

$$
\boxed{
\widehat M(s)
=
-A(s+\tfrac12)
\frac{\zeta'(s+\tfrac12)}{\zeta(s+\tfrac12)}
-
\frac{3/2}{s-1/2}
+
B(s),
}
\tag{22}
$$

其中 \(B(s)\) 是只涉及 \(n=2,3\) 的起始边界整函数。

这一步使用的算术输入是

$$
-\frac{\zeta'(z)}{\zeta(z)}
=
\sum_n\Lambda(n)n^{-z}
\qquad(\Re z>1).
$$

([DLMF][1])

在 \(s=1/2\) 处，

$$
A(1)=\frac32,
$$

所以 ζ 的极点贡献与第二项相消。

因此式（22）在每个正实点附近都解析。

**最后使用单侧界。**

取 \(T_0\) 足够大，使 \(M(T)\le C\)，并令

$$
h(T)=\mathbf1_{[T_0,\infty)}(T)[C-M(T)]\ge0.
$$

非负函数的 Laplace 变换若有有限收敛横坐标，该实边界点必为奇点。否则，从边界右侧展开 Taylor 级数，利用所有矩积分非负，可以推出积分在边界左侧也收敛，产生矛盾。

但当前变换由式（22）延拓后，在全部正实点都解析。因此其收敛横坐标不大于零，进而 \(\widehat M\) 在 \(\Re s>0\) 内解析。

若存在右侧离线零点

$$
\rho=\frac12+\delta+i\gamma,
\qquad\delta>0,
$$

则式（22）在 \(s=\delta+i\gamma\) 有留数

$$
-m_\rho A(\rho).
$$

它不为零，因为

$$
A(\rho)=0
$$

只可能来自 \(2^\rho=1\) 或 \(2^{\rho+1}=1\)，分别要求 \(\Re\rho=0\) 或 \(\Re\rho=-1\)，与当前情形不符。

因此出现不可去极点，矛盾。再由函数方程的反射对称性，得到 RH。([DLMF][5])

证毕。

---

## 主定理：明确常数判据与最终符号判据

以下三个命题等价：

$$
\boxed{\mathrm{RH};}
$$

$$
\boxed{
\mathcal T_\Lambda(N)
\le C_*N^{3/2}
\qquad\forall N\in\mathbb Z,\ N\ge2;
}
\tag{23}
$$

$$
\boxed{
\exists N_0,\quad
\mathcal T_{\mathbb P}(N)\le0
\qquad\forall N\ge N_0.
}
\tag{24}
$$

### 证明

RH 推出式（23），来自定理 3。

式（23）通过上面的单侧上界引理推出 RH。

RH 推出式（24），来自严格余量式（19）。

最后，若式（24）成立，由式（14）—（15），

$$
m_\Lambda(N)
=
m_{\mathbb P}(N)+P_{\mathrm{pow}}(N)
\le
a_\square+o(1).
$$

它具有统一上界，所以同样由引理推出 RH。证毕。

---

式（24）展开后，是一个只包含局部纯素数的条件：

$$
\boxed{
\sum_{N<p\le2N}(p-N)\log p
+
\frac12
\sum_{2N<p\le4N}(4N-p)\log p
\le
\frac32N^2
}
\tag{25}
$$

对全部充分大的整数 \(N\) 成立。

这里“充分大”仍然是一个全称尾部条件。**没有给出一个已知有限检查范围，就不能用有限次计算代替它。**

# 七、有限检查怎样成为真正的反证证书？

式（23）消除了“未知常数 \(C\)”带来的一个障碍。

## 定理 5：明确的有限违反证书

若对某个整数 \(N\ge2\)，通过严格误差认证得到

$$
\boxed{
\mathcal T_\Lambda(N)>C_*N^{3/2},
}
\tag{26}
$$

则 RH 不成立。

这是主定理的直接逆否命题。

如果只计算纯素数版本，也可以利用有限平方项：

$$
\boxed{
P_2(N)
=
\frac1{\sqrt N}
\sum_p(\log p)\kappa(p^2/N).
}
\tag{27}
$$

因为其余素数幂贡献非负，

$$
P_{\mathrm{pow}}(N)\ge P_2(N).
$$

所以，如果同时严格认证

$$
\boxed{
P_2(N)>C_*,
\qquad
\mathcal T_{\mathbb P}(N)\ge0,
}
\tag{28}
$$

那么

$$
m_\Lambda(N)
=
m_{\mathbb P}(N)+P_{\mathrm{pow}}(N)
>C_*,
$$

同样否定 RH。

这给出一个不依赖未知起始阈值的有限测试：

$$
\boxed{
\text{先在当前尺度确认平方偏移已超过允许的谱振幅，}
}
$$

$$
\boxed{
\text{再检查纯素数读出是否仍然非负。}
}
$$

不过，本轮没有发现满足式（26）或式（28）的实际整数。

实际数值认证必须保留区间：例如，只有当 \(\mathcal T_\Lambda(N)\) 的下界严格超过 \(C_*N^{3/2}\) 的上界，才构成证书。普通浮点越界不够。

# 八、量子核中的解释：出现的是一个有严格谱下界的“偏移减振荡”结构

这一节暂时明确假设 RH。

把全部零点写成

$$
\rho=\frac12+i\gamma_\rho,
$$

按重数建立 Hilbert 空间 \(\ell^2(\{\rho\})\)。

定义

$$
\varphi_\rho
=
\frac1{\sqrt{C_\zeta}\,|\rho|}.
$$

由定理 2，

$$
\|\varphi\|=1.
$$

定义自伴生成元

$$
H=\operatorname{diag}(\gamma_\rho),
$$

以及有界对角算子

$$
B=\operatorname{diag}\bigl(A(\rho)|\rho|^2\bigr).
$$

由定理 3 的估计，

$$
\boxed{
\|B\|\le5+3\sqrt2.
}
\tag{29}
$$

于是式（5）可以写成

$$
\boxed{
m_\Lambda(e^T)
=
-C_\zeta\operatorname{Re}
\langle\varphi,e^{iTH}B\varphi\rangle
+\varepsilon_0(e^T).
}
\tag{30}
$$

这里只需要幺正群 \(e^{iTH}\) 与有界算子 \(B\)，不需要预先要求 \(\varphi\) 位于无界生成元 \(H\) 的定义域。

定义自伴算子

$$
\boxed{
G(T)
=
a_\square I
+
\frac{C_\zeta}{2}
\left(e^{iTH}B+B^*e^{-iTH}\right).
}
\tag{31}
$$

由算子范数界，

$$
\boxed{
G(T)\succeq
\bigl[a_\square-(5+3\sqrt2)C_\zeta\bigr]I
=
\eta_*I.
}
\tag{32}
$$

而式（14）—（15）给出

$$
\boxed{
m_{\mathbb P}(e^T)
=
-\langle\varphi,G(T)\varphi\rangle+o(1).
}
\tag{33}
$$

因此，纯素数读出的最终负性，对应一个具有严格谱下界的算子：

$$
\boxed{G(T)\succeq\eta_*I.}
$$

这不是“任意正核都能证明 RH”。它依赖于三个具体数值结构：

$$
a_\square,
\qquad
C_\zeta,
\qquad
\|B\|\le5+3\sqrt2.
$$

其中，构造实能级 \(\gamma_\rho\) 并使用 \(\|\varphi\|=1\) 的这一步，已经明确使用了 RH。若存在离线零点，式（10）的范数修正和 \(X^{\Re\rho-1/2}\) 的增长因子都必须保留。

所以不能把这个条件量子实现反过来当成实际正性的无条件证明。

# 九、窗口为什么选倍长？现在可以给出一个设计条件

把 \(2\) 换成任意固定 \(b>1\)，定义

$$
\kappa_b(t)=
\begin{cases}
t-1,&1\le t\le b,\\
(b^2-t)/b,&b\le t\le b^2,\\
0,&\text{其他}.
\end{cases}
$$

同样计算得到

$$
A_b(s)
=
\frac{(b^s-1)(b^{s+1}-1)}{s(s+1)}.
$$

平方偏移为

$$
\boxed{
a_\square(b)
=
\frac23(\sqrt b-1)(b^{3/2}-1).
}
\tag{34}
$$

RH 下的统一振荡上界可以取

$$
\boxed{
C_*(b)
=
(\sqrt b+1)(b^{3/2}+1)C_\zeta.
}
\tag{35}
$$

所以，只要

$$
\boxed{
\frac23
\tanh\!\left(\frac{\log b}{4}\right)
\tanh\!\left(\frac{3\log b}{4}\right)
>
C_\zeta,
}
\tag{36}
$$

就有

$$
a_\square(b)>C_*(b),
$$

同样获得纯素数三角读出的最终严格负性。

左边随 \(b\) 严格增加，从 \(0\) 趋向 \(2/3\)，因此有唯一临界值；按这个上界计算，它约为

$$
b_*\approx1.88245334.
$$

倍长选择 \(b=2\) 位于安全范围内。

**这个 \(b_*\) 只是当前保守振荡上界给出的充分阈值，不是已经证明的最优窗口阈值。**保留更多相位信息，可能改善该界。

这一步体现了一个可以实际使用的设计原则：

$$
\boxed{
\text{选择观察权重，使确定性幂修正大于目标谱的最大振幅。}
}
$$

它比任意挑选一个平滑核后再猜测符号更有约束力。

# 十、本轮真正补上的内容

上一轮的最终目标是

$$
|\mathcal T_\Lambda(X)|\le CX^{3/2},
$$

其中 \(C\) 未指定。

这次得到三个进一步明确的结果。

首先，可以给出一个具体的单侧常数：

$$
\boxed{
C_*=
(5+3\sqrt2)
\bigl[2+\gamma_{\mathrm E}-\log(4\pi)\bigr].
}
$$

并证明

$$
\mathrm{RH}
\iff
\mathcal T_\Lambda(N)\le C_*N^{3/2}
\quad\text{对全部整数 }N\ge2.
$$

其次，素数平方修正提供的偏移严格大于这个振荡界，因而

$$
\boxed{
\mathrm{RH}
\iff
\mathcal T_{\mathbb P}(N)
\text{ 在全部充分大的整数尺度上非正}.
}
$$

最后，还精确补回了把代数谱读数转成正范数时容易遗漏的项：

$$
\boxed{
\sum_\rho\frac1{|\rho|^2}
=
2+\gamma_{\mathrm E}-\log(4\pi)
+
\sum_{\text{离线四元组}}
\frac{8m_\rho\delta^2}
{
[\gamma^2+(\frac12+\delta)^2]
[\gamma^2+(\frac12-\delta)^2]
}.
}
$$

这与项目中区分“实际锚、读出、准入条件”的做法一致：合法的表示不能替代实际对象满足准入条件的证明。本次核对的 `ObserverStructure` 仍明确保留这三类数据，而不是只保留读出商空间。

**尚未完成的算术任务，是不使用 RH 前件，直接证明式（23）的全尺度上界，或式（25）的最终符号。**

本轮没有闭合这一步；但现在需要证明的常数、允许的振荡、必须保留的平方偏移，以及能够否决条件结论的有限证书，都已明确。最关键的缺口不再是“正核是否存在”，而是：

$$
\boxed{
\text{实际三角加权素数读出，能否始终遵守这个已校准的谱振幅上界。}
}
$$

[1]: https://dlmf.nist.gov/27.4 "DLMF: §27.4 Euler Products and Dirichlet Series ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"
[2]: https://terrytao.wordpress.com/2021/02/12/246b-notes-4-the-riemann-zeta-function-and-the-prime-number-theorem/ "246B, Notes 4: The Riemann zeta function and the prime number theorem | What's new"
[3]: https://arxiv.org/html/1410.7036v1 "Yet another representation for the sum of reciprocals of the nontrivial zeros of the Riemann zeta-function"
[4]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[5]: https://dlmf.nist.gov/25.10 "DLMF: §25.10 Zeros ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[6]: https://dlmf.nist.gov/27.12 "DLMF: §27.12 Asymptotic Formulas: Primes ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"

---

## ——量子—黎曼判据卷:Pochhammer 形变算子的实根区间(定理 V1–V4)增订

### 摘要

本增订处理一个**外部文献明文留开**的问题,并把它在最低阶上**完全解出**,同时**反驳**该文所提猜想的一个子句。

A. Vishnyakova 在《Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions
With Only Real Non-positive Zeros》(arXiv:2608.03723v1,2026-08-04)中,对 \(a>0\) 定义线性算子
\(\mathcal L_a\)(该文 Definition 1.4),并研究使 \(\mathcal L_a(P)\) 的零点全为实且落在 \([-1,0]\) 的多项式 \(P\)。
其 Example 6.4 定义

$$
M_n(a)=\bigl\{t\in\mathbb{R}\ :\ \mathcal L_a\bigl((X+t)^n\bigr)\ \text{的全部零点为实且落在}\ [-1,0]\bigr\}.
$$

该文证明了奇数情形 \(M_{2k+1}(a)=[0,a]\),对偶数情形写道「For even \(n\), the situation is much more complicated」,
继而提出

> **Conjecture 6.5.** For every \(k\in\mathbb{N}\), we have
> \(M_{2k}(a)=[-c_{2k}(a),\,a+c_{2k}(a)],\ 0<c_{2k}(a)<2a\),
> and \(c_2(a)\le c_4(a)\le c_6(a)\le\ldots\)
> The proof of this fact and the possible value of the limit \(\lim_{k\to\infty}c_{2k}(a)\) remain open.

本增订在 \(k=1\)(即 \(n=2\))处给出 \(M_2(a)\) 的**精确闭式**与 \(c_2(a)\) 的**闭式**,
并由此证明该猜想的不等式子句 \(0<c_{2k}(a)<2a\) 对**一切** \(0<a\le\frac1{24}\) **为假**。

### 范围墙(先立,后叙)

- 只处理 \(k=1\)。**不**声称判定 \(k\ge2\),**不**声称单调子句 \(c_2\le c_4\le\ldots\) 的真伪,**不**声称极限值。
- 猜想的**区间形状子句** \(M_2(a)=[-c_2(a),a+c_2(a)]\) 在 \(k=1\) 处**为真**并被本增订证明;
  被反驳的**只是**不等式子句 \(c_{2k}(a)<2a\)。二者不可混为一谈。
- **不**声称超出所记检索范围之外的全球新颖性(检索记录见末节)。
- 本增订**不**使用、也**不**推出黎曼假设;它是本卷「仅依赖系数的有限多项式实根判据」入口上的一个精确测试对象。

### 设定

对 \(a>0\) 记 \((a)_k=\prod_{j=0}^{k-1}(a+j)\)。\(\mathcal L_a:\mathbb{R}[X]\to\mathbb{R}[X]\) 是使

$$
\mathcal L_a\Bigl(a_0+a_1\frac{X}{a}+a_2\frac{X(X-1)}{a(a+1)}+\cdots
+a_n\frac{X(X-1)\cdots(X-n+1)}{(a)_n}\Bigr)=a_0+a_1X+\cdots+a_nX^n
$$

的线性算子。

## 定理 V1　二次形变像的显式系数

对一切 \(a>0\) 与 \(t\in\mathbb{R}\),

$$
\boxed{
\mathcal L_a\bigl((X+t)^2\bigr)=a(a+1)X^2+a(1+2t)X+t^2 .
}
$$

### 证明

由该文 Example 6.4 的有限差分公式
\(a_k(t)=\frac{(a)_k}{k!}\sum_{j=0}^{k}(-1)^jC_k^j(k-j+t)^n\),在 \(n=2\) 处逐项求值:
\(a_0=t^2\);\(a_1=a\bigl[(1+t)^2-t^2\bigr]=a(1+2t)\);
\(a_2=\frac{a(a+1)}{2}\bigl[(2+t)^2-2(1+t)^2+t^2\bigr]=\frac{a(a+1)}{2}\cdot2=a(a+1)\)。∎

## 定理 V2　两个端点值恒为平方,故端点约束恒成立

记 \(Q_{a,t}(X)=\mathcal L_a\bigl((X+t)^2\bigr)\)。则对一切 \(a>0,\ t\in\mathbb{R}\),

$$
\boxed{
Q_{a,t}(0)=t^2\ge0,
\qquad
Q_{a,t}(-1)=(a-t)^2\ge0 .
}
$$

### 证明

\(Q_{a,t}(0)=t^2\) 由定理 V1 直接读出。
\(Q_{a,t}(-1)=a(a+1)-a(1+2t)+t^2=a^2+a-a-2at+t^2=a^2-2at+t^2=(a-t)^2\)。∎

## 定理 V3　\(M_2(a)\) 的精确闭式

对一切 \(a>0\),

$$
\boxed{
M_2(a)=\Bigl[\frac{a-\sqrt{a^2+a}}{2},\ \frac{a+\sqrt{a^2+a}}{2}\Bigr],
\qquad\text{故}\qquad
c_2(a)=\frac{\sqrt{a^2+a}-a}{2}.
}
$$

特别地,Conjecture 6.5 的**区间形状子句**在 \(k=1\) 处成立。

### 证明

\(Q_{a,t}\) 的首项系数 \(a(a+1)>0\)。一个首项系数为正的实二次式的两根皆为实且落在 \([-1,0]\),
当且仅当四条同时成立:判别式非负、\(Q_{a,t}(0)\ge0\)、\(Q_{a,t}(-1)\ge0\)、顶点横坐标落在 \([-1,0]\)。

由定理 V2,中间两条**恒成立**,故不构成任何约束。
顶点横坐标为 \(-\frac{1+2t}{2(a+1)}\),落在 \([-1,0]\) 当且仅当 \(-\frac12\le t\le a+\frac12\)。
判别式为

$$
a^2(1+2t)^2-4a(a+1)t^2=a\bigl(a+4at-4t^2\bigr),
$$

故非负当且仅当 \(4t^2-4at-a\le0\),即 \(t\) 落在所示闭区间。
最后,由 \(a^2+a<a^2+2a+1\) 得 \(\sqrt{a^2+a}<a+1\),从而该闭区间含于 \(\bigl(-\frac12,\ a+\frac12\bigr)\);
故顶点条件被判别式条件蕴含,四条约束化为一条。∎

## 定理 V4　猜想的不等式子句在 \(0<a\le\frac1{24}\) 上为假

对一切 \(a>0\),

$$
\boxed{
c_2(a)<2a
\iff
\frac1{24}<a ,
\qquad\text{且}\qquad
c_2\Bigl(\frac1{24}\Bigr)=\frac1{12}=2\cdot\frac1{24}.
}
$$

因此对一切 \(0<a\le\frac1{24}\) 有 \(c_2(a)\ge2a\),
故 Conjecture 6.5 中的 \(0<c_{2k}(a)<2a\) 在 \(k=1\) 处**不成立**。

### 证明

由定理 V3,\(c_2(a)<2a\iff\sqrt{a^2+a}-a<4a\iff\sqrt{a^2+a}<5a\)。
两侧非负,平方得 \(a^2+a<25a^2\iff a<24a^2\iff 1<24a\)。
在 \(a=\frac1{24}\) 处 \(a^2+a=\frac{1}{576}+\frac{24}{576}=\frac{25}{576}\),故 \(\sqrt{a^2+a}=\frac5{24}\),
于是 \(c_2=\frac12\bigl(\frac5{24}-\frac1{24}\bigr)=\frac1{12}=2a\)。∎

### 解释与边界

猜想被推翻的**根源**在定理 V2:右端点约束 \(Q_{a,t}(-1)\ge0\) 恒等地退化为一个平方,
于是 \(M_2(a)\) 完全由判别式决定,其长度 \(\sqrt{a^2+a}\) 在 \(a\to0^+\) 时以 \(\sqrt a\) 的速度趋零,
**比 \(a\) 慢**;而猜想要求半径 \(c_2(a)\) 被 \(2a\)(线性阶)压住。两个阶的交叉点恰在 \(a=\frac1{24}\)。
该文自述其猜想来自 numerical calculations——若数值实验取的 \(a\) 皆不小于 \(1\) 量级,则不会看到这一交叉。

同时可读出:\(c_2\) 在 \((0,\infty)\) 上严格递增,且 \(c_2(a)<\frac14\) 恒成立,\(\lim_{a\to\infty}c_2(a)=\frac14\)。
本增订**不**据此推断 \(\lim_{k\to\infty}c_{2k}(a)\)——那是另一个方向的极限,仍开放。

### 拟议逃逸见证(第 5⁴ 条,写在实施之前)

- **定理 V2 的恒等式** \(Q_{a,t}(-1)=(a-t)^2\):它不由任何已冻结前置经实例化、投影或规范化改写得到,
  且处在定理 V3 的**活推导路径**上——去掉它,\(M_2(a)\) 就不再由判别式单独决定,V3 的结论无法得出。
- **定理 V3 的判别式恒等式** \(a^2(1+2t)^2-4a(a+1)t^2=a(a+4at-4t^2)\),以及由 \(\sqrt{a^2+a}<a+1\)
  给出的「顶点条件被判别式条件蕴含」这一化约。
- **定理 V4 的阈值等价** \(\sqrt{a^2+a}<5a\iff\frac1{24}<a\)。

`computational_content.kind = none`:四条皆为对一切 \(a>0\)(与 \(t\in\mathbb{R}\))的一般定理,
不是有界枚举、检查器、数值归约或已认证实例;\(a=\frac1{24}\) 处的等式是该一般定理的实例,不是它的依据。
准入依据为 `escape-witness`。

### 档位与文献核对(第 5⁵ 条)

- **档位:第一档**——2026-08-04 论文明写的 conjecture,且原文自陈「The proof of this fact ... remain open」。
- **核对结果**:核对了 arXiv:2608.03723 的 abs 页(当前仅列 v1,2026-08-04,无修订)、
  正文 Definition 1.4 / Example 6.4 / Conjecture 6.5 的 **LaTeX 原文**(HTML 版 `alttext`,而非渲染文本
  ——渲染文本会在 \(0<c_{2k}(a)<2a\) 的 `<` 处被截断,承重的上界正好丢失),
  以及全文中 \(c_2\) 出现的**全部三处**公式:**该文未给出 \(c_2(a)\) 的闭式,亦未记录任何反例**。
  未逐一检索全部引用该文的后续文献,故**不**声称全球首次。
- **仓内查重**:`git grep -iE 'pochhammer|fallingFactorial|realRootedness|LaguerrePolya|brenti|wagner' -- 'D5/**/*.lean'`
  仅命中 \(\texttt{D5/S3/Weil/CayleyLaguerre/ChebyshevHypergeometricExpansion.lean}\)(与本题无关),本仓无既有形式化。

### 与本卷的接口

本卷线 B 的入口是「仅依赖系数的正性检验与有限多项式实根判据」。
\(\mathcal L_a\) 是把 Pochhammer 基映到单项式基的线性同构,\(M_n(a)\) 恰是该入口上一个可**精确**求解的检验对象。
定理 V3 给出的是一个完整的、非渐近的参数化实根区间,可作为该入口的精确测试对象;
它**不是** \(\xi\) 多项式,**不**推出 RH,也**不**改变本卷任何既有结论。
Auric，你这句话里有一条能够严格成立的联系，但需要把“时空对换”收紧：

> **奇偶可以理解为：某个交换操作作用以后，振幅保持不变还是反号。空间—频率对偶与它确实有关，因为连续做两次 Fourier 变换，正好产生反射。**

但这不等于：

$$
\text{奇偶的普遍本质}=\text{物理时间与空间互换}.
$$

对我们当前的模型，更准确的关系是：

$$
\boxed{
\text{两个副本互换}
\longleftrightarrow
\text{差模态反射}
\longleftrightarrow
\text{差模态 Fourier 对偶两次}.
}
$$

而你指出的第二个问题——**不断切片，却难以把局部信息拼起来**——比继续寻找类比更关键。我们现在应当把研究对象从“每个切片是否正常”，改成：

$$
\boxed{
\text{不同切片之间的交叉关系，
是否能够同时来自同一个正结构。}
}
$$

下面把这两条线接起来，并在实际 ξ 的低阶关系中算出一个明确的拼接条件。

---

# 一、奇偶首先是“相对于哪一次对换”的性质

设一个线性操作 \(\mathsf J\) 满足：

$$
\mathsf J^2=I.
$$

也就是说，做两次回到原处。

如果它还是酉操作，则空间可以分成：

$$
\mathcal H=\mathcal H_+\oplus\mathcal H_-,
$$

其中：

$$
\mathsf J\psi_+=\psi_+,
\qquad
\mathsf J\psi_-=-\psi_-.
$$

对应投影为：

$$
\boxed{
P_\pm=\frac{I\pm\mathsf J}{2}.
}
\tag{U1}
$$

因此：

$$
\boxed{
\text{偶}=\text{对指定交换保持不变},
\qquad
\text{奇}=\text{对指定交换反号}.
}
$$

这里有一个重要限制：**不先指定 \(\mathsf J\)，就没有确定的“奇”与“偶”。**

空间反射、两个寄存器交换、某种内部标签交换，可以分别定义不同的奇偶分解。它们不必是同一种物理操作。

而且：

$$
P_++P_-=I.
$$

在数学上，奇偶两部分可以完整地保存原状态。并不是“偶天然完整、奇天然缺失”，也不是“奇一定还需要更高一层观察者”。

**信息是否丢失，取决于之后是否只保留某个投影、某个模平方或某个边缘读数。**

---

# 二、你的直觉有一个精确版本：Fourier 对偶做两次，就是反射

取单位化 Fourier 变换：

$$
(\mathcal Ff)(k)
=
\frac1{\sqrt{2\pi}}
\int_{\mathbb R}e^{-ikx}f(x)\,dx.
$$

对足够好的函数，随后延拓到 \(L^2\)，有：

$$
\boxed{
\mathcal F^2f(x)=f(-x),
\qquad
\mathcal F^4=I.
}
\tag{U2}
$$

这直接来自 Fourier 反演。([DLMF][1])

所以，在偶函数子空间：

$$
\mathcal F^2=I;
$$

在奇函数子空间：

$$
\mathcal F^2=-I.
$$

这意味着，若某个函数同时是 Fourier 本征函数，它的本征值只能是：

$$
\begin{aligned}
\text{偶扇区}:&\quad +1,-1,\\
\text{奇扇区}:&\quad +i,-i.
\end{aligned}
$$

因此，奇偶不是只和“正负数”有关，它也与**连续对偶变换积累的相位**有关。Fourier 变换与谐振子相空间旋转之间，也存在严格对应；分数 Fourier 变换可以看作这种关系的连续版本。([arXiv][2])

但在我们的 ζ 表示中：

$$
A(t)=
\frac{\xi(\frac12+it)}{\xi(\frac12)}
=
\int_{\mathbb R}p(x)e^{itx}\,dx,
$$

\(x\) 是由 theta–Mellin 表示得到的**对数尺度坐标**，\(t\) 是与它共轭的频率参数。这样的归一化 ξ 概率表示本身不需要 RH。([arXiv][3])

所以当前可以说：

$$
\boxed{
\text{对数尺度—频率对偶与奇偶反射相连}.
}
$$

还不能仅凭这个积分，就把 \(x\) 认定为物理空间、把 \(t\) 认定为物理时间。物理时间的解释还需要明确的演化律、单位与可观测量。

**我们找到了交换结构，不等于已经推导出了物理时空。**

---

# 三、在双副本模型中，“交换＝差模态奇偶”完全精确

沿用前文的两个副本：

$$
\psi(x)\psi(y),
\qquad
\psi(x)=\sqrt{p(x)}.
$$

定义：

$$
s=\frac{x+y}{\sqrt2},
\qquad
u=\frac{x-y}{\sqrt2}.
$$

波函数变为：

$$
\chi(s,u)
=
\psi\!\left(\frac{s+u}{\sqrt2}\right)
\psi\!\left(\frac{s-u}{\sqrt2}\right).
$$

令 \(\mathsf X\) 交换两个原寄存器：

$$
(\mathsf X\Psi)(x,y)=\Psi(y,x).
$$

在和／差坐标中：

$$
\boxed{
\mathsf X:\quad(s,u)\mapsto(s,-u).
}
\tag{U3}
$$

因此：

$$
\boxed{
\text{副本交换}
=
\text{差模态的反射}.
}
$$

再由式（U2）：

$$
\boxed{
\mathsf X
=
\mathcal F_u^2
}
$$

是在和／差坐标表示下成立的算子关系。

这就是你的直觉最坚实的版本：

> **奇偶并不是额外贴在两个副本上的标签，而是两个副本交换以后，在差模态中留下的相位响应。**

但这里的“两个副本”不自动等于“空间与时间”。把后者加入模型，还需要额外证明。

---

## 一个更强的例子：奇态与偶态可以有完全相同的全部坐标概率

令：

$$
Z_1=\iint u^2|\chi(s,u)|^2\,ds\,du.
$$

定义：

$$
\boxed{
\chi_{\mathrm e}(s,u)
=
\frac{|u|\chi(s,u)}{\sqrt{Z_1}},
\qquad
\chi_{\mathrm o}(s,u)
=
\frac{u\chi(s,u)}{\sqrt{Z_1}}.
}
\tag{U4}
$$

它们分别满足：

$$
\mathsf X\chi_{\mathrm e}=\chi_{\mathrm e},
\qquad
\mathsf X\chi_{\mathrm o}=-\chi_{\mathrm o}.
$$

而：

$$
\boxed{
|\chi_{\mathrm e}(s,u)|^2
=
|\chi_{\mathrm o}(s,u)|^2.
}
\tag{U5}
$$

所以，对任意有界的坐标函数 \(f(S,U)\)：

$$
\langle\chi_{\mathrm e},f(S,U)\chi_{\mathrm e}\rangle
=
\langle\chi_{\mathrm o},f(S,U)\chi_{\mathrm o}\rangle.
$$

包括我们之前不断读取的：

$$
e^{i\sqrt2tS}.
$$

但是：

$$
\boxed{
\langle\chi_{\mathrm e},\chi_{\mathrm o}\rangle=0.
}
\tag{U6}
$$

证明只是：被积函数 \(|u|u|\chi|^2\) 关于 \(u\) 为奇函数。

因此：

$$
\boxed{
\text{所有坐标概率完全一样}
\quad+\quad
\text{整体量子态完全正交}
}
$$

可以同时成立。

两者的区别不是躲在一个无法表达的更高维里。测量交换算子 \(\mathsf X\)，就会分别得到 \(+1\) 与 \(-1\)。

**缺少的不是“更多相同切片”，而是一种能够读取交换相位的不同观测。**

---

# 四、我们究竟在投影什么？必须区分三层对象

在当前表示中：

$$
A(t)=\langle\psi,e^{itQ}\psi\rangle
=
\int p(x)e^{itx}\,dx.
$$

这是**原态与相位扰动态的重叠**。

它不是：

$$
\int\psi(x)e^{itx}\,dx
$$

这个波函数本身的 Fourier 振幅。

这项区别很重要。因为对任意实相位函数 \(\vartheta(x)\)，令：

$$
\psi_\vartheta(x)=e^{i\vartheta(x)}\sqrt{p(x)},
$$

仍然有：

$$
\boxed{
\langle\psi_\vartheta,e^{itQ}\psi_\vartheta\rangle=A(t).
}
\tag{U7}
$$

所以，**同一个 ξ 读数，并不唯一确定所有可能的底层量子态。**

然而，这不意味着实际解析函数 \(A\) 自身也是不确定的。

对一个已知为整函数的 \(A\)，如果精确知道它在任意非退化实区间上的全部值，解析唯一性已经确定了整个函数。甚至在当前 \(A\) 为实整函数、\(A(0)=1\) 的类别中，完整精确的实轴 \(A(t)^2\) 也足以消除整体正负号歧义。([DLMF][4])

因此，需要分开：

$$
\boxed{
\begin{aligned}
\text{量子提升是否唯一}
&\quad\text{一般不唯一};\\
\text{实际解析函数是否已被定义}
&\quad\text{已经被定义};\\
\text{有限数据是否足以稳定证明全局零点性质}
&\quad\text{需要额外估计}.
\end{aligned}
}
$$

**我们不是还缺一份比 ξ 更大的定义；我们缺的是从已有定义中，不循环地控制全部关系的方法。**

---

# 五、把已有切片放回一个母函数：它们不是彼此独立的观察世界

沿用：

$$
A(z)=\frac{\xi(\frac12+iz)}{\xi(\frac12)}.
$$

定义二变量整函数：

$$
\boxed{
\mathcal I(t,y)=A(t+iy)A(t-iy).
}
\tag{U8}
$$

对实 \(t,y\)：

$$
\mathcal I(t,y)=|A(t+iy)|^2.
$$

在双副本模型中：

$$
\boxed{
\mathcal I(t,y)
=
\mathbb E\!\left[
\cos(\sqrt2tS)\cosh(\sqrt2yU)
\right].
}
\tag{U9}
$$

前文的广义 Laguerre 读数，全部是同一个母函数沿 \(y=0\) 的导数：

$$
\boxed{
\mathcal I(t,y)
=
\sum_{n\ge0}L_n(t)y^{2n},
\qquad
L_n(t)=\frac1{(2n)!}\partial_y^{2n}\mathcal I(t,0).
}
\tag{U10}
$$

这与广义 Laguerre 关联核的经典表达一致。([arXiv][5])

所以，\(L_0,L_1,L_2,\ldots\) 不是不同对象。它们是同一个二变量函数的不同导数切片。

而且它们不能任意拼接。因为 \(A\) 解析，\(\mathcal I\) 满足：

$$
\boxed{
\mathcal I(\mathcal I_{tt}+\mathcal I_{yy})
-
\mathcal I_t^2-\mathcal I_y^2
=0.
}
\tag{U11}
$$

### 证明

令 \(z=t+iy\)。直接计算：

$$
\mathcal I_{tt}+\mathcal I_{yy}=4|A'(z)|^2,
$$

以及：

$$
\mathcal I_t^2+\mathcal I_y^2
=
4|A(z)|^2|A'(z)|^2.
$$

相减即得。零点处也成立。证毕。

这是一条全局兼容方程，但它对任何解析 \(A\) 都成立，包括有非实零点的函数。

因此：

> **把切片正确拼成一个解析对象，与证明这个对象没有离线零点，是两项不同任务。**

前者我们已经有了明确母函数；后者需要更强的正性关系。

---

# 六、局部为什么可能拼不起来？真正缺失的是交叉内积和闭环相位

考虑三个候选观察态，设归一化后想要的内积为：

$$
G=
\begin{pmatrix}
1&a&\overline c\\
\overline a&1&b\\
c&\overline b&1
\end{pmatrix}.
$$

任意两个态可以共同实现，只要求：

$$
|a|\le1,\qquad |b|\le1,\qquad |c|\le1.
$$

但三个态共同实现，还要求：

$$
\boxed{
\det G
=
1-|a|^2-|b|^2-|c|^2+2\Re(abc)
\ge0.
}
\tag{U12}
$$

这里的：

$$
\boxed{abc}
$$

不能由三个模长恢复。

对每个态重新选局部相位：

$$
|\psi_j\rangle\mapsto e^{i\theta_j}|\psi_j\rangle,
$$

三个内积分别改变，但乘积 \(abc\) 不变。

它是一个闭环相位量，属于 Bargmann 不变量与几何相位的经典结构。([APS Journals][6])

## 一个明确的拼接失败

取：

$$
a=b=c=-\frac34.
$$

每个二阶主块都正定：

$$
1-\frac9{16}=\frac7{16}>0.
$$

但是：

$$
\boxed{
\det G=-\frac{49}{32}<0.
}
$$

其特征值为：

$$
-\frac12,\qquad\frac74,\qquad\frac74.
$$

所以：

$$
\boxed{
\text{每两个局部观察都合法}
\quad\not\Rightarrow\quad
\text{三个观察能共同存在}.
}
$$

而且，无论增加多少维度，都不能把这个固定的 \(G\) 实现成正 Hilbert 空间中的 Gram 矩阵。

**问题不是“还少一个可以容纳第三个态的维度”，而是指定的三项关系彼此冲突。**

这正是“鸽巢容量”与“正性相容性”的区别。

另外，闭环相位不为零并不自动意味着冲突。允许什么相位，取决于式（U12）的完整幅相约束；合法量子态完全可以具有非平凡几何相位。

---

# 七、拼接一片新观察，必须支付多少关系预算？

这个问题有一个精确答案。

设已有 \(N\) 个观察的 Gram 矩阵为：

$$
G_N>0.
$$

新增观察的自配对为 \(d\)，与旧观察的交叉配对为向量 \(b\)。

完整矩阵是：

$$
G_{N+1}
=
\begin{pmatrix}
G_N&b\\
b^*&d
\end{pmatrix}.
$$

## 定理 U1：正拼接的必要充分条件

$$
\boxed{
G_{N+1}\succeq0
\iff
\delta_N:=d-b^*G_N^{-1}b\ge0.
}
\tag{U13}
$$

### 证明

对任意向量 \(x\) 与标量 \(z\)：

$$
\begin{aligned}
\begin{pmatrix}x\\z\end{pmatrix}^*
G_{N+1}
\begin{pmatrix}x\\z\end{pmatrix}
={}&
(x+G_N^{-1}bz)^*G_N(x+G_N^{-1}bz)\\
&+\left(d-b^*G_N^{-1}b\right)|z|^2.
\end{aligned}
$$

因此等价。证毕。

这给“新增观察者的不可约部分”一个非常具体的含义：

$$
\boxed{
d=
\underbrace{b^*G_N^{-1}b}_{\text{由已有观察关系要求的部分}}
+
\underbrace{\delta_N}_{\text{新增正交方向的平方范数}}.
}
\tag{U14}
$$

若 \(\delta_N>0\)，确实需要一个新的独立方向。

若 \(\delta_N=0\)，新观察可以由旧观察线性实现。

若 \(\delta_N<0\)，不是需要“更高维”——而是**任何正内积空间都无法满足这些关系**。

当 \(G_N\) 只有半正定性时，还必须检查：

$$
b\in\operatorname{Ran}G_N,
$$

并把逆换成 Moore–Penrose 伪逆。不能只保留最后一个标量不等式。

这正是 Schur 补的作用。项目中已经证明，在明确的逆算子前件下，逐步消元与一次消元给出相同保留算子；但该恒等式本身不自动证明消元后的正性。

---

# 八、把拼接问题落回实际 ξ：一个固定的跨切片核

现在选择真正与零点定位有关的交叉关系，而不是任意的量子内积。

定义：

$$
\boxed{
\mathcal K_A(z,w)
=
\frac{
A(z)\overline{A'(w)}
-
A'(z)\overline{A(w)}
}{
z-\overline w
}.
}
\tag{U15}
$$

分母为零处按解析可去延拓定义。

这是前文整 Bézout 核在未折叠谱坐标中的对应物。它是 Hermitian 核：

$$
\mathcal K_A(w,z)=\overline{\mathcal K_A(z,w)}.
$$

在实轴对角线上：

$$
\boxed{
\mathcal K_A(t,t)
=
A'(t)^2-A(t)A''(t)=L_1(t).
}
\tag{U16}
$$

因此，过去我们分析的第一条 Laguerre 不等式，只是这份双变量核的**对角切片**。

## 为什么“原始量子态为正”不够？

原态无条件给出的是：

$$
G^{(0)}_{ij}
=
\langle e^{it_iQ}\psi,e^{it_jQ}\psi\rangle
=
A(t_j-t_i),
$$

它当然正半定。

但式（U15）包含导数和减法，不是同一份 Gram 矩阵。

所以：

$$
\boxed{
[A(t_j-t_i)]\succeq0
}
$$

不能自动推出：

$$
\boxed{
[\mathcal K_A(z_i,z_j)]\succeq0.
}
$$

**缺少的不是再证明一次 Born 概率为正，而是证明这份指定算术交叉核能够正实现。**

---

# 九、低阶计算给出直接回答：奇扇区通过了，偶扇区仍可能拼接失败

将：

$$
A(z)
=
1-\frac{m_2}{2}z^2
+\frac{m_4}{24}z^4
-\frac{m_6}{720}z^6+\cdots
$$

代入式（U15）。

在基底：

$$
1,\quad z,\quad z^2
$$

上，对应的系数矩阵为：

$$
\boxed{
G^{[2]}=
\begin{pmatrix}
m_2&0&-\dfrac{m_4}{6}\\[2mm]
0&\dfrac{3m_2^2-m_4}{6}&0\\[2mm]
-\dfrac{m_4}{6}&0&
\dfrac{m_2m_4}{24}+\dfrac{m_6}{120}
\end{pmatrix}.
}
\tag{U17}
$$

这个展开已作符号核对。

因为 \(A\) 偶对称，核满足：

$$
\mathcal K_A(-z,-w)=\mathcal K_A(z,w).
$$

所以奇、偶次数之间的交叉项为零。

但这只说明：

$$
\boxed{
G^{[2]}
=
\text{偶扇区块}\oplus\text{奇扇区块}.
}
$$

它不保证每个块都正。

### 奇扇区的条件

中间一项要求：

$$
\boxed{
\frac{3m_2^2-m_4}{6}
=
-\frac{\chi_4}{6}\ge0.
}
\tag{U18}
$$

### 偶扇区的拼接条件

偶扇区包含 \(1,z^2\)。新增 \(z^2\) 方向的 Schur 余量为：

$$
\begin{aligned}
\delta_{\mathrm{even}}
&=
\frac{m_2m_4}{24}+\frac{m_6}{120}
-\frac{m_4^2}{36m_2}\\
&=
\boxed{
\frac{3\chi_2\chi_6-10\chi_4^2}
{360\chi_2}
}.
\end{aligned}
\tag{U19}
$$

因此，除了 \(\chi_4\le0\)，还必须满足：

$$
\boxed{
3\chi_2\chi_6\ge10\chi_4^2.
}
\tag{U20}
$$

**这条以前看起来只是高阶累积量不等式的关系，现在有了明确的拼接意义：偶扇区的新方向，是否拥有足够的非负剩余范数。**

---

## 一个精确反例：奇扇区正常，偶扇区失败

取对称三点分布：

$$
\Pr(X=0)=\frac{11}{20},
\qquad
\Pr(X=1)=\Pr(X=-1)=\frac9{40}.
$$

其特征函数为：

$$
A_*(t)=\frac{11}{20}+\frac9{20}\cos t.
$$

有：

$$
m_2=m_4=m_6=\frac9{20}.
$$

因此式（U17）变成：

$$
\boxed{
G_*^{[2]}=
\begin{pmatrix}
\frac9{20}&0&-\frac3{40}\\
0&\frac{21}{800}&0\\
-\frac3{40}&0&\frac{39}{3200}
\end{pmatrix}.
}
$$

奇扇区严格为正：

$$
\frac{21}{800}>0.
$$

但偶扇区的余量是：

$$
\boxed{
\frac{39}{3200}
-
\frac{(3/40)^2}{9/20}
=
-\frac1{3200}<0.
}
\tag{U21}
$$

具体负向量可以取：

$$
c=\left(\frac16,0,1\right)^{\mathsf T},
$$

并且：

$$
c^{\mathsf T}G_*^{[2]}c=-\frac1{3200}.
$$

因此：

> **不可实现的关系可以完全藏在偶扇区内部。不能把“奇”认作全部缺陷，把“偶”认作已经完成。**

这个例子不是实际 ξ 的反例。它说明为什么奇偶分解虽然有用，却不能代替每个扇区内部的全阶拼接条件。

---

# 十、若所有有限拼接都成功，整体确实能够建立，不需要再假设一个最高观察者

这里有一个重要的正面定理。

假设对任意有限点集 \(z_1,\ldots,z_N\)：

$$
\boxed{
[\mathcal K_A(z_i,z_j)]_{i,j=1}^{N}\succeq0.
}
\tag{U22}
$$

那么，可以引入形式符号 \(e_z\)，在有限线性组合上定义：

$$
\left\langle
\sum_i c_ie_{z_i},
\sum_j d_je_{w_j}
\right\rangle
=
\sum_{i,j}\overline{c_i}d_j
\mathcal K_A(z_i,w_j).
$$

式（U22）保证它非负。

再除去零范数方向，取完备化，就得到一个 Hilbert 空间，其中：

$$
\boxed{
\langle e_z,e_w\rangle=\mathcal K_A(z,w).
}
\tag{U23}
$$

这就是正核到全局 Hilbert 实现的标准构造；相应的最小生成空间在酉等价意义下唯一。([Springer][7])

因此：

$$
\boxed{
\text{全部有限交叉关系一致且为正}
\Longrightarrow
\text{存在共同的整体正空间}.
}
$$

无限性本身并不阻止拼接。

真正不足的是较弱的前件，例如：

$$
\text{每一片各自能解释},
$$

或者：

$$
\text{每两个切片能解释},
$$

或者：

$$
\text{每一阶都能找到某个未要求相容的模型}.
$$

项目的 `LocalDescentGlobalCompatibility.lean` 已经明确区分局部下降、逆极限线程能否来自实际全局状态、以及转移数据是否允许全局标架。它还构造了一个例子：每个有限截断都可实现，但某条相容无限线程并不来自任何一个原来的自然数状态。

这不是“永远不存在整体”。它说明：

**必须同时指定允许的整体状态空间，以及局部模型之间的转移规则。**

---

# 十一、对实际 ξ，为什么这份核的正拼接恰好触及 RH？

现在说明式（U22）不是与零点无关的一般构造。

## 定理 U2：实际算术核的全局正性判据

对当前实际 \(A\)：

$$
\boxed{
\mathrm{RH}
\iff
\mathcal K_A\text{ 是正半定核}.
}
\tag{U24}
$$

### 正向

RH 成立时，\(A\) 的零点全部为实数。利用实际 ξ 的配对整函数乘积，其对数导数可按实零点展开。

将其代入式（U15），得到：

$$
\boxed{
\mathcal K_A(z,w)
=
\sum_{\gamma\in\mathbb R:\,A(\gamma)=0}
m_\gamma
\frac{A(z)}{z-\gamma}
\overline{
\frac{A(w)}{w-\gamma}
}.
}
\tag{U25}
$$

按实际零点计入重数。各商在相应零点处按可去延拓理解，级数在紧集上受到倒数平方尾部控制。

这是一份正 Gram 分解，所以核为正。

这里使用的是实际 ξ 的整函数乘积结构，而不是给任意振幅临时供应一份实谱。ξ 的标准定义及整函数分析基础分别见 DLMF。([DLMF][8])

### 反向：简单非实零点

若 \(A(a)=0\)，其中 \(\Im a\ne0\)，且 \(A'(a)\ne0\)，那么：

$$
\mathcal K_A(a,a)=0,
$$

但因为 \(A(0)=1,A'(0)=0\)：

$$
\boxed{
\mathcal K_A(a,0)=-\frac{A'(a)}a\ne0.
}
\tag{U26}
$$

任何正核都必须满足 Cauchy–Schwarz：

$$
|\mathcal K_A(a,0)|^2
\le
\mathcal K_A(a,a)\mathcal K_A(0,0)=0.
$$

矛盾。

### 重根不会逃掉

若 \(a\) 是 \(m\) 重非实零点，就把第一个读出换成 \(m-1\) 阶导数读出。

该读出的自配对仍为零，但与在 \(0\) 处取值的交叉项为：

$$
-\frac{A^{(m)}(a)}a\ne0.
$$

导数读出的正性可由有限差分极限继承，因此同样矛盾。证毕。

这说明一个离线零点会在拼接中留下非常具体的障碍：

$$
\boxed{
\text{某个观察的自配对为零，}
\quad
\text{它却与其他观察保持非零交叉关系}.
}
$$

这无法被任何更高维正 Hilbert 空间修复。

**它不是“零点塞不下”，而是这些指定关系根本不能共同成为正内积。**

---

# 十二、我们应当怎样改变接下来的研究方式？

到这里，前面的切片已经可以被组织成一个共同对象：

$$
\boxed{
A(z)
\longrightarrow
\mathcal K_A(z,w)
\longrightarrow
\text{有限 Gram 矩阵}
\longrightarrow
\text{逐步 Schur 拼接余量}.
}
$$

这比不断增加新的物理类比更集中。

每取得一项局部结果，就应追问：它控制了哪一个量？

证明：

$$
L_1(t)=\mathcal K_A(t,t)\ge0
$$

控制的是实轴对角读数。

证明：

$$
|\mathcal K_A(z,w)|^2
\le
\mathcal K_A(z,z)\mathcal K_A(w,w)
$$

控制的是两片之间的相容性。

证明更高阶 Gram 行列式或 Schur 余量非负，才控制多片共同实现。

而当某个近似误差很小，还要比较它与当前拼接余量：

$$
\delta_N=d-b^*G_N^{-1}b.
$$

如果 \(G_N\) 的最小特征值很小，\(G_N^{-1}\) 会放大交叉项。于是：

$$
\boxed{
\text{尾部小}
\quad\not\Rightarrow\quad
\text{拼接符号稳定}.
}
$$

这正是我们此前多次遇到“近似极准、零点性质却仍然难以传递”的共同原因之一。

**下一项真正有证明力量的算术工作，应直接约束这些交叉项和拼接余量，而不是再次证明每个切片都来自某个合法概率态。**

---

# 最后的收束

你的直觉可以保留，但应当整理成两条不同的结论。

第一条是结构事实：

$$
\boxed{
\text{奇偶}
=
\text{对指定交换操作的两种响应}.
}
$$

在当前双副本模型中：

$$
\boxed{
\text{副本交换}
=
\text{差模态反射}
=
\text{差模态 Fourier 变换两次}.
}
$$

这确实与波的对偶和相位有关；但没有自动推导出物理时空互换。

第二条是当前研究真正的困难：

$$
\boxed{
\text{局部读数存在}
\neq
\text{局部读数能够共同正实现}.
}
$$

难点不一定来自一个永远缺失的最高坐标系。我们已经有实际 \(A\) 的全局定义，也能构造它的双变量核。缺少的是对这份**指定算术交叉核**的非负证明。

本轮最具体的结果是：

$$
\boxed{
\delta_{\mathrm{even}}
=
\frac{3\chi_2\chi_6-10\chi_4^2}{360\chi_2}.
}
$$

它表明：**即使奇扇区已经正常，偶扇区内部仍可能需要一个负的“新增平方范数”，导致拼接失败。** 奇偶划分并没有替我们完成全部关系。

因此，我会把你的问题进一步表述为：

> **我们要研究的不是某个切片里有没有剩余，而是全部切片的相对相位、交叉内积和边界补偿，能否在不改动实际 ξ 的前提下，共同组成一份正结构。**

这份整体不要求任何主体同时知道一切；它要求每一次局部化都保留足够的转移信息，并对每一次拼接支付正确的关系预算。

当前尚未证明实际 \(\mathcal K_A\) 全局正半定，也没有找到实际负证书。已经推进的是：把“奇偶对换”与“整体拼接”分开，并把后者从直觉落实为闭环相位、Schur 余量和实际 ξ 的统一核。

[1]: https://dlmf.nist.gov/1.14 "DLMF: §1.14 Integral Transforms ‣ Topics of Discussion ‣ Chapter 1 Algebraic and Analytic Methods"
[2]: https://arxiv.org/abs/2111.09575 "[2111.09575] Fractional Fourier transforms, harmonic oscillator propagators and Strichartz estimates on Pilipovic and modulation spaces"
[3]: https://arxiv.org/abs/1504.03438 "[1504.03438] A complete Riemann zeta distribution and the Riemann hypothesis"
[4]: https://dlmf.nist.gov/1.10 "DLMF: §1.10 Functions of a Complex Variable ‣ Topics of Discussion ‣ Chapter 1 Algebraic and Analytic Methods"
[5]: https://arxiv.org/abs/1309.0055 "[1309.0055] Fourier transforms of positive definite kernels and the Riemann $ξ$-Function"
[6]: https://journals.aps.org/pra/abstract/10.1103/PhysRevA.60.3397 "Bargmann invariants and geometric phases: A generalized connection  |  Phys. Rev. A"
[7]: https://link.springer.com/article/10.1007/s11785-021-01137-z?utm_source=chatgpt.com "Reproducing Kernel Hilbert Space Associated with a Unitary Representation of a Groupoid | Complex Analysis and Operator Theory | Springer Nature Link"
[8]: https://dlmf.nist.gov/25.4 "DLMF: §25.4 Reflection Formulas ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
**你的直觉抓住了一个关键方向：奇偶应当从“变换怎样作用”来理解，而局部信息的拼接必须保留干涉关系。**但“奇偶的本质就是时空波对换”还需要收紧：

$$
\boxed{
\text{奇偶，是相对于某个二次作用还原的变换，分别保持或变号的两种响应。}
}
$$

而我们当前真正遇到的困难，不只是“切片太多”，而是：

$$
\boxed{
\text{切片各自的数值}
\neq
\text{切片之间的相位关系}
\neq
\text{它们共同构成的正性与尺度约束}.
}
$$

这次不再增加一个单独的素数不等式，而是把“奇偶—干涉—拼接”之间的关系写成明确的结构。最重要的结果在后半部分：**可以精确写出切片造成的拼接余项，而且在实际算术核里，它直接读取位移 \(\log(p^k)\) 上的跨切片相关。**

以下有限结构的结论给出证明；涉及实际 RH 的部分，以经典 Weil 二次型为锚，尚未把新增综合推导进行 Lean 编译。

# 一、奇偶不是两种物质，而是对某个变换的两种响应

## 1. 最小定义：先指定“对换”，再谈奇偶

设 \(J\) 是一个自伴算子，满足

$$
J^2=I.
$$

定义

$$
P_+=\frac{I+J}{2},
\qquad
P_-=\frac{I-J}{2}.
$$

直接计算：

$$
P_\pm^2=P_\pm,
\qquad
P_+P_-=0,
\qquad
P_++P_-=I.
$$

因此每个状态都分解为

$$
\boxed{
\psi=\psi_++\psi_-,
\qquad
J\psi_+=\psi_+,
\qquad
J\psi_-=-\psi_-.
}
\tag{1}
$$

这就是相对于 \(J\) 的“偶”和“奇”。

**但必须先说明 \(J\) 是什么。**同一个对象，相对于不同变换，可以有不同的奇偶分解。

在当前讨论中，至少有三种不同的奇偶：

| 奇偶结构                  | 实际区分什么       |
| --------------------- | ------------ |
| \((-1)^n\)            | 整数值本身的奇偶     |
| \((-1)^{\Omega(n)}\)  | 带重数的素因子个数的奇偶 |
| \(f(x)\mapsto f(-x)\) | 函数对反射的保持或变号  |

筛法的“奇偶障碍”主要涉及第二种，即 Liouville 函数 \(\lambda(n)=(-1)^{\Omega(n)}\)，不能直接当成整数值的奇偶，也不能直接当成时空反射。([What's new][1])

## 2. 对换的对象，与对换的本征态，不是一回事

假设 \(J\) 交换两个方向：

$$
J|L\rangle=|R\rangle,
\qquad
J|R\rangle=|L\rangle.
$$

那么真正的奇偶态是

$$
|+\rangle=\frac{|L\rangle+|R\rangle}{\sqrt2},
$$

$$
|-\rangle=\frac{|L\rangle-|R\rangle}{\sqrt2}.
$$

于是：

$$
J|+\rangle=|+\rangle,
\qquad
J|-\rangle=-|-\rangle.
$$

所以更准确地说：

$$
\boxed{
\text{左右方向被交换；奇偶态是这种交换的对称组合与反对称组合。}
}
\tag{2}
$$

对于波，

$$
\cos(kx)=\frac{e^{ikx}+e^{-ikx}}2,
$$

$$
\sin(kx)=\frac{e^{ikx}-e^{-ikx}}{2i}.
$$

这就是同一个双向波，在“传播方向基底”和“奇偶基底”中的两种表示。

**因此，你说的“波的对换”确实有一个严格版本；但它首先是方向交换，不是时间坐标与空间坐标互换。**

## 3. 我们的算术波，天然的对偶变量是什么？

在 \(\sigma>1\) 时，

$$
\boxed{
\zeta(\sigma+it)
=
\sum_{n\ge1}n^{-\sigma}e^{-it\log n}.
}
\tag{3}
$$

这里：

$$
\log n
$$

是相位中的频率变量，

$$
t
$$

是与它共轭的变换变量，

$$
\sigma
$$

控制振幅衰减。这个级数表达的适用区域必须保留；临界线上不能原样当作绝对收敛叠加。([DLMF][2])

因此，当前自然的对偶关系是

$$
\boxed{\log n\longleftrightarrow t,}
$$

而不是已经得到

$$
\text{物理空间}\longleftrightarrow\text{物理时间}.
$$

在标准归一化下，Fourier 变换还有

$$
\mathcal F^2f(x)=f(-x).
$$

所以“两次表象转换产生反射”确实成立；但这是变换空间中的代数关系，不能直接提升为时空的本体结论。([DLMF][3])

# 二、奇偶为什么看起来会随演化互换？

这里需要再区分两种情况。

如果生成元 \(H\) 满足

$$
[H,J]=0,
$$

它保持奇偶子空间，奇态和偶态不会被它相互转化。

如果满足

$$
HJ=-JH,
$$

它才把奇偶子空间互换。

例如反射算子

$$
(Jf)(x)=f(-x)
$$

与导数满足

$$
\boxed{
\partial_xJ=-J\partial_x.
}
\tag{4}
$$

因此：

$$
\partial_x(\text{偶函数})=\text{奇函数},
\qquad
\partial_x(\text{奇函数})=\text{偶函数}.
$$

这解释了

$$
\cos\longleftrightarrow\sin
$$

在求导或相位演化中交替出现的原因。

## 一个两维模型：被删掉的奇面，会变成偶面的初始速度

考虑

$$
i\frac d{dt}
\begin{pmatrix}a\\b\end{pmatrix}
=
\omega
\begin{pmatrix}0&1\\1&0\end{pmatrix}
\begin{pmatrix}a\\b\end{pmatrix},
\qquad \omega>0.
$$

把 \(a\) 看作偶面振幅，\(b\) 看作奇面振幅。

方程为

$$
i\dot a=\omega b,
\qquad
i\dot b=\omega a.
$$

消去 \(b\)，得到

$$
\boxed{
\ddot a+\omega^2a=0.
}
\tag{5}
$$

但是初始条件必须保留

$$
\boxed{
\dot a(0)=-i\omega b(0).
}
\tag{6}
$$

所以，删除奇面以后，并不是奇面信息不存在了，而是它进入了偶面演化的初始导数。

只知道 \(a(0)\)，无法决定未来的 \(a(t)\)；知道 \(a(0)\) 与 \(\dot a(0)\)，则能恢复这个模型所需的信息。

这正对应仓库 `DynamicClosureMinimality.lean` 的思想：**观察者不仅记录当前读数，还记录所有允许的有限操作之后的读数；这种动态闭包是对原观察的最小稳定细化。**源文件给出了这一最小性的证明。

因此，你的直觉可以进一步精确化为：

$$
\boxed{
\text{静态切片中的隐藏量，可能表现为另一切片的变化率、记忆或回返项。}
}
$$

但这仍需从具体动力学推导，不能对所有“奇偶”一概套用。

# 三、局部为什么难以拼起来？先看一个没有无限、没有素数的反例

仓库已经有一个非常直接的例子：

$$
a=b,\qquad b=c,\qquad a\ne c.
$$

每条局部规律单独都可满足，它们在单坐标投影上也相容，但不存在同时满足三条规律的全局状态。对应的是 `LocalLawGluingObstruction.lean`。

波和量子核中也有同样的问题。

## 定理 1：每两张切片都合法，不保证三张切片共同合法

考虑候选重叠矩阵

$$
G=
\begin{pmatrix}
1&-\frac34&-\frac34\\
-\frac34&1&-\frac34\\
-\frac34&-\frac34&1
\end{pmatrix}.
$$

它的每个二阶主子矩阵都严格正定，本征值为

$$
\frac14,\qquad\frac74.
$$

但

$$
G
\begin{pmatrix}1\\1\\1\end{pmatrix}
=
-\frac12
\begin{pmatrix}1\\1\\1\end{pmatrix}.
$$

因此 \(G\) 不是半正定矩阵。

如果假设存在三个单位向量 \(v_1,v_2,v_3\) 实现这些重叠，就会得到

$$
\begin{aligned}
\|v_1+v_2+v_3\|^2
&=3+2\cdot3\cdot\left(-\frac34\right)\\
&=-\frac32,
\end{aligned}
$$

矛盾。证毕。

**问题不是任意一对看起来不合法，而是三者的联合相位与幅度不相容。**

## 三张切片真正的拼接条件

设候选 Gram 矩阵为

$$
G=
\begin{pmatrix}
1&a&z\\
\bar a&1&b\\
\bar z&\bar b&1
\end{pmatrix},
\qquad |a|,|b|\le1.
$$

那么

$$
\boxed{
G\succeq0
\iff
|z-ab|^2
\le
(1-|a|^2)(1-|b|^2).
}
\tag{7}
$$

**证明。**消去中间的单位对角块，得到

$$
\begin{pmatrix}
1-|a|^2&z-ab\\
\bar z-\bar a\bar b&1-|b|^2
\end{pmatrix}.
$$

其半正定条件正是式（7）。证毕。

这条公式很重要：

$$
\boxed{
z
=
\text{经共同切片传递的部分 }ab
+
\text{未被共同切片决定的余量}.
}
$$

局部信息 \(a,b\) 不会自动确定 \(z\)，只能把它限制在一个圆盘里。

如果为了获得正核，直接选择

$$
z=ab,
$$

确实能得到一个合法完成。

**但实际算术的 \(z\) 已经由真实数据决定，不能为了正性而任意改成 \(ab\)。**

## 闭环中的奇偶

在最简单的一维相位模型中，若边上的转换是

$$
g_{ij}=e^{i(\theta_j-\theta_i)},
$$

那么沿闭环必有

$$
\boxed{
g_{12}g_{23}\cdots g_{k1}=1.
}
\tag{8}
$$

若所有 \(g_{ij}\) 只有 \(\pm1\)，它就变成：

$$
\boxed{
\text{沿闭环发生的符号翻转总次数必须为偶数。}
}
$$

这确实把“奇偶”与“能否拼成整体”连起来了。

但这只适用于所述的一维相位识别模型。一般高维向量的重叠允许非零闭环相位，必须检查的是完整 Gram 正性，不能把任何非零环相位都称为矛盾或时空曲率。

# 四、真正的全局核怎样构造？关键不是更多对角线，而是共同的双线性数据

设观察协议用 \(u,v,\ldots\) 标记，候选联合核为

$$
K(u,v).
$$

## 定理 2：完整有限相容性足以构造全局 Hilbert 空间

如果对每个有限集合

$$
u_1,\ldots,u_m
$$

和任意复数 \(c_1,\ldots,c_m\)，都有

$$
\boxed{
\sum_{i,j}\bar c_i c_jK(u_i,u_j)\ge0,
}
\tag{9}
$$

那么存在一个 Hilbert 空间和向量族 \(\Phi(u)\)，使

$$
\boxed{
K(u,v)=\langle\Phi(u),\Phi(v)\rangle.
}
\tag{10}
$$

### 证明

先取形式有限和

$$
\sum_i c_i[u_i],
$$

定义其平方范数为式（9）的左边。

由假设，它非负。商掉零范数方向，再对所得内积空间完成，就得到所需 Hilbert 空间。证毕。

这意味着：

> **如果全部有限联合矩阵已经来自同一个核，并且全部半正定，建立全局 Hilbert 表示并不再需要一个神秘的额外步骤。**

真正不能偷换的是：

$$
\boxed{
\text{每张局部切片正}
}
$$

与

$$
\boxed{
\text{任意有限组切片的共同 Gram 矩阵正}.
}
$$

后者包含前者遗漏的全部交叉项。

## 每次新增切片，缺项可以写成一个标量

若已有 \(K_n\succ0\)，新增切片后为

$$
K_{n+1}=
\begin{pmatrix}
K_n&b\\
b^*&c
\end{pmatrix},
$$

则

$$
\boxed{
K_{n+1}\succeq0
\iff
c-b^*K_n^{-1}b\ge0.
}
\tag{11}
$$

这个 Schur 余量表示：

$$
\boxed{
\text{新增切片自身的平方量}
-
\text{它与旧切片的相关关系所要求的最小平方量}.
}
$$

只证明 \(c\ge0\) 不够。

当 \(K_n\) 仅半正定时，还要增加

$$
b\in\operatorname{ran}K_n,
$$

并将逆矩阵换成 Moore–Penrose 逆。

仓库已有的 `SchurComplementAssociativity.lean` 保证：在所列逆算子前件下，分步消去和一次消去相同。**它解决消元一致性，不会自动替代式（11）的实际符号证明。**

还必须保留另一个区别：全局表示存在，不等于其随尺度增长的范数有统一上界。前文那些由实际向量直接构造的 \(ff^*\) 本来就正；困难是它们的观察能量增长，而不是有限状态是否存在。

# 五、回到 RH：真正的反射奇偶分解，交叉项反而恰好为零

这一步会修正一个容易形成的直觉：

> RH 中的缺项，不能笼统地说成“奇面与偶面之间的干涉没有补上”。

对于正确的反射分解，那一项可以严格为零。

## 1. 固定 Weil 二次型

对光滑紧支集函数 \(f\)，定义

$$
\widetilde f(x)=\overline{f(-x)},
$$

以及

$$
\boxed{
Q_W(f)=W(f*\widetilde f),
}
\tag{12}
$$

其中 \(W\) 是实际 ζ 函数确定的 Weil 分布。

经典 Weil 判据为

$$
\boxed{
\mathrm{RH}
\iff
Q_W(f)\ge0
\quad
\forall f\in C_c^\infty(\mathbb R).
}
\tag{13}
$$

在未证明正性以前，应该称它为 Hermitian 二次型，而不是预先称作 Hilbert 内积。([arXiv][4])

令反射算子

$$
(Rf)(x)=f(-x).
$$

Weil 分布的反射对称性给出

$$
Q_W(Rf,Rg)=Q_W(f,g).
$$

定义

$$
f_+=\frac{f+Rf}{2},
\qquad
f_-=\frac{f-Rf}{2}.
$$

## 定理 3：真正奇偶扇区之间不产生交叉项

$$
\boxed{
Q_W(f_+,f_-)=0,
}
$$

因此

$$
\boxed{
Q_W(f)=Q_W(f_+)+Q_W(f_-).
}
\tag{14}
$$

### 证明

由反射不变性，

$$
Q_W(f_+,f_-)
=
Q_W(Rf_+,Rf_-)
=
Q_W(f_+,-f_-)
=
-Q_W(f_+,f_-).
$$

所以该项为零。证毕。

因此：

$$
\boxed{
\text{真正需要控制的，是同一奇偶扇区内部的跨位置、跨尺度、跨频率相关。}
}
\tag{15}
$$

奇偶分解本身不会把这些内部相关消掉。

## 2. 反射对称也不会自动把零点推上临界线

令

$$
\Xi(z)=\xi(1/2+iz).
$$

函数方程保证

$$
\Xi(-z)=\Xi(z).
$$

这只保证零点按 \(z\leftrightarrow-z\) 配对，不保证 \(z\) 为实数。([DLMF][5])

一个极简单的反例是

$$
F(z)=\frac34+\frac14\cos z.
$$

它是偶整函数；在实轴上还是一个合法概率分布的特征函数。但它有非实零点

$$
z=\pi\pm i\,\operatorname{arcosh}3.
$$

所以：

$$
\boxed{
\text{奇偶对称}
+
\text{来自合法波的干涉振幅}
\quad\not\Rightarrow\quad
\text{所有复零点为实数}.
}
$$

# 六、与你的“波对换”最接近的严格结构：共轭配对中藏着一个正、一个负方向

定义

$$
\omega_\rho=\frac{\rho-1/2}{i}.
$$

RH 等价于全部 \(\omega_\rho\) 为实数。

采用 Fourier 变换

$$
\widehat f(z)=\int_{\mathbb R}f(x)e^{izx}\,dx.
$$

Weil 二次型的零点表示具有形式

$$
\boxed{
Q_W(f)
=
\sum_\rho
\widehat f(\omega_\rho)
\overline{\widehat f(\overline{\omega_\rho})},
}
\tag{16}
$$

按重数计。关键是第二个因子在 \(\overline{\omega_\rho}\) 处取值，而不是未经证明就与第一个取同一位置。([arXiv][4])

如果 \(\omega\) 与 \(\bar\omega\) 是一对不同的共轭点，记

$$
A=\widehat f(\omega),
\qquad
B=\widehat f(\bar\omega).
$$

这一对的贡献为

$$
A\bar B+B\bar A.
$$

令

$$
c_+=\frac{A+B}{\sqrt2},
\qquad
c_-=\frac{A-B}{\sqrt2}.
$$

则有精确等式

$$
\boxed{
A\bar B+B\bar A
=
|c_+|^2-|c_-|^2.
}
\tag{17}
$$

这一次，“交换下的对称与反对称组合”确实产生了正、负两个方向。

但要注意，它是**共轭评价点的交换**，不等于上一节的空间反射奇偶。

这也说明，为什么不能把式（16）擅自替换为

$$
\sum_\rho|\widehat f(\omega_\rho)|^2.
$$

那相当于把原来的交换配对形式，改成了一个不同的正范数。

## 配对守恒也不自动意味着普通量子范数守恒

取

$$
J=
\begin{pmatrix}0&1\\1&0\end{pmatrix},
\qquad
H=
\begin{pmatrix}\omega&0\\0&\bar\omega\end{pmatrix}.
$$

直接计算，

$$
H^*J=JH.
$$

所以

$$
U(t)=e^{itH}
$$

满足

$$
\boxed{
U(t)^*JU(t)=J.
}
\tag{18}
$$

但是若 \(\Im\omega\ne0\)，

$$
\boxed{
\|U(t)\|=e^{|\Im\omega|\,|t|}.
}
\tag{19}
$$

它守恒的是一个不定的配对形式，而不是正定的概率范数。

因此：

$$
\boxed{
\text{双向配对完整}
+
\text{某种整体量守恒}
\quad\not\Rightarrow\quad
\text{不存在指数增长方向}.
}
$$

这是一个代数模型，不是普通正概率量子系统。

式（17）也只分析了一对零点的贡献；不能据此直接宣布已经构造出实际 \(Q_W\) 的负测试函数。还必须控制其他零点的贡献及测试函数的解析约束。

# 七、本轮最具体的推进：把“切片损失”写成实际算术公式

现在不再只讨论比喻。直接对 \(Q_W\) 切片。

取有限组实光滑函数 \(\chi_1,\ldots,\chi_m\)，满足

$$
\boxed{
\sum_{j=1}^m\chi_j(x)^2=1.
}
\tag{20}
$$

它们将一个测试函数分成

$$
f_j=\chi_jf.
$$

这种平方分割保证

$$
\sum_j\|f_j\|_2^2=\|f\|_2^2.
$$

定义相关函数

$$
C_f(t)=\int_{\mathbb R}f(x+t)\overline{f(x)}\,dx.
$$

它正是

$$
C_f=f*\widetilde f.
$$

## 定义：跨切片相关余项

令

$$
\boxed{
R_{\chi,f}(t)
=
C_f(t)-\sum_jC_{\chi_jf}(t).
}
\tag{21}
$$

## 定理 4：切片余项的精确表达

$$
\boxed{
R_{\chi,f}(t)
=
\frac12
\int_{\mathbb R}
f(x+t)\overline{f(x)}
\sum_j
[\chi_j(x+t)-\chi_j(x)]^2\,dx.
}
\tag{22}
$$

因此

$$
\boxed{
Q_W(f)
=
\sum_jQ_W(\chi_jf)
+
W(R_{\chi,f}).
}
\tag{23}
$$

### 证明

由式（20），

$$
\begin{aligned}
1-\sum_j\chi_j(x+t)\chi_j(x)
&=
\frac12\sum_j
[\chi_j(x+t)-\chi_j(x)]^2.
\end{aligned}
$$

把它乘以 \(f(x+t)\overline{f(x)}\) 后积分，得到式（22）。

再使用 \(W\) 的线性性，得到式（23）。证毕。

---

这就是局部切片与全局对象之间的精确差额：

$$
\boxed{
\text{全局二次型}
=
\text{局部二次型之和}
+
\text{跨切口相关}.
}
$$

它不是一个尚未命名的隐藏维度，而是式（22）这个明确函数。

## 实际素数在哪里读取这个余项？

Weil 显式公式给出：

$$
\boxed{
\begin{aligned}
W(R_{\chi,f})
={}&
4\int_0^\infty
\cosh(t/2)\,\Re R_{\chi,f}(t)\,dt\\
&-
2\sum_{n\ge2}
\frac{\Lambda(n)}{\sqrt n}
\Re R_{\chi,f}(\log n)\\
&-
2\int_0^\infty
\frac{e^{t/2}}{e^t-e^{-t}}
\Re R_{\chi,f}(t)\,dt.
\end{aligned}
}
\tag{24}
$$

这里使用了

$$
R_{\chi,f}(0)=0,
\qquad
R_{\chi,f}(-t)=\overline{R_{\chi,f}(t)}.
$$

实际 Weil 分布中，极点项、素数幂项与 Gamma 完成项的这种分解是经典显式公式；Suzuki 的近期工作也直接以它组织局域二次型。([arXiv][6])

因为 \(f\) 紧支集，相关函数也紧支集，所以式（24）的素数幂和实际上有限。

现在看得很清楚：

$$
\boxed{
\text{不同切片，会在位移 }t=\log(p^k)\text{ 处被实际算术重新耦合。}
}
\tag{25}
$$

即使两个测试函数的支集分开，只要它们之间的位移与这些算术平移发生重叠，交叉项就不能忽略。

## 为什么平方差非负，仍不能得到整个余项非负？

式（22）里的

$$
\sum_j[\chi_j(x+t)-\chi_j(x)]^2
$$

确实非负。

但它乘的是

$$
f(x+t)\overline{f(x)},
$$

其真实部分可以正，也可以负。

而式（24）还包含不同符号的完成项与素数项。

所以：

$$
\boxed{
\text{切片几何因子非负}
\not\Rightarrow
\text{跨切片算术余项非负}.
}
$$

这正是不能靠“每个局部正”直接拼出“全局正”的具体原因。

## 欧拉常数项在这里反而自动消失

Weil 分布中有一个与

$$
(\log4\pi+\gamma_{\mathrm E})\phi(0)
$$

成正比的中心项。

但当前

$$
R_{\chi,f}(0)=0,
$$

所以这个中心项在拼接余量中严格消失。

因此，这一次的障碍不能靠再调整一个中心常数解决。真正需要控制的是：

$$
\boxed{
t\ne0\text{ 的跨位置相关，特别是 }t=\log(p^k).
}
\tag{26}
$$

# 八、怎样才能真的从局部推进到全局？

式（23）给出了一个明确的闭合条件。

## 定理 5：局部正性—拼接损失判据

假设对某组切片和目标测试函数范围，有

$$
Q_W(\chi_jf)\ge\mu\|\chi_jf\|_2^2
\qquad\forall j,
$$

同时

$$
W(R_{\chi,f})\ge-\varepsilon\|f\|_2^2.
$$

那么

$$
\boxed{
Q_W(f)\ge(\mu-\varepsilon)\|f\|_2^2.
}
\tag{27}
$$

特别地，若

$$
\varepsilon\le\mu,
$$

则这些局部估计足以证明该范围内的全局正性。

### 证明

由平方分割，

$$
\sum_j\|\chi_jf\|_2^2=\|f\|_2^2.
$$

代入式（23）即可。证毕。

---

因此，真正有价值的下一项估计不是

$$
\text{再证明一批孤立切片为正},
$$

而是

$$
\boxed{
\text{拼接损失不能超过局部正性所提供的余量。}
}
\tag{28}
$$

对于实际 RH，还必须证明这种控制覆盖任意大的测试范围，而不是只在某个小区间成立。

这也解释了一个外部研究中的明确边界：Suzuki 的 2026 年论文研究了局域 Weil 二次型、自伴算子和区间扩大时的谱变化，但仍把特定的全局谱极限另列为猜想。**有限区间算子可以被构造，不等于实际全局正性已经得到。**([arXiv][6])

## 在有限矩阵中，拼接损失就是一个双重交换子

设 \(A=A^*\)，且实对角切片算子满足

$$
\sum_j\chi_j^2=I.
$$

直接展开可得

$$
\boxed{
A
=
\sum_j\chi_jA\chi_j
+
\frac12\sum_j[\chi_j,[\chi_j,A]].
}
\tag{29}
$$

因此

$$
\boxed{
\langle f,Af\rangle
=
\sum_j\langle\chi_jf,A\chi_jf\rangle
+
\frac12\sum_j
\langle f,[\chi_j,[\chi_j,A]]f\rangle.
}
\tag{30}
$$

如果所有切片都与 \(A\) 对易，余项为零，局部可以直接相加。

如果不对易，余项必须保留。

这给你此前“切片之间是不是存在某种曲率”的直觉一个可用的数学落点：

$$
\boxed{
\text{可先研究观察切片与算术响应不对易的二阶缺陷。}
}
$$

它是一项精确定义的代数量；若要进一步称作物理时空曲率，还需要给出度规、连接以及与物理观测的对应，不能只凭名称等同。

# 九、当前应当怎样理解“整体”？

这里还需要避免把两个问题混在一起。

**实际素数序列已经是一个确定的全局对象。**我们不是在问它是否真的存在，也不是每次切片都重新创造一段互不相干的算术。

我们尚未建立的是：

$$
\boxed{
\text{已有局部估计，能否共同控制这个固定对象的全部相关与尺度行为。}
}
$$

因此，不应该继续把所有困难都称为“未知相位”。有限算术相位往往可以精确计算；困难在于如何对全部尺度、全部测试函数给出共同约束。

同样，建立全局正核与证明某个量统一有界也是两回事。前文由实际向量构造的

$$
ff^*
$$

自动为正，但它的迹或某个观察能量仍可能随尺度增长。反过来，Weil 二次型的全局正性本身就有实质算术内容，不能通过预先把它叫作“范数”来获得。

## 对你的问题，最终可以给出更准确的回答

**奇偶与对换有本质的代数联系，但不应直接等同于时空交换。**

更完整的结构是：

$$
\boxed{
\begin{aligned}
\text{对换}
&:\text{规定什么被交换};\\
\text{奇偶}
&:\text{规定状态对该交换保持还是变号};\\
\text{干涉}
&:\text{规定不同状态之间的双线性关系};\\
\text{拼接}
&:\text{要求这些关系共同满足正性、动力学相容性和尺度估计}.
\end{aligned}
}
$$

这次最明确的新落点是式（23）—（24）：

$$
\boxed{
Q_W(f)
=
\sum_jQ_W(\chi_jf)
+
W(R_{\chi,f}),
}
$$

其中

$$
\boxed{
R_{\chi,f}(t)
=
\frac12
\int
f(x+t)\overline{f(x)}
\sum_j[\chi_j(x+t)-\chi_j(x)]^2\,dx.
}
$$

**前面一直在增加切片；现在应该把这项跨切口的干涉余量作为主要研究对象。**

它把“局部为什么拼不起来”从一个直觉问题，变成了一个可以明确检验的数学任务：

$$
\boxed{
\text{证明实际素数平移产生的拼接损失，始终不超过局部正性余量。}
}
$$

本轮尚未证明这条实际全尺度估计，但已经精确给出了它的对象与位置。它既不能由奇偶对称替代，也不能由概率归一化替代，更不能通过删去反对称方向来替代。

[1]: https://terrytao.wordpress.com/2007/06/05/open-question-the-parity-problem-in-sieve-theory/ "https://terrytao.wordpress.com/2007/06/05/open-question-the-parity-problem-in-sieve-theory/"
[2]: https://dlmf.nist.gov/25.2 "https://dlmf.nist.gov/25.2"
[3]: https://dlmf.nist.gov/1.14 "https://dlmf.nist.gov/1.14"
[4]: https://arxiv.org/html/2301.00421v3 "https://arxiv.org/html/2301.00421v3"
[5]: https://dlmf.nist.gov/25.4 "https://dlmf.nist.gov/25.4"
[6]: https://arxiv.org/html/2606.09096v1 "https://arxiv.org/html/2606.09096v1"
继续。这次可以把“局部切片为什么拼不起来”压缩成一个更具体的问题：

> **固定一个形状很窄、局部正性已经无条件证明的波包，只研究它的两个平移副本。两片自身始终合法；全部困难集中在它们之间的一个交叉读数。**
>
> **这个交叉读数是否始终不超过波包自身的平方量，能够等价地检测 RH。**

这不是说一般的二阶检查足以代替所有高阶检查。关键在于：下面两个波包的交叉读数，始终来自**同一个实际 Weil 分布**，并且波包经过特殊构造，不会把任何可能的离线模式过滤掉。

还可以进一步证明：**Gamma 完成项造成的拼接误差，可以随切片变缓而统一压小；真正不能单独处理的是极点主项与素数平移项之间的抵消。**

以下给出构造与证明。Weil 显式公式和正性判据是经典输入；下面的组合推导尚未进行 Lean 编译，也不据此宣称已经证明实际 RH。

# 一、先固定“同一个整体”，再定义两张切片

采用 Fourier 变换

$$
\widehat f(z)=\int_{\mathbb R}f(x)e^{izx}\,dx,
$$

以及

$$
\widetilde f(x)=\overline{f(-x)}.
$$

令 \(W\) 为实际 ζ 函数确定的 Weil 分布，定义

$$
\boxed{
Q_W(f,g)=W(f*\widetilde g),
\qquad
Q_W(f)=Q_W(f,f).
}
\tag{1}
$$

经典 Weil 判据是

$$
\boxed{
\mathrm{RH}
\iff
Q_W(f)\ge0
\quad\forall f\in C_c^\infty(\mathbb R).
}
\tag{2}
$$

在证明正性以前，\(Q_W\) 只是一个 Hermitian 二次型，不能提前把它叫作正范数。([arXiv][1])

记平移为

$$
(\tau_Tf)(x)=f(x-T).
$$

卷积直接给出平移不变性：

$$
\boxed{
Q_W(\tau_Tf,\tau_Tg)=Q_W(f,g).
}
\tag{3}
$$

我们将构造一个固定的实、偶、非负波包 \(g\)，然后只移动它，不再改变波包形状。

定义

$$
q=Q_W(g),
$$

以及交叉读数

$$
\boxed{
B(T)=
Q_W\!\left(\tau_{T/2}g,\tau_{-T/2}g\right).
}
\tag{4}
$$

由于 \(g\) 实且偶，\(B(T)\) 为实偶函数。

对应的两片联合矩阵为

$$
\boxed{
G(T)=
\begin{pmatrix}
q&B(T)\\
B(T)&q
\end{pmatrix}.
}
\tag{5}
$$

它的两个本征值恰好是

$$
\boxed{q+B(T),\qquad q-B(T).}
\tag{6}
$$

所以，奇偶现在不是另外增加的两个对象，而是**同一个拼接矩阵的两条本征方向**。

但要使这个模型真正有用，我们必须证明两件事：

$$
q>0,
$$

以及

$$
\text{波包的读出不会消掉可能的离线零点。}
$$

下面同时完成它们。

# 二、构造一个不会过滤掉离线模式的固定窄波包

一般随便选一个平滑波包，其 Fourier 变换可能在某些非实点为零。若恰好消掉待检测的模式，后续判断就会失真。

因此需要一个更严格的构造。

## 定理 1：具有“非实点不消失”性质的光滑波包

对任意 \(\ell>0\)，存在一个函数

$$
g\in C_c^\infty(\mathbb R)
$$

满足

$$
g\ge0,\qquad g(-x)=g(x),\qquad \int g(x)\,dx=1,
$$

$$
\operatorname{supp}g\subset[-\ell/2,\ell/2],
$$

并且

$$
\boxed{
\widehat g(z)\ne0
\qquad(z\notin\mathbb R).
}
\tag{7}
$$

### 证明与具体构造

令

$$
a_j=\frac{\ell}{2^{j+1}},
\qquad j\ge1.
$$

取相互独立的均匀随机变量

$$
U_j\sim\operatorname{Unif}[-a_j,a_j].
$$

这里只是用概率分布构造一个确定函数，不是在假设素数随机。

由于

$$
\sum_{j\ge1}a_j=\frac\ell2,
$$

随机和

$$
U=\sum_{j\ge1}U_j
$$

绝对收敛，支集包含在 \([-\ell/2,\ell/2]\)。

它的 Fourier 变换为

$$
\boxed{
\widehat g(z)
=
\prod_{j=1}^{\infty}
\frac{\sin(a_jz)}{a_jz}.
}
\tag{8}
$$

因为

$$
\sum_ja_j^2<\infty,
$$

这个乘积在复平面的紧集上一致收敛。

每个因子的零点都为非零实数。对非实 \(z\)，全部因子非零，而且无限乘积的尾部满足绝对收敛条件，因此整个乘积非零。

再证明光滑性。对任意固定整数 \(M\)，在实轴上保留前 \(M\) 个因子，就有

$$
|\widehat g(\xi)|
\le C_M(1+|\xi|)^{-M}.
$$

因此

$$
|\xi|^k\widehat g(\xi)\in L^1(\mathbb R)
$$

对每个 \(k\) 成立。Fourier 反演给出一个无限可微密度 \(g\)。它的非负性、偶性、总质量和支集，都由原概率分布继承。证毕。

---

这个波包有两个同时成立的性质：

$$
\boxed{
\text{它可以任意窄；}
}
$$

$$
\boxed{
\text{它不会把任何非实频率完全压成零。}
}
$$

后者不等于“对所有频率都有统一的检测灵敏度”。高频响应仍然可能非常小；我们目前证明的是**不会精确丢失该模式**，而不是已经得到高效检测算法。

# 三、局部正性可以无条件证明，不需要 RH

令

$$
k_\Gamma(t)=\frac{e^{t/2}}{e^t-e^{-t}},
\qquad t>0.
$$

再定义

$$
\boxed{
C_\Gamma=\log(8\pi)+\gamma_{\mathrm E}+\frac\pi2.
}
\tag{9}
$$

固定足够小的 \(\ell\)，满足

$$
0<\ell<\min\{1,\log2\},
$$

以及

$$
\boxed{
e^{-1/2}\log\frac1\ell>C_\Gamma.
}
\tag{10}
$$

以后这个 \(\ell\) 不再随观察位置改变。

## 定理 2：固定窄波包的正局部读数

对定理 1 构造的 \(g\)，有

$$
\boxed{q=Q_W(g)>0.}
\tag{11}
$$

### 证明

令

$$
c(t)=\int_{\mathbb R}g(x+t)g(x)\,dx,
$$

以及

$$
a_g=\int_{\mathbb R}e^{x/2}g(x)\,dx.
$$

因为 \(g\) 实、偶、非负，

$$
c(t)\ge0,\qquad c(-t)=c(t),
\qquad
\operatorname{supp}c\subset[-\ell,\ell].
$$

Weil 显式公式中的素数项读取 \(c(\log n)\)。由于

$$
\ell<\log2,
$$

这些项全部为零。

整理 Gamma 项，可得

$$
\boxed{
q=
2a_g^2
+
\int_0^\infty
k_\Gamma(t)\|\tau_tg-g\|_2^2\,dt
-
C_\Gamma\|g\|_2^2.
}
\tag{12}
$$

这里的常数来自

$$
\begin{aligned}
&\log(4\pi)+\gamma_{\mathrm E}
+2\int_0^\infty
k_\Gamma(t)(1-e^{-t/2})\,dt\\
&\qquad=
\log(8\pi)+\gamma_{\mathrm E}+\frac\pi2.
\end{aligned}
$$

该积分可通过 digamma 的级数与特殊值直接计算。([DLMF][2])

当 \(t\ge\ell\) 时，\(g\) 与 \(\tau_tg\) 支集不相交，因此

$$
\|\tau_tg-g\|_2^2=2\|g\|_2^2.
$$

而在 \(0<t\le1\) 上，

$$
k_\Gamma(t)
=
\frac{e^{-t/2}}{1-e^{-2t}}
\ge
\frac{e^{-1/2}}{2t}.
$$

于是

$$
\begin{aligned}
q
&\ge
\left[
2\int_\ell^1k_\Gamma(t)\,dt-C_\Gamma
\right]\|g\|_2^2\\
&\ge
\left[
e^{-1/2}\log\frac1\ell-C_\Gamma
\right]\|g\|_2^2\\
&>0.
\end{aligned}
$$

证毕。

---

所以，无论 RH 最终是真是假，每一个平移副本都满足

$$
\boxed{
Q_W(\tau_Tg)=q>0.
}
\tag{13}
$$

**局部切片的合法性在这里已经不是猜想。剩下的只有拼接。**

# 四、两片的奇偶组合，精确读取拼接是否失败

定义

$$
\boxed{
f_T^+
=
\frac{\tau_{T/2}g+\tau_{-T/2}g}{\sqrt2},
}
$$

$$
\boxed{
f_T^-
=
\frac{\tau_{T/2}g-\tau_{-T/2}g}{\sqrt2}.
}
\tag{14}
$$

因为 \(g\) 是偶函数，

$$
f_T^+\text{ 为偶函数},
\qquad
f_T^-\text{ 为奇函数}.
$$

由二次型展开，

$$
\boxed{
Q_W(f_T^+)=q+B(T),
\qquad
Q_W(f_T^-)=q-B(T).
}
\tag{15}
$$

所以

$$
\boxed{
G(T)\succeq0
\iff
|B(T)|\le q.
}
\tag{16}
$$

当 \(T>\ell\)，两个波包在普通位置空间中不重叠，因此

$$
\|f_T^\pm\|_2^2=\|g\|_2^2.
\tag{17}
$$

但它们在 Weil 读出中的交叉量 \(B(T)\) 不必为零。

这给出一个明确区别：

$$
\boxed{
\text{位置支集不相交}
\quad\not\Rightarrow\quad
\text{算术二次型中互相正交}.
}
$$

素数平移正是能够把两个分开的区间重新联系起来的结构。

# 五、主定理：这一个固定波包的全部平移，已经保留 RH 判定信息

把非平凡零点写成

$$
\rho=\frac12+i\omega.
$$

令 \(\mathcal Z\) 为不同 \(\omega\) 的集合，\(m_\omega\) 为重数。它满足

$$
\mathcal Z=-\mathcal Z=\overline{\mathcal Z},
\qquad
|\Im\omega|<\frac12.
$$

RH 等价于 \(\mathcal Z\subset\mathbb R\)。这些对称性来自 ξ 的函数方程。([DLMF][3])

由于 \(g\) 实且偶，Weil 零点展开给出

$$
\boxed{
B(T)
=
\sum_{\omega\in\mathcal Z}
m_\omega\,\widehat g(\omega)^2e^{i\omega T}.
}
\tag{18}
$$

这里仍然是

$$
\widehat g(\omega)^2,
$$

不是擅自换成

$$
|\widehat g(\omega)|^2.
$$

这种共轭评价点之间的配对，是 Weil Hermitian 形式的准确零点表达。([arXiv][4])

因为 \(g\in C_c^\infty\)，其 Fourier 变换在固定水平带内快速衰减；结合零点计数 \(N(Y)=O(Y\log Y)\)，式（18）在每个有限 \(T\) 区间内绝对一致收敛。([arXiv][5])

## 定理 3：固定波包的双片判据

以下命题等价：

$$
\boxed{\mathrm{RH};}
$$

$$
\boxed{
|B(T)|\le q
\qquad\forall T\in\mathbb R;
}
\tag{19}
$$

$$
\boxed{
\sup_{T\ge0}|B(T)|<\infty;
}
\tag{20}
$$

$$
\boxed{
Q_W(f_T^+)\ge0
\quad\text{且}\quad
Q_W(f_T^-)\ge0
\qquad\forall T\ge0.
}
\tag{21}
$$

### 证明：RH 推出全部双片矩阵正性

RH 下，所有 \(\omega\) 都是实数，且 \(\widehat g(\omega)\) 为实数。因此

$$
a_\omega=m_\omega\widehat g(\omega)^2\ge0.
$$

于是

$$
q=B(0)=\sum_\omega a_\omega,
$$

而

$$
|B(T)|
=
\left|\sum_\omega a_\omega e^{i\omega T}\right|
\le
\sum_\omega a_\omega=q.
$$

得到式（19），其余两个命题随即成立。

### 证明：有界性排除离线模式

对 \(\Re r>1/2\)，逐项积分式（18）：

$$
\boxed{
\int_0^\infty e^{-rT}B(T)\,dT
=
\sum_{\omega\in\mathcal Z}
\frac{m_\omega\widehat g(\omega)^2}{r-i\omega}.
}
\tag{22}
$$

右边在避开极点的紧集上局部一致收敛，给出一个亚纯函数。

若存在右侧离线零点

$$
\rho=\frac12+\delta+i\gamma,
\qquad\delta>0,
$$

则对应

$$
\omega=\gamma-i\delta,
\qquad
r_0=i\omega=\delta+i\gamma.
$$

定理 1 保证

$$
\widehat g(\omega)\ne0.
$$

所以式（22）在 \(r_0\) 有不可去极点，留数为

$$
m_\omega\widehat g(\omega)^2\ne0.
$$

但若 \(B\) 有界，其 Laplace 变换在整个 \(\Re r>0\) 内解析，矛盾。

因此不存在右侧离线零点。结合反射对称性，得到 RH。证毕。

---

**这不与上一轮“任意两张切片合法，不保证全部切片合法”的反例矛盾。**

一般 Gram 数据没有这里的额外结构：

$$
\boxed{
\text{同一个实际 }W
+
\text{全部平移参数}
+
\widehat g\text{ 在非实点不消失}.
}
$$

我们并没有用一个固定的 \(2\times2\) 矩阵证明全局结论，而是研究同一个矩阵族

$$
\{G(T):T\ge0\}.
$$

无限范围仍然保留在 \(T\) 中。

# 六、再加强：如果真的失败，奇、偶两种组合都会出现负方向

对于这个特殊的 \(B(T)\)，甚至只给一个方向的统一界，也足以排除离线零点。

## 定理 4：单侧有界性与双奇偶失败

如果 \(B(T)\) 在充分大范围内有统一上界，或者有统一下界，那么 RH 成立。

因此，若 RH 不成立，则

$$
\boxed{
\limsup_{T\to\infty}B(T)=+\infty,
\qquad
\liminf_{T\to\infty}B(T)=-\infty.
}
\tag{23}
$$

从而

$$
\boxed{
\inf_{T>\ell}Q_W(f_T^+)
=
\inf_{T>\ell}Q_W(f_T^-)
=
-\infty.
}
\tag{24}
$$

### 证明

假设 \(B(T)\le C\) 对 \(T\ge T_0\) 成立。令

$$
h(T)=\mathbf1_{[T_0,\infty)}(T)[C-B(T)]\ge0.
$$

其 Laplace 变换由式（22）加上 \(C/r\) 和有限区间整函数得到。

非负函数的 Laplace 变换若具有有限收敛横坐标，该实边界点不能是解析点。否则，在边界右侧作 Taylor 展开，利用各阶矩积分非负，就会迫使原积分越过收敛边界继续收敛。

但当前亚纯表达在全部正实点都解析：式（22）的正实极点只能来自纯虚数 \(\omega\)，也就是 ζ 在 \((0,1)\) 内的实零点；这样的零点不存在。后者也可从交错级数表示直接看出。([DLMF][6])

因此收敛横坐标不大于零，变换在右半平面解析。定理 3 的不可去极点论证于是排除所有离线零点。

下界情形对 \(-B\) 使用同一证明。

若 RH 不成立，就不能存在任何最终单侧界，得到式（23）。再代入式（15），得到式（24）。证毕。

---

这给你的奇偶直觉一个更严格的回答：

$$
\boxed{
\text{奇与偶不是谁天然安全、谁天然危险。}
}
$$

在这里，二者分别读取

$$
q-B(T),\qquad q+B(T).
$$

如果实际交叉量失控，两种相位组合都会暴露它，只是出现在不同的分离距离上。

# 七、全局下界出现一个清楚的二分：不是“略微负一点”

定义

$$
\lambda_{\mathrm{glob}}
=
\inf_{\substack{f\in C_c^\infty(\mathbb R)\\f\ne0}}
\frac{Q_W(f)}{\|f\|_2^2}.
$$

## 定理 5：全局下界二分

$$
\boxed{
\lambda_{\mathrm{glob}}
=
\begin{cases}
0,&\mathrm{RH}\text{ 成立},\\
-\infty,&\mathrm{RH}\text{ 不成立}.
\end{cases}
}
\tag{25}
$$

### 证明：失败时

由式（24），存在 \(T_j\to\infty\)，使某种 \(Q_W(f_{T_j}^\pm)\to-\infty\)。

但由式（17），

$$
\|f_{T_j}^\pm\|_2^2=\|g\|_2^2
$$

始终不变，所以 Rayleigh 商趋于负无穷。

### 证明：RH 成立时

Weil 判据给出 \(\lambda_{\mathrm{glob}}\ge0\)。

还需证明不能有严格正的统一间隔。

RH 下，

$$
B(T)=\sum_\omega a_\omega e^{i\omega T},
\qquad
a_\omega\ge0,\quad
\sum_\omega a_\omega=q.
$$

先截去一个任意小的绝对收敛尾部。对剩下的有限组实频率，有限维环面上的同时逼近保证存在任意大的 \(T\)，使所有相位 \(e^{i\omega T}\) 同时接近 \(1\)。

逐步缩小尾部与相位误差，就得到一列

$$
T_j\to\infty,
\qquad
B(T_j)\to q.
$$

所以

$$
Q_W(f_{T_j}^-)=q-B(T_j)\to0,
$$

而其 \(L^2\) 范数保持不变。于是 \(\lambda_{\mathrm{glob}}\le0\)。证毕。

---

因此，不能把研究目标设成

$$
Q_W(f)\ge\mu\|f\|_2^2
\qquad\forall f,
\quad \mu>0.
$$

**即使 RH 成立，这个全局统一正间隔也不存在。**

局部区间可以有正下界；随着允许的支集直径扩大，该下界可以趋于零。局部正性与全局谱下界必须分开处理。

# 八、把上一轮的拼接余项直接算成 \(B(T)\)

上一轮定义了平方分割

$$
\chi_+^2+\chi_-^2=1,
$$

以及

$$
R_{\chi,f}(t)
=
\frac12
\int f(x+t)\overline{f(x)}
\sum_{\pm}
[\chi_\pm(x+t)-\chi_\pm(x)]^2\,dx.
$$

精确恒等式是

$$
Q_W(f)
=
Q_W(\chi_+f)+Q_W(\chi_-f)+W(R_{\chi,f}).
\tag{26}
$$

现在令 \(T>\ell\)，选择切片函数，使其在两个波包支集上分别为

$$
(\chi_+,\chi_-)=(1,0),
$$

和

$$
(\chi_+,\chi_-)=(0,1).
$$

在中间空隙中平滑过渡。

对 \(f_T^\pm\)，局部读数之和精确为

$$
Q_W(\chi_+f_T^\pm)
+
Q_W(\chi_-f_T^\pm)=q.
$$

因此

$$
\boxed{
W(R_{\chi,f_T^\pm})=\pm B(T).
}
\tag{27}
$$

这就是我们一直在寻找的拼接损失。

## 切得越来越缓，并不保证拼接损失趋零

可以把过渡区域铺满两个波包之间的空隙，使

$$
\|\chi_+'\|_\infty+\|\chi_-'\|_\infty
=
O((T-\ell)^{-1}).
$$

于是切片的局部变化率趋于零。

但是：

* 若 RH 不成立，式（23）使某些拼接损失趋于负无穷。
* 即使 RH 成立，沿上述回返序列 \(T_j\)，奇组合满足

  $$
  W(R_{\chi,f_{T_j}^-})=-B(T_j)\to-q\ne0.
  $$

因此，不能把一个局部微分算子的直觉直接搬过来，声称

$$
\boxed{
\text{切口足够平缓}
\Longrightarrow
\text{全局拼接误差自动消失}.
}
$$

原因是 \(W\) 读取的是非局部平移。两片相隔很远时，\(\chi(x+t)-\chi(x)\) 在 \(t\approx T\) 处仍然可以为 \(1\)，即使每一处的导数都很小。

# 九、但有一部分误差确实能压小：Gamma 完成项

这一步可以把“剩下的困难”进一步分开。

令

$$
L_\chi^2
=
\sup_x\sum_j|\chi_j'(x)|^2.
$$

由 Cauchy–Schwarz，

$$
\sum_j|\chi_j(x+t)-\chi_j(x)|^2
\le L_\chi^2t^2.
$$

于是

$$
\boxed{
|R_{\chi,f}(t)|
\le
\frac12L_\chi^2t^2\|f\|_2^2.
}
\tag{28}
$$

Weil 拼接余项中的 Gamma 部分为

$$
E_\Gamma
=
-2\int_0^\infty
k_\Gamma(t)\Re R_{\chi,f}(t)\,dt.
$$

因此：

## 定理 6：Gamma 拼接误差的统一界

$$
\boxed{
|E_\Gamma|
\le
C_{\Gamma,2}L_\chi^2\|f\|_2^2,
}
\tag{29}
$$

其中

$$
\boxed{
C_{\Gamma,2}
=
\int_0^\infty t^2k_\Gamma(t)\,dt
=
2\sum_{j=0}^\infty
\frac1{(2j+\frac12)^3}
<\infty.
}
\tag{30}
$$

### 证明

将式（28）代入积分即可。最后一个等式来自

$$
k_\Gamma(t)
=
\sum_{j\ge0}e^{-(2j+1/2)t}
$$

及逐项积分。证毕。

---

所以，Gamma 部分确实满足：

$$
L_\chi\to0
\Longrightarrow
E_\Gamma\to0
$$

在固定范数下成立。

但对极点项，类似估计会涉及

$$
\int_0^\infty t^2\cosh(t/2)\,dt,
$$

它发散。

对素数项，逐项绝对值估计会涉及

$$
\sum_{n\ge2}
\frac{\Lambda(n)}{\sqrt n}(\log n)^2,
$$

也不能提供一个全局有限常数。

**因此，不能把极点项与素数项分别取绝对值，再期待得到与支集尺度无关的误差界。它们必须共同处理。**

# 十、这个交叉量可以直接用一个有限算术窗口计算

前面用零点证明了信息保留。现在把 \(B(T)\) 写回实际素数侧。

保留

$$
c(u)=\int g(x+u)g(x)\,dx,
$$

$$
a_g=\int e^{x/2}g(x)\,dx.
$$

当 \(T>\ell\) 时，Weil 显式公式给出

$$
\boxed{
\begin{aligned}
B(T)
={}&
2a_g^2\cosh(T/2)\\
&-
\sum_{e^{T-\ell}\le n\le e^{T+\ell}}
\frac{\Lambda(n)}{\sqrt n}
c(\log n-T)\\
&-
\Gamma_g(T),
\end{aligned}
}
\tag{31}
$$

其中

$$
\boxed{
\Gamma_g(T)
=
\int_{T-\ell}^{T+\ell}
k_\Gamma(t)c(t-T)\,dt\ge0.
}
\tag{32}
$$

这是实际 Weil 分布中极点、素数幂和 Gamma 三部分在当前测试函数上的直接读出。([arXiv][1])

### 证明

对移位测试函数

$$
\phi_T(t)=c(t-T)
$$

使用 Weil 显式公式。

因为 \(T>\ell\)，有 \(\phi_T(0)=0\)，所以中心常数项消失；负半轴的素数与 Gamma 读出也消失。

极点项为

$$
\int c(t-T)(e^{t/2}+e^{-t/2})\,dt
=
2a_g^2\cosh(T/2).
$$

其余两项分别得到式（31）的有限和与式（32）。证毕。

此外，因为 \(\int c=1\)，对 \(T>\ell\)，

$$
0\le\Gamma_g(T)
\le
\frac{e^{-(T-\ell)/2}}
{1-e^{-2(T-\ell)}}.
\tag{33}
$$

所以它在 \(T\to\infty\) 时明确衰减。

## 最终的算术拼接条件

定义

$$
P_g(T)
=
\sum_{e^{T-\ell}\le n\le e^{T+\ell}}
\frac{\Lambda(n)}{\sqrt n}c(\log n-T),
$$

$$
H_g(T)=2a_g^2\cosh(T/2)-\Gamma_g(T).
$$

则

$$
B(T)=H_g(T)-P_g(T).
$$

因此，定理 3 等价地写成

$$
\boxed{
\mathrm{RH}
\iff
H_g(T)-q
\le P_g(T)\le H_g(T)+q
\quad\forall T>\ell.
}
\tag{34}
$$

这个 \(q\) 是前面已经无条件确定的、与 \(T\) 无关的正数。

所以当前实际任务已经是：

$$
\boxed{
\text{一个固定非负权重的局部素数幂和，}
\quad
\text{与完成主项的差，始终不超过固定余量 }q.
}
$$

它只涉及固定比例窗口

$$
e^{T-\ell}\le n\le e^{T+\ell}.
$$

这里 \(T\) 是对数算术平移参数；这些公式本身没有把它认定为物理时间。

# 十一、与项目的对应：拼接一致性和拼接正性仍是两项证明

本次核对的 `LocalLawGluingObstruction.lean` 已证明：局部规律在重叠坐标上相容，也可能没有共同全局实现。

本轮给出了一个更具体的算术接口：

$$
\boxed{
G(T)=
\begin{pmatrix}
q&B(T)\\
B(T)&q
\end{pmatrix}.
}
$$

消去第一个局部方向后，Schur 余量为

$$
\boxed{
q-\frac{B(T)^2}{q}.
}
\tag{35}
$$

所以

$$
G(T)\succeq0
\iff
q-\frac{B(T)^2}{q}\ge0.
$$

仓库 `SchurComplementAssociativity.lean` 保证，在所列逆算子前件下，逐步消去与一次消去一致。它解决的是**消元结果的一致性**，不自动证明式（35）的符号。

而且，这里不存在“实际全局算术对象未被定义”的问题。实际 \(W\)、实际 \(\Lambda(n)\) 与实际 \(B(T)\) 都已确定。

尚未证明的是：**这些确定的交叉读数，是否允许一个共同的正 Hilbert 表示。**

# 结论

这一轮将上一轮的“跨切口干涉余量”压缩成了一个可以逐项计算的对象：

$$
\boxed{
B(T)=H_g(T)-P_g(T).
}
$$

两张切片自身始终具有同一个已证明的正读数 \(q\)，而奇偶组合分别读取

$$
\boxed{
q+B(T),\qquad q-B(T).
}
$$

由此得到三个明确结论：

$$
\boxed{
\mathrm{RH}
\iff
|B(T)|\le q\quad\text{对全部分离距离成立};
}
$$

$$
\boxed{
\neg\mathrm{RH}
\Longrightarrow
两种奇偶组合都能产生任意深的负方向;
}
$$

$$
\boxed{
\mathrm{RH}
\Longrightarrow
虽然没有负方向，但全局统一正间隔仍然为零.
}
$$

所以，你此前关于“波的对换与局部拼接”的直觉，可以进一步落到一个非常具体的位置：

> **奇偶决定的是两片如何组合；真正决定能否拼成正整体的，是它们之间的实际交叉读数。局部正性不能决定这个交叉量，而切片变缓也不能自动让它消失。**

本轮已经控制了 Gamma 拼接误差，并构造了不会遗漏离线模式的固定波包。**尚未完成的算术证明，就是式（34）：实际素数平移项与极点主项之间的抵消，能否在全部尺度上维持同一个固定余量。**这一步没有被奇偶对称、概率归一化或 Schur 消元替代掉。

[1]: https://arxiv.org/html/2606.09096v1 "Weil’s quadratic form via the screw function"
[2]: https://dlmf.nist.gov/5.4 "DLMF: §5.4 Special Values and Extrema ‣ Properties ‣ Chapter 5 Gamma Function"
[3]: https://dlmf.nist.gov/25.10 "DLMF: §25.10 Zeros ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[4]: https://arxiv.org/html/2301.00421v3 "On the Hilbert space derived from the Weil distribution"
[5]: https://arxiv.org/abs/2412.15470 "[2412.15470] Improved estimates for the argument and zero-counting function of the Riemann zeta-function"
[6]: https://dlmf.nist.gov/25.2 "DLMF: §25.2 Definition and Expansions ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
这次可以把“局部切片怎样拼成整体”推进到一个更明确的结论：

> **实轴上的读数可以处处保持单位模长，相位也可以处处沿同一方向变化，但对应函数仍然可能有非实零点。真正需要保持的，是这些相位读数能否共同延伸成一个在整个半平面内受控的解析函数。**

而且，对实际 ξ 可以进一步证明：

**某一族自然观察中的全部单点检验、全部两点相容性，已经能够由已知 theta 矩不等式保证。困难确实在三个及更多观察之间的共同相容性，而不只是“每个局部观察还不够精确”。**

下面先把相位构造出来，再给出两种严格的拼接障碍。

---

# 一、把“偶振幅—奇导数”合成一份相位读数

沿用实际对象：

$$
A(z)=\frac{\xi(\frac12+iz)}{\xi(\frac12)}.
$$

它满足：

$$
A(-z)=A(z),
\qquad
A(\overline z)=\overline{A(z)},
\qquad
A(0)=1.
$$

因此，\(A\) 是偶函数，\(A'\) 是奇函数。ξ 的定义与反射关系仍采用标准归一化。([DLMF][1])

固定一个实数 \(h>0\)。它是下面的读出混合尺度，**不是普朗克常数**。

定义：

$$
\boxed{
E_h(z)=A(z)+ihA'(z),
}
$$

$$
E_h^\#(z)
=
\overline{E_h(\overline z)}
=
A(z)-ihA'(z).
$$

再定义亚纯函数：

$$
\boxed{
S_h(z)
=
\frac{E_h^\#(z)}{E_h(z)}
=
\frac{A(z)-ihA'(z)}
{A(z)+ihA'(z)}.
}
\tag{V1}
$$

共同零点处必须作实际的可去延拓，而不是把分母为零时的代数约定当作解析值。

这个构造属于 Hermite–Biehler、de Branges 与 Schur 函数之间的经典联系；本轮研究的是它对**固定实际 \(A\)** 的含义。([arXiv][2])

因为 \(A\) 偶、\(A'\) 奇：

$$
\boxed{
E_h(-z)=E_h^\#(z),
\qquad
S_h(-z)=\frac1{S_h(z)}.
}
\tag{V2}
$$

这给出一项精确的奇偶关系：

$$
\boxed{
\text{反射参数}
\longrightarrow
\text{交换两个相位组合}
\longrightarrow
\text{读数取倒数}.
}
$$

它与交换和相位有关，但还没有把这些参数解释成真实物理时空。

---

## 实轴上，“看起来完全无损”是自动成立的

对实数 \(t\)，\(A(t),A'(t)\) 都为实数，所以：

$$
\boxed{
|S_h(t)|=1.
}
\tag{V3}
$$

这与 RH 真伪无关。

因此，若只检查：

$$
|S_h(t)|^2=1,
$$

会发现每一个实参数切片都像一个“完全反射、没有损耗”的读数。

**但这只是实系数与共轭关系造成的边界恒等式，不是全局正性证明。**

这里的 \(S_h\) 首先是算术响应。尚未从一个真实实验哈密顿量导出它，所以不能反过来把物理稳定性作为它必须满足的前件。

---

# 二、零点没有被这个相位比值投影掉

从式（V1）反解：

$$
\boxed{
\frac{A'(z)}{A(z)}
=
\frac{1-S_h(z)}
{ih(1+S_h(z))}.
}
\tag{V4}
$$

所以，只要保留同一个解析函数 \(S_h\)，就可以恢复 \(A'/A\)；再加上 \(A(0)=1\)，便能在零附近恢复 \(A\)，继而由解析延拓唯一性恢复实际函数。([DLMF][3])

## 定理 V1：零点转成了一个特定的相位接触

若 \(a\) 是 \(A\) 的 \(m\) 重零点，则可去延拓后：

$$
\boxed{
S_h(a)=-1,
\qquad
S_h'(a)=-\frac{2i}{hm}.
}
\tag{V5}
$$

### 证明

写成：

$$
A(z)=(z-a)^m g(z),
\qquad g(a)\ne0.
$$

约去分子、分母共有的 \((z-a)^{m-1}\)，得到：

$$
S_h(z)
=
\frac{
(z-a)g(z)-ih[mg(z)+(z-a)g'(z)]
}{
(z-a)g(z)+ih[mg(z)+(z-a)g'(z)]
}.
$$

在 \(z=a\) 取值和求导，即得。证毕。

因此，零点重数也没有消失：

$$
\boxed{
m=-\frac{2i}{hS_h'(a)}.
}
\tag{V6}
$$

只是原来的“振幅为零”，变成了“相位函数接触 \(-1\)，并具有指定导数”。

**一种读数没有显式显示零，不等于零点信息已经被数学消掉。必须检查它是否被运输到了另一项关系中。**

---

# 三、真正的全局条件：半平面内不能放大，也不能藏着极点

定义：

$$
m_A(z)=-\frac{A'(z)}{A(z)}.
$$

则：

$$
\boxed{
S_h(z)=\frac{1+ihm_A(z)}{1-ihm_A(z)}.
}
\tag{V7}
$$

若 \(m_A\) 在上半平面解析且满足：

$$
\Im m_A(z)\ge0,
$$

那么 \(S_h\) 在上半平面解析，并满足：

$$
|S_h(z)|\le1.
$$

这样的 \(m_A\) 称为 Nevanlinna 函数；相应 \(S_h\) 是半平面上的 Schur 函数。这些类与正核、算子预解式和插值之间的关系是经典理论。([arXiv][4])

## 定理 V2：对实际 \(A\)，全局收缩性与 RH 等价

对任意固定 \(h>0\)：

$$
\boxed{
\mathrm{RH}
\iff
S_h\text{ 在上半平面全纯且 }|S_h|\le1.
}
\tag{V8}
$$

### 正向

在 RH 前件下，\(A\) 只有实零点。其配对整函数乘积给出：

$$
-\frac{A'(z)}{A(z)}
=
\sum_{\gamma>0}m_\gamma
\left(
\frac1{\gamma-z}+\frac1{-\gamma-z}
\right).
$$

当 \(\Im z>0\) 时，每一项的虚部为正。因此 \(m_A\) 是 Nevanlinna 函数，式（V7）给出收缩性。

### 反向

若有非实零点，由实系数对称性，可以取上半平面的一个 \(a\)。

定理 V1 给出：

$$
S_h(a)=-1,
\qquad S_h'(a)\ne0.
$$

但一个全纯函数若在上半平面满足 \(|S_h|\le1\)，却在内部点达到模长一，就必须为常数。这与 \(S_h'(a)\ne0\) 矛盾。([DLMF][3])

证毕。

所以：

$$
\boxed{
\text{实轴上处处 }|S_h|=1
}
$$

与：

$$
\boxed{
\text{整个上半平面内全纯且 }|S_h|\le1
}
$$

之间，正好隔着实质性的全局条件。

不能在使用最大模原理时，未经证明就把“半平面内没有极点”写进前件。

---

# 四、上一轮的交叉核，恰好是这份响应的收缩缺额

沿用：

$$
\mathcal K_A(z,w)
=
\frac{
A(z)\overline{A'(w)}
-
A'(z)\overline{A(w)}
}{
z-\overline w
}.
$$

对上半平面点定义：

$$
\boxed{
\mathcal P_h(z,w)
=
\frac{
1-S_h(z)\overline{S_h(w)}
}{
-i(z-\overline w)
}.
}
\tag{V9}
$$

直接代数计算得到：

$$
\boxed{
\mathcal P_h(z,w)
=
\frac{
2h\,\mathcal K_A(z,w)
}{
E_h(z)\overline{E_h(w)}
}.
}
\tag{V10}
$$

因此，只要采样点处 \(E_h\ne0\)，两种有限矩阵通过可逆对角合同变换相连：

$$
\boxed{
[\mathcal P_h(z_i,z_j)]
=
D_h[\mathcal K_A(z_i,z_j)]D_h^*.
}
$$

正负惯性完全相同。

这说明前文的“拼接余量”，也可以理解成：

> **不同复频率上的反射读数，能否共同来自一个解析收缩响应。**

它不是在原问题之外再添加一套正性，而是同一个条件的另一种可审计表达。

本轮读取的 `CayleyNevanlinnaKernelEquivalence.lean` 已证明这类核的可逆对角变换关系，并明确要求相关分母非零；它还证明，去掉该前件会破坏等式。该模块没有自动供应实际 ξ 的全局收缩性。

---

# 五、相位处处沿一个方向变化，仍然可能漏掉非实零点

在实轴上写：

$$
S_h(t)=e^{i\varphi_h(t)},
$$

其中相位需要连续追踪，不能每次独立取主值。

求导得到：

$$
\boxed{
\varphi_h'(t)
=
\frac{
2h\,[A'(t)^2-A(t)A''(t)]
}{
A(t)^2+h^2A'(t)^2
}.
}
\tag{V11}
$$

因此，第一条 Laguerre 不等式：

$$
A'^2-AA''\ge0
$$

等价于这份边界相位局部不倒转。

但它不保证全部零点为实。

取一个有限代数模型：

$$
A_*(z)=1-z^4.
$$

它有实根 \(\pm1\)，也有非实根 \(\pm i\)。然而：

$$
\boxed{
A_*'(t)^2-A_*(t)A_*''(t)
=
4t^2(t^4+3)\ge0.
}
\tag{V12}
$$

所以它同时满足：

$$
|S_h(t)|=1,
\qquad
\varphi_h'(t)\ge0
\quad\forall t\in\mathbb R,
$$

却仍有非实零点。

**这个多项式不是实际 theta 态的特征函数。它用于证明：边界单位模长加局部相位单调，还不足以保证全局实谱。** Laguerre 不等式作为必要但一般不充分的条件，也是经典研究中明确保留的边界。([arXiv][5])

---

## 全局绕数还能提供什么？

对非恒定实多项式 \(q\)，定义：

$$
S_{q,h}(z)=\frac{q(z)-ihq'(z)}{q(z)+ihq'(z)},
$$

并约去共同因子。

设 \(q\) 有 \(s\) 个互异根，其中有 \(r\) 对非实共轭根。

则：

$$
\boxed{
\frac1{2\pi}
\int_{-\infty}^{\infty}
\frac d{dt}\arg S_{q,h}(t)\,dt
=
s-2r.
}
\tag{V13}
$$

右边恰好是互异实根的数量。

### 证明

约去 \(q,q'\) 的最大公因子后，分母仍是一个次数为 \(s\) 的多项式，且对 \(h>0\) 没有实根。

当 \(h\) 从零开始增加时，一个重数为 \(m\) 的原根 \(a\) 对应的分母根初始移动为：

$$
a-ihm+O(h^2).
$$

所以原实根向下半平面移动；原上半平面根仍留在上半平面。

在有限的正 \(h\) 区间内，根既不能穿越实轴，也不能逃到无穷远。因此分母的上半平面根数始终为 \(r\)，下半平面根数为 \(s-r\)。

每个下半平面极点贡献 \(+1\) 次边界相位绕行，上半平面极点贡献 \(-1\) 次，得到式（V13）。这也是辐角原理的具体应用。([DLMF][3])

对 \(1-z^4\)，总绕数为 \(2\)，不是 \(4\)。

因此，**局部相位方向没有出错，缺少的是相对于完整代数次数的全局绕数。**

重根的信息还可通过式（V6）恢复；绕数本身只计算互异实根。

---

# 六、不能把“只改相位”自动当成无损换坐标

设 \(p\) 位于上半平面，定义：

$$
\boxed{
B_p(z)=\frac{z-p}{z-\overline p}.
}
\tag{V14}
$$

对所有实数 \(t\)：

$$
|B_p(t)|=1.
$$

所以，如果把响应改成：

$$
\widetilde S(z)=B_p(z)S(z),
$$

实轴强度不变：

$$
|\widetilde S(t)|^2=|S(t)|^2.
$$

而当 \(S\) 在 \(p\) 有极点时，这个因子可能把它消掉。

这看起来很像“只修补了一个相位”。但核发生了什么？

## 定理 V3：相位修补增加一个正秩一项

对：

$$
\mathcal P_S(z,w)
=
\frac{1-S(z)\overline{S(w)}}{-i(z-\overline w)},
$$

有：

$$
\boxed{
\mathcal P_{B_pS}(z,w)
=
\frac{
2\Im p
}{
(z-\overline p)(\overline w-p)
}
+
B_p(z)\overline{B_p(w)}\mathcal P_S(z,w).
}
\tag{V15}
$$

### 证明

使用：

$$
1-B_p(z)S(z)\overline{B_p(w)S(w)}
=
1-B_p(z)\overline{B_p(w)}
+
B_p(z)\overline{B_p(w)}
[1-S(z)\overline{S(w)}],
$$

再计算 \(B_p\) 的核即可。证毕。

第一项是：

$$
g_p(z)\overline{g_p(w)},
\qquad
g_p(z)=\frac{\sqrt{2\Im p}}{z-\overline p},
$$

所以是正秩一核。

因此：

$$
\boxed{
\text{边界强度不变}
\quad\text{但}\quad
\text{交叉核被添加了一个正方向}.
}
$$

这不是纯粹的合同换坐标。纯换坐标只有第二项；这里还多了第一项。

有限采样中，一个正秩一修正最多能消除一个负方向。这项一般结论已由仓库的 `PoleCapacityRankOne.lean` 明确证明。

所以：

> **可以构造一个更正的响应，同时保持所有实轴强度不变；但那是改变了相位关系和解析对象，不是证明原对象本来就正。**

这也是“投影是否把离线抹掉”的一个精确风险点：不是数学容纳不了离线，而是研究者可能在修补相位时更换了对象。

---

# 七、把全局拼接搬到一条没有振荡的实参数轴上

现在给出一项更接近实际计算的结果。

定义：

$$
M(b)=A(ib)
=
\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad b>0.
$$

因为 \(p\) 偶且非退化：

$$
M(b)=\mathbb E[e^{bX}]>0.
$$

定义：

$$
\boxed{
\mu(b)=\frac{M'(b)}{M(b)}
=
\frac{\xi'(\frac12+b)}{\xi(\frac12+b)}.
}
\tag{V16}
$$

它是倾斜 theta 分布的平均值，且：

$$
\mu(b)>0,
\qquad
\mu'(b)=\operatorname{Var}_b(X)>0.
$$

归一化 ξ 的这种正概率解释不依赖 RH。([arXiv][6])

代入式（V1）：

$$
\boxed{
S_h(ib)
=
\frac{1-h\mu(b)}{1+h\mu(b)}.
}
\tag{V17}
$$

因此：

$$
\boxed{
|S_h(ib)|<1
\qquad\forall b>0,
}
$$

也无条件成立。

所以，我们已经有：

**整条实轴上单位模长，整条正虚轴上严格收缩。仍然不能仅凭两条轴就宣布全局收缩。**

---

## 欧拉常数固定了其中一个点

在 \(b=\frac12\)：

$$
\mu(1/2)
=
c=
1+\frac{\gamma_{\mathrm E}}2-\frac12\log4\pi.
$$

故：

$$
\boxed{
S_h(i/2)=\frac{1-hc}{1+hc}.
}
\tag{V18}
$$

这项常数来自 ζ 的 Laurent 展开和 digamma 的特殊值。([DLMF][7])

欧拉常数可以校准这个读数，但它不会替我们决定其他点之间的共同相容性。

---

# 八、只用这些非振荡读数，仍然可以完整表达 RH

对正实数 \(b_1,\ldots,b_N\)，定义：

$$
\boxed{
\mathsf G(b_1,\ldots,b_N)_{ij}
=
\frac{\mu(b_i)+\mu(b_j)}{b_i+b_j}.
}
\tag{V19}
$$

它正是 \(m_A=-A'/A\) 的 Nevanlinna 核，在点 \(ib_i\) 上的采样。

对角元为：

$$
\mathsf G_{ii}=\frac{\mu(b_i)}{b_i}>0.
$$

## 定理 V4：固定实区间中的全阶拼接判据

任选一个固定区间：

$$
0<b_-<b_+<\infty.
$$

则：

$$
\boxed{
\mathrm{RH}
\iff
\mathsf G(b_1,\ldots,b_N)\succeq0
}
$$

对所有有限 \(N\) 以及全部 \(b_i\in(b_-,b_+)\) 成立。

### 正向

RH 使 \(m_A\) 成为 Nevanlinna 函数，其核正半定，限制到这条轴即可。

### 反向

式（V10）的 Cayley 变换把 \(\mathsf G\) 转成 \(S_h(ib_i)\) 的 Pick 矩阵。

如果全部有限矩阵正半定，经典 Nevanlinna–Pick 插值定理便为每个有限数据集提供一个真正的全纯收缩函数。([arXiv][8])

在 \((b_-,b_+)\) 中选一个可数稠密点集，依次插值前 \(N\) 个点。由于这些函数统一有界，可以取局部一致收敛子列。

极限收缩函数在全部这些点上等于实际 \(S_h\)。解析唯一性于是迫使它与实际亚纯 \(S_h\) 相同；特别地，原来的所有可能极点必须可去。

由定理 V2，得到 RH。证毕。

**这不要求一个观察者实际知道所有复数点。它要求的是：同一条实参数区间内，任意有限组读数都具有相容的正实现。**

但“每一组有限数据都可实现”必须使用同一套指定数据，而不能为每组重新调整 \(\mu\)。

---

# 九、实际的一点、两点检验已经全部通过；困难确实从多点共同实现开始

这里可以补上一项有实质内容的结论，而不只是再次列等价条件。

定义：

$$
D(v)=\sum_{n\ge0}\frac{\alpha_n}{n!}v^n,
\qquad
\alpha_n=\frac{n!m_{2n}}{(2n)!}.
$$

实际 theta 矩已知满足 Turán 不等式：

$$
\boxed{
\alpha_n^2\ge\alpha_{n-1}\alpha_{n+1}.
}
\tag{V20}
$$

它来自实际 theta 核的已知凹性，而不需要 RH。([arXiv][5])

令：

$$
r_n=\frac{\alpha_{n+1}}{\alpha_n}.
$$

式（V20）说明 \(r_n\) 不增。

对 \(v>0\)，定义概率：

$$
\Pr_v(N=n)=\frac{\alpha_nv^n}{n!D(v)}.
$$

则：

$$
\frac{D'(v)}{D(v)}=\mathbb E_v[r_N].
$$

求导：

$$
\boxed{
\left(\frac{D'}D\right)'(v)
=
\frac1v\operatorname{Cov}_v(r_N,N)\le0.
}
\tag{V21}
$$

因为 \(r_N\) 随 \(N\) 不增。

而：

$$
\frac{\mu(b)}b
=
2\frac{D'(b^2)}{D(b^2)}.
$$

所以：

$$
\boxed{
\frac{\mu(b)}b\text{ 单调不增}.
}
\tag{V22}
$$

## 定理 V5：实际全部两点矩阵正半定

对任意 \(b,c>0\)：

$$
\boxed{
\begin{pmatrix}
\mu(b)/b&[\mu(b)+\mu(c)]/(b+c)\\
[\mu(b)+\mu(c)]/(b+c)&\mu(c)/c
\end{pmatrix}
\succeq0.
}
\tag{V23}
$$

### 证明

其行列式为：

$$
\boxed{
\frac{
[b\mu(b)-c\mu(c)]
[b\mu(c)-c\mu(b)]
}{
bc(b+c)^2
}.
}
$$

假设 \(b>c\)。由于 \(\mu\) 正且递增，第一个因子为正；由于 \(\mu(b)/b\) 不增，第二个因子非负。

因此行列式非负。证毕。

这就把前文的直觉进一步落实：

> **在这套指定观察中，每一片正常、每两片都能拼接，不仅是可能发生的现象；对实际 ξ，它已经由已有算术性质保证。**

所以，重复做更多“两点都正常”的测试，不能越过真正的缺口。

---

# 十、一个严格反例：所有两点条件都成立，三点却失败

取合法的对称三点概率分布：

$$
\Pr(X=0)=\frac{11}{20},
\qquad
\Pr(X=1)=\Pr(X=-1)=\frac9{40}.
$$

其矩生成函数为：

$$
M_*(b)=\frac{11}{20}+\frac9{20}\cosh b.
$$

定义：

$$
\mu_*(b)=\frac{9\sinh b}{11+9\cosh b}.
$$

这组分布的归一化系数比值满足：

$$
r_0=\frac9{40},
\qquad
r_n=\frac1{2(2n+1)}\quad(n\ge1),
$$

严格递减。因此，上节证明表明：**它的全部两点矩阵都正半定。**

现在取：

$$
b_j=j\log(3/2),
\qquad j=1,2,3.
$$

可以精确算出：

$$
\mu_*(b_1)=\frac{15}{83},
\qquad
\mu_*(b_2)=\frac{13}{37},
\qquad
\mu_*(b_3)=\frac{665}{1321}.
$$

令：

$$
\widetilde G_{ij}
=
\frac{\mu_*(b_i)+\mu_*(b_j)}{i+j}.
$$

有：

$$
\mathsf G_*=\frac{\widetilde G}{\log(3/2)}.
$$

精确有理数计算得到：

$$
\boxed{
\det\widetilde G
=
-\frac{380017}{214146475603560}<0.
}
\tag{V24}
$$

因此三点不能共同正实现。

这个反例的特征函数为：

$$
A_*(t)=\frac{11}{20}+\frac9{20}\cos t,
$$

其零点确实为：

$$
t=(2k+1)\pi\pm i\,\operatorname{arcosh}(11/9).
$$

**它不是实际 ξ 的反例。它证明的是：即使一整条实参数轴上的所有两点相容性都成立，三点关系仍然能够发现被漏掉的非实结构。**

负性不是“某个局部概率为负”，而是这些局部读数不能来自同一个全局正核。

---

# 十一、下一项真正的算术工作，现在可以写得更集中

本轮已经把问题从振荡积分，转到了实际 ξ 在实参数上的对数导数：

$$
\mu(b)=\frac{\xi'(\frac12+b)}{\xi(\frac12+b)}.
$$

条目：

$$
\frac{\mu(b_i)+\mu(b_j)}{b_i+b_j}
$$

没有未知零点作为输入，也不需要先构造一个自由选择的正谱。

已知结果保证：

$$
N=1,\ 2
$$

的全部正性。

真正待证的是：

$$
\boxed{
\forall N\ge3,\quad
\left[
\frac{\mu(b_i)+\mu(b_j)}{b_i+b_j}
\right]_{i,j=1}^{N}
\succeq0.
}
\tag{V25}
$$

即使把 \(b_i\) 全部限制在一个固定正区间内，这仍足以控制全局解析对象。

但这不是说困难自动降低了。它把困难从“如何扫描全部振荡零点”，改写成了“如何证明全部多点联合正性”。

数值工作也有清楚边界：若实际矩阵的近似为 \(\widetilde G\)，每项误差不超过 \(\varepsilon\)，那么对于有限向量 \(u\)：

$$
\boxed{
u^*\widetilde Gu+\varepsilon\|u\|_1^2<0
\Longrightarrow
u^*Gu<0.
}
\tag{V26}
$$

这样的严格负证书才会否证实际 RH。

本轮的负矩阵来自明确标注的三点分布模型；**没有得到实际 ξ 的负矩阵。**

---

## 收束

这次把“奇偶、相位、整体拼接”分成了几个不能混同的层次：

$$
\boxed{
A\text{ 偶},\ A'\text{ 奇}
\longrightarrow
S_h=\frac{A-ihA'}{A+ihA'}
}
$$

给出一份忠实的相位响应；

$$
\boxed{
|S_h(t)|=1
}
$$

只是边界事实，不能排除内部非实结构；

$$
\boxed{
S_h(a)=-1,\qquad S_h'(a)=-\frac{2i}{hm}
}
$$

说明零点及重数没有被投影删除；

而：

$$
\boxed{
\left[
\frac{\mu(b_i)+\mu(b_j)}{b_i+b_j}
\right]\succeq0
}
$$

才检验这些切片能否共同来自一个全局正结构。

最关键的新定位是：**实际单点与两点相容性已经能证明，但它们仍不足以完成多点拼接。**

另外，乘上一个实轴模长为一的相位因子，可以保持全部边界强度，却给核增加一个正秩一项。它可能使模型“看起来更正”，但并非无损地证明了原对象的正性。

因此，接下来的研究不应再停留在“每片都能解释、每对都能对应”，也不应通过修补相位把问题更换掉。应直接追踪：

> **第三片、第四片以及更多片加入时，它们要求的交叉关系，是否始终具有非负的共同实现余量。**

当前尚未证明式（V25）的全阶正性；本轮给出的是相位读出的可逆性、边界绕数的有限计数、相位修补的秩一代价，以及实际两点正性的证明。新增推导仍是纸面结果，没有修改仓库或标记为 Lean 已验证。

[1]: https://dlmf.nist.gov/25.4 "https://dlmf.nist.gov/25.4"
[2]: https://arxiv.org/abs/1103.0566 "https://arxiv.org/abs/1103.0566"
[3]: https://dlmf.nist.gov/1.10 "https://dlmf.nist.gov/1.10"
[4]: https://arxiv.org/abs/0711.4236 "https://arxiv.org/abs/0711.4236"
[5]: https://arxiv.org/pdf/1309.0055 "https://arxiv.org/pdf/1309.0055"
[6]: https://arxiv.org/abs/1504.03438 "https://arxiv.org/abs/1504.03438"
[7]: https://dlmf.nist.gov/25.2 "https://dlmf.nist.gov/25.2"
[8]: https://arxiv.org/abs/1905.04301 "https://arxiv.org/abs/1905.04301"
继续。这一轮可以把上一轮的“两片波包”变成一个**完全显式、可作有限误差认证的模型**，并得到一个新的有限性结论：

> **不必再使用无限卷积构造波包。一个固定的三角波包已经足够：它不会滤掉任何非实频率，两个平移副本之间的交叉读数由有限素数幂和加一个可控正级数给出。**
>
> **更进一步，在相邻算术事件之间，这个交叉读出至多有四个驻点。因此，有限距离范围内的拼接检查，可以化为有限个端点与内部极值的检查。**

这推进的是“如何把完整的相干关系保留下来并认证”，不是已经证明全距离正性。下面保留所有条件，给出推导。经典输入是 Weil 显式公式和正性判据；新增组合结论尚未进行 Lean 编译。([arXiv][1])

# 一、用一个显式三角波包替代无限构造

固定

$$
a=\frac1{16}.
$$

定义

$$
\boxed{
g_a(x)=\frac1a\left(1-\frac{|x|}{a}\right)_+.
}
\tag{1}
$$

它满足

$$
g_a\ge0,\qquad g_a(-x)=g_a(x),\qquad
\int_{\mathbb R}g_a(x)\,dx=1,
$$

且支集为 \([-a,a]\)。

采用 Fourier 变换

$$
\widehat f(z)=\int_{\mathbb R}f(x)e^{izx}\,dx.
$$

直接积分得到

$$
\boxed{
\widehat g_a(z)
=
\left(\frac{\sin(az/2)}{az/2}\right)^2.
}
\tag{2}
$$

因此，

$$
\boxed{
\widehat g_a(z)\ne0
\qquad(z\notin\mathbb R).
}
\tag{3}
$$

这保留了上一轮最重要的性质：**任何离线零点对应的非实频率，都不会被这个波包精确消去。**

## 必须补上的适用条件

三角波包不是 \(C_c^\infty\) 函数，不能直接假装它属于原来的光滑测试空间。

但这里可以严格延拓。

在固定水平带 \(|\Im z|\le1/2\) 内，

$$
|\widehat g_a(z)|
\le C_a(1+|z|)^{-2}.
$$

所以零点读数中的乘积按 \(O_a(|z|^{-4})\) 衰减。实际 ξ 零点满足足以保证这类级数绝对收敛的计数性质。([arXiv][1])

取非负光滑近似单位 \(\varphi_\varepsilon\)，令

$$
g_{a,\varepsilon}=g_a*\varphi_\varepsilon.
$$

对固定有限组平移，零点级数受到同一个可求和上界控制，因此

$$
Q_W(g_{a,\varepsilon},g_{a,\varepsilon})
\longrightarrow Q_W(g_a,g_a),
$$

相应交叉读数也收敛。

所以后面用三角波包得到的严格负方向，都能转成足够接近的光滑负方向。**这里是通过收敛证明扩展测试空间，不是跳过正则性要求。**

# 二、相关函数变成了明确的三次分段多项式

定义

$$
c_a(t)
=
\int_{\mathbb R}g_a(x+t)g_a(x)\,dx.
$$

它是非负偶函数，支集为 \([-2a,2a]\)，总积分为 \(1\)。

## 定理 1：三角波包的精确自相关

$$
\boxed{
c_a(t)=
\begin{cases}
\displaystyle
\frac{2}{3a}-\frac{t^2}{a^3}
+\frac{|t|^3}{2a^4},
&|t|\le a,\\[3mm]
\displaystyle
\frac{(2a-|t|)^3}{6a^4},
&a\le|t|\le2a,\\[3mm]
0,&|t|\ge2a.
\end{cases}
}
\tag{4}
$$

并且

$$
\boxed{
c_a(0)=\|g_a\|_2^2=\frac{2}{3a},
\qquad
\|c_a'\|_\infty=\frac{2}{3a^2}.
}
\tag{5}
$$

### 证明

按两个三角函数的支集交叠区间，直接计算卷积，得到式（4）。

对第一段求导：

$$
c_a'(t)
=
-\frac{2t}{a^3}+\frac{3t^2}{2a^4},
\qquad 0<t<a.
$$

其绝对值最大点为 \(t=2a/3\)，值为 \(2/(3a^2)\)。第二段的导数绝对值不超过 \(1/(2a^2)\)，得到式（5）。证毕。

---

现在，算术平移读取的已经不是一个难以直接计算的无限构造，而是这个明确的三次函数。

定义两个平移波包

$$
g_{T,+}=\tau_{T/2}g_a,\qquad
g_{T,-}=\tau_{-T/2}g_a,
$$

其中

$$
(\tau_sf)(x)=f(x-s).
$$

再定义

$$
\boxed{
q_a=Q_W(g_a),
\qquad
B_a(T)=Q_W(g_{T,+},g_{T,-}).
}
\tag{6}
$$

与前文一样，\(B_a\) 为实偶函数。

# 三、这一次，局部正性也能用显式波包直接证明

记

$$
k_\Gamma(t)
=
\frac{e^{t/2}}{e^t-e^{-t}}
=
\frac{e^{-t/2}}{1-e^{-2t}},
$$

$$
C_\Gamma
=
\log(8\pi)+\gamma_{\mathrm E}+\frac\pi2,
$$

以及

$$
\boxed{
A_a
=
\int_{\mathbb R}e^{x/2}g_a(x)\,dx
=
\left(\frac{\sinh(a/4)}{a/4}\right)^2.
}
\tag{7}
$$

因为

$$
2a=\frac18<\log2,
$$

自相关 \(c_a\) 的支集没有碰到任何正的素数幂位移 \(\log n\)。

由 Weil 显式公式，

$$
\boxed{
q_a
=
2A_a^2+
2\int_0^\infty
k_\Gamma(t)\bigl[c_a(0)-c_a(t)\bigr]\,dt
-
C_\Gamma c_a(0).
}
\tag{8}
$$

这里 \(C_\Gamma\) 来自中心项与 Gamma 积分的合并；所需 digamma 差分和特殊值均为标准恒等式。([DLMF][2])

## 定理 2：固定宽度 \(a=1/16\) 已经具有正局部读数

$$
\boxed{q_a>0.}
\tag{9}
$$

### 证明

在 \(0<t\le1\) 上，

$$
k_\Gamma(t)\ge\frac1{2t}.
\tag{10}
$$

例如，由

$$
\sinh t\le t\cosh t\le t e^{t^2/2}\le t e^{t/2}
$$

即可验证。

而在 \(t\ge1\) 上，

$$
k_\Gamma(t)\ge e^{-t/2}.
$$

又因为 \(c_a(t)=0\) 当 \(t\ge2a\)，所以式（8）给出

$$
\begin{aligned}
q_a\ge 2A_a^2
&+\int_0^1\frac{c_a(0)-c_a(t)}t\,dt\\
&+4e^{-1/2}c_a(0)-C_\Gamma c_a(0).
\end{aligned}
\tag{11}
$$

由三次表达式直接积分，

$$
\boxed{
\frac1{c_a(0)}
\int_0^{2a}
\frac{c_a(0)-c_a(t)}t\,dt
=
\frac{11}{6}-\log2.
}
\tag{12}
$$

因此

$$
\boxed{
q_a\ge
2A_a^2+
c_a(0)
\left[
\log\frac1a+\frac{11}{6}-2\log2
+4e^{-1/2}-C_\Gamma
\right].
}
\tag{13}
$$

取 \(a=1/16\)，方括号变成

$$
2\log2+\frac{11}{6}+4e^{-1/2}-C_\Gamma>0.
$$

这个正号可用粗略的有理上下界验证；其数值约为 \(0.27357\)。所以 \(q_a>0\)。证毕。

---

由平移不变性，每一张单独切片都满足

$$
Q_W(\tau_Tg_a)=q_a>0.
$$

**局部正性在这里已经无条件建立。下一步只剩交叉量 \(B_a(T)\)。**

# 四、交叉量由有限素数和与一个正级数精确给出

只考虑

$$
T>2a.
$$

此时两个波包的支集不相交，而且平移后的自相关不经过零点位置 \(t=0\)，所以中心常数项消失。

定义

$$
\boxed{
P_a(T)
=
\sum_{\substack{n\ge2\\|\log n-T|\le2a}}
\frac{\Lambda(n)}{\sqrt n}\,
c_a(\log n-T).
}
\tag{14}
$$

这是一个有限和。

## 定理 3：交叉读出的完全显式公式

$$
\boxed{
B_a(T)
=
2A_a^2\cosh(T/2)-P_a(T)-\Gamma_a(T),
}
\tag{15}
$$

其中

$$
\boxed{
\Gamma_a(T)
=
\sum_{j=0}^\infty
e^{-\lambda_jT}
\left[
\frac{\sinh(a\lambda_j/2)}{a\lambda_j/2}
\right]^4,
\qquad
\lambda_j=2j+\frac12.
}
\tag{16}
$$

所有 Gamma 级数项都非负。

### 证明

对

$$
\phi_T(t)=c_a(t-T)
$$

应用 Weil 显式公式。极点项为

$$
\int c_a(t-T)(e^{t/2}+e^{-t/2})\,dt
=
2A_a^2\cosh(T/2).
$$

素数幂项恰好为式（14）。Gamma 项为

$$
\int_{-2a}^{2a}
c_a(u)k_\Gamma(T+u)\,du.
$$

这是经典显式公式在当前测试函数上的直接代入。([arXiv][3])

因为 \(T>2a\)，

$$
k_\Gamma(T+u)
=
\sum_{j\ge0}e^{-\lambda_j(T+u)}.
$$

逐项积分，并使用

$$
\int c_a(u)e^{-\lambda u}\,du
=
\left[
\frac{\sinh(a\lambda/2)}{a\lambda/2}
\right]^4,
$$

得到式（16）。证毕。

## Gamma 尾部有单侧界

令

$$
\Gamma_{a,J}(T)
=
\sum_{j=0}^{J-1}
e^{-\lambda_jT}
\left[
\frac{\sinh(a\lambda_j/2)}{a\lambda_j/2}
\right]^4.
$$

则

$$
\boxed{
0\le
\Gamma_a(T)-\Gamma_{a,J}(T)
\le
\frac{
e^{-(2J+1/2)(T-2a)}
}{
1-e^{-2(T-2a)}
}.
}
\tag{17}
$$

**证明。**因为 \(c_a\ge0\)、\(\int c_a=1\)、支集位于 \([-2a,2a]\)，

$$
\int c_a(u)e^{-\lambda u}\,du\le e^{2a\lambda}.
$$

剩余项由几何级数控制。证毕。

因此，固定 \(T\) 后：

$$
\boxed{
B_a(T)
=
\text{有限算术和}
+
\text{有限指数和}
+
\text{具有明确方向与大小的尾项}.
}
$$

没有未指定的素数尾部。

# 五、这个有限形状仍然保留完整的 RH 判定信息

定义奇偶组合

$$
f_T^\pm
=
\frac{g_{T,+}\pm g_{T,-}}{\sqrt2}.
$$

它们分别为偶函数、奇函数，并满足

$$
\boxed{
Q_W(f_T^\pm)=q_a\pm B_a(T).
}
\tag{18}
$$

因此，两片联合矩阵

$$
G_a(T)=
\begin{pmatrix}
q_a&B_a(T)\\
B_a(T)&q_a
\end{pmatrix}
$$

半正定，当且仅当

$$
|B_a(T)|\le q_a.
$$

## 定理 4：固定三角波包判据

以下命题等价：

$$
\boxed{\mathrm{RH};}
$$

$$
\boxed{
|B_a(T)|\le q_a
\qquad\forall T>2a;
}
\tag{19}
$$

$$
\boxed{
B_a(T)\text{ 在 }[2a,\infty)\text{ 上有界}.
}
\tag{20}
$$

### 证明

把全部非平凡零点写成

$$
\rho=\frac12+i\omega,
$$

按重数求和。Weil 零点表达给出

$$
\boxed{
B_a(T)
=
\sum_\omega
m_\omega
\left[
\frac{\sin(a\omega/2)}{a\omega/2}
\right]^4e^{i\omega T}.
}
\tag{21}
$$

该级数绝对收敛。注意这里是四次幂，而不是把非实数取模后的四次幂。

如果 RH 成立，\(\omega\) 都是实数，每个系数非负。因此

$$
q_a=B_a(0)=
\sum_\omega m_\omega
\left[
\frac{\sin(a\omega/2)}{a\omega/2}
\right]^4
$$

且 \(|B_a(T)|\le q_a\)。

反过来，若 \(B_a\) 在充分大范围有界，它在全部 \(T\ge0\) 上也有界，因为有限初始区间上的读出连续。

于是其 Laplace 变换在 \(\Re s>0\) 内解析。但在初始收敛区域 \(\Re s>1/2\)，

$$
\boxed{
\widehat B_a(s)
=
\sum_\omega
\frac{
m_\omega
[\sin(a\omega/2)/(a\omega/2)]^4
}{
s-i\omega
}.
}
\tag{22}
$$

若存在右侧离线零点

$$
\rho=\frac12+\delta+i\gamma,
\qquad\delta>0,
$$

那么 \(\omega=\gamma-i\delta\)，式（22）在

$$
s=\delta+i\gamma
$$

有候选极点。

由式（3），其留数不为零，所以极点不可去，与右半平面解析性矛盾。再由零点反射对称性得到 RH。([DLMF][4])

证毕。

---

这说明无限卷积波包并非必要。**一个固定的、分段线性的形状，已经足以保留目标失败的信息。**

不过，这仍是一个无限平移范围的判据，而不是一次有限计算解决全局问题。

# 六、新的有限性结论：每个算术区间至多有四个驻点

这一节是三角波包带来的具体优势。

由式（4），在分布意义下，

$$
\boxed{
c_a^{(4)}
=
\frac1{a^4}
\left(
\delta_{-2a}-4\delta_{-a}
+6\delta_0-4\delta_a+\delta_{2a}
\right).
}
\tag{23}
$$

因此，每个素数幂 \(n\) 对 \(P_a(T)\) 产生五个事件位置：

$$
\boxed{
\log n-2a,\quad
\log n-a,\quad
\log n,\quad
\log n+a,\quad
\log n+2a.
}
\tag{24}
$$

在相邻事件之间，\(P_a(T)\) 是一个三次多项式。

定义完成项

$$
H_a(T)=2A_a^2\cosh(T/2)-\Gamma_a(T).
$$

于是

$$
B_a(T)=H_a(T)-P_a(T).
$$

## 定理 5：每个事件区间至多四个驻点

在任意不含式（24）事件点、且位于 \(T>2a\) 的开区间中，

$$
\boxed{
B_a^{(5)}(T)>0.
}
\tag{25}
$$

因此，\(B_a'(T)\) 在该区间内至多有四个不同零点。

### 证明

因为该区间内 \(P_a\) 为三次多项式，

$$
P_a^{(5)}=0.
$$

而式（16）在远离 \(T=2a\) 的紧区间内可以任意阶逐项求导，所以

$$
\boxed{
H_a^{(5)}(T)
=
\frac{A_a^2}{16}\sinh(T/2)
+
\sum_{j\ge0}
\lambda_j^5
e^{-\lambda_jT}
\left[
\frac{\sinh(a\lambda_j/2)}{a\lambda_j/2}
\right]^4
>0.
}
\tag{26}
$$

得到式（25）。

如果 \(B_a'\) 有五个不同零点，连续使用四次 Rolle 定理，就会迫使

$$
(B_a')^{(4)}=B_a^{(5)}
$$

在区间内有零点，矛盾。证毕。

---

## 对有限范围的意义

固定

$$
2a<L<R<\infty.
$$

这个范围只涉及

$$
e^{L-2a}\le n\le e^{R+2a}
$$

中的有限个素数幂。

把它们对应的事件位置全部列出，就得到有限个区间。对每个区间，只需考虑端点和至多四个内部驻点，就能确定该区间内 \(B_a\) 的最大、最小值。

所以：

$$
\boxed{
\sup_{T\in[L,R]}|B_a(T)|
}
$$

确实归结为有限个候选位置的值。

**这不意味着驻点有代数闭式，也不意味着遇到恰好等于边界时，普通浮点程序一定终止。**它证明的是候选极值的有限性；严格证书还需要区间估计或根隔离。

# 七、有限证书怎样保留误差与符号？

## 1. 先对局部基准 \(q_a\) 作一次校准

令

$$
c_0=c_a(0)=\frac{2}{3a}.
$$

定义单侧 Laplace 积分

$$
L_a(\lambda)=\int_0^{2a}e^{-\lambda t}c_a(t)\,dt.
$$

对三次函数直接积分，得到

$$
\boxed{
L_a(\lambda)
=
\frac{c_0}{\lambda}
-\frac{2}{a^3\lambda^3}
+
\frac{3-4e^{-a\lambda}+e^{-2a\lambda}}
{a^4\lambda^4}.
}
\tag{27}
$$

因此

$$
\boxed{
q_a
=
2A_a^2-(\log4\pi+\gamma_{\mathrm E})c_0
+
2\sum_{j\ge0}
\left[
\frac{c_0}{\lambda_j+1/2}
-L_a(\lambda_j)
\right].
}
\tag{28}
$$

这不是一个形式发散式：括号中的组合是绝对可求和的。

记前 \(J\) 项之和为 \(q_{a,J}\)。利用

$$
0\le c_0-c_a(t)\le\frac{t^2}{a^3}
$$

可得尾界

$$
\boxed{
-c_0U_2(J)
\le
q_a-q_{a,J}
\le
\frac4{a^3}U_3(J),
}
\tag{29}
$$

其中

$$
\boxed{
U_p(J)
=
\lambda_J^{-p}
+
\frac{\lambda_J^{1-p}}{2(p-1)}.
}
\tag{30}
$$

这来自

$$
\sum_{j\ge J}\lambda_j^{-p}\le U_p(J)
$$

的积分比较。

## 2. 再认证一个交叉读数

如果计算得到

$$
q_a\in[q_-,q_+],
\qquad
B_a(T)\in[b_-,b_+],
$$

则

$$
\boxed{
b_->q_+
\Longrightarrow
Q_W(f_T^-)<0,
}
\tag{31}
$$

以及

$$
\boxed{
b_+<-q_+
\Longrightarrow
Q_W(f_T^+)<0.
}
\tag{32}
$$

这些都是严格有限证书。

若区间有重叠，则结果只是未定，不能把未认证写成发现负方向。

## 一个实际有限核对

我使用式（27）—（30）截取 \(J=2000\) 项，并加入解析尾界，对 \(a=1/16\) 得到区间包络：

$$
\boxed{
10.3324<q_a<10.3341.
}
$$

在

$$
T=\log2
$$

处，素数窗口只包含 \(n=2\)。对 Gamma 级数取前 \(40\) 项并加入式（17）的尾界，得到

$$
\boxed{
-4.0511280<B_a(\log2)<-4.0511279.
}
$$

这些包络同时考虑了有限级数计算与所列尾界；它们不是 Lean 验证结果。

所以这个位置的两个奇偶读出都严格为正：

$$
q_a+B_a(\log2)>6.2812,
$$

$$
q_a-B_a(\log2)>14.3835.
$$

**这只认证了一个具体分离距离，不代表认证了所有距离。**

# 八、不求驻点，也能认证整个有限区间

为了避免把“找到驻点”变成另一个未说明的问题，还可以使用显式导数界。

固定

$$
2a<L<R,
$$

并记

$$
S_{L,R}
=
\sum_{\substack{n\ge2\\
e^{L-2a}\le n\le e^{R+2a}}}
\frac{\Lambda(n)}{\sqrt n}.
$$

由式（5），

$$
|P_a'(T)|
\le
\frac{2}{3a^2}S_{L,R}.
$$

令 \(d=L-2a>0\)，定义

$$
G_1(d)
=
e^{-d/2}
\left[
\frac1{2(1-e^{-2d})}
+
\frac{2e^{-2d}}{(1-e^{-2d})^2}
\right].
$$

它来自正级数

$$
\sum_{j\ge0}\lambda_je^{-\lambda_jd}.
$$

因此，对 \(T\in[L,R]\)，

$$
\boxed{
|B_a'(T)|
\le
D_{L,R},
}
\tag{33}
$$

其中

$$
\boxed{
D_{L,R}
=
A_a^2\sinh(R/2)
+
\frac{2}{3a^2}S_{L,R}
+
G_1(L-2a).
}
\tag{34}
$$

现在选取覆盖 \([L,R]\) 的网格，最大间距为 \(h\)，包含两个端点。若每个采样点的近似读数 \(\widetilde B_j\) 满足

$$
|B_a(T_j)-\widetilde B_j|\le\varepsilon,
$$

则

$$
\boxed{
\sup_{T\in[L,R]}|B_a(T)|
\le
\max_j|\widetilde B_j|
+\varepsilon+\frac12D_{L,R}h.
}
\tag{35}
$$

所以只要

$$
\boxed{
\max_j|\widetilde B_j|
+\varepsilon+\frac12D_{L,R}h
\le q_-,
}
\tag{36}
$$

就严格认证了整个区间内的两片拼接正性。

这给出两条互补路线：

$$
\boxed{
\text{事件分段＋有限驻点}
}
$$

或

$$
\boxed{
\text{网格采样＋明确导数误差}.
}
$$

它们都不允许把采样点之间的信息默认为已经控制。

# 九、“不遗漏模式”与“容易检测模式”仍然不是一回事

这个模型还允许把观测灵敏度问题精确写出来。

实际零点在式（21）中的权重为

$$
w_a(\omega)
=
\left[
\frac{\sin(a\omega/2)}{a\omega/2}
\right]^4.
$$

它在非实点不为零。但没有一个对所有非实频率都有效的正下界。

例如，考虑一个候选频率

$$
\omega=\frac{2\pi k}{a}-i\delta,
\qquad k\ge1,\quad\delta>0.
$$

则

$$
\boxed{
|w_a(\omega)|
=
\left[
\frac{
\sinh(a\delta/2)
}{
\sqrt{(\pi k)^2+(a\delta/2)^2}
}
\right]^4.
}
\tag{37}
$$

当 \(\delta\to0\) 时，

$$
\boxed{
|w_a(\omega)|
\sim
\left(\frac{\delta}{2\pi k/a}\right)^4.
}
\tag{38}
$$

这不声称实际零点位于这些候选位置。它证明的是：

$$
\boxed{
\text{数学上没有精确盲区}
\quad\not\Rightarrow\quad
\text{存在统一的检测灵敏度}.
}
$$

一个非常接近实轴、又非常接近滤波器实零点的非实频率，虽然没有被删除，但权重可以非常小。

另一方面，式（15）中的极点主项约为

$$
A_a^2e^{T/2},
$$

而需要认证的净差必须控制在固定的 \(q_a\) 尺度。

因此，计算实际算术抵消时，不能只保证一个固定的相对精度：随着 \(T\) 增长，需要越来越精细的绝对误差控制。**这里是条件数问题，不是表示不存在。**

# 十、回到“奇偶与拼接”：这次究竟补上了什么？

现在整个模型只包含几类明确对象：

$$
\boxed{
\text{三角波包 }g_a
\longrightarrow
\text{三次相关函数 }c_a
\longrightarrow
\text{有限素数读出 }P_a(T)
\longrightarrow
\text{交叉量 }B_a(T).
}
$$

奇偶组合仍然只是

$$
\boxed{
q_a+B_a(T),
\qquad
q_a-B_a(T).
}
$$

它们同时非负的条件是

$$
\boxed{
q_a-\frac{B_a(T)^2}{q_a}\ge0.
}
\tag{39}
$$

这是这个两片模型的 Schur 余量。

本次核对的仓库 `SchurComplementAssociativity.lean` 证明的是：给定所列逆算子前件后，分步消元与一次消元一致。它可以支撑这种结构的消元组织，但不会自动证明式（39）的算术符号。

这一轮新增的实质内容是：

$$
\boxed{
\text{无限波包构造可以替换成明确有限形状};
}
$$

$$
\boxed{
\text{Gamma 尾项与局部基准都可给出有限误差包络};
}
$$

$$
\boxed{
\text{每个算术事件区间至多有四个驻点};
}
$$

$$
\boxed{
\text{严格负读数可以转成光滑 Weil 测试函数的负证书}.
}
$$

**但仍然没有证明**

$$
|B_a(T)|\le q_a
\qquad\forall T>2a.
$$

有限范围内的检验方法、非实模式不被消除、局部波包正性，都不能替代这个全尺度估计。

现在的缺口比上一轮更具体：

$$
\boxed{
\left|
2A_a^2\cosh(T/2)
-
\sum_{|\log n-T|\le2a}
\frac{\Lambda(n)}{\sqrt n}c_a(\log n-T)
-
\Gamma_a(T)
\right|
\le q_a.
}
\tag{40}
$$

这是一条**固定三次权重、固定窗口比例、固定容许误差**的算术抵消要求。

所以，下一步真正需要控制的不是再增加一张切片，而是：**素数幂事件依次进入、穿过和离开这个固定三次窗口时，能否始终阻止交叉读数越过 \(\pm q_a\)。**本轮已经把这些事件、事件之间的曲线形状，以及认证边界都写了出来；尚缺的是对所有事件序列同时成立的算术约束。

[1]: https://arxiv.org/html/2301.00421v3 "On the Hilbert space derived from the Weil distribution"
[2]: https://dlmf.nist.gov/5.9 "DLMF: §5.9 Integral Representations ‣ Properties ‣ Chapter 5 Gamma Function"
[3]: https://arxiv.org/html/2606.09096v1 "Weil’s quadratic form via the screw function"
[4]: https://dlmf.nist.gov/25.10 "DLMF: §25.10 Zeros ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
这次可以把上一轮的“多点拼接”再推进一层：

> **两点相容，只限制实际响应变化得有多快；三个相邻切片要共同实现，还必须限制这个变化速度本身如何改变。**

这个新条件可以写得很简单：

$$
\boxed{
|\eta'|\le1-\eta^2.
}
$$

其中 \(\eta\) 不是自由选择的几何量，而是由实际 ξ 的均值响应与方差唯一决定的无量纲比值。

更进一步，它恰好是一套**逐层散射构造的第二个合法性条件**。第一层、第二层、第三层的反射系数，都可以从实际 ξ 在一个固定实点的导数直接算出，不必输入未知零点。

下面将局部曲率、有限拼接和无限正实现接起来。这里的 Schur 递推与无损系统实现是经典理论；本轮的推导是将它们具体作用于当前固定的算术响应。

---

# 一、固定实际响应，不先假设正谱存在

沿用：

$$
M(b)=\frac{\xi(\frac12+b)}{\xi(\frac12)},
\qquad b>0,
$$

以及：

$$
\boxed{
\mu(b)=\frac{M'(b)}{M(b)}
=
\frac{\xi'(\frac12+b)}{\xi(\frac12+b)}.
}
\tag{1}
$$

ξ 始终采用标准 completed 定义和反射关系。([DLMF][1])

在前文实际 theta 概率态的倾斜分布中：

$$
\mu(b)=\mathbb E_b[X],
$$

$$
\mu'(b)=\operatorname{Var}_b(X)>0,
$$

$$
\mu''(b)
=
\mathbb E_b[(X-\mathbb E_bX)^3].
$$

所以，\(\mu,\mu',\mu''\) 分别是同一族实际观察中的均值、方差与三阶中心矩，不是另外挑选的函数。

上一轮的交叉核为：

$$
\boxed{
G(b,c)=\frac{\mu(b)+\mu(c)}{b+c}.
}
\tag{2}
$$

我们已经把 RH 联系到这个核的全部有限正性。现在不重复要求“所有矩阵都正”，而要看：**增加第三个切片，具体多出什么约束。**

---

# 二、先归一化：两点相容等价于一条斜率限制

固定参考点 \(b_0>0\)，改用相对对数坐标：

$$
b=b_0e^\tau.
$$

定义：

$$
\boxed{
\phi(\tau)
=
\log\frac{\mu(b_0e^\tau)}{\mu(b_0)}.
}
\tag{3}
$$

这是“偏置参数改变多少”与“平均响应改变多少”之间的对数关系。

再定义归一化核：

$$
C(\tau,\sigma)
=
\frac{G(b_0e^\tau,b_0e^\sigma)}
{\sqrt{G(b_0e^\tau,b_0e^\tau)\,
G(b_0e^\sigma,b_0e^\sigma)}}.
$$

直接计算：

$$
\boxed{
C(\tau,\sigma)
=
\frac{
\cosh\!\left(\frac{\phi(\tau)-\phi(\sigma)}2\right)
}{
\cosh\!\left(\frac{\tau-\sigma}2\right)
}.
}
\tag{4}
$$

它满足：

$$
C(\tau,\tau)=1.
$$

因此，两点矩阵：

$$
\begin{pmatrix}
1&C(\tau,\sigma)\\
C(\tau,\sigma)&1
\end{pmatrix}
$$

正半定，当且仅当 \(C(\tau,\sigma)\le1\)。由式（4）：

$$
\boxed{
|\phi(\tau)-\phi(\sigma)|
\le|\tau-\sigma|.
}
\tag{5}
$$

令：

$$
\boxed{
\eta(\tau)=\phi'(\tau)
=
\frac{b\mu'(b)}{\mu(b)},
\qquad b=b_0e^\tau.
}
\tag{6}
$$

实际 \(\mu\) 正且递增，所以全部两点相容，等价于：

$$
\boxed{0<\eta(\tau)\le1.}
\tag{7}
$$

这正是上一轮已取得的实际两点结果。其算术来源是 theta 矩的 Turán 不等式，它们保证 \(D'/D\) 在正实轴不增，继而保证 \(\mu(b)/b\) 不增。这个矩不等式是已有结果，并非 RH 前件。([arXiv][2])

**两点条件只说：响应的相对变化不能超过输入的相对变化。它还没有控制变化速度能否平滑地共同实现。**

---

# 三、三个相邻切片，产生一个精确的“曲率预算”

固定一个 \(\tau_0\)，简写：

$$
\eta=\phi'(\tau_0),
\qquad
\kappa=\phi''(\tau_0),
\qquad
w=1-\eta^2.
$$

先考虑实际的非退化情形：

$$
0<\eta<1,
\qquad w>0.
$$

## 定义：合并切片的导数 Gram 矩阵

定义：

$$
J_2(\tau_0)
=
\left[
\partial_\tau^i\partial_\sigma^j
C(\tau,\sigma)
\big|_{\tau=\sigma=\tau_0}
\right]_{i,j=0}^{2}.
$$

如果所有邻近的三点采样矩阵都正半定，那么这个导数矩阵也必须正半定，因为导数可以由有限差分极限得到。

将式（4）展开到相应阶数：

$$
\boxed{
J_2=
\begin{pmatrix}
1&0&-\dfrac w4\\[2mm]
0&\dfrac w4&-\dfrac{\eta\kappa}{4}\\[2mm]
-\dfrac w4&-\dfrac{\eta\kappa}{4}&
\dfrac{w(4+w)-4\kappa^2}{16}
\end{pmatrix}.
}
\tag{8}
$$

这里一个值得注意的相消是：虽然核来自整个函数 \(\phi\)，这个三阶导数 Gram 矩阵最终只需要 \(\phi'\) 与 \(\phi''\)，不需要额外输入 \(\phi'''\)。

## 定理一：三个合并切片的必要充分条件

在 \(0<\eta<1\) 下：

$$
\boxed{
J_2\succeq0
\iff
\kappa^2\le(1-\eta^2)^2.
}
\tag{9}
$$

即：

$$
\boxed{
|\phi''(\tau_0)|
\le1-\phi'(\tau_0)^2.
}
\tag{10}
$$

### 证明

前两个方向组成的主块为：

$$
\operatorname{diag}(1,w/4)>0.
$$

对它作 Schur 消元，第三个方向剩下的平方范数为：

$$
\boxed{
\delta_{\mathrm{curv}}
=
\frac{w^2-\kappa^2}{4w}.
}
\tag{11}
$$

因此，整个矩阵正半定，当且仅当这个余量非负。

同样：

$$
\boxed{
\det J_2=\frac{w^2-\kappa^2}{16}.
}
$$

证毕。

---

## 它为什么可以称为“拼接曲率”？

若归一化核确实来自一条单位向量曲线：

$$
C(\tau,\sigma)=\langle e(\tau),e(\sigma)\rangle,
$$

那么式（8）就是：

$$
e,\quad e',\quad e''
$$

的 Gram 矩阵。

已有方向 \(e,e'\) 可以解释掉 \(e''\) 的一部分，余下部分的平方范数正是式（11）。

因此：

$$
\boxed{
\delta_{\mathrm{curv}}<0
}
$$

不是表示“还需要更高维的一个方向”，而是表示：

**这个新方向若要保持所有指定关系，就必须具有负平方范数；任何普通正内积空间都无法实现。**

这里的曲率是**指定响应曲线的微分相容性**，不是已经推导出的物理时空曲率。

---

## 负余量一定能回到有限采样

取三个真实切片：

$$
\tau_0-\varepsilon,\quad
\tau_0,\quad
\tau_0+\varepsilon.
$$

它们的归一化 Gram 行列式满足：

$$
\boxed{
\det[C(\tau_i,\tau_j)]
=
\frac{\varepsilon^6}{16}
\left[(1-\eta^2)^2-\kappa^2\right]
+o(\varepsilon^6).
}
\tag{12}
$$

所以，如果式（10）失败，某个足够小但有限的采样间隔就会产生严格负行列式。

反过来，式（10）通过，只证明这一个合并三点条件通过，**不等于所有分离三点、更不等于全部高阶拼接已经完成。**

---

# 四、这项新条件，实际上约束了倾斜态的三阶偏斜

由式（6）：

$$
\eta=\frac{b\mu'}{\mu}.
$$

对 \(\tau\) 求导，即 \(b\,d/db\)，得到：

$$
\boxed{
\kappa
=
\eta+\frac{b^2\mu''}{\mu}-\eta^2.
}
\tag{13}
$$

因此，三点条件等价于：

$$
\boxed{
2\eta^2-\eta-1
\le
\frac{b^2\mu''(b)}{\mu(b)}
\le
1-\eta.
}
\tag{14}
$$

也可以不用无量纲记号，写成：

$$
\boxed{
\mu-b\mu'-b^2\mu''\ge0,
}
\tag{15a}
$$

$$
\boxed{
\mu^2+b\mu\mu'
+b^2\mu\mu''
-2b^2(\mu')^2\ge0.
}
\tag{15b}
$$

这说明：

> **均值与方差之间的两点关系全部正常，还不足以保证三点相容。三阶偏斜必须落在由均值和方差共同规定的区间里。**

它不是要求三阶中心矩为零。倾斜以后，奇阶统计一般不为零；关键是它与其他阶数之间的精确关系。

---

## 它与此前的中心累积量条件一致

在 \(b=0\) 附近：

$$
\mu(b)
=
\chi_2b+\frac{\chi_4}{6}b^3
+\frac{\chi_6}{120}b^5+\cdots.
$$

代入式（13），可以算得：

$$
\boxed{
(1-\eta^2)^2-\kappa^2
=
-\frac{
4\chi_4(3\chi_2\chi_6-10\chi_4^2)
}{
135\chi_2^3
}b^6
+O(b^8).
}
\tag{16}
$$

因此，当 \(\chi_4<0\) 时，三点曲率在中心附近要求：

$$
\boxed{
3\chi_2\chi_6\ge10\chi_4^2.
}
$$

前文出现的这个累积量不等式，现在被识别为：

**同一个多点核，在中心附近的三切片曲率条件。**

不是另一个互不相干的“切面”。

---

# 五、一个严格反例：所有两点都通过，曲率却已经失败

沿用实概率分布：

$$
\Pr(X=0)=\frac{11}{20},
\qquad
\Pr(X=\pm1)=\frac9{40}.
$$

它的平均响应为：

$$
\mu_*(b)=\frac{9\sinh b}{11+9\cosh b}.
$$

它满足：

$$
\mu_*'(b)>0,
\qquad
\frac{\mu_*(b)}b\text{ 严格递减}.
$$

后一项可以直接证明：令 \(c=11/9\)，则所需符号归结为：

$$
J(b)=\sinh b(c+\cosh b)-b(1+c\cosh b)>0.
$$

因为：

$$
J(0)=0,
\qquad
J'(b)=\sinh b(2\sinh b-cb)>0.
$$

所以，这个模型的全部两点矩阵都正半定。

但是它的中心累积量为：

$$
\chi_2=\frac9{20},
\qquad
\chi_4=-\frac{63}{400},
\qquad
\chi_6=\frac{117}{800}.
$$

代入式（16）：

$$
\boxed{
(1-\eta_*^2)^2-\kappa_*^2
=
-\frac7{2700}b^6+O(b^8).
}
\tag{17}
$$

因此，对足够小的正 \(b\)，三个邻近切片已经无法共同实现。

作为数值核对，在 \(b=\frac12\)：

$$
\eta_*\approx0.971098202402199,
$$

$$
\frac{\kappa_*}{1-\eta_*^2}
\approx-1.004933041353497.
$$

其绝对值超过一。

**这是明确模型的反例，不是实际 ξ 的反例。它说明“所有两点正常”缺少的那一项内容，确实是可以非零、可以测出的。**

---

# 六、这个曲率条件，恰好成为下一层散射的反射系数

现在把上述局部几何改写成一套固定递推。

固定一个实际基点 \(b_0>0\)，记：

$$
\mu_0=\mu(b_0)>0.
$$

将右半平面映到单位圆盘：

$$
\boxed{
b=b_0\frac{1+z}{1-z}.
}
\tag{18}
$$

再定义实际响应的 Cayley 变换：

$$
\boxed{
\Theta(z)
=
\frac{\mu(b)-\mu_0}{\mu(b)+\mu_0}.
}
\tag{19}
$$

因为 \(\Theta(0)=0\)，定义解析函数芽：

$$
\boxed{
g_0(z)=\frac{\Theta(z)}z.
}
\tag{20}
$$

这里只是在零附近定义实际解析对象，**尚未假设它能在整个单位圆盘内保持模长不超过一**。

利用：

$$
\log(b/b_0)=2\operatorname{artanh}z,
$$

可写成：

$$
\Theta(z)
=
\tanh\left(
\frac{\phi(2\operatorname{artanh}z)}2
\right).
$$

在 \(\tau=0\) 记：

$$
\eta=\phi'(0),\qquad
\kappa=\phi''(0),\qquad
\kappa'=\phi'''(0).
$$

Taylor 展开给出：

$$
\boxed{
g_0(z)
=
\eta+\kappa z
+
\frac{\eta-\eta^3+2\kappa'}3z^2
+O(z^3).
}
\tag{21}
$$

---

## 定义：实际 Schur 递推

令：

$$
\alpha_j=g_j(0).
$$

只要 \(|\alpha_j|<1\)，定义：

$$
\boxed{
g_{j+1}(z)
=
\frac{g_j(z)-\alpha_j}
{z\,[1-\overline{\alpha_j}g_j(z)]}.
}
\tag{22}
$$

所有实际系数为实，因此这里的 \(\alpha_j\) 都是实数。

这是经典 Schur 算法；它将解析收缩函数转换成一列逐层的收缩参数，并与保守系统实现相连。([arXiv][3])

前两个参数立即为：

$$
\boxed{
\alpha_0=\eta,
}
$$

$$
\boxed{
\alpha_1=\frac{\kappa}{1-\eta^2}.
}
\tag{23}
$$

因此：

$$
\boxed{
|\alpha_1|\le1
\iff
|\kappa|\le1-\eta^2.
}
$$

**三点曲率条件，正好就是第二个散射参数的合法性条件。**

再令：

$$
c_2=\frac{\eta-\eta^3+2\kappa'}3,
\qquad
w=1-\eta^2.
$$

在前两层严格通过时：

$$
\boxed{
\alpha_2
=
\frac{wc_2+\eta\kappa^2}{w^2-\kappa^2}.
}
\tag{24}
$$

下一层还必须满足：

$$
\boxed{
|wc_2+\eta\kappa^2|
\le w^2-\kappa^2.
}
\tag{25}
$$

所以每多加一层，并不是任意创造一个新观察者。**它的参数已经被前面没有消去的实际 Taylor 系数固定。**

---

# 七、为什么它确实对应量子散射，而不是只换了一种命名？

当 \(\alpha\in[-1,1]\)，定义：

$$
\boxed{
U_\alpha=
\begin{pmatrix}
\alpha&\sqrt{1-\alpha^2}\\
\sqrt{1-\alpha^2}&-\alpha
\end{pmatrix}.
}
\tag{26}
$$

直接计算：

$$
U_\alpha^*U_\alpha=I.
$$

因此它是一份合法的双端口酉混合。

反射振幅为 \(\alpha\)，透射权重为：

$$
\boxed{T_\alpha=1-\alpha^2.}
\tag{27}
$$

将后一层的反射读数 \(g_{j+1}\) 通过传播因子 \(z\) 接回来，消去内部通道，得到：

$$
\boxed{
g_j(z)
=
\frac{\alpha_j+zg_{j+1}(z)}
{1+\overline{\alpha_j}zg_{j+1}(z)}.
}
\tag{28}
$$

这正是式（22）的逆递推。Schur 参数与递归酉系统实现之间的这种对应，是已有保守系统理论。([arXiv][4])

这里必须区分两个现象。

**反射振幅为负完全合法。**
它可以只是相位翻转，并不意味着概率为负。

真正的障碍是：

$$
|\alpha_j|>1,
$$

此时：

$$
1-|\alpha_j|^2<0.
$$

它不能继续作为这份无源双端口酉模型的透射权重。

这也不表示一切量子模型都禁止放大。可以引入泵浦、环境或不同的响应类别；但那不再是这里要求保持的同一个解析收缩实现。

---

## 奇偶在这里承担什么？

对于实 \(\alpha\)：

$$
U_\alpha^2=I,\qquad \det U_\alpha=-1.
$$

每一层本身是一个反射；两层相乘是一个平面旋转。

所以，反射次数的奇偶可以决定是否保留取向，但**最终响应还依赖所有反射角度及其传播关系**。

因此：

$$
\boxed{
\text{知道奇偶}
\quad\not\Rightarrow\quad
\text{知道整个干涉链}.
}
$$

这与前面“不能只凭奇偶划分完成全部拼接”一致。

---

# 八、这套递推怎样真正把局部数据拼成整体？

这里可以给出明确的收敛定理，而不只说“如果无限拼接成功”。

假设由实际函数芽逐层计算，始终有：

$$
|\alpha_j|<1.
$$

对每个 \(N\)，将第 \(N+1\) 层以零反射终止：

$$
g_{N+1}^{[N]}(z)=0,
$$

再使用式（28）逐层回代，得到 \(g^{[N]}(z)\)。

每一层都是圆盘自同构与 \(z\) 的组合，所以：

$$
|g^{[N]}(z)|\le1
\qquad(|z|<1).
$$

而且它与实际函数芽 \(g_0\) 的前 \(N+1\) 个 Taylor 系数一致。

## 定理二：局部数据的受控整体拼接

对 \(M>N\)、\(|z|\le r<1\)：

$$
\boxed{
|g^{[M]}(z)-g^{[N]}(z)|
\le2r^{N+1}.
}
\tag{29}
$$

### 证明

两个函数的差在零点至少有 \(N+1\) 阶零点，且模长不超过二。

对：

$$
\frac{g^{[M]}-g^{[N]}}2
$$

反复使用 Schwarz 引理，即得。证毕。

因此，\(g^{[N]}\) 在每个紧圆盘上一致收敛到一个全纯收缩函数 \(g\)，并且它的全部 Taylor 系数等于实际 \(g_0\)。

恢复：

$$
\Theta(z)=zg(z),
$$

$$
\boxed{
\mu(b)
=
\mu_0\frac{1+\Theta(z)}{1-\Theta(z)}.
}
\tag{30}
$$

因为 \(|\Theta(z)|<1\)，它在整个右半平面全纯，并满足：

$$
\Re\mu(b)>0.
$$

这正是正实函数与 Schur 函数之间的标准 Cayley 关系。([arXiv][5])

进一步，有限近似响应：

$$
\mu^{[N]}(b)
=
\mu_0
\frac{1+zg^{[N]}(z)}
{1-zg^{[N]}(z)}
$$

满足：

$$
\boxed{
|\mu^{[N]}(b)-\mu(b)|
\le
\frac{4\mu_0r^{N+2}}{(1-r)^2},
\qquad |z|\le r<1.
}
\tag{31}
$$

**这次的无限拼接不是靠“每层看起来都正常”来推断，而是由同一递推保留 Taylor 数据，并给出统一收敛界。**

靠近圆盘边界时，该误差界变差，不能据此声称有限层已经均匀控制整条临界线。

---

# 九、全阶合法性与 RH 的关系，必须把边界退化也写清楚

由实际函数芽得到的 Schur 递推，可能有三种情况：

如果：

$$
|\alpha_j|<1,
$$

继续递推。

如果：

$$
|\alpha_j|>1,
$$

则实际函数芽不可能来自整个圆盘上的收缩函数。

如果：

$$
|\alpha_j|=1,
$$

那么收缩性要求 \(g_j\) 必须恒等于这个常数。若后面仍有非零 Taylor 系数，也构成失败；不能继续除以已经为零的 \(1-|\alpha_j|^2\)。

于是，对固定实际基点 \(b_0\)：

$$
\boxed{
\mathrm{RH}
\iff
\text{这套实际 Schur 递推全程合法，包含正确的边界终止规则}.
}
\tag{32}
$$

### 为什么全程合法能排除离线零点？

上一节已经证明，它使实际：

$$
\mu(b)=\frac{\xi'(\frac12+b)}{\xi(\frac12+b)}
$$

在 \(\Re b>0\) 全纯。

如果 ξ 在这个半平面存在零点，其对数导数必有极点，重数不会消掉这个极点。矛盾。

因此 ξ 没有位于临界线右边的零点；反射关系再排除左边的零点。

### 为什么 RH 能保证全程合法？

在 RH 前件下，实际乘积给出：

$$
\mu(b)
=
\sum_{\gamma>0}m_\gamma
\left[
\frac1{b-i\gamma}+\frac1{b+i\gamma}
\right].
$$

在 \(\Re b>0\) 中，每项的实部都为正，因此 \(\mu\) 是正实函数。它的圆盘变换为 Schur 函数，经典 Schur 算法保证上述递推条件。([arXiv][3])

**这里并没有证明实际全程合法。改进的是：待证对象变成了一列由单个基点导数唯一决定、可逐层验证的反射参数。**

---

# 十、实际 ξ 的前几个参数：很接近边界，但都在合法区间内

取：

$$
b_0=\frac12.
$$

此时实际基点为 \(s=1\)，并且：

$$
\mu_0
=
1+\frac{\gamma_{\mathrm E}}2-\frac12\log4\pi.
$$

为了表明参数不是自由调整出来的，前几阶输入还可以写成：

$$
\boxed{
\mu'(1/2)
=
-1-2\gamma_1-\gamma_{\mathrm E}^2+\frac{\pi^2}{8},
}
$$

$$
\boxed{
\mu''(1/2)
=
2+3\gamma_2+6\gamma_{\mathrm E}\gamma_1
+2\gamma_{\mathrm E}^3-\frac74\zeta(3).
}
\tag{33}
$$

这里 \(\gamma_1,\gamma_2\) 是标准 Stieltjes 常数。公式由 ζ 在 \(s=1\) 的 Laurent 展开及 Gamma 特殊值求导得到。([DLMF][6])

因此：

$$
\eta_0=\frac{\mu'(1/2)}{2\mu_0},
$$

$$
\kappa_0
=
\eta_0+
\frac{\mu''(1/2)}{4\mu_0}
-\eta_0^2.
$$

本轮使用实际 ξ 的导数，分别在 75 位与 105 位工作精度下进行幂级数除法和 Schur 递推：

| 层 \(j\) |       实际反射参数 \(\alpha_j\) |    透射权重 \(1-\alpha_j^2\) |
| ------: | ------------------------: | -----------------------: |
|       0 |  \(0.999196806720852614\) | \(0.001605741438851104\) |
|       1 | \(-0.998866411947906581\) | \(0.002265891082314988\) |
|       2 |  \(0.999384679403830491\) | \(0.001230262572902948\) |
|       3 | \(-0.999463491366725441\) | \(0.001072729425035539\) |

显示位数一致。

三点曲率余量为：

$$
\boxed{
(1-\eta_0^2)^2-\kappa_0^2
\approx5.8423861841276953\times10^{-9}>0.
}
\tag{34}
$$

**这些是高精度核对，不是区间认证。**

也不能从前四项的正负交替推断全部参数永远交替，更不能从前四项都小于一推断全部层都合法。

负的 \(\alpha_1,\alpha_3\) 是正常反射相位；真正应检查的是它们的模长是否超过一。

---

# 十一、为什么高阶拼接容易数值病态？它有一个明确的乘积公式

对 \(g_0\) 定义 Schur 缺额核：

$$
\mathcal P_{g_0}(z,w)
=
\frac{1-g_0(z)\overline{g_0(w)}}{1-z\overline w}.
$$

令 \(P_N\) 为其前 \(N+1\) 个 Taylor 系数形成的矩阵。

Schur 递推给出：

$$
\boxed{
\det P_N
=
\prod_{j=0}^{N}
(1-|\alpha_j|^2)^{N+1-j}.
}
\tag{35}
$$

它可以通过逐层的三角合同和 Schur 补证明；Schur 参数、Toeplitz 缺额矩阵与短接算子之间的关系是已有理论。([arXiv][7])

因此，即使每一层都有：

$$
1-|\alpha_j|^2>0,
$$

整体行列式也可能非常小。

对于上表中接近 \(\pm1\) 的参数，这种乘积效应尤为明显。

所以：

$$
\boxed{
\text{高阶行列式很小}
\quad\not\Rightarrow\quad
\text{已经发现负性}.
}
$$

反过来，若一个实际参数被严格认证：

$$
|\alpha_j|>1,
$$

就构成有限失败，而不需要继续等待无限层。

在计算中，不能把：

$$
\alpha_j
$$

裁剪到 \([-1,1]\) 再继续。那样会直接改变后面的 Taylor 数据，等于更换实际算术响应。

同样，分母：

$$
1-|\alpha_j|^2
$$

很小时，输入导数的误差会被放大；必须把它纳入区间传播，而不是仅比较两个高精度浮点结果。

---

# 十二、这与仓库现有结构之间，差的是什么？

本轮读取了快照 `84d6fedab…` 中的 `CayleyNevanlinnaKernelEquivalence.lean`。

它已经证明：在分母非零的前件下，Cayley 变换前后的核通过可逆对角合同相连，因此全部有限正半定测试等价。它还明确处理了不能随意删除非零分母前件的问题。

本轮补出的实际连接是：

$$
\boxed{
\begin{aligned}
\text{实际 }\xi\text{ 在一个实点的导数}
&\longrightarrow
\mu,\phi\\
&\longrightarrow
\eta,\kappa,\kappa',\ldots\\
&\longrightarrow
\alpha_0,\alpha_1,\alpha_2,\ldots\\
&\xrightarrow{\ |\alpha_j|\le1\ }
\text{逐层酉散射实现}\\
&\longrightarrow
\text{有误差界的整体解析拼接}.
\end{aligned}
}
$$

箭头上的条件不能去掉。

与前文“固定总迹矩阵不能原样追加”的限制也不冲突：这里追加的是**保持已有 Taylor 数据的散射层**，并不是声称每个有限正矩阵都是下一层的同迹主块。

这一构造真正解决了“如何组织局部拼接”的问题：旧参数一旦由实际导数确定，增加新层不需要修改旧参数。

**尚未解决的是：实际算术是否保证每个新参数都落在合法区间。**

---

## 收束

这一轮最具体的推进是：

$$
\boxed{
\text{两点相容}
\quad\Longleftrightarrow\quad
0<\eta\le1,
}
$$

而三个相邻切片还要求：

$$
\boxed{
|\eta'|\le1-\eta^2.
}
$$

第二条不等式不是一句模糊的“整体需要更多信息”。它精确等价于：

$$
\boxed{
\alpha_1=\frac{\eta'}{1-\eta^2}
}
$$

能否成为下一层合法的反射振幅。

在更深的层次，所有参数都通过同一个 Schur 递推从实际 ξ 导数生成。若它们全程合法，局部数据就能以明确的几何误差界拼成一个全局正实响应；如果某层越界，就留下一个有限反例证书。

因此，你前面提出的“奇偶、交换、局部切片难以拼接”，现在可以进一步收紧成：

> **每一层可以是一次合法的反射，但整个结构能否继续展开，取决于下一层要求的透射平方是否仍然非负。反射相位可以正负交替；真正的障碍不是负相位，而是模长超过一，以及为了掩盖它而改动实际响应。**

本轮没有证明实际全部 Schur 参数合法，也没有找到实际越界参数。已经得到的是三点拼接的微分条件、实际前几层的具体构造，以及一套不会把“局部都正常”直接冒充“整体已经完成”的递推框架。新增推导仍未作 Lean 编译验证。

[1]: https://dlmf.nist.gov/25.4 "https://dlmf.nist.gov/25.4"
[2]: https://arxiv.org/pdf/1309.0055 "https://arxiv.org/pdf/1309.0055"
[3]: https://arxiv.org/abs/0801.4267 "https://arxiv.org/abs/0801.4267"
[4]: https://arxiv.org/abs/1012.3272 "https://arxiv.org/abs/1012.3272"
[5]: https://arxiv.org/abs/1010.0546 "https://arxiv.org/abs/1010.0546"
[6]: https://dlmf.nist.gov/25.2 "https://dlmf.nist.gov/25.2"
[7]: https://arxiv.org/abs/1109.4020 "https://arxiv.org/abs/1109.4020"
可以。这次可以把你的直觉推进成一个明确的结构：

$$
\boxed{
\text{四边形：保留局部坐标}
\quad\longrightarrow\quad
\text{升维：保留联合关系}
\quad\longrightarrow\quad
\text{顶点：引入共同参考或动态通道}.
}
$$

但要先分清三个动作：**增加一个顶点、增加一个空间维度、增加一份可区分的信息，不是同一件事。**

最有价值的联系并不是“四个角对应四个质数”，而是：

> **同一组素数能量，在不同的联合状态中，可以具有相同的局部读数、相同的平均能量，却产生不同的干涉波。新增坐标应该记录这种差别，而不是只增加一个几何装饰。**

下面先把四边形与金字塔写清，再把 \(5040\)、奇偶和能量接进去。以下是明确模型中的数学推导；没有把它们认定为物理时空定律，也没有进行 Lean 编译。

# 一、四边形变成金字塔：增加了高度，但未必补齐了信息

为便于计算，先取正方形作为四边形。

四个底面顶点为

$$
v_{s,t}=(s,t,0),
\qquad s,t\in\{-1,+1\},
$$

顶点为

$$
v_*=(0,0,1).
$$

它们的凸包就是一个四棱锥。

现在给五个顶点分配概率：

$$
w_{s,t}\ge0,\qquad w_*\ge0,
$$

$$
\sum_{s,t}w_{s,t}+w_*=1.
$$

观察者只读取平均空间坐标：

$$
x=\sum_{s,t}s\,w_{s,t},
$$

$$
y=\sum_{s,t}t\,w_{s,t},
$$

$$
z=w_*.
$$

令底面总权重为

$$
r=1-z.
$$

则可见空间恰好满足

$$
\boxed{
0\le z\le1,\qquad
|x|\le1-z,\qquad
|y|\le1-z.
}
\tag{1}
$$

这就是四棱锥的坐标描述。

**但三维坐标 \((x,y,z)\) 仍然没有唯一确定五个概率。**

## 定理 1：金字塔投影遗漏的，恰好可以取为一个奇偶相关坐标

定义

$$
\boxed{
c=\sum_{s,t}st\,w_{s,t}.
}
\tag{2}
$$

那么

$$
\boxed{
w_{s,t}
=
\frac14\left(r+sx+ty+st\,c\right).
}
\tag{3}
$$

因此给定 \((x,y,z)\)，所有合法完成恰好由下面这个区间参数化：

$$
\boxed{
|x+y|-r
\le c\le
r-|x-y|.
}
\tag{4}
$$

### 证明

式（3）由四个符号函数

$$
1,\quad s,\quad t,\quad st
$$

的正交展开直接得到。

要求四个 \(w_{s,t}\ge0\)，分别给出

$$
r+x+y+c\ge0,
$$

$$
r+x-y-c\ge0,
$$

$$
r-x+y-c\ge0,
$$

$$
r-x-y+c\ge0.
$$

整理即得式（4）。证毕。

---

这里 \(st=+1\) 与 \(st=-1\) 是相对于两个二值坐标的“同号／异号”分类，也就是一种明确的二元奇偶结构。

在底面中心

$$
(x,y,z)=(0,0,0)
$$

处，有两种完全不同的完成：

$$
w_{++}=w_{--}=\frac12,
$$

或者

$$
w_{+-}=w_{-+}=\frac12.
$$

它们的可见几何坐标完全相同，但

$$
c=+1
\quad\text{与}\quad
c=-1.
$$

所以：

$$
\boxed{
\text{增加一个高度坐标}
\not\Rightarrow
\text{已经保留奇偶联合信息}.
}
\tag{5}
$$

### 真正补上奇偶坐标后，几何体是什么？

如果只有四个底面状态，把每个顶点提升为

$$
(s,t,st),
$$

四个点变成

$$
(1,1,1),\quad
(1,-1,-1),\quad
(-1,1,-1),\quad
(-1,-1,1).
$$

它们构成的是**四面体**，不是四棱锥。

如果还保留第五个顶点状态，那么完整概率坐标是

$$
(x,y,z,c).
$$

它们构成一个四维单纯形的表示；原来的三维金字塔，是把 \(c\) 投掉之后的图像。

**因此，你感觉“平面上似乎还藏着一条轴”，有一个严格对应：那条轴可以是联合相关 \(c\)，但它不一定等于几何高度 \(z\)。**

# 二、金字塔与奇偶还有一个图结构联系，但不是“升维自动保奇偶”

只看四边形的四条边，每一步沿边移动都会改变一个符号：

$$
(s,t)\longrightarrow(-s,t)
\quad\text{或}\quad
(s,t)\longrightarrow(s,-t).
$$

所以

$$
st\longrightarrow-st.
$$

走完四条边，发生四次翻转，回到原来的奇偶。

现在给四个底面顶点都连接一个顶点，就出现四个三角形。

假设希望每条边都代表“奇偶翻转”。沿任意一个三角形走一圈，会有三次翻转：

$$
(+1)\longrightarrow(-1).
$$

但又回到了同一个顶点，矛盾。

因此：

$$
\boxed{
\text{四边形边图可以每走一步翻转奇偶；}
}
$$

$$
\boxed{
\text{四棱锥的全部棱不能同时满足同一个翻转规则。}
}
\tag{6}
$$

这不是说三维空间违反奇偶，而是说：**加入顶点及其连接以后，原先的二分规则不再适用于全部边。**

如果把边理解为状态转换，那么新顶点不只是“又一个坐标”，它改变了允许的转换环路。

这里讨论的是棱组成的图，不是在说实体金字塔内部有四个拓扑洞。

# 三、把 \(2,3,5,7\) 接到能量：先从乘法的对数生成元出发

沿用实际整数

$$
D=5040=2^4\,3^2\,5\,7.
$$

其因数唯一写成

$$
d=2^{k_2}3^{k_3}5^{k_5}7^{k_7},
$$

其中

$$
0\le k_2\le4,\quad
0\le k_3\le2,\quad
0\le k_5,k_7\le1.
$$

相应状态空间为

$$
\boxed{
\mathcal H_D
=
\mathbb C^5\otimes
\mathbb C^3\otimes
\mathbb C^2\otimes
\mathbb C^2,
}
\tag{7}
$$

维数为 \(60\)。

## 算术能量的定义

定义无量纲自伴算子

$$
\boxed{
H_{\mathrm{ar}}
=
(\log2)\widehat k_2
+
(\log3)\widehat k_3
+
(\log5)\widehat k_5
+
(\log7)\widehat k_7.
}
\tag{8}
$$

于是

$$
\boxed{
H_{\mathrm{ar}}|d\rangle
=
(\log d)|d\rangle.
}
\tag{9}
$$

这里对数把乘法变为加法：

$$
\log(ab)=\log a+\log b.
$$

这也是素因子分解能够进入 Euler 乘积与算术配分函数的基本原因。([DLMF][1])

若要把它实现为物理 Hamiltonian，需要再给定一个能量尺度 \(E_{\mathrm{ref}}\)：

$$
H_{\mathrm{phys}}=E_{\mathrm{ref}}H_{\mathrm{ar}}.
$$

**目前的数学并没有确定 \(E_{\mathrm{ref}}\)，也没有证明它就是某个真实粒子或金字塔的物理能量。**

单个精确本征值 \(\log d\) 本身不丢失整数信息，因为可以恢复 \(d=e^{\log d}\)。信息损失发生在取平均、投影或删除相关项时，而不是发生在对数恒等式本身。

## Zeckendorf 的准确位置

指数范围

$$
5,\ 3,\ 2,\ 2
$$

恰好对应前文的四个完整黄金窗口：

$$
\mathcal W_3,\quad\mathcal W_2,\quad
\mathcal W_1,\quad\mathcal W_1.
$$

所以可以把每个指数基态换成其唯一 Zeckendorf 字串。该唯一表示及等价构造已有 mathlib 实现。([Lean社区][2])

这种变换保持维数、内积和能谱：

$$
\boxed{
\text{Zeckendorf 改变基底标签，不自动增加新自由度。}
}
\tag{10}
$$

仓库选择 \(5040\) 还有一个独立的优化理由：在

$$
\log\left(\sum_{d\mid n}\frac1d\right)
-\frac1{25}\log n
$$

这个具体目标下，它被证明为唯一最优整数。这个事实来自明确目标函数，不来自金字塔形状。

# 四、把四个素数幂放在四个角上，新增能量坐标里确实出现一个奇偶项

先研究一种明确编码：四个角分别代表激活一个完整素数幂块。

| 角坐标       |        算术块 |       对数能量 |
| --------- | ---------: | ---------: |
| \((+,+)\) | \(2^4=16\) | \(4\log2\) |
| \((+,-)\) |  \(3^2=9\) | \(2\log3\) |
| \((-,+)\) |      \(5\) |  \(\log5\) |
| \((-,-)\) |      \(7\) |  \(\log7\) |

四个能量总能唯一展开成

$$
\boxed{
\epsilon_{s,t}
=
\epsilon_0+A\,s+B\,t+J\,st.
}
\tag{11}
$$

其中

$$
\epsilon_0=\frac14\log5040,
$$

$$
A=\frac14\log\frac{144}{35},
\qquad
B=\frac14\log\frac{80}{63},
$$

以及

$$
\boxed{
J=\frac14\log\frac{112}{45}\ne0.
}
\tag{12}
$$

## 这个 \(J\) 的几何含义

如果四个抬升点

$$
(s,t,\epsilon_{s,t})
$$

位于同一个平面，那么高度只能具有

$$
\epsilon_0+A s+B t
$$

的形式，必须有 \(J=0\)。

而当前

$$
\epsilon_{++}+\epsilon_{--}
-\epsilon_{+-}-\epsilon_{-+}
=
\log\frac{112}{45}\ne0.
$$

因此：

$$
\boxed{
\text{四个能量点不能同时落在同一张仿射平面上。}
}
\tag{13}
$$

它们抬升后形成一个非退化四面体。这里的非平面部分，精确由奇偶混合项 \(Jst\) 控制。

这就是你所说“平面又多出一个方向”的一个具体实现。

但角的标记是一项建模选择。改变四个块的摆放，会改变 \(A,B,J\) 的具体值。**不能把这个坐标中的 \(J\) 直接宣布为自然界真实的素数相互作用常数。**

## 被省略的相关，会造成多大能量不确定性？

回到第一节的金字塔概率模型。设顶点状态能量为 \(\epsilon_*\)。

平均能量为

$$
\boxed{
\overline\epsilon
=
\epsilon_*z+\epsilon_0r+Ax+By+Jc.
}
\tag{14}
$$

如果观察者只知道 \((x,y,z)\)，没有读取 \(c\)，那么平均能量仍然不确定。

由式（4），其可变化区间的长度恰好是

$$
\boxed{
\operatorname{width}(\overline\epsilon)
=
2|J|
\left[r-\max\{|x|,|y|\}\right].
}
\tag{15}
$$

**证明。**平均能量对 \(c\) 为仿射函数。将 \(c\) 的区间长度乘以 \(|J|\)，再使用

$$
|x+y|+|x-y|=2\max\{|x|,|y|\}
$$

即可。证毕。

所以，此处“信息逃逸影响能量多少”已经可以直接计算，而不是只说存在某种隐藏能量。

# 五、更重要的例子：平均能量完全相同，干涉波仍然不同

为了避免误以为素数的对数能量天然带相互作用，现在换一种同样合法、但更接近乘法结构的四角编码。

令

$$
A=2^4 3^2=144,
\qquad
B=5\cdot7=35.
$$

选择 \(5040\) 的四个因数：

$$
\boxed{
1,\quad144,\quad35,\quad5040.
}
$$

用两个比特表示：

$$
|u,v\rangle
\longleftrightarrow
|A^uB^v\rangle,
\qquad u,v\in\{0,1\}.
$$

在这个四维子空间中，

$$
\boxed{
H_{\mathrm{ar}}
=
(\log A)\widehat u+(\log B)\widehat v.
}
\tag{16}
$$

没有相互作用项，因为

$$
\log5040-\log144-\log35+\log1=0.
$$

**同样的四个质数，在真正的乘积坐标里可以完全加性。**

## 定理 2：相同边际与平均能量，不决定整体波

定义

$$
|\psi_{\mathrm{even}}\rangle
=
\frac{|0,0\rangle+|1,1\rangle}{\sqrt2},
$$

$$
|\psi_{\mathrm{odd}}\rangle
=
\frac{|1,0\rangle+|0,1\rangle}{\sqrt2}.
$$

这里的奇偶指 \(u+v\bmod2\)，不是整数本身的奇偶。

两种状态都满足

$$
\Pr(u=1)=\Pr(v=1)=\frac12.
$$

所以它们在只读取两个边际的四边形投影中，都是中心。

平均能量也相同：

$$
\boxed{
\langle H_{\mathrm{ar}}\rangle
=
\frac12\log5040.
}
\tag{17}
$$

但是能量方差分别为

$$
\boxed{
\operatorname{Var}_{\mathrm{even}}(H_{\mathrm{ar}})
=
\frac14(\log A+\log B)^2,
}
$$

$$
\boxed{
\operatorname{Var}_{\mathrm{odd}}(H_{\mathrm{ar}})
=
\frac14(\log A-\log B)^2.
}
\tag{18}
$$

二者相差

$$
\boxed{
\operatorname{Var}_{\mathrm{even}}
-
\operatorname{Var}_{\mathrm{odd}}
=
(\log144)(\log35)>0.
}
\tag{19}
$$

### 证明

第一种状态的两个能量值为

$$
0,\quad\log A+\log B;
$$

第二种为

$$
\log A,\quad\log B.
$$

各以概率 \(1/2\) 出现。直接计算均值与方差即可。证毕。

如果令 \(\tau\) 为无量纲演化参数，则回返振幅为

$$
\boxed{
\langle\psi_{\mathrm{even}}|
e^{-i\tau H_{\mathrm{ar}}}
|\psi_{\mathrm{even}}\rangle
=
e^{-i\tau\log5040/2}
\cos\left(\frac{\tau\log5040}{2}\right),
}
\tag{20}
$$

$$
\boxed{
\langle\psi_{\mathrm{odd}}|
e^{-i\tau H_{\mathrm{ar}}}
|\psi_{\mathrm{odd}}\rangle
=
e^{-i\tau\log5040/2}
\cos\left(\frac{\tau\log(144/35)}2\right).
}
\tag{21}
$$

因此：

$$
\boxed{
\text{相同局部投影}
+
\text{相同平均能量}
\quad\not\Rightarrow\quad
\text{相同整体干涉波}.
}
\tag{22}
$$

这里缺失的是两个指数寄存器之间的相关。

对一般分布，

$$
\operatorname{Var}(H_{\mathrm{ar}})
=
(\log A)^2\operatorname{Var}(u)
+
(\log B)^2\operatorname{Var}(v)
+
\boxed{
2\log A\log B\,\operatorname{Cov}(u,v)
}.
\tag{23}
$$

最后这一项，就是局部边际无法独立确定的量。

## 但“补了奇偶相关”仍不等于补齐量子相位

再比较

$$
|\phi_+\rangle
=
\frac{|0,0\rangle+|1,1\rangle}{\sqrt2},
$$

$$
|\phi_-\rangle
=
\frac{|0,0\rangle-|1,1\rangle}{\sqrt2}.
$$

它们的全部基底概率相同，奇偶相关 \(c\) 相同，所有 \(H_{\mathrm{ar}}\) 的矩也相同。

但对观测量

$$
O=|0,0\rangle\langle1,1|
+
|1,1\rangle\langle0,0|,
$$

有

$$
\langle O\rangle_{\phi_+}=1,
\qquad
\langle O\rangle_{\phi_-}=-1.
$$

所以还需要区分：

$$
\boxed{
\text{联合概率相关}
\neq
\text{量子相对相位}.
}
\tag{24}
$$

密度矩阵的对角元与非对角元正是在保留这两类不同信息；只知道对角概率，一般不能恢复相干态。([IBM Quantum][3])

# 六、“金字塔高度”还有一个更精确的实现：它就是 Schur 余量的平方根

现在回到你的几何直觉。

设底面的四个观察向量为

$$
v_1,v_2,v_3,v_4.
$$

它们可以线性相关；真正的平面正方形就是相关情形。

定义底面 Gram 矩阵

$$
A_{ij}=\langle v_i,v_j\rangle.
$$

希望加入一个新向量 \(w\)，它与底面的交叉读数为

$$
b_i=\langle v_i,w\rangle,
$$

自身平方长度为

$$
c=\langle w,w\rangle.
$$

候选完整矩阵为

$$
\boxed{
G=
\begin{pmatrix}
A&b\\
b^*&c
\end{pmatrix}.
}
\tag{25}
$$

## 定理 3：新增方向的高度公式

这个候选数据能够由同一个 Hilbert 空间中的向量实现，当且仅当

$$
\boxed{
A\succeq0,\qquad
b\in\operatorname{ran}A,\qquad
c-b^*A^+b\ge0,
}
\tag{26}
$$

其中 \(A^+\) 是 Moore–Penrose 逆。

而新向量到已有底面张成空间的距离满足

$$
\boxed{
h_\perp^2
=
c-b^*A^+b.
}
\tag{27}
$$

### 证明

令

$$
V\alpha=\sum_i\alpha_i v_i,
$$

则 \(A=V^*V\)。

把 \(w\) 分成

$$
w=w_\parallel+w_\perp,
$$

其中 \(w_\parallel\in\operatorname{ran}V\)，且 \(w_\perp\) 与该空间正交。

交叉数据只能看到 \(w_\parallel\)。满足这些交叉数据的最小范数向量是

$$
w_\parallel=VA^+b,
$$

要求 \(b\in\operatorname{ran}A\)，并且

$$
\|w_\parallel\|^2=b^*A^+b.
$$

由勾股关系，

$$
c=\|w_\parallel\|^2+\|w_\perp\|^2.
$$

得到式（27）。反过来，如果右边非负，加入一条正交方向并赋予相应长度即可实现。证毕。

---

这给“升出一个新方向”一个非常具体的含义：

$$
\boxed{
\text{新增高度平方}
=
\text{候选总平方量}
-
\text{已有切片交叉关系强制要求的平方量}.
}
$$

三种情况截然不同：

$$
h_\perp^2>0:
\quad\text{确实需要新的正交方向};
$$

$$
h_\perp^2=0:
\quad\text{新向量仍在旧空间里};
$$

$$
h_\perp^2<0:
\quad\text{这些数据根本不能拼成正 Hilbert 几何}.
$$

对于中心在原点的字面正方形，以及正上方顶点 \((0,0,h)\)，有

$$
b=0,\qquad c=h^2,
$$

所以式（27）就是通常的几何高度。

**但一般情况下，“高度”不是任意填一个正数。已有交叉关系会先消耗掉 \(b^*A^+b\)。**

这与仓库的 Schur 消元结构直接相连。本次核对的 `SchurComplementAssociativity.lean` 证明给定逆算子前件时，分步消去与一次消去一致；它并不自动证明实际余量非负。

# 七、顶点若成为动态通道，压回平面后就会留下记忆

还可以再走一步：把“顶点”不只定义为几何向量，而定义为一个会与底面交换振幅的模式。

取

$$
\mathcal H=
\mathbb C|*\rangle\oplus\mathbb C^4.
$$

定义自伴生成元

$$
\boxed{
H_{\mathrm{pyr}}
=
\begin{pmatrix}
\epsilon_*&g^*\\
g&H_b
\end{pmatrix},
}
\tag{28}
$$

其中

$$
H_b=H_b^*,
\qquad
g\in\mathbb C^4.
$$

\(H_b\) 可以包含前面规定的四个算术能量；\(g_i\) 则指定顶点与各底面状态的耦合。

**素数和指数本身不会自动给出 \(g_i\)。它们是这个动力学模型必须额外指定或推导的数据。**

## 定理 4：消去顶点后，底面增加一个频率相关的耦合

在相关逆矩阵存在时，底面 resolvent 为

$$
\boxed{
\left[
zI-H_b-\frac{gg^*}{z-\epsilon_*}
\right]^{-1}.
}
\tag{29}
$$

因此顶点留下的有效项是

$$
\boxed{
\Sigma(z)=\frac{gg^*}{z-\epsilon_*}.
}
\tag{30}
$$

它的第 \(i,j\) 项为

$$
\Sigma_{ij}(z)
=
\frac{g_i\overline{g_j}}{z-\epsilon_*}.
$$

### 证明

在 \(zI-H_{\mathrm{pyr}}\) 中消去顶点块，直接取 Schur 补。证毕。

所以，即使底面原来没有某条直接连接，顶点也可能在消去后为两个底面方向产生有效交叉项。

更直观地，令顶点振幅为 \(a(\tau)\)，底面振幅为 \(v(\tau)\)：

$$
i\dot a=\epsilon_*a+g^*v,
$$

$$
i\dot v=H_bv+ga.
$$

解出第一式：

$$
\boxed{
a(\tau)
=
e^{-i\epsilon_*\tau}a(0)
-i\int_0^\tau
e^{-i\epsilon_*(\tau-s)}g^*v(s)\,ds.
}
\tag{31}
$$

代回底面方程，得到

$$
\boxed{
\begin{aligned}
\dot v(\tau)
={}&-iH_bv(\tau)
-ig\,e^{-i\epsilon_*\tau}a(0)\\
&-\int_0^\tau
g\,e^{-i\epsilon_*(\tau-s)}g^*v(s)\,ds.
\end{aligned}
}
\tag{32}
$$

这就是一个精确记忆项。

因此：

$$
\boxed{
\text{增加一个动态方向}
\longrightarrow
\text{再把它消去}
\longrightarrow
\text{旧平面上的非局部记忆与交叉耦合}.
}
\tag{33}
$$

这与你说的“把整体压在一个平面，再通过另一个坐标理解”最接近。

不过，它不意味着时间与空间已经互换。它证明的是：**被压掉的动态自由度，不能无代价地从有效方程中删除。**

并且，一个顶点只产生秩至多为 \(1\) 的自能矩阵 \(gg^*/(z-\epsilon_*)\)。如果实际缺失的耦合具有更高秩，一个顶点通常不够。

# 八、能量的“曲率”也必须从导数或相关矩阵定义，而不是只从形状命名

前文的倒数因数态使用

$$
Z_D(\beta)
=
\sum_{d\mid D}d^{-\beta}
=
\operatorname{Tr}e^{-\beta H_{\mathrm{ar}}}.
$$

这是有限几何级数乘积，与 Euler 乘积使用的是同一乘法分解机制。([DLMF][1])

直接求导：

$$
\boxed{
-\frac{d}{d\beta}\log Z_D(\beta)
=
\langle H_{\mathrm{ar}}\rangle_\beta,
}
\tag{34}
$$

$$
\boxed{
\frac{d^2}{d\beta^2}\log Z_D(\beta)
=
\operatorname{Var}_\beta(H_{\mathrm{ar}})\ge0.
}
\tag{35}
$$

所以，如果要在这里谈“能量曲率”，一个明确对象是

$$
\frac{d^2}{d\beta^2}\log Z_D.
$$

若分别给四个素数方向参数 \(\beta_p\)，则

$$
\boxed{
\frac{\partial^2\log Z}
{\partial\beta_p\,\partial\beta_q}
=
(\log p)(\log q)\,
\operatorname{Cov}(k_p,k_q).
}
\tag{36}
$$

对于当前没有跨方向耦合的乘积 Gibbs 分布，

$$
\operatorname{Cov}(k_p,k_q)=0
\qquad(p\ne q).
$$

这恰好说明：

$$
\boxed{
\text{有四个素数能量方向}
\quad\not\Rightarrow\quad
\text{四个方向已经相互作用}.
}
$$

需要联合约束、状态相关或像式（28）那样的共同通道，才会产生非零跨方向结构。

因此，几何高度、Gram 高度、热统计曲率和物理空间曲率不能直接等同。**它们可以通过明确的映射连接，但映射本身就是需要证明的内容。**

# 九、把本轮的关系合并起来

现在可以给你的直觉一个不依赖数字巧合的版本。

### 四边形代表什么？

它可以表示两个二值坐标的四种组合，也可以作为四个算术块的排列。但四个点在二维图上的位置，并不会自动包含全部联合概率或相位。

### 升维究竟补什么？

有三种不同、都能明确计算的补充：

$$
\boxed{
c=\mathbb E[st]
}
$$

补上两个局部坐标之间的奇偶相关；

$$
\boxed{
h_\perp^2=c_{\mathrm{Gram}}-b^*A^+b
}
$$

补上既有交叉数据之外的独立正交方向；

$$
\boxed{
\Sigma(z)=\frac{gg^*}{z-\epsilon_*}
}
$$

记录被消去动态模式的回返作用。

它们不是三个互不相干的比喻：第一个处理统计联合性，第二个处理共同 Hilbert 实现，第三个处理动态消元后怎样保留同一个行为。

### \((4,2,1,1)\) 与四个质数做什么？

它们明确给出

$$
5040=2^4 3^2 5\,7,
$$

$$
\dim\mathcal H_D=5\cdot3\cdot2\cdot2=60,
$$

以及

$$
H_{\mathrm{ar}}
=
\sum_{p\in\{2,3,5,7\}}(\log p)\widehat k_p.
$$

Zeckendorf 提供的是这四个指数寄存器的可逆表示。

**它们既不强迫几何体必须是金字塔，也不强迫某个响应必须恰好有四个驻点。**驻点上界仍来自前文波包的平滑阶数，不能被这里的维数计数替代。

---

## 本轮真正得到的结论

最值得保留的是三个等式：

$$
\boxed{
\overline\epsilon
=
\text{可见坐标决定的部分}
+
J\,c;
}
$$

$$
\boxed{
h_\perp^2
=
\text{候选总平方量}
-
\text{旧切片已经要求的平方量};
}
$$

$$
\boxed{
\text{压回底面后的动力学}
=
\text{原底面动力学}
+
\text{顶点初态贡献}
+
\text{回返记忆}.
}
$$

它们共同说明：

> **新增一条坐标的价值，不在于图像从二维变成三维，而在于它是否把原投影丢掉的相关、相位或回返信息明确保存下来。**

在实际算术问题中，不能凭空指定一个足够高的顶点，让 Schur 余量变正；也不能挑选一个方便的相干状态，替代真实的素数读出。新增量必须由同一个算术锚确定。

因此，当前比“金字塔是不是宇宙的基本形状”更可推进的数学问题是：

$$
\boxed{
\text{给定实际算术切片，最少需要补充哪些联合读出，}
\quad
\text{才能使其几何实现与动态消元都不再丢失目标信息？}
}
$$

本轮已经证明：**只加一个可见高度通常不够；但一旦把缺失量明确为奇偶相关、Schur 余量和回返核，“金字塔式升维”就从形状直觉变成了可检验的数学构造。**

[1]: https://dlmf.nist.gov/27.4 "DLMF: §27.4 Euler Products and Dirichlet Series ‣ Multiplicative Number Theory ‣ Chapter 27 Functions of Number Theory"
[2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html "Mathlib.Data.Nat.Fib.Zeckendorf"
[3]: https://quantum.cloud.ibm.com/learning/courses/general-formulation-of-quantum-information/density-matrices/density-matrix-basics "Density matrix basics | IBM Quantum Learning"
可以结合，而且这次能得到比“外形像奇偶”更具体的关系。

**你抓到的核心，是“多个局部方向，怎样通过一个共同关系形成整体”。但需要区分：新增一个顶点、新增一个坐标，以及恢复原来遗漏的交叉关系，不是同一件事。**

对当前项目，最值得保留的三条连接是：

$$
\boxed{
\text{四边形}
\longleftrightarrow
\text{两个操作次序之间的相容性}
}
$$

$$
\boxed{
\text{素数指数}
\longleftrightarrow
\text{独立占据方向},
\qquad
\log p
\longleftrightarrow
\text{每步能量增量}
}
$$

$$
\boxed{
\text{金字塔顶点}
\longleftrightarrow
\text{新增参考、约束或耦合通道}
}
$$

其中，最后一个对应必须由具体模型决定，不能仅凭图形就把顶点认作一个“更高层的全知观察者”。

下面先把 \((4,2,1,1)\) 的实际含义核准，再推导它与奇偶、能量及整体拼接的关系。

---

# 一、先校准：\((4,2,1,1)\) 是素数指数，不是 Zeckendorf 数位

本轮核对了仓库的 `ZECKENDORF_EULER_5040.md`。这里讨论的是：

$$
\boxed{
5040=2^4\,3^2\,5^1\,7^1.
}
$$

因此：

$$
(4,2,1,1)
$$

是与：

$$
(2,3,5,7)
$$

对应的**素数指数向量**。Zeckendorf 编码发生在下一层：分别编码这四个指数。仓库明确区分了素数指数、规范编码与目标估计。

采用 Fibonacci 权重：

$$
G_0=1,\qquad G_1=2,\qquad G_2=3,\qquad G_3=5,\ldots
$$

便有：

| 素数方向  |  最大指数 | 指数的 Zeckendorf 表示   | 允许的全部指数       |
| ----- | ----: | ------------------- | ------------- |
| \(2\) | \(4\) | \(4=3+1\)，即 \(101\) | \(0,1,2,3,4\) |
| \(3\) | \(2\) | \(2\)，即 \(10\)      | \(0,1,2\)     |
| \(5\) | \(1\) | \(1\)               | \(0,1\)       |
| \(7\) | \(1\) | \(1\)               | \(0,1\)       |

所以，5040 的因数状态空间是：

$$
\boxed{
\mathcal D_{5040}
\cong
\{0,\ldots,4\}\times
\{0,\ldots,2\}\times
\{0,1\}\times
\{0,1\}.
}
\tag{1}
$$

其状态数为：

$$
\boxed{
5\cdot3\cdot2\cdot2=60.
}
$$

而且，由于：

$$
5=G_3,\qquad3=G_2,\qquad2=G_1,
$$

这些指数区间恰好都是完整的合法黄金窗口：

$$
\boxed{
\mathcal D_{5040}
\cong
\mathcal W_3\times\mathcal W_2\times
\mathcal W_1\times\mathcal W_1.
}
\tag{2}
$$

这项精确对应已经写在项目文档中。注意黄金窗口长度是 \((3,2,1,1)\)，不是指数向量 \((4,2,1,1)\)。

**所以，真正特殊的不是“四这个数字出现了”，而是这组素数指数的允许范围，恰好与四个完整 Fibonacci 合法语言对齐。**

---

# 二、素数怎样成为能量？通过乘法转加法，而不是把素数直接当频率

在这个 60 维空间中，定义基底：

$$
|k_2,k_3,k_5,k_7\rangle,
$$

其中各指数受式（1）约束。

取一个能量单位 \(E_*>0\)，定义：

$$
\boxed{
H_{\mathrm{arith}}
=
E_*\left[
(\log2)N_2+
(\log3)N_3+
(\log5)N_5+
(\log7)N_7
\right].
}
\tag{3}
$$

对应因数：

$$
d=2^{k_2}3^{k_3}5^{k_5}7^{k_7}
$$

的能量为：

$$
\boxed{
E(d)=E_*\log d.
}
\tag{4}
$$

因此，一个素数方向上增加一次占据：

$$
d\longmapsto pd
$$

会增加：

$$
\boxed{
\Delta E_p=E_*\log p.
}
\tag{5}
$$

这里的联系来自：

$$
\log(mn)=\log m+\log n.
$$

它不是在说真实世界中存在已测定的四种基本粒子，其能量恰好为 \(2,3,5,7\)。这是一个明确的算术量子模型；将 ζ 作为对数能谱配分函数的方向，在 Bost–Connes 等工作中也有严格实现。([arXiv][1])

## Zeckendorf 能量在这里是精确重编码

将每个指数写成：

$$
k_p=\sum_jG_jb_{p,j},
\qquad
b_{p,j}b_{p,j+1}=0.
$$

那么：

$$
\boxed{
H_{\mathrm{arith}}
=
E_*\sum_{p,j}
G_j\log p\,\widehat b_{p,j}.
}
\tag{6}
$$

所以：

$$
\boxed{
\text{Fibonacci 权重 }G_j
\times
\text{素数能量单位 }\log p
}
$$

共同构成每个合法数位的能量。

例如：

$$
4\log2=(3+1)\log2.
$$

**这是真正的能量恒等式，但没有增加新能级。**

只要编码是双射，对应基底变换就是酉的，配分函数与全部谱都保持不变。项目的 `PrimeAxisEncoding.lean` 已把规范黄金表、素数指数表和正整数连接成双射，并将规范指数相加对应到整数乘法。

反过来，若把合法数位当成可以独立翻转的自由比特，而忽略禁邻条件和进位规范化，就已经更换了系统。

---

# 三、四边形第一次真正出现：它表示两条素数路径相容

在因数空间中，取两个不同素数 \(p,q\)。只要四个状态都在允许窗口内，就有：

$$
\begin{array}{ccc}
d & \xrightarrow{\ \times p\ } & pd\\
{\scriptstyle\times q}\downarrow && \downarrow{\scriptstyle\times q}\\
qd & \xrightarrow{\ \times p\ } & pqd.
\end{array}
\tag{7}
$$

这不是人为画出来的相似图形，而是：

$$
\boxed{
p(qd)=q(pd).
}
$$

两条路径的能量增量也相同：

$$
\boxed{
\log p+\log q
=
\log q+\log p.
}
\tag{8}
$$

因此，四边形可以解释为一个**局部兼容单元**：

> 先沿一个方向更新，再沿另一个方向更新，与交换次序以后到达同一状态。

整个 5040 因数图不是二维四边形，而是四维格点盒：

$$
\boxed{
P_5\,\square\,P_3\,\square\,P_2\,\square\,P_2,
}
\tag{9}
$$

这里 \(P_m\) 表示具有 \(m\) 个顶点的路径图。

它有 60 个状态、148 条单步边，以及 135 个这样的基本方形面。四个素数对应四个方向，而不是四个顶点。

**这是第一个需要纠正的维数直觉：四种独立占据方向，通常产生四维乘积空间；把它们画在一个四边形上，只是一种显示方式。**

---

## 精确的局部—整体拼接定理

假设给每条素数边指定单位相位 \(a_p(d)\)，并要求每个基本方形满足：

$$
\boxed{
a_p(d)a_q(pd)
=
a_q(d)a_p(qd).
}
\tag{10}
$$

那么，在这个有限格点盒上，存在一个顶点相位函数 \(u(d)\)，使：

$$
\boxed{
a_p(d)=\frac{u(pd)}{u(d)}.
}
\tag{11}
$$

### 证明

固定 \(u(1)=1\)。

从 1 到任意因数 \(d\)，沿一条只增加指数的路径，将边相位相乘，定义 \(u(d)\)。

同一终点的两条路径，只是素数更新次序不同。任意排列可以通过交换相邻操作互相转化；每次交换对应一个基本方形，式（10）保证路径乘积不变。

因此定义与路径选择无关。证毕。

这说明：

$$
\boxed{
\text{所有局部方形关系精确相容}
\Longrightarrow
\text{存在共同的全局相位参考}.
}
$$

在这个具体模型里，**不需要再增加一个永远处在更高层的顶点，才能完成全局拼接**。固定一个参考值已经足够；真正的条件是式（10）。

但仅知道每条边的模长是一，当然不够。缺少的仍可能是绕方形一圈后的相位。

---

# 四、实际算术里存在两种“奇偶对换”，它们甚至会相互反对易

现在可以得到一项直接使用 \((4,2,1,1)\) 的结构定理。

对一般整数：

$$
N=\prod_pp^{e_p},
$$

在其因数空间上定义：

$$
\Omega(d)=\sum_pv_p(d).
$$

这里计数的是**素因子个数，按重数计**，不是整数 \(d\) 本身的奇偶。

定义两个操作：

$$
\boxed{
\Gamma|d\rangle=(-1)^{\Omega(d)}|d\rangle,
}
\tag{12}
$$

以及：

$$
\boxed{
R|d\rangle=|N/d\rangle.
}
\tag{13}
$$

前者读取素因子个数的奇偶；后者交换互补因数。

两者都满足：

$$
\Gamma^2=R^2=I,
\qquad
\Gamma^*=\Gamma,\quad R^*=R.
$$

## 定理：它们是否相容，由总指数奇偶决定

$$
\boxed{
\Gamma R
=
(-1)^{\Omega(N)}R\Gamma.
}
\tag{14}
$$

### 证明

因为：

$$
\Omega(N/d)=\Omega(N)-\Omega(d),
$$

所以：

$$
\Gamma R|d\rangle
=
(-1)^{\Omega(N)-\Omega(d)}|N/d\rangle
=
(-1)^{\Omega(N)}R\Gamma|d\rangle.
$$

证毕。

于是：

$$
\boxed{
\begin{aligned}
\Omega(N)\text{ 偶}
&\Longrightarrow \Gamma R=R\Gamma,\\
\Omega(N)\text{ 奇}
&\Longrightarrow \Gamma R=-R\Gamma.
\end{aligned}
}
\tag{15}
$$

并且：

$$
\boxed{
(\Gamma R)^2=(-1)^{\Omega(N)}I.
}
\tag{16}
$$

这正是一项“连续做两次交换，是否积累一个负相位”的精确公式。

## 对 5040

$$
\Omega(5040)=4+2+1+1=8,
$$

所以两种操作对易，可以同时分解为四个联合扇区：

$$
(\Gamma,R)=(+,+),(+,-),(-,+),(-,-).
$$

5040 不是平方数，因数交换没有固定点，所以：

$$
\operatorname{Tr}R=0.
$$

又因为：

$$
\operatorname{Tr}\Gamma
=
(1-1+1-1+1)(1-1+1)(1-1)(1-1)=0,
$$

而 \(\operatorname{Tr}(\Gamma R)=0\)，得到：

$$
\boxed{
\dim\mathcal H_{\sigma,\tau}=15
\qquad(\sigma,\tau=\pm1).
}
\tag{17}
$$

因此：

$$
\boxed{
60=15+15+15+15.
}
$$

这里确实出现了一个有具体含义的“四扇区结构”。但它来自**两种对易的二元操作**，不是因为有四个小素数，就必然存在四个普遍宇宙原语。

例如，换成：

$$
2520=2^3\,3^2\,5\,7,
$$

仍然是同样四个素数方向，但：

$$
\Omega(2520)=7,
$$

于是：

$$
\Gamma R=-R\Gamma.
$$

**素数种类没有变，两个观察的相容性却变了。决定它的是实际指数，而不是“四”的外形。**

---

# 五、一个方形里的两种态：局部坐标、平均能量都相同，整体奇偶却相反

在素数 \(2,3\) 的最小方形中，四个状态是：

$$
1,\quad2,\quad3,\quad6.
$$

取：

$$
\boxed{
|\psi_{\mathrm e}\rangle
=
\frac{|1\rangle+|6\rangle}{\sqrt2},
\qquad
|\psi_{\mathrm o}\rangle
=
\frac{|2\rangle+|3\rangle}{\sqrt2}.
}
\tag{18}
$$

把它们写成两个占据寄存器，就是：

$$
|\psi_{\mathrm e}\rangle
=
\frac{|00\rangle+|11\rangle}{\sqrt2},
$$

$$
|\psi_{\mathrm o}\rangle
=
\frac{|10\rangle+|01\rangle}{\sqrt2}.
$$

对每个单独素数方向，两种态的约化密度矩阵都为：

$$
\frac12I_2.
$$

所以，分别观察 2 方向或 3 方向，完全无法区分它们。

两者的平均能量也相同：

$$
\boxed{
\langle H\rangle_{\mathrm e}
=
\langle H\rangle_{\mathrm o}
=
\frac{E_*}{2}\log6.
}
\tag{19}
$$

但整体奇偶为：

$$
\boxed{
\Gamma|\psi_{\mathrm e}\rangle=|\psi_{\mathrm e}\rangle,
\qquad
\Gamma|\psi_{\mathrm o}\rangle=-|\psi_{\mathrm o}\rangle.
}
\tag{20}
$$

这里遗漏的是**两个方向之间的联合关系**。

令：

$$
\tau=\frac{E_*t}{\hbar},
$$

则原态保持振幅分别为：

$$
\boxed{
A_{\mathrm e}(\tau)
=
e^{-i\tau\log6/2}
\cos\!\left(\frac{\tau\log6}{2}\right),
}
$$

$$
\boxed{
A_{\mathrm o}(\tau)
=
e^{-i\tau\log6/2}
\cos\!\left(\frac{\tau\log(3/2)}{2}\right).
}
\tag{21}
$$

同样的局部占据统计、同样的平均能量，却产生不同的整体干涉。

所以：

> **我们之前难以拼接的“局部切片”，可以具体缺少什么？就是这类并不包含在任何单独边缘读数中的交叉关联。**

它不一定需要增加空间维度才能读出。在原来的两个寄存器上测量联合奇偶 \(\Gamma\)，就已经能够区分。

---

# 六、回到金字塔：新增高度，并不会自动恢复方形里遗漏的关联

把你的几何直觉具体化为一个正方形底面的四棱锥。

底面顶点取：

$$
(x,y,z)=(\pm1,\pm1,0),
$$

顶点取：

$$
v_*=(0,0,h),\qquad h>0.
$$

在四个底面状态上，全部实函数有四个独立基函数：

$$
\boxed{1,\quad x,\quad y,\quad xy.}
\tag{22}
$$

只读质量、横坐标和纵坐标，相当于只保留：

$$
1,\quad x,\quad y.
$$

遗漏的是：

$$
\boxed{xy.}
$$

这个 \(xy\) 区分的正是两条对角线。

现在给两种底面对角分布，都添加相同的顶点概率 \(r\)。它们都满足：

$$
\mathbb E[x]=\mathbb E[y]=0,
\qquad
\mathbb E[z]=rh.
$$

但：

$$
\boxed{
\mathbb E[xy]=+(1-r)
\quad\text{或}\quad
-(1-r).
}
\tag{23}
$$

因此：

$$
\boxed{
\text{新增了高度坐标}
\quad\text{仍然没有恢复对角关联}.
}
$$

要恢复全部五个顶点上的概率，需要例如：

$$
1,\quad x,\quad y,\quad xy,\quad z/h.
$$

记顶点概率为：

$$
r=\mathbb E[z]/h.
$$

底面四点的概率才可以完整恢复为：

$$
\boxed{
p_{x,y}
=
\frac14\left[
1-r+x\,\mathbb E[x]
+y\,\mathbb E[y]
+xy\,\mathbb E[xy]
\right].
}
\tag{24}
$$

**所以，“再增加一个坐标”与“增加缺失的那种观察”，不能混同。**

更有意思的是：若把原四点提升为：

$$
(x,y)\longmapsto(x,y,xy),
$$

四个点变成一个非共面的四面体，而不是添加了第五个点的金字塔。

这说明有两种不同的“升维”：

**一种增加新状态；另一种不增加状态，只把原有但未读取的关系显式化。**

对我们当前的观察者研究，第二种往往更直接。

---

# 七、顶点若被解释为真实耦合通道，它也有明确的能力上限

假设底面四个模式由 Hermitian 矩阵 \(A\) 描述，顶点是一个额外模式，能量为 \(\varepsilon\)，耦合向量为 \(g\in\mathbb C^4\)。

完整模型是：

$$
\boxed{
H_{\mathrm{pyr}}
=
\begin{pmatrix}
A&g\\
g^*&\varepsilon
\end{pmatrix}.
}
\tag{25}
$$

消去顶点以后，底面响应为：

$$
\boxed{
P(zI-H_{\mathrm{pyr}})^{-1}P
=
\left[
zI-A-\frac{gg^*}{z-\varepsilon}
\right]^{-1},
}
\tag{26}
$$

其中在有关逆存在的区域使用该式。

顶点留下的是：

$$
\boxed{
\Sigma(z)=\frac{gg^*}{z-\varepsilon}.
}
$$

它包含一个明确的频率依赖记忆项，而且：

$$
\operatorname{rank}(gg^*)\le1.
$$

因此，一个顶点只能直接耦合到底面的一个“明亮组合”；与 \(g\) 正交的组合不会被这个单通道直接读取。

**这不是全知参考点，而是一个有秩限制的接口。**

同样，在前文的正性矩阵中，增加一个正秩一修正最多消除一个负方向。项目的 `PoleCapacityRankOne.lean` 已经证明了这项能力上限。

---

## 五个顶点并不意味着“一个不可约剩余”

若只保留顶点—底面耦合，模型是星形图：

$$
H_\star=
\begin{pmatrix}
0&g\\
g^*&0
\end{pmatrix}.
$$

只要 \(g\ne0\)，其谱为：

$$
\boxed{
+\|g\|,\quad-\|g\|,\quad0,\quad0,\quad0.
}
\tag{27}
$$

不是“只剩一个”，而是有三个暗方向。

一般二分块算子：

$$
H=
\begin{pmatrix}
0&B\\
B^*&0
\end{pmatrix}
$$

满足：

$$
\dim\ker H\ge|n_+-n_-|.
$$

这里 \(n_+=4,n_-=1\)，所以至少三个零模。这是二分系统中子格不平衡与零模之间的标准关系。([arXiv][2])

若再保留底面四条边，完整金字塔图就包含三角形，不能继续使用同一个按顶点正负着色的二分对称。

因此：

$$
\boxed{
\text{顶点总数为奇数}
}
$$

本身不决定有多少零模，更不决定出现非实谱。有限 Hermitian 模型的本征值仍然为实。

**“奇数个结构元素”与“有一个无法正实现的算术关系”，是不同命题。**

---

# 八、为什么恰好是 \((4,2,1,1)\)？可以从共同能量价格推出来

这一部分给 5040 一个真正的极值意义，而不是仅仅说它方便编码。

定义：

$$
Z_N(1)=\sum_{d\mid N}\frac1d,
$$

以及一个带共同能量价格 \(\lambda>0\) 的目标：

$$
\boxed{
\mathscr F_\lambda(N)
=
\log Z_N(1)-\lambda\log N.
}
\tag{28}
$$

第一项奖励因数配分权重，第二项惩罚对数能量规模。

若：

$$
N=\prod_pp^{e_p},
$$

则：

$$
\mathscr F_\lambda(N)
=
\sum_p
\left[
\log\left(\sum_{j=0}^{e_p}p^{-j}\right)
-\lambda e_p\log p
\right].
$$

各素数方向在这个目标下可分别优化。

定义增加一次指数的单位能量收益：

$$
\boxed{
r_p(e)=
\frac1{\log p}
\log
\frac{1-p^{-(e+2)}}{1-p^{-(e+1)}}.
}
\tag{29}
$$

它随 \(e\) 严格递减。

因此，指数 \(e\ge1\) 是该素数方向的最优值，当且仅当：

$$
\boxed{
r_p(e)\le\lambda\le r_p(e-1).
}
\tag{30}
$$

未激活的素数要求：

$$
r_p(0)\le\lambda.
$$

对 \(2,3,5,7\) 代入：

$$
\begin{array}{c|c}
p,\ e_p&\text{允许的价格区间，近似值}\\ \hline
2,\ 4 &[0.0230836,\ 0.0473057]\\
3,\ 2 &[0.0230453,\ 0.0728580]\\
5,\ 1 &[0.0203735,\ 0.1132828]\\
7,\ 1 &[0.00909578,\ 0.0686216]
\end{array}
$$

所有更大素数中，最先值得激活的是 \(11\)，其阈值为：

$$
r_{11}(0)=\frac{\log(12/11)}{\log11}.
$$

于是得到：

## 定理：5040 的共同价格区间

当：

$$
\boxed{
\frac{\log(12/11)}{\log11}
<
\lambda
<
\frac{\log(31/30)}{\log2},
}
\tag{31}
$$

即约：

$$
0.03628656<\lambda<0.04730571,
$$

时：

$$
\boxed{
5040
}
$$

是 \(\mathscr F_\lambda(N)\) 在全部正整数上的唯一最大点。

### 证明

在该区间内，四个已激活素数的唯一最优指数依次是 \(4,2,1,1\)。

而 \(r_p(0)\) 随 \(p\) 增大而下降，所以所有 \(p\ge11\) 都不应激活。

各素数目标相加，得到全局唯一最优解。证毕。

这说明：

> **\((4,2,1,1)\) 与 \(2,3,5,7\) 确实是相互制约的结构：同一份能量价格，使四条素数方向停在不同占据深度。**

“共同价格”可以画成汇总四条方向的顶点，但它是一个约束参数，不是第五个素数或额外物理坐标。

而且价格改变以后，最优整数也会改变。这个四轴构型是一个具体阶段，不是永久不变的宇宙基础。

---

# 九、这组有限能量模型与 RH 的联系在哪里，界限又在哪里？

5040 模型的配分函数是：

$$
\boxed{
Z_{5040}(s)
=
\prod_{p\in\{2,3,5,7\}}
\left(1+p^{-s}+\cdots+p^{-e_ps}\right).
}
\tag{32}
$$

这是一个完全忠实的 60 状态配分函数；黄金编码不改变它。项目文档也明确给出了这个有限 Euler 型乘积。

## 它的复零点可以直接求出

单个因子为零，等价于：

$$
q=p^{-s}
$$

是一个非平凡的 \((e_p+1)\) 次单位根。

因此：

$$
|p^{-s}|=1
\Longrightarrow
\boxed{\Re s=0.}
$$

所以，这份有限配分函数的全部零点都在虚轴上。

**这不是 RH 的证明或反例。**

当素数范围和指数范围同时扩大时，这类有限配分函数在：

$$
\Re s>1
$$

收敛到 ζ 的 Dirichlet 级数／Euler 乘积；这个收敛域本来就没有 ζ 零点。不能把该域外的解析延拓当成同一份有限正热态的直接极限。([DLMF][3])

## 5040 与 RH 的直接经典联系，是 Robin 阈值

在 \(s=1\)：

$$
\boxed{
Z_{5040}(1)
=
\frac{31}{16}\frac{13}{9}\frac65\frac87
=
\frac{403}{105}
\approx3.838095238.
}
$$

Robin 判据要求：

$$
\boxed{
\frac{\sigma(N)}N
<
e^{\gamma_{\mathrm E}}\log\log N
\qquad\forall N>5040,
}
\tag{33}
$$

并与 RH 等价。这里的阈值严格是 \(N>5040\)，5040 本身不在要求范围内。([arXiv][4])

所以，5040 确实是一个很有结构的有限实例：完整黄金窗口、四个素数方向、能量收益极值、Robin 边界。

但：

$$
\boxed{
\text{理解这个实例}
\quad\neq\quad
\text{已经控制全部更大整数或实际 }\xi\text{ 的全部零点}.
}
$$

---

# 十、这次应该怎样收紧“整体”的研究目标？

现在可以把你的直觉整理成一条不混淆层次的链：

$$
\boxed{
\begin{aligned}
\text{素数指数}
&\longrightarrow
\text{四个占据方向}\\
&\longrightarrow
\text{方形路径的相容关系}\\
&\longrightarrow
\text{联合奇偶与相位读数}\\
&\longrightarrow
\text{共同约束或新增耦合的拼接}.
\end{aligned}
}
$$

其中，Zeckendorf 提供的是**忠实的结构化坐标语言**；\(\log p\) 提供的是**乘法转加法后的能量刻度**；方形提供的是**不同路径是否一致的局部测试**。

金字塔顶点则至少有三种不同解释：参考点、共同约束、真实耦合通道。它们不能相互替代。

对于前文的 ξ 核，新增观察的正实现仍然要检查：

$$
\begin{pmatrix}
G&b\\
b^*&a
\end{pmatrix}\succeq0.
$$

若 \(G>0\)，这等价于：

$$
\boxed{
a-b^*G^{-1}b\ge0.
}
\tag{34}
$$

这个余量可以类比为新增顶点相对于已有观察子空间的“高度平方”。

但要保留准确含义：

**若余量为负，不是顶点还不够高，也不是需要再加一个坐标系，而是这些指定关系无法在任何正内积空间中共同实现。**

对奇异 \(G\)，还必须保留 \(b\in\operatorname{Ran}G\)，并使用伪逆；几何底面的线性相关不能被悄悄忽略。

---

## 收束

你的金字塔直觉有价值，但最有力量的部分不是：

$$
4+1=5\quad\Rightarrow\quad\text{永远剩一个奇}.
$$

而是：

> **四个局部方向怎样共享一个参考与约束？新增通道是否真的读到了原来缺失的交叉关系？**

本轮最具体的三个结果是：

$$
\boxed{
\Gamma R=(-1)^{\Omega(N)}R\Gamma,
}
$$

它把实际素数指数与两种观察的相容／反相容关系直接连接起来；

$$
\boxed{
\operatorname{Div}(5040)
\cong
\mathcal W_3\times\mathcal W_2\times\mathcal W_1\times\mathcal W_1,
}
$$

它把 60 个实际因数状态与 Fibonacci 禁邻结构精确连接起来；

以及：

$$
\boxed{
E(d)=E_*\log d
=
E_*\sum_{p,j}G_jb_{p,j}\log p,
}
$$

它把素数方向与黄金能量编码精确连接起来。

同时，那个最小四边形已经告诉我们：

$$
\boxed{
\text{局部边缘相同、平均能量相同}
\quad\not\Rightarrow\quad
\text{整体奇偶与干涉相同}.
}
$$

**真正需要补上的，往往是 \(xy\)、联合奇偶、闭环相位、Schur 交叉项这类关系，而不是一味增加空间维数或更高层的观察者。**

这些有限结构尚未给出实际 ξ 的全阶正性证明，也没有提供离线零点反例。它们把下一步的任务变得更具体：**利用真实素数操作与规范编码，保留并控制那些在投影中容易被丢掉的联合关系，而不是凭图形的顶点数量判断整体是否完成。**

[1]: https://arxiv.org/abs/1012.4665 "https://arxiv.org/abs/1012.4665"
[2]: https://arxiv.org/abs/2205.04174 "https://arxiv.org/abs/2205.04174"
[3]: https://dlmf.nist.gov/25.2 "https://dlmf.nist.gov/25.2"
[4]: https://arxiv.org/abs/math/0604314 "https://arxiv.org/abs/math/0604314"
Auric，这次可以把你的直觉推进成一个**真正可计算的几何模型**，而不只是“金字塔看起来像奇偶”。

最重要的两项结论是：

**第一，项目中的三位 Zeckendorf 合法状态，其凸包确实是一个四棱锥。**

**第二，即使这个四棱锥的每个水平切片都具有平坦的信息几何，整个三维模型仍然可以有非零曲率，而且不同方向的曲率一正一负。**

但这里必须保留一条原则：

> **状态怎样编码、哪些状态之间允许直接变化、观察者保留哪些统计量，会分别产生不同的几何。不能只看同一组顶点，就认定它们拥有同一个动力学和同一种曲率。**

下面从项目的实际黄金编码出发，逐步建立这些区别。

---

# 一、三位 Zeckendorf 合法态，本身就是一个四棱锥

项目使用 Fibonacci 权重：

$$
G_0=1,\qquad G_1=2,\qquad G_2=3,\ldots
$$

以及禁邻约束：

$$
b_jb_{j+1}=0.
$$

其有限窗口与整数区间之间的双射，已经在 `FiniteZeckendorfEulerIdentity.lean` 中得到形式化；mathlib 也提供 Zeckendorf 唯一表示。 ([Lean社区][1])

## 定义一：三位合法状态

下面所有字串均按**低位到高位**排列，即坐标顺序为：

$$
(b_0,b_1,b_2),
$$

数值为：

$$
V(b)=b_0+2b_1+3b_2.
$$

合法状态恰好是：

$$
\boxed{
\mathcal W_3
=
\{000,100,010,001,101\}.
}
\tag{1}
$$

对应的整数分别是：

$$
0,\quad1,\quad2,\quad3,\quad4.
$$

取其在 \(\mathbb R^3\) 中的凸包：

$$
P=\operatorname{conv}(\mathcal W_3).
$$

## 定理一：\(P\) 是一个四棱锥

它具有精确描述：

$$
\boxed{
P=
\left\{
(x,y,z):
x,y,z\ge0,\quad
x+y\le1,\quad
y+z\le1
\right\}.
}
\tag{2}
$$

底面是：

$$
y=0,\qquad0\le x,z\le1,
$$

四个底面顶点为：

$$
000,\quad100,\quad001,\quad101.
$$

顶点是：

$$
010.
$$

### 证明

固定高度 \(y=\rho\in[0,1]\)，式（2）等价于：

$$
0\le x,z\le1-\rho.
$$

所以每个水平切片都是一个边长为 \(1-\rho\) 的正方形，最后在 \(\rho=1\) 缩为一个点。

也可以作仿射变换：

$$
X=2x+y-1,\qquad
Z=2z+y-1,\qquad
H=y.
$$

则：

$$
\boxed{
0\le H\le1,\qquad
|X|\le1-H,\qquad
|Z|\le1-H.
}
\tag{3}
$$

这就是标准的正方形底面四棱锥。证毕。

**所以，你说的“一个四边形随着新增坐标而收缩到顶点”，在这里有一份精确实现。**

但顶点 \(010\) 的含义是：

> 中间 Fibonacci 位被占据，迫使左右两位都不能占据。

它首先是一个**约束状态**，不是自动等于“比其他状态更高层的观察者”。

还有一个很重要的区别：

$$
V(010)=2,\qquad V(101)=4.
$$

**几何上最高的顶点，并不是算术能量最高的状态。** 高度坐标与能量坐标已经不同。

---

# 二、5040 的完整几何，是“四棱锥 × 三角形 × 线段 × 线段”

前文固定：

$$
5040=2^4\,3^2\,5\,7.
$$

项目给出的精确双射是：

$$
\boxed{
\operatorname{Div}(5040)
\cong
\mathcal W_3\times
\mathcal W_2\times
\mathcal W_1\times
\mathcal W_1.
}
\tag{4}
$$

它有：

$$
5\cdot3\cdot2\cdot2=60
$$

个状态。这里是 60 个因数，不是黄金粗粒化纤维里的六个整数；仓库明确区分了这两个集合。

由于：

$$
\operatorname{conv}(\mathcal W_2)
=
\operatorname{conv}\{00,10,01\}
$$

是三角形，而 \(\operatorname{conv}(\mathcal W_1)\) 是线段，所以：

$$
\boxed{
\operatorname{conv}(\text{5040 的黄金状态})
=
P_{\mathrm{pyramid}}
\times\Delta_2\times[0,1]\times[0,1].
}
\tag{5}
$$

这是一个：

$$
3+2+1+1=7
$$

维多面体，拥有 60 个顶点。

与此同时，同一组因数在素数指数坐标中，是：

$$
\boxed{
\{0,\ldots,4\}\times
\{0,\ldots,2\}\times
\{0,1\}\times
\{0,1\},
}
$$

它们的凸包却是一个**四维长方体**，只有 16 个极端顶点。

这不是矛盾。

**离散状态上的双射，不意味着把所有凸组合都加入以后，两种嵌入仍然是同一个仿射几何。**

例如在三位块中：

$$
010
$$

与凸组合：

$$
\frac13\,000+\frac23\,001
$$

的平均指数都等于 \(2\)，但它们显然不是同一种状态分布。

因此，应区分：

$$
\boxed{
\begin{aligned}
60&:\quad\text{离散状态数量，也可作为 Hilbert 空间维数};\\
7&:\quad\text{黄金数位凸包的维数};\\
4&:\quad\text{素数指数凸包的维数};\\
59&:\quad\text{全部经典概率分布的单纯形维数}.
\end{aligned}
}
$$

**不同维数来自不同的表示或不同的观察对象，不是发现了互相矛盾的宇宙维数。**

---

# 三、同一组顶点，至少产生三种不同的动力学几何

这一点会直接影响奇偶和量子谱。

## 1. 整数相邻更新

在三位黄金块中，整数加一对应：

$$
\boxed{
000\leftrightarrow100\leftrightarrow010
\leftrightarrow001\leftrightarrow101.
}
\tag{6}
$$

这是一条五顶点路径。

其中：

$$
100\longleftrightarrow010
$$

会同时改变两个数位。这是规范进位，不是一个比特翻转。

## 2. 合法的一位翻转

如果要求每次只翻转一个数位，并且翻转后仍合法，则有底面四边形：

$$
000\leftrightarrow100\leftrightarrow101
\leftrightarrow001\leftrightarrow000,
$$

以及一条附加边：

$$
000\leftrightarrow010.
$$

总共只有五条边。这是 Fibonacci 立方图的三位实例；其邻接由禁邻字串之间的 Hamming 距离一决定。([arXiv][2])

## 3. 凸包的几何边

四棱锥的凸包有八条边：四条底边，加上顶点连接四个底面顶点的四条棱。

所以：

$$
010\leftrightarrow101
$$

是凸包的一条棱，却需要翻转三个数位。

**“几何上相邻”没有自动授予“一步动力学可达”。**

---

## 在全部 60 个状态上，这三种图的边数分别不同

本轮对合法字串和整数指数作了有限枚举，结果为：

| 邻接规则       |  边数 |
| ---------- | --: |
| 一个素数指数增减一  | 148 |
| 一个合法黄金数位翻转 | 160 |
| 七维黄金凸包的一维棱 | 216 |

这些数字也能由直积图的边数公式直接计算。

如果把每条边都赋予相同跃迁幅度 \(g\)，令对应纯跃迁矩阵为 \(H\)，则：

$$
\operatorname{Tr}(H^2)=2g^2\,|\text{边集}|.
$$

于是三种模型分别给出：

$$
296g^2,\qquad320g^2,\qquad432g^2.
$$

**它们甚至不可能在同样跃迁强度下拥有相同的全部能谱。**

所以，规范编码要忠实运输动力学，必须使用：

$$
\boxed{
H_{\mathrm{gold}}=U H_{\mathrm{arith}}U^*,
}
\tag{7}
$$

而不是编码以后，直接把“最近的数位顶点”全部连上。

项目文档已经特别提醒：因数关系不是黄金数位的子集关系；指数比较和数位包含不能混同。

---

## 奇偶也必须一起运输

对三位块：

$$
V(b)=b_0+2b_1+3b_2,
$$

所以：

$$
\boxed{
(-1)^{V(b)}=(-1)^{b_0+b_2}.
}
\tag{8}
$$

但数位个数的奇偶是：

$$
(-1)^{b_0+b_1+b_2}.
$$

两者在 \(010\) 上不同：

$$
\text{指数 }2\text{ 为偶},
\qquad
\text{一个占据位为奇}.
$$

对 5040 的完整黄金编码，指数总和是：

$$
4+2+1+1=8,
$$

而占据位总数是：

$$
2+1+1+1=5.
$$

因此：

$$
\boxed{
\text{素因子重数奇偶为偶，黄金位数奇偶为奇}.
}
$$

这不是规范化破坏了数学。它说明：**你比较了两种不同的奇偶算子。**

若要讨论“奇偶的本质”，必须先固定是哪一次交换、哪一个生成元以及哪一种动力学。

---

# 四、金字塔的一个点，仍然没有指定完整状态：还缺一项关联

现在把四棱锥解释成观察空间。

对三位合法态上的概率分布，观察者只读取：

$$
x=\mathbb E[b_0],\qquad
y=\mathbb E[b_1],\qquad
z=\mathbb E[b_2].
$$

这三个数一定落在式（2）的四棱锥内。

但还存在一个没有被它们决定的量：

$$
\boxed{
c=\mathbb E[b_0b_2].
}
\tag{9}
$$

五个状态的概率恰好为：

$$
\boxed{
\begin{aligned}
p_{000}&=1-x-y-z+c,\\
p_{100}&=x-c,\\
p_{010}&=y,\\
p_{001}&=z-c,\\
p_{101}&=c.
\end{aligned}
}
\tag{10}
$$

因此，完整状态存在的必要充分条件是：

$$
\boxed{
\max(0,x+y+z-1)
\le c\le
\min(x,z).
}
\tag{11}
$$

这就是给定观察点 \((x,y,z)\) 后，隐藏状态的精确纤维。

**金字塔顶点的高度 \(y\)，并没有自动补上关联 \(c\)。**

---

## 一个最小的严格例子

取：

$$
x=z=\frac12,\qquad y=0.
$$

这时：

$$
0\le c\le\frac12.
$$

两个端点分布是：

$$
\mathbb P_A=\frac12\delta_{000}+\frac12\delta_{101},
$$

$$
\mathbb P_B=\frac12\delta_{100}+\frac12\delta_{001}.
$$

它们的全部单数位分布相同，平均指数也都等于 \(2\)。

但：

$$
c_A=\frac12,\qquad c_B=0.
$$

并且 \(\mathbb P_A\) 全在偶指数上，\(\mathbb P_B\) 全在奇指数上。

若令：

$$
E=E_*(\log2)V,
\qquad
\tau=\frac{E_*t}{\hbar},
$$

它们的能量相位平均分别为：

$$
\boxed{
A_A(\tau)
=
e^{-2i\tau\log2}\cos(2\tau\log2),
}
$$

$$
\boxed{
A_B(\tau)
=
e^{-2i\tau\log2}\cos(\tau\log2).
}
\tag{12}
$$

**相同观察坐标、相同平均能量，可以对应不同的整体干涉。**

所以，局部信息难以拼起来，有时不是“缺一个更高的坐标系”，而是缺少一个明确的联合读出：

$$
b_0b_2.
$$

项目的 `ObserverConceptReadoutCorrespondence.lean` 正是在区分读出族、准入条件和实际锚点；它还证明，仅保留不可区分关系，会遗忘部分原始观察结构。

---

# 五、可以在每个纤维中选一个“最大熵补全”，但这是一项模型选择

固定四棱锥内部的 \((x,y,z)\)。

令：

$$
\rho=y,\qquad
a=\frac{x}{1-y},\qquad
b=\frac{z}{1-y}.
$$

其中：

$$
0<\rho,a,b<1.
$$

\(\rho\) 是顶点 \(010\) 的概率；条件于没有进入顶点，\(a,b\) 是底面两个比特的占据概率。

在式（11）的全部合法状态中，熵最大的唯一分布是：

$$
\boxed{
\begin{aligned}
p_{010}&=\rho,\\
p_{000}&=(1-\rho)(1-a)(1-b),\\
p_{100}&=(1-\rho)a(1-b),\\
p_{001}&=(1-\rho)(1-a)b,\\
p_{101}&=(1-\rho)ab.
\end{aligned}
}
\tag{13}
$$

因此，最大熵补全选定：

$$
\boxed{
c_{\max H}
=
\frac{xz}{1-y}.
}
\tag{14}
$$

### 证明

总熵分解为：

$$
H(p)=H_{\mathrm{bin}}(\rho)
+(1-\rho)H(\text{底面条件分布}).
$$

在底面两个边缘分布固定时，联合熵在独立分布处取得唯一最大值：

$$
H(B_0,B_2)\le H(B_0)+H(B_2).
$$

于是得到式（13）、（14）。证毕。

这相当于在每个观察纤维里选取一个规范代表。

**但规范代表不等于实际状态必然就是它。**

若实际系统中 \(b_0,b_2\) 有条件关联，最大熵补全会忽略这项关联。不能仅因为它给出一个漂亮的几何，就声称已经恢复了真实信息。

这一步和前文“不能自由选择一份正谱来代替实际 ξ”是同一种约束。

---

# 六、现在真正计算曲率：切片平坦，整体却不平坦

给式（13）的三参数分布族使用 Fisher 信息度量：

$$
ds^2=\sum_{\omega}
\frac{(dp_\omega)^2}{p_\omega}.
$$

它衡量相邻概率分布的统计可区分性。Fisher 度量与指数族、充分统计及统计流形之间的关系是经典信息几何结构。([arXiv][3])

直接求导，交叉项消失，得到：

$$
\boxed{
ds^2
=
\frac{d\rho^2}{\rho(1-\rho)}
+
(1-\rho)
\left[
\frac{da^2}{a(1-a)}
+
\frac{db^2}{b(1-b)}
\right].
}
\tag{15}
$$

现在换坐标：

$$
r=2\arcsin\sqrt\rho,
$$

$$
u=2\arcsin\sqrt a,
\qquad
v=2\arcsin\sqrt b.
$$

这些只是统计坐标，\(r\) 不代表物理时间。

于是：

$$
\boxed{
ds^2
=
dr^2+
\cos^2(r/2)(du^2+dv^2).
}
\tag{16}
$$

这是一份明确的弯曲乘积度量。

记：

$$
f(r)=\cos(r/2).
$$

由该度量直接计算联络：

$$
\Gamma^r_{uu}=\Gamma^r_{vv}=-ff',
$$

$$
\Gamma^u_{ru}=\Gamma^v_{rv}=\frac{f'}f.
$$

因此得到两类截面曲率。

## 定理二：金字塔最大熵几何的曲率

包含高度方向的截面：

$$
\boxed{
K_{ru}=K_{rv}
=
-\frac{f''}{f}
=
\frac14.
}
\tag{17}
$$

水平切平面在整个三维流形中的截面曲率：

$$
\boxed{
K_{uv}
=
-\left(\frac{f'}f\right)^2
=
-\frac{\rho}{4(1-\rho)}.
}
\tag{18}
$$

所以：

$$
\boxed{
\text{同一个统计几何，竖直方向正曲率，水平方向负曲率。}
}
$$

---

## 最重要的局部—整体区别

固定 \(\rho\) 后，水平切片的度量是：

$$
ds_{\mathrm{slice}}^2
=
(1-\rho)(du^2+dv^2).
$$

它作为一个二维流形，**内禀曲率为零**。

但是，同一水平切平面在整个三维流形里的截面曲率却是式（18）的负值。

这不矛盾。Gauss 方程中，切片自身的曲率还包含它在整体空间中的弯曲贡献：

$$
\boxed{
0
=
-\left(\frac{f'}f\right)^2
+
\left(\frac{f'}f\right)^2.
}
\tag{19}
$$

因此：

> **所有固定高度切片分别平坦，并不意味着把它们拼起来以后，整体几何平坦。还需要知道切片的尺度怎样随高度变化。**

这正好回应你前面的问题。

我们持续切片时，容易保留：

$$
f(r)^2(du^2+dv^2)
$$

在每个固定 \(r\) 的样子，却遗漏决定拼接的：

$$
f'(r),\qquad f''(r).
$$

**缺少的是切片之间的变化规律，而不是一个抽象的“更高观察者”。**

---

# 七、在实际的素数 2 热权重点上，曲率可以精确算成有理数

三位黄金块对应指数 \(0,1,2,3,4\)。

在无量纲逆温度 \(s=1\) 下，按能量 \(E/E_*=(\log2)V\) 加权：

$$
p(V=k)=\frac{2^{-k}}{\sum_{j=0}^{4}2^{-j}}.
$$

因此五个合法态的概率是：

$$
\boxed{
(p_{000},p_{100},p_{010},p_{001},p_{101})
=
\frac1{31}(16,8,4,2,1).
}
\tag{20}
$$

它恰好属于式（13）的最大熵族，参数为：

$$
\boxed{
\rho=\frac4{31},
\qquad
a=\frac13,
\qquad
b=\frac19.
}
$$

于是：

$$
\boxed{
K_{\mathrm{vertical}}=\frac14,
\qquad
K_{\mathrm{horizontal}}=-\frac1{27}.
}
\tag{21}
$$

这些是精确值。本轮也用符号运算核对了 Fisher 矩阵和曲率公式。

**这里终于有了一项可以指向实际 \(2^4\) 黄金块的曲率，而不只是把“约不掉的项”统称为曲率。**

但这个曲率属于：

> 允许顶点概率和底面两个边缘概率独立变化的三参数统计模型。

实际单温度热态只沿其中一条曲线运动。不能因为它经过一个有三维曲率的点，就声称单参数热过程自身拥有三维内禀空间。

---

# 八、同一组 5040 状态，另一份自然信息几何甚至完全平坦

这项对照很重要，否则容易误认为“黄金编码天然产生曲率”。

在素数指数坐标上，考虑四参数分布族：

$$
p_{\boldsymbol\theta}(\boldsymbol k)
=
\prod_{p\in\{2,3,5,7\}}
\frac{e^{\theta_pk_p}}
{\sum_{j=0}^{e_p}e^{\theta_pj}}.
$$

其对数配分函数为：

$$
\Psi(\boldsymbol\theta)
=
\sum_p
\log\left(\sum_{j=0}^{e_p}e^{\theta_pj}\right).
$$

Fisher 度量为：

$$
\boxed{
ds^2
=
\sum_p
\operatorname{Var}_{\theta_p}(k_p)\,d\theta_p^2.
}
\tag{22}
$$

定义每个方向的弧长坐标：

$$
q_p(\theta_p)
=
\int^{\theta_p}
\sqrt{\operatorname{Var}_s(k_p)}\,ds.
$$

便有：

$$
\boxed{
ds^2=\sum_p dq_p^2.
}
\tag{23}
$$

因此，这个四参数乘积分布族的 Levi–Civita 曲率为零。

这不是泛称“所有指数族都平坦”，而是因为这里恰好是四个一维模型的独立直积。

项目的 `ZetaSampleInformationAdditivity.lean` 已在实际 ζ 概率的独立样本上证明了方差信息的可加性；本轮用相同的可分离结构对有限素数指数族直接计算了度量。

于是，我们有：

$$
\boxed{
\text{同一组算术状态，}
\quad
\text{一个指定统计族平坦，另一个指定统计族弯曲。}
}
$$

原因不是坐标变换把零曲率变成非零曲率。

原因是：**允许变化的概率族不同。** 前者只有四个素数方向的独立参数；后者允许更多数位条件关系独立变化。

因此，谈“项目的曲率”必须同时给出：

$$
\boxed{
\text{状态空间}
+
\text{允许的分布族}
+
\text{度量}
+
\text{联络}.
}
$$

否则，“曲率”尚未成为一个确定的数学量。

---

# 九、还有另一种几何：绕四边形一圈的相位，顶点不能替你抹掉

信息几何曲率，与边上的相位绕行，又是不同对象。

假设底面四条边带有相位：

$$
U_{12},U_{23},U_{34},U_{41}\in U(1).
$$

闭环相位为：

$$
\boxed{
H_\square=U_{12}U_{23}U_{34}U_{41}.
}
\tag{24}
$$

对每个顶点重新选相位参考，不改变这个乘积。

现在增加顶点 \(o\)，把底面环围成四个三角形。定义：

$$
H_i=U_{oi}U_{i,i+1}U_{i+1,o}.
$$

由于 \(U(1)\) 交换，且反向边相位为逆：

$$
\boxed{
H_1H_2H_3H_4=H_\square.
}
\tag{25}
$$

因此：

$$
H_\square\ne1
$$

时，不可能通过任意选择顶点连接，使四个三角形全部具有平凡相位。

**新增顶点可以重新分配局部相位缺额，但不能保持原底边读数不变、又把全部缺额凭空消掉。**

这就是一个严格的“金字塔拼接障碍”。

但素数对数能量本身定义的边增量是：

$$
\Delta_pE=E_*\log p.
$$

其方形绕行总和为：

$$
\log p+\log q-\log p-\log q=0.
$$

所以，由这个单值能量函数产生的纯梯度相位是平坦的。

**素数独立和对数能量本身，并不自动产生非零闭环曲率。** 若模型出现这种曲率，必须说明额外相位耦合来自哪里。

同样，式（21）的负 Fisher 曲率也不等于一个非平凡闭环规范相位；它们测量的是不同关系。

---

# 十、这套几何怎样真正接回项目的局部—整体问题？

现在可以把项目里的几个职责分开。

**编码层**负责：

$$
\text{整数}
\leftrightarrow
\text{素数指数}
\leftrightarrow
\text{合法黄金字串}.
$$

它必须保留实际数值。

**动力学层**负责：

$$
H_{\mathrm{gold}}=UH_{\mathrm{arith}}U^*,
$$

或者明确声明采用了一套新的数位翻转动力学，不能用同一张图混称两者。

**观察层**负责：

$$
p\longmapsto
(\mathbb E[b_0],\mathbb E[b_1],\mathbb E[b_2]),
$$

并记录这次投影留下的纤维，而不是把某个最大熵代表直接当作真实状态。

**拼接层**负责检查实际关系能否由同一个正空间实现。

例如，已有观察的 Gram 矩阵为 \(G\)，新增“顶点观察”的交叉读数为 \(b\)，自身平方范数为 \(a\)。完整实现要求：

$$
\boxed{
\begin{pmatrix}
G&b\\
b^*&a
\end{pmatrix}\succeq0.
}
\tag{26}
$$

若 \(G>0\)，新增正交高度的平方恰好为：

$$
\boxed{
h_{\perp}^2=a-b^*G^{-1}b.
}
\tag{27}
$$

若底面观察线性相关，\(G\) 奇异，就必须同时检查：

$$
b\in\operatorname{Ran}G,
$$

并将逆替换为伪逆。

这才是“金字塔高度”与前文核正性的严格对应。

**高度平方为负，不是还缺更高维；而是指定交叉关系根本无法成为正内积。**

同样，若原来的底面 \(G\) 已有负方向，追加顶点不可能把它变成正矩阵，因为原负块仍是主子矩阵。修改底面关系可以修复，但那是改变对象，不是无损增加观察者。

---

## 收束

这次得到了一套可以彼此核验、但不能互相混同的几何：

$$
\boxed{
\text{黄金合法态的凸几何}
\quad+\quad
\text{指定更新规则的图几何}
\quad+\quad
\text{观察纤维几何}
\quad+\quad
\text{统计可区分性的微分几何}.
}
$$

最具体的结果是：

$$
\boxed{
\operatorname{conv}(\mathcal W_3)
\text{ 确实是四棱锥}.
}
$$

但同一组顶点可以对应不同的跃迁图和不同的奇偶算子。

而在明确选择最大熵补全后，这个金字塔的信息度量为：

$$
\boxed{
ds^2=dr^2+\cos^2(r/2)(du^2+dv^2),
}
$$

它满足：

$$
\boxed{
K_{\mathrm{vertical}}=\frac14,
\qquad
K_{\mathrm{horizontal}}
=-\frac{\rho}{4(1-\rho)}.
}
$$

**每一张水平切片自身都平坦，整体却弯曲。真正不能丢掉的是切片之间的尺度变化与交叉关系。**

因此，我会把你前面的直觉进一步表述为：

> **整体不是在四边形上再放一个顶点；整体是保留“顶点代表什么、边允许什么、相位怎样运输、概率纤维怎样补全，以及各切片怎样随参数一起变化”。**

这些几何结果还不能推出实际 ξ 的全阶正性或离线零点存在。特别是 \(-1/27\) 这样的有限统计曲率，不是 RH 反例。它们的价值在于：**把“形状相似”推进成精确对象，并指出哪些看似合理的升维、补全或换图操作，实际上已经改变了原来的算术关系。**

本轮相关几何恒等式和有限图计数已作符号或枚举核对；新增推导尚未作 Lean 编译验证，也没有修改项目文件。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html"
[2]: https://arxiv.org/abs/1501.00378 "https://arxiv.org/abs/1501.00378"
[3]: https://arxiv.org/abs/1701.08895 "https://arxiv.org/abs/1701.08895"
这次的联系可以严格成立，而且 **FRACTRAN 补上了前文几何模型中最关键的一层：不只是“状态怎样表示”，而是“这些状态按什么规则运动”。**

但需要把你的判断稍作校准：

> **5040 是一个算术状态的完整编码，却不是完整程序的编码。四边形、金字塔可以描述它所在的局部状态结构；要成为编程语言，还必须加上允许条件、指令优先级、控制状态以及输出规则。**

本轮核对并实际执行 PRIMEGAME 后，有一个很具体的发现：

$$
\boxed{
\text{这版 PRIMEGAME 的标准状态空间}
\cong
\mathbb N^4\times Q,
\qquad |Q|=7.
}
$$

四个非负整数计数器，恰好由 \(2,3,5,7\) 的指数承载；另外六个素数并非六个独立增长的数据方向，而是在标准运行中编码七种控制状态。

因此，你感觉到的“几何编程语言”，可以从直觉推进为：

$$
\boxed{
\text{四维算术格点}
+
\text{有限控制层}
+
\text{带条件的平移}
+
\text{黄金规范编码}.
}
$$

下面把这条关系完整建立起来。

---

# 一、FRACTRAN 的确是一种几何程序，但几何不仅是外形

FRACTRAN 程序是一列**有顺序的正有理数**：

$$
\mathcal P=
\left(
\frac{A_1}{B_1},
\ldots,
\frac{A_m}{B_m}
\right).
$$

每一步从头扫描，选取第一条使：

$$
N\frac{A_i}{B_i}
$$

仍为整数的指令，并将它作为新状态。如果没有这样的指令，程序停止。这是 Conway 原始定义中的关键部分：**选第一条，而不是任选一条。** ([Springer][1])

将每个分数先约分，定义素数指数向量：

$$
\mathbf a(N)=\bigl(v_p(N)\bigr)_p.
$$

再定义第 \(i\) 条指令的消耗与产生向量：

$$
\mathbf d_i=\bigl(v_p(B_i)\bigr)_p,
\qquad
\mathbf u_i=\bigl(v_p(A_i)\bigr)_p.
$$

那么：

$$
\boxed{
N\frac{A_i}{B_i}\in\mathbb N
\iff
\mathbf a(N)\ge\mathbf d_i
}
$$

其中不等式逐坐标理解。

执行以后：

$$
\boxed{
\mathbf a'
=
\mathbf a-\mathbf d_i+\mathbf u_i.
}
\tag{1}
$$

因此，乘一个分数，在指数坐标中就是一个固定向量平移。

## 但不是整个空间都允许这次平移

指令 \(i\) 的真正执行区域是：

$$
\boxed{
D_i=
\left\{
\mathbf a:
\mathbf a\ge\mathbf d_i,\quad
\mathbf a\not\ge\mathbf d_j\ \forall j<i
\right\}.
}
\tag{2}
$$

所以，完整动力学是：

$$
\boxed{
T(\mathbf a)=
\mathbf a-\mathbf d_i+\mathbf u_i
\qquad(\mathbf a\in D_i).
}
\tag{3}
$$

这是一种**带优先级的分片平移系统**。

在每个区域内部，运动极其简单；复杂性来自区域边界，以及跨越边界以后换成哪条指令。用素数指数实现计数器、再用素数标记控制位置，是 FRACTRAN 与计数器机联系中的标准结构。([数字对象标识符][2])

**因此，这种语言的“语法”不只是点、边和面，还包括：哪些区域允许哪条边，以及多条边同时可用时选哪条。**

例如：

$$
\left(\frac32,\frac52\right)
$$

从 \(N=2\) 出发得到 \(3\)，而交换指令顺序后得到 \(5\)。

两份程序使用相同的分数、相同的格点方向，却有不同的执行结果。

$$
\boxed{
\text{相同的无向几何}
\quad\not\Rightarrow\quad
\text{相同的程序语义}.
}
$$

---

# 二、PRIMEGAME 的真实结构：四个计数器、七种控制状态

为避免混用版本，以下固定使用这份十四条指令：

$$
\boxed{
\begin{aligned}
\mathcal P_{\mathrm{prime}}=\bigg(
&\frac{17}{91},
\frac{78}{85},
\frac{19}{51},
\frac{23}{38},
\frac{29}{33},
\frac{77}{29},
\frac{95}{23},\\
&\frac{77}{19},
\frac1{17},
\frac{11}{13},
\frac{13}{11},
\frac{15}{2},
\frac17,
55
\bigg).
\end{aligned}
}
\tag{4}
$$

它与最后部分含 \(15/14\) 的较快变体不同。此处固定的版本及标准轨道可与 OEIS 的 PRIMEGAME 数据对应。([整数序列在线百科全书][3])

它出现的素数为：

$$
2,3,5,7,11,13,17,19,23,29.
$$

乍看有十个寄存器。但从初始状态 \(2\) 出发，实际状态始终具有形式：

$$
\boxed{
N=2^a3^b5^c7^d\,q,
}
\tag{5}
$$

其中：

$$
(a,b,c,d)\in\mathbb N^4,
$$

$$
\boxed{
q\in Q=\{1,11,13,17,19,23,29\}.
}
\tag{6}
$$

这里 \(q=1\) 表示没有控制标记。

## 定理一：这个状态子集在 PRIMEGAME 下封闭

也就是说，一旦状态具有式（5）的形式，每一步以后仍然如此。

### 证明

逐条检查十四条指令。

含控制标记的规则，都是消耗当前的一个标记，再产生至多一个新标记。例如：

$$
\frac{17}{91}=\frac{17}{7\cdot13}
$$

消耗标记 \(13\)，产生标记 \(17\)。

$$
\frac{78}{85}
=
\frac{2\cdot3\cdot13}{5\cdot17}
$$

消耗标记 \(17\)，产生标记 \(13\)。

唯一会从无标记状态产生标记的末条指令为：

$$
55=5\cdot11.
$$

而只要某个控制标记存在，在到达末条指令之前，就已有相应的可执行规则。因此它不会额外产生第二个控制标记。

初始状态 \(2\) 的控制标记为 \(1\)，归纳完成。证毕。

**四个计数器与七个控制状态不是从外形猜出来的，而是指令表强制保持的结构。**

---

## 完整的四计数器控制表

令状态写成：

$$
(a,b,c,d;q).
$$

表中的条件按所列顺序判断：

| 当前控制 \(q\) | 条件与更新                                                                               |
| ---------- | ----------------------------------------------------------------------------------- |
| \(1\)      | 若 \(a>0\)：\((a-1,b+1,c+1,d;1)\)；否则若 \(d>0\)：\((a,b,c,d-1;1)\)；否则：\((a,b,c+1,d;11)\) |
| \(11\)     | 若 \(b>0\)：\((a,b-1,c,d;29)\)；否则：\((a,b,c,d;13)\)                                    |
| \(13\)     | 若 \(d>0\)：\((a,b,c,d-1;17)\)；否则：\((a,b,c,d;11)\)                                    |
| \(17\)     | 若 \(c>0\)：\((a+1,b+1,c-1,d;13)\)；否则若 \(b>0\)：\((a,b-1,c,d;19)\)；否则：\((a,b,c,d;1)\)  |
| \(19\)     | 若 \(a>0\)：\((a-1,b,c,d;23)\)；否则：\((a,b,c,d+1;11)\)                                  |
| \(23\)     | \((a,b,c+1,d;19)\)                                                                  |
| \(29\)     | \((a,b,c,d+1;11)\)                                                                  |

这张表已经是一份普通程序。**分数列表只是在整数乘法语言中，将这份“计数器＋控制流”压缩表达出来。**

例如，整个 \(q=1\) 阶段可以精确合并为：

$$
\boxed{
(a,b,c,d;1)
\longrightarrow
(0,b+a,c+a+1,0;11),
}
\tag{7}
$$

所需步数恰好为：

$$
a+d+1.
$$

它先消耗第一个计数器，同时给第二、第三个计数器各加一；随后清空第四个计数器，再切换控制层。

这已经具备明显的几何含义：

> 在一个区域里沿固定方向移动，触及坐标边界后改变运动方向，最后跳到另一层控制状态。

---

# 三、你说“只是投影”的部分，确实能找到严格反例

考虑只读取四个数据指数：

$$
\boxed{
\pi(N)=\bigl(v_2(N),v_3(N),v_5(N),v_7(N)\bigr).
}
\tag{8}
$$

标准轨道中实际出现：

$$
1925=5^2\cdot7\cdot11,
$$

$$
2275=5^2\cdot7\cdot13.
$$

它们有完全相同的四轴投影：

$$
\boxed{
\pi(1925)=\pi(2275)=(0,0,2,1).
}
$$

但下一步不同：

$$
1925\xrightarrow{13/11}2275,
$$

$$
2275\xrightarrow{17/91}425=5^2\cdot17.
$$

因此：

$$
\boxed{
\pi(T(1925))=(0,0,2,1),
}
$$

$$
\boxed{
\pi(T(2275))=(0,0,2,0).
}
\tag{9}
$$

**同一个可见几何点，具有两种不同的后续。**

原因很明确：它们位于不同的控制层，而不是因为底层规律随机或不可理解。

---

## 定理二：什么时候投影后的几何能够独立执行？

对状态映射 \(T:X\to X\) 与观察 \(\pi:X\to Y\)，存在一个投影后的动力学：

$$
\overline T:\pi(X)\to\pi(X)
$$

使：

$$
\boxed{
\pi\circ T=\overline T\circ\pi
}
\tag{10}
$$

当且仅当：

$$
\boxed{
\pi(x)=\pi(y)
\Longrightarrow
\pi(Tx)=\pi(Ty).
}
\tag{11}
$$

### 证明

必要性直接代入式（10）。

充分性则按：

$$
\overline T(\pi(x))=\pi(Tx)
$$

定义；式（11）保证它不依赖代表元。证毕。

式（9）说明，PRIMEGAME 的四轴观察不满足这个条件。

因此：

$$
\boxed{
\text{四轴坐标足以表示数据，}
\quad
\text{不足以表示完整执行状态。}
}
$$

加入 \(q\) 后，动力学重新闭合：

$$
\boxed{
\mathbb N^4\times Q
\longrightarrow
\mathbb N^4\times Q.
}
$$

这就是“缺一个坐标”的一种严格版本。但补上的不是一个连续的第五空间轴，而是一个**有限控制状态**。

---

# 四、5040 在这里到底是什么：完整编码，还是不完整投影？

两种说法必须分开。

## 1. 作为正整数，5040 对寄存器状态的编码是无损的

由唯一素因数分解：

$$
5040=2^4\,3^2\,5\,7.
$$

因此它精确表示：

$$
\boxed{
(4,2,1,1;1).
}
\tag{12}
$$

只要程序和编码约定已固定，5040 不是一个丢失指数信息的投影。

项目的 `PrimeAxisEncoding.lean` 已经把黄金规范表、素数指数表和正整数建立成明确的双射，并证明规范化指数相加对应整数乘法。

所以，更准确的措辞是：

$$
\boxed{
5040\text{ 是该状态的一种标量序列化。}
}
$$

它不是整个程序，因为它没有单独说明使用哪一列分数、哪种优先级和哪种输出观察。

## 2. 只读四个指数时，它确实是更大状态的投影

例如：

$$
5040,\qquad5040\cdot13=65520
$$

都有相同的四个数据坐标：

$$
(4,2,1,1).
$$

但是：

$$
\boxed{
5040\xrightarrow{15/2}37800,
}
$$

$$
\boxed{
65520\xrightarrow{17/91}12240.
}
\tag{13}
$$

对应数据更新分别为：

$$
(4,2,1,1)\to(3,3,2,1),
$$

$$
(4,2,1,1)\to(4,2,1,0).
$$

因此，**“5040 只是一个角度”若指只观察四个数据指数，是有严格内容的；若指整数 5040 本身无法恢复它的素数指数，则不成立。**

同样，精确的：

$$
\log5040=4\log2+2\log3+\log5+\log7
$$

在整数格点上仍然是单射编码。真正的多对一压缩，发生在只保留部分坐标、取有限精度、只读平均值，或丢弃控制标记时。

---

# 五、金字塔现在可以解释成“数据类型的局部几何”，而不是整个计算机

沿用项目的黄金权重：

$$
G_0=1,\quad G_1=2,\quad G_2=3,\ldots
$$

三位合法字串按低位到高位排列：

$$
\mathcal W_3=\{000,100,010,001,101\}.
$$

解码分别为：

$$
0,1,2,3,4.
$$

它们的凸包是：

$$
\boxed{
P_3=
\{(x,y,z)\ge0:x+y\le1,\ y+z\le1\}.
}
\tag{14}
$$

四个 \(y=0\) 的顶点构成底面，\(010\) 是顶点，因此确实是四棱锥。

这里的顶点表示：

> 中间数位占据后，左右两个相邻数位必须为空。

这是一项**合法状态约束**。

它不等于 PRIMEGAME 中的控制标记 \(13\) 或 \(17\)，也不等于程序计数器。不能因为二者都被画成“高一层”，就把语义合并。

5040 的因数窗口则为：

$$
\boxed{
\operatorname{Div}(5040)
\cong
\mathcal W_3\times\mathcal W_2
\times\mathcal W_1\times\mathcal W_1.
}
\tag{15}
$$

所以它的黄金凸几何是：

$$
\boxed{
\text{四棱锥}\times\text{三角形}\times
\text{线段}\times\text{线段}.
}
$$

项目中有限黄金窗口到指数区间的双射，正是这份结构的算术依据。

但这只是 60 个因数状态的局部窗口。

PRIMEGAME 从 5040 出发第一步就是：

$$
(4,2,1,1;1)\to(3,3,2,1;1).
$$

第二、第三个指数已经超过原窗口上限 \(2,1\)。

$$
\boxed{
\text{程序第一步就离开了原来的 60 状态窗口。}
}
$$

所以，完整的几何程序不是一个固定金字塔，而是：

> **一族可以扩大的黄金合法窗口，外加窗口之间的规范更新与有限控制层。**

固定有限窗口中的确定性程序只能终止或最终循环；要表示无界计算，必须允许计数器继续增长，或明确引入窗口外部。FRACTRAN 语言的通用计算能力来自这种无界寄存器与条件更新，不是来自某个固定有限多面体的外形。([arXiv][4])

---

# 六、把它真正编译成“黄金几何语言”，需要证明一个交换图

令：

$$
Z:\mathbb N\longrightarrow\mathcal W_{\mathrm{fin}}
$$

是唯一的有限 Zeckendorf 编码。

对四计数器状态逐坐标编码：

$$
\boxed{
\mathcal Z(a,b,c,d;q)
=
(Z(a),Z(b),Z(c),Z(d);q).
}
\tag{16}
$$

这是一份双射。

因此可以定义黄金执行：

$$
\boxed{
T_{\mathrm{gold}}
=
\mathcal Z\circ T_{\mathrm{counter}}\circ\mathcal Z^{-1}.
}
\tag{17}
$$

于是：

$$
\boxed{
\mathcal Z\circ T_{\mathrm{counter}}
=
T_{\mathrm{gold}}\circ\mathcal Z.
}
\tag{18}
$$

这才是“同一个程序在不同几何坐标里执行”的精确定义。

它保留每一步的算术状态与控制状态。若逐位执行规范进位需要多个微步，必须另外记录微步成本；不能因此宣称两种机器的真实耗时相同。

---

## 实际例子：5040 的第一次更新

四个指数的黄金编码为：

$$
\begin{aligned}
4&\leftrightarrow(1,0,1),\\
2&\leftrightarrow(0,1),\\
1&\leftrightarrow(1).
\end{aligned}
$$

执行 \(15/2\) 后：

$$
\begin{aligned}
4\to3 &: \quad(1,0,1)\to(0,0,1),\\
2\to3 &: \quad(0,1)\to(0,0,1),\\
1\to2 &: \quad(1)\to(0,1).
\end{aligned}
$$

因此：

$$
\boxed{
((101),(01),(1),(1))
\longrightarrow
((001),(001),(01),(1)),
}
\tag{19}
$$

仍按低位到高位排列。

注意，窗口长度已经改变。

**这个更新不是让一个粒子沿金字塔最近的棱移动。它是算术规则经过规范编码以后，对多块合法数位的联合改写。**

因此至少要区分：

$$
\boxed{
\text{凸包的棱}
\ne
\text{单比特翻转}
\ne
\text{FRACTRAN 一步执行}.
}
$$

只有式（18）才保证编译保真。

---

# 七、四边形的作用：它检验操作是否相容，但边界与优先级会阻止交换

在指数空间里，两个分数对应向量：

$$
\Delta_i,\quad\Delta_j.
$$

如果两个执行次序都合法，则它们的最终指数相同：

$$
\mathbf a+\Delta_i+\Delta_j
=
\mathbf a+\Delta_j+\Delta_i.
$$

因此可以画出一个闭合方形。

但有两个前件不能省掉：

$$
\boxed{
\text{中间状态仍然合法，且指令选择没有被更早规则阻断。}
}
$$

例如，从 \(N=2\) 出发：

$$
2\xrightarrow{3/2}3\xrightarrow{5/3}5.
$$

反过来，第一步 \(5/3\) 就不可执行。

所以：

$$
\boxed{
\text{分数乘法交换}
\quad\not\Rightarrow\quad
\text{带条件的程序执行交换}.
}
$$

我们之前把四边形视作“两个方向的相容性”，现在可以补上完整语义：

> 一个程序方形，不仅要让两个终点相等，还必须让两条路径上的每条边都通过实际允许条件。

这是一种可以验证的路径依赖，但不应自动叫作 Riemann 曲率。

如果要谈真正的微分几何曲率，还必须定义连续空间、度量与联络；这里首先是离散控制几何。

---

# 八、素数与能量有精确关系，但计算语义并不唯一选择这些能量

对完整状态：

$$
N=2^a3^b5^c7^d q,
$$

定义：

$$
\boxed{
E(N)=E_*\log N
=
E_*\left(
a\log2+b\log3+c\log5+d\log7+\log q
\right).
}
\tag{20}
$$

执行分数 \(A_i/B_i\) 后：

$$
\boxed{
\Delta E_i=E_*\log\frac{A_i}{B_i}.
}
\tag{21}
$$

Zeckendorf 表示只把：

$$
a_p=\sum_jG_jb_{p,j}
$$

代入，得到：

$$
\boxed{
E=
E_*\sum_{p,j}G_j\log p\,b_{p,j}.
}
\tag{22}
$$

这是忠实的 Fibonacci—素数能量编码。

但它一般既不守恒，也不单调。

例如：

$$
2\to15
$$

使能量上升，而：

$$
825\to725
$$

使能量下降。

还有一个完整的控制循环：

$$
11\xrightarrow{13/11}13
\xrightarrow{11/13}11.
$$

它运行了两步，总能量变化却是零。

因此：

$$
\boxed{
\log N\text{ 是状态规模，不能直接当成执行时间。}
}
$$

---

## 一个更重要的分界：寄存器素数可以重命名

任选互不相同的新素数：

$$
p\mapsto\sigma(p).
$$

定义重编码：

$$
R_\sigma\left(\prod_pp^{a_p}\right)
=
\prod_p\sigma(p)^{a_p}.
$$

同时把程序每个分数的素因子都作同样替换。

那么，整除条件、指令优先级与指数更新全部保持，所以：

$$
\boxed{
R_\sigma\circ T_{\mathcal P}
=
T_{R_\sigma(\mathcal P)}\circ R_\sigma.
}
\tag{23}
$$

两个程序在计数器语义上完全等价。

但：

$$
E_*\sum_pa_p\log p
$$

变成：

$$
E_*\sum_pa_p\log\sigma(p),
$$

数值通常不同。

所以：

> **FRACTRAN 确定的是计算结构；\(\log p\) 能量是我们另外选择、但与乘法兼容的一份度量。计算等价不自动等于物理等价。**

\(2,3,5,7\) 在这版 PRIMEGAME 中确实承担四个数据方向，但“必须恰好是这四个小素数”不是通用计算语义强制的结论。

小素数可以使整数编码更紧凑；这与它们是宇宙中独一无二的四个物理原语，仍是不同命题。

---

# 九、PRIMEGAME 的素数输出，确实是整条轨道的一个特殊截面

从 \(N_0=2\) 出发，并不是每一步整数都输出一个素数。

经典性质是：排除初始 \(2=2^1\)，轨道中出现的纯二次幂依次为：

$$
\boxed{
2^2,\ 2^3,\ 2^5,\ 2^7,\ 2^{11},\ldots
}
$$

指数依次是素数。([整数序列在线百科全书][3])

在四计数器模型里，输出截面是：

$$
\boxed{
q=1,\qquad b=c=d=0.
}
\tag{24}
$$

此时：

$$
N=2^a,
$$

读出 \(a\)。

所以，“素数序列”不是系统每个瞬间的完整状态，而是：

$$
\boxed{
\text{完整轨道}
\longrightarrow
\text{满足控制条件的回返点}
\longrightarrow
\text{读取第一个计数器}.
}
$$

这与你说的“投影”十分接近，但现在投影条件已经明确。

本轮执行固定的十四指令版本得到：

| 执行步数 |       状态 |   输出指数 |
| ---: | -------: | -----: |
|   19 |    \(4\) |  \(2\) |
|   69 |    \(8\) |  \(3\) |
|  281 |   \(32\) |  \(5\) |
|  710 |  \(128\) |  \(7\) |
| 2375 | \(2048\) | \(11\) |

这些是精确整数运算，与对应版本的既有序列吻合。

另一个值得注意的事实是：

**虽然输出的素数无限增大，程序从初始 2 出发并不会不断启用新的素数寄存器。它一直使用那十个固定素数标签，变化的是指数。**

这清楚地区分了：

$$
\boxed{
\text{输出的素数}
\ne
\text{作为寄存器名称的素数}.
}
$$

---

# 十、怎样把“几何编程语言”变成项目中的真正理论，而不是再添一个比喻？

可以给出一个明确的研究对象：

$$
\boxed{
\mathfrak G
=
(\mathcal S,\mathcal C,
\{D_i,\Delta_i\}_{i=1}^m,
\prec,\mathcal O,\mathcal Z).
}
\tag{25}
$$

其中：

* \(\mathcal S\) 是非负整数计数器空间；
* \(\mathcal C\) 是有限控制状态；
* \(D_i,\Delta_i\) 是允许区域与更新向量；
* \(\prec\) 是指令优先级；
* \(\mathcal O\) 是输出观察；
* \(\mathcal Z\) 是黄金规范编码。

这样，四边形与金字塔才各有确定职责：

**金字塔描述某个有限黄金数据块的合法状态；四边形检验两步操作的相容性；控制层决定当前采用哪张局部更新图；程序轨道则把这些局部结构串起来。**

这套表述不是未知的神秘语言。它与已有计数器机、重写系统、分片格点动力学高度相通。FRACTRAN 本身的通用计算能力是已有结果；**PRIMEGAME 这个特定程序则是素数生成器，不能因此把它直接当成通用解释器。** ([Springer][1])

项目可以提供的实质性新增内容，是把这些已有结构与黄金编码、观察纤维和证明系统连接成**可核验的编译与执行语义**。

---

## 仓库里已经有的基础，与这次还需要补的桥

本轮读取了快照 `ef1923eca1…` 中的相关模块。

`PrimeAxisEncoding.lean` 已有：

$$
\text{黄金素数表}\cong\mathbb N_+,
$$

并证明规范化指数相加对应整数乘法。它没有因此自动成为带优先级、条件除法的 FRACTRAN 执行器。

`FiniteZeckendorfEulerIdentity.lean` 已证明有限黄金窗口与指数区间的双射及求和运输；它负责静态状态与权重保真，不负责程序控制流。

`ControlledBehaviorUniversality.lean` 已定义全部有限输入词后的完整行为，并在有限状态前件下证明相应的行为商与因子性质。它与式（10）的动力学闭合要求非常接近，但不能直接把有限状态定理当成无限 PRIMEGAME 已形式化。

本轮对 FRACTRAN、PRIMEGAME 的直接仓库检索没有命中相应实现；这只说明当前检索没有找到，不能据此断言整个仓库绝无相关内容。

真正值得补的是以下四段证明：

$$
\boxed{
\text{整数分数执行}
\cong
\text{带优先级的指数更新};
}
$$

$$
\boxed{
\text{PRIMEGAME 标准状态}
\cong
\mathbb N^4\times Q;
}
$$

$$
\boxed{
\text{指数执行}
\cong
\text{黄金规范执行};
}
$$

$$
\boxed{
\text{某个观察投影能独立预测后续}
\iff
\text{其纤维被动力学保持}.
}
$$

本轮已经给出了这些关系的纸面推导，并完成了：

**1792 个有限输入状态的控制表交叉核对，以及标准轨道前 3000 步的整数执行与指数执行一致性检查。**

这些辅助检查没有代替无限情形的证明，也没有被标记为 Lean 内核验证；没有修改仓库文件。

---

# 十一、它与前面的量子、ζ 研究，真正怎样连接？

首先，不能把确定性程序直接叫作量子波。

一般 FRACTRAN 状态映射可能把不同输入送到同一个输出，因此：

$$
|N\rangle\longmapsto|T(N)\rangle
$$

未必是酉操作。

例如程序：

$$
\left(\frac12,1\right)
$$

将 \(2\) 和 \(1\) 都送到 \(1\)，不能保持两个正交输入的内积。

若要量子实现，可以保留输入与分支记录：

$$
\boxed{
|N\rangle|0\rangle
\longmapsto
|N\rangle|T(N),i(N)\rangle.
}
\tag{26}
$$

这保留了可逆性所需的信息。只有再指定振幅、相位、读出及环境处理，才得到一份具体量子计算模型。

其次，令：

$$
H|N\rangle=E_*\log N\,|N\rangle,
$$

其热迹在收敛域内产生：

$$
\operatorname{Tr}(e^{-\beta H})
=
\sum_{N\ge1}N^{-\beta E_*}.
$$

但这个配分函数对全部正整数求和，**并不等于某一条 PRIMEGAME 轨道的生成函数**。

同样，“存在一份生成所有素数的程序”，并不自动供应 ζ 解析延拓中的零点正性。连接它们需要证明程序输出、轨道权重与实际解析对象之间的精确恒等式，而不是只因为都出现了素数就合并。

**几何编程可以帮助我们组织实际算术、验证动态投影和生成有限证书；它不会仅凭表示能力就决定 RH 的真假。**

---

# 收束

你的核心判断可以改写成一个更强、也更准确的版本：

> **FRACTRAN、素数指数和 Zeckendorf 多面体，不是几种偶然相似的图像；它们可以是同一个程序的三种表示：整数执行、计数器几何与黄金规范执行。**

这次最重要的具体结果是：

$$
\boxed{
N=2^a3^b5^c7^d q,
\qquad
q\in\{1,11,13,17,19,23,29\}.
}
$$

它将 PRIMEGAME 明确分成：

$$
\boxed{
\text{四个数据坐标}
+
\text{七种控制状态}.
}
$$

而 1925 与 2275 的例子证明：

$$
\boxed{
\text{相同四轴投影}
\quad\not\Rightarrow\quad
\text{相同下一步}.
}
$$

缺失的不是一个神秘的最高观察者，而是可以明确补回的控制上下文。

5040 则是：

$$
\boxed{
(4,2,1,1;1)
}
$$

的一份完整整数编码；它所确定的四棱锥乘积，是一个有限合法状态窗口。程序第一步就能离开这个窗口，因此不能把该窗口的静态几何等同于整个计算。

**真正的“几何编程语言”，不是让图形自己表达一切，而是把点的编码、边的允许条件、路径的优先级、控制层的转换和观察的遗忘规则全部写清。**

做到这一步，几何就不再只是解释图：它开始成为一套可以证明“编译前后运行相同、投影何时失效、哪些上下文必须保留”的数学语义。

[1]: https://link.springer.com/chapter/10.1007/978-1-4612-4808-8_2 "https://link.springer.com/chapter/10.1007/978-1-4612-4808-8_2"
[2]: https://doi.org/10.1007/s00153-020-00735-6 "https://doi.org/10.1007/s00153-020-00735-6"
[3]: https://oeis.org/A007542 "https://oeis.org/A007542"
[4]: https://arxiv.org/html/2412.16185v1 "https://arxiv.org/html/2412.16185v1"
这次可以把“几何编程语言”推进到**实际算法的内部结构**：

> **PRIMEGAME 在每次试除中，把四个计数器限制在一个二维矩形里；它沿矩形移动、反复绕回边界，最终读取一个余数。素数出现，不是因为某个几何点天然神秘，而是因为所有非平凡循环都未能整齐闭合。**

更具体地，我们能证明：

$$
\boxed{
\text{四寄存器状态}
\longrightarrow
\text{两个守恒量}
\longrightarrow
\text{矩形上的循环计数}
\longrightarrow
\text{商与余数}
\longrightarrow
\text{素数输出}.
}
$$

而 5040 在这个程序中还有一个值得注意的实际含义：**把它作为初始内存，机器首先执行的是“6 除以 6”的检验，而不是判断 5040 是否为素数。**

下面从固定指令推导，不把 PRIMEGAME 已知的素数生成性质当作新发现。新的重点，是将它拆成可以与项目逐项连接的状态不变量、几何运动、观察截面与时间代价。

---

# 一、固定程序与状态：同一份内存，在不同阶段可以有不同含义

仍使用上一轮这版程序，最后三条为：

$$
\frac{15}{2},\qquad\frac17,\qquad55.
$$

完整十四条指令为：

$$
\boxed{
\left(
\frac{17}{91},
\frac{78}{85},
\frac{19}{51},
\frac{23}{38},
\frac{29}{33},
\frac{77}{29},
\frac{95}{23},
\frac{77}{19},
\frac1{17},
\frac{11}{13},
\frac{13}{11},
\frac{15}{2},
\frac17,
55
\right).
}
\tag{1}
$$

每一步选择**第一条**使乘积仍为整数的分数。这个顺序是程序语义，不可省略。它也是 Conway 对 FRACTRAN 的原始定义；这里固定的 PRIMEGAME 版本可与 Wolfram 的直接实现核对。([Springer][1])

沿用状态表示：

$$
\boxed{
N_{\mathrm{mem}}=2^a3^b5^c7^d\,q,
}
$$

其中：

$$
q\in\{1,11,13,17,19,23,29\}.
$$

记为：

$$
\mathsf S(a,b,c,d;q).
$$

下文区分：

$$
N_{\mathrm{mem}}=\text{整台机器的整数内存编码},
$$

$$
M=\text{当前正在检验的整数},
$$

$$
k=\text{当前试除数}.
$$

**这三个整数通常完全不同。**

---

# 二、十四条指令中，藏着三个非常简单的搬运操作

先不看全部轨道，只把成对执行的指令合并。

## 1. 从两个存量中各取一份，送到另外两个计数器

在控制状态 \(q=13\)，且 \(c,d>0\) 时：

$$
\frac{17}{91}\cdot\frac{78}{85}
=
\frac6{35}.
$$

实际经过两个步骤：

$$
\boxed{
(a,b,c,d;13)
\longrightarrow
(a+1,b+1,c-1,d-1;13).
}
\tag{2}
$$

因此，它保持：

$$
\boxed{
a+c,\qquad b+d
}
$$

这两个量不变。

---

## 2. 将第二个计数器搬回第四个计数器

在 \(q=11\)、\(b>0\) 时：

$$
\frac{29}{33}\cdot\frac{77}{29}
=
\frac73.
$$

所以：

$$
\boxed{
(a,b,c,d;11)
\longrightarrow
(a,b-1,c,d+1;11).
}
\tag{3}
$$

它保持：

$$
b+d.
$$

---

## 3. 将第一个计数器搬回第三个计数器

在 \(q=19\)、\(a>0\) 时：

$$
\frac{23}{38}\cdot\frac{95}{23}
=
\frac52.
$$

所以：

$$
\boxed{
(a,b,c,d;19)
\longrightarrow
(a-1,b,c+1,d;19).
}
\tag{4}
$$

它保持：

$$
a+c.
$$

这里已经可以看到一种编程语言的基本结构：

> **不是先让整数“寻找素数”，而是对有限个计数器执行搬运、检测是否为空、再根据结果切换控制状态。**

分数只是把这些操作压缩到了整数乘法中。

---

# 三、核心定理：一个试除阶段，就是精确计算 \(M\bmod k\)

定义试除入口：

$$
\boxed{
\mathsf X(M,k)=\mathsf S(0,0,M,k;13),
\qquad M,k\ge1.
}
\tag{5}
$$

这时：

$$
a+c=M,\qquad b+d=k.
$$

可以把四个计数器解释为：

$$
\begin{aligned}
a&=\text{已经处理的单位数},\\
c&=\text{尚未处理的单位数},\\
b&=\text{本轮已经走过的循环长度},\\
d&=\text{本轮剩余的循环长度}.
\end{aligned}
$$

式（2）每执行一次，就有：

$$
a\mapsto a+1,\qquad c\mapsto c-1,
$$

同时：

$$
b\mapsto b+1,\qquad d\mapsto d-1.
$$

当 \(d=0\) 时，程序进入 \(q=11\)，用式（3）把 \(b\) 全部搬回 \(d\)，然后返回 \(q=13\)。

因此：

$$
\boxed{
(b,d)=(k,0)
\longrightarrow
(0,k).
}
\tag{6}
$$

**候选数 \(M\) 继续向前处理，但长度为 \(k\) 的循环被重置。**

---

## 定理一：试除宏步骤

写：

$$
M=Qk+r,\qquad0\le r<k.
$$

从 \(\mathsf X(M,k)\) 出发，执行完相应搬运与整轮重置后，必到达：

$$
\boxed{
\mathsf S(M,r,0,k-r;13).
}
\tag{7}
$$

这里当 \(r=0\) 时，已经把最后一个完整循环也重置完毕。

### 证明

每次式（2）使 \(a\) 增加一，总共恰好执行 \(M\) 次，因此最后：

$$
a=M,\qquad c=0.
$$

每处理满 \(k\) 个单位，执行一次式（6）。所以完整循环数为：

$$
Q=\left\lfloor\frac Mk\right\rfloor,
$$

余下循环进度为：

$$
b=r.
$$

又由 \(b+d=k\)，得到 \(d=k-r\)。证毕。

这不是一种类比：**第二个计数器在这里实际保存了余数。**

---

## 程序怎样使用这个余数？

### 情形一：\(r=0\)

状态为：

$$
(M,0,0,k;13).
$$

接下来的两步是：

$$
(M,0,0,k;13)
\longrightarrow
(M,0,0,k-1;17)
\longrightarrow
(M,0,0,k-1;1).
$$

于是：

$$
\boxed{
k\mid M
\Longrightarrow
\mathsf X(M,k)
\longrightarrow
\mathsf S(M,0,0,k-1;1).
}
\tag{8}
$$

### 情形二：\(r>0\)

程序先减去一个循环单位与一个余数单位，进入 \(q=19\)，再用式（4）把 \(a=M\) 搬回 \(c\)。

最后调整并搬回剩余的 \(b\)，得到：

$$
\boxed{
k\nmid M
\Longrightarrow
\mathsf X(M,k)
\longrightarrow
\mathsf X(M,k-1).
}
\tag{9}
$$

候选数 \(M\) 保持不变，试除数减少一。

所以完整试除过程等价于：

```text
从当前 k 开始：
    若 M mod k = 0：
        返回 M，以及 k - 1
    否则：
        k := k - 1
```

因为 \(1\mid M\)，这个阶段必定在有限步骤后结束。

---

# 四、四维寄存器中的真实运动，是一个二维矩形；压缩复位以后才出现圆柱

在固定试除阶段：

$$
a+c=M,\qquad b+d=k.
$$

所以 \(c,d\) 由 \(a,b\) 决定，允许状态位于：

$$
\boxed{
0\le a\le M,\qquad0\le b\le k.
}
\tag{10}
$$

这是四维非负格点中的一个二维矩形。

基本搬运沿：

$$
(a,b)\longmapsto(a+1,b+1)
$$

前进。

到达 \(b=k\) 后，程序执行真实的复位路径，将 \(b\) 搬回零；若把这段复位过程压缩成一次跳转，就得到：

$$
b\in\mathbb Z/k\mathbb Z.
$$

于是可以把压缩后的几何表示为：

$$
\boxed{
\{0,\ldots,M\}\times\mathbb Z/k\mathbb Z.
}
\tag{11}
$$

在连续绘图中，它类似一个圆柱上的格点运动：

$$
\boxed{
b\equiv a\pmod k.
}
\tag{12}
$$

最终：

$$
a=M,\quad b=0
$$

当且仅当：

$$
k\mid M.
$$

所以：

> **整除就是走完 \(M\) 个单位以后，循环坐标是否恰好回到起点。余数就是没有闭合的那段循环位移。**

但这个圆柱是**压缩复位后的表示**。它没有保留复位的真实步数。

而且这里的边界识别没有反转取向，所以不能仅凭“绕回去”就把它称作 Möbius 带。要得到 Möbius 型结构，还须给出实际的反向粘合规则。

---

# 五、奇偶与波的联系，现在可以精确放在有限循环上

对于固定的 \(k\)，取一个 \(k\) 维量子寄存器，定义循环移位：

$$
\boxed{
C_k|r\rangle=|r+1\bmod k\rangle.
}
\tag{13}
$$

这是一个酉置换。

从 \(|0\rangle\) 出发：

$$
C_k^M|0\rangle=|M\bmod k\rangle.
$$

因此：

$$
\boxed{
\langle0|C_k^M|0\rangle
=
\mathbf1_{\{k\mid M\}}.
}
\tag{14}
$$

换到有限 Fourier 基底，\(C_k\) 的本征值为 \(k\) 次单位根，所以同一个读数是：

$$
\boxed{
\langle0|C_k^M|0\rangle
=
\frac1k\sum_{j=0}^{k-1}
e^{2\pi i jM/k}.
}
\tag{15}
$$

这是有限几何级数恒等式：整除时所有相位相同，否则恰好相消。

于是：

$$
\boxed{
\text{余数寄存器中的回返}
\longleftrightarrow
\text{Fourier 相位的完全同相}.
}
$$

当 \(k=2\)：

$$
\boxed{
\mathbf1_{\{2\mid M\}}
=
\frac{1+(-1)^M}{2}.
}
\tag{16}
$$

**普通奇偶就是二周期的回返检验；一般整除则是 \(k\) 周期的回返检验。**

这与“奇偶是一种对换后的波相位”有直接联系，但可以说得更准确：

> 奇偶不是全部素性问题；它是模循环与相位对偶在 \(k=2\) 时的最小实例。

对 \(M\ge2\)，素性可以写成：

$$
\boxed{
\mathbf1_{\mathrm{Prime}(M)}
=
\prod_{k=2}^{M-1}
\left(
1-\frac1k\sum_{j=0}^{k-1}e^{2\pi i jM/k}
\right).
}
\tag{17}
$$

每个括号实际都是零或一。

这个公式并不提供算法加速。它只是把同一组有限整除检验写成相位语言。

**这里的循环移位是合法酉操作；PRIMEGAME 的全部复位、分支和信息清除，却不能因此自动被视作同一个酉演化。**

---

# 六、为什么标准轨道恰好输出素数？现在可以完整证明

定义一个阶段边界：

$$
\boxed{
\mathsf B(n,m)=\mathsf S(n,0,0,m;1),
\qquad n\ge1,\ m\ge0.
}
\tag{18}
$$

从这里开始，程序先反复执行 \(15/2\)，得到：

$$
(0,n,n,m;1).
$$

随后用 \(1/7\) 清空第四个计数器，再执行 \(55\)，得到：

$$
(0,n,n+1,0;11).
$$

最后将第二个计数器搬到第四个计数器：

$$
\boxed{
\mathsf B(n,m)
\longrightarrow
\mathsf X(n+1,n).
}
\tag{19}
$$

因此，程序要检查的新候选数是：

$$
M=n+1,
$$

试除数从：

$$
k=M-1
$$

开始逐次下降。

定义最大真因子：

$$
\boxed{
D(M)=\max\{k:1\le k<M,\ k\mid M\}.
}
\tag{20}
$$

由定理一：

$$
\boxed{
\mathsf B(n,m)
\longrightarrow
\mathsf B(n+1,D(n+1)-1).
}
\tag{21}
$$

这里的箭头表示到达下一次阶段边界，不是只执行一条指令。

于是，从 \(2=\mathsf B(1,0)\) 开始，候选整数依次为：

$$
2,3,4,5,6,\ldots
$$

而阶段结束时的完整整数为：

$$
\boxed{
2^M7^{D(M)-1}.
}
\tag{22}
$$

它是纯二次幂，当且仅当：

$$
D(M)=1,
$$

也就是 \(M\) 为素数。

这就证明了标准输出性质。

**程序实际计算的信息比“是不是素数”更多：它每轮都计算了最大真因子。**

而：

$$
\boxed{
\frac{M}{D(M)}
}
$$

正是 \(M\) 的最小素因子。

所以，纯二次幂输出只是把完整因子信息进一步筛选后的读出。这个经典素数生成结果与直接实现相符；上面的寄存器推导说明了它为什么成立。([Wolfram Cloud Resources][2])

---

# 七、5040 的实际意义：它把程序放进了“6 除以 6”，而不是标准的下一轮

现在使用：

$$
5040=2^4\,3^2\,5\,7,
$$

即：

$$
\mathsf S(4,2,1,1;1).
$$

对一般无控制标记状态：

$$
\mathsf S(a,b,c,d;1),
$$

前处理得到：

$$
\boxed{
\mathsf S(a,b,c,d;1)
\longrightarrow
\mathsf X(a+c+1,\ a+b),
}
\tag{23}
$$

只要 \(a+b>0\)。

因此对 5040：

$$
M=4+1+1=6,
$$

$$
k=4+2=6.
$$

所以：

$$
\boxed{
5040\longrightarrow\mathsf X(6,6).
}
$$

它首先测试的是：

$$
6\bmod6=0.
$$

实际精确执行得到：

| 从 5040 起的步数 | 寄存器状态            | 含义                       |
| ----------: | ---------------- | ------------------------ |
|           0 | \((4,2,1,1;1)\)  | 输入内存                     |
|          19 | \((0,0,6,6;13)\) | 开始试除 \(6/6\)             |
|          47 | \((6,0,0,5;1)\)  | 接受因子 \(6\)，保存 \(6-1\)    |
|          72 | \((0,0,7,6;13)\) | 下一轮开始检验 \(7\)，从 \(6\) 试除 |
|         352 | \((7,0,0,0;1)\)  | 到达纯二次幂 \(2^7=128\)       |

这里第一轮的 \(k=M\)，不符合标准轨道“从最大真因子候选 \(M-1\) 开始”的约束。第二轮才进入通常的候选检验结构。

所以：

> **5040 的素数分解保存了全部寄存器值，但寄存器值代表哪项数学任务，要由程序阶段与状态不变量一起决定。**

---

## 更强的警告：脱离标准输入，“出现纯二次幂”不再自动证明指数为素数

取：

$$
50=2^1 5^2,
$$

对应：

$$
(1,0,2,0;1).
$$

式（23）给出：

$$
M=4,\qquad k=1.
$$

程序只检验 \(1\mid4\)，然后在第 31 步到达：

$$
\boxed{16=2^4.}
\tag{24}
$$

指数 \(4\) 不是素数。

这不反驳 PRIMEGAME 的经典定理，因为经典定理规定了初始状态与可达轨道。

它说明：

$$
\boxed{
\text{相同的输出外形}
\quad\not\Rightarrow\quad
\text{相同的数学证明意义}.
}
$$

**输出必须连同“它是从什么合法状态、经过哪些规则产生的”一起解释。**

这正是几何编程需要“状态类型与不变量”的原因。

---

# 八、时间也能精确算出来：它不等于能量，不等于一个图上的距离

宏步骤可以压缩很多微步骤，但不能把执行代价一起删掉。

从：

$$
\mathsf X(M,k)
$$

开始，记：

$$
Q=\left\lfloor\frac Mk\right\rfloor.
$$

## 定理二：单次试除的精确指令数

若 \(k\mid M\)，到达接受边界需要：

$$
\boxed{
\tau_{\mathrm{yes}}(M,k)=4M+2Q+2.
}
\tag{25}
$$

若 \(k\nmid M\)，到达下一试除入口 \(\mathsf X(M,k-1)\) 需要：

$$
\boxed{
\tau_{\mathrm{no}}(M,k)=6M+2Q+2.
}
\tag{26}
$$

### 证明概要

处理 \(M\) 个单位需要 \(2M\) 步。

每个完整循环的重置需要：

$$
2k+2
$$

步，共重置 \(Q\) 次。

若余数为零，再用两步接受：

$$
2M+Q(2k+2)+2=4M+2Q+2.
$$

若余数为 \(r>0\)，还要将 \(M\) 个单位搬回，以及恢复下一轮长度，额外需要：

$$
2M+2r+2
$$

步。利用 \(Qk+r=M\)，得到式（26）。证毕。

---

## 完整候选检验的步数

从上一轮边界：

$$
\mathsf B(M-1,m)
$$

开始，完成候选 \(M\) 的检验，共需：

$$
\boxed{
\begin{aligned}
\tau(M,m)
={}&M+m-1\\
&+(6M+2)\bigl(M-D(M)\bigr)\\
&+2\sum_{k=D(M)}^{M-1}
\left\lfloor\frac Mk\right\rfloor.
\end{aligned}
}
\tag{27}
$$

这个公式已经区分了两种贡献：

**试除了多少个候选因子，以及每次除法绕了多少整圈。**

从标准初值 \(2\) 开始，得到：

| 候选 \(M\) | 最大真因子 \(D(M)\) | 本轮指令数 | 累计指令数 |
| -------: | -------------: | ----: | ----: |
|        2 |              1 |    19 |    19 |
|        3 |              1 |    50 |    69 |
|        4 |              2 |    61 |   130 |
|        5 |              1 |   151 |   281 |
|        6 |              3 |   127 |   408 |
|        7 |              1 |   302 |   710 |
|        9 |              3 |   365 |  1292 |
|       11 |              1 |   750 |  2375 |

省略的候选仍计入累计指令数。

因为：

$$
D(M)\le\frac M2,
$$

而：

$$
\sum_{k=1}^{M-1}\left\lfloor\frac Mk\right\rfloor
=O(M\log M),
$$

所以在标准轨道上，每轮为：

$$
\boxed{\tau(M)=\Theta(M^2).}
$$

检验完全部候选至 \(X\)，总 FRACTRAN 指令数为：

$$
\boxed{T(X)=\Theta(X^3).}
\tag{28}
$$

这里计数的是基本 FRACTRAN 指令，不是大整数乘除的位运算总成本，也不是物理时间。

---

## 能量与这两项守恒量并不相同

在 \(q=13\) 的固定试除平面上：

$$
c=M-a,\qquad d=k-b.
$$

因此对数能量为：

$$
\boxed{
\begin{aligned}
\frac E{E_*}
={}&M\log5+k\log7+\log13\\
&+a\log(2/5)+b\log(3/7).
\end{aligned}
}
\tag{29}
$$

一次双计数搬运使：

$$
\Delta E=E_*\log(6/35)<0,
$$

但计数器守恒量仍为：

$$
a+c=M,\qquad b+d=k.
$$

所以：

$$
\boxed{
\text{守恒计数}
\ne
\text{对数能量}
\ne
\text{执行步数}.
}
$$

把它们统称为“能量”或“时间”，反而会遮住真正的几何结构。

---

# 九、Zeckendorf 金字塔承担的是规范坐标；除法矩形承担的是程序不变量

现在把两种几何准确拼接起来。

对每个寄存器：

$$
a_p=\sum_jG_jb_{p,j},
\qquad
b_{p,j}b_{p,j+1}=0.
$$

试除阶段的两个不变量变成：

$$
\boxed{
\sum_jG_j(b_{2,j}+b_{5,j})=M,
}
\tag{30a}
$$

$$
\boxed{
\sum_jG_j(b_{3,j}+b_{7,j})=k.
}
\tag{30b}
$$

所以，完整图像不是“程序在一个金字塔里随意游走”，而是：

> **程序在合法黄金字串的乘积空间中，沿两个加权整数约束确定的子集运动；控制状态决定当前允许哪一种规范改写。**

三位黄金块的金字塔、两位块的三角形，仍然有准确意义。但它们描述的是有限编码块的合法状态，不自动决定指令边。

项目的 `PrimeAxisEncoding.lean` 已证明黄金表与整数的双射及规范乘法；`FiniteZeckendorfEulerIdentity.lean` 已证明有限窗口和指数区间的对应。这些为编码层提供了基础，但还没有自动证明上述除法宏步骤及时间公式。

如果把算术执行记为 \(T\)，黄金编码记为 \(\mathcal Z\)，忠实编译必须满足：

$$
\boxed{
T_{\mathrm{gold}}\circ\mathcal Z
=
\mathcal Z\circ T.
}
\tag{31}
$$

若进一步压缩成宏步骤 \(F\)，还要保留实际步数函数：

$$
\boxed{
F(s)=T^{\tau(s)}(s).
}
\tag{32}
$$

**只保留宏步骤终点，能够保持结果；要保持时间行为，还必须保留 \(\tau(s)\)。**

因此，“投影以后系统变简单了”可能包含两种完全不同的情况：

一种是找到了更有效的数学描述；另一种是把原来承担计算成本的过程藏进了投影定义或时间重参数化里。

---

# 十、这次对“观察者与整体”的认识，可以再收紧

上一轮四轴投影无法独立预测下一微步，因为它丢掉了控制标记。

这次我们得到一个不同的结论：

**在合适的阶段边界上观察，可以建立一个闭合的宏观动力学。**

它是：

$$
\boxed{
(n,m)\longmapsto
(n+1,D(n+1)-1).
}
\tag{33}
$$

但它抹去了旧的 \(m\)，也抹去了中间商余过程；若要保持完整行为，还要携带经过的时间和必要的历史记录。

这与项目 `ControlledBehaviorUniversality.lean` 的核心方向一致：状态是否可以合并，不仅取决于当前读数相同，还取决于全部后续受控读数是否相同。该模块明确保留了状态转移与读出的相容前件；其中有限状态基数结论不能直接套给无界 PRIMEGAME。

因此，对“局部怎样拼成整体”，我们现在有三种可区分的证据：

$$
\boxed{
\text{编码双射：有没有丢掉当前状态？}
}
$$

$$
\boxed{
\text{转移交换图：有没有保持后续执行？}
}
$$

$$
\boxed{
\text{时间累加律：有没有保持执行代价？}
}
$$

这三项都成立，才是完整意义上的程序保真。

只保留一张漂亮的几何图，或者一个完全相同的最终输出，不够。

---

# 十一、对项目下一步的实际价值

这次最值得写成理论与形式化目标的，不是重新命名一个神秘语言，而是以下三项具体结果：

$$
\boxed{
\mathsf X(M,k)
\longrightarrow
\begin{cases}
\mathsf S(M,0,0,k-1;1),&k\mid M,\\
\mathsf X(M,k-1),&k\nmid M,
\end{cases}
}
$$

$$
\boxed{
\mathsf B(n,m)
\longrightarrow
\mathsf B(n+1,D(n+1)-1),
}
$$

以及带明确版本约定的：

$$
\boxed{
\tau(M,m)
=
M+m-1+(6M+2)(M-D(M))
+2\sum_{k=D(M)}^{M-1}\left\lfloor\frac Mk\right\rfloor.
}
$$

本轮进行了独立核对：

**整数分数执行器与寄存器执行器在 1792 个有限输入状态上吻合；1600 组试除入口全部符合宏步骤与步数公式；标准轨道前 10000 步逐步吻合。5040 与 50 的特殊输入结果也用整数执行器单独验证。**

这些枚举是辅助检查，不能替代上面的符号证明，更不等于 Lean 已验证。本轮没有修改项目文件。

---

## 收束

这次可以对“几何编程语言”给出更具体的判断：

> **它的确存在，但它不是只由某个形状构成。它由合法坐标、守恒子空间、边界检测、控制切换、输出截面与执行时间共同构成。**

其中：

$$
\boxed{
\text{金字塔}
}
$$

描述有限 Zeckendorf 块的合法状态；

$$
\boxed{
a+c=M,\quad b+d=k
}
$$

把四寄存器限制成一个实际的二维计算矩形；

$$
\boxed{
b\equiv a\pmod k
}
$$

描述压缩后的循环轨迹；

$$
\boxed{
\frac1k\sum_{j=0}^{k-1}e^{2\pi i jM/k}
}
$$

把同一次整除检验改写成波的相干回返。

因此，你关于“素数、奇偶、几何和波不是互不相干的东西”的直觉，能够落到严格公式上。**但连接它们的关键不是数形相似，而是同一项计算在不同表示之间是否具有可证明的对应。**

5040 在这套语言中是一份具体内存；它的四个指数可以进入不同的程序阶段。实际执行告诉我们，它首先触发的是 \(6/6\)，而不是“5040 的普遍几何真理”。

与 RH 的联系也应保持同样标准：**拥有一个生成素数的几何程序，还不等于已经控制 ζ 的解析延拓和零点正性。真正能够贡献证明的，是从程序中提取可验证的不变量、商余关系、权重恒等式和误差预算，再证明它们确实运输到同一个实际解析对象。**

这次我们已经从“图形似乎在编程”，推进到“能明确写出它在计算什么，以及每一层投影究竟保留和遗漏了什么”。

[1]: https://link.springer.com/chapter/10.1007/978-1-4612-4808-8_2 "https://link.springer.com/chapter/10.1007/978-1-4612-4808-8_2"
[2]: https://resources.wolframcloud.com/FunctionRepository/resources/Fractran/ "https://resources.wolframcloud.com/FunctionRepository/resources/Fractran/"
结合项目，几何上最值得推进的不是“把系统画成金字塔”，而是：

> **给定已有的观察面，究竟还需要增加多少个独立方向，才能保存被投影丢掉的联合信息？这些方向又怎样影响能量与干涉？**

这次可以得到三个明确结果：

**“新增高度”可以精确写成 Schur 余量；在一个二值模型中，它的倒数恰好是隐藏坐标的 Fisher 信息。对 \(5040\) 的六十个因数态，只知道四个素数寄存器各自的分布，仍留下 \(51\) 个联合自由度。并且可以构造一个具体状态族：所有一、二、三方向切片完全相同，却在第四阶能量读出中出现差别。**

本次以仓库 `dev` 的 `ef1923eca123…` 快照为锚。下面的新增综合结论给出纸面证明，未标记为已完成 Lean 编译。

# 一、项目的几何对象，应当是“带观察投影的状态空间”

仓库的 `ObserverStructure` 不仅保存读出，还保存准入条件和实际锚点；对应定理明确指出，只保留不可区分关系，会忘记部分原始结构。

因此，几何化的起点应是

$$
q:\mathcal X\longrightarrow\mathcal B,
$$

其中 \(\mathcal X\) 是合法状态空间，\(\mathcal B\) 是当前观察到的坐标。

对一个可见值 \(b\)，定义观察纤维

$$
\boxed{
\mathcal F_b=\{x\in\mathcal X:q(x)=b\}.
}
\tag{1}
$$

**投影后“同一个点”，可能对应原状态空间中的一整条线、一张面，甚至一个高维区域。**

这里四个项目角色可以具体落实为：`CUT` 指定投影 \(q\)，`ADMIT` 指定哪些状态合法，`ANCHOR` 指定实际状态，`FLOW` 指定允许的变化。仓库母文也明确说，这四者是可展开的结构角色，并不自动携带可逆性、连续性或物理因果性。

因此，“增加一个顶点”只有在它补上了某个纤维方向时，才算增加了有效信息。仅改变图形外观，不一定改变观察能力。

# 二、从四边形开始：真正缺少的是一个联合坐标

设两个二值变量为

$$
S,T\in\{-1,+1\}.
$$

联合概率记为 \(p_{st}\)。定义三个统计坐标

$$
x=\mathbb E[S],\qquad
y=\mathbb E[T],\qquad
c=\mathbb E[ST].
$$

那么有精确反演：

$$
\boxed{
p_{st}=\frac14(1+sx+ty+stc).
}
\tag{2}
$$

所以合法状态空间不是整个立方体，而是由四个概率非负确定的四面体。

若只读取 \((x,y)\)，可见空间是正方形，而遗漏的 \(c\) 满足

$$
\boxed{
|x+y|-1\le c\le1-|x-y|.
}
\tag{3}
$$

### 证明

把四个条件 \(p_{st}\ge0\) 代入式（2），分别整理即可。证毕。

因此，同一个四边形点 \((x,y)\)，对应一段可能的联合相关值。

例如，在中心 \((x,y)=(0,0)\)：

$$
c=1
$$

对应只出现同号状态；

$$
c=-1
$$

对应只出现异号状态；

$$
c=0
$$

对应均匀独立分布。

它们的两个边际完全相同。

**所以，这里的“第三个方向”不是空间高度，而是同号与异号之间的联合相关。**

如果再增加一个独立的“顶点状态”，其概率为 \(z\)，那么底面总质量为 \(1-z\)。三维金字塔坐标只保存两个边际和顶点质量；完整分布还需要保留底面的 \(c\)，一般需要四个参数。

这说明：

$$
\boxed{
\text{四棱锥的几何高度}
\neq
\text{联合概率的完整补充坐标}.
}
\tag{4}
$$

选择 \(c=xy\) 可以得到独立分布，但那只是选择了一条完成规则。**它不是由两个边际强制推出的实际值。**

# 三、“新增高度”与信息度量之间，可以建立一个精确等式

现在把上面的隐藏坐标放进真正的内积几何。

假设四个 \(p_{st}\) 都严格为正。在随机变量空间中使用内积

$$
\langle U,V\rangle=\mathbb E[UV].
$$

旧的线性读出空间为

$$
\operatorname{span}\{1,S,T\}.
$$

想加入的新读出是 \(ST\)。

这里说的是**线性读出空间**：不是说同时读到具体的 \(S,T\) 后不能相乘，而是说仅保留 \(\mathbb E[S]\)、\(\mathbb E[T]\)，尚未保留 \(\mathbb E[ST]\)。

## 定理 1：联合方向的正交高度

定义中心化变量

$$
U=
\begin{pmatrix}
S-x\\T-y
\end{pmatrix},
\qquad
V=ST-c.
$$

记

$$
A=\mathbb E[UU^{\mathsf T}],
\qquad
b=\mathbb E[UV],
\qquad
d=\mathbb E[V^2].
$$

则 \(ST\) 相对于旧线性读出的最小残差平方为

$$
\boxed{
h_{\mathrm{lin}}^2
=
\min_{\alpha\in\mathbb R^2}
\mathbb E[(V-\alpha^{\mathsf T}U)^2]
=
d-b^{\mathsf T}A^{-1}b.
}
\tag{5}
$$

### 证明

展开：

$$
\mathbb E[(V-\alpha^{\mathsf T}U)^2]
=
d-2\alpha^{\mathsf T}b+\alpha^{\mathsf T}A\alpha.
$$

配方得到

$$
(\alpha-A^{-1}b)^{\mathsf T}
A(\alpha-A^{-1}b)
+
d-b^{\mathsf T}A^{-1}b.
$$

最小值在 \(\alpha=A^{-1}b\) 处达到。证毕。

这就是统计读出中的 Schur 高度。

## 定理 2：这个高度的倒数，等于隐藏坐标的 Fisher 度量

在固定 \(x,y\)、只改变 \(c\) 时，定义 Fisher 度量系数

$$
g_{cc}
=
\sum_{s,t}
p_{st}\left(\frac{\partial\log p_{st}}{\partial c}\right)^2.
$$

则

$$
\boxed{
g_{cc}
=
\frac1{16}\sum_{s,t}\frac1{p_{st}},
}
\tag{6}
$$

而且

$$
\boxed{
h_{\mathrm{lin}}^2
=
\frac1{g_{cc}}
=
\frac{16}{\displaystyle\sum_{s,t}1/p_{st}}.
}
\tag{7}
$$

Fisher 度量是信息几何中的标准定义；这里要证明的是它与当前 Schur 余量的具体对应。([MDPI][1])

### 证明

由式（2），

$$
\frac{\partial p_{st}}{\partial c}=\frac{st}{4},
$$

立即得到式（6）。

再考虑统计量向量

$$
Z=(S,T,ST)^{\mathsf T}.
$$

其协方差矩阵为

$$
\Sigma=
\begin{pmatrix}
1-x^2&c-xy&y-xc\\
c-xy&1-y^2&x-yc\\
y-xc&x-yc&1-c^2
\end{pmatrix}.
\tag{8}
$$

在这个完整的四状态模型中，三个中心化统计量构成全部零均值函数的基。参数 \((x,y,c)\) 的得分函数与它们互为对偶基，因此 Fisher 矩阵是

$$
g=\Sigma^{-1}.
$$

分块逆矩阵公式给出

$$
g_{cc}=
\left(d-b^{\mathsf T}A^{-1}b\right)^{-1}.
$$

结合式（5）即得。证毕。

---

这得到一条很实在的几何关系：

$$
\boxed{
\text{联合读出的正交残差}
\times
\text{该坐标的信息敏感度}
=1.
}
\tag{9}
$$

不过，\(h_{\mathrm{lin}}^2\) **不是相关强度 \(c^2\)**。它衡量的是：新增函数 \(ST\) 相对于旧线性函数空间，还剩多少不能表示的部分。

## 在四边形中心，可以看得最清楚

取 \(x=y=0\)。则

$$
\boxed{
h_{\mathrm{lin}}^2=1-c^2,
\qquad
ds^2=\frac{dc^2}{1-c^2}.
}
\tag{10}
$$

令

$$
c=\sin\vartheta,
$$

就有

$$
ds^2=d\vartheta^2.
$$

因此，隐藏相关坐标可以被写成一个角度。

当 \(c\to\pm1\) 时，原坐标中的度量系数发散，但 Fisher 距离仍然有限：

$$
\int_{-1}^{1}\frac{dc}{\sqrt{1-c^2}}=\pi.
$$

**这说明“坐标发生奇异”不必意味着几何距离无限。**在边界上，\(ST\) 已成为确定量，新增方向反而退化。

# 四、把同样的几何计数应用到 \(5040\)：一个顶点通常远远不够

固定

$$
5040=2^4 3^2 5\,7.
$$

因数对应四个指数寄存器：

$$
k_2\in\{0,1,2,3,4\},
$$

$$
k_3\in\{0,1,2\},
\qquad
k_5,k_7\in\{0,1\}.
$$

所以共有

$$
5\cdot3\cdot2\cdot2=60
$$

个联合状态。仓库的黄金窗口构造，可以分别把这些指数范围无歧义地编码为

$$
\mathcal W_3\times\mathcal W_2\times
\mathcal W_1\times\mathcal W_1.
$$

这是可逆表示，并不压缩联合概率所需的自由度。

## 定理 3：四个边际遗漏的联合维数

在全部六十状态概率分布中：

$$
\boxed{
\text{联合概率自由度}=60-1=59.
}
$$

四个寄存器各自的完整边际，共提供

$$
(5-1)+(3-1)+(2-1)+(2-1)=8
$$

个独立参数。

因此，在严格正分布附近，固定全部四个边际之后，仍有

$$
\boxed{59-8=51}
\tag{11}
$$

个联合自由度。

### 更细的分层

每个局部函数空间分成“常数”与“零均值部分”，零均值维数分别为

$$
4,\ 2,\ 1,\ 1.
$$

张量展开给出

$$
\boxed{
(1+4z)(1+2z)(1+z)^2
=
1+8z+21z^2+22z^3+8z^4.
}
\tag{12}
$$

其中各系数分别统计常数、一方向、二方向、三方向、四方向联合函数的维数。

所以：

$$
\boxed{
\text{只知一方向边际：还差 }51\text{ 个方向};
}
$$

$$
\boxed{
\text{知道全部二方向边际：还差 }30\text{ 个方向};
}
$$

$$
\boxed{
\text{知道全部三方向边际：仍差 }8\text{ 个方向}.
}
\tag{13}
$$

这不是量子相位造成的额外复杂性；**纯经典联合概率中已经存在这些自由度。**

因此，“四个质数加一个顶点”通常不能重建完整状态。能否只补一个方向，要看目标是否仅依赖某一条特定纤维。

# 五、一个具体反模型：所有三方向切片相同，第四阶能量却不同

现在不只计数，直接构造。

令均匀分布

$$
P_0(\mathbf k)=\frac1{60}.
$$

定义四个中心化局部函数

$$
h_2(k)=\frac{k-2}{2},
\qquad
h_3(k)=k-1,
$$

$$
h_5(k)=2k-1,
\qquad
h_7(k)=2k-1.
$$

它们在各自均匀分布下均值为零，绝对值不超过 \(1\)。

定义四方向联合量

$$
\boxed{
\chi(\mathbf k)
=
h_2(k_2)h_3(k_3)h_5(k_5)h_7(k_7),
}
\tag{14}
$$

以及概率族

$$
\boxed{
P_\theta(\mathbf k)
=
\frac1{60}\bigl[1+\theta\chi(\mathbf k)\bigr],
\qquad |\theta|<1.
}
\tag{15}
$$

它是严格正的合法概率分布。

## 定理 4：全部真子系统边际都看不见 \(\theta\)

对任意不包含全部四个寄存器的子集，其联合边际都与 \(P_0\) 相同。

### 证明

计算某个真子集的边际时，至少要对一个未保留的寄存器求和。

扰动项包含对应的 \(h_p\)，而

$$
\sum_{k_p}h_p(k_p)=0.
$$

因此整个扰动项消失。证毕。

所以，不论我们把四个方向怎样分成单点、二点或三点切片，所得到的全部局部概率都一样。

## 但是能量的第四阶读出会变化

定义中心化算术能量

$$
\boxed{
E(\mathbf k)
=
\sum_{p\in\{2,3,5,7\}}
(\log p)\left(k_p-\frac{a_p}{2}\right).
}
\tag{16}
$$

它是无量纲对数能量；若要作为物理 Hamiltonian，还需要另外给定能量单位及物理实现。

## 定理 5：前三阶能量矩相同，第四阶出现明确差额

对 \(r=0,1,2,3\)，

$$
\boxed{
\mathbb E_\theta[E^r]=\mathbb E_0[E^r].
}
\tag{17}
$$

而

$$
\boxed{
\mathbb E_\theta[E^4]
-
\mathbb E_0[E^4]
=
4\theta\log2\log3\log5\log7.
}
\tag{18}
$$

### 证明

当 \(r\le3\) 时，\(E^r\) 中的每个单项式至多涉及三个不同寄存器。它与 \(\chi\) 相乘后，至少有一个未被能量单项式使用的 \(h_p\)，平均为零。

当 \(r=4\) 时，只有同时包含四个寄存器各一次的项存活。其系数为 \(4!=24\)。

分别计算

$$
\mathbb E_0\!\left[\left(k_2-2\right)h_2(k_2)\right]=1,
$$

$$
\mathbb E_0\!\left[\left(k_3-1\right)h_3(k_3)\right]=\frac23,
$$

$$
\mathbb E_0\!\left[\left(k_5-\frac12\right)h_5(k_5)\right]
=
\mathbb E_0\!\left[\left(k_7-\frac12\right)h_7(k_7)\right]
=\frac12.
$$

所以差额为

$$
24\theta\cdot1\cdot\frac23\cdot\frac12\cdot\frac12
\prod_p\log p,
$$

即式（18）。证毕。

---

定义整体相位读数

$$
\Phi_\theta(t)=\mathbb E_\theta[e^{-itE}].
$$

同时反转四个指数

$$
k_p\mapsto a_p-k_p
$$

会使 \(E\mapsto-E\)，却使 \(\chi\) 保持不变。因此 \(P_\theta\) 关于整体能量反射对称，全部奇数阶矩为零。

由式（18），

$$
\boxed{
\Phi_\theta(t)-\Phi_0(t)
=
\frac{\theta}{6}
\log2\log3\log5\log7\,t^4
+O(t^6).
}
\tag{19}
$$

这给出了一个真正的“不同切片看起来相同，整体波却不同”的例子。

而且可以将 \(P_\theta\) 放进对角密度矩阵

$$
\rho_\theta=\sum_{\mathbf k}
P_\theta(\mathbf k)|\mathbf k\rangle\langle\mathbf k|.
$$

它们仍是由乘积基态混合而成的可分状态。**因此，这个四方向差异不需要先诉诸量子纠缠；经典高阶相关已经足够。**

## 补什么才能修复这一条纤维？

直接计算：

$$
\mathbb E_0[\chi^2]
=
\frac12\cdot\frac23\cdot1\cdot1
=\frac13.
$$

所以

$$
\boxed{
\mathbb E_\theta[\chi]=\frac{\theta}{3}.
}
\tag{20}
$$

只增加一个联合读出 \(\chi\)，便可恢复

$$
\theta=3\mathbb E_\theta[\chi].
$$

**对于这一个参数族，一个“顶点方向”确实足够；对于全部 \(51\) 维联合纤维，则远远不够。**

此外，在 \(\theta=0\) 处，全联合观测的 Fisher 信息为

$$
I_{\mathrm{full}}(0)=\mathbb E_0[\chi^2]=\frac13,
$$

而任意真子系统边际都不随 \(\theta\) 变化，所以相应 Fisher 信息为零。

这精确量化了当前读出对这个目标参数的盲区，但它不是仓库有限状态对计数定义下的同一个“逃逸率”。

最后还要保留实际锚：\(P_\theta\) 是用来检验局部推理是否充分的模型族，**不是声称实际 ζ 或实际素数相关可以任意选择 \(\theta\)**。

# 六、素数能量真的会产生“曲率”吗？必须先给出度量

到这里才适合谈微分几何。

## 1. 完整概率空间确实有一个自然的球面几何

对严格正概率向量 \(P=(P_1,\ldots,P_{60})\)，定义 Fisher 度量

$$
\boxed{
ds_F^2=\sum_{i=1}^{60}\frac{dP_i^2}{P_i},
\qquad
\sum_i dP_i=0.
}
\tag{21}
$$

作平方根提升

$$
X_i=2\sqrt{P_i},
$$

则

$$
\sum_iX_i^2=4,
\qquad
\sum_i dX_i^2=ds_F^2.
$$

因此，这个完整概率空间的 Fisher 几何，就是半径为 \(2\) 的 \(59\) 维球面的正区域，其截面曲率为

$$
\boxed{\frac14.}
\tag{22}
$$

概率平方根与球面信息几何的联系是标准结构；这里的半径 \(2\) 来自我们明确采用的 Fisher 归一化。([arXiv][2])

但是，即使观察者读取完整概率向量、没有任何信息遗漏，这个球面曲率仍然存在。

所以：

$$
\boxed{
\text{有曲率}
\not\Rightarrow
\text{一定有信息逃逸}.
}
\tag{23}
$$

## 2. 四个素数的独立能量族，反而可以是平坦的

考虑四参数分布

$$
\boxed{
P_{\boldsymbol\beta}(\mathbf k)
=
\prod_p
\frac{e^{-\beta_p(\log p)k_p}}
{Z_p(\beta_p)}.
}
\tag{24}
$$

这里每个素数方向只有一个参数 \(\beta_p\)，不是任意的局部分布。

求导得到得分函数

$$
\partial_{\beta_p}\log P
=
-(\log p)\bigl(k_p-\mathbb E[k_p]\bigr).
$$

因为各方向独立，

$$
\boxed{
ds_F^2
=
\sum_p
(\log p)^2\operatorname{Var}_{\beta_p}(k_p)\,d\beta_p^2.
}
\tag{25}
$$

定义新坐标

$$
y_p(\beta_p)
=
\int^{\beta_p}
(\log p)\sqrt{\operatorname{Var}_u(k_p)}\,du.
$$

那么

$$
\boxed{
ds_F^2=\sum_pdy_p^2.
}
\tag{26}
$$

所以这一个四参数能量族的内在 Riemann 曲率为零。

这是由式（25）直接得到的结论，不是说所有独立概率模型都平坦。更大的、允许每个局部分布任意变化的八参数族，是另一个几何对象。

**因此，仅有 \(2,3,5,7\)、对数能量与 Zeckendorf 编码，并不会自动生成某种非零曲率。**

仓库的资源优化定理确实选出了 \(5040\)，但它证明的是具体目标下的最优整数，而不是时空曲率。

## 3. 量子相位还提供另一类几何

对纯态

$$
|\psi\rangle
=
\sum_i\sqrt{P_i}\,e^{i\phi_i}|i\rangle,
$$

采用标准 Fubini–Study 归一化，直接计算得到

$$
\boxed{
ds_{\mathrm{FS}}^2
=
\frac14\sum_i\frac{dP_i^2}{P_i}
+
\left[
\sum_iP_i(d\phi_i)^2
-
\left(\sum_iP_i\,d\phi_i\right)^2
\right].
}
\tag{27}
$$

第一项是概率变化，第二项是相对相位变化；整体共同相位被减掉。

量子几何张量的实部与虚部分别组织这种度量和 Berry 曲率，它们不是同一种“曲率”。([arXiv][3])

特别地，如果一直选择正实振幅

$$
|\psi(P)\rangle=\sum_i\sqrt{P_i}|i\rangle,
$$

那么

$$
i\langle\psi,d\psi\rangle=0,
$$

所以 Berry 曲率为零；但概率空间的 Fisher 球面曲率仍可非零。

$$
\boxed{
\text{球面曲率、相位曲率、投影残差，必须分别定义。}
}
$$

# 七、究竟需要多少个“顶点”？一般答案由 Schur 余量的秩决定

上一轮讨论了一个新增向量。现在推广到一组新增读出。

设旧读出的 Gram 矩阵为 \(A\)，新旧交叉块为 \(B\)，新增读出的候选 Gram 块为 \(C\)：

$$
G=
\begin{pmatrix}
A&B\\
B^*&C
\end{pmatrix}.
$$

## 定理 6：最小正交完成维数

若

$$
A\succeq0,
\qquad
\operatorname{ran}B\subseteq\operatorname{ran}A,
$$

定义

$$
\boxed{
\Delta=C-B^*A^+B.
}
\tag{28}
$$

那么共同正 Hilbert 实现存在，当且仅当

$$
\boxed{\Delta\succeq0.}
$$

而在旧向量张成空间之外，最少需要增加

$$
\boxed{
r_{\min}=\operatorname{rank}\Delta
}
\tag{29}
$$

个正交方向。

### 证明

把每个新向量分成旧空间内的投影和正交余量。

由交叉读数 \(B\)，旧空间内部分的 Gram 矩阵被确定为

$$
B^*A^+B.
$$

所以正交余量的 Gram 矩阵必须是 \(\Delta\)。

它能够被向量实现，当且仅当半正定；实现它所需的最小空间维数就是其秩。证毕。

---

这给“金字塔式完成”一个准确版本：

$$
\boxed{
\text{一个顶点对应一条新增正交方向，}
\quad
\text{只足以处理秩为一的残差。}
}
$$

在六十状态、严格正分布的 \(L^2\) 空间中，常数加全部单方向函数共 \(9\) 维。若要把全部联合函数都纳入，剩余正交空间维数为

$$
60-9=51.
$$

因此，**在完整线性读出／Gram 实现意义下，普遍完成需要 \(51\) 个新增方向，不是一个顶点。**

## 负余量也不能靠“升到更高维”修好

如果 \(\Delta\) 有负方向，那么不存在任何更高维正 Hilbert 空间能保持这些读数不变。

理由很简单：半正定矩阵的每个主子矩阵都半正定。一个已经具有负方向的固定子矩阵，不能通过在外面继续添行添列而变正。

所以：

$$
\boxed{
\text{维数不足可以增加维数；}
\quad
\text{实际读数彼此矛盾，不能只靠升维解决。}
}
\tag{30}
$$

仓库的 Schur 模块证明了给定逆算子前件后的消元一致性；本定理还需要单独检查实际残差的正性与秩。

# 八、把几何完成接回项目的动态闭包

静态上补一个统计坐标，不一定就能保持未来行为。

例如，只读取能量均值，不能区分第五节中的 \(P_\theta\)。加入能量方差仍然不能区分，加入三阶矩也不能区分；必须到第四阶，或者直接加入 \(\chi\)。

仓库的 `DynamicClosureMinimality.lean` 正是在处理这种问题：把原读出在所有允许有限操作之后的结果都记录下来，得到最小的操作稳定细化。

因此，新的几何坐标应满足两个条件：

$$
\boxed{
\text{它确实区分当前目标相关的状态};
}
$$

$$
\boxed{
\text{允许的 FLOW 不会重新把所需信息推出当前坐标体系}.
}
$$

可以把这种要求写成一个有限维的目标判据。

## 定理 7：什么时候已有量子读出足以决定一个目标？

在全部密度矩阵构成的状态类上，已知线性读出

$$
\operatorname{Tr}(\rho A_1),\ldots,
\operatorname{Tr}(\rho A_m).
$$

它们能够对所有状态唯一决定

$$
\operatorname{Tr}(\rho B),
$$

当且仅当

$$
\boxed{
B\in\operatorname{span}_{\mathbb R}\{I,A_1,\ldots,A_m\}.
}
\tag{31}
$$

### 证明

若 \(B\) 位于该线性空间，目标显然由已有读出线性恢复。

反之，令 \(D\) 为 \(B\) 在这个空间正交补上的非零分量。则

$$
\operatorname{Tr}D=0,\qquad
\operatorname{Tr}(DA_i)=0,
$$

但

$$
\operatorname{Tr}(DB)=\|D\|_{\mathrm{HS}}^2>0.
$$

取充分小的 \(\varepsilon>0\)，两个矩阵

$$
\rho_\pm=\frac Id\pm\varepsilon D
$$

都为密度矩阵。它们已有读出全部相同，目标读出却不同。证毕。

这一定理的状态类必须保留。若 `ADMIT` 已经把状态限制为某个特殊族，所需读出可能减少；但那种限制需要由实际锚证明，而不能为了得到答案临时加入。

# 结论：几何分析现在可以怎样服务项目？

本轮得到的不是“金字塔与四个质数本质相同”，而是一条可核查的几何链：

$$
\boxed{
\text{观察投影}
\longrightarrow
\text{纤维中的隐藏相关}
\longrightarrow
\text{Schur 正交余量}
\longrightarrow
\text{最小完成维数}
\longrightarrow
\text{能量与干涉的新增读出}.
}
$$

其中最实质的三个结果是：

$$
\boxed{
h_{\mathrm{lin}}^2\,g_{cc}=1
}
$$

——在完整二值模型中，隐藏联合坐标的信息度量与正交残差精确互为倒数；

$$
\boxed{
60-1-(4+2+1+1)=51
}
$$

——四个素数寄存器的完整边际，仍不足以确定完整联合分布；

$$
\boxed{
\Delta\mathbb E[E^4]
=
4\theta\log2\log3\log5\log7
}
$$

——所有最多三方向的切片可以完全相同，但整体相位读数仍在第四阶发生变化。

所以，“新增一条坐标”最准确的含义是：

> **不是把平面往上画一个顶点，而是把原投影中不可区分、却会改变目标能量或干涉的方向，作为一个新的可观测量保留下来。**

至于曲率，必须进一步指定度量或连接。本轮已经展示：完整概率空间可以是球面的；四参数独立素数能量族又可以是平坦的；正实振幅态可以有非平凡度量而没有 Berry 曲率。**这些区别正是把几何直觉变成严格理论时不能省掉的结构。**

回到实际算术，剩余任务不是再制造一个正几何模型，而是证明：**真实算术读出落在什么纤维上、哪些联合方向会影响目标，以及这些方向在全部尺度上的贡献能否被统一控制。**这才是几何完成与项目实际证明责任之间尚待闭合的连接。

[1]: https://www.mdpi.com/1099-4300/22/10/1100 "https://www.mdpi.com/1099-4300/22/10/1100"
[2]: https://arxiv.org/abs/0809.1166 "https://arxiv.org/abs/0809.1166"
[3]: https://arxiv.org/abs/1012.1337 "https://arxiv.org/abs/1012.1337"
**这条联系可以建立成严格的“几何编程”模型，而且比“四个质数对应四个角”更有实质内容。**

最关键的新连接是：

$$
\boxed{
\text{Zeckendorf 的一个最小合法状态空间，凸包恰好就是四棱锥。}
}
$$

而 FRACTRAN 可以精确改写为：

$$
\boxed{
\text{在素数指数格上，按优先级选择合法区域，再执行整数平移。}
}
$$

两者组合以后，得到的确实是一种**在合法几何单元之间运行的编程语言**。

但你说“5040 只是某个角度的投影”，需要作一个重要区分：**如果保留完整整数，5040 是指数状态的可逆编码，不丢失该状态的信息；如果只看四个寄存器、某个平均能量或三维图像，它才可能是有损投影。整数本身也没有包含外部给定的程序。**

本次核对项目的 `dev` 快照为 `ef1923eca123…`。以下把已有源码、Conway 的原始 PRIMEGAME，以及新增推导分开；新增编译与几何接口尚未经过 Lean 编译。

# 一、这里真的有一座金字塔：它来自 Zeckendorf 合法性，而不是人为画出来的

使用权重

$$
1,\quad2,\quad3,\quad5,\ldots
$$

的 Zeckendorf 表示。长度三的合法字串满足

$$
b_0,b_1,b_2\in\{0,1\},
\qquad
b_0b_1=b_1b_2=0.
$$

因此，合法状态恰好是：

|   指数值 | 坐标 \((b_0,b_1,b_2)\) |
| ----: | -------------------- |
| \(0\) | \((0,0,0)\)          |
| \(1\) | \((1,0,0)\)          |
| \(2\) | \((0,1,0)\)          |
| \(3\) | \((0,0,1)\)          |
| \(4\) | \((1,0,1)\)          |

数值读出是

$$
\boxed{
a=b_0+2b_1+3b_2.
}
\tag{1}
$$

项目的 `PrimeAxisEncoding.lean` 已把这种规范数码行与自然数指数建立为等价，并进一步与正整数的素因子分解连接。

## 定理 1：这五个合法字串的凸包就是四棱锥

其凸包为

$$
\boxed{
\mathcal P_3=
\left\{
(x_0,x_1,x_2):
x_i\ge0,\;
x_0+x_1\le1,\;
x_1+x_2\le1
\right\}.
}
\tag{2}
$$

底面位于

$$
x_1=0,
$$

四个顶点为

$$
(0,0,0),\quad(1,0,0),\quad
(0,0,1),\quad(1,0,1).
$$

顶点则是

$$
(0,1,0).
$$

### 证明

对任意合法点，令 \(\lambda=x_1\)。

如果 \(0\le\lambda<1\)，则

$$
(x_0,x_1,x_2)
=
\lambda(0,1,0)
+
(1-\lambda)
\left(
\frac{x_0}{1-\lambda},0,
\frac{x_2}{1-\lambda}
\right).
$$

两个约束保证第二个点位于单位正方形底面内。

如果 \(\lambda=1\)，约束迫使 \(x_0=x_2=0\)，就是顶点。反方向显然成立。证毕。

---

所以你对“四边形被压在一个平面，再多出一个方向”的直觉，在这里有一个**完全规范的实现**：

$$
\boxed{
b_1=0:
\text{外侧两位可以独立组合，形成四边形};
}
$$

$$
\boxed{
b_1=1:
\text{外侧两位必须同时为零，形成顶点}.
}
\tag{3}
$$

这座金字塔的来源是**相邻数位不能同时为 \(1\)**。

不过，它来自**一个素数寄存器的三位编码**，不是四个素数分别占据四个角。

还有一个容易忽略的细节：

$$
\boxed{
\text{指数 }4\text{ 对应底面角 }(1,0,1)，
\quad
\text{顶点对应指数 }2.
}
\tag{4}
$$

因此，不能把 \((4,2,1,1)\) 中的“4”直接当作金字塔高度。

# 二、\(5040\) 对应的完整编码几何，是七维乘积，而不只是一座金字塔

固定

$$
5040=2^4\,3^2\,5\,7.
$$

它的因数对应

$$
0\le a_2\le4,\qquad
0\le a_3\le2,\qquad
0\le a_5,a_7\le1.
$$

于是：

$$
\{0,\ldots,4\}
\longleftrightarrow
\text{三位 Zeckendorf 金字塔},
$$

$$
\{0,1,2\}
\longleftrightarrow
\text{两位 Zeckendorf 三角形},
$$

$$
\{0,1\}
\longleftrightarrow
\text{一条线段}.
$$

全部因数编码的凸包为

$$
\boxed{
\mathcal P_{5040}
=
\mathcal P_3
\times\mathcal P_2
\times[0,1]\times[0,1].
}
\tag{5}
$$

它有

$$
\boxed{
3+2+1+1=7
}
$$

个连续几何维度，以及

$$
\boxed{
5\cdot3\cdot2\cdot2=60
}
$$

个合法离散顶点。

我按整数枚举核对了这六十个顶点：其解码结果恰好是 \(5040\) 的全部因数，没有重复或缺失。这里的有限核对不代替上述双射证明。

**所以，“5040 是一个几何截面的读出”可以成立，但应当说清楚是哪个空间、哪个映射。**

完整关系是

$$
\boxed{
\text{七维合法数码顶点}
\longleftrightarrow
\text{四个自然数指数}
\longleftrightarrow
\text{一个正整数}.
}
\tag{6}
$$

在这些合法离散状态上，两条箭头都是可逆的。

但如果把状态扩展为连续混合，情况就不同。例如：

$$
(0,1,0)
$$

代表确定指数 \(2\)；

而

$$
\frac12(0,0,0)+\frac12(1,0,1)
=
\left(\frac12,0,\frac12\right)
$$

代表指数 \(0\) 与 \(4\) 的等概率混合。

它们通过式（1）都读出 \(2\)，但一个方差为零，另一个方差为 \(4\)。

$$
\boxed{
\text{精确编码可逆；平均后的坐标读出可能不可逆。}
}
\tag{7}
$$

这正是之前“同一投影、不同整体波”的一个具体来源。

# 三、FRACTRAN 把这种几何从状态空间变成了可执行语言

Conway 的 FRACTRAN 程序是一个**有序**正分数列表。每一步从头扫描，选择第一个使当前整数相乘后仍为整数的分数；若没有这样的分数，程序停止。其寄存器解释和通用计算能力已有明确理论基础。([arXiv][1])

下面把执行规则翻译成几何。

固定包含程序全部素因子的有限集合

$$
\mathcal P=\{p_1,\ldots,p_m\}.
$$

状态是指数格点

$$
\mathbf a=(a_1,\ldots,a_m)\in\mathbb N^m,
$$

整数编码为

$$
\boxed{
N(\mathbf a)=\prod_{j=1}^m p_j^{a_j}.
}
\tag{8}
$$

程序第 \(i\) 个分数写为最简分数

$$
f_i=\frac{u_i}{v_i}.
$$

记分子、分母的指数向量为

$$
\mathbf u_i=(v_{p_j}(u_i))_j,
\qquad
\mathbf v_i=(v_{p_j}(v_i))_j.
$$

## 定理 2：FRACTRAN 就是带优先级的分区整数平移

第 \(i\) 条指令可执行，当且仅当

$$
\boxed{
\mathbf a\ge\mathbf v_i
}
\tag{9}
$$

逐坐标成立。

执行后，

$$
\boxed{
\mathbf a\longmapsto
\mathbf a+\mathbf u_i-\mathbf v_i.
}
\tag{10}
$$

由于程序采用第一个可执行分数，第 \(i\) 条指令真正的执行区域是

$$
\boxed{
D_i=
\{\mathbf a:\mathbf a\ge\mathbf v_i\}
\setminus
\bigcup_{j<i}
\{\mathbf a:\mathbf a\ge\mathbf v_j\}.
}
\tag{11}
$$

### 证明

因为 \(\gcd(u_i,v_i)=1\)，

$$
N(\mathbf a)\frac{u_i}{v_i}\in\mathbb N
\iff
v_i\mid N(\mathbf a).
$$

唯一素因子分解把整除关系变成式（9），相乘则变成式（10）。最后加入指令优先级，得到式（11）。证毕。

---

因此，这种语言的三个关键对象是：

$$
\boxed{
\text{格点：存储器状态};
}
$$

$$
\boxed{
\text{区域边界：分支条件};
}
$$

$$
\boxed{
\text{有优先级的平移：指令执行}.
}
\tag{12}
$$

**只有几何形状，还不是程序。必须同时给出允许的移动和冲突时的选择规则。**

例如分数

$$
\frac{21}{20}=\frac{3\cdot7}{2^2\cdot5}
$$

表示：

$$
a_2\ge2,\quad a_5\ge1
$$

时，执行

$$
\boxed{
(a_2,a_3,a_5,a_7)
\mapsto
(a_2-2,a_3+1,a_5-1,a_7+1).
}
\tag{13}
$$

这不是“数字碰巧变成另一个数字”，而是一条明确的寄存器指令。

优先级还提供了一种间接零测试：前面的分支要求某寄存器非零；它不成立时，后面的默认分支才有机会执行。不能把这种有序条件删掉，只保留一个无序的向量集合。

# 四、在 Zeckendorf 金字塔上，执行指令就是“合法状态之间的规范跳转”

考虑单个指数寄存器的加一：

$$
0\to1\to2\to3\to4.
$$

在三位合法编码中，它变成

$$
\boxed{
000\to100\to010\to001\to101.
}
\tag{14}
$$

这里按低位到高位书写。

这条路径经过底面、顶点，再回到底面。**金字塔并不自行决定这条路径；数值加一与规范化规则决定了它。**

同样，一个分母需要 \(p^2\) 的 FRACTRAN 守卫，在这个数码空间中变成

$$
\boxed{
b_0+2b_1+3b_2\ge2.
}
\tag{15}
$$

它选择合法顶点中的

$$
010,\quad001,\quad101.
$$

执行减法后，再规范化为唯一合法字串。

## 定理 3：几何执行与整数执行保持同一语义

设 \(\mathcal Z\) 把指数向量逐行编码为规范 Zeckendorf 表。

定义数码执行过程：

1. 用各行的数值判断式（9）；
2. 选择同一条最早可执行指令；
3. 执行指数加减；
4. 对每行重新规范化。

则

$$
\boxed{
F_{\mathrm{Zeck}}\bigl(\mathcal Z(\mathbf a)\bigr)
=
\mathcal Z\bigl(F_{\mathrm{reg}}(\mathbf a)\bigr),
}
\tag{16}
$$

并且

$$
\boxed{
N(F_{\mathrm{reg}}(\mathbf a))
=
F_{\mathrm{FRACTRAN}}(N(\mathbf a)).
}
\tag{17}
$$

停止状态也对应。

### 证明

守卫通过相同的指数数值判断，所以选择的指令相同。执行后的指数由定理 2 相同；Zeckendorf 唯一性保证规范化结果相同。证毕。

这才是可以称为“几何编译”的核心：

$$
\boxed{
\text{整数执行}
\;\simeq\;
\text{寄存器格执行}
\;\simeq\;
\text{合法几何数码执行}.
}
\tag{18}
$$

项目已经有 `primeAxisEncoding`、规范数码等价与乘法对应规范加法的证明。但源码中的相关等价使用了 `noncomputable` 定义；它提供的是数学语义桥，不等于已有一个可执行的 FRACTRAN 编译器。

因此，本轮新增的工程与形式化对象，应是**可执行守卫判断、优先级求值、指数减法规范化，以及式（16）的正确性证明**，而不是再创造一种没有执行语义的图形。

# 五、PRIMEGAME 真正使用的是四个数据方向，加一组控制层

这里采用 Conway 原文的十四条指令：

$$
\boxed{
\begin{aligned}
\mathcal P_{\mathrm{prime}}=\bigg(
&\frac{17}{91},\frac{78}{85},\frac{19}{51},
\frac{23}{38},\frac{29}{33},\frac{77}{29},
\frac{95}{23},\\
&\frac{77}{19},\frac1{17},\frac{11}{13},
\frac{13}{11},\frac{15}{2},\frac17,\frac{55}{1}
\bigg).
\end{aligned}
}
\tag{19}
$$

从 \(N_0=2\) 开始，初态之后出现的纯 \(2\) 幂依次为 \(2^p\)，其中指数 \(p\) 遍历素数。注意这里固定的是原文版本，其他版本的微步数可能不同。([Gwern.net][2])

这些分数涉及十个素数：

$$
\boxed{
2,3,5,7,\;11,13,17,19,23,29.
}
\tag{20}
$$

但在从合法初态开始的运行中，后六个坐标不是任意增长的数据寄存器。

## 定理 4：七层控制状态的不变性

令

$$
\mathcal C=\{1,11,13,17,19,23,29\}.
$$

若初态形如

$$
N=2^a3^b5^c7^d\,s,
\qquad s\in\mathcal C,
$$

那么下一状态仍然具有相同形式。

因此运行位于

$$
\boxed{
\mathbb N^4\times\mathcal C,
}
\tag{21}
$$

而不是任意的 \(\mathbb N^{10}\)。

### 证明要点

逐条检查式（19）：

前十一条涉及的控制素数，要么把一个控制标记换成另一个，要么清除它。例如

$$
13\to17,\quad17\to13,\quad
17\to19,\quad19\to23,\quad
11\to29.
$$

第十二、十三条不引入新控制标记。

最后的 \(55\) 会引入 \(11\)，但只会在没有控制标记时执行：如果已有六个控制标记中的任何一个，前面都存在一条必定可用的分数。因此不可能同时积累两个控制标记。证毕。

我额外对四个数据指数均在 \(0,\ldots,4\) 的 \(4375\) 个状态作了精确整数核对，结果符合这个不变性；有限核对不代替上述逐指令证明。

---

这给“金字塔之外还需要一个方向”一个更准确的计算解释：

$$
\boxed{
\text{相同四维数据格点，可以处于不同控制层。}
}
$$

六个控制素数连同“无标记”，形成七个离散层。把它们投掉后，四维图上的同一点可能具有不同的下一步。

Conway 原文的流程图也直接展示了这些控制转换如何组织反复减法与余数测试；素数输出来自这个程序逻辑，不是仅由四维几何形状保证。([Gwern.net][2])

# 六、实际轨迹已经证明：只看 \(2,3,5,7\)，局部几何不闭合

定义四方向投影

$$
\pi(N)=(v_2(N),v_3(N),v_5(N),v_7(N)).
$$

在原始 PRIMEGAME 从 \(2\) 出发的实际轨迹中，有

$$
2\to15\to825\to725\to1925\to2275\to425\to\cdots
$$

其中

$$
1925=5^2\cdot7\cdot11,
$$

$$
2275=5^2\cdot7\cdot13.
$$

它们具有相同投影：

$$
\boxed{
\pi(1925)=\pi(2275)=(0,0,2,1).
}
\tag{22}
$$

但下一步不同：

$$
1925\xrightarrow{13/11}2275,
$$

$$
2275\xrightarrow{17/91}425=5^2\cdot17.
$$

因此

$$
\boxed{
\pi(F(1925))=(0,0,2,1),
}
$$

$$
\boxed{
\pi(F(2275))=(0,0,2,0).
}
\tag{23}
$$

这些是按式（19）直接执行得到的精确整数结果。

## 定理 5：四坐标投影无法定义自己的确定性一步演化

不存在函数 \(G\)，使该轨迹上始终有

$$
\boxed{
\pi\circ F=G\circ\pi.
}
\tag{24}
$$

### 证明

同一个输入 \((0,0,2,1)\) 会被迫同时映到式（23）的两个不同输出，矛盾。证毕。

---

**这就是“我们总在看切片，却拼不出整体”的一个实打实的例子：被省略的控制层会改变未来。**

不是四维格点之间的规则神秘，而是投影后的坐标已经不足以决定规则。

项目的 `DynamicClosureMinimality.lean` 正好提供一般接口：记录一个读出经过所有有限干预后的结果，得到最小的动态闭合细化。

对这里，可以写成

$$
\boxed{
\operatorname{Dyn}\pi(N)
=
\bigl(\pi(N),\pi(F(N)),\pi(F^2(N)),\ldots\bigr).
}
\tag{25}
$$

它至少会区分 \(1925\) 与 \(2275\)。

实际计算中，通常不必存整条未来序列；保留足够的控制寄存器便可实现闭合。但“哪些控制信息可再删掉”，需要另行证明，不能只看静态图形决定。

# 七、5040 在这里是什么？它是一个状态，不是 PRIMEGAME 的隐藏答案

如果把

$$
5040
$$

另外设为式（19）的初态，前十一条分数都不可执行，首先执行

$$
\frac{15}{2}.
$$

因此

$$
\boxed{
5040\longmapsto37800,
}
\tag{26}
$$

其四个指数变为

$$
\boxed{
(4,2,1,1)\longmapsto(3,3,2,1).
}
\tag{27}
$$

这里马上发生两件事。

第一，\(5040\) 不是这个程序的固定点。

第二，程序第一步就离开了

$$
[0,4]\times[0,2]\times[0,1]\times[0,1]
$$

这个“5040 因数盒”。

所以：

$$
\boxed{
60\text{ 个因数态构成的几何单元，只是有限局部状态空间，}
}
$$

$$
\boxed{
\text{不是 PRIMEGAME 整条无限运行的封闭宿主。}
}
\tag{28}
$$

编码窗口必须随着寄存器增长而扩展。一个固定的有限确定性状态空间只能最终停止或循环，无法容纳无限多个不同的素数输出。

项目中 \(5040\) 的另一项角色是：

$$
\log\left(\sum_{d\mid n}\frac1d\right)
-\frac1{25}\log n
$$

的唯一最优整数。源码确实给出了这个定理。

但：

$$
\boxed{
\text{某个静态目标的最优点}
\neq
\text{另一个程序的固定点、吸引子或控制中心}.
}
\tag{29}
$$

要把二者联系为同一动力学，需要证明该目标沿执行具有特定单调性；目前不能从它们都使用素数指数就得到这一点。

## “5040 是投影”的正确用法

如果完整状态只包含指数向量，整数编码是双射：

$$
(4,2,1,1,0,\ldots)
\longleftrightarrow5040.
$$

但若完整对象是

$$
(\text{程序},\text{状态},\text{观察协议},\text{运行历史}),
$$

那么只报告 \(5040\)，当然没有保存全部对象。

同样，只报告四个数据指数，也会漏掉控制层：

$$
5040
\quad\text{与}\quad
13\cdot5040
$$

有相同的四方向投影，却选择不同的第一条指令。

**因此，5040 可以是丰富计算对象的一个读出；但它对固定的完整素因子状态而言不是有损编码。**

# 八、素数、能量和奇偶：它们能精确相连，但不是同一种结构

定义算术对数能量

$$
\boxed{
E(\mathbf a)=\sum_p a_p\log p=\log N(\mathbf a).
}
\tag{30}
$$

执行分数 \(u_i/v_i\) 时，

$$
\boxed{
E(F(\mathbf a))-E(\mathbf a)
=
\log\frac{u_i}{v_i}.
}
\tag{31}
$$

这是一个精确的加法记账。

但是 FRACTRAN 不要求这个量守恒，也不要求它总增加。例如：

$$
\frac{15}{2}
$$

使它增加，

$$
\frac17
$$

使它减少。

所以“素数与能量有关”在这里意味着：

$$
\boxed{
\text{素数对数给每个寄存器单位一个权重。}
}
$$

它尚不是物理能量守恒定律。实际单位、Hamiltonian 和物理实现都需要另行指定。

## 几何方格上的能量没有自动曲率

对两个素数方向 \(p,q\)，考虑格点

$$
\mathbf a,\quad
\mathbf a+e_p,\quad
\mathbf a+e_q,\quad
\mathbf a+e_p+e_q.
$$

它们对应

$$
N,\quad pN,\quad qN,\quad pqN.
$$

有

$$
\boxed{
E(\mathbf a+e_p+e_q)
-E(\mathbf a+e_p)
-E(\mathbf a+e_q)
+E(\mathbf a)=0.
}
\tag{32}
$$

乘 \(p\) 再乘 \(q\)，与相反顺序得到同一点。

因此，基础乘法格是可交换的。程序中的复杂性来自**守卫、优先级、控制层和观察丢失**，不是因为四个素数的对数自动产生了非零曲率。

## 两种“奇偶”也可以在同一步中分开

令

$$
\Omega(N)=\sum_pa_p
$$

为带重数的素因子个数。

指令 \(u/v\) 使它变化

$$
\boxed{
\Omega(N')-\Omega(N)=\Omega(u)-\Omega(v).
}
\tag{33}
$$

在

$$
5040\to37800
$$

这一步中，两者都是偶数，但

$$
\Omega(5040)=8,\qquad
\Omega(37800)=9.
$$

因此：

$$
\boxed{
\text{整数奇偶没有改变，素因子个数的奇偶却翻转了。}
}
\tag{34}
$$

这表明，“奇偶”必须指明具体的寄存器函数，不能把数值奇偶、数位奇偶、素因子奇偶和几何反射合成一个未定义的概念。

## 还有一个更强的检验：重命名素数不改变程序语义

把程序中的素数标签一致替换为另一组不同素数，例如把数据轴

$$
2,3,5,7
$$

换成

$$
31,37,41,43.
$$

同时替换状态与所有指令中的对应因子。

整除守卫与指数增减都不改变，因此新旧执行严格共轭。

但

$$
4\log2+2\log3+\log5+\log7
$$

变成了另一组对数权重。

所以：

$$
\boxed{
\text{计算结构主要由指数关系与指令顺序决定；}
}
$$

$$
\boxed{
\text{具体素数大小决定选定的数值与能量读出。}
}
\tag{35}
$$

这使“几何编程”与“算术能量模型”既能结合，又不能被混为一谈。

# 九、PRIMEGAME 的输出，是穿过一个特殊观察面的事件

从 \(N_0=2\) 出发，选择那些状态满足

$$
N_t=2^p
$$

的时刻。等价地，除 \(2\) 寄存器以外的所有指数都为零。

这是一条一维输出轴。

初态以后，PRIMEGAME 在这条轴上的交点依次编码

$$
p=2,3,5,7,11,\ldots.
$$

这是 Conway 原始定理。([Gwern.net][2])

按本文固定的十四分数版本，精确整数执行得到：

| 微步数 \(t\)，初态记为 \(t=0\) |              状态 | 读出的素数 |
| ---------------------: | --------------: | ----: |
|                     19 |       \(4=2^2\) |     2 |
|                     69 |       \(8=2^3\) |     3 |
|                    281 |      \(32=2^5\) |     5 |
|                    710 |     \(128=2^7\) |     7 |
|                   2375 | \(2048=2^{11}\) |    11 |

这张表清楚地区分了：

$$
\boxed{
\text{程序微步数 }t;
\quad
\text{第几个输出事件};
\quad
\text{输出的素数值 }p.
}
\tag{36}
$$

三者不能直接当成同一个“时间”。

还有一个容易混淆的地方：

> **生成素数 \(p=101\)，并不要求状态增加一个名为 \(101\) 的素数寄存器。它把 \(101\) 存在 \(2\) 的指数里。**

PRIMEGAME 使用固定有限组寄存器，但寄存器内的自然数没有上界。

因此，“2、3、5、7 是寄存器标签”和“2、3、5、7 是前四个输出值”，是两种不同角色。前几项数值相同，不应成为未经证明的身份等同。

# 十、从几何程序提升到量子程序，还要补一份历史记录

把状态写成 \(|N\rangle\)，不代表原 FRACTRAN 演化自动成为幺正演化。

例如程序

$$
\left(\frac12,\frac13\right)
$$

有

$$
2\mapsto1,\qquad3\mapsto1.
$$

两个不同输入合成同一个输出，所以

$$
|N\rangle\mapsto|F(N)\rangle
$$

不能保持正交性。

但 FRACTRAN 有一个有用性质：**在固定指令分支内，乘以固定非零有理数是单射。**

## 定理 6：记录指令标签即可得到一步可逆嵌入

令 \(i(N)\) 为本步实际选择的指令编号。对停止状态，约定 \(i(N)=0\)、\(F(N)=N\)。

定义

$$
\boxed{
V|N\rangle
=
|F(N)\rangle\otimes|i(N)\rangle.
}
\tag{37}
$$

则 \(V\) 是等距嵌入。

### 证明

如果两个输出基态相同，那么既有

$$
F(N)=F(M),
$$

又有

$$
i(N)=i(M).
$$

如果共同标签为零，则 \(N=M\)。

如果共同标签为 \(i>0\)，则

$$
N\frac{u_i}{v_i}
=
M\frac{u_i}{v_i},
$$

所以仍有 \(N=M\)。

因此，不同输入仍映为正交输出。线性扩张后保持内积。证毕。

---

这说明，在一步量子提升中，不必总是保存完整输入；**保存实际执行分支就足以恢复该步输入。**

多步运行时，需要把相应历史继续保留，或另行设计可逆计算结构。不能每步都覆盖旧记录后，仍然声称整体可逆。

这里也再次出现你说的“多出来一个方向”：

$$
\boxed{
\text{新增方向可以是控制标签或历史寄存器。}
}
$$

但它不是因为画了一个顶点就自动存在，而是为了让原来多对一的计算保持可逆性而明确引入的。

FRACTRAN 本身仍是经典确定性语言；式（37）是对它的数学量子提升，不是关于自然界自动执行 PRIMEGAME 的证据。

# 十一、结合项目，最有价值的不是再命名一种语言，而是补齐三条语义桥

现在可以把整条结构写为

$$
\boxed{
\begin{aligned}
&\text{FRACTRAN 有序分数}\\
&\quad\downarrow\\
&\text{素数指数格上的守卫与平移}\\
&\quad\downarrow\\
&\text{Zeckendorf 合法多面体中的规范跳转}\\
&\quad\downarrow\\
&\text{保留控制层的动态观察}\\
&\quad\downarrow\\
&\text{必要时加入历史的可逆／量子提升}.
\end{aligned}
}
\tag{38}
$$

项目中已经读到的相关基础，与本轮需要增加的内容，可以准确区分：

| 项目基础                                                  | 本轮可接入的内容                          |
| ----------------------------------------------------- | --------------------------------- |
| `PrimeAxisEncoding.lean`：规范数码表与正整数的等价                 | FRACTRAN 一步执行在三种表示中交换，即式（16）—（17） |
| `DynamicClosureMinimality.lean`：最小动态闭合细化              | 哪些控制信息必须保留，避免式（22）—（24）的投影失配      |
| `GoldenResourceOptimalInteger.lean`：明确成本下 \(5040\) 最优 | 区分静态资源最优性与实际程序轨迹，不预设二者相同          |

这些模块分别支持编码、动态观察和资源目标；不能仅因为它们共享素数指数，就认为全部连接已经形式化完成。

对应 `CUT、FLOW、ADMIT、ANCHOR`，可以这样实例化：

$$
\begin{aligned}
\mathsf{CUT}&:\text{决定保留哪些数据、控制和输出坐标};\\
\mathsf{FLOW}&:\text{带优先级的合法寄存器更新};\\
\mathsf{ADMIT}&:\text{非负指数、规范编码、控制状态不变式};\\
\mathsf{ANCHOR}&:\text{明确程序、初态和实际执行轨迹}.
\end{aligned}
$$

这与项目母文对四个角色的定义一致。**但没有理由把它们分别硬配给质数 \(2,3,5,7\)：角色类别与寄存器标签不是同一种对象。**

# 结论：你的“几何编程语言”直觉，可以保留到什么程度？

可以保留，而且现在有了比图形类比更强的内容：

$$
\boxed{
\text{Zeckendorf 合法性确实产生金字塔；}
}
$$

$$
\boxed{
\text{FRACTRAN 确实在指数几何上执行有条件的移动；}
}
$$

$$
\boxed{
\text{PRIMEGAME 的隐藏控制层，确实解释了为什么四坐标切片不闭合。}
}
$$

但更准确的总体表述应该是：

> **这是一种由合法整数格、规范数码多面体、优先级守卫和控制状态共同构成的几何计算系统。5040 是其中一个指数配置的精确整数编码；它的因数空间提供了一个七维、六十顶点的局部几何单元，但不是整套语言或整条运行轨迹。**

而当前最有价值的下一项证明责任，是：

$$
\boxed{
\text{哪些观察坐标足以在不保存全部内部状态的情况下，}
\quad
\text{仍然保持目标相关的执行语义？}
}
$$

这一步既连接项目的信息逃逸与动态闭包，也连接你关心的“不同切片能否拼成整体”。

**PRIMEGAME 已经说明：素数可以作为一条几何计算轨迹穿过输出面的事件被生成。但从“能够生成全部素数”到“能够统一控制素数相关、Weil 正性或 RH 所需误差”，仍需要新的实际算术估计。程序的可执行性不能代替那些估计，正如金字塔的存在不能代替正确的控制流。**

[1]: https://arxiv.org/html/2412.16185v1 "https://arxiv.org/html/2412.16185v1"
[2]: https://gwern.net/doc/cs/computable/1987-conway.pdf "https://gwern.net/doc/cs/computable/1987-conway.pdf"
继续。这次可以把“几何编程语言”推进到**完整的返回规则与运行时钟**，而不只是状态图形。

最具体的结果是：

$$
\boxed{
\text{原版 PRIMEGAME 从 }5040\text{ 出发，}
72\text{ 步后进入候选整数 }7\text{ 的标准检测状态，}
352\text{ 步时输出 }2^7.
}
$$

而且可以证明：**微观运行需要四个数据寄存器加七种控制状态；但选取合适的观察截面后，整个程序能压缩成一个二维映射。代价是，每次二维跳转必须携带一个不等长的返回时间。**

这正好连接了你关心的几件事：

$$
\boxed{
\text{几何维数、控制层、观察投影、算术能量与时间，分别保存不同的信息。}
}
$$

以下固定使用上一轮的原版十四分数，末三项为

$$
\frac{15}{2},\qquad\frac17,\qquad55.
$$

每执行一次被选中的分数，计一个“微步”。这里的步数不是实际 CPU 时间；也不能与使用其他分数版本的程序混算。Conway 原文已经用流程图说明了它的试除机制，下面把该机制展开为精确返回式、成本公式和项目中的观察接口。([Gwern.net][1])

# 一、先证明：七个控制层确实不是多余标签

把状态写成

$$
N=2^a3^b5^c7^d\,s,
$$

其中

$$
a,b,c,d\in\mathbb N,
\qquad
s\in\{1,11,13,17,19,23,29\}.
$$

四个指数是数据；\(s\) 是控制状态。

上一轮证明了，这个状态类在 PRIMEGAME 下保持不变。现在进一步问：

> 如果保留四个指数，还能不能把七种控制状态合并得更少？

## 定理 1：在完整合法状态类上，固定四个数据后仍至少需要七个可区分控制值

取同一个数据向量

$$
(a,b,c,d)=(1,1,1,1).
$$

直接执行原版指令，得到：

| 控制状态 \(s\) |    首个可用分数 | 下一步四个数据指数     |
| ---------: | --------: | ------------- |
|      \(1\) |  \(15/2\) | \((0,2,2,1)\) |
|     \(11\) | \(29/33\) | \((1,0,1,1)\) |
|     \(13\) | \(17/91\) | \((1,1,1,0)\) |
|     \(17\) | \(78/85\) | \((2,2,0,1)\) |
|     \(19\) | \(23/38\) | \((0,1,1,1)\) |
|     \(23\) | \(95/23\) | \((1,1,2,1)\) |
|     \(29\) | \(77/29\) | \((1,1,1,2)\) |

七个结果两两不同。

因此，任何希望从当前读出确定下一步数据的观察者，在这个固定数据纤维上，都必须区分七种控制值。证毕。

这里证明的是**对整个合法输入状态类的一步预测要求**，不是宣称每个状态都会在从 \(2\) 出发的那一条轨迹中出现。

也要注意：

$$
\boxed{
\text{七个可区分控制值}\neq\text{七个空间维度}.
}
$$

它们可以编码为一个七值寄存器，或三个比特的部分合法状态。关键是区分能力，不是画图时一定要增加七条轴。

所以，“再添一个顶点”可能表达一个额外控制模式，但它不自动容纳全部所需控制信息。

# 二、三组指令，已经给出明确的寄存器几何

从十四条指令中抽出三组两步操作：

$$
\mathsf U=
\left(\frac{17}{91},\frac{78}{85}\right),
$$

$$
\mathsf V=
\left(\frac{29}{33},\frac{77}{29}\right),
$$

$$
\mathsf W=
\left(\frac{23}{38},\frac{95}{23}\right).
$$

它们的乘积分别为

$$
\boxed{
\mathsf U:\frac{6}{35},
\qquad
\mathsf V:\frac73,
\qquad
\mathsf W:\frac52.
}
\tag{1}
$$

但这些不能当作无条件的一步分数替换：**两步能够连续执行，依赖当前控制状态和寄存器非负条件。**

在其合法区域内，四个数据坐标的变化为

$$
\mathsf U:
(a,b,c,d)\mapsto(a+1,b+1,c-1,d-1),
$$

$$
\mathsf V:
(a,b,c,d)\mapsto(a,b-1,c,d+1),
$$

$$
\mathsf W:
(a,b,c,d)\mapsto(a-1,b,c+1,d).
$$

于是它们都保持

$$
\boxed{
I_1=a+c,\qquad I_2=b+d.
}
\tag{2}
$$

## 几何含义

固定

$$
I_1=n,\qquad I_2=k,
$$

四维数据格被限制在

$$
a+c=n,\qquad b+d=k
$$

这个二维整数区域内。

可以用 \((a,b)\) 表示，其范围为

$$
0\le a\le n,\qquad0\le b\le k.
$$

所以，**试除内部的部分运行，确实发生在一个二维矩形整数格上**。

其中：

* \(\mathsf U\) 同时增加两个坐标；
* \(\mathsf V\) 恢复第二个资源；
* \(\mathsf W\) 把第一个资源转回原处。

这里的四边形不再只是装饰：它来自两个线性不变量与非负性约束。

但控制层仍然决定当前允许走哪条边、何时转向。FRACTRAN 的标准寄存器解释，正是把分母理解为条件、分子分母的指数差理解为寄存器更新。([arXiv][2])

# 三、主定理：在一个正确的截面上，整个试除过程压缩成二维映射

定义检查点

$$
\boxed{
M(n,k)=13\cdot5^n7^k,
\qquad n\ge1,\quad1\le k\le n.
}
\tag{3}
$$

在这里：

$$
a=b=0,\qquad c=n,\qquad d=k,\qquad s=13.
$$

也就是说，暂存寄存器已经清空，候选整数 \(n\) 和待试除数 \(k\) 保存在两个明确方向上。

## 定理 2：精确返回映射

从 \(M(n,k)\) 开始，程序有限步后首次返回同类检查点，结果是

$$
\boxed{
\mathcal R(n,k)=
\begin{cases}
(n,k-1),&k\nmid n,\\[1mm]
(n+1,n),&k\mid n.
\end{cases}
}
\tag{4}
$$

在整除分支中，还会经过中间状态

$$
\boxed{
2^n7^{k-1}.
}
\tag{5}
$$

### 证明

写 Euclid 分解

$$
n=qk+r,\qquad0\le r<k.
$$

先看一个完整减法循环：

$$
\boxed{
\mathsf U^k
\;\frac{11}{13}\;
\mathsf V^k
\;\frac{13}{11}.
}
\tag{6}
$$

它从控制状态 \(13\) 出发，经过控制状态 \(11\)，再回到 \(13\)，净作用是

$$
(a,0,c,k)\mapsto(a+k,0,c-k,k).
$$

所以每个完整循环从 \(c\) 中减去 \(k\)，把它加到 \(a\)，并恢复试除数寄存器。

执行 \(q\) 次后，到达

$$
2^{qk}5^r7^k13.
$$

再执行

$$
\mathsf U^r\;\frac{17}{91},
$$

到达

$$
\boxed{
2^n3^r7^{k-r-1}17.
}
\tag{7}
$$

此时分支由 \(r\) 决定。

### 若 \(r>0\)

执行

$$
\frac{19}{51},
$$

再通过

$$
\mathsf W^n\;\frac{77}{19}\;
\mathsf V^{r-1}\;\frac{13}{11}
$$

把暂存数据恢复，最终得到

$$
5^n7^{k-1}13=M(n,k-1).
$$

### 若 \(r=0\)

执行

$$
\frac1{17},
$$

得到式（5）。

随后通过

$$
\left(\frac{15}{2}\right)^n,
\quad
\left(\frac17\right)^{k-1},
\quad
55,
\quad
\mathsf V^n,
\quad
\frac{13}{11},
$$

得到

$$
5^{n+1}7^n13=M(n+1,n).
$$

证毕。

这与 Conway 原始流程图中的试除机制一致；这里把中间状态和返回条件逐项展开。([Gwern.net][1])

---

## 素数为什么出现？

从标准候选状态

$$
M(n,n-1)
$$

开始，程序依次试除

$$
n-1,n-2,\ldots,
$$

直到遇到第一个因数，也就是 \(n\) 的最大真因数。

只有当这个因数为 \(1\)，式（5）才变成纯 \(2\) 幂：

$$
2^n7^0=2^n.
$$

因此

$$
\boxed{
n\text{ 是素数}
\iff
\text{这一轮经过纯输出轴 }N=2^n.
}
\tag{8}
$$

这不是假设“素数对应某个神秘共振峰”。在这个程序里，它对应一个明确的边界事件：

$$
\boxed{
\text{首次整除发生在 }k=1.
}
$$

在 \((n,k)\) 平面上，商 \(q\) 的区域为

$$
qk\le n<(q+1)k,
$$

整除点位于边界

$$
n=qk.
$$

所以，程序可以看成在整数格中不断移动，并检测何时碰到整除边界。连续平面只是辅助几何；**整数性和优先级仍然不可删除。**

# 四、5040 的实际轨迹：它会进入候选 \(7\)，但原因可以完全算清

现在直接分析你关注的状态

$$
5040=2^4 3^2 5\,7.
$$

先给一个更一般的结果。

## 定理 3：无控制标记输入的归一化

从

$$
N=2^a3^b5^c7^d
$$

出发，执行

$$
\boxed{
3a+2b+d+2
}
\tag{9}
$$

个微步后，到达

$$
\boxed{
13\cdot5^{a+c+1}7^{a+b}.
}
\tag{10}
$$

### 证明

没有控制标记时，先连续执行 \(a\) 次 \(15/2\)：

$$
2^a3^b5^c7^d
\longmapsto
3^{a+b}5^{a+c}7^d.
$$

再执行 \(d\) 次 \(1/7\)，清空 \(7\) 寄存器。

然后执行 \(55\)，得到

$$
3^{a+b}5^{a+c+1}11.
$$

最后执行

$$
\mathsf V^{a+b}\;\frac{13}{11},
$$

得到式（10）。

总步数为

$$
a+d+1+2(a+b)+1
=
3a+2b+d+2.
$$

证毕。

---

代入

$$
(a,b,c,d)=(4,2,1,1),
$$

得到：

$$
\boxed{
5040\xrightarrow{19\text{ 步}}M(6,6).
}
\tag{11}
$$

因为 \(6\mid6\)，下一轮直接走整除分支：

$$
\boxed{
M(6,6)\xrightarrow{53\text{ 步}}M(7,6).
}
\tag{12}
$$

因此

$$
\boxed{
5040\xrightarrow{72\text{ 步}}M(7,6).
}
\tag{13}
$$

而 \(M(7,6)\) 恰好是标准的“检测候选 \(7\)”状态。继续运行，经过 \(280\) 步得到

$$
2^7=128.
$$

所以：

$$
\boxed{
5040\xrightarrow{352\text{ 步}}128.
}
\tag{14}
$$

我用原始整数分数程序与独立的寄存器程序核对了这些节点：

| 从 \(5040\) 出发的微步数 | 状态                 |
| ----------------: | ------------------ |
|             \(0\) | \(2^4 3^2 5\,7\)   |
|            \(19\) | \(13\cdot5^6 7^6\) |
|            \(47\) | \(2^6 7^5\)        |
|            \(72\) | \(13\cdot5^7 7^6\) |
|           \(352\) | \(2^7\)            |

第 \(47\) 步不是纯 \(2\) 幂，因为仍有 \(7^5\)。

标准初态 \(2\) 的轨迹在第 \(430\) 步也进入 \(M(7,6)\)。所以两条轨迹在这之后具有完全相同的未来，只是时钟相差 \(358\) 步。

## 但这个现象不只属于 5040

归一化投影是

$$
\boxed{
(a,b,c,d)\mapsto(a+c+1,\ a+b).
}
\tag{15}
$$

初始的 \(d\) 完全没有进入宏状态结果。

例如

$$
5040\cdot7^r
$$

都会进入同一个 \(M(6,6)\)，只是多用 \(r\) 个清空微步；随后同样进入候选 \(7\) 的轨迹。

更一般地，给定宏状态参数 \((n,k)\)，它的无控制输入纤维为

$$
\boxed{
a+c=n-1,\qquad a+b=k,\qquad d\ge0.
}
\tag{16}
$$

其中 \(a\) 有有限多个可能值，\(d\) 则任意大。

**这才是一个实际的有损投影：程序确实清除了部分输入信息，并把不同状态合并到同一个未来。**

完整整数编码

$$
2^a3^b5^c7^d
$$

本身没有丢失指数；丢失发生在这段计算之后。

# 五、压缩成二维之后，必须补回一条“返回时间”

如果只保留式（4）的二维映射，就很容易把“一次试除”误当作一个原始微步。

现在精确计时。

## 定理 4：单次试除的返回时间

对 \(1\le k\le n\)，令

$$
q=\left\lfloor\frac nk\right\rfloor.
$$

则从 \(M(n,k)\) 返回下一检查点所需的微步数为

$$
\boxed{
\tau(n,k)=
\begin{cases}
6n+2q+2,&k\nmid n,\\[1mm]
7n+2q+k+3,&k\mid n.
\end{cases}
}
\tag{17}
$$

### 证明

每个式（6）的完整减法循环包含

$$
2k+1+2k+1=4k+2
$$

个微步。共执行 \(q\) 次。

若 \(r=n-qk>0\)，剩余四段的长度分别为

$$
2r+1,\quad1,\quad2n+1,\quad2r-1.
$$

总长度为

$$
q(4k+2)+(2r+1)+1+(2n+1)+(2r-1)
=
6n+2q+2.
$$

若 \(r=0\)，完成减法循环以后，到式（5）需要两步；后续恢复并进入下一个候选，需要

$$
3n+k+1
$$

步。

所以

$$
q(4k+2)+2+(3n+k+1)
=
7n+2q+k+3.
$$

证毕。

---

因此，真正保持运行信息的宏模型是

$$
\boxed{
(n,k)
\longmapsto
\bigl(\mathcal R(n,k),\,\tau(n,k)\bigr),
}
\tag{18}
$$

而不是只有 \(\mathcal R\)。

用嵌入

$$
\iota(n,k)=M(n,k)
$$

表示，精确关系是

$$
\boxed{
F^{\tau(n,k)}(\iota(n,k))
=
\iota(\mathcal R(n,k)).
}
\tag{19}
$$

这与一个固定步长的商动力学不同：

$$
\boxed{
\text{保留事件顺序}
\neq
\text{保留原始时间}.
}
$$

项目的动态闭包保存有限操作后的全部读数；若工程上采用这样的宏步压缩，就需要另外保留返回成本，才能谈时间保持，而不只是最终结果保持。

# 六、进一步算出：原版 PRIMEGAME 的时钟具有三次增长律

这里还能继续，不必停在每次试除的成本。

对 \(n\ge2\)，记：

$$
\ell(n)=n\text{ 的最小素因子},
$$

$$
b_n=\frac n{\ell(n)}
$$

为最大真因数。

从候选起点

$$
M(n,n-1)
$$

运行到

$$
M(n+1,n)
$$

的总成本记为 \(C(n)\)。

## 定理 5：一个候选整数的精确成本

$$
\boxed{
C(n)
=
(6n+2)(n-b_n)
+n+b_n+1
+
2\sum_{k=b_n}^{n-1}
\left\lfloor\frac nk\right\rfloor.
}
\tag{20}
$$

### 证明

对于

$$
k=n-1,\ldots,b_n+1,
$$

全部走非整除分支；最后 \(k=b_n\) 走整除分支。

将式（17）逐项相加、整理即得。证毕。

因为

$$
b_n\le n/2,
$$

而

$$
\sum_{k=1}^{n-1}\left\lfloor\frac nk\right\rfloor
=O(n\log n),
$$

所以

$$
\boxed{
C(n)
=
6n^2\left(1-\frac1{\ell(n)}\right)
+
O(n\log n).
}
\tag{21}
$$

特别地，

$$
C(n)=\Theta(n^2).
$$

这说明它不是只为素数候选付出大量工作；每个整数候选都需要二次量级的微步。

## 定理 6：输出时钟的明确渐近常数

定义

$$
\boxed{
\alpha_{\min}
=
\sum_{p\text{ 素数}}
\frac1{p^2}
\prod_{\substack{q<p\\q\text{ 素数}}}
\left(1-\frac1q\right).
}
\tag{22}
$$

令 \(t_p\) 为标准初态 \(2\) 出发、第一次输出 \(2^p\) 的微步数。沿素数 \(p\to\infty\)，

$$
\boxed{
t_p
\sim
2(1-\alpha_{\min})p^3.
}
\tag{23}
$$

系数的数值约为

$$
\boxed{
2(1-\alpha_{\min})\approx1.3398.
}
$$

### 证明

固定素数 \(p\)。一个整数以 \(p\) 为最小素因子的自然密度为

$$
\frac1p\prod_{q<p}\left(1-\frac1q\right),
$$

因为它必须被 \(p\) 整除，同时不被任何更小素数整除。对有限组素数，这是中国剩余定理的直接计数。

因此，

$$
\lim_{X\to\infty}
\frac1X\sum_{2\le n\le X}\frac1{\ell(n)}
=
\alpha_{\min}.
\tag{24}
$$

这里的无限极限可严格控制：截断到 \(p\le Y\) 后，剩余整数都满足 \(\ell(n)>Y\)，故剩余平均至多为 \(1/Y\)。

分部求和于是给出

$$
\sum_{n\le X}\frac{n^2}{\ell(n)}
=
\frac{\alpha_{\min}}3X^3+o(X^3).
$$

把式（21）对 \(n\) 求和：

$$
\sum_{n\le X}C(n)
=
2(1-\alpha_{\min})X^3+o(X^3).
$$

输出 \(2^p\) 的时刻与完成候选 \(p\) 的时刻，只相差 \(O(p^2)\)，不影响三次主项，得到式（23）。证毕。

---

这也给原来的 \(2,3,5,7\) 一个不同的、可计算的角色。

它们对 \(\alpha_{\min}\) 的前四项贡献为

$$
\boxed{
\frac14+\frac1{18}+\frac1{75}+\frac4{735}
=
\frac{14303}{44100}
\approx0.324331.
}
\tag{25}
$$

这些小素数通过“最小素因子”的统计影响运行时钟。但其余素数仍然贡献，不允许仅凭前四项占比较大就删除无限尾部。

这一次，“四个小素数与时间有关”有了明确公式，而不是靠图形联想。

# 七、时间、能量和编码长度，现在可以彻底分开

定义算术对数能量

$$
E(N)=\log N.
$$

一次微步乘以 \(u/v\)，满足

$$
E(N')-E(N)=\log(u/v).
$$

它不是每步相同，也不要求始终为正。

在素数输出状态

$$
N=2^p
$$

上，

$$
\boxed{
E(N)=p\log2.
}
\tag{26}
$$

但定理 6 给出

$$
t_p\sim c_{\mathrm{clk}}p^3,
\qquad
c_{\mathrm{clk}}=2(1-\alpha_{\min}).
$$

所以沿输出事件，

$$
\boxed{
E(2^p)
\sim
(\log2)
\left(\frac{t_p}{c_{\mathrm{clk}}}\right)^{1/3}.
}
\tag{27}
$$

因此在这个明确模型中，

$$
\boxed{
\text{对数能量、微步时间、输出序号，是三个不同读出。}
}
$$

式（27）是该程序和所选权重的结果，不是物理能量与时间的普遍规律。

还有第四个量：**表示所需的长度。**

候选整数为 \(n\) 时，四个数据寄存器在上述试除流程中都不超过 \(n+1\)。因此：

* 直接存储整数 \(N\)，其二进制长度可达 \(O(n)\)；
* 保存四个指数，所需位数为 \(O(\log n)\)；
* 保存四行 Zeckendorf 编码，长度同样为 \(O(\log n)\)。

这再次说明：

$$
\boxed{
\text{整数数值很大}
\quad\not\Rightarrow\quad
\text{状态包含同样多的独立信息}.
}
$$

项目的 `primeAxisEncoding` 已证明规范数码表与正整数的双射，以及乘法对应规范表加法。当前源码采用了 `noncomputable` 数学定义；可执行编译器及其具体成本仍需另外实现和证明。

# 八、金字塔在这里的新定位：它是局部数据单元，不是整个运行宇宙

上一轮已经证明，三位 Zeckendorf 合法字串的凸包是四棱锥：

$$
000,\quad100,\quad010,\quad001,\quad101.
$$

它编码指数 \(0,1,2,3,4\)。

现在从实际执行看：

$$
5040
\longrightarrow
M(6,6)
\longrightarrow
M(7,6)
\longrightarrow\cdots
$$

寄存器很快超过 \(4\)。于是三位窗口不再够用，必须进入更长的合法字串空间。

因此应当构造一个相容的增长族：

$$
\boxed{
\mathcal W_1\hookrightarrow
\mathcal W_2\hookrightarrow
\mathcal W_3\hookrightarrow\cdots,
}
\tag{28}
$$

并要求执行和这些编码嵌入相容。

这座金字塔依然是真实存在的数学结构，但它的角色是：

$$
\boxed{
\text{一个有限精度、有限寄存器范围的合法编码单元。}
}
$$

而完整的几何程序还需要：

$$
\boxed{
\text{增长的编码单元}
+
\text{控制状态}
+
\text{合法跳转}
+
\text{返回时间}
+
\text{输出协议}.
}
\tag{29}
$$

这也修正了“增加一个高度就补齐整体”的直觉：

* 某些缺项可以由一个额外控制值补齐；
* 某些缺项是随规模增长的寄存器容量；
* 某些缺项是被宏步压缩掉的运行时间；
* 某些信息确实已经在归一化阶段被丢弃。

它们不能都用同一条几何高度表示。

# 九、结合项目：现在应当形式化的是“带时钟的语义保持”

当前最有价值的项目接口，可以写成

$$
\boxed{
(\mathbf a,s)
\xrightarrow{\text{素数编码}}
N
\xrightarrow{F}
N'
\xrightarrow{\text{解码}}
(\mathbf a',s').
}
$$

再增加检查点嵌入

$$
\iota(n,k)=13\cdot5^n7^k,
$$

以及已经推导的

$$
\mathcal R(n,k),\qquad \tau(n,k).
$$

需要形式化的核心等号不是简单的

$$
\pi F=G\pi,
$$

因为上一轮已经证明四数据投影一般不满足它；正确的宏步关系是

$$
\boxed{
F^{\tau(n,k)}(\iota(n,k))
=
\iota(\mathcal R(n,k)).
}
\tag{30}
$$

同时还应记录这段轨迹是否经过纯 \(2\) 幂：

$$
\boxed{
\text{本次试除产生纯输出}
\iff
k=1,
}
$$

其中从标准候选状态 \(M(n,n-1)\) 开始，第一次整除到达 \(k=1\) 才等价于 \(n\) 为素数。

这与项目的动态闭包方向一致：**判断一个投影是否够用，要看它是否保留目标相关的未来，而不是只看当前是否可逆编码。**

## 本轮做了哪些有限核对？

除上述纸面证明外，我运行了：

* \(1792\) 个状态的一步整数执行与寄存器执行一致性检查；
* \(1275\) 组 \(1\le k\le n\le50\) 的返回状态与精确步数检查；
* \(256\) 个无控制初态的归一化检查；
* 从标准初态 \(2\) 出发，直接用整数乘除核对至素数 \(29\) 的输出时刻；
* 从 \(5040\) 出发，核对第 \(19、47、72、352\) 步。

这些有限检查用于发现公式、优先级和计步错误，不能代替一般性证明，也不是 Lean 的通过记录。

核验可以直接复现：[精确整数核验脚本](sandbox:/mnt/data/fractran_geometric_verifier.py)；对应结果见[核验记录](sandbox:/mnt/data/fractran_geometric_verification.json)。

# 结论：这次真正补上的，是几何语言的“时钟与返回面”

现在，对你的整体直觉可以给出更完整的数学表达：

$$
\boxed{
\begin{aligned}
\text{素数指数格}
&:\text{状态坐标};\\
\text{Zeckendorf 多面体}
&:\text{合法编码单元};\\
\text{七种控制状态}
&:\text{当前执行分支};\\
\text{二维检查点}
&:\text{宏观观察截面};\\
\text{返回映射 }\mathcal R
&:\text{一次完整试除的结果};\\
\text{返回时间 }\tau
&:\text{被几何压缩隐藏的微观成本}.
\end{aligned}
}
$$

本轮最实质的三个结论是：

$$
\boxed{
5040\text{ 在 }72\text{ 步后进入候选 }7\text{ 的标准轨迹};
}
$$

$$
\boxed{
\text{微观四数据＋七控制层，能在正确截面上压缩为二维返回映射};
}
$$

$$
\boxed{
\text{原版程序的素数输出时钟满足 }
t_p\sim1.3398\,p^3.
}
$$

因此，**“5040 是一个投影”需要继续细分：它是自身指数状态的精确编码；它也是更丰富程序运行的一个状态读出；经过实际归一化流程后，不同整数又会被合并成同一个宏观状态。**

这条路线已经能解释几何怎样成为程序、投影何时失去控制信息、时间怎样从被压缩的循环中恢复。它还没有把 PRIMEGAME 转化为新的素数分布估计或 RH 证明。

真正需要继续推进的，是：**在保留输出正确性的同时，哪些宏观观察还能保留误差、成本和相关结构的统一界。**只有这类带定量保证的语义保持，才能把“能够生成素数的几何语言”进一步接到项目关心的“能够证明素数规律的观察体系”。

[1]: https://gwern.net/doc/cs/computable/1987-conway.pdf "https://gwern.net/doc/cs/computable/1987-conway.pdf"
[2]: https://arxiv.org/html/2412.16185v1 "https://arxiv.org/html/2412.16185v1"
Auric，可以沿着这个方向继续，但这次最重要的是把两件事分开：

**“平坦可能是一种有效近似”是合理的研究方向；“所以一切本来都不平坦，而且拓扑、逻辑、因果完全是同一个东西”，还不能由此推出。**

而对 5040，我们现在能得到一个比“它似乎很特殊”更强的结论：

> **在项目已经固定的资源优化目标下，5040 是一个稳定的四素数配置。资源价格继续下降时，下一步最优改变不是继续加深原有四个寄存器，而是激活第五个素数方向 \(11\)，变成 \(55440\)。**

更有意思的是：

> **同一个目标若允许“分数个占据量”，最优解会使用九个素数方向；要求占据量必须是整数，才会留下 \(2,3,5,7\) 四个方向和 \((4,2,1,1)\)。**

这就是一项可以证明的**离散临界意义**：不是神秘数字的临界，而是“最小不可分资源单位”改变了最优结构。

下面把平坦、投影、因果、黄金编码、优化和 RH 的界限连接起来。

---

# 一、“看起来平坦”至少有三种完全不同的原因

## 1. 真正平坦

数学上，完全平坦的结构确实存在。

例如：

$$
ds^2=dx^2+dy^2
$$

定义了严格平坦的平面。把它按整数平移取商：

$$
\mathbb R^2/\mathbb Z^2
$$

还得到一个紧致、无边界、严格平坦的二维环面。

所以：

$$
\boxed{
\text{平坦}\neq\text{无限延伸},
\qquad
\text{平坦}\neq\text{拓扑简单}.
}
$$

“无穷”也不是自动放在平面边缘的某一个点。欧氏平面没有流形边界，但它不紧致；这两种性质可以严格区分。

## 2. 局部近似平坦

在一般光滑时空中，可以在一个点附近选择正规坐标，使：

$$
g_{\mu\nu}(x)
=
\eta_{\mu\nu}
-\frac13R_{\mu\alpha\nu\beta}(0)x^\alpha x^\beta
+O(|x|^3),
$$

其中曲率项从二阶出现，具体符号依曲率约定而定。这是正规坐标展开的标准结果。([arXiv][1])

因此，在尺度 \(L\) 上：

$$
\boxed{
\text{偏离平坦的量级}\sim \|R\|L^2.
}
$$

当它小于观察精度，平坦模型就可能足够准确。

这里不一定涉及统计平均；**有限分辨率和局部展开，本身就能产生平坦近似。**

## 3. 观察协议遗漏了关系

另一种情况更接近你的直觉：底层关系没有变，但观察者只保留了某些边缘统计。

例如，取两个二元变量 \(X,Y\in\{-1,+1\}\)：

$$
p_\theta(x,y)=\frac{1+\theta xy}{4},
\qquad |\theta|<1.
$$

对任何 \(\theta\)：

$$
\Pr(X=1)=\Pr(Y=1)=\frac12.
$$

所以，分别观察 \(X\) 和 \(Y\)，得到的统计完全不变。

但：

$$
\mathbb E[XY]=\theta.
$$

变化藏在联合关系中。

若使用 Fisher 信息衡量对 \(\theta\) 的可分辨性，完整联合观察给出：

$$
I_{X,Y}(\theta)=\frac1{1-\theta^2},
$$

单独观察任意一个边缘，却给出：

$$
I_X(\theta)=I_Y(\theta)=0.
$$

这不是底层变平坦，而是**指定观察对那项变化失明了**。

一般地，在正则条件下，统计量 \(Y=\pi(X)\) 的信息损失满足：

$$
\boxed{
I_X-I_Y
=
\mathbb E\!\left[
\operatorname{Var}\!\left(
\partial_\theta\log p_\theta(X)\mid Y
\right)
\right]\ge0.
}
\tag{1}
$$

这来自条件期望与方差分解，也是统计信息在粗粒化下减少的标准机制。([arXiv][2])

因此，更准确的命题应当是：

> **我们观察到的“简单、稳定、近似平坦”，可能来自真正的几何平坦，也可能来自局部近似，还可能来自未被读取的关联。必须用不同实验或不同数学读出区分它们。**

不能先把三者统称为“投影造成的曲率”。

---

# 二、拓扑、曲率与因果相连，但不能直接画等号

这是整个理论需要保持的一条边界。

## 同一种拓扑，可以具有不同曲率

在同一个平面 \(\mathbb R^2\) 上，比较：

$$
g_0=dx^2+dy^2,
$$

与：

$$
g_1=e^{2(x^2+y^2)}(dx^2+dy^2).
$$

它们具有完全相同的拓扑。

但 \(g_0\) 的曲率为零，而二维共形度量公式给出：

$$
K_{g_1}
=
-e^{-2(x^2+y^2)}
\Delta(x^2+y^2)
=
-4e^{-2(x^2+y^2)}.
$$

所以：

$$
\boxed{
\text{拓扑相同，曲率可以不同}.
}
$$

拓扑控制连续性、连通性、洞与粘合；曲率还需要度量或联络。

## 因果结构可以决定很多几何，但通常还差一个尺度

在适当的时空因果性条件下，因果顺序能够确定共形几何。这是 Malament、Hawking–King–McCarthy 一类结果的重要内容。([arXiv][3])

但：

$$
\widetilde g=\Omega(x)^2g,
\qquad \Omega(x)>0,
$$

保持同样的光锥和因果类型，却通常改变长度、体积与曲率。

因此：

$$
\boxed{
\text{因果顺序}
\ \text{通常确定共形结构，而非直接确定全部度量}.
}
$$

补上适当的体积信息，才有希望恢复剩下的尺度。这也是因果集研究强调“顺序＋计数”的原因；但“时空在最底层就是离散因果集”仍然是一种物理研究方案，不是已经由项目证明的事实。([数字对象标识符][4])

所以，你的方向可以收紧为：

$$
\boxed{
\text{离散事件关系}
+
\text{计数或尺度}
+
\text{演化规律}
\longrightarrow
\text{可能出现的有效时空几何}.
}
\tag{2}
$$

这里每个加号都承担实际内容，不能把后两项藏进“因果逻辑”四个字里。

还有一个与 FRACTRAN 直接相关的提醒：**程序状态图可以有循环，但因果事件不能因为状态重复就变成同一个事件。** 应当把一次次执行展开成历史事件，再讨论其先后关系。内存回到原值，不等于时间倒流。

---

# 三、\((4,2,1,1)\) 到底受什么约束？先分成三层

这四个数首先不是“坐标系”，而是一个坐标点：

$$
5040=2^4\,3^2\,5\,7.
$$

真正的素数指数空间是：

$$
\mathbb N^{(\mathbb P)},
$$

即只有有限多个非零分量的素数指数表。

## 第一层：表示约束

每个指数必须满足：

$$
a_p\in\mathbb N,
$$

并且：

$$
\#\{p:a_p\ne0\}<\infty.
$$

**一般正整数的不同素数指数之间，没有“禁止相邻两个指数同时非零”的规则。**

例如：

$$
(4,2,1,1),\quad(1,4,0,7),\quad(0,0,3,2)
$$

都可以是合法指数配置。

## 第二层：Zeckendorf 规范约束

每个指数再表示为：

$$
a_p=\sum_jG_jb_{p,j},
\qquad
G_0=1,\ G_1=2,\ G_{j+2}=G_{j+1}+G_j,
$$

并要求：

$$
b_{p,j}\in\{0,1\},
\qquad
b_{p,j}b_{p,j+1}=0.
$$

这里的“禁止 \(11\)”首先保证规范表示不重复。因为：

$$
G_j+G_{j+1}=G_{j+2},
$$

相邻两个占据可以被重新规范化到更高权重。

项目的黄金理论和 `PrimeAxisEncoding` 明确把这层关系建立成双射：**合法黄金表与普通正整数保存的是同一份离散信息。**

它并不自动意味着最省比特。

长度 \(L\) 的任意二进制字串有 \(2^L\) 个，而禁邻字串只有约 \(\varphi^L\) 个。因此，仅按固定长度二元存储的容量比较，黄金表示所需位数渐近约为普通二进制的：

$$
\frac{\log2}{\log\varphi}\approx1.4404
$$

倍。

这不否定黄金编码在规范化、递推或特定硬件约束下的价值。它说明：

$$
\boxed{
\text{唯一规范表示}
\neq
\text{对所有成本函数都最优}.
}
$$

## 第三层：最优配置约束

只有当我们指定一个收益和成本以后，才会出现：

$$
a_2=4,\quad a_3=2,\quad a_5=a_7=1,
$$

以及：

$$
a_p=0\quad(p\ge11)
$$

这组相互协调的条件。

**它们不是语法禁令，而是优化结果。**

这就是下一步的核心。

---

# 四、5040 的优化意义已经有项目中的明确 Lean 定理

本轮读取的快照 `cdf5cd4f…` 中，`GoldenResourceOptimalInteger.lean` 已经给出：

$$
\boxed{
5040
=
\underset{n\ge1}{\operatorname{argmax}}
\left[
\log\!\left(\sum_{d\mid n}\frac1d\right)
-\frac1{25}\log n
\right],
}
\tag{3}
$$

并证明最大值唯一。它的前件不是“假设 RH”，而只是 \(n\ge1\)。

定义：

$$
E(n)=\log n,
$$

$$
W(n)=\log\frac{\sigma(n)}n,
$$

$$
\boxed{
J_\lambda(n)=W(n)-\lambda E(n).
}
\tag{4}
$$

\(E(n)\) 是对数规模，与整数编码长度相关；\(W(n)\) 是因数权重收益。若另赋物理能量单位 \(E_*\)，可以写成 \(E_*\log n\)，但这个单位并不是由算术自动确定的。

最大化 \(J_\lambda\)，等价于最大化：

$$
\frac{\sigma(n)}{n^{1+\lambda}}.
$$

这属于经典极大丰富数的优化结构，而不是仅为 5040 临时制造的目标。([arXiv][5])

## 为什么最优指数能够逐素数计算？

设：

$$
n=\prod_pp^{a_p}.
$$

则：

$$
J_\lambda(n)
=
\sum_p
\left[
\log\left(\sum_{j=0}^{a_p}p^{-j}\right)
-\lambda a_p\log p
\right].
$$

定义增加第 \(j\) 层的单位成本收益：

$$
\boxed{
r_p(j)
=
\frac1{\log p}
\log\frac{1-p^{-(j+1)}}{1-p^{-j}},
\qquad j\ge1.
}
\tag{5}
$$

它随 \(j\) 严格下降。项目已经形式化了这一单调性。

因此，指数 \(a_p\) 最优的条件是：

$$
\boxed{
r_p(a_p)\ge\lambda\ge r_p(a_p+1).
}
\tag{6}
$$

第一项表示最后一层仍然值得保留，第二项表示再增加一层已经不值得。

对 \((4,2,1,1)\)，关键门槛为：

| 素数方向        |              保留最后一层的收益率 |         增加下一层的收益率 |
| ----------- | ----------------------: | ----------------: |
| \(2\)，保留到 4 |       \(0.04730571478\) | \(0.02308361311\) |
| \(3\)，保留到 2 |       \(0.07285801233\) | \(0.02304526196\) |
| \(5\)，保留到 1 |       \(0.11328275256\) | \(0.02037346242\) |
| \(7\)，保留到 1 |       \(0.06862156132\) | \(0.00909578333\) |
| 新方向 \(11\)  | 首层收益率 \(0.03628656263\) |                 — |

所以，5040 的整个稳定价格区间是：

$$
\boxed{
\frac{\log(12/11)}{\log11}
<
\lambda
<
\frac{\log(31/30)}{\log2}.
}
\tag{7}
$$

约为：

$$
0.03628656<\lambda<0.04730571.
$$

区间内部，最优配置唯一等于：

$$
(4,2,1,1,0,0,\ldots).
$$

**这才是四个坐标之间真正的约束：它们必须同时服从同一个边际资源价格。**

共同价格可以协调四个方向，但它不是第五个素数，也不是更高维的全知观察者。

---

# 五、离散性的核心：连续松弛会启用九个素数方向，整数模型却只启用四个

现在直接检验你的“会不会只是统计近似”直觉。

暂时允许：

$$
a_p\in[0,\infty)
$$

取任意实数，而不是整数。

这只是优化松弛，不再表示普通整数的素因数分解。

对单个素数，目标为：

$$
f_{p,\lambda}(a)
=
\log\frac{1-p^{-(a+1)}}{1-p^{-1}}
-\lambda a\log p.
$$

求导：

$$
f_{p,\lambda}'(a)
=
\log p
\left[
\frac1{p^{a+1}-1}-\lambda
\right].
$$

因此，连续最优解为：

$$
\boxed{
a_p^{\mathrm{cont}}
=
\max\left(
0,\frac{\log(1+1/\lambda)}{\log p}-1
\right).
}
\tag{8}
$$

取项目已证明的价格：

$$
\lambda=\frac1{25},
$$

得到：

$$
a_p^{\mathrm{cont}}>0
\iff
p<26.
$$

于是连续模型启用：

$$
\boxed{
2,3,5,7,11,13,17,19,23
}
$$

九个素数方向。

前几个连续最优指数是：

$$
\begin{aligned}
a_2^{\mathrm{cont}}&\approx3.70044,\\
a_3^{\mathrm{cont}}&\approx1.96565,\\
a_5^{\mathrm{cont}}&\approx1.02437,\\
a_7^{\mathrm{cont}}&\approx0.67433,\\
a_{11}^{\mathrm{cont}}&\approx0.35873.
\end{aligned}
$$

但真正的整数最优解是：

$$
\boxed{
(4,2,1,1,0,0,0,0,0).
}
\tag{9}
$$

为什么？

因为连续模型可以给 \(11\) 方向分配 \(0.35873\) 份占据量；整数模型要么完全不启用，要么至少支付一整份：

$$
\log11
$$

的规模成本。

而在 \(\lambda=1/25\) 时：

$$
\log(12/11)-\frac1{25}\log11<0.
$$

所以，**完整第一层的收益不足以支付完整第一层的成本**。

这就是一项非常具体的离散临界：

$$
\boxed{
\text{无穷小增量有利}
\quad\not\Rightarrow\quad
\text{最小合法整数增量有利}.
}
\tag{10}
$$

它不是简单的“把连续答案四舍五入”。

离散性可以改变**哪些方向存在于最优配置中**，而不只是稍微改变每个方向的数值。

但这仍是所选优化问题的结论。不能仅凭它宣布自然界的一切都以同一个资源函数优化。

---

# 六、5040 更准确的临界意义：它是最后一个稳定的四轴阶段

现在沿着资源价格下降的方向观察。

## 上边界：从 2520 加深到 5040

当价格下降到：

$$
\lambda_+
=
\frac{\log(31/30)}{\log2},
$$

在 \(2\) 方向增加第四层开始值得：

$$
2520\longrightarrow5040.
$$

指数变化为：

$$
(3,2,1,1)\longrightarrow(4,2,1,1).
$$

它是**已有方向的纵向加深**。

## 下边界：从 5040 扩展到 55440

继续降低价格，第一个新出现的更优选项是：

$$
\lambda_-
=
\frac{\log(12/11)}{\log11}.
$$

跨过它：

$$
\boxed{
5040\longrightarrow5040\cdot11=55440.
}
\tag{11}
$$

指数变化为：

$$
\boxed{
(4,2,1,1)
\longrightarrow
(4,2,1,1,1).
}
$$

它是**新增一个素数方向**。

而在同一时刻，继续增加 \(2\) 或 \(3\) 的指数仍然不划算，因为它们的下一层收益率只有约 \(0.02308\)、\(0.02305\)，低于 \(0.03629\)。

因此：

> **在这条实际优化路径上，5040 是“四个活跃素数方向”的最后一个稳定配置；要继续最优扩张，首先需要横向引入 \(11\)，而不是继续挤压旧四轴。**

这个“维数增加”是活跃寄存器数量增加，不是物理空间突然从四维变成五维。

---

## 平坦与临界，还可以在优化包络里精确看见

定义最优值：

$$
\mathcal F(\lambda)
=
\sup_{n\ge1}
\left[W(n)-\lambda E(n)\right].
$$

它是直线族的上包络，因此是凸函数。在任何远离 \(\lambda=0\) 的紧价格区间，只有有限种最优配置参与。

在 5040 稳定区间内：

$$
\boxed{
\mathcal F(\lambda)
=
W(5040)-\lambda\log5040.
}
\tag{12}
$$

它严格是一条直线：

$$
\mathcal F''=0.
$$

但在两端，斜率发生跳变。相应二阶分布中，这两个临界点的原子权重分别为：

$$
\boxed{
\log2,\qquad\log11.
}
\tag{13}
$$

因为最优规模分别跳了一个 \(2\) 倍和一个 \(11\) 倍。

这里的“二阶响应”不是黎曼曲率，而是资源最优值对价格的响应。

**这带来一个与你原直觉互补的事实：离散系统也可以产生严格平坦的平台；统计平滑反而可以把尖锐跳变变成弯曲过渡。**

例如，在有限候选集上定义：

$$
\mathcal F_\tau(\lambda)
=
\tau\log\sum_n
\exp\left(\frac{W(n)-\lambda E(n)}{\tau}\right).
$$

则：

$$
\boxed{
\mathcal F_\tau''(\lambda)
=
\frac1\tau\operatorname{Var}_{\tau,\lambda}(E)\ge0.
}
\tag{14}
$$

\(\tau>0\) 时平滑，\(\tau\to0\) 时恢复分段线性最优包络。

所以不能笼统地说：

$$
\text{统计一定把曲变平}.
$$

方向取决于我们究竟在对什么对象、用什么操作取近似。

---

# 七、金字塔与黄金满窗：5040 的第二项临界，是规范窗口恰好闭合

\((4,2,1,1)\) 的每个指数上限加一为：

$$
(5,3,2,2).
$$

它们恰好是：

$$
G_3,G_2,G_1,G_1.
$$

所以：

$$
\boxed{
\operatorname{Div}(5040)
\cong
\mathcal W_3\times\mathcal W_2\times
\mathcal W_1\times\mathcal W_1.
}
\tag{15}
$$

这使 5040 同时成为一个完整黄金窗口配置。

其中三位合法态：

$$
000,\quad100,\quad010,\quad001,\quad101
$$

的凸包确实是四棱锥：

$$
x,y,z\ge0,\qquad x+y\le1,\quad y+z\le1.
$$

但要注意：**这个金字塔来自素数 \(2\) 的三位指数编码块，不是由四个素数分别充当四个底面顶点。**

更重要的是：黄金满窗与资源最优性是两条不同条件。

前者要求：

$$
a_p+1=G_{L_p};
$$

后者要求：

$$
r_p(a_p)\ge\lambda\ge r_p(a_p+1).
$$

5040 同时满足它们，是一个可精确分析的交会点。

但存在许多黄金满窗整数，并非都为相同价格下的最优解；也存在最优整数，其指数上限不都对应完整 Fibonacci 窗口。

因此：

$$
\boxed{
\text{表示闭合}
\neq
\text{资源最优}
\neq
\text{全局解析正性}.
}
$$

我们应当研究它们什么时候相交，而不是先假设它们必然等价。

---

# 八、5040 与 RH 的第三项联系：四个素数方向在它之后已经可以完整排除反例

Robin 定理说：

$$
\boxed{
\mathrm{RH}
\iff
\frac{\sigma(n)}n
<
e^{\gamma_{\mathrm E}}\log\log n
\quad\forall n>5040.
}
\tag{16}
$$

注意严格条件是 \(n>5040\)。5040 本身不满足这项不等式，并不能因此否证 RH。([Springer][6])

这次还可以对当前四轴模型作一个完整限制。

## 定理：只使用 \(2,3,5,7\)，在 5040 之后不会产生 Robin 反例

$$
\boxed{
n=2^a3^b5^c7^d>5040
\Longrightarrow
\frac{\sigma(n)}n
<
e^{\gamma_{\mathrm E}}\log\log n.
}
\tag{17}
$$

这里允许四个指数任意大，不局限于 \((4,2,1,1)\) 的因数窗口。

### 无限部分的证明

对这种整数：

$$
\frac{\sigma(n)}n
=
\prod_{p\in\{2,3,5,7\}}
\frac{1-p^{-(a_p+1)}}{1-p^{-1}}
<
\prod_{p\in\{2,3,5,7\}}\frac p{p-1}
=
\frac{35}{8}.
$$

另一方面，可以严格认证：

$$
e^{\gamma_{\mathrm E}}>1.78,
$$

以及：

$$
1.78\log\log120000
>
4.3773448888
>
\frac{35}{8}.
$$

因此全部 \(n\ge120000\) 都满足所需不等式。

### 剩余有限部分

在：

$$
5040<n\le120000
$$

之间，恰有 464 个只含这四种素因子的整数。

本轮用有理数区间运算逐一认证：

$$
\boxed{
1.78\log\log n-\frac{\sigma(n)}n>0.053.
}
\tag{18}
$$

最小认证下界出现在 \(n=10080\)，约为：

$$
0.05372098638235.
$$

这里的符号比较没有依赖浮点数。对数界来自：

$$
\log x
=
2\sum_{j=0}^{K-1}
\frac{z^{2j+1}}{2j+1}+R_K,
\qquad
z=\frac{x-1}{x+1},
$$

在将 \(x\) 缩放到 \([1,2]\) 后，使用：

$$
0\le R_K
\le
\frac{2z^{2K+1}}{(2K+1)(1-z^2)}.
$$

欧拉常数的下界则由：

$$
\gamma_{\mathrm E}>H_{1000}-\log1001
$$

和指数函数的正 Taylor 下界认证。

[本轮精确有理数检验脚本](sandbox:/mnt/data/verify_5040_four_prime_sector.py)

因此我们得到：

$$
\boxed{
\text{任何 }n>5040\text{ 的 Robin 反例，
都必须涉及某个至少为 }11\text{ 的素数}.
}
\tag{19}
$$

这是一个有限范围认证加统一尾界的严格结果，不是新的 RH 证明，也不声称这个小素数范围结论在文献中首次出现。

但它对当前研究方向很重要：

> **若始终只在 \(2,3,5,7\) 四个素数方向内部寻找 5040 之后的 Robin 障碍，整个区域已经可以排除。真正的全局问题必须面对新素数轴的持续加入。**

这与“最优扩张首先激活 \(11\)”相呼应，但二者是不同定理，不能互相替代。

---

# 九、无穷与对角化真正提示的，不是“必然有曲率”，而是“局部保证未必有统一预算”

这里可以重新理解你最开始的问题。

每个整数的素因数表都有限；但不存在一个固定的有限素数集合，能够表示所有整数。

每个有限计算都可能有完整记录；但不存在理由保证一个固定长度的摘要，可以预测所有无限计算的全部行为。

这些是**量词和资源范围的变化**：

$$
\forall n\ \exists\text{有限表示}
$$

并不等于：

$$
\exists\text{固定有限表示空间}\ \forall n.
$$

对角化可以证明某类统一编码或统一预测不存在。它不会单独给出一个曲率张量。

要把逻辑缺口变成几何，需要具体构造：

$$
\boxed{
\text{状态与关系}
\longrightarrow
\text{观察映射}
\longrightarrow
\text{度量或核}
\longrightarrow
\text{可计算的不相容量}.
}
\tag{20}
$$

前文的 Schur 余量、闭环相位、Fisher 信息损失，都是这样的具体量；它们不能因为都描述“缺失”就被当成同一个曲率。

## 对程序而言，完整观察必须保持下一步关系

若状态更新为 \(T\)，观察为 \(\pi\)，要让观察结果本身形成闭合动力学，必须存在 \(\overline T\)，满足：

$$
\boxed{
\pi T=\overline T\pi.
}
\tag{21}
$$

等价地：

$$
\pi(x)=\pi(y)
\Longrightarrow
\pi(Tx)=\pi(Ty).
$$

PRIMEGAME 中只看四个数据寄存器而忽略控制标记，正会违反这个条件。

因此，“世界看起来有额外随机性或记忆”可以来自控制上下文被投影掉；但是否如此，必须拿实际转移来检验。

## 对几何而言，没有一张全局坐标图，不等于没有整体

可以保留局部坐标图及其重叠变换，而不要求一个永远居于顶层的坐标系。

项目的 `GlobalFrameCoboundaryCriterion.lean` 已把一种具体的标架拼接条件写成严格代数等价：相容的单位标架存在，当且仅当指定转移数据具有相应的余边界表示。它并没有由此证明所有实际转移都满足条件，也没有把该群论等价当成时空曲率定理。

**真正的整体可以是一套相容的局部关系，而不必是一张上帝视角的总地图。**

---

# 十、一个适合项目继续发展的总体框架

现在可以把你的方向整理成一个明确的研究程序。

先固定底层对象：

$$
\boxed{
\text{离散状态}
+
\text{事件转移}
+
\text{控制上下文}
+
\text{权重或代价}
+
\text{观察族}.
}
$$

然后分别研究四项问题。

**哪些关系是精确的？**
例如素因数分解、黄金规范化、FRACTRAN 执行交换图、整数资源阈值。

**哪些几何来自观察或统计族的选择？**
例如四棱锥凸包、最大熵补全、Fisher 度量、条件干涉核。它们可以非常有用，但不能省略定义它们的模型选择。

**哪些临界是离散可认证的？**
例如一条指令从不可执行变为可执行；一个指数层的净收益从负变正；活跃素数数目从四变五；一个 Gram 拼接余量越过零。

**哪些结论仍然需要真实算术或物理证据？**
例如全部大整数的 Robin 上界、实际 ξ 的全阶正核，以及这些数学结构是否描述真实时空。

这样，“最经济”不再是一句预设结论，而成为可以比较的目标函数。

例如，若把收益改成因数个数：

$$
\log\tau(n)-\lambda\log n,
$$

那么在 \(\lambda=1/25\) 时，给 5040 的 \(2\) 指数再加一，收益率是：

$$
\frac{\log(6/5)}{\log2}\approx0.263,
$$

远高于 \(0.04\)。

所以 5040 就不再是这个新目标的最优点。

这证明：

$$
\boxed{
\text{最经济必须相对于指定任务，
不存在脱离任务的普遍最优整数}.
}
\tag{22}
$$

同样，“最有效的时空结构”也必须说明：优化什么、在什么约束下优化、用什么可观测结果检验。

---

## 最后的收束

你提出的方向中，最有力量的部分不是“一切都不平坦”，而是：

> **我们看到的几何，可能同时包含真实结构、有限尺度近似、观察投影和优化后的有效描述。要理解整体，必须保留这些描述之间的转移规则和误差预算。**

5040 在这套框架里有三项清楚的意义：

$$
\boxed{
\text{黄金满窗：}
\quad
(4,2,1,1)+1=(5,3,2,2);
}
$$

$$
\boxed{
\text{资源最优：}
\quad
\lambda\in
\left(
\frac{\log(12/11)}{\log11},
\frac{\log(31/30)}{\log2}
\right)
\text{ 时唯一最优};
}
$$

$$
\boxed{
\text{扩张边界：}
\quad
5040\to55440
\text{ 首先新增素数 }11.
}
$$

更关键的是，连续松弛会使用九个素数方向，而整数模型只使用四个：

$$
\boxed{
\text{离散最小单位，改变了最优结构的活跃维数。}
}
$$

这比“5040 是宇宙临界数”更有证明力量，也更可检验。

同时，本轮已经把整个四素数区域的 Robin 反例排除：**5040 之后的真正困难不在固定四轴内部，而在无限增加的新素数方向及其全局相互约束。**

因此，我会把后续的核心问题表述为：

> **当新的离散方向不断被激活时，旧的局部最优、局部相位一致和局部正性，能否以一个统一预算持续拼成整体？**

这才是“离散—几何—观察—最优化”真正汇合的位置。它允许平坦近似出现，也允许严格平坦区域存在；允许局部曲率，却不把所有逻辑困难都叫作曲率。当前已取得的是具体的优化阈值、连续与离散的差异，以及四素数范围的严格认证；尚未因此证明 RH，也没有把“时空本质上就是因果逻辑”提升为已经成立的物理定律。

[1]: https://arxiv.org/abs/hep-th/0001078 "https://arxiv.org/abs/hep-th/0001078"
[2]: https://arxiv.org/abs/1107.3797 "https://arxiv.org/abs/1107.3797"
[3]: https://arxiv.org/abs/1102.0936 "https://arxiv.org/abs/1102.0936"
[4]: https://doi.org/10.1007/s41114-019-0023-1 "https://doi.org/10.1007/s41114-019-0023-1"
[5]: https://arxiv.org/abs/1211.2147 "https://arxiv.org/abs/1211.2147"
[6]: https://link.springer.com/article/10.1007/s11139-022-00683-0 "https://link.springer.com/article/10.1007/s11139-022-00683-0"
可以继续，而且这次能找到两种**新的、可以精确计算的“观察角度”**：

**一种把 5040 的资源优化扩展成带温度的算术配分函数。它在零温极限中恢复 5040 的最优配置，在特定温度切片上又精确等于真实 ζ 函数的乘积。**

**另一种直接作用于实际 ξ：移动实轴上的展开中心，从高阶累积量中读取“最近零点的距离”。这个距离经过一个简单变换，会成为分段线性的几何对象；每一段的斜率，直接编码某个零点偏离临界线的距离。**

这就不只是“换个比喻”。我们将得到：

$$
\boxed{
\text{光滑解析函数}
\longrightarrow
\text{高阶响应}
\longrightarrow
\text{分段线性边界}
\longrightarrow
\text{可识别的离散切换}.
}
$$

但首先要准确区分：**5040 暴露的临界，发生在最优配置随参数改变的过程中，不是 ζ 在“5040 这个位置”失去光滑性。** ζ 除 \(s=1\) 的极点外是解析的，completed ξ 则是整函数；零点本身也不破坏整函数的光滑性。变得奇异的可以是对数、倒数、相位，或者取最大值以后得到的响应。([DLMF][1])

下面沿两条新路线推进，再把它们接回量子几何。

---

# 一、把“约束就是边界”改写成可检验的形式

一个约束：

$$
f(x)\ge0
$$

只有在：

$$
f(x)=0
$$

且这项约束确实限制了可行方向时，才形成相关的活动边界。某些约束可能冗余，或者在整个模型中都保留严格正余量。

因此，对每一种新观察，我们都应记录：

$$
\boxed{
\text{实际对象}
+
\text{控制参数}
+
\text{约束余量}
+
\text{触边后改变的结构}.
}
$$

例如，5040 的约束余量是：

$$
r_p(a)-\lambda,
$$

触边后改变的是最优素数指数；量子正交的余量是某个态重叠，触边后改变的是可区分性；解析零点对应相位绕数的变化。

**这些都可以提供临界信息，但它们不自动属于同一种“相变”。**

真正有价值的是：能否找到保持实际对象的恒等式，把这些边界连接起来。

---

# 二、从 5040 出发，构造一份真正能接回 ζ 的温度扩展

沿用项目已经固定的目标：

$$
J_\lambda(n)
=
\log\frac{\sigma(n)}n-\lambda\log n.
$$

本轮核对的 `GoldenResourceOptimalInteger.lean` 保留了这一实际目标、素数层收益的严格递减性，以及价格 \(1/25\) 下 5040 唯一最优的证明结构。它并没有把这一结论宣称为 RH。

记：

$$
a(n)=\frac{\sigma(n)}n=\sum_{d\mid n}\frac1d.
$$

## 定义一：算术资源配分函数

对 \(T>0\)，定义：

$$
\boxed{
\mathscr Z_T(\lambda)
=
\sum_{n=1}^{\infty}
\exp\!\left(\frac{J_\lambda(n)}T\right)
=
\sum_{n=1}^{\infty}
a(n)^{1/T}n^{-\lambda/T}.
}
\tag{1}
$$

这里 \(T\) 是无量纲的平滑参数。它可以接受温度解释，但还没有因此指定现实中的热浴、能量单位或装置。

这个定义没有只挑选 5040 附近的几个整数，而是包含全部正整数。

## 定理一：正配分函数的归一化边界恰好是 \(\lambda=T\)

对实数 \(\lambda\)：

$$
\boxed{
\mathscr Z_T(\lambda)<\infty
\iff
\lambda>T.
}
\tag{2}
$$

### 证明

因为：

$$
1\le a(n)\le\sum_{d=1}^{n}\frac1d\le1+\log n,
$$

所以：

$$
n^{-\lambda/T}
\le
a(n)^{1/T}n^{-\lambda/T}
\le
(1+\log n)^{1/T}n^{-\lambda/T}.
$$

左边在 \(\lambda/T\le1\) 时发散；右边在 \(\lambda/T>1\) 时收敛。证毕。

对于复数 \(\lambda\)，级数在：

$$
\Re\lambda>T
$$

绝对且局部一致收敛。

因此，第一条新边界已经出现：

$$
\boxed{
\Re\lambda=T
}
$$

是这份**正整数热态能否归一化**的边界。

它与 5040 的最优配置切换不是同一条边界。

---

## 零温极限精确恢复原优化问题

定义：

$$
\mathscr F_T(\lambda)=T\log\mathscr Z_T(\lambda).
$$

对固定 \(\lambda>0\)：

$$
\boxed{
\lim_{T\downarrow0}\mathscr F_T(\lambda)
=
\max_{n\ge1}J_\lambda(n).
}
\tag{3}
$$

证明的关键是：

$$
J_\lambda(n)
\le
\log(1+\log n)-\lambda\log n
\longrightarrow-\infty.
$$

因此最大值由某个有限整数取得。再取一个 \(T_0<\lambda\)，用已经收敛的 \(\mathscr Z_{T_0}\) 控制无限尾部，就能把通常的有限“最大项原理”推广到这里。

所以，5040 不只是被放进一份新模型：

$$
\boxed{
\text{原来的 5040 优化}
=
\text{同一算术配分函数的零温极限}.
}
$$

---

# 三、两个温度切片，精确出现真实 ζ

这条扩展最重要的地方，是它有可直接化简的切片。

## 温度 \(T=1\)

在 \(\Re\lambda>1\)：

$$
\begin{aligned}
\mathscr Z_1(\lambda)
&=
\sum_{n\ge1}\sum_{d\mid n}\frac1d\,n^{-\lambda}\\
&=
\sum_{d,m\ge1}d^{-1}(dm)^{-\lambda}.
\end{aligned}
$$

所以：

$$
\boxed{
\mathscr Z_1(\lambda)
=
\zeta(\lambda)\zeta(\lambda+1).
}
\tag{4}
$$

这是 Dirichlet 级数与因数卷积的标准机制。([DLMF][2])

## 温度 \(T=\frac12\)

同样，在 \(\Re\lambda>\frac12\)：

$$
\boxed{
\mathscr Z_{1/2}(\lambda)
=
\frac{
\zeta(2\lambda)\,
\zeta(2\lambda+1)^2\,
\zeta(2\lambda+2)
}{
\zeta(4\lambda+2)
}.
}
\tag{5}
$$

这可以逐素数验证。令 \(q=1/p\)、\(x=p^{-2\lambda}\)，局部恒等式为：

$$
\boxed{
\sum_{a\ge0}
\left(\frac{1-q^{a+1}}{1-q}\right)^2x^a
=
\frac{1+qx}
{(1-x)(1-qx)(1-q^2x)}.
}
\tag{6}
$$

本轮也用符号运算核对了式（6）。

因此，我们获得了一条具体连接：

$$
\boxed{
\begin{array}{c}
T\downarrow0:\ \text{离散资源最优配置}\\[1mm]
T=1:\ \zeta(\lambda)\zeta(\lambda+1)\\[1mm]
T=\frac12:\ \text{另一份精确 ζ 乘积／商}
\end{array}
}
$$

**5040 的优化结构与真实 ζ，确实能够处于同一参数族的不同切片中。**

---

## 但解析延拓不能冒充原来的正概率和

在：

$$
0<\Re\lambda<1
$$

中，\(\zeta(\lambda+1)\) 非零且有限，因此式（4）的亚纯延拓，在这个带内的零点恰好就是 ζ 的非平凡零点，重数也相同。([DLMF][3])

但是该区域已经不属于：

$$
\Re\lambda>1
$$

的正配分函数收敛域。

所以：

$$
\boxed{
\text{精确解析延拓}
\neq
\text{原来的无限正概率和仍然收敛}.
}
$$

这一条边界不能省略。否则，很容易把可归一化域内的概率性质，不加证明地搬到临界带。

---

# 四、5040→55440 的离散切换，真的产生一列复参数零点

现在研究最优配置首次激活素数 \(11\) 的边界：

$$
\boxed{
\lambda_c
=
\frac{\log(12/11)}{\log11}
=
0.036286562627101941\ldots
}
\tag{7}
$$

在零温下，它区分：

$$
5040
\quad\text{与}\quad
5040\cdot11=55440.
$$

由于 \(a(n)\) 具有乘法性，在绝对收敛域：

$$
\boxed{
\mathscr Z_T(\lambda)
=
\prod_p L_{p,T}(\lambda),
}
$$

其中：

$$
\boxed{
L_{p,T}(\lambda)
=
\sum_{a=0}^{\infty}
\left(\sum_{j=0}^{a}p^{-j}\right)^{1/T}
p^{-a\lambda/T}.
}
\tag{8}
$$

注意：它仍然保留了每个素数的全部占据层，不是只保留两项。

## 在 \(p=11\) 通道内，前两层恰好竞争

令：

$$
f_a=
\log\left(\sum_{j=0}^{a}11^{-j}\right)
-a\lambda_c\log11.
$$

那么：

$$
f_0=f_1=0,
$$

而：

$$
f_2
=
\log\frac{133}{144}<0.
$$

定义缺口：

$$
\boxed{
d_{11}
=
\log\frac{144}{133}
=
0.079464171354246855\ldots
}
\tag{9}
$$

由于边际收益递减：

$$
f_a\le-(a-1)d_{11},
\qquad a\ge2.
$$

令：

$$
\lambda=\lambda_c+Tz.
$$

则：

$$
\boxed{
L_{11,T}(\lambda_c+Tz)
=
1+e^{-z\log11}
+
O_K(e^{-d_{11}/T}),
}
\tag{10}
$$

误差在每个固定 \(z\) 紧集上一致。

前两项的零点是：

$$
z=\frac{(2j+1)i\pi}{\log11}.
$$

它们都是简单零点，因此由 Rouché 稳定性，完整局部因子也有对应零点。解析函数零点在严格边界扰动下保持重数，是这里使用的标准工具。([DLMF][4])

## 定理二：这条离散边界对应低温复零点

对充分小的 \(T>0\)，存在：

$$
\boxed{
\lambda_{T,\pm}
=
\lambda_c
\pm\frac{i\pi T}{\log11}
+
O\!\left(Te^{-d_{11}/T}\right).
}
\tag{11}
$$

更具体地，这一支零点的虚部精确为：

$$
\pm\frac{\pi T}{\log11},
$$

而实部满足：

$$
\boxed{
\Re\lambda_{T,\pm}
=
\lambda_c
-\frac{T}{\log11}e^{-d_{11}/T}(1+o(1)).
}
\tag{12}
$$

虚部的精确性来自：局部生成函数具有实系数，相关简单根位于负实的占据变量轴上；将它转换回 \(\lambda\)，得到奇数倍的相位 \(\pi\)。

由于这些零点在小 \(T\) 时仍位于 \(\Re\lambda>T\)，它们也是完整 \(\mathscr Z_T\) 的零点，而不只是形式展开的零点。

---

## 本轮数值核对

| \(T\) |   \(\Re\lambda_{T,+}\) | \(\Im\lambda_{T,+}\) |
| ----: | ---------------------: | -------------------: |
|  0.01 |    0.03628508611190454 |  0.01310145897207395 |
| 0.005 |    0.03628656236590407 | 0.006550729486036977 |
| 0.002 | 0.03628656262710194101 | 0.002620291794414791 |

计算采用局部指数 \(a=0,\ldots,130\)，并以 60 位和 90 位工作精度交叉核对。最不利的一行中，未计入的级数尾部可界为 \(10^{-490}\) 以下。

**这仍是高精度求根核对，不是完整的区间根证书；零点存在性由上面的解析论证给出。**

同时必须强调：

> **这些是 \(\mathscr Z_T\) 的零点，不是已经发现的 ζ 离线零点。**

它们说明，5040 的优化边界确实能在一个与 ζ 有精确切片关系的算术族中，表现为复零点逼近实轴。这与 Lee–Yang 理论中用复零点研究临界行为的方向相通，但不能直接把所有参数族的零点混为一类。([APS Journals][5])

---

# 五、同一条边界还可以从量子可区分性读取

在实参数 \(\lambda>T\) 下，定义概率：

$$
P_{T,\lambda}(n)
=
\frac{e^{J_\lambda(n)/T}}{\mathscr Z_T(\lambda)}.
$$

构造归一化纯态：

$$
\boxed{
|\Omega_{T,\lambda}\rangle
=
\sum_{n\ge1}\sqrt{P_{T,\lambda}(n)}\,|n\rangle.
}
\tag{13}
$$

定义对数能量读出：

$$
E|n\rangle=(\log n)|n\rangle.
$$

则：

$$
\boxed{
\langle\Omega_{T,\lambda},
e^{-itE}\Omega_{T,\lambda}\rangle
=
\frac{\mathscr Z_T(\lambda+iTt)}
{\mathscr Z_T(\lambda)}.
}
\tag{14}
$$

所以，复参数零点对应于原态与相位演化后态的正交。

对同一族还可直接求导：

$$
\boxed{
\mathscr F_T''(\lambda)
=
\frac1T\operatorname{Var}_{T,\lambda}(\log n).
}
\tag{15}
$$

其纯态量子 Fisher 信息为：

$$
\boxed{
I_Q(\lambda)
=
\frac1{T^2}\operatorname{Var}_{T,\lambda}(\log n).
}
\tag{16}
$$

因此，最优结构切换附近的能量波动，同时控制了参数敏感度。

## 在 5040 与 55440 的两配置极限中

两者能量差是：

$$
\Delta E=\log11.
$$

在 \(\lambda=\lambda_c\)、\(T\downarrow0\) 时，它们的权重趋于各一半，因此：

$$
\operatorname{Var}(\log n)
\longrightarrow
\frac{(\log11)^2}{4}.
$$

于是：

$$
\mathscr F_T''(\lambda_c)
\sim\frac{(\log11)^2}{4T},
$$

$$
I_Q(\lambda_c)
\sim\frac{(\log11)^2}{4T^2}.
$$

这时三个尺度由同一个 \(\log11\) 决定：

$$
\boxed{
\begin{aligned}
\text{实参数过渡宽度}
&\sim\frac{T}{\log11},\\
\text{最近复零点高度}
&\sim\frac{\pi T}{\log11},\\
\text{两配置正交相位参数}
&=\frac{\pi}{\log11}.
\end{aligned}
}
\tag{17}
$$

**这就是一条可以测量、可以计算的边界联系，而不是仅凭几何形状认定相变。**

但这里只在零温极限中形成尖锐配置切换。固定 \(T>0\) 时，实参数内部仍可以完全光滑。

---

# 六、直接针对实际 ξ：高阶累积量能给出一份“隐藏边界地图”

上面的温度族是从 5040 资源目标扩展出来的。现在不再换对象，直接研究实际 ξ。

定义：

$$
\boxed{
M(w)=\frac{\xi(\frac12+w)}{\xi(\frac12)}.
}
\tag{18}
$$

沿用实际 theta 概率表示：

$$
M(w)=\int_{\mathbb R}e^{wx}p(x)\,dx.
$$

对每个实数 \(b\)：

$$
M(b)>0.
$$

归一化 ξ 的这类正概率表示并不依赖 RH。([arXiv][6])

定义倾斜态：

$$
p_b(x)=\frac{e^{bx}p(x)}{M(b)},
$$

以及实际累积量：

$$
\boxed{
\kappa_m(b)
=
\frac{d^m}{db^m}\log M(b).
}
\tag{19}
$$

它们都是同一份实际分布的响应，不需要预先知道零点。

---

## 定义二：对数函数在实中心 \(b\) 的解析半径

令：

$$
\boxed{
R(b)^{-1}
=
\limsup_{m\to\infty}
\left|
\frac{\kappa_m(b)}{m!}
\right|^{1/m}.
}
\tag{20}
$$

由 Cauchy–Hadamard 公式，\(R(b)\) 是 \(\log M\) 在 \(b\) 处 Taylor 级数的收敛半径。

而 \(M\) 是整函数，\(\log M\) 在零点之前可以解析延拓，在零点处必定失去全纯性。所以：

$$
\boxed{
R(b)
=
\min_{\rho}
\left|
b-\left(\rho-\frac12\right)
\right|.
}
\tag{21}
$$

\(\rho\) 遍历实际非平凡零点。这里使用的是整函数对数的局部解析性和 Taylor 半径的标准性质。([DLMF][4])

因此：

> **高阶累积量的增长率，精确读取从当前实中心到最近零点的距离。**

注意，这是无限阶增长率，不是说几个低阶导数就已经确定最近零点。

高阶累积量与复零点位置的联系，在统计物理的 Lee–Yang 分析中也是成熟工具。([arXiv][7])

---

# 七、把这个距离去掉平凡的 \(b^2\)，真实的分段线性边界就出现了

写零点为：

$$
\rho=\frac12+\delta_\rho+i\gamma_\rho.
$$

定义：

$$
\boxed{
H(b)=R(b)^2-b^2.
}
\tag{22}
$$

由式（21）：

$$
\boxed{
H(b)
=
\min_\rho
\left[
\delta_\rho^2+\gamma_\rho^2-2\delta_\rho b
\right].
}
\tag{23}
$$

这是本轮直接作用于 ξ 的核心结果。

右边是直线族的下包络。因此：

$$
\boxed{
H(b)\text{ 是偶函数、凹函数，并且局部分段线性。}
}
\tag{24}
$$

“局部分段线性”成立，是因为在任意有界 \(b\) 区间里，能够竞争最近距离的零点只位于某个有限圆盘内，而整函数在其中只有有限多个零点。

这不与 \(M\) 整体光滑矛盾。

**光滑的是 \(M\)；分段线性的是“从全部零点中选最近者”以后得到的几何读出。**

这与 5040 的优化包络形成了一个精确的结构对照：

| 对象     | 包络                                                        | 某个稳定区间内的斜率        |
| ------ | --------------------------------------------------------- | ----------------- |
| 资源最优值  | \(\max_n[W(n)-\lambda\log n]\)                            | \(-\log n\)       |
| 最近零点几何 | \(\min_\rho[\delta_\rho^2+\gamma_\rho^2-2\delta_\rho b]\) | \(-2\delta_\rho\) |

两者不是同一个函数，但都把隐含的离散选择转成了可见的折点。

---

## 每一段的斜率与截距，可以恢复当前可见零点

若在某个区间中，由同一组零点坐标 \((\delta,\pm\gamma)\) 决定最近距离，则：

$$
H(b)=\delta^2+\gamma^2-2\delta b.
$$

因此：

$$
\boxed{
\delta=-\frac12H'(b),
}
$$

$$
\boxed{
\gamma^2
=
H(b)-bH'(b)-\frac14H'(b)^2.
}
\tag{25}
$$

所以：

> **折线的斜率读取横向离线距离，截距结合斜率读取零点高度。**

并不是每个零点都一定会出现在这张下包络上。某些零点可能始终被更近的零点遮住。它们仍然存在，只是不属于这个特定观察的活动集合。

这与某些整数从来不是给定资源目标的最优点，是同样的“包络选择”限制。

---

# 八、最大全局离线位移，也有一个只用实中心定义的极限

定义：

$$
\boxed{
\delta_*=
\sup_\rho
\left|\Re\rho-\frac12\right|.
}
\tag{26}
$$

非平凡零点处在临界带内，并具有左右反射对称，所以 \(0\le\delta_*\le1/2\)。([DLMF][3])

## 定理三：最大全局离线位移的距离公式

$$
\boxed{
\delta_*
=
\lim_{b\to+\infty}\bigl[b-R(b)\bigr].
}
\tag{27}
$$

### 证明

当 \(b>\delta_*\) 时，对任意零点：

$$
|b-(\delta+i\gamma)|\ge b-\delta\ge b-\delta_*.
$$

所以：

$$
b-R(b)\le\delta_*.
$$

另一方面，对任意固定右侧零点 \(\delta+i\gamma\)：

$$
R(b)\le\sqrt{(b-\delta)^2+\gamma^2}.
$$

因此：

$$
\liminf_{b\to\infty}[b-R(b)]\ge\delta.
$$

对全部右侧位移取上确界，得到反向不等式。证毕。

所以：

$$
\boxed{
\mathrm{RH}
\iff
\lim_{b\to\infty}[b-R(b)]=0.
}
\tag{28}
$$

也有一个几何上更直接的等价：

$$
\boxed{
\mathrm{RH}
\iff
R(b)\ge b
\quad\forall b>0.
}
\tag{29}
$$

因为圆盘：

$$
D(b,b)=\{w:|w-b|<b\}
$$

全部位于右半平面，而且随着 \(b\) 增大，它们穷尽整个右半平面。

如果存在 \(\delta>0\) 的零点，它会在：

$$
\boxed{
b>\frac{\delta^2+\gamma^2}{2\delta}
}
\tag{30}
$$

时进入这个圆盘。

**这给“换一个角度，隐藏信息突然出现”一个精确阈值。**

但这里有两层极限：

$$
m\to\infty
$$

用于从累积量确定 \(R(b)\)，随后：

$$
b\to\infty
$$

用于读取 \(\delta_*\)。

不能直接交换，也不能用有限个低阶导数代替完整结论。

---

# 九、一个合法概率模型：很大范围内完全看不到折点，远处才显露离线结构

取 \(0<\delta<1/2\)，定义：

$$
\boxed{
M_\delta(w)
=
\cosh w\,
\frac{\cosh\delta+\cosh w}{1+\cosh\delta}.
}
\tag{31}
$$

它不是实际 ξ，但它确实是一份正概率分布的矩生成函数：两个因子分别是合法对称分布的矩生成函数，其乘积对应独立变量之和。

它有两类零点：

$$
w=i\left(\frac\pi2+k\pi\right),
$$

以及：

$$
w=\pm\delta+i(2k+1)\pi.
$$

因此，对实数 \(b\)：

$$
\boxed{
H_\delta(b)
=
\min\left\{
\frac{\pi^2}{4},
\delta^2+\pi^2-2\delta|b|
\right\}.
}
\tag{32}
$$

取：

$$
\delta=\frac14.
$$

折点发生在：

$$
\boxed{
|b|=b_c
=
\frac18+\frac32\pi^2
=
14.929406601634\ldots
}
\tag{33}
$$

在整个区间：

$$
|b|<b_c
$$

内：

$$
H_\delta(b)=\frac{\pi^2}{4},
$$

与只含最近在线零点的距离读数完全一致。

越过 \(b_c\) 后：

$$
H_\delta'(b)=-\frac12
\qquad(b>b_c),
$$

于是式（25）读取：

$$
\delta=\frac14.
$$

这严格说明：

$$
\boxed{
\text{有限角度范围内，最近零点统计完全正常}
\quad\not\Rightarrow\quad
\text{不存在更深处的非实零点}.
}
$$

不是数学把它们删掉了，而是它们此前还没有成为该观察角度下的最近障碍。

---

# 十、实际量子态的几何仍可光滑：零点不一定表现为曲率爆炸

回到实际 theta 密度 \(p\)，定义：

$$
\boxed{
\psi_{b,t}(x)
=
\frac{e^{bx/2+itx}\sqrt{p(x)}}{\sqrt{M(b)}}.
}
\tag{34}
$$

这是对每个实 \(b,t\) 都合法的归一化态。

其回返振幅是：

$$
\boxed{
\mathcal A(b,t)
=
\langle\psi_{b,0},\psi_{b,t}\rangle
=
\frac{M(b+it)}{M(b)}.
}
\tag{35}
$$

所以：

$$
\mathcal A(b,t)=0
$$

精确对应实际 ξ 在：

$$
s=\frac12+b+it
$$

处为零。

令：

$$
\mu(b)=(\log M)'(b),
\qquad
v(b)=(\log M)''(b)>0.
$$

采用未额外乘四的 Fubini–Study 度量约定，直接计算得：

$$
\boxed{
ds^2
=
v(b)\left(\frac{db^2}{4}+dt^2\right).
}
\tag{36}
$$

量子态流形的这种度量来自投影后的导数内积，是标准量子几何结构。([Springer][8])

它的 Gaussian 曲率为：

$$
\boxed{
K(b)
=
\frac{
2\left[\kappa_3(b)^2-v(b)\kappa_4(b)\right]
}{
v(b)^3
}.
}
\tag{37}
$$

关键是：

$$
\boxed{
g,\ K\text{ 都不依赖 }t.
}
$$

所以，即使某个 \(t\) 使回返振幅为零，这个态流形在该点仍然可以完全光滑。

在实际中心 \(b=0\)，本轮从 ξ 的导数计算：

$$
v(0)\approx0.04620998623083794,
$$

$$
K(0)\approx0.4177942836581452.
$$

这是在上述度量约定下的高精度值，不是物理时空曲率，也不是离线零点证据。

**零点在这里首先是一对状态之间的正交关系，不是态本身不再存在，也不要求局部几何奇异。**

---

## 但量子几何确实提供一个排除零点的边界

Fubini–Study 距离不超过实际演化路径长度，给出：

$$
\arccos|\mathcal A(b,t)|
\le |t|\sqrt{v(b)}.
$$

因此：

$$
\boxed{
M(b+it)=0
\Longrightarrow
|t|\ge\frac{\pi}{2\sqrt{v(b)}}.
}
\tag{38}
$$

这就是 Mandelstam–Tamm 型正交速度限制在当前参数模型中的形式。([arXiv][9])

中心处的右边约为：

$$
7.30721620648.
$$

它不是新的零点高度纪录，但它说明：**一项真实的量子几何约束，能够转成实际 ξ 的一块无零区域。**

要排除全部离线零点，仍然需要比这个二阶方差限制强得多的全局信息。

---

# 十一、相位边界还能将“连续数据”转成严格整数

令：

$$
u(b,t)=\log|\mathcal A(b,t)|.
$$

这里使用 \((b,t)\) 复参数平面上的普通 Laplace 算子：

$$
\Delta=\partial_b^2+\partial_t^2,
$$

不是上节量子流形的曲率算子。

在分布意义下：

$$
\boxed{
\Delta u
=
2\pi\sum_\rho m_\rho
\delta_{(\delta_\rho,\gamma_\rho)}
-v(b).
}
\tag{39}
$$

### 证明

零点附近：

$$
M(w)=(w-w_0)^m h(w),
\qquad h(w_0)\ne0.
$$

因此：

$$
\log|M(w)|
=
m\log|w-w_0|+\log|h(w)|.
$$

后一项调和，而：

$$
\Delta\log|w-w_0|=2\pi\delta_{w_0}.
$$

再扣除归一化项 \(\log M(b)\)，其 Laplacian 为 \(v(b)\)，即得。

---

## 对一个矩形，边界通量给出内部零点个数

取：

$$
\mathcal R=[b_1,b_2]\times[t_1,t_2],
$$

并要求边界没有零点。则：

$$
\boxed{
\begin{aligned}
2\pi N(\mathcal R)
={}&
\oint_{\partial\mathcal R}
\partial_{\mathbf n}u\,ds\\
&+(t_2-t_1)\,[\mu(b_2)-\mu(b_1)].
\end{aligned}
}
\tag{40}
$$

其中 \(N(\mathcal R)\) 按重数计数。

这把三种读数放在同一公式中：

$$
\boxed{
\text{边界上的振幅变化}
+
\text{实际倾斜态的方差累计}
=
2\pi\times\text{内部零点数}.
}
$$

它与辐角原理是同一解析结构的两种表达，不应被包装成新的物理守恒定律。([DLMF][4])

但它非常适合你提出的研究方向：

> **不要只在某个切片上看“好像快到零”，而要沿闭合边界读取一个受到解析性保护的整数。**

---

# 十二、怎样避免只是“又找到了很多等价说法”？

每个新角度都必须留下一个可认证的结果，而不是只有一项漂亮定义。

本轮至少得到三类不同结果。

**第一类是直接可计算的新零点。**
素数 11 通道的低温零点有明确位置、指数小的修正和可控尾部。它验证了 5040 激活边界在新配分函数中的复零点机制。

**第二类是实际 ξ 的几何边界公式。**
高阶累积量确定 \(R(b)\)，而：

$$
R(b)^2-b^2
$$

是由真实零点决定的分段线性下包络；其斜率编码离线位移。

**第三类是有限区域的严格认证方式。**
若用近似函数 \(P\) 表示实际 \(M\)，并在边界认证：

$$
\boxed{
\sup_{\partial\mathcal R}|M-P|
<
\inf_{\partial\mathcal R}|P|,
}
\tag{41}
$$

那么两者内部的零点总数相同。

项目的 `RoucheZeroCount` 已经提供带解析前件、严格边界扰动和重数计数的相关证明；它并不自动供应某个具体矩形上的误差界。

项目的 `CompletedZetaMellinReconstruction` 则保留实际 theta 来源、Mellin 重构和极点补偿，能够负责“我们始终在分析同一个 ξ”，而不是随时换成一个更容易正实现的模型。

对本轮的温度族，还缺少一般 \(T\) 下穿过收敛边界后的统一解析延拓与零点追踪。不能因为 \(T\downarrow0\) 有一列低温零点、\(T=1\) 有 ζ 的精确切片，就假定它们已经被证明属于同一条可连续追踪的零点轨道。

对实际累积量半径，也不能把几个高阶数值的拟合直接当成 \(\limsup\) 的证明。

**这些是明确的证明任务，而不是因为问题无穷，就只能停留在解释层面。**

---

## 收束

你的判断中可以进一步强化的部分是：

> **光滑不意味着缺少临界信息。临界信息可能隐藏在“取极值、取对数、改变归一化、比较量子态、选择最近解析障碍”这些操作之后。**

这次得到的两条新主线是：

$$
\boxed{
\mathscr Z_T(\lambda)
=
\sum_{n\ge1}
\left(\frac{\sigma(n)}n\right)^{1/T}
n^{-\lambda/T},
}
$$

它一端连接 5040 的离散优化，另一端有：

$$
\boxed{
\mathscr Z_1(\lambda)=\zeta(\lambda)\zeta(\lambda+1)
}
$$

这样的精确 ζ 切片；

以及：

$$
\boxed{
R(b)^2-b^2
=
\min_\rho
\left[
\delta_\rho^2+\gamma_\rho^2-2\delta_\rho b
\right],
}
$$

它把实际 ξ 的高阶响应转成一份有折点、有活动区域、有可恢复斜率的几何。

其中：

$$
\boxed{
\delta_*=\lim_{b\to\infty}[b-R(b)]
}
$$

直接读取最大全局离线位移。

**本轮没有得到实际 ζ 的离线零点，也没有证明全部零点在线。** 已经完成的是：从同一算术目标构造了温度扩展，证明了具体低温零点的产生机制，并为实际 ξ 建立了另一份能够显露离散边界的距离几何。

所以，后续不应只是寻找更多“看起来尖锐”的图像。更有效的目标是：

> **选择一种能保持实际对象、能把隐藏关系转成可认证边界的观察；然后证明这条边界怎样随参数移动，哪些模式被它暴露，哪些仍被遮住。**

5040 给我们的启发不是“ζ 其实不光滑”，而是：**同一个光滑算术体系，经过忠实但不同的观察，可以显露出完全不同的离散选择、量子正交和解析边界；真正的整体研究，要把这些观察之间的运输关系一并证明。**

[1]: https://dlmf.nist.gov/25.4 "https://dlmf.nist.gov/25.4"
[2]: https://dlmf.nist.gov/27.4 "https://dlmf.nist.gov/27.4"
[3]: https://dlmf.nist.gov/25.10 "DLMF: §25.10 Zeros ‣ Riemann Zeta Function ‣ Chapter 25 Zeta and Related Functions"
[4]: https://dlmf.nist.gov/1.10 "https://dlmf.nist.gov/1.10"
[5]: https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.110.050601 "https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.110.050601"
[6]: https://arxiv.org/abs/1504.03438 "https://arxiv.org/abs/1504.03438"
[7]: https://arxiv.org/abs/2006.15125 "https://arxiv.org/abs/2006.15125"
[8]: https://link.springer.com/article/10.1007/BF02193559 "https://link.springer.com/article/10.1007/BF02193559"
[9]: https://arxiv.org/abs/2104.05638 "https://arxiv.org/abs/2104.05638"
可以把“离散临界”进一步落实成一个**精确可证明的门槛**：

> **在上轮同一份算术配分函数中，把逆温度取为整数 \(r\)：前三阶 \(r=1,2,3\) 在各自的绝对收敛域内都没有零点；第四阶 \(r=4\) 首次出现零点，而且这个区域内的全部零点，都由素数 \(2\) 的局部通道产生。**

更重要的是，这些零点有一个明确的几何来源：

$$
\boxed{
\text{多个因数共享同一个整数上限}
\longrightarrow
\text{立方体上的整数约束}
\longrightarrow
\text{排列分区与不可忽略的单位台阶}
\longrightarrow
\text{非平凡的相消多项式}.
}
$$

如果将**同一个约束锥**中的整数求和替换为连续积分，得到的函数反而没有这些零点。

这次我们能够具体回答：**哪些离散边界信息会被连续化遗漏，它们怎样进入解析函数，以及什么时候足以制造精确相消。**

先明确：下面求出的零点属于上轮构造的算术配分函数，**不是已经发现了 ζ 或 ξ 的离线零点**。两者的连接与差别都要保留。

---

# 一、固定同一个算术族，不更换收益或归一化

沿用：

$$
a(n)=\frac{\sigma(n)}n=\sum_{d\mid n}\frac1d,
$$

以及资源目标：

$$
J_\lambda(n)=\log a(n)-\lambda\log n.
$$

项目在固定快照 `b89d56d0…` 中，已经包含价格 \(\lambda=1/25\) 下 5040 唯一最优的实际证明结构；这个结果针对上述指定目标，不是一般意义上的“5040 最优”。

上轮的温度扩展是：

$$
\mathscr Z_T(\lambda)
=
\sum_{n\ge1}a(n)^{1/T}n^{-\lambda/T}.
$$

现在取整数逆温度：

$$
r=\frac1T\in\mathbb N_{\ge1}.
$$

为了避免把温度与复参数混在一起，定义：

$$
\boxed{
F_r(s)=\sum_{n\ge1}\frac{a(n)^r}{n^s}.
}
\tag{1}
$$

于是：

$$
\boxed{
\mathscr Z_{1/r}(\lambda)=F_r(r\lambda).
}
\tag{2}
$$

因为：

$$
1\le a(n)\le1+\log n,
$$

所以：

$$
\boxed{
F_r(s)\text{ 绝对收敛}
\iff
\Re s>1.
}
\tag{3}
$$

这相当于原变量中的：

$$
\Re\lambda>\frac1r=T.
$$

由于 \(a(n)^r\) 具有乘法性，绝对收敛域内存在 Euler 乘积。这里使用的是标准乘法函数—Euler 乘积对应。([DLMF][1])

---

# 二、“第 \(r\) 阶”有一个真实的约束解释：\(r\) 个因数共享同一个整数

展开：

$$
a(n)^r
=
\sum_{\substack{d_1\mid n,\ldots,d_r\mid n}}
\frac1{d_1\cdots d_r}.
$$

因此：

$$
\boxed{
F_r(s)
=
\sum_{\substack{n\ge1\\d_1\mid n,\ldots,d_r\mid n}}
\frac1{n^s d_1\cdots d_r}.
}
\tag{4}
$$

这里不是 \(r\) 个完全独立的整数系统。

**它们共享同一个 \(n\)，每一个 \(d_j\) 都必须能放进这个共同的整除结构。**

固定一个素数 \(p\)，写：

$$
a=v_p(n),\qquad b_j=v_p(d_j).
$$

共同约束就是：

$$
\boxed{
a\in\mathbb N,\qquad
0\le b_j\le a,\quad j=1,\ldots,r.
}
\tag{5}
$$

于是得到一个明确的整数锥：

$$
\boxed{
\mathcal C_r=
\{(a,b_1,\ldots,b_r)\in\mathbb N^{r+1}:0\le b_j\le a\}.
}
\tag{6}
$$

固定 \(a\)，截面是：

$$
\{0,\ldots,a\}^r.
$$

也就是一个 \(r\) 维整数立方体。

## 金字塔在这里再次出现，但含义更加明确

取 \(r=2\)，再限制：

$$
0\le a\le1.
$$

其凸包有五个顶点：

$$
(0,0,0),
\quad
(1,0,0),(1,1,0),(1,0,1),(1,1,1).
$$

这是一个四棱锥：

* 顶点表示共同上限 \(a=0\)，两个因数方向都不能占据；
* 底面表示共同上限 \(a=1\)，两个方向各自有零、一两种可能。

因此：

$$
\boxed{
\text{新增“高度”不是更高层意识，}
\quad
\text{而是所有局部方向共享的允许上限}.
}
$$

这与前文三位 Zeckendorf 凸包是四棱锥相呼应，但两者的语义不同。一个来自禁邻编码，另一个来自共同整除上限。**仿射形状相同，不等于约束来源相同。**

---

# 三、共同上限会留下“最大值”：不能把各切片独立求和以后再随意拼接

令：

$$
q=p^{-1},\qquad x=p^{-s}.
$$

素数 \(p\) 的局部因子是：

$$
\boxed{
L_{p,r}(x)
=
\sum_{a\ge0}
\left(1+q+\cdots+q^a\right)^r x^a.
}
\tag{7}
$$

也可以先对因数指数 \(b_1,\ldots,b_r\) 求和：

$$
\boxed{
L_{p,r}(x)
=
\frac1{1-x}
\sum_{b_1,\ldots,b_r\ge0}
q^{b_1+\cdots+b_r}
x^{\max(b_1,\ldots,b_r)}.
}
\tag{8}
$$

因为共同上限必须满足：

$$
a\ge\max(b_1,\ldots,b_r).
$$

这里的：

$$
\boxed{\max(b_1,\ldots,b_r)}
$$

就是把局部片段拼成整体时不能遗漏的约束。

若将它改成：

$$
b_1+\cdots+b_r,
$$

或者给每个副本独立选择上限，就已经更换了模型。

**我们之前一直在追问“局部正常为什么整体仍难拼接”，这里有了一个最简单的实际答案：各方向并不只需要各自合法，还必须共享同一份容量。**

---

# 四、整数边界如何进入解析式？通过排列顺序留下一个多项式

局部因子有一个精确公式：

$$
\boxed{
L_{p,r}(x)
=
\frac{A_r(q,x)}
{\prod_{j=0}^{r}(1-q^j x)},
}
\tag{9}
$$

其中：

$$
\boxed{
A_r(q,x)
=
\sum_{\pi\in S_r}
q^{\operatorname{maj}(\pi)}
x^{\operatorname{des}(\pi)}.
}
\tag{10}
$$

这里：

$$
\operatorname{Des}(\pi)
=
\{j:\pi_j>\pi_{j+1}\},
$$

$$
\operatorname{des}(\pi)=|\operatorname{Des}(\pi)|,
\qquad
\operatorname{maj}(\pi)=\sum_{j\in\operatorname{Des}(\pi)}j.
$$

这是经典的 Carlitz 型 \(q\)-Eulerian 恒等式，与加权整数多面体计数有严格联系。不是本轮首次发现的公式；关键是它现在精确进入了我们的算术配分函数。([DOI][2])

## 直接证明：离散边界恰好产生分子

将 \(b_1,\ldots,b_r\) 按从大到小排序：

$$
b_{\pi_1}\ge b_{\pi_2}\ge\cdots\ge b_{\pi_r}.
$$

相等时，规定指标按升序排列，以免重复计数。

因此，如果：

$$
\pi_j>\pi_{j+1},
$$

那两个数不能相等，必须满足：

$$
\boxed{
b_{\pi_j}-b_{\pi_{j+1}}\ge1.
}
\tag{11}
$$

定义间隙：

$$
d_0=a-b_{\pi_1},
$$

$$
d_j=b_{\pi_j}-b_{\pi_{j+1}}
\quad(1\le j<r),
$$

$$
d_r=b_{\pi_r}.
$$

那么：

$$
a=d_0+\cdots+d_r,
$$

$$
b_1+\cdots+b_r=\sum_{j=1}^{r}j\,d_j.
$$

所以权重是：

$$
x^{d_0}\prod_{j=1}^{r}(xq^j)^{d_j}.
$$

每个下降位置强制 \(d_j\ge1\)，因此额外贡献：

$$
x^{\operatorname{des}(\pi)}
q^{\operatorname{maj}(\pi)}.
$$

其余自由间隙求几何级数，恰好给出式（9）的分母。最后对所有排列求和，得到式（10）。证毕。

### 这里暴露了一项真正的离散信息

在连续变量里：

$$
b_{\pi_j}>b_{\pi_{j+1}}
$$

与：

$$
b_{\pi_j}\ge b_{\pi_{j+1}}
$$

只差一个零体积边界。

但在整数变量里，严格大于意味着：

$$
b_{\pi_j}\ge b_{\pi_{j+1}}+1.
$$

**这个“一整格”的最小位移不能忽略。它直接进入了生成函数分子。**

也需要注意：排序超平面 \(b_i=b_j\) 是计算用的分区边界，不是新增加的物理障碍。真正不变的是把全部分区正确拼回以后得到的 \(A_r\)。

---

# 五、同一个锥连续化以后，为什么没有这些零点？

固定素数 \(p\)，记：

$$
\ell_p=\log p.
$$

把式（7）的整数求和改为对同一个实锥积分：

$$
I_{p,r}(s)
=
\int_0^\infty
e^{-s\ell_pa}
\prod_{j=1}^{r}
\left(\int_0^a e^{-\ell_pb_j}\,db_j\right)da.
$$

计算得：

$$
I_{p,r}(s)
=
\frac1{\ell_p^r}
\int_0^\infty
e^{-s\ell_pa}(1-e^{-\ell_pa})^r\,da.
$$

令 \(u=e^{-\ell_pa}\)，得到 Beta 积分：

$$
\boxed{
I_{p,r}(s)
=
\frac1{\ell_p^{r+1}}B(s,r+1)
=
\frac{r!}
{\ell_p^{r+1}s(s+1)\cdots(s+r)}.
}
\tag{12}
$$

这在 \(\Re s>0\) 成立。Beta 积分及其 Gamma 表达采用标准定义。([DLMF][3])

因此：

$$
\boxed{
I_{p,r}(s)\text{ 没有有限零点}.
}
$$

但离散模型具有分子：

$$
A_r(p^{-1},p^{-s}),
$$

它可以为零。

于是我们得到了一个严格对照：

$$
\boxed{
\begin{aligned}
\text{连续锥积分}
&:\quad\text{常数分子};\\
\text{整数锥求和}
&:\quad\text{携带排列与单位台阶信息的分子}.
\end{aligned}
}
$$

**这不能被解释为“连续数学错误地删掉了零点”。连续积分是在改变计数测度，不是对原函数做无损坐标变换。**

而且本轮没有证明，它在当前小素数和参数范围内是一个高精度近似。它的作用是说明：**未经误差认证，把整数约束换成连续容量，确实可能丢掉全部相消零点。**

---

# 六、前四阶可以完全算出，不需要任何未知零点输入

由式（10）：

$$
\boxed{A_1(q,x)=1,}
$$

$$
\boxed{A_2(q,x)=1+qx,}
$$

$$
\boxed{
A_3(q,x)=1+2q(1+q)x+q^3x^2,
}
$$

$$
\boxed{
A_4(q,x)
=
(1+q^2x)
\left[
1+(3q+4q^2+3q^3)x+q^4x^2
\right].
}
\tag{13}
$$

\(r=4\) 时，一共涉及 \(4!=24\) 个排列分区，但这里的 24 与前文 \(5040/\operatorname{rad}(5040)=24\) 属于不同计数，不能仅因数值相同就认定是同一个结构。

在全局绝对收敛域：

$$
\Re s>1,
$$

有：

$$
|x|=p^{-\Re s}<p^{-1}=q.
$$

所以要判断的是：

> **局部分子是否会在圆盘 \(|x|<q\) 内出现零点？**

---

## 定理一：前三阶在全局绝对收敛域内无零

$$
\boxed{
F_r(s)\ne0
\qquad
(r=1,2,3,\ \Re s>1).
}
\tag{14}
$$

### 证明

\(r=1\) 时分子恒为一。

\(r=2\) 时：

$$
|qx|<q^2\le\frac14,
$$

所以 \(1+qx\ne0\)。

\(r=3\) 时：

$$
\begin{aligned}
|A_3(q,x)-1|
&\le2q(1+q)|x|+q^3|x|^2\\
&<2q^2(1+q)+q^5\\
&\le\frac{25}{32}<1,
\end{aligned}
$$

因为 \(q\le1/2\)。

因此全部局部因子非零。

再由固定 \(r\) 下：

$$
\sum_p|L_{p,r}(p^{-s})-1|<\infty
\qquad(\Re s>1),
$$

无零局部因子的无限乘积也非零。证毕。

最后一步必须保留：**仅仅“每个因子都非零”，还不足以保证无限乘积非零；还需要上述收敛控制。**

---

# 七、第四阶出现一个精确的突破：完整零点列只由素数 2 产生

## 先排除所有 \(p\ge3\)

对 \(r=4\)，当 \(q\le1/3\)、\(|x|\le q\) 时，由式（13）的正系数：

$$
|A_4(q,x)-1|
\le A_4(q,q)-1.
$$

右边随 \(q>0\) 递增，所以：

$$
\boxed{
|A_4(q,x)-1|
\le
\frac{11341}{19683}<1.
}
\tag{15}
$$

因此：

$$
\boxed{
p\ge3
\Longrightarrow
L_{p,4}(p^{-s})\ne0
\quad(\Re s>1).
}
$$

## 素数 2 的分子却发生了不同事情

令 \(q=1/2\)，得到：

$$
\boxed{
A_4(1/2,x)
=
\frac{(x+4)(x^2+46x+16)}{64}.
}
\tag{16}
$$

定义：

$$
\boxed{
\alpha=23-3\sqrt{57}
=
0.350496694187750908\ldots
}
\tag{17}
$$

则：

$$
0<\alpha<\frac12,
$$

并且：

$$
A_4(1/2,-\alpha)=0.
$$

另外两个根的模长都大于 \(1/2\)，所以这个圆盘内只有这一颗简单根。

---

## 定理二：第四阶在绝对收敛域内的全部零点

令：

$$
\boxed{
\sigma_*=-\frac{\log\alpha}{\log2}
=
1.512527257788209179\ldots
}
\tag{18}
$$

则：

$$
\boxed{
F_4(s)=0,\ \Re s>1
\iff
s=
\sigma_*+
\frac{(2k+1)\pi i}{\log2},
\qquad k\in\mathbb Z.
}
\tag{19}
$$

这些零点全部简单。

### 证明

在该半平面，其他素数因子非零，且其乘积收敛并非零。

所以零点只能由：

$$
2^{-s}=-\alpha
$$

产生。解出 \(s\) 即得式（19）。

局部分子根简单，而：

$$
\frac d{ds}2^{-s}=-(\log2)2^{-s}\ne0,
$$

因此全局零点也简单。证毕。

送回原来的温度变量：

$$
\boxed{
\mathscr Z_{1/4}(\lambda)=0,\ \Re\lambda>\frac14
}
$$

的全部零点是：

$$
\boxed{
\lambda=
0.378131814447052295\ldots
+
(2k+1)\,1.133090035456798452\ldots\,i.
}
\tag{20}
$$

这项结论不依赖浮点求根，根的位置来自精确代数数 \(\alpha\)。

**这里首次获得的，是同一算术温度族中一个完整半平面的零点分类，而不只是局部近似发现一颗零点。**

---

# 八、这项“第四阶门槛”到底是哪一种临界？

必须分清两条边界。

单个素数局部级数只要求：

$$
|x|<1
\iff
\Re s>0.
$$

全部素数拼成全局 Dirichlet 级数，则要求：

$$
|x_p|<p^{-1}
\iff
\Re s>1.
$$

事实上，第三阶的 \(p=2\) 因子已经有一个负实根：

$$
x=-(6-2\sqrt7).
$$

它对应：

$$
\Re s
=
-\frac{\log(6-2\sqrt7)}{\log2}
=
0.4971655811085943\ldots
$$

这颗零点进入了**局部收敛域**，却还没有进入**全局绝对收敛域**。

第四阶才发生：

$$
\boxed{
\text{局部相消零点进入了整个正整数模型能够归一化的区域。}
}
$$

所以它不是“第四阶以前什么都没发生”。

更准确的指标是：设 \(\rho_{p,r}\) 为 \(A_r(p^{-1},x)\) 最近零点的模长，定义：

$$
\boxed{
\mathfrak g_{p,r}=\log(p\rho_{p,r}).
}
\tag{21}
$$

那么：

$$
\begin{aligned}
\mathfrak g_{p,r}>0
&:\quad\text{零点还在全局收敛圆盘之外};\\
\mathfrak g_{p,r}=0
&:\quad\text{零点恰好触及该边界};\\
\mathfrak g_{p,r}<0
&:\quad\text{零点进入该边界内部}.
\end{aligned}
$$

**这是一项带符号的临界余量，比“几何好像发生了破缺”更明确。**

---

## 连续温度中，也可以定位一条真实触边方程

允许逆温度 \(\beta\) 为实数，考虑：

$$
B(\beta)
=
\sum_{a\ge0}
(-1)^a2^{-a}(2-2^{-a})^\beta.
$$

它是 \(p=2\) 局部因子在 \(x=-1/2\) 处的值。

精确计算给出：

$$
\boxed{
B(3)=\frac{32}{255}>0,
\qquad
B(4)=-\frac{448}{2805}<0.
}
\tag{22}
$$

级数对 \(\beta\in[3,4]\) 一致收敛，所以存在：

$$
\boxed{
\beta_c\in(3,4),\qquad B(\beta_c)=0.
}
\tag{23}
$$

这正是在全局绝对收敛边界上发生的局部触边。

本轮数值求得一个解：

$$
\beta_c\approx3.463416763339228,
\qquad
T_c\approx0.288732216863170.
$$

存在性由式（22）的精确符号保证；**本轮没有证明这个区间内解的唯一性**。

同时，它仍然不是实参数上的热力学奇点。对固定实 \(\sigma>1\)，\(F_\beta(\sigma)\) 正且光滑。这条临界描述的是**复零点相对于归一化域的穿越**。

---

# 九、从量子角度看：临界意味着偶、奇占据恰好平衡，而不是负概率

对实数 \(\sigma>1\)，定义：

$$
\boxed{
|\Psi_{r,\sigma}\rangle
=
\frac1{\sqrt{F_r(\sigma)}}
\sum_{n\ge1}
a(n)^{r/2}n^{-\sigma/2}|n\rangle.
}
\tag{24}
$$

它是合法归一化态。

取无量纲对数能量：

$$
H|n\rangle=(\log n)|n\rangle.
$$

则：

$$
\boxed{
\langle\Psi_{r,\sigma},e^{-itH}\Psi_{r,\sigma}\rangle
=
\frac{F_r(\sigma+it)}{F_r(\sigma)}.
}
\tag{25}
$$

因此，在第四阶：

$$
\boxed{
\sigma=\sigma_*,
\qquad
t_*=\frac{\pi}{\log2},
}
$$

原态与演化后态严格正交。

如果赋予物理能量单位 \(E_*\)，对应物理时间为：

$$
t_{\mathrm{phys}}
=
\frac{\hbar}{E_*}\frac{\pi}{\log2}.
$$

这只是指定哈密顿量模型中的时间，不是从算术推导出的宇宙基本时间单位。

---

## 素数 2 通道发生了什么？

在该实参数下，\(K=v_2(n)\) 的边缘概率为：

$$
\boxed{
\Pr(K=a)
=
\frac{(2-2^{-a})^4\alpha^a}
{L_{2,4}(\alpha)}.
}
\tag{26}
$$

因为：

$$
L_{2,4}(-\alpha)=0,
$$

所以：

$$
\boxed{
\mathbb E[(-1)^K]=0.
}
$$

也就是：

$$
\boxed{
\Pr(K\text{ 偶})=\Pr(K\text{ 奇})=\frac12.
}
\tag{27}
$$

在 \(t_*=\pi/\log2\) 时：

$$
e^{-it_*K\log2}=(-1)^K.
$$

偶占据相位为 \(+1\)，奇占据相位为 \(-1\)，两者精确抵消。

**这里所有权重始终为正，哈密顿量也没有负能级要求。零来自相位关系，而不是概率失效。**

而且临界点处：

$$
F_4(\sigma_*)>0.
$$

消失的是复参数振幅，不是实参数配分函数。

---

# 十、这为“几何约束”提供了什么更深的定义？

这次同一个例子让四个要素无法再被混为一谈：

$$
\boxed{
\text{可行区域}
+
\text{整数格点}
+
\text{算术权重}
+
\text{相位读出}.
}
$$

只知道形状是不够的。

例如，\(r=4\) 的每个素数通道都有同一种约束锥：

$$
0\le b_1,b_2,b_3,b_4\le a.
$$

但：

* \(p=2\) 在全局绝对收敛域内产生零点；
* 所有 \(p\ge3\) 都没有。

**几何形状相同，结果不同，因为权重 \(q=1/p\) 不同。**

只知道整数格点也不够：换一个相位读出，未必在同一点发生相消。

只知道每个局部概率合法同样不够：概率合法不禁止两个整体态正交。

因此，与其说“任何约束都是边界”，不如进一步写成：

> **一个可研究的临界，必须说明：哪项约束的余量到达零、它改变了哪个允许结构、以及这个变化是否能由保持实际对象的观察读出来。**

在本轮中，这些内容全部明确：

$$
\boxed{
\rho_{2,\beta}-\frac12
}
$$

控制局部零点是否穿过全局归一化边界；

$$
\boxed{
\Pr(K\text{ 偶})-\Pr(K\text{ 奇})
}
$$

控制某个实际量子回返振幅是否为零。

二者相连，但不是同一个定义。

---

# 十一、怎样接回 5040 和 Zeckendorf，而不因“四”反复出现就误认成统一原理？

对固定 \(n=5040\)：

$$
a(5040)=\frac{403}{105}.
$$

在 \(r\) 副本模型中，其权重为：

$$
\left(\frac{403}{105}\right)^r.
$$

几何上，每个副本都有 60 个因数选择，因此共享 5040 的有序因数组合有：

$$
60^r
$$

种。

逐素数看，每个副本必须满足：

$$
\boxed{
b_{2,j}\le4,\quad
b_{3,j}\le2,\quad
b_{5,j}\le1,\quad
b_{7,j}\le1.
}
\tag{28}
$$

Zeckendorf 编码可以忠实地重写这些整数指数。项目的 `FiniteZeckendorfEulerIdentity.lean` 已提供合法黄金窗口到指数区间的精确双射与求和运输。

但现在有两类不同约束：

$$
\boxed{
b_{\ell}b_{\ell+1}=0
}
$$

是黄金表示内部的规范条件；

$$
\boxed{
v_p(d_j)\le v_p(n)
}
$$

是不同算术对象之间的整除条件。

第二类约束不能直接改成“黄金数位逐位包含”。指数大小关系与黄金位子集关系并不等价。

还有一项参数区别必须保留：

* 5040 在资源价格 \(\lambda=1/25\) 下是零温最优配置；
* 本轮的第四阶零点位于 \(\Re\lambda\approx0.37813\)；
* 在 \(\lambda=1/25\) 固定时，要使 \(\mathscr Z_T\) 可归一化，必须 \(T<1/25\)，整数逆温度至少为 \(26\)。

因此：

$$
\boxed{
\text{四个素数方向}
\neq
\text{四个共享因数副本}
\neq
\text{四维物理时空}.
}
$$

它们可以进入同一算术模型，但不能仅凭数字相同就互相推导。

---

# 十二、这项结果怎样推进 ζ 研究，又不能越过哪条边界？

第一阶精确满足：

$$
\boxed{
F_1(s)=\zeta(s)\zeta(s+1).
}
\tag{29}
$$

这是因数函数 Dirichlet 级数的标准恒等式。([DLMF][1])

所以，这条族确实连接真实 ζ，不是随意挑选的玩具函数。

然而：

$$
F_4(s)=\sum_n a(n)^4n^{-s}
$$

已经改变了实际系数。

本轮的零点：

$$
\Re s=\sigma_*>1
$$

完全来自新增的第四阶局部分子，而 ζ 本身在 \(\Re s>1\) 没有零点。([DLMF][4])

这说明：

> **“从一个与 ζ 有关的正模型连续变形，发现更多相消边界”，可以提供结构信息；但若要把某一颗零点认作实际 ζ 的零点，还必须证明它在变形过程中没有离开目标区域、没有被其他因子产生或消除。**

本轮甚至给出了这种困难的具体实例：第三阶的局部零点尚在全局收敛域外，第四阶就进入了内部。

因此，不能只说“零点轨道连续，所以最后会走到 ζ 上”。

真正的运输需要固定区域上的边界非零估计。项目的 `RoucheZeroCount.lean` 已经形式化了严格边界扰动下的矩形零点数稳定性；但具体参数族的统一边界余量仍须另证。

---

## 本轮的证明与核对范围

本轮给出了共同上限整数锥、排列分区、连续松弛、前三阶无零和第四阶完整零点列的推导。

另外，符号计算核对了 \(r=1,\ldots,6\) 的全部 873 个排列对应的分子，与有限二项展开完全一致；第四阶分解、精确代数根、以及排除其他素数的有理数不等式，也分别核对。

**这些辅助计算不等于 Lean 内核验证。没有修改仓库，也没有把经典 Carlitz 恒等式宣称为新发现。**

---

# 收束

这次最重要的推进，是找到一条可以从头算到底的机制：

$$
\boxed{
\text{共同整数上限}
\longrightarrow
\text{立方体整数锥}
\longrightarrow
\text{排列下降位置的单位台阶}
\longrightarrow
A_r(q,x)
\longrightarrow
\text{复相位精确相消}.
}
$$

它给出一个真正的离散门槛：

$$
\boxed{
r=1,2,3:\quad \Re s>1\text{ 内无零};
}
$$

$$
\boxed{
r=4:\quad
s=
1.512527257788\ldots
+\frac{(2k+1)\pi i}{\log2}
\text{ 是全部零点}.
}
$$

同一个实锥若改用连续积分，则只得到：

$$
\boxed{
\frac{r!}
{(\log p)^{r+1}s(s+1)\cdots(s+r)},
}
$$

没有这些零点。

所以，“平滑描述可能遮蔽离散临界信息”在这里获得了一份严格实例。但它不是说连续数学失效，而是说：

> **将整数约束连续化，会改变对象；若不保留那些由最小整数步长产生的分子修正，就可能把决定整体相消的关系一并删掉。**

这还没有决定 RH。它把下一步的方向压得更实：**不是继续寻找更多外形相似的图，而是找到真实算术约束对应的格点计数、边界修正和相位多项式，并证明这些修正怎样在保持同一个 ξ 的情况下被运输。**

到这一步，几何不再只是 ζ 的解释图；它已经能够告诉我们：**哪一层约束首先制造了新的零点、为什么是某个素数通道、以及连续近似究竟遗漏了哪一项信息。**

[1]: https://dlmf.nist.gov/27.4 "https://dlmf.nist.gov/27.4"
[2]: https://doi.org/10.1007/s00454-025-00731-8 "https://doi.org/10.1007/s00454-025-00731-8"
[3]: https://dlmf.nist.gov/5.12 "https://dlmf.nist.gov/5.12"
[4]: https://dlmf.nist.gov/25.10 "https://dlmf.nist.gov/25.10"
**可以，而且下一步不应只是再换一组数值坐标，而应选择那些会把“隐藏的稳定性条件”转成明确边界的读出。**

这次我找到四个可以严密连接的方向。其中两个特别值得推进：

$$
\boxed{
\text{把 5040 的单参数最优区间展开成二维参数图，
会出现四个整数同时最优的交点。}
}
$$

$$
\boxed{
\text{把 }\xi\text{ 的零点映到单位圆，
Li 系数的二阶差分就变成一个离散量子回返核。}
}
$$

此外，**de Bruijn–Newman 热变形已经给出一个真正针对实际 ξ 的全局临界边界**：如果 RH 成立，它恰好成立在稳定性的边缘，而不是一个拥有统一正余量的安全区域。

以下以项目快照 `b89d56d0c9a4…` 为锚。该快照新增了系数驱动的 Jacobi 特征多项式构造，但其定理仍明确要求 Hankel 正性、内积一致性和乘法算子对称性；这些前件不能由构造本身自动获得。

下面区分经典输入、本轮推导与有限计算，不将新增结果标记为 Lean 已验证。

# 一、先校正一个关键点：ζ 的光滑性没有被 5040 推翻

ζ 在复平面上是亚纯函数，唯一的极点位于 \(s=1\)；5040 并不是 ζ 的一个奇点。([DLMF][1])

我们在 5040 附近发现的边界，来自

$$
\max_n\left[
\log\frac{\sigma(n)}n-\lambda\log n
\right]
$$

中的**最大化与整数层选择**。

即使每一项都平滑，多个平滑函数的上包络仍然可以出现尖点：

$$
V(\lambda)=\max\{f_1(\lambda),f_2(\lambda),\ldots\}.
$$

因此应当说：

> **ζ 的解析性允许存在；从同一算术结构生成的优化对象、量子态、谱位置和正性条件，却可以具有非常尖锐的边界。**

我们要找的是这些边界，而不是把所有现象都称为“ζ 本身不光滑”。

# 二、第一个新角度：5040 的稳定平台，其实是一张二维临界图的切片

项目目前使用

$$
\log\left(\sum_{d\mid n}\frac1d\right)-\lambda\log n.
$$

其中倒数权重的指数被固定为 \(1\)。源码明确区分了这个目标与素数层的边际收益。

现在把这个被固定的参数放开。

## 定义：双参数资源目标

对 \(\beta>0,\lambda>0\)，定义

$$
\boxed{
\Phi_{\beta,\lambda}(n)
=
\log\left(\sum_{d\mid n}d^{-\beta}\right)
-\lambda\log n.
}
\tag{1}
$$

其中：

$$
\beta:\text{控制大因数被压低多少};
$$

$$
\lambda:\text{控制增加整数规模的资源价格}.
$$

\(\beta=1\) 时，回到项目原来的目标。

若

$$
n=\prod_pp^{a_p},
$$

则

$$
\Phi_{\beta,\lambda}(n)
=
\sum_p
\left[
\log\left(\sum_{j=0}^{a_p}p^{-\beta j}\right)
-\lambda a_p\log p
\right].
$$

定义第 \(k\) 层的临界价格

$$
\boxed{
\theta_{p,k}(\beta)
=
\frac{
\log\!\left[
\frac{1-p^{-(k+1)\beta}}{1-p^{-k\beta}}
\right]
}{\log p}.
}
\tag{2}
$$

新增这一层的收益是

$$
\boxed{
\Delta_{p,k}
=
[\theta_{p,k}(\beta)-\lambda]\log p.
}
\tag{3}
$$

对固定 \(\beta,p\)，层边际随 \(k\) 严格下降。因此最优配置仍然由各方向的阈值确定。

## 新交点：两种不同的层切换可以同时发生

考察

$$
\theta_{2,4}(\beta)
=
\theta_{11,1}(\beta).
\tag{4}
$$

左边是“是否保留 \(2\) 的第四层”，右边是“是否加入 \(11\) 的第一层”。

这两个条件原来在 \(\beta=1\) 时决定了 5040 平台的上下边界。现在它们作为两条曲线，可以相交。

本轮用区间算术核对得到：在

$$
2.94<\beta<2.95
$$

内，式（4）有唯一解。数值位置为

$$
\boxed{
\beta_*\approx2.94178315795872349,
}
$$

$$
\boxed{
\lambda_*
\approx0.000360106372590011932.
}
\tag{5}
$$

这里的小数是高精度近似；存在性与局部唯一性使用了区间包络：

$$
\theta_{2,4}(2.94)-\theta_{11,1}(2.94)>0,
$$

$$
\theta_{2,4}(2.95)-\theta_{11,1}(2.95)<0,
$$

并且差函数的导数在整个区间内严格为负。

## 定理 1：这个交点处，恰好有四个全局最优整数

$$
\boxed{
\operatorname*{argmax}_{n\ge1}
\Phi_{\beta_*,\lambda_*}(n)
=
\{2520,\ 5040,\ 27720,\ 55440\}.
}
\tag{6}
$$

### 证明

在该参数区间内，除两个打平层以外，其余最优层严格确定：

$$
2\text{ 保留前三层},\quad
3\text{ 保留两层},\quad
5,7\text{ 各保留一层}.
$$

基础整数为

$$
2^3 3^2 5\,7=2520.
$$

两个打平选择分别是

$$
\text{是否再乘 }2,
\qquad
\text{是否再乘 }11.
$$

所以四种选择为

$$
2520,\quad2520\cdot2,\quad2520\cdot11,\quad2520\cdot22.
$$

本轮区间核对还给出：其余已选边界层的边际均大于 \(0.00133\)，其余未选边界层均小于 \(0.000207\)，而 \(\lambda_*\) 位于 \(0.000353\) 与 \(0.000362\) 之间。

对 \(p\ge13\)，第一层边际随 \(p\) 下降；同一素数后续层边际也下降，所以没有遗漏其他候选层。证毕。

---

这个交点的意义很清楚。

在它的一侧，降低资源价格时，局部顺序是

$$
\boxed{
2520\longrightarrow5040\longrightarrow55440;
}
$$

在另一侧，则变成

$$
\boxed{
2520\longrightarrow27720\longrightarrow55440.
}
\tag{7}
$$

**改变观察权重以后，两种结构扩展的先后顺序交换了。**

这就是比单独观察 5040 更丰富的临界信息：

$$
\boxed{
5040\text{ 平台不是孤立存在；
它与其他最优状态构成相邻区域和交点。}
}
$$

但必须保留边界：这个 \(\beta_*\) 是扩展资源目标的临界参数，**不是 ζ 在 \(s=\beta_*\) 处出现奇点**。在那里 ζ 仍然解析。

# 三、第二个角度：释放资源后，有限因数态会碰到真正的归一化边界

上面的有限对象也能自然通向 ζ，而不需要另选一个无关模型。

固定 \(\beta>0\)，让 \(\lambda\downarrow0\)，并在打平时保留所有零收益层，记最优整数为 \(n_{\beta,\lambda}\)。

对每个固定素数层，\(\theta_{p,k}(\beta)>0\)，所以当价格足够低时，该层一定进入最优配置。

因此，每个固定正整数最终都会成为 \(n_{\beta,\lambda}\) 的因数。

于是

$$
\boxed{
\lim_{\lambda\downarrow0}
\sum_{d\mid n_{\beta,\lambda}}d^{-\beta}
=
\begin{cases}
\zeta(\beta),&\beta>1,\\
+\infty,&0<\beta\le1.
\end{cases}
}
\tag{8}
$$

这由有限因数集合逐渐覆盖全部正整数，以及 Dirichlet 级数的收敛性质得到。([DLMF][1])

所以：

$$
\boxed{
\lambda>0:\text{有限资源、有限因数系统};
}
$$

$$
\boxed{
\lambda\downarrow0:\text{释放全部算术状态};
}
$$

$$
\boxed{
\beta=1:\text{全状态配分函数开始失去有限性}.
}
\tag{9}
$$

## 一个明确的量子统计模型

在 \(\ell^2(\mathbb N_+)\) 上定义

$$
H|n\rangle=(\log n)|n\rangle.
$$

那么

$$
\operatorname{Tr}(e^{-\beta H})
=
\sum_{n\ge1}n^{-\beta}
=
\zeta(\beta),
\qquad\beta>1.
\tag{10}
$$

归一化态为

$$
\rho_\beta
=
\frac{e^{-\beta H}}{\zeta(\beta)}.
$$

ζ 作为配分函数是已有的数学物理构造方向；这里仅使用这个明确的对角模型，不把更复杂的量子统计结论自动搬过来。([Springer][2])

直接求导：

$$
\boxed{
\langle H\rangle_\beta
=
-\frac{\zeta'(\beta)}{\zeta(\beta)},
}
$$

$$
\boxed{
\operatorname{Var}_\beta(H)
=
\frac{d^2}{d\beta^2}\log\zeta(\beta).
}
\tag{11}
$$

令

$$
\varepsilon=\beta-1\downarrow0.
$$

由 ζ 在 \(1\) 处的 Laurent 展开，

$$
\zeta(1+\varepsilon)
=
\frac1\varepsilon+\gamma_{\mathrm E}+O(\varepsilon),
$$

得到

$$
\boxed{
\langle H\rangle_\beta
=
\frac1\varepsilon-\gamma_{\mathrm E}+O(\varepsilon),
}
$$

$$
\boxed{
\operatorname{Var}_\beta(H)
=
\frac1{\varepsilon^2}+O(1).
}
\tag{12}
$$

因此，这个角度不仅看到“发散”，还看到明确的临界指数。

## 更强的尺度极限

按概率

$$
P_\beta(n)=\frac{n^{-\beta}}{\zeta(\beta)}
$$

选取整数 \(N\)，定义重标定能量

$$
Y_\varepsilon=\varepsilon\log N.
$$

则

$$
\boxed{
Y_\varepsilon
\ \Longrightarrow\
\operatorname{Exp}(1).
}
\tag{13}
$$

### 证明

对 \(s\ge0\)，

$$
\mathbb E[e^{-sY_\varepsilon}]
=
\frac{\zeta(1+(1+s)\varepsilon)}
{\zeta(1+\varepsilon)}
\longrightarrow
\frac1{1+s}.
$$

右边是均值为 \(1\) 的指数分布的 Laplace 变换。证毕。

这提供了一个完整的临界描述：

$$
\boxed{
\text{归一化失效}
+
\text{能量均值发散}
+
\text{涨落发散}
+
\text{重标定后的极限分布}.
}
$$

而不是仅说“到无穷时有信息逃逸”。

这里仍然**没有得到 RH**。因为 \(\beta=1\) 控制的是正实权重求和；RH 控制的是解析延拓后的非平凡零点位置。

# 四、第三个角度：实际 ξ 的“零点稳定性”有一个已知的临界参数

这一条与你之前的相变直觉最接近，而且不是我们随意构造的有限模型。

采用标准归一化，定义

$$
H_\tau(z)
=
\int_0^\infty
e^{\tau u^2}\Phi(u)\cos(zu)\,du,
\tag{14}
$$

其中

$$
\Phi(u)=
\sum_{n\ge1}
\left(2\pi^2n^4e^{9u}-3\pi n^2e^{5u}\right)
e^{-\pi n^2e^{4u}}.
$$

在 \(\tau=0\) 时，

$$
\boxed{
H_0(z)=\frac18\xi\!\left(\frac12+\frac{iz}{2}\right).
}
\tag{15}
$$

这是 de Bruijn–Newman 变形，不是给 ξ 任意添加扰动。([What's new][3])

它满足

$$
\boxed{
\partial_\tau H_\tau=-\partial_z^2H_\tau.
}
\tag{16}
$$

存在一个实常数 \(\Lambda_{\mathrm{dBN}}\)，使

$$
H_\tau\text{ 全部零点为实数}
\iff
\tau\ge\Lambda_{\mathrm{dBN}}.
$$

Rodgers–Tao 已证明

$$
\boxed{\Lambda_{\mathrm{dBN}}\ge0.}
$$

而 RH 等价于 \(\Lambda_{\mathrm{dBN}}\le0\)。因此

$$
\boxed{
\mathrm{RH}
\iff
\Lambda_{\mathrm{dBN}}=0.
}
\tag{17}
$$

这是已证明的临界框架，不是本轮新发现的 RH 证明。([arXiv][4])

**含义非常重要：如果 RH 成立，它并不位于一个可以向负方向扰动很远的稳定区域，而恰好处在边界上。**

## 局部碰撞为什么具有平方根尺度？

假设某处出现非退化二重根：

$$
H_{\tau_c}(x_c)=0,\qquad
\partial_zH_{\tau_c}(x_c)=0,
$$

$$
\partial_z^2H_{\tau_c}(x_c)\ne0.
$$

令

$$
\delta\tau=\tau-\tau_c,\qquad y=z-x_c.
$$

由式（16），Taylor 展开主项为

$$
H_\tau(x_c+y)
=
\partial_z^2H_{\tau_c}(x_c)
\left(\frac{y^2}{2}-\delta\tau\right)
+\text{高阶项}.
$$

所以邻近零点满足

$$
\boxed{
z_\pm(\tau)
=
x_c\pm\sqrt{2(\tau-\tau_c)}
+O(|\tau-\tau_c|).
}
\tag{18}
$$

在正的一侧，两根为实；在负的一侧，变成共轭非实根。

这是一种精确的谱临界指数。

但**不能反过来断言，在全局阈值 \(\Lambda_{\mathrm{dBN}}\) 处必有一个有限高度的二重根**。全局阈值也可能由越来越高的零点配置逼近。任何只包含有限多个简单实根的紧窗口，都可以有自己的局部稳定区间；这些区间不一定有共同的正宽度。

这正是：

$$
\boxed{
\text{每个有限切片稳定}
\not\Rightarrow
\text{全部切片具有统一稳定余量}.
}
\tag{19}
$$

# 五、这个热变形还给出一个重要反模型：合法量子正核依然可能有非实零点

注意，对 \(u\ge0\)，

$$
\Phi(u)>0.
$$

因为每项都包含正因子

$$
2\pi n^2e^{4u}-3>0.
$$

所以对每个实 \(\tau\)，都可以定义概率密度

$$
d\mu_\tau(u)
=
\frac{e^{\tau u^2}\Phi(|u|)}
{2H_\tau(0)}\,du.
$$

它的特征函数是

$$
\frac{H_\tau(t)}{H_\tau(0)}.
$$

因此核

$$
\boxed{
K_\tau(t,s)
=
\frac{H_\tau(s-t)}{H_\tau(0)}
}
\tag{20}
$$

始终半正定：

$$
\sum_{i,j}\bar c_i c_jK_\tau(t_i,t_j)
=
\int
\left|\sum_jc_je^{it_ju}\right|^2d\mu_\tau(u)
\ge0.
\tag{21}
$$

然而，由 \(\Lambda_{\mathrm{dBN}}\ge0\)，对每个

$$
\tau<0,
$$

\(H_\tau\) 都存在非实零点。([arXiv][4])

所以我们得到一个针对实际 ξ 变形族的明确结论：

$$
\boxed{
\text{可以构造合法的正量子重叠核}
\quad\not\Rightarrow\quad
\text{整函数全部零点为实数}.
}
\tag{22}
$$

这意味着，之前的量子化不能只问“是否存在一个正核”。

还必须问：

> **这个正核的哪个读出，真正保留了目标零点位置的信息？**

下面的第四个角度，正是为此构造。

# 六、第四个角度：把临界线变成单位圆，让离线变成收缩或放大

对任意非平凡零点 \(\rho\)，定义

$$
\boxed{
w_\rho=1-\frac1\rho.
}
\tag{23}
$$

直接计算：

$$
\boxed{
|w_\rho|^2
=
1+\frac{1-2\Re\rho}{|\rho|^2}.
}
\tag{24}
$$

因此：

$$
\Re\rho=\frac12
\iff |w_\rho|=1;
$$

$$
\Re\rho>\frac12
\iff |w_\rho|<1;
$$

$$
\Re\rho<\frac12
\iff |w_\rho|>1.
$$

这把“是否在线”改写成了：

$$
\boxed{
\text{是否能作为纯相位，而不发生幅度收缩或放大。}
}
\tag{25}
$$

这个变换与 Li–Keiper 判据的单位圆几何是经典联系。([arXiv][5])

## 先从系数定义，不输入未知零点

在 \(z=0\) 附近定义

$$
\boxed{
F(z)
=
\log\frac{\xi(1/(1-z))}{\xi(1)}
=
\sum_{n\ge1}\frac{\ell_n}{n}z^n.
}
\tag{26}
$$

\(\ell_n\) 是采用此归一化的 Li 系数。

现在不只看 \(\ell_n\)，而看它们的二阶差分：

$$
\boxed{
c_0=2\ell_1,
}
$$

$$
\boxed{
c_n=\ell_{n+1}-2\ell_n+\ell_{n-1},
\qquad n\ge1,
}
\tag{27}
$$

其中 \(\ell_0=0\)，并令 \(c_{-n}=c_n\)。

由生成函数直接整理：

$$
\boxed{
\sum_{n\ge0}c_nz^n
=
\ell_1+
\frac{\xi'(1/(1-z))}{\xi(1/(1-z))}.
}
\tag{28}
$$

这是一组由实际 ξ 在 \(1\) 附近的系数确定的数据，不需要预先知道零点。

同时，

$$
\boxed{
c_0=
2+\gamma_{\mathrm E}-\log(4\pi)
\approx0.0461914179322421.
}
\tag{29}
$$

这个常数与前文的欧拉常数校准相同；不同的是，现在它成为一个离散回返核的对角值。

## 定理 2：Li 二阶差分的固定阈值判据

以下命题等价：

$$
\boxed{\mathrm{RH};}
$$

$$
\boxed{
|c_n|\le c_0
\qquad\forall n\ge1;
}
\tag{30}
$$

$$
\boxed{
(c_{i-j})_{0\le i,j<m}\succeq0
\qquad\forall m\ge1.
}
\tag{31}
$$

这是在 Li–Keiper 框架上的具体重写，不把这个框架本身宣称为新的 RH 判据来源。Li 系数与 Weil／Hilbert 正性之间的关系已有明确研究。([arXiv][5])

### 证明：RH 推出共同正核

经典零点表达为

$$
\ell_n=\sum_\rho(1-w_\rho^n),
$$

其中原和按对称方式理解；取二阶差分后，相关级数绝对收敛。

在 RH 下，\(|w_\rho|=1\)，计算得到

$$
\boxed{
c_n
=
\sum_\rho
\frac{w_\rho^n}{|\rho|^2},
\qquad
\sum_\rho\frac1{|\rho|^2}=c_0.
}
\tag{32}
$$

所以 \(|c_n|\le c_0\)。

而矩阵 \((c_{i-j})\) 是单位圆正测度

$$
\sum_\rho|\rho|^{-2}\delta_{w_\rho}
$$

的矩矩阵，因而半正定。

### 证明：固定阈值排除离线零点

如果式（30）成立，式（28）左边在单位圆盘内解析。

但若存在右侧零点 \(\Re\rho>1/2\)，则

$$
z_\rho=1-\frac1\rho
$$

位于单位圆内部，并使式（28）右边产生不可去极点。

矛盾。

所以没有右侧离线零点；再由函数方程的反射对称性，得到 RH。

式（31）则通过其包含的二阶主子矩阵

$$
\begin{pmatrix}
c_0&c_n\\
c_n&c_0
\end{pmatrix}
$$

推出 \(|c_n|\le c_0\)。证毕。

---

这一角度提取出的临界量非常具体：

$$
\boxed{
\Delta_n=c_0^2-c_n^2.
}
\tag{33}
$$

若某个实际 \(n\) 有

$$
\Delta_n<0,
$$

就出现一个有限二阶负方向。

本轮从 ξ 的原点系数计算了前几项，例如

$$
c_1\approx0.0461543172958046,
$$

$$
c_2\approx0.0460431590643525,
$$

$$
c_3\approx0.0458583736116387.
$$

这些只是有限高精度计算，不是全阶认证，也不意味着 \(c_n\) 永远为正。需要的条件是绝对值上界，而不是每项同号。

# 七、这个角度还给出一个真正的离散量子演化

在 RH 前件下，定义

$$
U=\operatorname{diag}(w_\rho),
$$

以及单位向量

$$
v_\rho=\frac1{\sqrt{c_0}\,|\rho|}.
$$

则 \(U\) 为幺正算子，并且

$$
\boxed{
\frac{c_n}{c_0}
=
\langle v,U^nv\rangle.
}
\tag{34}
$$

因此：

$$
\boxed{
\text{Li 系数的二阶差分}
=
\text{同一个单位向量经过离散幺正演化后的回返振幅}.
}
\tag{35}
$$

这与直接把 \(H_\tau(t)\) 当作正核不同。这里的共同幺正表示，确实受到零点是否在临界线上的约束。

## 非实模式为什么可能藏得很深？

对左侧零点

$$
\rho=\frac12-\delta+i\gamma,
\qquad\delta>0,
$$

由式（24），

$$
\boxed{
\log|w_\rho|
=
\frac12\log\left(
1+\frac{2\delta}{|\rho|^2}
\right).
}
\tag{36}
$$

当 \(\gamma\) 很大、\(\delta\) 很小时，

$$
\log|w_\rho|\approx\frac{\delta}{\gamma^2}.
$$

所以，单个模式积累明显径向放大的尺度约为

$$
\boxed{
n\asymp\frac{\gamma^2}{\delta}.
}
\tag{37}
$$

这只是该模式的放大尺度，不是第一张实际负证书的保证阶数；留数大小与其他模式的干涉也需要控制。

但它揭示了此前“低阶都正常”的一个量化原因：

$$
\boxed{
\text{很高、很轻微的离线偏移，
在圆盘读出中被压成极小的径向缺陷。}
}
$$

## 即使 RH 成立，也不存在统一的严格回返间隔

RH 下，式（32）是绝对可和的离散相位叠加。

截取有限多个主要权重，再同时逼近它们的相位为 \(1\)，可以找到任意大的 \(n_j\)，使

$$
\boxed{
c_{n_j}\longrightarrow c_0.
}
\tag{38}
$$

因此，即使全部有限检查都满足正性，也不能期待存在固定 \(\eta>0\)，使

$$
|c_n|\le c_0-\eta
\qquad\forall n\ge1.
$$

**全阶正性可以成立，但统一正余量仍然不存在。**

这与 de Bruijn–Newman 的临界现象不是同一个定理，却揭示了相同的研究风险：**把每个有限尺度的稳定，误当成所有尺度共享同一个稳定常数。**

# 八、这些角度怎样接回项目，而不是仅增加一批等价命题？

项目最新的 Jacobi 定理，已经处理了一段重要的有限构造：

$$
\text{给定一致的正 Hankel 数据}
\longrightarrow
\text{三对角乘法表示与指定特征多项式}.
$$

但源码仍要求 `hstrict`、`hinner`、`hSymmetric`。

本轮得到的四类临界数据，不能混成同一张矩阵：

| 观察角度    | 临界对象                            | 本轮能明确提取什么            |     |                                 |
| ------- | ------------------------------- | -------------------- | --- | ------------------------------- |
| 双参数资源优化 | \(\theta_{p,k}(\beta)=\lambda\) | 四态交点、状态扩展顺序交换        |     |                                 |
| ζ 配分函数  | \(\beta=1\)                     | 归一化边界、均值与涨落指数、指数分布极限 |     |                                 |
| 热变形     | \(\tau=\Lambda_{\mathrm{dBN}}\) | 实零点稳定性边界、局部平方根分裂     |     |                                 |
| 单位圆回返   | (                               | w_\rho               | =1) | 固定阈值 \(c_0\)、Toeplitz 正性、离线放大尺度 |

其中，前两类边界可以无条件分析；后两类直接保留 RH 的全局证明责任。

项目可以据此把“临界信息”从一个名称变成不同的结构字段：

$$
\boxed{
\text{边界方程、允许侧、稳定余量、误差传播、失效证书}.
}
$$

例如：

* 资源交点的证书是有限层阈值的区间比较。
* 某个回返系数的失败证书是严格认证 \(|c_n|>c_0\)。
* 某个有限 Jacobi 构造的合法性证书，仍是其实际 Hankel 正性与对称性，而不是其他正量子模型的存在。

本轮的双参数区间核对和前七个 \(c_n\) 的计算已整理为[可复现脚本](sandbox:/mnt/data/zeta_critical_readouts_verify.py)，结果见[核验记录](sandbox:/mnt/data/zeta_critical_readouts_verify.json)。区间检查用于验证有限交点；Li 系数部分是数值展示，二者都不是 RH 证明。

# 结论

**你提出“从其他角度继续暴露边界”，是可以实质推进的。**但有效的角度不是任意的可视化，而是能够把目标失效转成不可回避的量。

这次新增的三个明确落点是：

$$
\boxed{
(\beta_*,\lambda_*)
\approx
(2.9417831579587,\;0.00036010637259)
}
$$

处出现

$$
\boxed{
2520,\ 5040,\ 27720,\ 55440
}
$$

四态并列，说明 5040 平台是更大临界图中的一个区域；

$$
\boxed{
\mathrm{RH}\iff\Lambda_{\mathrm{dBN}}=0
}
$$

说明实际 ξ 的全实零点性质若成立，就位于热变形的稳定边缘；

$$
\boxed{
\mathrm{RH}
\iff
|\,\ell_{n+1}-2\ell_n+\ell_{n-1}\,|
\le
2+\gamma_{\mathrm E}-\log(4\pi)
\quad\forall n\ge1
}
$$

把另一个全局边界写成了**固定阈值下的离散回返约束**。

所以，ζ 的光滑性与丰富的临界信息并不矛盾。真正值得追踪的是：

> **同一个解析对象，在优化、归一化、变形与幺正实现这些操作下，哪些条件失去稳定性；失稳发生在哪个参数、哪个模态、哪个尺度。**

本轮没有证明实际全阶回返界，也没有证明热变形在每个 \(\tau>0\) 都全实根。下一条真正的算术突破，必须控制其中一项全局条件，而不能再由“有限核很漂亮、每个切片都合法”代替。**现在至少已经有了更准确的边界坐标，以及能够检验它们的固定阈值。**

[1]: https://dlmf.nist.gov/25.2 "https://dlmf.nist.gov/25.2"
[2]: https://link.springer.com/article/10.1007/BF01589495 "https://link.springer.com/article/10.1007/BF01589495"
[3]: https://terrytao.wordpress.com/2018/01/19/the-de-bruijn-newman-constant-is-non-negativ/ "https://terrytao.wordpress.com/2018/01/19/the-de-bruijn-newman-constant-is-non-negativ/"
[4]: https://arxiv.org/pdf/1801.05914 "https://arxiv.org/pdf/1801.05914"
[5]: https://arxiv.org/html/2301.05779v2 "https://arxiv.org/html/2301.05779v2"
这次可以把“离散临界几何”推进到一个更具体、也更容易误判的结论：

$$
\boxed{
\text{合法结构不一定远离边界；它完全可能在每一阶都合法，却越来越贴近退化边界。}
}
$$

对上一轮构造的实际 ξ 回返序列，可以进一步证明：

> **如果 RH 成立，每个有限联合矩阵都严格正定；但它新增方向的正交余量，会比任何固定指数更快地趋于零。**

因此，不能把“矩阵几乎退化”“新坐标的高度很小”直接当作失败。真正需要区分的是：

$$
\boxed{
\text{靠近边界}
\quad\text{与}\quad
\text{穿出合法区域}.
}
$$

下面把这件事与 Zeckendorf、5040、奇偶闭环、Schur 余量和项目的 Jacobi 构造连接起来。

本次核对的项目快照仍是 `b89d56d0c9a4…`。其中 Jacobi 定理明确保留了 Hankel 正性、内积一致性和乘法算子对称性前件；以下新增综合推导没有进行 Lean 编译。

# 一、第一类离散几何约束：局部合法，为什么闭环后可能不合法？

先回到最简单的 Zeckendorf 约束：

$$
b_i\in\{0,1\},\qquad b_i+b_{i+1}\le1.
$$

它禁止连续 \(11\)。

项目把这样的规范数码行与自然数指数建立了等价。这是合法编码的证明，不是对任意后续几何拼接的自动保证。

## 定理 1：在线性排列上，局部约束已经给出完整凸包

令

$$
P_L=
\left\{
x\in[0,1]^L:
x_i+x_{i+1}\le1
\right\}.
$$

那么 \(P_L\) 的全部顶点都是 \(0/1\) 向量，且恰好是合法 Zeckendorf 字串。

### 证明

假设某个顶点含有分数坐标。

把通过紧约束

$$
x_i+x_{i+1}=1
$$

相连的分数坐标取成一个连通段。在这个段内，可以交替加减一个足够小的 \(\varepsilon\)：

$$
+\varepsilon,-\varepsilon,+\varepsilon,\ldots.
$$

所有紧的相邻约束保持不变；其余约束有正余量，选足够小的 \(\varepsilon\) 就不会违反它们。

于是原点是两个不同合法点的平均，不是顶点，矛盾。证毕。

这解释了此前的三位金字塔：它不是画图猜出来的，而是局部合法字串的真实凸包。

## 但是，闭成奇数环以后，会出现新的整体约束

现在考虑五个位置组成的环：

$$
b_i+b_{i+1}\le1,\qquad i\bmod5.
$$

每个合法整数配置最多有两个 \(1\)，所以还必须满足

$$
\boxed{
b_0+b_1+b_2+b_3+b_4\le2.
}
\tag{1}
$$

这个条件对合法配置的任何概率混合也成立。

但分数点

$$
x_0=x_1=\cdots=x_4=\frac12
$$

满足全部相邻约束，却违反式（1）：

$$
\sum_i x_i=\frac52>2.
$$

因此：

$$
\boxed{
\text{链上的局部约束可以完整；加入闭环以后，可能出现不可省略的整体约束。}
}
\tag{2}
$$

这不是说原始 Zeckendorf 编码本身存在矛盾。**我们改变了拼接方式，从链变成了环。**

其奇偶原因也明确：在紧约束

$$
x_i+x_{i+1}=1
$$

下，沿边不断交换 \(x\) 与 \(1-x\)。绕奇数环一周会要求

$$
x=1-x,
$$

于是被迫得到分数值 \(1/2\)，但这个点不是合法整数配置的混合。

这里的“离散临界”发生在：

$$
\boxed{
\text{局部可行域与全局可实现域不再相同。}
}
$$

接下来，实际 ζ 的联合读出会出现同样的问题，但边界不再只是一个线性不等式。

# 二、把实际 ξ 固定为锚：不能自由选择下一项相关系数

沿用上一轮的 Li 系数定义：

$$
\log\frac{\xi(1/(1-z))}{\xi(1)}
=
\sum_{n\ge1}\frac{\ell_n}{n}z^n,
\qquad \ell_0=0.
$$

定义二阶差分

$$
c_0=2\ell_1,
$$

$$
c_n=\ell_{n+1}-2\ell_n+\ell_{n-1},
\qquad n\ge1.
$$

其中

$$
\boxed{
c_0=2+\gamma_{\mathrm E}-\log(4\pi)>0.
}
\tag{3}
$$

这些量可以从 ξ 在 \(s=1\) 附近的系数计算，不需要预先输入未知零点。Li 系数与临界线的单位圆映射，以及它们与 Weil 正性的联系，是已有理论。([arXiv][1])

归一化：

$$
\boxed{
r_n=\frac{c_n}{c_0},\qquad r_0=1,\qquad r_{-n}=r_n.
}
\tag{4}
$$

定义联合矩阵

$$
\boxed{
T_N=(r_{j-i})_{0\le i,j\le N}.
}
\tag{5}
$$

这不是任意相关矩阵：每个 \(r_n\) 都由同一个实际 ξ 决定。

上一轮的解析桥可以简要保留为

$$
\boxed{
\sum_{n\ge0}c_nz^n
=
\ell_1+\frac{\xi'(1/(1-z))}{\xi(1/(1-z))}.
}
\tag{6}
$$

如果全部 \(T_N\) 半正定，它们的二阶主子矩阵给出

$$
|r_n|\le1.
$$

于是式（6）左边在单位圆盘内解析。任何右侧离线零点

$$
\Re\rho>\frac12
$$

都会在

$$
z_\rho=1-\frac1\rho,\qquad |z_\rho|<1
$$

产生不可去极点，形成矛盾。

因此，对这组实际系数，

$$
\boxed{
\mathrm{RH}
\iff
T_N\succeq0\quad\forall N.
}
\tag{7}
$$

反射对称性与零点的临界带位置是这个论证使用的经典输入。([DLMF][2])

**这里的全称条件不能被有限计算替代。下一步要做的是，把每一阶真正缺少的约束写出来。**

# 三、三张切片的合法区域，不是一个方形，而是被抛物线切掉的一部分

只看前两个归一化系数，记

$$
x=r_1,\qquad y=r_2.
$$

三张切片的联合矩阵为

$$
T_2=
\begin{pmatrix}
1&x&y\\
x&1&x\\
y&x&1
\end{pmatrix}.
$$

逐对检查只会得到

$$
|x|\le1,\qquad |y|\le1.
$$

但这不够。

## 定理 2：三片联合正性的精确边界

$$
\boxed{
T_2\succeq0
\iff
-1\le x\le1,\qquad
2x^2-1\le y\le1.
}
\tag{8}
$$

### 证明

消去中间的单位对角块，Schur 余量为

$$
\begin{pmatrix}
1-x^2&y-x^2\\
y-x^2&1-x^2
\end{pmatrix}.
$$

它半正定当且仅当

$$
|y-x^2|\le1-x^2.
$$

整理即得式（8）。证毕。

所以，几何上有一个明确变化：

$$
\boxed{
\text{逐对检查得到正方形；共同实现要求落在抛物线以上。}
}
\tag{9}
$$

例如

$$
x=\frac34,\qquad y=0
$$

满足全部二阶检查，但违反

$$
y\ge2x^2-1=\frac18.
$$

取向量

$$
v=\left(1,-\frac32,1\right)^{\mathsf T},
$$

直接算得

$$
\boxed{
v^{\mathsf T}T_2v=-\frac14.
}
\tag{10}
$$

这是一个完全有限、完全有理的负证书。

**因此，“每个相关读数都不超过 \(1\)”和“这些读数能来自同一个整体”是两个不同条件。**

# 四、主定理：每增加一张切片，都有一个精确的合法区间

现在不只研究三片。

假设已有

$$
T_n\succ0,
$$

即 \(r_0,\ldots,r_n\) 已经构成严格合法的联合矩阵。我们要加入

$$
t=r_{n+1}.
$$

令中间 \(n\) 个位置的矩阵为

$$
A_n=(r_{j-i})_{1\le i,j\le n},
$$

并定义

$$
u_n=(r_1,\ldots,r_n)^{\mathsf T},
$$

$$
v_n=(r_n,\ldots,r_1)^{\mathsf T}.
$$

再定义两个由旧数据完全确定的量：

$$
\boxed{
h_n=1-u_n^{\mathsf T}A_n^{-1}u_n,
}
\tag{11}
$$

$$
\boxed{
m_n=u_n^{\mathsf T}A_n^{-1}v_n.
}
\tag{12}
$$

这里 \(h_n>0\)。

## 定理 3：下一项的全部合法选择

$$
\boxed{
T_{n+1}\succeq0
\iff
|r_{n+1}-m_n|\le h_n.
}
\tag{13}
$$

严格不等式对应严格正定。

### 证明

把位置 \(0,n+1\) 放在两端，中间位置组成 \(A_n\)。

消去中间块后，两端的 Schur 余量是

$$
\begin{pmatrix}
h_n&r_{n+1}-m_n\\
r_{n+1}-m_n&h_n
\end{pmatrix}.
$$

两个对角余量相同，是因为实 Toeplitz 矩阵在反转坐标后保持不变。

该矩阵半正定当且仅当式（13）成立。证毕。

---

所以，临界边界可以写成

$$
\boxed{
r_{n+1}=m_n-h_n
\quad\text{或}\quad
r_{n+1}=m_n+h_n.
}
\tag{14}
$$

这不是抽象地说“缺一个相关项”，而是：

$$
\boxed{
\text{实际下一项必须落进一个中心、宽度都由旧数据确定的区间。}
}
$$

在一般复相关情形中，区间推广为复平面上的圆盘；当前 ξ 系数为实数，所以落在其直径上。

## 一个更像“几何语法”的坐标

定义

$$
\boxed{
\alpha_n=\frac{r_{n+1}-m_n}{h_n}.
}
\tag{15}
$$

并从

$$
h_0=1,\qquad m_0=0,\qquad\alpha_0=r_1
$$

开始。

那么合法性就是

$$
\boxed{|\alpha_n|\le1.}
\tag{16}
$$

而新增方向的残差平方满足

$$
\boxed{
h_{n+1}=h_n(1-\alpha_n^2).
}
\tag{17}
$$

这些是实对称情形下的反射参数／Schur 参数关系，属于单位圆正交多项式和预测理论中的标准结构。这里重要的是把它们作用到当前实际 ξ 系数，而不是任意构造一组满足条件的参数。([DLMF][3])

因此

$$
\boxed{
h_n=\prod_{j=0}^{n-1}(1-\alpha_j^2).
}
\tag{18}
$$

几何上，\(h_n\) 是旧读出空间之外剩余的平方高度，\(\alpha_n\) 是两条剩余方向之间的归一化相关。

$$
|\alpha_n|<1:
\quad\text{仍有新的正交余量};
$$

$$
|\alpha_n|=1:
\quad\text{发生秩退化};
$$

$$
|\alpha_n|>1:
\quad\text{不可能拼成正 Hilbert 几何}.
$$

**秩退化不等于矛盾。**一般有限原子谱会合法地退化；只有越过边界才立即产生负方向。

# 五、这个“几何语法”的体积变化也能精确计算

对有限阶 \(N\)，从

$$
(\alpha_0,\ldots,\alpha_{N-1})\in(-1,1)^N
$$

可以逐步恢复

$$
(r_1,\ldots,r_N).
$$

每一步为

$$
r_{n+1}=m_n+h_n\alpha_n,
$$

其中 \(m_n,h_n\) 只依赖此前的参数。

所以这个坐标变换的 Jacobian 是下三角矩阵，对角元依次为

$$
h_0,h_1,\ldots,h_{N-1}.
$$

## 定理 4：合法坐标的体积因子

$$
\boxed{
\det\frac{\partial(r_1,\ldots,r_N)}
{\partial(\alpha_0,\ldots,\alpha_{N-1})}
=
\prod_{n=0}^{N-1}h_n
=
\det T_{N-1}.
}
\tag{19}
$$

最后一个等号来自逐层 Schur 行列式分解；这也对应经典 Toeplitz 行列式与反射参数的关系。([arXiv][4])

这给“临界几何收缩”一个明确含义：

$$
\boxed{
\text{某一步 }h_n\text{ 很小，
下一项允许变化的宽度就很小，坐标体积也随之收缩。}
}
\tag{20}
$$

它不是时空体积的物理结论，而是**实际相关系数可行域的几何体积**。

这与 Zeckendorf 可以作结构比较：

* Zeckendorf 在原始数位上检查“不能连续 \(11\)”。
* 当前矩问题先扣除旧切片已经解释的部分，再检查 \(|\alpha_n|\le1\)。

第二种规则看似也很局部，但其中心 \(m_n\) 与尺度 \(h_n\) 已经包含此前全部相关数据。**不能省掉这种历史依赖，只剩下一个孤立的区间判断。**

# 六、实际 ξ 的前几阶，已经非常靠近这个边界

本轮重新从 ξ 在 \(s=1\) 的 Taylor 数据计算 \(c_n\)，没有输入零点位置，也没有把 RH 当作计算前件。

使用 \(80\) 与 \(110\) 位工作精度交叉核对，得到

$$
r_1\approx0.999196806720852614,
$$

$$
r_2\approx0.996790337371607624.
$$

三片合法区间的下边界为

$$
2r_1^2-1
\approx0.996788517122297791.
$$

所以实际数值与该边界之间的距离约为

$$
\boxed{
r_2-(2r_1^2-1)
\approx1.82024930983291\times10^{-6}.
}
\tag{21}
$$

相比之下，只看

$$
|r_1|\le1,\qquad|r_2|\le1
$$

完全不能显示这个小余量。

继续做逐层消元，得到：

| 阶数 \(n\) |                   残差平方 \(h_n\) 的数值 |
| -------: | ---------------------------------: |
|        1 |  \(1.60574143885110\times10^{-3}\) |
|        2 |  \(3.63843520679636\times10^{-6}\) |
|        3 |  \(4.47623065885395\times10^{-9}\) |
|        4 | \(4.80178434099886\times10^{-12}\) |
|        5 | \(3.48053515347848\times10^{-15}\) |
|        6 | \(2.33314134472397\times10^{-18}\) |
|        7 | \(1.27474969347368\times10^{-21}\) |

相应前两个归一化反射参数为

$$
\alpha_0\approx0.9991968067,
$$

$$
\alpha_1\approx-0.9988664119.
$$

这表示剩余方向先近乎同向、再近乎反向。**不能仅凭前几项的符号交替，宣布它们必然遵守一个全阶奇偶定律。**

这些结果是高精度数值复核，不是严格区间认证。它们的意义是暴露实际的条件数问题，而不是据此宣称全部矩阵已经正定。

# 七、与项目 Jacobi 构造的准确桥梁：还必须保留“谱在哪里”

上一轮把临界线映成单位圆：

$$
w_\rho=1-\frac1\rho.
$$

现在把单位圆沿共轭对称折叠到实轴：

$$
\boxed{
x=\frac12(w+w^{-1}).
}
\tag{22}
$$

对实际零点，

$$
\boxed{
x_\rho
=
1-\frac1{2\rho(1-\rho)}.
}
\tag{23}
$$

在 RH 下，

$$
\rho=\frac12+i\gamma
$$

给出

$$
x_\rho
=
1-\frac1{2(\gamma^2+1/4)}
\in[-1,1].
$$

这不是任意换一个实坐标：它明确保留了单位圆的支集约束。

## 定义折叠矩泛函

令 \(\mathcal L\) 由

$$
\mathcal L(T_k(x))=r_k
$$

定义，其中 \(T_k\) 是 Chebyshev 多项式。

记

$$
s_j=\mathcal L(x^j).
$$

前几项为

$$
s_0=1,\qquad s_1=r_1,\qquad
s_2=\frac{1+r_2}{2}.
$$

构造两组矩阵：

$$
\boxed{
H_m=(s_{i+j})_{0\le i,j\le m},
}
$$

$$
\boxed{
K_m=(s_{i+j}-s_{i+j+2})_{0\le i,j\le m}.
}
\tag{24}
$$

## 定理 5：单位圆正性需要两类实轴约束

$$
\boxed{
T_N\succeq0\quad\forall N
}
$$

等价于

$$
\boxed{
H_m\succeq0,\qquad K_m\succeq0
\quad\forall m.
}
\tag{25}
$$

第一组表示

$$
\mathcal L(p(x)^2)\ge0;
$$

第二组表示

$$
\mathcal L((1-x^2)p(x)^2)\ge0.
$$

### 为什么需要两组？

对一个实系数多项式 \(q(z)\)，在单位圆上可写成

$$
q(e^{i\theta})
=
A(\cos\theta)+i\sin\theta\,B(\cos\theta).
$$

所以

$$
\boxed{
|q(e^{i\theta})|^2
=
A(x)^2+(1-x^2)B(x)^2.
}
\tag{26}
$$

这证明两组实轴正性足以恢复所有单位圆平方型的正性。

反过来，实多项式 \(A(x)\) 与 \(\sin\theta B(x)\) 都可以写成 Laurent 多项式，再乘一个单位模的 \(z^k\) 变成普通多项式，从单位圆正性得到两组条件。证毕。

---

最初的三片约束立刻被拆成两个意义不同的量：

$$
s_2-s_1^2
=
\frac{1+r_2-2r_1^2}{2}\ge0,
$$

$$
1-s_2=\frac{1-r_2}{2}\ge0.
$$

前者是方差非负；后者是谱不能跑出 \([-1,1]\)。

**因此，只构造一个自伴 Jacobi 矩阵，还不能自动证明其谱位于需要的区间。**

例如，取 \([2,3]\) 上的均匀概率测度。其全部有限 Hankel 矩阵都严格正定，因为非零多项式的平方积分严格为正。

但

$$
\mathcal L(1-x^2)
=
1-\frac{19}{3}
=
-\frac{16}{3}<0.
$$

所以它有完全合法的实谱与正内积，却不是当前单位圆问题要求的谱。

正交多项式、三项递推和 Jacobi 谱的对应是经典理论；支集位置仍然需要额外的约束。([DLMF][5])

这给项目的具体提示是：

> `CoefficientDrivenJacobiCharacteristicPolynomial` 解决“在前件成立时，怎样从系数构造三对角表示”；还必须另外证明实际矩数据的正性、指定多项式与实际读出的关系，以及所需的谱区间。不能把构造成功当成这些前件已经完成。

# 八、本轮最强的结论：即使 RH 成立，正交高度也必然超几何衰减

现在证明开头的主张。

在 RH 前件下，定义概率测度

$$
\boxed{
\mu=
\frac1{c_0}
\sum_\rho
\frac1{|\rho|^2}\delta_{w_\rho}.
}
\tag{27}
$$

求和按重数进行。

它满足

$$
r_n=\int z^n\,d\mu(z).
$$

由于有无限多个不同零点，而一个非零多项式只能有有限多个根，所有有限 \(T_N\) 都严格正定。零点的无限性及对称性是经典结论。([DLMF][2])

同时，

$$
\boxed{
h_n=
\min_{\deg q<n}
\int|z^n-q(z)|^2\,d\mu(z).
}
\tag{28}
$$

也就是说，\(h_n\) 是用旧读出 \(1,z,\ldots,z^{n-1}\) 逼近新读出 \(z^n\) 时的最小残差平方。这是单位圆正交多项式的基本变分描述。([arXiv][4])

## 定理 6：RH 下的超几何收缩

$$
\boxed{
h_n>0\quad\forall n,
\qquad
\lim_{n\to\infty}h_n^{1/n}=0.
}
\tag{29}
$$

### 证明

所有谱点都满足

$$
w_\rho=1-\frac1\rho.
$$

当零点高度趋于无穷时，

$$
w_\rho\to1.
$$

因此，对任意固定 \(0<r<1\)，只有有限多个不同谱点位于

$$
|z-1|>r.
$$

把它们记为

$$
\zeta_1,\ldots,\zeta_K.
$$

对 \(n\ge K\)，构造首一多项式

$$
\boxed{
P_n(z)=
\prod_{j=1}^K(z-\zeta_j)(z-1)^{n-K}.
}
\tag{30}
$$

在被列出的谱点处，它为零。

在其余谱点处，\(|z-1|\le r\)，且单位圆上任意两点距离不超过 \(2\)，所以

$$
|P_n(z)|^2
\le4^K r^{2(n-K)}.
$$

由于 \(\mu\) 总质量为 \(1\)，

$$
h_n
\le
\int|P_n|^2\,d\mu
\le
4^K r^{2(n-K)}.
$$

取 \(n\) 次方根：

$$
\limsup_{n\to\infty}h_n^{1/n}\le r^2.
$$

\(r>0\) 任意，所以极限为零。证毕。

---

这不是仅仅证明“存在一列接近边界”。

它证明：

$$
\boxed{
\text{若 RH 成立，这组原始矩坐标必然越来越严重地贴近退化边界。}
}
\tag{31}
$$

## 还可以得到一个明确的衰减阶数上界

经典零点计数给出

$$
N(T)=O(T\log T).
$$

已有显式研究远强于本轮需要的这个增长阶。([arXiv][6])

取

$$
T=\frac{n}{(\log n)^2}.
$$

消去所有高度不超过 \(T\) 的不同谱点，数量为

$$
K=O\!\left(\frac n{\log n}\right).
$$

剩余谱点满足

$$
|z-1|\le\frac1T.
$$

将它代入上一证明，得到在 RH 前件下

$$
\boxed{
\log h_n
\le
-2n\log n
+
4n\log\log n
+
O(n).
}
\tag{32}
$$

这是上界，不是已证明的精确渐近等式。

## 对数值与几何意味着什么？

设 \(T_N\) 使用目前的原始矩坐标。由式（28）的试验多项式系数向量可得

$$
\lambda_{\min}(T_N)\le h_N.
$$

而矩阵对角线全为 \(1\)，所以

$$
\lambda_{\max}(T_N)\ge1.
$$

因此

$$
\boxed{
\operatorname{cond}_2(T_N)\ge\frac1{h_N}.
}
\tag{33}
$$

条件数会比任何固定指数更快地恶化。

这不是所有可能算法的复杂度下界。换基可以改善矩阵表示；但原始系数的误差如何通过换基传播，仍需控制。

**最重要的修正是：不能把“存在一个与阶数无关的正性余量”当作 RH 的中间目标。对当前矩阵族，这个要求即使在 RH 成立时也不可能满足。**

# 九、有限切片为什么不能自己决定后续？一个可以延迟到任意高阶的反模型

给定任意有限观察阶数 \(N\)，选择整数

$$
M>N.
$$

定义一个候选相关序列：

$$
r_0=1,\qquad
r_M=r_{-M}=\frac34,
$$

其余非零下标的 \(r_k\) 全部为零。

那么：

$$
T_N=I,
$$

所以前 \(N\) 阶看起来完全安全。

而且对全部 \(k\)，

$$
|r_k|\le1.
$$

但是在位置

$$
0,M,2M
$$

上，联合子矩阵为

$$
\begin{pmatrix}
1&\frac34&0\\
\frac34&1&\frac34\\
0&\frac34&1
\end{pmatrix}.
$$

它正是式（10）的负例。

所以：

$$
\boxed{
\text{任意长的有限安全前缀}
+
\text{所有逐对相关有界}
\quad\not\Rightarrow\quad
\text{整体正性}.
}
\tag{34}
$$

这不是 ξ 的系数序列，也不是 RH 反例。它证明的是：**抽象有限数据无法自行给出实际尾部的符号保证。**

对于实际 ξ，式（6）的解析结构额外约束了所有后续项；必须使用这一实际约束，不能把未知尾部任意挑成一个漂亮的正完成。

# 十、回到 5040：两种临界，不应该要求同一种“安全距离”

项目中的 \(5040\) 最优性，有明确的资源目标与正价格前件。源码证明了价格 \(1/25\) 下的唯一最优性。

在前文得到的价格平台内部，

$$
\frac{\log(12/11)}{\log11}
<
\lambda
<
\frac{\log(31/30)}{\log2},
$$

可以保留一个严格正的层切换余量：稍微扰动价格，最优指数仍然是 \((4,2,1,1)\)。

但当前 ξ 的矩阵几何不同：

$$
\boxed{
\text{5040 平台：内部有正的参数余量；}
}
$$

$$
\boxed{
\text{ξ 的全阶矩：即使全部合法，余量仍必然不断缩小。}
}
\tag{35}
$$

因此，“临界”至少应区分三个量：

$$
\boxed{
\text{是否可实现：符号};
}
$$

$$
\boxed{
\text{距离失败多远：余量};
}
$$

$$
\boxed{
\text{计算与扰动有多敏感：条件数}.
}
$$

它们不能混为一谈。

## 下一项实际约束，现在可以写得很精确

要从第 \(n\) 阶推进到第 \(n+1\) 阶，需要证明

$$
\boxed{
|r_{n+1}-m_n|\le h_n.
}
\tag{36}
$$

若计算提供

$$
|r_{n+1}-\widehat r_{n+1}|\le\varepsilon_r,
$$

$$
|m_n-\widehat m_n|\le\varepsilon_m,
$$

$$
h_n\ge\widehat h_n-\varepsilon_h,
$$

那么一个充分的严格正性证书是

$$
\boxed{
|\widehat r_{n+1}-\widehat m_n|
+\varepsilon_r+\varepsilon_m
<
\widehat h_n-\varepsilon_h.
}
\tag{37}
$$

反方向，若左侧差额的严格下界超过 \(h_n\) 的上界，就得到有限负证书。

**没有认证成功，只表示当前误差预算不足；不等于已经发现负性。**

本轮的精确有理反例、80／110 位数值复核与逐层残差计算，可由[核验脚本](sandbox:/mnt/data/discrete_critical_geometry_verify.py)复现；数据见[核验记录](sandbox:/mnt/data/discrete_critical_geometry_verify.json)。其中 ξ 系数部分明确标记为数值核对，不是区间认证。

# 结论

这次可以把“离散临界几何约束”归结为三条真正不同的边界。

第一条是**整数可实现边界**：

$$
\boxed{
\text{局部不出现 }11
\quad\text{不一定保证闭环后的全局合法性。}
}
$$

第二条是**联合相位的正性边界**：

$$
\boxed{
|r_{n+1}-m_n|\le h_n.
}
$$

它决定新的切片能否与旧切片来自同一个正 Hilbert 几何。

第三条是**无限阶稳定性边界**：

$$
\boxed{
\mathrm{RH}
\Longrightarrow
h_n>0\ \forall n,
\qquad
h_n^{1/n}\to0.
}
$$

所以，真正的目标不是把实际数据推离所有边界，而是证明：

> **实际数据可以在无限细、无限接近退化的合法区域里继续前进，却从不穿过正性边界。**

这比“ζ 很光滑，因此整体应该稳定”更严格，也比“数值很接近零，因此一定要相变”更准确。

目前尚未证明的，仍是实际 ξ 系数在全部阶数上满足式（36）。但缺项的位置已经明确：**不是再补一个任意顶点，而是证明下一项实际相关偏离预测中心的幅度，始终不超过此前几何留下的、正在迅速缩小的余量。**

[1]: https://arxiv.org/html/2301.05779v2 "https://arxiv.org/html/2301.05779v2"
[2]: https://dlmf.nist.gov/25.10 "https://dlmf.nist.gov/25.10"
[3]: https://dlmf.nist.gov/18.33 "https://dlmf.nist.gov/18.33"
[4]: https://arxiv.org/html/math/0502485v1 "https://arxiv.org/html/math/0502485v1"
[5]: https://dlmf.nist.gov/18.2 "https://dlmf.nist.gov/18.2"
[6]: https://arxiv.org/html/2412.15470v1 "https://arxiv.org/html/2412.15470v1"
这一步非常关键。**只研究“哪些离散状态允许存在”，还没有完整研究“这些状态能否按合法步骤到达”。**

而且，加入离散时间以后，会出现此前仅看静态数据无法发现的三种临界：

$$
\boxed{
\text{状态可以归一化，但平均执行时间已经发散};
}
$$

$$
\boxed{
\text{全部空间模式都存在，但某个采样节拍使它们永久混叠};
}
$$

$$
\boxed{
\text{单个端点只计一次时没有奇点，逐条历史计数以后却产生新奇点}.
}
$$

这些都能构造出明确实例。对 5040，还可以精确算出：

> **它有 60 个因数状态；在单步乘一个素数的生成规则下，有 840 条从 1 到 5040 的最短历史；若允许独立寄存器并行更新，则最少只需 4 拍。**

因此，“空间”“时间”“路径数量”不能相互替代，但可以放进同一套离散几何。

下面从状态、事件和历史开始，再接回黄金编码、量子观察与 ζ。

---

# 一、先区分三个此前容易重合的参数

前文出现过：

$$
s=\sigma+it,
$$

也出现过副本阶数 \(r\)、FRACTRAN 步数，以及量子演化参数。

这里必须明确：

$$
\boxed{
r=\text{副本数或矩阶数，不自动等于时间};
}
$$

$$
\boxed{
t=\text{与对数能量共轭的相位参数，不自动等于指令步数};
}
$$

$$
\boxed{
k=\text{已经执行的离散步骤数}.
}
$$

离散时间不能只通过“让 ζ 的 \(t\) 取整数”来定义。必须先说明：

**每一步允许做什么、消耗多少时间，以及哪些操作可以并行。**

所以，一个离散时空模型至少应包含：

$$
\boxed{
\mathfrak S=
(\text{状态},\text{事件},\text{转移},\text{先后约束},
\text{步长},\text{权重},\text{观察}).
}
\tag{1}
$$

这里把数据状态称为“空间”，首先是计算与状态空间意义，不是在未经论证的情况下把它认定为物理位置。

---

# 二、时间一般不能压缩成“当前状态的一个函数”

设每个事件 \(e:x\to y\) 消耗正整数时间：

$$
\tau(e)\ge1.
$$

一条历史：

$$
\gamma:x_0\to x_1\to\cdots\to x_m
$$

的时间为：

$$
\boxed{
T(\gamma)=\sum_{j=1}^{m}\tau(e_j).
}
\tag{2}
$$

能不能只从终点 \(x_m\) 读出已经经过的时间？

一般不能。

## 定理一：状态内时钟的必要条件

若存在函数 \(h\)，使每条允许边满足：

$$
h(y)-h(x)=\tau(e),
$$

那么任意两条具有相同起点、终点的历史，必须消耗同样时间。

特别地，只要存在一条正耗时闭环，就不存在这样的 \(h\)。

### 证明

沿路径求和：

$$
h(x_m)-h(x_0)=\sum_j\tau(e_j).
$$

若闭环返回原状态，左边为零，右边严格为正，矛盾。证毕。

例如前文 PRIMEGAME 的控制循环：

$$
11\longrightarrow13\longrightarrow11
$$

消耗两步，但内存重新回到 11。

因此：

$$
\boxed{
\text{状态重复}
\neq
\text{事件重复}
\neq
\text{时间回到过去}.
}
$$

完整事件应写成：

$$
(x,k),
$$

而不是只保留 \(x\)。把状态图沿执行历史展开以后，先后关系才不会被循环误导。

这也说明：**给状态再附加一个时钟，不只是多画一条坐标轴，而是在恢复被端点投影遗漏的历史信息。**

---

# 三、5040 的统一离散几何：60 个切片、8 个基本事件、840 种串行顺序

先选择一个明确的最小生成规则：

> 从 1 出发，每一步只允许乘以一个素数；目标是到达 5040。

这不是 PRIMEGAME 的实际运行时间，而是另一份明确的生成协议。

因为：

$$
5040=2^4\,3^2\,5\,7,
$$

所需事件为：

$$
2_1\prec2_2\prec2_3\prec2_4,
$$

$$
3_1\prec3_2,
$$

以及单独的：

$$
5_1,\qquad7_1.
$$

同一个寄存器内的事件必须按占据层次先后执行；不同素数寄存器之间没有额外依赖。

这构成一个有限因果偏序。

## 1. 空间切片是已完成事件的向下封闭集合

在某一时刻，若 \(2_3\) 已完成，则 \(2_1,2_2\) 也必须完成。

所以，一个合法切片由：

$$
(a_2,a_3,a_5,a_7)
\in
\{0,\ldots,4\}\times
\{0,\ldots,2\}\times
\{0,1\}\times
\{0,1\}
$$

确定。

合法切片数为：

$$
\boxed{
5\cdot3\cdot2\cdot2=60.
}
\tag{3}
$$

它们正是 5040 的因数。

因此：

$$
\boxed{
\text{因数格}
=
\text{这份事件偏序的合法历史切片集合}.
}
$$

这比把因数画成一堆点更完整：每个点都表示“已经完成了哪些事件”。

## 2. 串行执行需要 8 步，但有 840 种顺序

事件总数：

$$
4+2+1+1=8.
$$

保持各寄存器内部顺序的串行执行数为：

$$
\boxed{
\frac{8!}{4!\,2!\,1!\,1!}=840.
}
\tag{4}
$$

所以：

$$
\boxed{
60\text{ 个状态切片}
\quad\neq\quad
840\text{ 条完整串行历史}.
}
$$

不同历史可以经过不同中间切片，最终到达同一个整数。

## 3. 并行时间的下界是 4 拍，而不是 8 拍

若每一拍允许不同素数寄存器同时各增加一层，那么最长依赖链长度为 4，因此至少需要 4 拍，而且这个下界可以达到。

这种“事件总数”与“最长依赖链”的区别，在并发迹与 Cartier–Foata 分解中有经典的严格表达：前者对应串行长度，后者对应并行高度。([arXiv][1])

对 5040，要求每一拍至少有一个事件、每个寄存器每拍至多更新一次，执行恰好 \(L\) 拍的调度数为：

$$
\boxed{
N_L
=
\sum_{j=0}^{L}
(-1)^j\binom Lj
\binom{L-j}{4}
\binom{L-j}{2}
\binom{L-j}{1}^2.
}
\tag{5}
$$

这是对空拍作容斥。

本轮用该公式与独立动态规划交叉核对，得到：

| 拍数 \(L\) | 合法调度数 |
| -------: | ----: |
|        4 |    96 |
|        5 |   770 |
|        6 |  2040 |
|        7 |  2205 |
|        8 |   840 |

因此可以定义这份具体任务的时间生成多项式：

$$
\boxed{
\mathcal T_{5040}(z)
=
96z^4+770z^5+2040z^6+2205z^7+840z^8.
}
\tag{6}
$$

**5040 本身没有唯一的“所需时间”。时间必须相对于指令集、依赖关系和并行规则来定义。**

---

# 四、黄金金字塔要升级为“黄金执行历史”，而不是只编码每张截图

项目中的黄金编码首先保证：

$$
\text{合法 Zeckendorf 表}
\longleftrightarrow
\text{素数指数表}
\longleftrightarrow
\text{正整数}.
$$

这是静态信息的无损对应。

但是：

$$
2=(0,1),\qquad3=(0,0,1)
$$

按低位到高位的黄金表示，指数增加一时，可能同时改变多个数位。

因此：

$$
\boxed{
\text{一个算术步骤}
\neq
\text{一个黄金比特翻转}.
}
$$

假设算术更新为 \(T\)，编码为 \(\mathcal Z\)，黄金微步更新为 \(U\)。正确关系可能是：

$$
\boxed{
U^{\tau(x)}\mathcal Z(x)=\mathcal Z(Tx),
}
\tag{7}
$$

其中 \(\tau(x)\) 是这次规范更新实际需要的微步数。

连续执行 \(m\) 个算术步骤后：

$$
\boxed{
U^{\,\sum_{j=0}^{m-1}\tau(T^jx)}
\mathcal Z(x)
=
\mathcal Z(T^mx).
}
\tag{8}
$$

这就是状态保真之外，还需维护的**时间账本**。

若把每次宏更新都算作一拍，却不记录 \(\tau(x)\)，最终结果可以正确，执行时间却已经被改变。

项目的 `ControlledBehaviorUniversality.lean` 已经把状态转移与所有有限输入词后的读出一起纳入行为等价，而不只比较当前数值。本轮新增的要求，是进一步运输步骤成本，而不是直接把有限行为商当成完整的时间模型。

---

# 五、上一轮的静态约束锥，加入“每个前缀都合法”以后，出现新的时间临界

上一轮研究了共同上限约束：

$$
0\le b_j\le a.
$$

现在先取最小情形：

$$
\boxed{
\mathcal C_1=\{(a,b)\in\mathbb N^2:0\le b\le a\}.
}
\tag{9}
$$

赋予明确的步骤：

$$
(a,b)\longrightarrow(a+1,b),
$$

或者：

$$
(a,b)\longrightarrow(a,b+1),
$$

但第二种操作必须满足 \(b<a\)。

解释为：先创造一份容量，才能消耗一份容量。

这是一个指定的合法执行方案，**不是说 ζ 唯一的微观动力学必定如此**。

## 端点合法，与整个过程合法，是两件事

到达：

$$
(a,b)=(m,m)
$$

时，容量总数等于消耗总数。

若只检查终点，每个 \(m\) 只是一种状态。

若要求每个中间时刻都满足：

$$
b_k\le a_k,
$$

历史数就成为：

$$
\boxed{
C_m=\frac1{m+1}\binom{2m}{m}.
}
\tag{10}
$$

这是 Catalan 数：对应从未越过禁止边界的 Dyck 路径。它是经典离散路径计数。([麻省理工学院数学系][2])

前三个非空例子为：

$$
C_1=1,\qquad C_2=2,\qquad C_3=5.
$$

比如 \(m=2\) 时：

$$
\text{创造、创造、消耗、消耗}
$$

与：

$$
\text{创造、消耗、创造、消耗}
$$

都合法；一开始就消耗则不合法。

---

## 同一批端点，历史计数改变了收敛边界

给每个配对的“创造＋消耗”赋权 \(\chi\)。

只计端点：

$$
\boxed{
Z_{\mathrm{end}}(\chi)=\sum_{m\ge0}\chi^m=\frac1{1-\chi}.
}
\tag{11}
$$

逐条合法历史计数：

$$
\boxed{
Z_{\mathrm{hist}}(\chi)
=
\sum_{m\ge0}C_m\chi^m
=
\frac{1-\sqrt{1-4\chi}}{2\chi}.
}
\tag{12}
$$

后一式由“首个回返把路径分成两段”得到：

$$
Z_{\mathrm{hist}}=1+\chi Z_{\mathrm{hist}}^2.
$$

因此，临界半径从：

$$
1
$$

变成：

$$
\boxed{\frac14}.
$$

**没有增加任何新的终点；增加的是每个终点背后的合法时间顺序。**

---

# 六、真正的新时间边界：总概率仍可归一化，平均步骤已经无限

每条到达 \((m,m)\) 的历史，长度为：

$$
L=2m.
$$

在权重 \(\chi^m\) 下归一化，则：

$$
\mathbb E_\chi[L]
=
2\chi\frac{Z_{\mathrm{hist}}'(\chi)}
{Z_{\mathrm{hist}}(\chi)}.
$$

代入式（12）：

$$
\boxed{
\mathbb E_\chi[L]
=
\frac1{\sqrt{1-4\chi}}-1,
\qquad0\le\chi<\frac14.
}
\tag{13}
$$

但在边界：

$$
\boxed{
Z_{\mathrm{hist}}(1/4)=2<\infty,
}
$$

同时：

$$
\boxed{
\mathbb E_{1/4}[L]=\infty.
}
\tag{14}
$$

这就是一项严格的时间临界：

> **合法历史的总权重仍然有限，可以定义概率分布；但从这份分布抽取一条历史，其平均执行步数已经发散。**

它甚至可以定义一个归一化的历史叠加态，但该态的时钟算子期望值为无穷。

所以：

$$
\boxed{
\text{概率态合法}
\quad\not\Rightarrow\quad
\text{平均观察时间有限}.
}
$$

送回上一轮的素数权重，可以取：

$$
\chi=z^2p^{-(s+1)},
$$

其中 \(z\) 每执行一步乘一次，\(p^{-s}\) 与 \(p^{-1}\) 分别来自共同上限和因数占据的权重。

临界曲线变成：

$$
\boxed{
4z^2p^{-(\sigma+1)}=1.
}
\tag{15}
$$

这是一条真正同时涉及：

$$
\text{素数尺度 }p,\quad
\text{空间权重 }\sigma,\quad
\text{时间权重 }z
$$

的边界。

但它由当前路径规则产生，不能仅因某些参数下落在 \(\sigma=1\)，就认作 ζ 极点的唯一机制。

---

# 七、直接接到 ζ：整数只计一次，与每条生成历史都计一次，是不同解析函数

考虑从 1 出发，每一步乘一个素数。

定义：

$$
\Omega(n)=\sum_pv_p(n).
$$

在这个特定规则下：

$$
\Omega(n)
$$

既是事件总数，也是任意最短串行历史的长度。

## 1. 每个终点只计一次

定义：

$$
\boxed{
Z_{\mathrm{state}}(s,z)
=
\sum_{n\ge1}z^{\Omega(n)}n^{-s}
=
\prod_p\frac1{1-zp^{-s}}.
}
\tag{16}
$$

在 \(\Re s>1,\ |z|\le1\) 内可直接使用绝对收敛。

特别地：

$$
\boxed{
Z_{\mathrm{state}}(s,1)=\zeta(s).
}
\tag{17}
$$

这由唯一素因数分解和 Euler 乘积给出。([DLMF][3])

## 2. 每条有序生成历史都计一次

一条历史是一列素数：

$$
\gamma=(p_1,\ldots,p_k).
$$

定义：

$$
\boxed{
Z_{\mathrm{path}}(s,z)
=
\sum_\gamma
z^{|\gamma|}
(p_1\cdots p_k)^{-s}.
}
$$

记素数 ζ 函数：

$$
P(s)=\sum_pp^{-s}.
$$

按长度求和：

$$
\boxed{
Z_{\mathrm{path}}(s,z)
=
\sum_{k\ge0}[zP(s)]^k
=
\frac1{1-zP(s)},
}
\tag{18}
$$

成立条件为：

$$
|z|P(\Re s)<1.
$$

素数 ζ 函数及其收敛、计算关系是经典对象。([Springer][4])

同一终点 \(n=\prod p^{a_p}\) 的历史数为：

$$
\boxed{
h(n)=\frac{\Omega(n)!}{\prod_pa_p!}.
}
\tag{19}
$$

所以：

$$
Z_{\mathrm{path}}(s,z)
=
\sum_nh(n)z^{\Omega(n)}n^{-s}.
$$

对 5040：

$$
h(5040)=840.
$$

**历史计数把其系数从 1 改成了 840。**

---

## 一项精确的时间熵临界

取 \(z=1\)。

全部素数历史的临界实点满足：

$$
\boxed{
P(\sigma_{\mathrm{path}})=1.
}
$$

数值为：

$$
\boxed{
\sigma_{\mathrm{path}}
\approx1.3994333287263303.
}
\tag{20}
$$

这时 \(Z_{\mathrm{path}}\) 出现极点，而 ζ 在这个点并无奇点。

即使只允许：

$$
p\in\{2,3,5,7\},
$$

也会出现：

$$
2^{-\sigma}+3^{-\sigma}+5^{-\sigma}+7^{-\sigma}=1
$$

的唯一实根：

$$
\boxed{
\sigma\approx1.1473384117893520.
}
\tag{21}
$$

相比之下，同样四个素数的终点配分函数：

$$
\prod_{p\in\{2,3,5,7\}}\frac1{1-p^{-\sigma}}
$$

对每个 \(\sigma>0\) 都有限。

因此：

$$
\boxed{
\text{有限个空间方向}
+
\text{无限多合法步骤顺序}
}
$$

本身就能产生新的收敛边界。

这是一项时间历史熵造成的临界，不是 ζ 离线零点。

---

## 要保持同一个 ζ，必须怎样处理历史？

如果希望保留所有历史，同时仍然恢复原来的终点权重，需要给历史附加补偿：

$$
\boxed{
\sum_{\gamma:\,\mathrm{end}(\gamma)=n}
\frac{n^{-s}}{h(n)}
=n^{-s}.
}
\tag{22}
$$

或者把可交换的独立操作顺序识别成同一个并发迹。这样的“保留哪些顺序、商掉哪些顺序”正是迹幺半群与并发系统研究的内容。([arXiv][5])

**不是不能统一空间时间，而是统一时必须说明：是在计数状态、计数历史，还是对历史作了怎样的归一化。**

否则新出现的临界可能完全来自重复计数。

---

# 八、空间维度被消去以后，常常不是消失，而是变成时间记忆

这个关系可以直接用线性代数证明。

设离散系统为：

$$
\begin{pmatrix}
x_{k+1}\\y_{k+1}
\end{pmatrix}
=
\begin{pmatrix}
A&B\\C&D
\end{pmatrix}
\begin{pmatrix}
x_k\\y_k
\end{pmatrix}.
$$

观察者只保留 \(x_k\)，忽略 \(y_k\)。

迭代第二个方程：

$$
y_k=D^ky_0+
\sum_{j=0}^{k-1}D^{k-1-j}Cx_j.
$$

代回得到：

$$
\boxed{
x_{k+1}
=
Ax_k
+
BD^ky_0
+
\sum_{j=0}^{k-1}BD^{k-1-j}Cx_j.
}
\tag{23}
$$

它包含：

* 当前状态项；
* 被隐藏初态的贡献；
* 全部过去观察的记忆项。

因此：

$$
\boxed{
\text{少一个空间寄存器}
\quad\可能意味着\quad
\text{多一段时间记忆}.
}
$$

这不是一般性的口号，而是式（23）的严格消元。投影后产生记忆，也是 Mori–Zwanzig 方法中的核心机制。([arXiv][6])

在步数生成变量 \(z\) 中，保留的响应算子为：

$$
\boxed{
I-zA-z^2B(I-zD)^{-1}C.
}
\tag{24}
$$

其中：

$$
z^2B(I-zD)^{-1}C
=
z^2BC+z^3BDC+z^4BD^2C+\cdots.
$$

每一项都记录了一种不同长度的隐藏往返。

项目的 `SchurComplementAssociativity` 已证明，在明确逆算子前件下，分步消元与一次消元得到同一个保留算子。本轮式（24）是将同一消元机制应用到离散时间生成函数。

## 最小例子

取：

$$
x_{k+1}=y_k,\qquad y_{k+1}=x_k.
$$

消去 \(y\)：

$$
\boxed{x_{k+2}=x_k.}
$$

其时间生成函数是：

$$
\boxed{
X(z)=\frac{x_0+zy_0}{1-z^2}.
}
\tag{25}
$$

两个时间相位 \(+1,-1\) 都保留下来。

若只看静态保留块 \(A=0\)，并错误地用 \(x_{k+1}=0\) 替代，就把整个二周期结构删除了。

**这说明，所谓“投影后需要更高层结构”，有时可以具体实现为一个有限记忆寄存器，而不需要无穷追逐更高维观察者。**

---

# 九、5040 还有一项纯粹由离散采样造成的秩临界：60 个模式可以塌缩成 12 类

在 5040 的因数空间上，取对数能谱：

$$
H|d\rangle=E_*\log d\,|d\rangle,
\qquad d\mid5040.
$$

设无量纲采样间隔为：

$$
\Delta=\frac{E_*\Delta t}{\hbar}.
$$

考虑有限模式的线性读出：

$$
\boxed{
y_k=\sum_{d\mid5040}c_d\,e^{-ik\Delta\log d},
\qquad k=0,1,2,\ldots.
}
\tag{26}
$$

这里研究的是振幅参数 \(c_d\) 能否从时间样本中区分，不是把 \(y_k\) 当成概率。

如果全部乘子：

$$
\lambda_d=e^{-i\Delta\log d}
$$

互不相同，前 60 个样本组成 Vandermonde 系统，能够精确恢复全部 60 个振幅。

项目的 `TemporalFiberObserverUpgrade.lean` 已经证明：增加观察时间只能缩小观察纤维，并在**模式乘子互异**的前件下，由首个完整窗口区分全部振幅。这个互异前件不能省略。

## 现在选择一个特殊节拍

取：

$$
\boxed{
\Delta_0=\frac{2\pi}{\log2}.
}
\tag{27}
$$

将因数写成：

$$
d=2^a r,\qquad r\mid315.
$$

则：

$$
e^{-ik\Delta_0\log d}
=
e^{-ik\Delta_0\log r},
$$

因为：

$$
e^{-2\pi ika}=1.
$$

因此：

$$
\boxed{
y_k=
\sum_{r\mid315}
\left(\sum_{a=0}^{4}c_{2^ar}\right)
e^{-ik\Delta_0\log r}.
}
\tag{28}
$$

315 有 12 个因数，而这些剩余乘子互不相同。

所以：

$$
\boxed{
\text{全部时间样本的总秩}=12,
}
$$

$$
\boxed{
\text{永久不可区分的线性方向数}=60-12=48.
}
\tag{29}
$$

观察多久都无法分离同一组：

$$
r,\ 2r,\ 4r,\ 8r,\ 16r
$$

内部的振幅。

同理：

| 采样间隔           | 最多可区分的模式数 |
| -------------- | --------: |
| \(2\pi/\log2\) |        12 |
| \(2\pi/\log3\) |        20 |
| \(2\pi/\log5\) |        30 |
| \(2\pi/\log7\) |        30 |

**空间谱没有消失；特定的时间格点使它们产生了精确混叠。**

---

## 接近临界节拍时，需要更长的观察时间

令：

$$
\Delta=\Delta_0+\varepsilon.
$$

对 \(d\) 与 \(2d\) 的前 \(K\) 个样本列向量，有：

$$
\boxed{
\frac{\|v_d-v_{2d}\|_2}{\sqrt K}
\le
|\varepsilon|\log2
\sqrt{\frac{(K-1)(2K-1)}6}.
}
\tag{30}
$$

证明只需使用：

$$
|1-e^{iu}|\le|u|.
$$

因此，当：

$$
K|\varepsilon|\log2\ll1
$$

时，两个模式仍然非常难区分。

这给出一条真正的空间—时间联合约束：

> **离散空间中两个不同能级，能否被观察区分，不仅取决于能级差，还取决于采样节拍与累计观察长度。**

\(\varepsilon=0\) 时是精确秩损失；\(\varepsilon\ne0\) 但很小时是条件数恶化。两者不能混同。

---

# 十、可以把整段离散计算统一编码成一个量子几何，但正性本身不会证明 RH

现在假设一段有限计算已经通过保存输入、分支和必要记录，实现为幺正门：

$$
U_0,U_1,\ldots,U_{L-1}.
$$

不能直接假设一般 FRACTRAN 更新：

$$
|N\rangle\mapsto|T(N)\rangle
$$

就是幺正，因为不同输入可能合并到同一输出。

引入时钟空间：

$$
\mathcal H_{\mathrm{clock}}
=
\operatorname{span}\{|0\rangle,\ldots,|L\rangle\}.
$$

完整空间为：

$$
\mathcal H_{\mathrm{clock}}\otimes\mathcal H_{\mathrm{data}}.
$$

对块向量：

$$
\Psi=(\psi_0,\ldots,\psi_L),
$$

定义传播能量：

$$
\boxed{
\langle\Psi,H_{\mathrm{hist}}\Psi\rangle
=
E_c\sum_{k=0}^{L-1}
\|\psi_{k+1}-U_k\psi_k\|^2,
\qquad E_c>0.
}
\tag{31}
$$

它把“空间状态必须怎样随下一步变化”写成一个统一的正二次型。

这是 Feynman–Kitaev 历史态构造的基本机制。([arXiv][7])

其零能量态满足：

$$
\psi_{k+1}=U_k\psi_k.
$$

所以一份初态 \(\psi_0\) 产生：

$$
\boxed{
|\Psi_{\mathrm{hist}}\rangle
=
\frac1{\sqrt{L+1}}
\sum_{k=0}^{L}
|k\rangle\otimes
U_{k-1}\cdots U_0|\psi_0\rangle.
}
\tag{32}
$$

空间状态与离散时间被放入同一向量，但不同时间片仍保留各自的标签。

---

## 一个重要限制：这份时间能隙与具体算法内容无关

令：

$$
V_0=I,\qquad V_k=U_{k-1}\cdots U_0.
$$

作分块酉变换：

$$
W=\sum_{k=0}^{L}|k\rangle\langle k|\otimes V_k.
$$

则：

$$
\boxed{
W^*H_{\mathrm{hist}}W
=
E_cL_{\mathrm{path}}\otimes I,
}
\tag{33}
$$

其中 \(L_{\mathrm{path}}\) 是 \(L+1\) 个顶点的路径图 Laplacian。

所以传播部分的本征值为：

$$
\boxed{
2E_c\left[
1-\cos\frac{j\pi}{L+1}
\right],
\qquad j=0,\ldots,L.
}
\tag{34}
$$

最小非零能隙为：

$$
\boxed{
\Delta_L
=
2E_c\left[
1-\cos\frac{\pi}{L+1}
\right]
\sim
\frac{E_c\pi^2}{(L+1)^2}.
}
\tag{35}
$$

因此：

$$
L\to\infty
\Longrightarrow
\Delta_L\to0.
$$

这类历史时钟导致的临界性有系统研究，但必须保留具体构造与假设。([arXiv][8])

**这里的能隙闭合，首先来自越来越长的时钟链，并不自动说明数据算法发现了 ζ 离线零点。**

任何有限幺正计算都能构造这样的传播正算子。因此“已经找到一个正的时空哈密顿量”本身，还没有排除任何实际算术反例。

真正的算术信息仍需进入：初始条件、允许事件、输出读数，以及它们与实际 ξ 的保真关系。

---

# 十一、把这些结果统一：应研究“带时间权重的路径核”，而不是只研究状态图

对一个有限允许事件图，给每条边 \(e\) 指定：

$$
\tau(e)\in\mathbb N_{\ge1},
\qquad
\varepsilon(e)\in\mathbb R,
\qquad
a(e)\in\mathbb C.
$$

分别表示耗时、选定的能量或作用量权重，以及振幅。

定义矩阵：

$$
\boxed{
\mathsf T(s,z)_{yx}
=
\sum_{e:x\to y}
a(e)e^{-s\varepsilon(e)}z^{\tau(e)}.
}
\tag{36}
$$

那么，在收敛范围内，或作为形式幂级数：

$$
\boxed{
(I-\mathsf T(s,z))^{-1}
=
I+\mathsf T+\mathsf T^2+\cdots.
}
\tag{37}
$$

每一项都对应若干事件组成的历史，且完整保留：

$$
z^{T(\gamma)}
e^{-sE(\gamma)}
\prod_{e\in\gamma}a(e).
$$

于是，临界可以来自不同来源：

$$
\det(I-\mathsf T)=0
$$

表示某种回返响应失去可逆性；

某个指定矩阵元为零，表示特定输入输出之间的振幅相消；

某个导数发散，可能表示平均时间或时间方差发散；

某个采样矩阵降秩，表示观察协议无法再区分模式。

**这些是不同的边界，不能只因为都出现“零”或“发散”，就认作同一种离线机制。**

而消去内部节点时，应使用式（24）那样保留全部 \(z\) 次幂的 Schur 补。将一条三步路径直接改成一条一步边，会改变时间生成函数，即使终点没有改变。

---

# 十二、这对当前项目最直接的推进是什么？

本轮核对的项目快照仍是 `b89d56d0…`。其中三块基础能够分别承担不同任务：

`ControlledBehaviorUniversality` 负责保持全部有限输入历史的读出关系；`TemporalFiberObserverUpgrade` 负责区分观察时间窗口与模式分离前件；`SchurComplementAssociativity` 负责在实际逆算子前件下维护消元结果。它们不能互相替代，也不能被统称为“已经统一了时空”。

下一步的理论对象应当同时保留四项：

$$
\boxed{
\text{空间编码保真}
}
$$

$$
\boxed{
\text{合法历史与因果前缀保真}
}
$$

$$
\boxed{
\text{实际步骤数与并行深度保真}
}
$$

$$
\boxed{
\text{振幅、概率和路径计数的权重保真}.
}
$$

其中最后一项尤其重要：**同样的状态和同样的合法路径，仅仅改变“每个终点计一次”还是“每条路径计一次”，就能把 ζ 改成 \(1/(1-P(s))\)，并移动收敛边界。**

所以，对实际 ξ 的研究不能只要求“模型里面有素数、有黄金编码、有量子波”。必须证明：

$$
\boxed{
\text{完整时空路径读出}
=
\text{指定的实际 }\xi\text{ 表达},
}
$$

并且在截断时间、截断空间、消去内部状态时，保留可认证误差。

---

## 收束

加入离散时间以后，前面的几何确实获得了新的内容。

5040 不再只是：

$$
(4,2,1,1)
$$

这个状态点，而可以同时对应：

$$
\boxed{
60\text{ 个合法切片},
\quad
8\text{ 个基本事件},
\quad
840\text{ 条串行历史},
\quad
4\text{ 拍最小并行时间}.
}
$$

同一份因果约束，还能出现：

$$
\boxed{
Z_{\mathrm{hist}}(1/4)<\infty,
\qquad
\mathbb E[L]=\infty,
}
$$

说明时间临界可以先于概率归一化失效。

而在量子观察上：

$$
\boxed{
\Delta=\frac{2\pi}{\log2}
}
$$

会使 5040 的 60 个因数模式永久合并成 12 类，即使无限增加样本，也保留 48 个不可区分方向。

这些结论共同指向：

> **离散空间与离散时间应当通过“允许的事件历史”统一，而不是把时间简单当成又一个静态坐标。空间描述哪些状态可区分；因果描述哪些事件必须先发生；时钟描述执行与观察的代价；相位决定不同历史怎样相加。**

本轮的调度计数、Catalan 路径计数与时间期望恒等式作了独立枚举或符号核对；采样秩结论由精确算术证明得到。新增内容没有修改仓库，也尚未作 Lean 编译验证。

**这些结果尚未决定 RH。它们首先建立了一项必要的审计原则：任何声称从离散时空模型揭示 ζ 临界的推导，都必须证明新临界不是来自遗漏控制状态、重复计数历史、重标执行时间，或者选用了恰好失明的采样节拍。** 只有跨过这层审计，时空几何提供的约束才真正作用于同一个实际算术对象。

[1]: https://arxiv.org/abs/cs/0112012 "https://arxiv.org/abs/cs/0112012"
[2]: https://math.mit.edu/~rstan/zeros/ "https://math.mit.edu/~rstan/zeros/"
[3]: https://dlmf.nist.gov/27.4 "https://dlmf.nist.gov/27.4"
[4]: https://link.springer.com/article/10.1007/BF01933420 "https://link.springer.com/article/10.1007/BF01933420"
[5]: https://arxiv.org/abs/1505.05536 "https://arxiv.org/abs/1505.05536"
[6]: https://arxiv.org/abs/2209.05544 "https://arxiv.org/abs/2209.05544"
[7]: https://arxiv.org/abs/1712.07395 "https://arxiv.org/abs/1712.07395"
[8]: https://arxiv.org/abs/1810.06528 "https://arxiv.org/abs/1810.06528"
这次可以进一步做到：**不再把空间、时间、几何分别建模，而是先固定完整的离散历史，再把不同“切面”理解为对同一份历史读取不同关系。**

这样会出现一项很具体、也很容易被忽略的事实：

> **即使两份系统具有相同终点、相同步数，甚至在所有“过去／未来”切面上具有相同的纠缠谱，它们仍然可以是完全正交的量子态。把切面改成“奇数拍／偶数拍”，原来隐藏的区别就会显现。**

对 5040，这件事能用有限整数计算完整验证。

另一项结果是：

> **离散历史的相消零点，其重数可以由一个模数进位公式精确计算。新增一步若落在原有寄存器，和新增一个素数寄存器，会改变不同的零点结构。**

下面把这两项结果与项目的编码、切面拼接和 ζ 表示接起来。这里使用的逆序统计、\(q\)-多项式和循环多项式是经典工具；本轮的工作是把它们组织成当前项目的一套明确历史模型，而不是宣称发现了未知的普遍时空定律。

---

# 一、统一对象不是“空间加一根时间轴”，而是一组合法历史

先固定与上一轮一致的简单生成协议：

**从 1 出发，每一步乘一个素数，最终到达指定整数。**

这不是 PRIMEGAME 的全部指令语义。它是一份明确的、可独立研究的生成模型。

设：

$$
N=\prod_{i=1}^{m}p_i^{a_i},
\qquad p_1<\cdots<p_m,
$$

并记：

$$
\mathbf a=(a_1,\ldots,a_m),
\qquad
L=\sum_i a_i.
$$

一条历史是一个长度为 \(L\) 的字：

$$
\gamma=(i_1,\ldots,i_L),
$$

其中类型 \(i\) 恰好出现 \(a_i\) 次。

历史集合记为：

$$
\Gamma_{\mathbf a}.
$$

它有：

$$
\boxed{
|\Gamma_{\mathbf a}|
=
\frac{L!}{a_1!\cdots a_m!}.
}
\tag{1}
$$

在第 \(k\) 拍，已经完成的指数向量为：

$$
\mathbf n_\gamma(k)
=
\left(
\#\{r\le k:i_r=1\},\ldots,
\#\{r\le k:i_r=m\}
\right).
$$

因此：

$$
\boxed{
\sum_i n_{\gamma,i}(k)=k.
}
\tag{2}
$$

这才是一份统一的离散时空记录：

$$
\boxed{
\gamma
\longmapsto
\bigl\{(k,\mathbf n_\gamma(k))\bigr\}_{k=0}^{L}.
}
$$

“空间切片”是某个时刻的指数状态；“时间过程”是这些切片之间允许的移动。

项目的 `PrimeAxisEncoding.lean` 已经把黄金规范表与正整数建立成双射，并运输了乘法。它保证的是每张状态切片可以无损编码；要保持完整历史，还必须把事件顺序一起运输。

---

# 二、换坐标后，奇偶确实会成为时空格点的约束

先只看两个操作方向，设累计次数为 \(a,b\)。

定义：

$$
\boxed{
t=a+b,\qquad x=a-b.
}
\tag{3}
$$

那么：

$$
a=\frac{t+x}{2},
\qquad
b=\frac{t-x}{2}.
$$

因此，合法离散事件必须满足：

$$
\boxed{
t\ge0,\qquad |x|\le t,\qquad t\equiv x\pmod2.
}
\tag{4}
$$

每增加一次第一类事件：

$$
(t,x)\longmapsto(t+1,x+1);
$$

每增加一次第二类事件：

$$
(t,x)\longmapsto(t+1,x-1).
$$

所以原来非负象限中的单调路径，旋转坐标以后，成为一个棋盘状锥形格点中的路径。

**这里的奇偶条件不是额外添加的物理公理，而是保证反变换后的 \(a,b\) 仍是整数。**

交换两个操作方向：

$$
a\leftrightarrow b
$$

只产生：

$$
x\leftrightarrow-x,
\qquad t\text{ 不变}.
$$

但若强行交换 \(t\) 与 \(x\)，则：

$$
b\longmapsto-b.
$$

一般会离开合法状态空间。

因此：

> **统一空间时间，不意味着所有轴都可以任意交换；合法事件的方向约束依然存在。**

这里的 \(t,x\) 是计算事件坐标。尚未因此证明它们就是物理时间和空间，也不能仅因式（4）呈锥形就认定已经得到相对论。

---

# 三、哪些“其他切面”可以直接拼接？答案是：必须恰好截获每条历史一次

考虑一个有限、无环的允许事件图。给每条边 \(e\) 一个权重：

$$
w(e),
$$

它可以包含步数变量、能量权重和相位。

一条历史的权重是：

$$
w(\gamma)=\prod_{e\in\gamma}w(e).
$$

从起点 \(s\) 到终点 \(t\) 的总读数为：

$$
Z_{s\to t}=\sum_{\gamma:s\to t}w(\gamma).
$$

加权路径与矩阵幂、矩阵逆之间的这种对应是标准方法。([arXiv][1])

## 定理一：忠实切面的拼接公式

若一组边 \(\mathcal C\) 使每条完整历史**恰好经过其中一条边**，则：

$$
\boxed{
Z_{s\to t}
=
\sum_{e\in\mathcal C}
Z_{s\to\operatorname{tail}(e)}
\,w(e)\,
Z_{\operatorname{head}(e)\to t}.
}
\tag{5}
$$

### 证明

每条历史都可以按唯一的切面交点拆成：

$$
\text{切面前历史}
+
\text{跨切面事件}
+
\text{切面后历史}.
$$

反过来，每个合法拼接也唯一对应一条完整历史。逐条求和即可。证毕。

例如，累计步数：

$$
k=\sum_i n_i
$$

严格递增，因此固定步数形成合法切面。

对数能量：

$$
E(\mathbf n)=\sum_i n_i\log p_i
$$

也沿每次乘素数严格递增，因此“首次跨过 \(E=E_0\)”的边集也可以构成合法切面。

但：

$$
x=a-b
$$

不单调。一条路径可能多次穿越 \(x=0\)。

如果直接按所有交点拼接，计算的是：

$$
\sum_\gamma
\bigl(\text{这条历史与切面的交点数}\bigr)w(\gamma),
$$

不再是原来的 \(Z\)。

**因此，切面不是任意一刀。非单调切面需要首次穿越规则、额外记忆，或其他明确的计数修正。**

---

# 四、终点和时间仍然不够：还要读取操作顺序围出的“离散面积”

对历史：

$$
\gamma=(i_1,\ldots,i_L),
$$

定义逆序数：

$$
\boxed{
A(\gamma)
=
\#\{(r,s):r<s,\ i_r>i_s\}.
}
\tag{6}
$$

它统计：较大的素数操作，有多少次发生在较小素数操作之前。

这不是新的执行步数。所有历史仍然恰好执行 \(L\) 步。

## 为什么它是一种面积？

固定两个类型 \(i<j\)，删掉历史中其他事件。剩下的是一个：

$$
a_i\times a_j
$$

矩形中的格点路径。

每交换一对相邻的不同事件：

$$
ij\leftrightarrow ji,
$$

路径扫过一个单位方格，逆序数改变一。

因此：

$$
\boxed{
A(\gamma)
=
\text{所有两方向投影中，相对规范路径的整数面积之和}.
}
\tag{7}
$$

多重集排列的逆序统计与 \(q\)-多项式有经典对应。([DLMF][2])

这里的“面积”是寄存器更新格点上的组合面积，不是物理面积单位。

---

## 它可以逐步更新，不需要先知道整条历史

如果下一步执行类型 \(i\)，而此前累计计数为 \(\mathbf n\)，则：

$$
\boxed{
A_{\mathrm{new}}
=
A_{\mathrm{old}}+\sum_{j>i}n_j.
}
\tag{8}
$$

所以完整状态可以扩充为：

$$
(\mathbf n,k,A).
$$

也可以不保存整数 \(A\)，而是在每一步施加对应的受控相位。

但若只保留终点 \(\mathbf a\) 和总时间 \(L\)，\(A\) 一般无法恢复。

对 5040，规范顺序：

$$
2,2,2,2,3,3,5,7
$$

有：

$$
A=0;
$$

相反顺序：

$$
7,5,3,3,2,2,2,2
$$

有：

$$
A=21.
$$

它们终点相同、步数相同、总对数能量相同，却具有完全不同的顺序面积。

---

# 五、把统一历史沿“顺序面积”切开，得到一个精确多项式

定义：

$$
\boxed{
Q_{\mathbf a}(q)
=
\sum_{\gamma\in\Gamma_{\mathbf a}}q^{A(\gamma)}.
}
\tag{9}
$$

这里 \(q\) 是辅助生成参数，之后可以取单位复相位；它不是 PRIMEGAME 的控制标记。

令：

$$
[n]_q=1+q+\cdots+q^{n-1},
\qquad
[n]_q!=\prod_{j=1}^{n}[j]_q.
$$

经典逆序生成恒等式给出：

$$
\boxed{
Q_{\mathbf a}(q)
=
\frac{[L]_q!}{[a_1]_q!\cdots[a_m]_q!}.
}
\tag{10}
$$

这是一个具有非负整数系数的多项式，不是在单位根处随意代入一个未处理的 \(0/0\) 商。([DLMF][2])

也可以直接用式（8）递推验证：

$$
\boxed{
Q_{\mathbf a}(q)
=
\sum_{i:a_i>0}
q^{\sum_{j>i}a_j}
Q_{\mathbf a-\mathbf e_i}(q).
}
\tag{11}
$$

---

## 对 5040，结果完全分解

取：

$$
\mathbf a=(4,2,1,1),
\qquad L=8.
$$

得到：

$$
\boxed{
Q_{5040}(q)
=
\frac{[8]_q!}{[4]_q![2]_q!}.
}
$$

用 \(\Phi_d(q)\) 表示第 \(d\) 个分圆多项式，则：

$$
\boxed{
Q_{5040}(q)
=
\Phi_2(q)\Phi_3(q)\Phi_4(q)
\Phi_5(q)\Phi_6(q)\Phi_7(q)\Phi_8(q).
}
\tag{12}
$$

它的次数为：

$$
\sum_{i<j}a_ia_j=21,
$$

而：

$$
Q_{5040}(1)=840.
$$

因此，原来的同一组历史具有三种不同读数：

$$
\boxed{
\begin{aligned}
\text{终点}&:\quad5040;\\
\text{步骤长度}&:\quad8;\\
\text{顺序面积分布}&:\quad Q_{5040}(q).
\end{aligned}
}
$$

第三种读数不是前两种读数的函数。

---

# 六、真正的离散临界公式：零点重数等于一次模数进位

式（10）还给出一个比 5040 更一般的定理。

由：

$$
[n]_q
=
\prod_{\substack{d\mid n\\d>1}}\Phi_d(q),
$$

得到：

$$
\boxed{
Q_{\mathbf a}(q)
=
\prod_{d=2}^{L}\Phi_d(q)^{c_d(\mathbf a)},
}
\tag{13}
$$

其中：

$$
\boxed{
c_d(\mathbf a)
=
\left\lfloor\frac Ld\right\rfloor
-
\sum_i\left\lfloor\frac{a_i}{d}\right\rfloor
=
\left\lfloor
\frac{\sum_i(a_i\bmod d)}d
\right\rfloor.
}
\tag{14}
$$

最后一个表达式是非负整数。

因此：

## 定理二：模数进位—相消重数关系

若 \(\omega\) 是一个本原 \(d\) 次单位根，则：

$$
\boxed{
\operatorname{ord}_{q=\omega}Q_{\mathbf a}
=
c_d(\mathbf a).
}
\tag{15}
$$

也就是说：

> **把各寄存器的占据数对 \(d\) 取余，再将这些余数相加；产生多少个向上一位的进位单位，相应相位处就有多少重零点。**

这里说的是最低余数层的进位，不是全部 \(d\) 进制数位中进位次数的总和。

这类零点全为单位根的组合生成函数，属于已有的分圆生成函数理论。([arXiv][3])

但式（14）给当前项目一个非常具体的临界量：

$$
\boxed{
c_d(\mathbf a)=0
\quad\text{或}\quad
c_d(\mathbf a)>0.
}
$$

空间占据量、总步骤数与相位零点重数，被同一个整数公式连接起来。

---

## 5040 的精确均匀性

对 \((4,2,1,1)\)：

$$
c_d=1
\qquad(d=2,\ldots,8).
$$

由有限 Fourier 反演，顺序面积模 \(d\) 的分布，在每个 \(d=2,\ldots,8\) 上都严格均匀：

| 模数 \(d\) | 每个余数类中的历史数 |
| -------: | ---------: |
|        2 |        420 |
|        3 |        280 |
|        4 |        210 |
|        5 |        168 |
|        6 |        140 |
|        7 |        120 |
|        8 |        105 |

所以：

$$
\boxed{
\frac1{840}Q_{5040}(e^{2\pi i/d})=0
\qquad(d=2,\ldots,8).
}
\tag{16}
$$

最小的正相位零点是：

$$
\boxed{\theta_*=\frac\pi4.}
\tag{17}
$$

这项最小相位也不能被神秘化：对任何至少含两种事件类型、总长度为 \(L\) 的完整多重集历史族，\(\Phi_L\) 都会出现，因此都有相位 \(2\pi/L\) 的零点。

**5040 的具体信息在于完整的分圆因子组合及其重数，而不只是某一个数字相同。**

---

# 七、同样增加一步：加深旧方向与启用新方向，改变的是不同零点

从 5040 出发，考虑两种一步扩展。

## 增加一个 \(2\) 事件

$$
10080=2^5\,3^2\,5\,7.
$$

其历史多项式满足：

$$
\boxed{
Q_{10080}(q)
=
Q_{5040}(q)\frac{[9]_q}{[5]_q}.
}
\tag{18}
$$

因此，原来的 \(\Phi_5\) 因子被消去，而增加了 \(\Phi_3\Phi_9\)。

## 增加一个新的 \(11\) 事件

$$
55440=2^4\,3^2\,5\,7\,11.
$$

新事件可以插在原八步历史的九个位置，分别产生零到八个新逆序，因此：

$$
\boxed{
Q_{55440}(q)
=
[9]_q\,Q_{5040}(q).
}
\tag{19}
$$

它保留全部旧因子，再增加：

$$
[9]_q=\Phi_3(q)\Phi_9(q).
$$

特别地，三次单位根处的零点变为二重。

结果是：

| 终点    | 步数 |  历史数 | 顺序面积多项式次数 |
| ----- | -: | ---: | --------: |
| 5040  |  8 |  840 |        21 |
| 10080 |  9 | 1512 |        25 |
| 55440 |  9 | 7560 |        29 |

**同样多走一步，并不意味着产生同样的时空结构。**

一步落在已有方向，会改变旧方向内部的排序冗余；一步引入新方向，会与此前全部事件建立新的先后关系。

这与前文资源优化中区分“纵向加深”与“横向增加素数轴”相互呼应，但这里的历史恒等式不依赖任何最优性假设。

---

# 八、现在正式研究“换切面”：跨切面的关系必须单独保留

把一条历史分成前、后两段：

$$
\gamma=\gamma_1\gamma_2.
$$

设它们的事件计数分别为：

$$
\mathbf u,\qquad\mathbf v.
$$

则：

$$
\boxed{
A(\gamma)
=
A(\gamma_1)+A(\gamma_2)+B(\mathbf u,\mathbf v),
}
\tag{20}
$$

其中：

$$
\boxed{
B(\mathbf u,\mathbf v)
=
\sum_{i>j}u_i v_j.
}
\tag{21}
$$

这个最后一项统计：

> 前段的较大类型事件，与后段的较小类型事件，形成了多少跨切面的逆序。

因此，在第 \(k\) 拍切开：

$$
\boxed{
Q_{\mathbf a}(q)
=
\sum_{\substack{0\le\mathbf u\le\mathbf a\\|\mathbf u|=k}}
q^{B(\mathbf u,\mathbf a-\mathbf u)}
Q_{\mathbf u}(q)\,
Q_{\mathbf a-\mathbf u}(q).
}
\tag{22}
$$

它精确保留同一份整体读数。

若只把前段和后段各自算对，却漏掉：

$$
q^{B(\mathbf u,\mathbf a-\mathbf u)},
$$

仍然会拼错整体。

最小例子是两个不同事件：

$$
Q_{(1,1)}(q)=1+q.
$$

前后各只看一个事件时，每段都没有内部逆序。若直接相乘相加，只会得到 2，遗漏全部相消信息。

---

## 多次换切面为何仍然一致？

跨段项满足：

$$
\boxed{
B(\mathbf u,\mathbf v)
+
B(\mathbf u+\mathbf v,\mathbf w)
=
B(\mathbf v,\mathbf w)
+
B(\mathbf u,\mathbf v+\mathbf w).
}
\tag{23}
$$

因为两边都等于：

$$
B(\mathbf u,\mathbf v)+B(\mathbf u,\mathbf w)+B(\mathbf v,\mathbf w).
$$

因此，先拼前两段还是先拼后两段，得到同一个总相位。

这是一项明确的**拼接相容律**。

项目中的 `SchurComplementAssociativity.lean` 在另一种算子表达下，同样强调：在相应逆算子存在的前件下，逐层消元与一次消元必须一致。这里不是直接调用那项定理证明式（23），而是形成了相同的审计要求——**换分解顺序，不能暗中换掉整体对象。**

---

# 九、量子化整条历史：所有“过去／未来”纠缠谱都可能看不见区别

把每一拍的事件类型保存在一个四维寄存器中。

对 5040 的 840 条合法历史，定义：

$$
\boxed{
|\Psi_\theta\rangle
=
\frac1{\sqrt{840}}
\sum_{\gamma\in\Gamma_{(4,2,1,1)}}
e^{i\theta A(\gamma)}|\gamma\rangle.
}
\tag{24}
$$

这是历史记录空间中的合法纯态。

它与零相位态的重叠为：

$$
\boxed{
\langle\Psi_0|\Psi_\theta\rangle
=
\frac{Q_{5040}(e^{i\theta})}{840}.
}
\tag{25}
$$

所以：

$$
\boxed{
\langle\Psi_0|\Psi_{\pi/4}\rangle=0.
}
\tag{26}
$$

这不是原来的 \(\log N\) 能谱自动产生的相位。原模型中所有这些历史都有相同终点能量，不能仅靠那个终点能量区分它们。

现在测量的是一个明确新增的历史观测量：

$$
\widehat A|\gamma\rangle=A(\gamma)|\gamma\rangle.
$$

可以用它实施受控相位，但不能把该零点叫作 ζ 零点。

---

## 定理三：每一个连续时间切面的 Schmidt 系数都与 \(\theta\) 无关

在第 \(k\) 拍后，将历史分成前 \(k\) 个寄存器和后 \(8-k\) 个寄存器。

记：

$$
h(\mathbf u)=\frac{|\mathbf u|!}{\prod_i u_i!}.
$$

由式（20），有 Schmidt 分解：

$$
\boxed{
|\Psi_\theta\rangle
=
\sum_{\substack{\mathbf u\le\mathbf a\\|\mathbf u|=k}}
\sqrt{p_k(\mathbf u)}\,
e^{i\theta B(\mathbf u,\mathbf a-\mathbf u)}
|\mathbf u;\theta\rangle
\otimes
|\mathbf a-\mathbf u;\theta\rangle,
}
\tag{27}
$$

其中：

$$
\boxed{
p_k(\mathbf u)
=
\frac{
h(\mathbf u)h(\mathbf a-\mathbf u)
}{
h(\mathbf a)
}.
}
\tag{28}
$$

不同 \(\mathbf u\) 对应不同事件计数，所以左右两侧的对应向量分别正交。

因此，Schmidt 系数就是：

$$
\sqrt{p_k(\mathbf u)},
$$

与 \(\theta\) 无关。证毕。

对 \(k=4\)，允许的 \(\mathbf u\) 恰好有 12 个，所以：

$$
\boxed{
\operatorname{SchmidtRank}_{1\ldots4\,|\,5\ldots8}
|\Psi_\theta\rangle=12.
}
\tag{29}
$$

于是：

> **\(|\Psi_0\rangle\) 与 \(|\Psi_{\pi/4}\rangle\) 完全正交，但在每一个“前几拍／后几拍”切面上，它们具有相同的纠缠谱和纠缠熵。**

这不表示它们的约化密度矩阵全部相同。其本征向量一般会变化；这里严格相同的是本征值。

因此，**即使收集了全部连续时间切面的纠缠熵，也没有恢复整条历史的相位结构。**

---

# 十、换成奇数拍／偶数拍切面，隐藏区别立即变成秩变化

现在不用连续时间切面，而是按寄存器位置分成：

$$
A=\{1,3,5,7\},
\qquad
B=\{2,4,6,8\}.
$$

这是对完整历史记录的一种合法量子二分。

但它不是某个真实瞬间的因果切面：要操作它，必须先保存所需历史。不能将它直接当成新的正向演化时间。

## 在 \(\theta=0\) 时

所有历史振幅相同，因此按奇、偶寄存器各自的事件计数分块，每块都是秩一矩阵。

仍然只有 12 个可能的计数块，所以：

$$
\boxed{
\operatorname{SchmidtRank}_{\mathrm{odd}\,|\,\mathrm{even}}
|\Psi_0\rangle=12.
}
\tag{30}
$$

## 加入顺序相位以后

在其中一块中，选择奇数拍记录：

$$
r_1=(2,2,3,5),
\qquad
r_2=(2,2,5,3),
$$

以及偶数拍记录：

$$
c_1=(2,2,3,7),
\qquad
c_2=(2,2,7,3).
$$

将行列交错拼回八拍历史，其逆序数分别为：

$$
\begin{pmatrix}
0&3\\
2&4
\end{pmatrix}.
$$

因此，这个 \(2\times2\) 子矩阵为：

$$
\boxed{
\frac1{\sqrt{840}}
\begin{pmatrix}
1&q^3\\
q^2&q^4
\end{pmatrix},
\qquad q=e^{i\theta}.
}
\tag{31}
$$

行列式为：

$$
\boxed{
\frac{q^4(1-q)}{840}.
}
\tag{32}
$$

只要 \(q\ne1\)，它就非零。

其余 11 个计数块仍各自至少具有秩一，因此：

$$
\boxed{
q\ne1
\Longrightarrow
\operatorname{SchmidtRank}_{\mathrm{odd}\,|\,\mathrm{even}}
|\Psi_\theta\rangle\ge13.
}
\tag{33}
$$

特别地，对 \(\theta=\pi/4\)：

$$
\boxed{
\begin{aligned}
\text{所有连续时间切面的纠缠谱}
&:\quad\text{不变};\\
\text{奇数拍／偶数拍切面的秩}
&:\quad12\longrightarrow至少13.
\end{aligned}
}
$$

这就是你要求的“统一结构再从其他切面分析”的一个完整实例。

**不是新切面创造了区别，而是它读取了旧切面谱数据没有决定的交叉相位。**

---

# 十一、相位不能随意解释成几何曲率：必须固定它从哪里来

式（8）允许在每条类型 \(i\) 的边上放置局部相位：

$$
U_i(\mathbf n)
=
e^{i\theta\sum_{j>i}n_j}.
$$

对 \(i<j\)，交换两个相邻操作的次序，有：

$$
\boxed{
\frac{
U_j(\mathbf n)U_i(\mathbf n+\mathbf e_j)
}{
U_i(\mathbf n)U_j(\mathbf n+\mathbf e_i)
}
=
e^{i\theta}.
}
\tag{34}
$$

所以，历史面积相位可以写成每个基本方形上相同的离散绕行相位。

但必须强调：

**这个绕行相位是由我们选择的顺序观测协议引入的。**

如果只使用：

$$
E(\mathbf n)=\sum_i n_i\log p_i
$$

的梯度差作为边相位，那么绕方形一圈为零，不会自动出现式（34）的非平凡相位。

因此，不能从素数乘法本身推出“时空一定有某种曲率”。正确的说法是：

> **同一算术历史空间可以承载不同的观测联络；联络一旦指定，换切面时就必须保留它的跨切面相位。**

这也划清了两件事：

$$
\boxed{
\text{改变切面，读取同一对象}
}
$$

与：

$$
\boxed{
\text{改变相位规则，构造一个新响应}
}
$$

并不相同。

本轮的 \(\theta\) 是一个明确的可调探针；并没有证明它是实际 ξ 的唯一或必然微观相位。

---

# 十二、把空间、时间和顺序切面接回同一份 ζ 表示

最后构造一份保留这三种信息、并且能恢复原 ζ 的母函数。

对每个正整数 \(n\)，令：

$$
\mathbf a(n)=(v_p(n))_p,
$$

$$
L(n)=\Omega(n)=\sum_pv_p(n),
$$

$$
h(n)=Q_{\mathbf a(n)}(1).
$$

定义：

$$
\boxed{
\mathcal Z(s,z,q)
=
\sum_{n\ge1}
n^{-s}z^{\Omega(n)}
\frac{Q_{\mathbf a(n)}(q)}{h(n)}.
}
\tag{35}
$$

其中 \(n=1\) 的因子按 1 定义。

等价地：

$$
\mathcal Z(s,z,q)
=
\sum_{n\ge1}
\frac{n^{-s}}{h(n)}
\sum_{\gamma\in\Gamma_{\mathbf a(n)}}
z^{|\gamma|}q^{A(\gamma)}.
$$

这里除以 \(h(n)\) 很重要：它保证每个终点总权重不因历史数不同而被重复放大。

当：

$$
\Re s>1,\qquad |z|\le1,\qquad |q|\le1,
$$

有：

$$
\left|
\frac{Q_{\mathbf a(n)}(q)}{h(n)}
\right|\le1.
$$

因此：

$$
|\mathcal Z(s,z,q)|\le\zeta(\Re s),
$$

级数绝对收敛。

## 不同切面给出不同的实际算术读数

关闭顺序探针：

$$
\boxed{
\mathcal Z(s,z,1)
=
\sum_nz^{\Omega(n)}n^{-s}
=
\prod_p\frac1{1-zp^{-s}}.
}
\tag{36}
$$

再关闭步骤标记：

$$
\boxed{
\mathcal Z(s,1,1)=\zeta(s).
}
\tag{37}
$$

这是标准 Euler 乘积。([DLMF][4])

若读取步骤奇偶，取 \(z=-1\)，则：

$$
\boxed{
\mathcal Z(s,-1,1)
=
\sum_n\frac{(-1)^{\Omega(n)}}{n^s}
=
\frac{\zeta(2s)}{\zeta(s)}.
}
\tag{38}
$$

证明直接来自：

$$
\frac1{1+p^{-s}}
=
\frac{1-p^{-s}}{1-p^{-2s}}.
$$

这里出现的是 Liouville 函数，而不是 Möbius 函数。

若改取：

$$
z=1,\qquad q=-1,
$$

读取的则是历史面积奇偶。

对 5040：

$$
(-1)^{\Omega(5040)}=1,
$$

但：

$$
\frac{Q_{5040}(-1)}{840}=0.
$$

因此：

$$
\boxed{
\text{步骤奇偶}
\neq
\text{历史面积奇偶}.
}
$$

这两种切面都来自同一份带标记的历史对象，却产生不同的信息。

---

## 与 RH 的连接，仍须守住实际对象

式（38）的解析延拓，在：

$$
\Re s>\frac12
$$

中，分子 \(\zeta(2s)\) 没有零点。因此，ζ 在该区域的离线零点会表现为这个比值的极点。

但原 Dirichlet 级数只是在：

$$
\Re s>1
$$

得到绝对收敛保证。要向临界线推进，仍然需要控制带符号部分和，不能只凭“它来自一份统一时空模型”就延伸正性或收敛性。

而式（16）的有限历史相消零点，属于 \(q\) 方向的辅助读出。它们没有自动变成 \(s\) 方向的 ζ 零点。

**母函数的价值是让不同切面的关系明确；它不允许把不同切面的结论互相冒充。**

---

# 十三、对项目而言，这次新增的理论责任是什么？

本轮读取的仓库快照是 `777f5c1694…`。

`PrimeAxisEncoding` 已承担状态层面的规范编码；`TemporalFiberObserverUpgrade` 已证明增加观察时间不会扩大不可区分纤维，但保留了模式分离等必要前件；`SchurComplementAssociativity` 则保证在相应逆算子存在时，消元次序不改变保留结果。

现在还可以明确补出三项研究对象：

$$
\boxed{
\text{合法切面：每条历史恰好被截获一次};
}
$$

$$
\boxed{
\text{跨切面数据：}
B(\mathbf u,\mathbf v)=\sum_{i>j}u_iv_j;
}
$$

$$
\boxed{
\text{拼接相容律：式（23）}.
}
$$

黄金编码必须运输的不只是：

$$
\mathbf n\longleftrightarrow\text{黄金字串},
$$

还包括原事件标签、逻辑步骤和跨段关系。

若一次指数加一在黄金机器里展开成多个微步，应当区分：

$$
\text{逻辑事件时钟}
\quad\text{与}\quad
\text{编码实现时钟}.
$$

不能把黄金进位中的每个比特操作，当成新的素数事件，再声称历史面积仍然相同。

---

## 本轮核对范围

本轮精确枚举了 5040 的全部 840 条生成历史，核对了逆序分布、分圆分解、模 \(2\) 至模 \(8\) 的均匀性，以及全部九个连续时间切面的拼接恒等式。

还分别核对了：

$$
Q_{10080}=Q_{5040}[9]_q/[5]_q,
\qquad
Q_{55440}=Q_{5040}[9]_q,
$$

以及奇数拍／偶数拍切面中的非零子行列式。

**这些是整数、多项式和有限矩阵层面的精确核对，不等于已经完成 Lean 编译验证。没有修改仓库。**

---

# 收束

这次可以给“统一离散时空，再从其他切面分析”一个完整答案：

$$
\boxed{
\text{固定合法历史}
\longrightarrow
\text{保留时间与权重}
\longrightarrow
\text{选择切面}
\longrightarrow
\text{运输跨切面关系}
\longrightarrow
\text{比较不变量与可见性}.
}
$$

对 5040，最具体的新结果是：

$$
\boxed{
Q_{5040}(q)=\prod_{d=2}^{8}\Phi_d(q),
}
$$

以及：

$$
\boxed{
c_d(\mathbf a)
=
\left\lfloor\frac{\sum_i a_i}{d}\right\rfloor
-\sum_i\left\lfloor\frac{a_i}{d}\right\rfloor.
}
$$

后一个式子把空间占据、时间总长、模数进位与相位零点重数直接连接起来。

更深的一项结论是：

$$
\boxed{
\text{所有连续时间切面的纠缠谱相同}
\quad\not\Rightarrow\quad
\text{完整历史态相同}.
}
$$

在我们构造的例子中，两个整体态甚至正交；换成奇数拍／偶数拍切面，原本隐藏的区别会表现为 Schmidt 秩从 12 增加到至少 13。

所以，整体研究的关键不是不断添加“更高一层观察者”，而是：

> **识别哪一种跨切面关系没有被当前读出保留，并证明更换切面以后，读取的仍然是同一份带权历史，而不是重新构造了一个更容易解释的对象。**

当前还没有由此决定 RH。已经得到的是一套更严格的几何研究方法：**空间是合法状态，时间是合法事件的顺序，其他切面读取的是这些顺序之间的关系；真正的离散临界，可以出现在进位、相位抵消、切面秩变化或解析收敛边界上，但必须分别定义，再证明它们之间的运输。**

[1]: https://arxiv.org/abs/1112.1588 "https://arxiv.org/abs/1112.1588"
[2]: https://dlmf.nist.gov/26.16 "https://dlmf.nist.gov/26.16"
[3]: https://arxiv.org/abs/2305.07620 "https://arxiv.org/abs/2305.07620"
[4]: https://dlmf.nist.gov/27.4 "https://dlmf.nist.gov/27.4"
**这次应当把研究对象从“某一时刻的离散状态”，提升为“满足局部规则的整段离散历史”。**这样，空间约束与时间约束才能放在同一个对象里检验。

而且能得到三个明确结果：

$$
\boxed{
\text{Zeckendorf 的一次寄存器加一，在局部实现中可能需要跨越整条进位链。}
}
$$

$$
\boxed{
\text{即使每一步完全合法，长度为 }T\text{ 的历史也会产生 }T^{-2}\text{ 级谱间隙。}
}
$$

$$
\boxed{
\text{前文的 }\xi\text{ Toeplitz 矩阵，在共同幺正实现存在时，正是历史态的时钟约化密度矩阵。}
}
$$

第三条尤其重要：**此前讨论的“联合几何正性”，本来就可以同时理解为“跨时间的相干一致性”。**

但这里必须区分三种时钟：FRACTRAN 的一条分数指令、局部数码机器的一次更新、谱算子 \(U\) 的一次作用，不自动具有相同成本。统一它们，应当证明模拟与计时关系，而不是把它们都记成 \(t\) 后直接等同。

本次核对的项目快照仍为 `b89d56d0c9a4…`；已有编码等价和动态闭包可以作为接口。下面的新增推导给出证明，未进行 Lean 编译。

# 一、时间不能只当作状态上的又一个标签：它首先属于路径

设状态空间为 \(\mathcal X\)，允许的基本转移为

$$
x\xrightarrow{e}y.
$$

给每条基本转移赋予正整数成本

$$
\tau(e)\in\mathbb N_{>0}.
$$

一条历史

$$
\gamma:
x_0\xrightarrow{e_0}x_1
\xrightarrow{e_1}\cdots
\xrightarrow{e_{m-1}}x_m
$$

的时间是

$$
\boxed{
T(\gamma)=\sum_{j=0}^{m-1}\tau(e_j).
}
\tag{1}
$$

它一般不是仅由终点 \(x_m\) 决定的函数。

## 一个真实的 FRACTRAN 例子

在前文固定的原版 PRIMEGAME 中，合法输入 \(13\) 会运行成

$$
\boxed{
13\longrightarrow11\longrightarrow13.
}
\tag{2}
$$

这是两次微步，但回到了同一个整数状态。这里不声称该循环出现在从标准初态 \(2\) 出发的轨迹中。指令优先级与控制寄存器规则保存在前文核验脚本中。

如果试图给每个状态赋予一个绝对时间 \(t(x)\)，要求每步

$$
t(y)-t(x)=1,
$$

那么沿式（2）相加会得到

$$
0=2,
$$

矛盾。

因此：

$$
\boxed{
\text{状态可以回返；事件时间不能由状态值单独恢复。}
}
\tag{3}
$$

正确的事件对象应至少是

$$
(x_j,j),
$$

或者更一般的“状态＋历史位置”。状态图中的循环，不等于事件历史中出现倒因果。

## 5040 也给出一个具体的时间纤维

前文的归一化规则是

$$
2^a3^b5^c7^d
\longrightarrow
13\cdot5^{a+c+1}7^{a+b},
$$

所用微步数为

$$
3a+2b+d+2.
$$

相应有限检查已经保存在核验文件中。

于是，对所有 \(r\ge0\)，

$$
\boxed{
5040\cdot7^r
\xrightarrow{\,19+r\text{ 步}\,}
13\cdot5^6 7^6.
}
\tag{4}
$$

终点完全相同，时间却可以任意增加。

所以，把这些输入都归并为同一个宏观状态，可以保存后续事件顺序，却不能自动保存已经消耗的时间。

**这是一种明确的时间信息丢失，不需要借助模糊的“隐藏维度”解释。**

# 二、空间长度会强制时间成本：Zeckendorf 进位的因果下界

项目的 `PrimeAxisEncoding.lean` 已证明规范 Zeckendorf 表与正整数之间的等价，并定义了乘法对应的规范表加法。但该数学定义采用 `noncomputable` 构造，不能据此认定规范化在局部机器中只需要一步。

现在明确规定一个执行模型：

* 数码排列在一维位置 \(0,1,2,\ldots\)；
* 每一步，一个位置只能读取距离不超过 \(R\) 的旧状态；
* 辅助寄存器初始值局部固定，不预先藏入整个输入的计算结果；
* 算法必须在统一的最坏深度内输出正确的规范编码。

中间步骤可以使用进位标记等额外状态；不要求中间数码始终已经规范化。

## 定理一：规范加一的最坏局部深度至少与编码跨度成正比

令

$$
q_L=F_{L+2}-1,
$$

其中 \(F_0=0,F_1=1\)。

任何满足上述局部性条件、能正确完成 Zeckendorf 加一的算法，其最坏深度 \(\tau_L\) 满足

$$
\boxed{
R\tau_L\ge L-1.
}
\tag{5}
$$

对奇数 \(L\)，还能加强为

$$
\boxed{
R\tau_L\ge L.
}
\tag{6}
$$

### 证明

使用权重

$$
F_2,F_3,F_4,\ldots=1,2,3,\ldots.
$$

\(q_L\) 的规范表示在位置

$$
L-1,L-3,L-5,\ldots
$$

上取 \(1\)，其余位置取零。

而

$$
q_L+1=F_{L+2}
$$

只在新位置 \(L\) 取 \(1\)。

比较两个输入

$$
q_L,\qquad q_L-1.
$$

当 \(L\) 为奇数时，它们只在位置 \(0\) 不同；当 \(L\) 为偶数时，只在位置 \(0,1\) 不同。

但加一后的正确输出

$$
q_L+1,\qquad q_L
$$

在位置 \(L\) 不同。

一个半径为 \(R\) 的局部更新系统，经过 \(\tau\) 步后，位置 \(L\) 只能依赖初始区间

$$
[L-R\tau,L+R\tau].
$$

如果这个区间没有碰到两个输入的差异位置，输出就必须相同，与正确性矛盾。证毕。

这里使用的 Zeckendorf 唯一表示是既有数学结构；时间下界则来自上述明确的局部因果约束。([Lean Prover Community][1])

---

## 5040 中已经有一个最小实例

只看 \(2\) 的指数寄存器：

$$
3=(0,0,1,0),
$$

$$
4=(1,0,1,0),
$$

$$
5=(0,0,0,1),
$$

数码按低位到高位排列。

比较“指数 \(3\) 加一”与“指数 \(4\) 加一”：

$$
3\to4,\qquad4\to5.
$$

两个输入只在最低位不同，但输出在位置 \(3\) 不同。

因此，半径 \(R=1\) 的局部机器，至少需要三步才能对这两个输入都正确完成操作。

放回整数：

$$
2520\xrightarrow{\times2}5040,
$$

$$
5040\xrightarrow{\times2}10080.
$$

这两条都是合法的乘法，但后一条跨过了当前三位黄金窗口的容量边界。

$$
\boxed{
\text{空间中新增一个高位，要求时间中完成一段信息传播。}
}
\tag{7}
$$

这不是所有计算机上的普遍加法下界。允许远程门、全局预处理或其他编码时，成本模型会改变。**但一旦要求固定半径的局部执行，空间跨度与时间深度就不再能独立选择。**

# 三、真正统一离散空间与时间：把整段历史写成一个约束态

现在进入线性或量子模型。

对一段有限计算，先给不可逆步骤保留必要的控制与历史记录，再把其可逆演化记为

$$
U_0,U_1,\ldots,U_{T-1}.
$$

设它们作用在同一个足够大的 Hilbert 空间 \(\mathcal H\) 上。

定义历史向量

$$
\boxed{
|\Psi\rangle
=
\sum_{t=0}^{T}|t\rangle\otimes|\psi_t\rangle.
}
\tag{8}
$$

这里：

* \(|\psi_t\rangle\) 保存数据；
* \(|t\rangle\) 保存执行位置；
* 不同时间切片属于同一个整体向量。

通过时钟寄存器把动力学编码为静态历史对象，是 Feynman–Kitaev 构造的核心；已有工作也使用局部时钟保存电路的空间—时间结构。([arXiv][2])

## 定义：传播一致性能量

$$
\boxed{
\mathcal E_{\mathrm{prop}}(\Psi)
=
\sum_{t=0}^{T-1}
\|\psi_{t+1}-U_t\psi_t\|^2.
}
\tag{9}
$$

它对应一个半正定算子 \(H_{\mathrm{prop}}\)。

显然，

$$
\boxed{
\mathcal E_{\mathrm{prop}}(\Psi)=0
\iff
\psi_{t+1}=U_t\psi_t\quad\forall t.
}
\tag{10}
$$

这就把时间规则变成了整段历史上的几何约束。

但要注意：式（9）只检查“是否按这些 \(U_t\) 演化”，并不检查输入是否正确、输出是否满足 RH 等算术目标。历史态方法本来就需要把传播、初始化和输出条件分别编码。([arXiv][3])

# 四、时间本身会制造临界：完全合法的历史，其谱间隙仍然趋零

## 定理二：开放历史链的精确谱间隙

在式（9）的单位边权归一化下，

$$
\boxed{
\operatorname{gap}(H_{\mathrm{prop}})
=
2-2\cos\frac{\pi}{T+1}
\sim\frac{\pi^2}{(T+1)^2}.
}
\tag{11}
$$

这个结果与具体执行了哪些幺正操作无关。

### 证明

令

$$
W_0=I,\qquad
W_{t+1}=U_tW_t.
$$

作可逆坐标变换

$$
\psi_t=W_t\phi_t.
$$

则

$$
\psi_{t+1}-U_t\psi_t
=
W_{t+1}(\phi_{t+1}-\phi_t).
$$

所以

$$
\mathcal E_{\mathrm{prop}}
=
\sum_{t=0}^{T-1}\|\phi_{t+1}-\phi_t\|^2.
$$

这就是 \(T+1\) 个顶点的路径图 Laplacian，张量乘以数据空间上的恒等算子。

它的本征值为

$$
2-2\cos\frac{k\pi}{T+1},
\qquad k=0,\ldots,T.
$$

取第一个非零值即得。证毕。

这属于历史态时钟谱分析中的标准结构；改变边权、边界条件或时钟图以后，必须重新分析，不能无条件套用同一个公式。([arXiv][4])

---

这与上一轮的矩阵高度衰减形成了一个重要对应：

$$
\boxed{
\text{数据联合阶数增加，会逼近某种几何退化；}
}
$$

$$
\boxed{
\text{执行历史变长，也会逼近某种谱退化。}
}
$$

两者都不自动意味着出现非法状态。

## 小的逐步误差，怎样累积成全局历史误差？

令 \(P_{\mathrm{hist}}\) 投影到精确历史子空间。对归一化 \(\Psi\)，由谱间隙，

$$
\boxed{
\|(I-P_{\mathrm{hist}})\Psi\|^2
\le
\frac{\mathcal E_{\mathrm{prop}}(\Psi)}
{2-2\cos[\pi/(T+1)]}.
}
\tag{12}
$$

因此，若要把到精确历史的距离压到 \(\eta\)，一个充分条件是

$$
\boxed{
\mathcal E_{\mathrm{prop}}(\Psi)
\lesssim
\frac{\eta^2}{T^2}.
}
\tag{13}
$$

假设每个归一化数据切片的更新误差都不超过 \(\delta\)。将它们组成均匀历史态后，总传播能量不超过 \(\delta^2\)，所以全局距离上界约为

$$
\boxed{O(T\delta).}
\tag{14}
$$

因此，“每一步误差都很小”不够；还要看

$$
T\delta
$$

是否受到控制。

一个简单例子是，目标更新为恒等操作，但实际每步把一个二能级向量旋转一个小角 \(\delta\)。每步误差可以很小，经过约 \(\pi/(2\delta)\) 步后，状态却与初态正交。

**这就是一种真正的时间临界：不是单步合法性突然消失，而是累计偏差超过了整段历史允许的余量。**

# 五、空间与时间分开合法，仍然不保证混合方格合法

历史链只处理一个方向。若要同时分析离散空间和时间，还必须比较不同路径。

设在网格位置 \((i,t)\)：

$$
V_{i,t}:\text{沿空间方向搬运状态},
$$

$$
U_{i,t}:\text{向下一时间层演化}.
$$

从 \((i,t)\) 到 \((i+1,t+1)\)，有两条前向路径：

$$
\text{先空间后时间}:
\quad U_{i+1,t}V_{i,t},
$$

$$
\text{先时间后空间}:
\quad V_{i,t+1}U_{i,t}.
$$

## 定理三：混合方格的相容条件

若希望对所有输入状态，两条路径给出相同结果，就必须且只需

$$
\boxed{
U_{i+1,t}V_{i,t}
=
V_{i,t+1}U_{i,t}.
}
\tag{15}
$$

定义回返算子

$$
\boxed{
\mathcal W_{i,t}
=
(V_{i,t+1}U_{i,t})^*
U_{i+1,t}V_{i,t}.
}
\tag{16}
$$

对幺正搬运，

$$
\boxed{
\text{全部状态路径独立}
\iff
\mathcal W_{i,t}=I.
}
\tag{17}
$$

对一个指定状态，则只要求它属于 \(\mathcal W_{i,t}\) 的固定子空间。

这里的“回返”是比较两条前向路径的代数差，不要求物理上倒转时间。

在单连通矩形网格中，全部基本方格满足式（15），便能通过相邻步骤交换证明路径独立；若加上周期边界，还必须另查整体环路。

## 一个精确反例：每条边都合法，整个方格却无法零误差拼接

给四条边分配标量相位。前三条为 \(+1\)，最后一条为 \(-1\)。

每条边本身都是合法幺正操作，但绕方格的相位乘积为

$$
-1.
$$

非零状态不可能绕一圈后既保持原值，又变成相反数。

更定量地，若总环相位为 \(\Theta\in[-\pi,\pi]\)，定义四顶点传播能量

$$
\mathcal E_\square
=
\sum_{j=0}^{3}
\left|
\psi_{j+1}-e^{i\Theta/4}\psi_j
\right|^2,
\qquad
\psi_4=\psi_0.
$$

在

$$
\sum_{j=0}^3|\psi_j|^2=1
$$

下，其最小值为

$$
\boxed{
\min\mathcal E_\square
=
2-2\cos\frac{|\Theta|}{4}.
}
\tag{18}
$$

这是直接对四点 Fourier 模态求本征值的结果。

当 \(\Theta=\pi\) 时，

$$
\boxed{
\min\mathcal E_\square=2-\sqrt2>0.
}
\tag{19}
$$

这个正数就是无法消除的拼接残差。

**它不是负概率，也不是 Hamiltonian 不正；它说明不存在同时满足全部边关系的非零零能量历史。**带幺正边标签的图及其环路约束，是电路—Hamiltonian 构造中的已有框架。([Quantum Journal][5])

这给“统一离散时空”一个明确要求：

$$
\boxed{
\text{除了空间边和时间边，还必须检查空间—时间混合环路。}
}
\tag{20}
$$

# 六、前文的 ξ 矩阵，本来就同时是一张时间相关矩阵

现在接回实际算术，而不是只讨论抽象电路。

沿用

$$
\log\frac{\xi(1/(1-z))}{\xi(1)}
=
\sum_{n\ge1}\frac{\ell_n}{n}z^n,
$$

$$
c_0=2+\gamma_{\mathrm E}-\log(4\pi),
$$

$$
c_n=\ell_{n+1}-2\ell_n+\ell_{n-1},
\qquad
r_n=\frac{c_n}{c_0}.
$$

前文的 Toeplitz 矩阵为

$$
\boxed{
T_N=(r_{j-i})_{0\le i,j\le N},
\qquad r_{-n}=r_n\in\mathbb R.
}
\tag{21}
$$

Li 系数、单位圆映射与相关正性的联系具有经典基础。([arXiv][6])

在 RH 前件下，令

$$
w_\rho=1-\frac1\rho,
$$

则 \(|w_\rho|=1\)，并可构造幺正算子 \(U\) 与单位向量 \(v\)，使

$$
\boxed{
r_n=\langle v,U^nv\rangle.
}
\tag{22}
$$

这里明确使用了 RH。反过来，对实际系数建立全部阶数的共同正实现，正是此前的证明责任，不能预先假设。

## 定理四：Toeplitz 矩阵是历史态的时钟约化密度矩阵

构造

$$
\boxed{
|\Psi_N\rangle
=
\frac1{\sqrt{N+1}}
\sum_{t=0}^{N}
|t\rangle\otimes U^t|v\rangle.
}
\tag{23}
$$

那么

$$
\boxed{
\rho_{\mathrm{clock}}
=
\operatorname{Tr}_{\mathrm{data}}
|\Psi_N\rangle\langle\Psi_N|
=
\frac{T_N}{N+1}.
}
\tag{24}
$$

### 证明

时钟矩阵的第 \(i,j\) 项为

$$
\frac1{N+1}
\langle U^jv,U^iv\rangle
=
\frac{r_{i-j}}{N+1}.
$$

由于当前 \(r_{i-j}=r_{j-i}\) 为实数，得到式（24）。证毕。

---

这是一条真正的空间—时间统一：

$$
\boxed{
\text{同一张矩阵，}
\quad
\begin{cases}
\text{作为 Gram 矩阵：描述状态之间的几何关系};\\
\text{作为时钟密度矩阵：描述不同执行时刻之间的相干关系}.
\end{cases}
}
\tag{25}
$$

但是，时钟的对角概率始终是

$$
\frac1{N+1}.
$$

只查看“每个时刻出现的概率”，无法看出非对角的联合约束。

**如果把非对角元全部删除，就得到一个合法的均匀时钟分布；但实际 ξ 的相干正性问题也被同时删除了。**

这与前文“只看切片，各自都合法，却不知道能否拼起来”完全一致。

## 矩阵阶数与时间长度还不能重复计数

设所谓第 \(i\) 个空间读出已经是

$$
v_i=U^iv.
$$

再让它演化 \(t\) 步：

$$
U^tv_i=U^{i+t}v.
$$

因此，标签 \((i,t)\) 实际只通过 \(i+t\) 进入状态。

若

$$
0\le i\le L,\qquad0\le t\le N,
$$

则共有

$$
(L+1)(N+1)
$$

个标签，但它们的张成空间至多只有

$$
L+N+1
$$

维。

在当前 RH 下的无限谱支集上，幂向量线性独立，因此维数恰好是

$$
\boxed{
\operatorname{rank}K_{\mathrm{space-time}}
=
L+N+1,
}
\tag{26}
$$

而冗余维数为

$$
\boxed{LN.}
$$

这不是一般物理时空的维数公式。它说明：**如果两个坐标本来就是同一操作的不同累计次数，不能把它们当成彼此独立的新自由度。**

# 七、真正的时间分辨率：高处零点为什么需要很长的回返窗口？

这一节给出一个新的定量约束。

先只研究一个固定时间采样通道。对候选频率 \(\vartheta\)，记录

$$
\boxed{
u_N(\vartheta)
=
\frac1{\sqrt{N+1}}
(1,e^{i\vartheta},\ldots,e^{iN\vartheta}).
}
\tag{27}
$$

这里比较的是两种频率的**时间响应向量**，不是已经能够直接读取的两个谱本征态。

若频率差为 \(\delta\)，它们的重叠是

$$
\boxed{
\langle u_N(\vartheta),u_N(\vartheta+\delta)\rangle
=
e^{iN\delta/2}
\frac{\sin((N+1)\delta/2)}
{(N+1)\sin(\delta/2)}.
}
\tag{28}
$$

## 定理五：固定分离度需要足够长的时间

有

$$
\boxed{
1-
|\langle u_N(\vartheta),u_N(\vartheta+\delta)\rangle|^2
\le
\frac{N(N+2)}{12}\delta^2.
}
\tag{29}
$$

因此，如果要求

$$
|\langle u_N(\vartheta),u_N(\vartheta+\delta)\rangle|
\le\eta<1,
$$

就必须满足

$$
\boxed{
N(N+2)\delta^2\ge12(1-\eta^2).
}
\tag{30}
$$

### 证明

记重叠为 \(K\)。则

$$
1-|K|^2
=
\frac1{(N+1)^2}
\sum_{j,k=0}^{N}
[1-\cos((j-k)\delta)].
$$

使用 \(1-\cos x\le x^2/2\)，以及

$$
\frac1{(N+1)^2}\sum_{j,k=0}^N(j-k)^2
=
\frac{N(N+2)}6,
$$

即得式（29）。证毕。

所以：

$$
\boxed{
N|\delta|\ll1
\Longrightarrow
\text{两个频率的有限时间响应几乎平行。}
}
\tag{31}
$$

这不是所有频率估计算法的普遍时间下界；它是当前时间响应几何达到固定分离度所需的条件。

## 对 ξ 的单位圆映射，频率间距被压缩了多少？

在 RH 下，

$$
\rho=\frac12+i\gamma,\qquad\gamma>0,
$$

对应

$$
w_\rho=e^{i\vartheta_\gamma},
$$

其中

$$
\boxed{
\vartheta_\gamma
=
2\arctan\frac1{2\gamma}.
}
\tag{32}
$$

所以

$$
\boxed{
\frac{d\vartheta_\gamma}{d\gamma}
=
-\frac1{\gamma^2+1/4}.
}
\tag{33}
$$

两个高度 \(\gamma<\gamma'\) 的相位差为

$$
|\delta|
=
\int_\gamma^{\gamma'}
\frac{du}{u^2+1/4}
\le
\frac{\gamma'-\gamma}{\gamma^2+1/4}.
$$

结合式（30），得到

$$
\boxed{
\sqrt{N(N+2)}
\ge
\sqrt{12(1-\eta^2)}
\frac{\gamma^2+1/4}{\gamma'-\gamma}.
}
\tag{34}
$$

例如，要求重叠不超过 \(1/2\)，就必须有

$$
\boxed{
\sqrt{N(N+2)}
\ge
3\frac{\gamma^2+1/4}{\gamma'-\gamma}.
}
\tag{35}
$$

**因此，高处谱信息映到单位圆以后，看起来非常密集；要把它们重新分开，需要相应增长的时间窗口。**

这不是 ζ 失去了信息，而是当前观察坐标压缩了分辨尺度。

## 离线位移与时间相位分辨，具有同一个局部压缩因子

令

$$
\rho_0=\frac12+i\gamma,
\qquad
w(\rho)=1-\frac1\rho.
$$

直接求导：

$$
\boxed{
\left.
\frac{d}{d\rho}\log w(\rho)
\right|_{\rho=\rho_0}
=
-\frac1{\gamma^2+1/4}.
}
\tag{36}
$$

所以，对小扰动

$$
\delta\rho=\delta\beta+i\,\delta\gamma,
$$

有

$$
\boxed{
\delta\log w
=
-\frac{\delta\beta+i\delta\gamma}{\gamma^2+1/4}
+
O_\gamma(|\delta\rho|^2).
}
\tag{37}
$$

其中：

* \(\delta\beta\) 改变单位圆的径向幅度；
* \(\delta\gamma\) 改变单位圆上的相位；
* 两者都被约 \(1/\gamma^2\) 压缩；
* 经过 \(N\) 次作用，指数中的变化被乘以 \(N\)。

这就是一条可以严格使用的统一尺度关系：

$$
\boxed{
\text{法向离线偏移与切向频率间距，}
\quad
\text{在这个解析坐标中受同一个局部灵敏度控制。}
}
\tag{38}
$$

但它只是单个模式的局部响应。要保证实际 \(r_n\) 出现负证书，还要控制留数、其他模式和误差，不能把式（37）直接当成检测时刻公式。

# 八、重新理解上一轮的 \(h_N\)：它也是“新增一步时间究竟增加多少独立信息”

在共同幺正实现存在时，前文的正交高度为

$$
\boxed{
h_N
=
\min_{a_0,\ldots,a_{N-1}}
\left\|
U^Nv-\sum_{j=0}^{N-1}a_jU^jv
\right\|^2.
}
\tag{39}
$$

这是单位圆矩问题中标准的预测残差解释。([arXiv][7])

因此：

$$
h_N>0
$$

表示第 \(N\) 个时间读出没有被前面的读出精确线性决定；

$$
h_N\ll1
$$

表示它几乎已经落在旧时间读出的张成空间里。

上一轮在 RH 前件下证明了

$$
\boxed{
h_N>0\quad\forall N,
\qquad
h_N^{1/N}\to0.
}
\tag{40}
$$

其原因是：全部谱点 \(w_\rho\) 只有一个聚集点 \(1\)。可以先用有限个多项式零点消去远离 \(1\) 的谱，再用高次 \((z-1)\) 压低剩余部分。

现在可以更准确地解释这一结果：

$$
\boxed{
\text{每增加一个时刻，都增加一个严格独立的方向；}
}
$$

$$
\boxed{
\text{但新增方向与旧历史的夹角可以极端微小。}
}
\tag{41}
$$

“严格独立”与“数值上容易区分”不是一回事。

这里还应分开两种退化：

$$
\operatorname{gap}(H_{\mathrm{prop}})
\asymp T^{-2}
$$

描述整段历史对传播误差的敏感度；

$$
h_N^{1/N}\to0
$$

描述实际回返轨道的线性可区分度。

**它们不能在没有指定耦合模型时直接相乘，称为一个新的“时空间隙”。**

# 九、把时间误差真正带回正性认证

设实际目标仍是

$$
T_N=(r_{j-i}).
$$

如果有限计算得到 \(\widetilde r_k\)，并有经过证明的误差界

$$
\boxed{
|\widetilde r_k-r_k|\le k\varepsilon,
\qquad0\le k\le N,
}
\tag{42}
$$

其中 \(r_0\) 精确归一化，则对应矩阵误差满足

$$
\boxed{
\|\widetilde T_N-T_N\|_{\mathrm{op}}
\le
\frac{N(N+1)}2\varepsilon.
}
\tag{43}
$$

### 证明

每一行的绝对误差和不超过

$$
\varepsilon\sum_{j=0}^{N}|j-i|.
$$

最大值出现在端点行，为

$$
\varepsilon\frac{N(N+1)}2.
$$

对 Hermitian 矩阵，算子范数不超过最大绝对行和。证毕。

因此，一个充分的正性证书是

$$
\boxed{
\lambda_{\min}(\widetilde T_N)
>
\frac{N(N+1)}2\varepsilon.
}
\tag{44}
$$

如果观测或计算误差随时间积累，不能只检查

$$
\lambda_{\min}(\widetilde T_N)>0
$$

就结束。

同时，前文有

$$
\lambda_{\min}(T_N)\le h_N.
$$

所以当前原始矩坐标的可认证余量会变得非常小。

这并不构成所有算法的复杂度下界：换基、符号不等式、严格递推可能改善计算。但它确实排除了一个不可靠做法：

$$
\boxed{
\text{固定精度计算越来越长的历史，}
\quad
\text{然后把浮点正号当作全局正性。}
}
\tag{45}
$$

反过来，误差区间跨过零，也不等于实际矩阵已经为负。

# 十、结合项目，下一层理论应当记录什么？

项目已有的编码等价、动态闭包和前文矩几何，可以进一步组织成一个**带局部性与时钟成本的历史接口**：

$$
\boxed{
\mathfrak S=
(\mathcal X,\mathcal E,\tau,q,\mathcal A).
}
\tag{46}
$$

其中：

$$
\mathcal X:\text{数据、控制和必要历史组成的状态空间};
$$

$$
\mathcal E:\text{允许的基本转移};
$$

$$
\tau:\text{每条转移的时间成本};
$$

$$
q:\text{实际观察协议};
$$

$$
\mathcal A:\text{合法性、相干性与误差约束}.
$$

对于一个宏观程序，正确的语义保持应写成

$$
\boxed{
F^{\tau(x)}(\iota x)=\iota(\overline F x),
}
\tag{47}
$$

而不是简单要求 \(F\iota=\iota\overline F\)。

还需要检查：

$$
\boxed{
\text{空间投影是否保留未来分支};
}
$$

$$
\boxed{
\text{时间压缩是否保留返回成本};
}
$$

$$
\boxed{
\text{空间与时间的混合路径是否相容};
}
$$

$$
\boxed{
\text{随步数增长，误差与谱余量怎样共同变化}.
}
$$

已有 `DynamicClosureMinimality` 可以支持第一项的抽象最小性；`PrimeAxisEncoding` 支持编码语义。局部执行成本、传播半径、带时钟模拟与混合方格条件，仍需作为明确的新前件和定理封装，而不能从编码双射中自动推出。

本轮做了有限核对：\(63\) 组黄金进位输入对、\(31\) 组 \(5040\cdot7^r\) 的归一化时钟、随机幺正历史的路径谱、四边形相位残差，以及时间响应重叠界。整数部分为精确核对，矩阵部分为普通浮点复核。可复现代码见[核验脚本](sandbox:/mnt/data/discrete_spacetime_constraints_verify.py)，结果见[核验记录](sandbox:/mnt/data/discrete_spacetime_constraints_verify.json)。

# 结论

这次可以把离散临界分成四种互相连接、但不能混同的边界：

$$
\boxed{
R\tau_L\ge L-1
}
$$

是**空间信息传播所要求的最低时间**；

$$
\boxed{
\operatorname{gap}(H_{\mathrm{prop}})
=
2-2\cos\frac{\pi}{T+1}
}
$$

是**长历史的传播稳定性边界**；

$$
\boxed{
U_{i+1,t}V_{i,t}
=
V_{i,t+1}U_{i,t}
}
$$

是**空间与时间共同拼接的相容条件**；

$$
\boxed{
\sqrt{N(N+2)}
\gtrsim
\frac{\gamma^2}{|\Delta\gamma|}
}
$$

是**当前 ξ 回返坐标下的时间分辨约束**。

最重要的统一等式则是

$$
\boxed{
\rho_{\mathrm{clock}}=\frac{T_N}{N+1}.
}
$$

它说明：**此前的几何矩阵，不只是“不同状态排在一起”的静态对象；在共同幺正实现下，它正是整段历史的时间相干状态。**

因此，下一步不能只问“每个离散数据点是否合法”，也不能只问“每次操作是否正确”。必须问：

> **这些数据能否沿允许的步骤形成同一段历史；这段历史在改变切片、合并步骤和增加观察时长之后，是否仍保留相同的因果结果、相位关系与误差保证。**

本轮没有证明实际 ξ 的全阶正性。但已经把尚待控制的内容从“再补一个空间方向”，推进到了更明确的**时空联合约束**：传播范围、时钟成本、环路相容、时间分辨与正性余量，必须在同一个模型里同时成立。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html"
[2]: https://arxiv.org/abs/1311.6101 "https://arxiv.org/abs/1311.6101"
[3]: https://arxiv.org/html/1712.07395v2 "https://arxiv.org/html/1712.07395v2"
[4]: https://arxiv.org/abs/1712.07395 "https://arxiv.org/abs/1712.07395"
[5]: https://quantum-journal.org/papers/q-2018-09-19-94/ "https://quantum-journal.org/papers/q-2018-09-19-94/"
[6]: https://arxiv.org/html/2301.05779v2 "https://arxiv.org/html/2301.05779v2"
[7]: https://arxiv.org/html/math/0502485v1 "https://arxiv.org/html/math/0502485v1"
**这次可以把“统一离散时空，再从其他切面分析”变成一组明确的数学操作，而不只是更换图像。**

最重要的推进是：

$$
\boxed{
\text{整段执行历史压缩到边界后，时间不会自动消失；
它会进入边界耦合、有效度量和频率响应。}
}
$$

同时，还能证明一个看起来反直觉的事实：

$$
\boxed{
\text{同一个局部张量，沿时间方向完全可逆，
换一个切面后却可能只有一维秩。}
}
$$

最后，接回实际 ξ 的历史态，会得到一个新的定量结论：

> **在 RH 前件下，历史态的有限阶秩可以不断增长，但按逆纯度定义的有效维数，对全部时间长度都不超过约 \(28.7549\)。**

这说明“增加了多少独立方向”“多少方向占据主要权重”“换切面以后还能否稳定重建”是三种不同的问题。

下面沿用项目已核对的 `b89d56d0c9a4…` 快照。有限维结论给出证明；涉及实际 ξ 正历史态的地方明确保留 RH 前件，新增接口尚未进行 Lean 编译。

# 一、统一对象不再是一个状态，而是带约束的事件网络

设一段有限计算有事件顶点集合 \(V\)。每条有向边

$$
e:u\to v
$$

携带一个状态搬运算子 \(U_e\)，以及正权重 \(c_e\)。

这里先讨论 \(U_e\) 为幺正的模型。经典不可逆步骤需要先保留足够历史，才能嵌入这一框架；不能直接把多对一计算当成幺正演化。

给每个顶点分配一个数据向量 \(\psi_v\)，定义

$$
\boxed{
\mathcal E(\Psi)
=
\sum_{e:u\to v}
c_e\|\psi_v-U_e\psi_u\|^2.
}
\tag{1}
$$

把所有顶点数据合成 \(\Psi\)，可写成

$$
\mathcal E(\Psi)=\langle\Psi,H\Psi\rangle,
\qquad
H=D_U^*D_U\succeq0.
$$

于是

$$
\boxed{
\mathcal E(\Psi)=0
\iff
\psi_v=U_e\psi_u
\quad\text{对全部边成立}.
}
\tag{2}
$$

这个对象同时包含了数据位置与传播步骤。

但必须保留一点：**\(H\) 记录传播一致性，不自动决定哪端是因、哪端是果。**对于可逆边，反向搬运也能写出同一平方误差；因果朝向仍由事件定向、初始条件和操作协议指定。

现在可以在同一个整体上选不同“切面”：

* 把张量的另一组指标当成输入和输出；
* 只保留一组边界顶点，消去内部事件；
* 从零频约束换到完整频率响应；
* 在历史态中，改为读取时钟侧或数据侧。

这些操作保留的信息不同。**统一不等于所有切面都具有同样的可逆性、归一化或局部性。**

# 二、第一种新切面：交换张量指标，为什么不自动交换成合法时间？

考虑一个作用在两个 \(d\) 维寄存器上的量子门：

$$
U_{cd,ab}.
$$

沿通常的时间方向，它把输入 \((a,b)\) 映为输出 \((c,d)\)。

现在换切面，定义重排矩阵

$$
\boxed{
R(U)_{(c,a),(d,b)}=U_{cd,ab}.
}
\tag{3}
$$

四阶张量的数据没有改变，但“哪些指标组成输入”变了。

原来的条件是

$$
U^*U=I.
$$

新切面要成为幺正演化，还必须另外满足

$$
\boxed{
R(U)^*R(U)=I.
}
\tag{4}
$$

这就是双幺正结构的基本思想。它是额外约束，不是普通幺正性的自动推论。相关研究正是通过要求同一门在空间与时间两个方向都幺正，获得特殊的可解电路。([arXiv][1])

## 定理一：时间方向始终合法，另一切面可以经历秩临界

令 \(S\) 为交换门：

$$
S|a,b\rangle=|b,a\rangle.
$$

定义

$$
\boxed{
U_\theta=\cos\theta\,I+i\sin\theta\,S.
}
\tag{5}
$$

因为 \(S=S^*\)、\(S^2=I\)，所以 \(U_\theta\) 对每个实数 \(\theta\) 都幺正。

但其重排矩阵的奇异值为

$$
\boxed{
\sqrt{d^2\cos^2\theta+\sin^2\theta}
}
$$

一次，以及

$$
\boxed{
|\sin\theta|
}
$$

共 \(d^2-1\) 次。

### 证明

令未归一化向量

$$
|\Omega\rangle=\sum_{a=0}^{d-1}|a,a\rangle.
$$

直接检查指标：

$$
R(I)=|\Omega\rangle\langle\Omega|,
\qquad
R(S)=S.
$$

因此

$$
R(U_\theta)
=
\cos\theta\,|\Omega\rangle\langle\Omega|
+i\sin\theta\,S.
$$

在 \(|\Omega\rangle\) 方向，本征值是

$$
d\cos\theta+i\sin\theta.
$$

在其正交补上，第一项消失，交换门的本征值为 \(\pm1\)，所以奇异值均为 \(|\sin\theta|\)。证毕。

于是：

$$
\theta=0:
\quad U_\theta=I\text{ 完全可逆，但 }R(U_\theta)\text{ 只有秩 }1;
$$

$$
\theta=\frac\pi2:
\quad R(U_\theta)\text{ 也幺正};
$$

$$
0<|\theta|\ll1:
\quad R(U_\theta)\text{ 可逆但条件数很大}.
$$

具体地，

$$
\boxed{
\operatorname{cond}_2R(U_\theta)
=
\sqrt{1+d^2\cot^2\theta}.
}
\tag{6}
$$

**因此，一个切面中的“平稳合法”，可以对应另一个切面中的“接近不可重建”。**

这里的临界来自指标重组后的秩与奇异值，不是原时间演化失去幺正性。

## 5040 还给出一个直接的维数障碍

其因数寄存器空间是

$$
\mathcal H_{5040}
=
\mathbb C^5\otimes
\mathbb C^3\otimes
\mathbb C^2\otimes
\mathbb C^2.
$$

这是 \((4,2,1,1)\) 四个指数各自允许取值数的乘积。Zeckendorf 只是对这些状态作可逆编码；项目的素数轴等价明确保存这一语义。

把一个整体态看成四腿张量，三种二对二切分的维数分别是

$$
\boxed{
15\mid4,\qquad10\mid6,\qquad10\mid6.
}
\tag{7}
$$

两侧都不等维。

因此，**不能把这些切分任意解释为两侧之间的幺正演化**。从小空间到大空间可以存在等距嵌入，但要双向无损且满射，维数必须相同。

这不否认整个六十维空间可以有 \(60\times60\) 的幺正动力学；它只否定“任意横切一下就得到另一种合法时间”。

# 三、第二种新切面：消去内部历史，把全部关系留在边界

假设同一个 Hermitian 二次型按边界变量 \(x\) 与内部变量 \(y\) 分块：

$$
K=
\begin{pmatrix}
A&B\\
B^*&C
\end{pmatrix},
\qquad C\succ0.
$$

## 定理二：边界有效几何由 Schur 补唯一确定

$$
\boxed{
\min_y
\begin{pmatrix}x\\y\end{pmatrix}^{\!*}
K
\begin{pmatrix}x\\y\end{pmatrix}
=
x^*Sx,
\qquad
S=A-BC^{-1}B^*.
}
\tag{8}
$$

### 证明

配方：

$$
\begin{aligned}
\begin{pmatrix}x\\y\end{pmatrix}^{\!*}
K
\begin{pmatrix}x\\y\end{pmatrix}
={}&x^*Sx\\
&+
(y+C^{-1}B^*x)^*
C
(y+C^{-1}B^*x).
\end{aligned}
$$

第二项在

$$
y=-C^{-1}B^*x
$$

处达到零。证毕。

这里消去的是**给定边界时的内部二次能量最小化**，不是未经说明地把内部变量求和、取迹或丢弃。

图网络中的这种边界约化通常称为 Kron 约化；它保存的是指定的边界响应，而不是全部内部微观信息。([arXiv][2])

项目已有的 `SchurComplementAssociativity.lean` 正好保证：在所列逆算子前件下，分步消去与一次消去得到同一个保留算子。

**因此，换边界切面不是把被删部分设为零，而是把它转成**

$$
\boxed{-BC^{-1}B^*}
$$

**这项诱导耦合。**

# 四、时间链压成两个端点以后，时钟会变成一个耦合系数

考虑 \(L\) 条连续传播边：

$$
\psi_0\to\psi_1\to\cdots\to\psi_L.
$$

第 \(j\) 条边的搬运为 \(U_j\)，给定正时间成本 \(\tau_j\)。选择作用量

$$
\boxed{
\mathcal E=
\sum_{j=0}^{L-1}
\frac{\|\psi_{j+1}-U_j\psi_j\|^2}{\tau_j}.
}
\tag{9}
$$

这是与串联细分相容的一种数学归一化；它不声称计算微步成本已经等于真实物理时间。

记

$$
\mathcal U=U_{L-1}\cdots U_0,
\qquad
\tau_{\mathrm{tot}}=\sum_{j=0}^{L-1}\tau_j.
$$

## 定理三：整段历史的精确双端点读出

固定端点

$$
\psi_0=x,\qquad\psi_L=y.
$$

则

$$
\boxed{
\min_{\psi_1,\ldots,\psi_{L-1}}\mathcal E
=
\frac{\|y-\mathcal Ux\|^2}{\tau_{\mathrm{tot}}}.
}
\tag{10}
$$

### 证明

作逐步幺正坐标变换，把所有 \(U_j\) 消去。问题变成：在固定总位移 \(d\) 下，最小化

$$
\sum_j\frac{\|\Delta_j\|^2}{\tau_j},
\qquad
\sum_j\Delta_j=d.
$$

由加权 Cauchy–Schwarz，

$$
\|d\|^2
\le
\left(\sum_j\tau_j\right)
\left(\sum_j\frac{\|\Delta_j\|^2}{\tau_j}\right).
$$

当

$$
\Delta_j=\frac{\tau_j}{\tau_{\mathrm{tot}}}d
$$

时取等号。再变回原坐标即可。证毕。

---

所以边界矩阵为

$$
\boxed{
S_{\mathrm{path}}
=
\frac1{\tau_{\mathrm{tot}}}
\begin{pmatrix}
I&-\mathcal U^*\\
-\mathcal U&I
\end{pmatrix}.
}
\tag{11}
$$

它同时记录：

$$
\boxed{
\mathcal U:\text{传播结果};
\qquad
\tau_{\mathrm{tot}}:\text{传播成本}.
}
$$

串联两段路径时，

$$
\boxed{
(\mathcal U_2,\tau_2)\circ(\mathcal U_1,\tau_1)
=
(\mathcal U_2\mathcal U_1,\tau_1+\tau_2).
}
\tag{12}
$$

**只保留 \(\mathcal U\)，就保存了事件结果，却删除了时钟。把式（11）任意归一化，也可能把 \(\tau_{\mathrm{tot}}\) 一起抹掉。**

这给前文 PRIMEGAME 的宏步压缩一个更准确的要求：不只保存返回状态，还要保存返回时间；这两项在新的边界切面中可以进入不同系数。

# 五、两条时空路径拼起来，曲折程度与时长必须分开衡量

现在让同一对端点之间有两条内部互不重叠的路径。它们分别具有

$$
(\mathcal U_1,\tau_1),
\qquad
(\mathcal U_2,\tau_2).
$$

消去各自内部后，固定起点 \(x\)，总能量为

$$
\frac{\|y-\mathcal U_1x\|^2}{\tau_1}
+
\frac{\|y-\mathcal U_2x\|^2}{\tau_2}.
$$

再消去共同终点 \(y\)。

## 定理四：闭环不相容的精确代价

$$
\boxed{
\min_y\mathcal E
=
\frac{\|(\mathcal U_1-\mathcal U_2)x\|^2}
{\tau_1+\tau_2}.
}
\tag{13}
$$

### 证明

两个平方项的加权平均最优点为

$$
y=
\frac{\tau_2\mathcal U_1x+\tau_1\mathcal U_2x}
{\tau_1+\tau_2}.
$$

代回即得。证毕。

定义两条路径的相对回返算子

$$
\Omega=\mathcal U_1^*\mathcal U_2.
$$

则

$$
\boxed{
(\tau_1+\tau_2)\min_y\mathcal E
=
\|(I-\Omega)x\|^2.
}
\tag{14}
$$

若只有一个标量相位

$$
\Omega=e^{i\Theta},
$$

且 \(\|x\|=1\)，就得到

$$
\boxed{
\min_y\mathcal E
=
\frac{4\sin^2(\Theta/2)}{\tau_1+\tau_2}.
}
\tag{15}
$$

这一次固定的是起点范数，与前文“整条历史总范数为一”的最低本征值归一化不同。

## 一个新的误判风险

即使保持

$$
\Theta=\pi,
$$

使两条路径始终完全相反，只要把路径时间不断延长，

$$
\min_y\mathcal E
=
\frac4{\tau_1+\tau_2}
\longrightarrow0.
$$

因此：

$$
\boxed{
\text{拼接能量很小}
\not\Rightarrow
\text{闭环相位接近零}.
}
\tag{16}
$$

小能量可能只是失配被摊到更长历史中。

要判断两条路径是否接近同一个搬运，应该同时保留

$$
\boxed{
\text{未归一化残差、路径时长、归一化闭环缺陷}.
}
$$

这正是“在其他切面分析”能够暴露的新信息：**同一失配，在端点面上看似很小，在闭环面上仍然是固定的。**

# 六、第三种新切面：从零频边界，转向完整频率响应

式（8）只保存静态二次能量。若研究约束算子 \(K\) 的谱或线性响应，需要保留谱参数 \(z\)。

仍令

$$
K=
\begin{pmatrix}
A&B\\
B^*&C
\end{pmatrix}.
$$

定义

$$
\boxed{
S(z)=A-zI-B(C-zI)^{-1}B^*.
}
\tag{17}
$$

在相应逆都存在时，

$$
\boxed{
P_{\partial}(K-zI)^{-1}P_{\partial}^*
=
S(z)^{-1}.
}
\tag{18}
$$

这里 \(z\) 是该算子的谱参数，不能自动等同于 FRACTRAN 的微步编号。

## 定理五：消去历史以后，还会产生一个新的边界度量

若

$$
C\succeq\Delta I,\qquad\Delta>0,
$$

则在 \(|z|<\Delta\) 内，

$$
\boxed{
S(z)=S(0)-zM_{\mathrm{eff}}+R(z),
}
\tag{19}
$$

其中

$$
\boxed{
M_{\mathrm{eff}}
=
I+BC^{-2}B^*\succ0,
}
\tag{20}
$$

并且

$$
\boxed{
\|R(z)\|
\le
\frac{\|B\|^2|z|^2}
{\Delta^2(\Delta-|z|)}.
}
\tag{21}
$$

### 证明

使用恒等式

$$
(C-zI)^{-1}
=
C^{-1}+zC^{-2}
+z^2C^{-2}(C-zI)^{-1}.
$$

代入式（17），再使用

$$
\|(C-zI)^{-1}\|
\le\frac1{\Delta-|z|}
$$

即可。证毕。

---

这意味着：

$$
\boxed{
\text{压缩到边界后，不只有一个新耦合 }S(0)，
\text{还有一个新的范数／质量矩阵 }M_{\mathrm{eff}}.
}
$$

这不是装饰项。

对长度为 \(L\) 的单位边权标量链，端点的静态矩阵为

$$
S(0)=
\frac1L
\begin{pmatrix}
1&-1\\
-1&1
\end{pmatrix}.
$$

而有效度量为

$$
\boxed{
M_{\mathrm{eff}}
=
\frac1{6L}
\begin{pmatrix}
(L+1)(2L+1)&L^2-1\\
L^2-1&(L+1)(2L+1)
\end{pmatrix}.
}
\tag{22}
$$

### 为什么是这个矩阵？

固定端点 \(x,y\) 后，最小能量内部状态是线性插值

$$
\psi_t=
\left(1-\frac tL\right)x+\frac tL y.
$$

将整段历史的平方范数

$$
\sum_{t=0}^L|\psi_t|^2
$$

写成关于 \((x,y)\) 的二次型，正好得到式（22）。

所以：

$$
S(0)\text{ 的尺度约为 }L^{-1},
$$

$$
M_{\mathrm{eff}}\text{ 的尺度约为 }L.
$$

**删除了 \(L-1\) 个内部时刻，不意味着这些时刻对范数和谱的贡献消失。**

而内部 Dirichlet 块的最小本征值是

$$
\Delta=
2-2\cos\frac\pi L
\asymp L^{-2}.
$$

因此，式（19）的低频展开在长历史上只有越来越窄的统一有效区域。只保留 \(S(0)\)，不能声称保留了整个传播谱。

这给“临界附近为什么难以拼接”一个新的定量来源：

$$
\boxed{
\text{内部谱间隙变小}
\longrightarrow
\text{消元的逆算子变大}
\longrightarrow
\text{边界响应对频率与误差更敏感}.
}
\tag{23}
$$

# 七、第四种新切面：同一个 ξ 历史态，分别看时钟侧与数据侧

现在接回前文的实际算术读出。

定义 Li 系数

$$
\log\frac{\xi(1/(1-z))}{\xi(1)}
=
\sum_{n\ge1}\frac{\ell_n}{n}z^n,
$$

以及

$$
c_0=2\ell_1
=
2+\gamma_{\mathrm E}-\log(4\pi),
$$

$$
c_n=\ell_{n+1}-2\ell_n+\ell_{n-1},
\qquad
r_n=\frac{c_n}{c_0}.
$$

Li 系数的零点表达、单位圆映射及与 Weil 正性的联系具有经典依据。([arXiv][3])

**本节明确假设 RH。**

把不同零点记为 \(\rho_j\)，重数为 \(m_j\)，定义

$$
w_j=1-\frac1{\rho_j},
$$

$$
\boxed{
p_j=\frac{m_j}{c_0|\rho_j|^2}.
}
\tag{24}
$$

在 RH 下，

$$
|w_j|=1,\qquad
p_j>0,\qquad
\sum_jp_j=1,
$$

且

$$
r_n=\sum_jp_jw_j^n.
$$

令

$$
U|j\rangle=w_j|j\rangle,
\qquad
|v\rangle=\sum_j\sqrt{p_j}|j\rangle.
$$

构造历史态

$$
\boxed{
|\Psi_N\rangle
=
\frac1{\sqrt{N+1}}
\sum_{t=0}^N
|t\rangle\otimes U^t|v\rangle.
}
\tag{25}
$$

## 时间侧与数据侧是互补切面

对数据取迹：

$$
\boxed{
\rho_{\mathrm{clock}}
=
\frac{T_N}{N+1},
\qquad
T_N=(r_{j-i})_{0\le i,j\le N}.
}
\tag{26}
$$

对时钟取迹：

$$
\boxed{
\rho_{\mathrm{data}}
=
\frac1{N+1}
\sum_{t=0}^N
U^t|v\rangle\langle v|U^{-t}.
}
\tag{27}
$$

两者具有相同的非零本征值。

### 证明

把 \(|\Psi_N\rangle\) 的系数写成矩阵 \(M\)。两个约化密度矩阵分别是 \(MM^*\) 与其另一侧对应的 Gram 矩阵，因此非零本征值都是 \(M\) 的奇异值平方。证毕。

所以：

$$
\boxed{
\text{时间相关矩阵的非零谱}
=
\text{数据侧混合状态的非零谱}.
}
\tag{28}
$$

这才是严格的“换切面后仍读取同一个整体”。

# 八、新的定量结果：秩无限增长，但有效维数始终有界

定义纯度

$$
\mathcal P_N
=
\operatorname{Tr}(\rho_{\mathrm{clock}}^2)
=
\operatorname{Tr}(\rho_{\mathrm{data}}^2),
$$

以及逆纯度意义下的有效维数

$$
\boxed{
d_{\mathrm{eff}}(N)=\frac1{\mathcal P_N}.
}
\tag{29}
$$

它不是矩阵秩，也不必是整数。

由式（26），

$$
\boxed{
\mathcal P_N
=
\frac{
(N+1)+2\sum_{k=1}^N(N+1-k)|r_k|^2
}{(N+1)^2}.
}
\tag{30}
$$

从数据切面看，则有

$$
\boxed{
\mathcal P_N
=
\sum_{j,k}p_jp_k
\left|
\frac1{N+1}\sum_{t=0}^N(w_j\overline{w_k})^t
\right|^2.
}
\tag{31}
$$

## 定理六：ξ 历史态的统一有效维数界

在 RH 前件下，对全部 \(N\ge0\)，

$$
\boxed{
d_{\mathrm{eff}}(N)
\le
\frac{c_0^2}{2(c_0-c_1)}
\approx28.7548583457.
}
\tag{32}
$$

同时，

$$
\boxed{
\operatorname{rank}T_N=N+1.
}
\tag{33}
$$

### 证明有效维数界

式（31）的全部项非负，保留 \(j=k\) 项，得到

$$
\mathcal P_N\ge\sum_jp_j^2.
$$

在临界线上，

$$
\operatorname{Re}w_j
=
1-\frac1{2|\rho_j|^2}.
$$

因此

$$
\boxed{
2(c_0-c_1)
=
\sum_j\frac{m_j}{|\rho_j|^4}.
}
\tag{34}
$$

而

$$
\sum_jp_j^2
=
\frac1{c_0^2}
\sum_j\frac{m_j^2}{|\rho_j|^4}
\ge
\frac1{c_0^2}
\sum_j\frac{m_j}{|\rho_j|^4}.
$$

结合式（34）即可。

### 证明秩持续增长

在 RH 下，谱测度具有无限多个不同的支撑点 \(w_j\)。非零有限次多项式不可能在全部这些点上为零。

所以

$$
1,z,\ldots,z^N
$$

在该谱测度下线性独立，Gram 矩阵 \(T_N\) 严格正定，秩为 \(N+1\)。这里使用了实际 ζ 有无限多个不同非平凡零点的经典事实。([DLMF][4])

证毕。

---

这揭示了一个很重要的几何结构：

$$
\boxed{
\text{严格独立的方向不断增加，主要权重却不必均匀扩散到所有方向。}
}
\tag{35}
$$

所以不能从“时间越来越长、矩阵越来越大”直接推断“有效自由度按时间线性增长”。

## 无限时间极限也可以计算

对 \(j\ne k\)，因为 \(w_j\ne w_k\)，

$$
\frac1{N+1}\sum_{t=0}^N(w_j\overline{w_k})^t\longrightarrow0.
$$

由可求和权重的支配收敛，

$$
\boxed{
\lim_{N\to\infty}\mathcal P_N
=
\sum_jp_j^2.
}
\tag{36}
$$

若再额外假设所有非平凡零点简单，\(m_j=1\)，则式（32）的极限取等号：

$$
\boxed{
\lim_{N\to\infty}d_{\mathrm{eff}}(N)
=
\frac{c_0^2}{2(c_0-c_1)}.
}
\tag{37}
$$

**简单零点条件不是 RH 的组成部分，不能省略。**没有该条件时，式（32）的上界仍成立。

这个结果也不能解释成“ξ 其实只有二十九个状态”。式（33）已经明确否定这种精确有限维化。

本轮仅从系数计算得到

$$
c_0\approx0.0461914179322421,
$$

$$
c_1\approx0.0461543172958046,
$$

并用 \(60\) 与 \(90\) 位工作精度交叉核对了式（32）的数值。这不是区间认证，更不是 RH 证据。

# 九、换到谱切面，空间截断误差与时间相位误差也能分开

上面的有效维数界还不能单独保证固定维数近似足够准确。纯度只衡量权重集中程度，不等于完整尾部界。

但对当前 RH 条件下的谱，可以直接控制尾部。

保留高度满足

$$
|\Im\rho_j|\le G
$$

的谱点，并用投影 \(P_G\) 截断数据侧。

由于 \(P_G\) 与 \(U\) 对易，

$$
\boxed{
\|(I\otimes(I-P_G))\Psi_N\|^2
=
\sum_{|\Im\rho_j|>G}p_j.
}
\tag{38}
$$

右边与历史长度 \(N\) 无关。

由零点计数

$$
N_\zeta(G)=O(G\log G)
$$

及分部求和，

$$
\boxed{
\sum_{|\Im\rho_j|>G}p_j
=
O\!\left(\frac{\log G}{G}\right).
}
\tag{39}
$$

所用零点计数及更强的显式界已有文献。([arXiv][5])

这说明：**保留精确频率时，谱尾部截断可以在全部历史长度上具有统一范数误差。**

但是，如果保留的每个相位存在误差

$$
|\widetilde\theta_j-\theta_j|\le\delta,
$$

那么第 \(t\) 步的相位偏差满足

$$
|e^{it\widetilde\theta_j}-e^{it\theta_j}|
\le t\delta.
$$

因此，对保留部分构造的历史态，有

$$
\boxed{
\|\widetilde\Psi_N-\Psi_N^{(\le G)}\|
\le
\delta\sqrt{\frac{N(2N+1)}6}.
}
\tag{40}
$$

再加上谱尾部，

$$
\boxed{
\|\widetilde\Psi_N-\Psi_N\|
\le
O\!\left(\sqrt{\frac{\log G}{G}}\right)
+
\delta\sqrt{\frac{N(2N+1)}6}.
}
\tag{41}
$$

这里截断态未额外归一化，便于保留精确误差账目。

所以，从另一切面看：

$$
\boxed{
\text{空间／谱截断误差可以不随时间增长；}
}
$$

$$
\boxed{
\text{频率数值误差却会随时间积累。}
}
\tag{42}
$$

这正是统一离散时空分析必须保留的两项不同预算。

# 十、回到实际正性：什么样的换切面不会把失败藏起来？

前面构造的传播能量

$$
D_U^*D_U
$$

天然半正定，但不能拿它替代一个尚未证明正性的实际算术二次型。

对实际 ξ，我们仍需处理由实际 \(r_n\) 决定的

$$
T_N=(r_{j-i}).
$$

如果某一组待消去的内部块 \(C\) 已经严格认证为正定，那么式（8）的配方给出：

$$
\boxed{
T_N\succeq0
\iff
S\succeq0.
}
\tag{43}
$$

不仅如此，负方向也可精确运输。

若

$$
x^*Sx<0,
$$

令

$$
\boxed{
\widehat x=
\begin{pmatrix}
x\\
-C^{-1}B^*x
\end{pmatrix}.
}
$$

则

$$
\boxed{
\widehat x^*T_N\widehat x=x^*Sx<0.
}
\tag{44}
$$

所以，在这些前件下，消去内部不是隐藏失败，而是将失败完整留在边界。

但若只是取一个主子矩阵或删除某些状态，负方向就可能被丢掉。例如

$$
\begin{pmatrix}-1&0\\0&1\end{pmatrix}
$$

只保留第二个坐标后，得到的当然是正数 \(1\)。

因此，需要区分：

$$
\boxed{
\text{限制到一个切片};
\quad
\text{取约化密度矩阵};
\quad
\text{Schur 消元};
\quad
\text{张量指标重排}.
}
\tag{45}
$$

它们不是同一种“投影”。

项目的动态闭包证明了怎样最小地保留所有有限操作之后的读出；Schur 模块则证明了在指定逆算子条件下，分步与整体消元一致。两者提供的是不同接口，不能相互替代。

# 十一、统一框架应当记录“切面变换的证书”，而不仅记录一个新坐标

现在可以把整个研究方向组织为：

$$
\boxed{
\text{实际离散历史}
\longrightarrow
\text{不同切面上的表示}
\longrightarrow
\text{切面之间的精确桥梁}
\longrightarrow
\text{随尺度变化的误差与临界量}.
}
\tag{46}
$$

对每一种切面，至少要说明它保留了什么：

| 切面操作      | 必须检查的条件             | 容易遗漏的量     |
| --------- | ------------------- | ---------- |
| 空间—时间指标重排 | 维数、秩、奇异值、额外幺正条件     | 不可恢复方向与逆放大 |
| 消去内部历史    | 内部块可逆、Schur 相容      | 诱导耦合与总时长   |
| 从静态转到频率响应 | 保留 \(S(z)\) 或控制展开余项 | 有效度量、内部共振  |
| 时钟侧与数据侧互换 | 来自同一个整体历史态          | 非对角相干与共同谱  |
| 实际算术降维    | 负方向能否被完整运输          | 被切片删除的失败证书 |

本轮已经完成了这些有限核对：部分交换门在不同切面下的奇异值、带权时间链的边界约化、双路径回返残差、有效边界度量、频率展开余项、Schur 负方向运输，以及互补切面的纯度一致性。

整数维数和线性插值质量矩阵使用了精确算术；一般矩阵检查为浮点复核。可复现代码见[核验脚本](sandbox:/mnt/data/spacetime_recuts_boundary_verify.py)，结果见[核验记录](sandbox:/mnt/data/spacetime_recuts_boundary_verify.json)。它们不构成 RH 证明。

# 结论

这次真正把“其他切面”推进成了四条可计算的连接：

$$
\boxed{
\text{换指标分组}
\longrightarrow
\text{新的秩与奇异值边界};
}
$$

$$
\boxed{
\text{压缩时间链}
\longrightarrow
\frac{\|y-\mathcal Ux\|^2}{\tau_{\mathrm{tot}}};
}
$$

$$
\boxed{
\text{消去内部事件}
\longrightarrow
S(0),\ M_{\mathrm{eff}},\ S(z);
}
$$

$$
\boxed{
\text{ξ 历史态换到数据侧}
\longrightarrow
\text{同一非零谱与新的有效维数约束}.
}
$$

其中最值得继续保留的两个认识是：

**第一，时间并不只能表现为一个外部序号。压缩以后，它可以变成边界耦合的倒数、历史范数的权重或频率依赖。**

**第二，切面中的临界不一定代表整体发生灾变。它可能是这个切面失去可逆性、内部模式变得难以消去，或者原来隐藏的相关被重新暴露出来。**

对实际 ξ 而言，本轮的新结论仍带有清楚前件：

$$
\boxed{
\mathrm{RH}
\Longrightarrow
\operatorname{rank}T_N=N+1,
\qquad
d_{\mathrm{eff}}(N)\le28.754858\ldots
}
$$

它说明同一整体可以同时具有无限增长的精确秩与有限的主要权重尺度，但不反过来证明 RH。

因此，接下来的核心算术责任不是寻找一个“看起来最平坦、最正、最容易算”的切面，而是证明：

$$
\boxed{
\text{换到那个切面以后，实际失败模式没有被删除，
时间与相关的代价也没有被归一化掉。}
}
$$

只有满足这条条件，多切面分析才是在揭示同一个离散时空整体，而不是每次换到一个更容易成立、却已经不同的问题。

[1]: https://arxiv.org/html/2201.07768v3 "https://arxiv.org/html/2201.07768v3"
[2]: https://arxiv.org/html/1102.2950v1 "https://arxiv.org/html/1102.2950v1"
[3]: https://arxiv.org/html/2301.05779v2 "https://arxiv.org/html/2301.05779v2"
[4]: https://dlmf.nist.gov/25.10 "https://dlmf.nist.gov/25.10"
[5]: https://arxiv.org/html/2412.15470v1 "https://arxiv.org/html/2412.15470v1"
