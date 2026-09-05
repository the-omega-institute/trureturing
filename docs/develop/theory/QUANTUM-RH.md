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
