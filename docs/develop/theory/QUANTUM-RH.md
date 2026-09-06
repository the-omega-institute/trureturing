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
