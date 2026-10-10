# Auric FIB-ATOM：局部生成规则的反演与闭环修正

**来源与范围。** 本卷固定项目读取快照 `d856565`，研究带相邻排斥的有限 FIB 位置来源。原生五模式、活动权、严格接缝和相干记录分别属于不同层；本卷只在明确声明的经典概率模型内作普通数学推导。理论正文是参考输入，Lean 代码才是仓库的数学真值来源；本卷不声称 Lean 已验证这些命题。

## 1. 五模式中的两种自由度

令

$$
\Sigma_3=\{\mathsf F[\varnothing],\mathsf F[1],\mathsf F[2],\mathsf F[3],\mathsf F[1,3]\},
$$

并按实际位置写成 $b_1,b_2,b_3\in\{0,1\}$，满足

$$
b_1b_2=b_2b_3=0.
$$

平均坐标为

$$
(X,Y,Z)=(\mathbb E b_1,\mathbb E b_3,\mathbb E b_2).
$$

### theorem 1.1: 一阶均值的关联纤维

**Claim status: open.** 对任意合法五模式概率律，令 $\kappa=\mathbb E[b_1b_3]$。则

$$
\max(0,X+Y+Z-1)\le \kappa\le\min(X,Y).
$$

这些不等式精确给出三个均值的全部合法补全范围。

**证明。** 由非负事件 $b_1b_3$、$1-b_1-b_3-b_2+b_1b_3$ 以及 $b_1-b_1b_3$、$b_3-b_1b_3$ 取期望，得到四个界。把任一端点代入五模式概率反解，所得五个概率仍非负，因此端点可达。证毕。

这说明合法来源空间仍有一项联合自由度。若另行声明乘积活动权模型

$$
P(b_1,b_2,b_3)\propto a^{b_1}b^{b_2}c^{b_3}\mathbf1_{\{b_1b_2=b_2b_3=0\}},
$$

其五个权重为 $1,a,b,c,ac$，于是

$$
p_{\varnothing}p_{13}=p_1p_3,
\qquad
\kappa=\frac{XY}{1-Z}.
$$

这里是生成规则排除了纤维中的其他分布，而不是三个均值本身创造了缺失信息。

## 2. 开放位置链的局部 Markov 重建

### 定义 2.1：合法链与局部表

对 $N\ge2$，令

$$
\Sigma_N=\{b\in\{0,1\}^N:b_ib_{i+1}=0\ (1\le i<N)\}.
$$

给定位置均值 $u_i=\mathbb E[b_i]$，并在严格内部假设

$$
0<u_i<1,
\qquad r_i=1-u_i-u_{i+1}>0.
$$

每条相邻边的完整二元表由均值唯一决定：

$$
\Pi_i=
\begin{pmatrix}
r_i&u_{i+1}\\
u_i&0
\end{pmatrix},
\qquad
\pi_i=(1-u_i,u_i).
$$

### theorem 2.2: 一阶 Markov 补全的存在与唯一性

**Claim status: open.** 定义

$$
P_u^*(b_1,\ldots,b_N)=
\frac{\prod_{i=1}^{N-1}\Pi_i(b_i,b_{i+1})}
{\prod_{i=2}^{N-1}\pi_i(b_i)}.
$$

则它是归一化的合法来源，具有给定的全部均值。并且在满足

$$
\Pr(b_{i+1}\mid b_1,\ldots,b_i)=\Pr(b_{i+1}\mid b_i)
$$

的一阶 Markov 来源中，它是唯一的。

**证明。** 令

$$
T_i=
\begin{pmatrix}
\dfrac{r_i}{1-u_i}&\dfrac{u_{i+1}}{1-u_i}\\[2mm]
1&0
\end{pmatrix}.
$$

每行和为一，且 $\pi_iT_i=\pi_{i+1}$。从 $\pi_1$ 出发依次使用这些转移，得到归一化链律并恢复所有边缘。任意具有同样边缘的一阶 Markov 来源，其条件转移必须等于 $\Pi_i/\pi_i$，故唯一。证毕。

分母只消除每个内部位置被左右两条边重复计入的一次。边界余量趋于零时，这个表达式可能变得病态；边界支撑必须另行处理。

## 3. 均值到单位置活动权的反演

### 定义 3.1：单位置活动权模型

给定 $w_i>0$，定义

$$
P_w(b)=\frac1{\mathcal Z_N(w)}\prod_{i=1}^Nw_i^{b_i},
\qquad b\in\Sigma_N,
$$

其中

$$
\mathcal Z_N(w)=\sum_{b\in\Sigma_N}\prod_iw_i^{b_i}.
$$

这是一个额外的来源模型假设，不是相邻排斥合法性的同义词。

### theorem 3.2: 活动权与均值的双向对应

**Claim status: open.** 约定 $u_0=u_{N+1}=0$，$r_i=1-u_i-u_{i+1}$。在严格内部条件下，

$$
\boxed{
w_i=\frac{u_i(1-u_i)}{r_{i-1}r_i}
}
$$

并且

$$
\boxed{
\mathcal Z_N=
\frac{\prod_{i=2}^{N-1}(1-u_i)}{\prod_{i=1}^{N-1}r_i}.
}
$$

因此各位置均值唯一确定这份已声明的乘积权模型。

**证明。** 使用 theorem 2.2 的 Markov 补全。把允许配置中位置 $i$ 从零改成一，比较相邻两张表和公共单位置分母的比值，得到 $u_i(1-u_i)/(r_{i-1}r_i)$。任何合法配置都可从全零配置逐个加入其选中位置，因此 $P_u^*(b)=P_u^*(0)\prod_iw_i^{b_i}$。全零概率为

$$
P_u^*(0)=\frac{\prod_{i=1}^{N-1}r_i}{\prod_{i=2}^{N-1}(1-u_i)},
$$

从而得到配分函数。反向地，乘积权模型固定中间位后左右权重分开，满足 Markov 条件，唯一性完成反演。证毕。

三位置中令 $(u_1,u_2,u_3)=(X,Z,Y)$，便有

$$
a=\frac{X}{1-X-Z},
\qquad
b=\frac{Z(1-Z)}{(1-X-Z)(1-Y-Z)},
\qquad
c=\frac{Y}{1-Y-Z}.
$$

## 4. Markov 补全遗漏的关系

### theorem 4.1: 熵差等于条件互信息总和

**Claim status: open.** 设 $P$ 是任意合法链概率，并具有与 $P_u^*$ 相同的全部位置均值。以自然对数定义相对熵，则

$$
\boxed{
D(P\Vert P_u^*)=H(P_u^*)-H(P)
}
$$

以及

$$
\boxed{
D(P\Vert P_u^*)=
\sum_{i=2}^{N-1}I_P(b_{i+1};b_1,\ldots,b_{i-1}\mid b_i).
}
$$

因此 $P=P_u^*$ 当且仅当这些“过去仍影响下一步”的条件互信息全部为零。

**证明。** $\log P_u^*$ 是相邻二位函数之和减去共同单位置函数。$P$ 与 $P_u^*$ 具有相同边缘，所以 $\mathbb E_P[\log P_u^*]=\mathbb E_{P_u^*}[\log P_u^*]$，相对熵等于熵差。再分别使用 Markov 链的熵分解和任意链律的链式法则，逐项相减即得条件互信息和。证毕。

五位置的例子可把 $b_2=b_4=0$，只在 $(b_1,b_3,b_5)$ 的偶数子集上均匀分布，或在三个活动位独立均匀分布。两者的一阶、相邻二阶、连续三位置分布相同，但来源数分别为四和八，熵差为 $\log 2$。差异保存在三方奇偶关系中。

## 5. 协方差的逆显露局部骨架

令 $C_{ij}=\operatorname{Cov}(b_i,b_j)$，$\theta_i=\log w_i$。配分函数给出

$$
u_i=\frac{\partial\log\mathcal Z_N}{\partial\theta_i},
\qquad
C_{ij}=\frac{\partial^2\log\mathcal Z_N}{\partial\theta_i\partial\theta_j}.
$$

### theorem 5.1: 逆协方差为三对角矩阵

**Claim status: open.** 在严格正活动权模型中，$C$ 正定，且

$$
\boxed{(C^{-1})_{ij}=0\quad(|i-j|>1).}
$$

相邻项与对角项分别为

$$
\boxed{(C^{-1})_{i,i+1}=\frac1{1-u_i-u_{i+1}}}
$$

和

$$
\boxed{(C^{-1})_{ii}=\frac1{u_i}-\frac1{1-u_i}+\frac1{r_{i-1}}+\frac1{r_i}.}
$$

**证明。** 全零配置和单位置配置都具有正概率，故非零线性组合 $\sum_i a_ib_i$ 不可能恒定，$C$ 正定。theorem 3.2 给出均值到 $\theta$ 的可逆映射，故 $C^{-1}=\partial\theta/\partial u$。对

$$
\theta_i=\log u_i+\log(1-u_i)-\log r_{i-1}-\log r_i
$$

直接求导即得三对角式。证毕。

五模式等权时，$u=(2/5,1/5,2/5)$，

$$
C=\frac1{25}\begin{pmatrix}6&-2&1\\-2&4&-2\\1&-2&6\end{pmatrix},
$$

而

$$
C^{-1}=\begin{pmatrix}5&5/2&0\\5/2&35/4&5/2\\0&5/2&5\end{pmatrix}.
$$

两端的协方差为正，但直接逆关系为零。这一稀疏性依赖于已声明的乘积权模型，不能推广到任意只满足排斥的来源律。

## 6. 正交余量与响应体积

令 $R_i=b_i-u_i$，$\alpha_i=-u_{i+1}/(1-u_i)$，并递归定义

$$
E_1=R_1,
\qquad
E_{i+1}=R_{i+1}-\alpha_iR_i.
$$

### theorem 6.1: 逐步扣除后的余量两两正交

**Claim status: open.** 在概率内积 $\langle f,g\rangle=\mathbb E[fg]$ 下，$E_i$ 两两正交，并且

$$
\mathbb E[E_1^2]=u_1(1-u_1),
\qquad
\mathbb E[E_{i+1}^2]=\frac{u_{i+1}r_i}{1-u_i}.
$$

**证明。** 由转移表，

$$
\mathbb E[R_{i+1}\mid b_1,\ldots,b_i]=\mathbb E[R_{i+1}\mid b_i]=\alpha_iR_i.
$$

故 $E_{i+1}$ 对全部过去函数正交。展开方差并使用 $\operatorname{Cov}(b_i,b_{i+1})=-u_iu_{i+1}$，得到所列对角量。证毕。

### theorem 6.2: 响应协方差的行列式

**Claim status: open.** 对 $C=\operatorname{Cov}(b_1,\ldots,b_N)$，有

$$
\boxed{
\det C=\frac{\prod_{i=1}^{N}u_i}{\mathcal Z_N}
=P_u^*(0,\ldots,0)\prod_{i=1}^{N}u_i.
}
$$

**证明。** 从 $R$ 到 $E$ 的变换是单位三角变换，故协方差行列式等于各正交余量方差之积。代入 theorem 6.1 并整理，正好得到 theorem 3.2 的配分函数表达式。证毕。

这里的行列式是中心化响应向量在 $L^2(P)$ 中的 Gram 体积平方，不是三维物理空间的体积。活动权全为一时，$\mathcal Z_N=F_{N+2}$，并且固定位置 $i$ 被选的配置数为 $F_iF_{N-i+1}$，故

$$
u_i=\frac{F_iF_{N-i+1}}{F_{N+2}},
\qquad
\det C=\frac{(F_1F_2\cdots F_N)^2}{F_{N+2}^{N+1}}.
$$

对 $N=3$ 得 $\det C=4/625$。当某条接缝余量 $r_i$ 趋于零时，响应体积趋于零，而逆矩阵的相应敏感度增大；这是同一边界关系的正反两面。

## 追加锚（本行以下为增补区）
