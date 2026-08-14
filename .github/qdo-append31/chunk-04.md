## 31.7 对角自指与动力学的自然性缺陷由层析余质量控制

MUB 对角塔不仅重构状态，还可以控制任意状态操作在有限观察坐标中的降阶误差。

令

\[
P_m:
\operatorname{Herm}_d^0
\to S_m
\]

为正交投影。

设

\[
F:
\operatorname{Herm}_d^0
\to
\operatorname{Herm}_d^0
\]

为 \(L_F\)-Lipschitz 映射：

\[
\|F(X)-F(Y)\|_2
\le
L_F\|X-Y\|_2.
\]

定义其第 \(m\) 层压缩模型

\[
\boxed{
F_m
=
P_mF|_{S_m}.
}
\]

定义自然性缺陷

\[
\boxed{
\partial_mF(X)
=
\|
P_mF(X)
-
F_m(P_mX)
\|_2.
}
\]

### 定理 31.13（余质量控制自然性缺陷）

\[
\boxed{
\partial_mF(X)
\le
L_F
\|(I-P_m)X\|_2.
}
\]

对密度矩阵 \(X=X_\rho\)，

\[
\boxed{
\partial_mF(X_\rho)
\le
L_F
\sqrt{
r_m^{(2)}(\rho)
}.
}
\]

#### 证明

由 \(F_m(P_mX)=P_mF(P_mX)\)，

\[
\partial_mF(X)
=
\|
P_m(F(X)-F(P_mX))
\|_2.
\]

正交投影为收缩，故

\[
\partial_mF(X)
\le
\|F(X)-F(P_mX)\|_2
\le
L_F\|X-P_mX\|_2.
\]

\(\square\)

这条定理把第 30 节的抽象界

\[
\text{自然性缺陷}
\le
\text{观察余量}
\]

在量子层析塔中完全具体化。若 \(F\) 是自指／对角操作，则它控制“先在完整状态空间自指再观察”与“先投影到有限概率坐标再自指”的误差；若 \(F\) 是动力学，则它控制有限观察层的有效演化误差。

在完整 MUB 集存在时，

\[
P_{d+1}=I,
\]

因此

\[
\boxed{
\partial_{d+1}F=0
}
\]

对任意 \(F\) 成立。这里的零缺陷不是因为操作本身简单，而是因为观察坐标已经信息完备，不再有状态余量。

### 定理 31.14（自然性缺陷的复合 Leibniz 界）

设 \(F,G\) 分别具有局部压缩 \(F_m,G_m\)，并且 \(F_m\) 为 \(L_m(F)\)-Lipschitz。则

\[
\boxed{
\partial_m(F\circ G)(X)
\le
\partial_mF(GX)
+
L_m(F)\partial_mG(X),
}
\]

其中局部复合取 \(F_m\circ G_m\)。

#### 证明

插入中间项 \(F_m(P_mGX)\)：

\[
\begin{aligned}
&
\|P_mFGX-F_mG_mP_mX\|_2
\\
&\le
\|P_mFGX-F_mP_mGX\|_2
+
\|F_mP_mGX-F_mG_mP_mX\|_2
\\
&\le
\partial_mF(GX)
+
L_m(F)\partial_mG(X).
\end{aligned}
\]

\(\square\)

### 推论 31.15（时间迭代误差）

若 \(F_m\) 的 Lipschitz 常数不超过 \(L\)，则

\[
\boxed{
\partial_m(F^n)(X)
\le
\sum_{k=0}^{n-1}
L^{n-1-k}
\partial_mF(F^kX).
}
\]

若沿轨道单步缺陷均不超过 \(\varepsilon_m\)，则

\[
\boxed{
\partial_m(F^n)(X)
\le
\begin{cases}
n\varepsilon_m,&L=1,\\[1mm]
\dfrac{1-L^n}{1-L}\varepsilon_m,&0\le L<1,\\[3mm]
\dfrac{L^n-1}{L-1}\varepsilon_m,&L>1.
\end{cases}
}
\]

这把“时间”与“有限坐标自然性”连接起来：

- 收缩动力学会使有限观察误差饱和；
- 等距动力学最多线性累计局部缺陷；
- 扩张动力学可能指数放大未观察余量。

该结论仍是模型误差传播，不等同于物理光速或普适时间箭头。

---

## 31.8 重复投影界面产生的熵箭头：每一步熵增恰等于被删除相干

令

\[
U:\mathscr H\to\mathscr H
\]

为酉算子，固定上下文 \(\mathcal B\)，并定义离散时间演化

\[
\boxed{
\rho_{n+1}
=
\mathbb E_{\mathcal B}
\left(
U\rho_nU^*
\right).
}
\]

整体酉演化本身保持 von Neumann 熵：

\[
S(U\rho U^*)=S(\rho).
\]

对去相干映射有标准恒等式

\[
\boxed{
D(\sigma\|
\mathbb E_{\mathcal B}\sigma)
=
S(\mathbb E_{\mathcal B}\sigma)-S(\sigma).
}
\]

### 定理 31.16（熵生产—相干删除恒等式）

对每个 \(n\)，

\[
\boxed{
S(\rho_{n+1})-S(\rho_n)
=
D\!\left(
U\rho_nU^*
\big\|
\mathbb E_{\mathcal B}(U\rho_nU^*)
\right)
\ge0.
}
\]

因此

\[
\boxed{
S(\rho_N)-S(\rho_0)
=
\sum_{n=0}^{N-1}
D\!\left(
U\rho_nU^*
\big\|
\mathbb E_{\mathcal B}(U\rho_nU^*)
\right).
}
\]

#### 证明

令

\[
\sigma_n=U\rho_nU^*.
\]

则

\[
\rho_{n+1}
=
\mathbb E_{\mathcal B}\sigma_n.
\]

利用去相干相对熵恒等式和酉熵不变性：

\[
\begin{aligned}
S(\rho_{n+1})-S(\rho_n)
&=
S(\mathbb E_{\mathcal B}\sigma_n)-S(\sigma_n)
\\
&=
D(\sigma_n\|
\mathbb E_{\mathcal B}\sigma_n).
\end{aligned}
\]

求和即得。 \(\square\)

这给出一个严格的时间箭头分解：

\[
\boxed{
\text{熵增}
=
\text{每一步由观察界面删除的相干总量}.
}
\]

若没有 \(\mathbb E_{\mathcal B}\)，则酉动力学熵不变。若 \(U\) 保持对角代数，并且 \(\rho_0\) 已在该代数中，则所有相对熵项均为零，熵不增加。

所以本模型中的不可逆性不来自 Hilbert 空间本身，而来自

\[
\boxed{
\text{可逆整体动力学}
+
\text{重复非单射界面投影}.
}
\]

### 定理 31.17（投影后动力学退化为 unistochastic Markov 链）

从第一步以后，

\[
\rho_n
=
\sum_jp_{n,j}P_j^{\mathcal B}.
\]

定义

\[
\boxed{
T_{kj}
=
|\langle b_k,Ub_j\rangle|^2.
}
\]

则 \(T\) 为双随机矩阵，并且

\[
\boxed{
p_{n+1}=Tp_n.
}
\]

#### 证明

若

\[
\rho_n=\sum_jp_{n,j}P_j,
\]

则

\[
p_{n+1,k}
=
\operatorname{Tr}
\left(
P_kU\rho_nU^*
\right)
=
\sum_j
|\langle b_k,Ub_j\rangle|^2p_{n,j}.
\]

酉矩阵各行各列模平方和为一，故 \(T\) 双随机。 \(\square\)

因此，一旦每一步都将状态投影回同一个经典对角上下文，量子过程在可见层变成一个经典 Markov 链。双随机性给出

\[
p_{n+1}\prec p_n,
\]

故 Shannon 熵满足

\[
\boxed{
H(p_{n+1})\ge H(p_n).
}
\]

若 \(T\) primitive，则

\[
p_n\to
\left(
\frac1d,\ldots,\frac1d
\right)
\]

并且

\[
H(p_n)\to\log d.
\]

这不是量子力学所有时间箭头的唯一解释，而是一个精确模型，展示了概率、熵、投影与时间如何从同一界面递推中出现。

---

## 31.9 不能再使用一个“上下文缺陷”概括所有量子非经典性

本节的 MUB 反例要求对第 30 节作 append-only 收紧。至少存在以下四个不同问题：

### 1. 锐利兼容性

问投影是否共同可测／共同对角化：

\[
[P_j^{\mathcal B},P_k^{\mathcal C}]=0.
\]

对应量：

\[
\mathcal I(\mathcal B,\mathcal C).
\]

### 2. 粗粒化顺序性

问两次信息删除的顺序是否重要：

\[
\mathbb E_{\mathcal B}
\mathbb E_{\mathcal C}
\stackrel{?}{=}
\mathbb E_{\mathcal C}
\mathbb E_{\mathcal B}.
\]

对应状态依赖量：

\[
\mathcal O_{\mathcal B,\mathcal C}(\rho).
\]

### 3. 层析冗余

问两个坐标系抽取的线性状态方向有多少重合：

\[
\mathcal R(\mathcal B,\mathcal C)
=
\sum_{jk}(M_{jk}-1/d)^2.
\]

MUB 使其为零，因此每个上下文带来最大正交创新。

### 4. 全局 contextuality

问一个测量情景的全部局部统计是否存在统一的非上下文全局实现。这是多上下文、多操作等价关系与概率约束的全局问题，不能由任意一对基的交换子或 dephasing 顺序完全决定。

因此建议将量子上下文审计记录为向量

\[
\boxed{
\mathfrak C
=
\left(
\mathcal I,\mathcal O,\mathcal R,\mathcal G
\right),
}
\]

而不是单一标量。

特别地，

\[
\boxed{
\mathcal I=1,\quad
\mathcal O=0,\quad
\mathcal R=0
}
\]

是 MUB 对的规范签名：

- 锐利投影最大不兼容；
- 两次完全去相干顺序却无差别；
- 两个概率坐标平面在线性层析意义下完全无冗余。

这一签名揭示“互补”不是单纯的不交换，而是：

\[
\boxed{
\text{局部经典坐标最大不同，同时携带最大独立信息}.
}
\]

---
