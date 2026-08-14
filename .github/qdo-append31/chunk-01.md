---

# 31. 追加：算子 Hilbert 坐标塔、互补对角与三类量子闭合缺陷

## 31.0 研究定位

第 30 节把相对性、商余、概率与量子上下文统一到“观察界面及其完成”之下，但仍留下一个关键歧义：若两个上下文的去相干通道交换，是否说明它们在物理上兼容？答案是否定的。事实上，两组互相无偏基（mutually unbiased bases, MUB）的锐利投影是最大互补的，但对应去相干通道的复合都等于完全退极化通道，因此两种顺序完全相同。

这迫使本文把“上下文差异”拆成三种彼此独立的结构：

1. **锐利不兼容度**：组成上下文的投影是否能够共同对角化；
2. **粗粒化顺序缺陷**：先按哪个上下文丢弃相干是否影响结果；
3. **全局拼接障碍**：全部局部统计是否存在一个统一的非上下文全局模型。

本节首先把有限维量子状态空间嵌入算子 Hilbert 空间，证明一次基测量恰好是到一个 \((d-1)\)-维“经典对角坐标平面”的正交投影；其余 \(d^2-d\) 个实方向是该上下文看不见的相干余量。随后证明，成套 MUB 上下文在算子 Hilbert 空间中形成正交商余塔：每增加一个最大互补坐标系，恰好抽取一个新的 \((d-1)\)-维正交切片；若存在完整的 \(d+1\) 组 MUB，则这些局部经典对角平面正交直和成全部无迹 Hermitian 算子空间，从而完成量子态层析。

在此基础上，本节给出五组新推导：

- 单一锐利上下文的状态自由度可见率为 \(1/(d+1)\)，线性余量率为 \(d/(d+1)\)；
- \(m\) 组 MUB 的状态无关余维率为 \(1-m/(d+1)\)；
- 状态的 Hilbert–Schmidt 余质量按每个新增概率坐标的二次偏差精确递减；
- 对任意 Lipschitz 自指算子或动力学，观察自然性缺陷由尚未捕获的余质量控制；
- 重复“酉演化—投影界面”产生的熵增，逐步恰等于每轮被删除的相对熵相干。

本节不声称这些组成部分各自都是新发现。MUB 层析、算子 Hilbert 几何、条件期望、量子相干和上下文性均有成熟文献。本文的候选贡献是把它们接入同一个“对角—商余—观察完成”演算，并识别出一个此前框架中的错误替代：**去相干通道交换子不能作为锐利上下文不兼容性的统一度量。**

以下固定

\[
\mathscr H=\mathbb C^d,
\qquad
d\ge2.
\]

所有新增结论均为纸面证明，未经 Lean kernel 验证不得标记为 `Closed`。

---

## 31.1 状态不是一个概率向量，而是算子 Hilbert 空间中的点

令

\[
\operatorname{Herm}_d
=
\{X\in M_d(\mathbb C):X=X^*\}
\]

视为实 Hilbert 空间，内积为

\[
\langle X,Y\rangle_{\mathrm{HS}}
=
\operatorname{Tr}(XY).
\]

其无迹子空间为

\[
\operatorname{Herm}_d^0
=
\{X\in\operatorname{Herm}_d:\operatorname{Tr}X=0\}.
\]

维数为

\[
\boxed{
\dim_{\mathbb R}\operatorname{Herm}_d=d^2,
\qquad
\dim_{\mathbb R}\operatorname{Herm}_d^0=d^2-1.
}
\]

任意密度矩阵唯一写成

\[
\boxed{
\rho=\frac{I}{d}+X_\rho,
\qquad
X_\rho\in\operatorname{Herm}_d^0.
}
\]

这里 \(I/d\) 是共同的仿射原点，而 \(X_\rho\) 携带全部可变状态信息。其 Hilbert–Schmidt 长度满足

\[
\boxed{
\|X_\rho\|_2^2
=
\operatorname{Tr}(\rho^2)-\frac1d.
}
\]

所以偏离最大混合态的总二次信息量就是 purity excess。

### 定义 31.1（基上下文的对角平面）

取一组正交规范基

\[
\mathcal B=(|b_1\rangle,\ldots,|b_d\rangle),
\]

并令

\[
P_j^{\mathcal B}=|b_j\rangle\langle b_j|.
\]

定义该上下文的无迹对角平面

\[
\boxed{
\mathcal D_{\mathcal B}^0
=
\left\{
\sum_{j=1}^d x_jP_j^{\mathcal B}:
x_j\in\mathbb R,\ 
\sum_jx_j=0
\right\}.
}
\]

显然

\[
\boxed{
\dim_{\mathbb R}\mathcal D_{\mathcal B}^0=d-1.
}
\]

定义去相干／pinching 映射

\[
\boxed{
\mathbb E_{\mathcal B}(X)
=
\sum_{j=1}^d
P_j^{\mathcal B}XP_j^{\mathcal B}.
}
\]

### 定理 31.2（一次基测量是算子 Hilbert 正交投影）

\(\mathbb E_{\mathcal B}\) 是 \(\operatorname{Herm}_d\) 上到

\[
\mathcal D_{\mathcal B}
=
\mathbb RI\oplus\mathcal D_{\mathcal B}^0
\]

的 Hilbert–Schmidt 正交投影。限制到 \(\operatorname{Herm}_d^0\) 时，它是到 \(\mathcal D_{\mathcal B}^0\) 的正交投影。

#### 证明

由投影正交性，

\[
\mathbb E_{\mathcal B}^2(X)
=
\sum_{j,k}P_jP_kXP_kP_j
=
\sum_jP_jXP_j
=
\mathbb E_{\mathcal B}(X).
\]

又因为

\[
\operatorname{Tr}\!\left(
Y\mathbb E_{\mathcal B}(X)
\right)
=
\sum_j\operatorname{Tr}(YP_jXP_j)
=
\sum_j\operatorname{Tr}(P_jYP_jX)
=
\operatorname{Tr}\!\left(
\mathbb E_{\mathcal B}(Y)X
\right),
\]

故 \(\mathbb E_{\mathcal B}\) 对 Hilbert–Schmidt 内积自伴。幂等且自伴即为正交投影。其像恰为在 \(\mathcal B\) 中对角的 Hermitian 算子。由于保持迹，限制到无迹空间后的像为 \(\mathcal D_{\mathcal B}^0\)。 \(\square\)

设

\[
p_j^{\mathcal B}(\rho)
=
\operatorname{Tr}(\rho P_j^{\mathcal B}).
\]

则

\[
\boxed{
\mathbb E_{\mathcal B}(\rho)
=
\sum_jp_j^{\mathcal B}(\rho)P_j^{\mathcal B}.
}
\]

所以一组测量概率并不是整个状态，而只确定状态在一个 \((d-1)\)-维经典对角平面上的投影。

### 推论 31.3（单上下文的线性可见率与余量率）

在无迹状态方向空间 \(\operatorname{Herm}_d^0\) 中，一组秩一 PVM 最多可见

\[
d-1
\]

个独立实方向，留下

\[
d^2-d
\]

个正交余方向。因此

\[
\boxed{
\text{visible ratio}
=
\frac{d-1}{d^2-1}
=
\frac1{d+1},
}
\]

\[
\boxed{
\text{remainder ratio}
=
\frac{d^2-d}{d^2-1}
=
\frac d{d+1}.
}
\]

这里的比例是线性维数比例，不是任意具体状态的概率质量比例。

这给出一个精确修正：

\[
\boxed{
\text{一个量子概率向量通常只暴露状态线性自由度的 }1/(d+1).
}
\]

其余部分不是“没有定义”，而是相对于该坐标系仍处于非对角余空间。

---

## 31.2 纯态概率映射的纤维就是相对相位余坐标

在纯态层，取射影空间

\[
\mathbb{CP}^{d-1}
\]

并定义基概率映射

\[
q_{\mathcal B}:
\mathbb{CP}^{d-1}
\longrightarrow
\Delta_{d-1},
\]

\[
q_{\mathcal B}([\psi])
=
\left(
|\langle b_1,\psi\rangle|^2,
\ldots,
|\langle b_d,\psi\rangle|^2
\right).
\]

### 定理 31.4（内点概率纤维为 \((d-1)\)-环面）

若

\[
p=(p_1,\ldots,p_d)
\in\operatorname{int}\Delta_{d-1},
\qquad
p_j>0,
\]

则

\[
\boxed{
q_{\mathcal B}^{-1}(p)
\cong
\mathbb T^{d-1}.
}
\]

#### 证明

任意位于该纤维的单位向量可写成

\[
\psi
=
\sum_{j=1}^d
\sqrt{p_j}e^{i\theta_j}|b_j\rangle.
\]

全部 \(\theta_j\in\mathbb R/2\pi\mathbb Z\) 可自由选择，但共同平移

\[
(\theta_1,\ldots,\theta_d)
\mapsto
(\theta_1+\alpha,\ldots,\theta_d+\alpha)
\]

只改变全局相位，在 \(\mathbb{CP}^{d-1}\) 中代表同一点。因此纤维为

\[
\mathbb T^d/\mathbb T
\cong
\mathbb T^{d-1}.
\]

\(\square\)

所以对于纯态：

\[
\boxed{
\text{概率坐标}
=
\text{模长平方},
}
\]

\[
\boxed{
\text{余坐标}
=
\text{相对相位}.
}
\]

维数核对为

\[
2d-2
=
(d-1)+(d-1).
\]

在概率单纯形边界上，零振幅坐标不再携带相位，纤维退化为更低维环面。

这使“概率是投影”获得一个非常具体的商余形式：

\[
\boxed{
\mathbb{CP}^{d-1}
\longrightarrow
\Delta_{d-1}
}
\]

忘掉的不是一个抽象神秘变量，而是相对于该基的相对相位纤维。

---
