---

# 29. 追加：以 Hilbert 正交商余塔分析 Riemann 假设

## 29.0 文档地位与结论边界

本节把第 28 节的 Hilbert 正交商余塔用于 Riemann 假设（RH），目标不是把抽象的“无限维余空间”直接宣称为 RH 的证明，而是回答四个严格问题：

1. RH 能否被写成某个完成商中的**目标余类消失**；
2. 有限高度零点核验为什么不能推出全局 RH；
3. Li–Cayley 指标为何能够放大高处零点极小的离线偏移；
4. Weil 正性若要通过有限压缩传递到无限维极限，究竟还缺少什么算子论条件。

本节得到两个层次不同的接口。

第一种是**零点侧的诊断塔**：它把 RH 精确改写为一个 Cayley 对角算子的酉性，但该算子直接由零点定义，因此本身是结构诊断，不是非循环证明。

第二种是**Nyman–Beurling–Báez-Duarte 逼近塔**：它完全由显式分数部分函数生成，并把 RH 精确改写为一个指定目标向量在最终正交余空间中的质量为零。这是本节最直接、非循环且可计算的 Hilbert 商余接口。

本节没有证明最终余质量为零，没有证明 Weil 二次型全局非负，也没有构造 Hilbert–Pólya 自伴算子。所有新增结论均为纸面推导；在获得 Lean proof term、依赖闭包与冻结收据以前，不得标记为 `Closed`。

---

## 29.1 零点 Cayley 算子：RH 是酉性缺陷消失

设 \(\mathcal Z\) 为 Riemann \(\xi\) 函数的非平凡零点多重集。对每个

\[
\rho=\sigma+i\gamma\in\mathcal Z
\]

定义 Cayley–Li 坐标

\[
\boxed{
c_\rho
=
1-\frac1\rho
=
\frac{\rho-1}{\rho}.
}
\]

取零点 Hilbert 空间

\[
\mathscr H_{\mathcal Z}
=
\ell^2(\mathcal Z),
\]

其规范正交基记为 \((e_\rho)_{\rho\in\mathcal Z}\)。在有限支撑向量上定义对角算子

\[
\boxed{
Ce_\rho=c_\rho e_\rho.
}
\]

由于非平凡零点位于临界带 \(0<\sigma<1\)，并且 \(|\gamma|\to\infty\) 时 \(c_\rho\to1\)，该对角算子可按标准方式闭包为有界算子。

### 定理 29.1（Cayley 酉性缺陷公式）

对每个非平凡零点 \(\rho=\sigma+i\gamma\)，

\[
\boxed{
(C^*C-I)e_\rho
=
\delta_\rho e_\rho,
}
\]

其中

\[
\boxed{
\delta_\rho
=
|c_\rho|^2-1
=
\frac{1-2\sigma}{|\rho|^2}.
}
\]

因此下列命题等价：

\[
\boxed{
\mathrm{RH};
}
\]

\[
\boxed{
|c_\rho|=1
\quad
\text{对全部 }\rho\in\mathcal Z;
}
\]

\[
\boxed{
C^*C=I;
}
\]

\[
\boxed{
C\text{ 为酉算子}.
}
\]

#### 证明

直接计算：

\[
|c_\rho|^2
=
\frac{|\rho-1|^2}{|\rho|^2}.
\]

而

\[
|\rho-1|^2
=
(\sigma-1)^2+\gamma^2,
\qquad
|\rho|^2
=
\sigma^2+\gamma^2.
\]

故

\[
|c_\rho|^2-1
=
\frac{(\sigma-1)^2-\sigma^2}{|\rho|^2}
=
\frac{1-2\sigma}{|\rho|^2}.
\]

于是

\[
|c_\rho|=1
\iff
1-2\sigma=0
\iff
\sigma=\frac12.
\]

对全部零点同时成立，恰为 RH。对角算子在每个基向量上的模均为一，当且仅当其为酉算子。 \(\square\)

这一公式把临界线从“零点位置”转换成了“Cayley 演化是否保持 Hilbert 范数”：

\[
\boxed{
\Re\rho=\frac12
\iff
\|Ce_\rho\|=\|e_\rho\|.
}
\]

这与仓库 `SpectralDynamics` 中“临界线—镜像固定—半密度酉性—共振”的形式化接口一致，但这里的 \(C\) 是直接按零点对角化的诊断算子，并未构造独立于零点的 Hilbert–Pólya 动力学。

### 推论 29.2（对数径向缺陷与镜像反号）

定义

\[
\boxed{
\beta_\rho
=
\log|c_\rho|
=
\frac12
\log
\frac{|\rho-1|^2}{|\rho|^2}.
}
\]

则

\[
\boxed{
\mathrm{RH}
\iff
\beta_\rho=0
\quad
\text{对全部 }\rho.
}
\]

对函数方程镜像

\[
\rho^\sharp=1-\overline\rho
\]

有

\[
\boxed{
|c_{\rho^\sharp}|=|c_\rho|^{-1},
\qquad
\beta_{\rho^\sharp}=-\beta_\rho.
}
\]

#### 证明

由

\[
c_{\rho^\sharp}
=
\frac{-\overline\rho}{1-\overline\rho}
\]

立即得到模长互为倒数。 \(\square\)

所以一个离线四元轨道不是产生两个独立的“径向偏差”，而是产生一对相反的对数深度

\[
+\beta,
\qquad
-\beta.
\]

这正是本文前述 Li–Cayley 四元贡献中 \(\cosh(n\beta)\) 出现的结构根源。

---

## 29.2 零点高度商余塔与有限核验的严格极限

按非降高度枚举零点多重集：

\[
|\Im\rho_1|
\le
|\Im\rho_2|
\le\cdots.
\]

定义

\[
S_N^{\mathcal Z}
=
\operatorname{span}
(e_{\rho_1},\ldots,e_{\rho_N}),
\]

\[
R_N^{\mathcal Z}
=
(S_N^{\mathcal Z})^\perp,
\]

并令 \(P_N^{\mathcal Z}\) 为 \(S_N^{\mathcal Z}\) 上的正交投影。由于 \(C\) 与缺陷算子

\[
D=C^*C-I
\]

均在零点基下对角化，每个 \(S_N^{\mathcal Z}\) 都是 reducing subspace，因而没有跨壳层块：

\[
P_iDP_j=0
\qquad(i\ne j).
\]

有限高度核验“前 \(N\) 个零点在临界线”恰等价于

\[
\boxed{
P_N^{\mathcal Z}DP_N^{\mathcal Z}=0.
}
\]

### 命题 29.3（有限核验不能消除最终余块）

对任意有限 \(N\)，

\[
P_N^{\mathcal Z}DP_N^{\mathcal Z}=0
\]

只说明已枚举壳层上的缺陷为零；它不给出

\[
P_{R_N^{\mathcal Z}}D
P_{R_N^{\mathcal Z}}=0.
\]

因此任何有限数量的临界线零点核验都不能单独推出 RH。

#### 证明

取任意 \(M>N\)，在 \(R_N^{\mathcal Z}\) 内把某个基向量 \(e_{\rho_M}\) 的对角值改为非零，不影响 \(S_N^{\mathcal Z}\) 上的压缩。抽象地说，有限压缩完全遗忘余空间中的对角数据。 \(\square\)

这里第 28 节的“最坏盲区恒为一”得到一个精确实例：

\[
\|I-P_N^{\mathcal Z}\|_{\mathrm{op}}=1
\]

对每个有限 \(N\) 成立。即使

\[
P_N^{\mathcal Z}x\to x
\]

对每个固定 \(x\) 强收敛，也不存在任何有限阶段在整个单位球上消除余空间。

但零点缺陷还有一个更微妙的性质。由

\[
|\delta_\rho|
=
\frac{|1-2\sigma|}{|\rho|^2}
\le
\frac1{|\rho|^2}
\]

可见，高处离线零点在原始 Cayley 酉性中只产生很小的缺陷。若按高度枚举，则 \(D\) 的对角值趋于零，故 \(D\) 是紧对角算子。

因此：

\[
\boxed{
\text{高处离线零点可以具有任意小的单步酉性缺陷，}
}
\]

而

\[
\boxed{
\text{“缺陷很小”与“缺陷严格为零”不是同一命题。}
}
\]

这解释了为什么提高零点核验高度虽然强烈增加证据，却不能通过连续极限自动把 RH 的等式条件证明出来。

---

## 29.3 Li–Cayley 放大：为什么需要 \((n,T)\) 联合控制

写

\[
c_\rho=e^{\beta_\rho+i\theta_\rho}.
\]

对函数方程与共轭生成的完整四元轨道，本文既有约定下的第 \(n\) 个 Li–Cayley 轨道贡献为

\[
\boxed{
L_n(\rho)
=
4-4\cosh(n\beta_\rho)\cos(n\theta_\rho).
}
\]

在临界线上，

\[
\beta_\rho=0,
\]

故单轨道贡献化为
