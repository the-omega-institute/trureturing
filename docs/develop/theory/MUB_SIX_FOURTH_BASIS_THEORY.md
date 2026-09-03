# MUB Six Fourth-Basis Research Theory

> **统一理论卷规则。** 从本文件建立以后，六维四互无偏基 research lane 的新理论推理统一追加到 `MUB_SIX_FOURTH_BASIS_THEORY.md`。形式化节点继续拥有各自的 Lean GID、Scribe 与 Blueprint 投影，但不再为每个新 obstruction 单独建立 theory 文档。
>
> **理论状态。** 研究卷。区分已证明恒等式、文献输入、条件归约、待证猜想和最终开放目标。任何中间证书都不得被表述为六维四 MUB 已解决。

## 0. 目标与当前坐标

目标是六维开放问题：是否存在四个两两 mutually unbiased orthonormal bases in `C^6`。

固定第一基为坐标基以后，剩余三个基可表示为六阶 complex Hadamard matrices。前一轮已经建立标准 Hadamard 等价、pairwise flat transition、exact atlas consumer contract，以及独立选择等价类代表会破坏 MUB compatibility 的反例。

本卷把主坐标进一步从“三个完整 Hadamard 矩阵联合搜索”改为：

```text
fixed Hadamard edge H
  -> completion fiber over H
  -> two completions compatible with the same edge
  -> centered-projector / cube cross-Gram certificate
  -> branch-specific exact exclusion
```

## 1. 固定一条 Hadamard 边后的 double-completion locus

设四个 MUB 为 `B0,B1,B2,B3`。固定共同酉规范使 `B0=I`，再令 `B1=H`。第三、第四基不再作为任意两个独立 Hadamard matrices 处理，而视为同一底边 `(I,H)` 的两个 completions。

记固定底面 `H` 的合法 completion fiber 为

```math
\mathfrak C(H).
```

若 `C,D in \mathfrak C(H)` 分别编码第三、第四基，则两者互无偏可压缩成一个 cross-Gram 条件：

```math
C^*D=dJ_d.
```

在 `d=6` 时：

```math
C^*C=36I_6,\qquad D^*D=36I_6,\qquad C^*D=6J_6.
```

因此定义两个层次：

```math
\mathcal E_6^{(1)}=\{H:\mathfrak C(H)\ne\varnothing\},
```

即能进入至少一个 MUB triplet 的 Hadamard；以及

```math
\mathcal E_6^{(2)}=
\{H:\exists C,D\in\mathfrak C(H),\ C^*D=6J_6\}.
```

四 MUB 问题精确收缩为：

```math
\boxed{\mathcal E_6^{(2)}=\varnothing.}
```

这比分类整个 `E_6^(1)` 更窄。quartet-specific 的额外 cross-Gram 方程应当直接参与证明，而不应先完整解决所有 triplets。

## 2. cube cross-Gram 与 centered-projector plane 是同一结构

归一化写

```math
\widehat C=C/d,\qquad \widehat D=D/d,
```

并定义

```math
u=d^{-1/2}\mathbf 1_d.
```

completion 的 piercing-sum 条件固定共同方向 `u`。cross-Gram 条件化为

```math
\widehat C^*\widehat D=uu^*.
```

因此对所有 `x,y in u^perp`：

```math
\langle \widehat Cx,\widehat Dy\rangle=0.
```

即

```math
\widehat C(u^\perp)\perp \widehat D(u^\perp).
```

两个空间的维数均为 `d-1`。在 `d=6` 时正好是两个正交五维平面。这与仓库已有的 `centeredContextPlane` 几何完全一致。

所以 Hadamard-cube 路线和 centered-projector SoS 路线并非两套独立编码。共同核心是去掉全一方向后，两个 completion 的 `5` 维 trace-zero information planes 必须正交。

## 3. completion gluing 的 Hadamard-product rigidity

若一个 cube completion 可分解为

```math
C_{ijk}=H_{ij}X_{jk}Y_{ik},
```

另一个为

```math
D_{ij\ell}=H_{ij}X'_{j\ell}Y'_{i\ell},
```

且 `H` entrywise unimodular，则直接展开得到：

```math
\boxed{C^*D=(X^*X')\circ(Y^*Y').}
```

其中 `circ` 是逐项 Hadamard product。

令

```math
U=X/\sqrt d,\quad U'=X'/\sqrt d,
\quad V=Y/\sqrt d,\quad V'=Y'/\sqrt d.
```

quartet gluing 给出

```math
(U^*U')\circ(V^*V')=d^{-1}J.
```

设

```math
A=U^*U',\qquad B=V^*V'.
```

由于 `A,B` 均酉，对固定一行使用 Cauchy-Schwarz equality：

```math
A_{k\ell}B_{k\ell}=1/d
```

迫使

```math
|A_{k\ell}|=|B_{k\ell}|=d^{-1/2},
```

并进一步得到

```math
\boxed{B=\overline A.}
```

因此两个 completion 的两个相对 transition 不可独立变化。quartet 条件消掉了一个完整相对矩阵。

**形式化优先级：高。** 这里的第一步是有限和与矩阵乘法的精确恒等式；第二步只需要 finite-dimensional unitary row normalization 与 Cauchy-Schwarz equality。

## 4. centered rank-one projector 的二次 variety

对纯态投影 `P=|psi><psi|` 定义

```math
Q=P-I/d.
```

由 `P^2=P` 得

```math
Q^2=(1-2/d)Q+(d-1)d^{-2}I.
```

在 `d=6`：

```math
\boxed{Q^2=\frac23Q+\frac5{36}I.}
```

并且

```math
Tr(Q)=0,\qquad Tr(Q^2)=5/6.
```

同一基的 centered projectors 构成正则 `5`-simplex：

```math
Tr(Q_iQ_j)=-1/6\quad(i\ne j),
```

不同 MUB 之间则满足

```math
Tr(Q_iQ_j)=0.
```

因此固定两个 MUB 后，共同无偏纯态属于：

```math
\mathcal P_1\cap(V_I\oplus V_H)^\perp,
```

其中 `P_1` 是上述 rank-one quadratic variety。固定三个 MUB 后则落在

```math
\mathcal P_1\cap(V_I\oplus V_H\oplus V_C)^\perp.
```

一般维数上界只能看见正交平面的线性 packing；六维 `m=4` 需要利用这里的二次 rank-one variety 与 Hadamard branch equations 的交。

## 5. 三三分割 moment 的 feature-kernel 压缩

对六阶 Hadamard `H`，对三元素子集 `I subset {1,...,6}` 定义符号向量

```math
\mu(I)_i=+1\ (i\in I),\qquad -1\ (i\notin I).
```

定义列乘积

```math
\delta_k(H)=\prod_i H_{ik}.
```

对奇数 `q` 定义 `20 x 6` square-free feature matrix：

```math
V_q(H)_{I,k}=\left(\prod_{i\in I}H_{ik}\right)^{2q}.
```

利用 unimodularity：

```math
\boxed{
g_H(q\mu(\cdot))
=V_q(H)\,\overline{\delta(H)^q}.
}
```

因此全部三三分割 moments vanishing 等价于指定向量进入 feature matrix 的 kernel：

```math
V_q(H)\overline{\delta(H)^q}=0.
```

再定义 positive semidefinite kernel matrix

```math
K_q(H)=V_q(H)^*V_q(H).
```

则

```math
V_q(H)x=0\iff K_q(H)x=0.
```

所以 20 个 feature equations 可以压缩成一个 `6 x 6` prescribed-kernel 条件。

## 6. Newton-Gram 闭式

令

```math
G_m(H)=(H^{\circ m})^*H^{\circ m},
```

其中 `H^{circ m}` 表示 entrywise power。

对 `K_q` 的每个 entry，令

```math
r_i=\overline{H_{ik}^{2q}}H_{i\ell}^{2q}.
```

则 `K_q(k,l)` 是 `r_1,...,r_6` 的三阶 elementary symmetric polynomial `e_3(r)`。Newton identity

```math
6e_3=p_1^3-3p_1p_2+2p_3
```

给出：

```math
\boxed{
K_q(H)=\frac16\left[
G_{2q}(H)^{\circ3}
-3G_{2q}(H)\circ G_{4q}(H)
+2G_{6q}(H)
\right].
}
```

于是原先大量 permutation moments 可改写为小型 Gram matrices 的 kernel certificate。

对 `q=1`：

```math
\left[G_2^{\circ3}-3G_2\circ G_4+2G_6\right]\overline\delta=0.
```

对 `q=3`：

```math
\left[G_6^{\circ3}-3G_6\circ G_{12}+2G_{18}\right]\overline{\delta^3}=0.
```

这类表达非常适合 branch-specific exact factorization、resultant 或 rational SDP dual search。

## 7. cubic square-free Gram identity

定义

```math
T_H(I,k)=\prod_{i\in I}H_{ik},\qquad |I|=3.
```

若 `H` 本身是六阶 complex Hadamard，则：

```math
\boxed{
T_H^*T_H
=18I_6+\frac13(H^{\circ3})^*H^{\circ3}.
}
```

原因是对不同列 `k,l`，令 `r_i=conj(H_ik) H_il`。Hadamard 正交给 `p_1=0`，Newton identity 化为 `3e_3=p_3`。对角线上 `e_3(1,...,1)=20=18+6/3`。

更一般的 polarized identity 是：

```math
\boxed{
T_H^*T_K=
\frac16\left[
(H^*K)^{\circ3}
-3(H^*K)\circ((H^{\circ2})^*K^{\circ2})
+2(H^{\circ3})^*K^{\circ3}
\right].
}
```

这是目前最值得先形式化的新技术 lemma 之一。它不依赖六维 MUB conjecture，只依赖有限三元素 subset 和 Newton identity，因此具有独立复用价值。

## 8. cubic orientation coherence 是独立缺口

2026 triplet 论证中需要严格区分：

```math
\forall\pi,\ a_\pi b_\pi=0
```

与

```math
(\sum_\pi a_\pi)(\sum_\pi b_\pi)=0.
```

仅由非负性，第二式推出第一式；第一式不能一般性推出第二式。逐 permutation 允许零侧随 `pi` 改变。

因此应把后续所需的逻辑拆成：

1. **pointwise cubic product vanishing**；
2. **orientation coherence**；
3. **global one-sided cubic vanishing**。

形式化上绝不能把 1 与 3 写成等价。

对 feature vectors

```math
a=V_3(H)\overline{\delta(H)^3},
\qquad
b=V_3(H^*)\overline{\delta(H^*)^3},
```

coherence 的精确形式是：

```math
supp(a)\cap supp(b)=\varnothing
\Longrightarrow a=0\ \text{or}\ b=0.
```

这应视为一个新的有限代数子问题。若能利用 quartet 的 double-completion 条件证明它，就无需对所有 MUB triplets 解决更强 conjecture。

## 9. strict 2-circulant 余项的有限对称骨架

Fourier family 已有 quartet exclusion。若 double-completion moments 能把底面压到 Fourier / transposed Fourier / `X` family，则任何剩余 quartet 的边都必须属于严格 2-circulant 部分：

```math
\mathcal X_{strict}=\mathcal X\setminus(\mathcal F\cup\mathcal F^T).
```

`X` family 的 `3 x 3` circulant blocks 给出一个阶三 monomial symmetry，其 permutation part 的 cycle type 是 `(3)(3)`。

在一个基上固定第一条边的 permutation

```math
s=(123)(456).
```

另一条 strict-X 边的 permutation `t` 也具有 `(3)(3)` cycle type。在 `s` 的 centralizer 下，40 个候选 `t` 分成六个 orbit：

```text
1 + 1 + 2 + 9 + 9 + 18 = 40.
```

对应生成 permutation groups 的阶为：

```text
3, 3, 9, 12, 12, 60.
```

因此 all-strict-X triangle 的 permutation alignment 已经是有限六分支问题。连续自由度只剩 monomial phases。

### aligned Z3 branch

若多个边共享同一个阶三 symmetry，把环境空间分解为三个二维本征空间：

```math
E_0\oplus E_1\oplus E_2,
\qquad \dim E_r=2.
```

任何兼容基可写为：

```math
|\psi^{(A)}_{s,p}\rangle
=\frac1{\sqrt3}
\sum_{r=0}^2\omega^{pr}A_r|s\rangle\otimes|r\rangle,
```

其中 `A_r in U(2)`，`s in {1,2}`，`p in Z_3`。

两个这样的基 `A,B` 互无偏当且仅当：

```math
\boxed{
\left|\sum_{r=0}^2
\omega^{rn}(A_r^*B_r)_{st}
\right|^2=\frac32
}
```

对所有 `s,t,n` 成立。

这把 aligned strict-X triangle 降为 `U(2)^3` 上的低维紧致多项式系统。其余五种 finite permutation skeleton 可分别利用有限群表示约束。

## 10. 当前最有价值的 quartet-specific 猜想

应优先尝试证明：

```math
H\in\mathcal E_6^{(2)}
\Longrightarrow
K_1(H)\overline{\delta(H)}=0,
```

以及经过正确 orientation 处理的 cubic statement：

```math
K_3(H)\overline{\delta(H)^3}=0
\quad\lor\quad
K_3(H^*)\overline{\delta(H^*)^3}=0.
```

这里与 triplet-only conjecture 的关键差异是可以直接使用两个 completion 以及：

```math
C^*D=6J.
```

如果 double-completion 真的强制这些 kernel conditions，就可以把 2026 年分类、2024 年 binary-pattern characterization 与 Fourier exclusion 串成：

```text
double completion
 -> low-order feature kernel
 -> Fourier / F^T / X support
 -> Fourier exclusions
 -> strict-X finite symmetry skeletons
 -> exact branch certificates
 -> no quartet
```

## 11. 形式化顺序

### Truth source A. Cube cross-Gram factorization

证明：

```math
C^*D=(X^*X')\circ(Y^*Y')
```

并明确所需的 entrywise-unit 假设。

### Truth source B. Hadamard-product rigidity

在 `A,B` unitary 且 `A circ B = J/d` 下证明：

```math
|A_{ij}|=|B_{ij}|=1/\sqrt d,
\qquad B=conj(A).
```

### Truth source C. centered rank-one quadratic equation

从 `P^2=P` 推出一般 `d` 的 centered-projector polynomial，并特化到六维。

### Truth source D. square-free cubic Gram / Newton identity

先形式化 polarized identity，再导出 Hadamard specialization。

### Truth source E. feature kernel compression

定义 `V_q,K_q,delta`，证明 permutation moments 与 prescribed-kernel statement 的等价。

### Truth source F. orientation logic separation

机器证明 pointwise product vanishing 不推出 global one-sided vanishing 的有限反例，并将 coherence 保留为显式 hypothesis / conjecture。

### Truth source G. strict-X symmetry skeleton

先形式化 finite permutation classification，再处理 aligned `Z3` 的 `U(2)^3` 参数化。

## 12. 开放边界与可证伪点

当前未证明：

- double completion 强制 `q=1` feature-kernel vanishing；
- quartet-specific cubic orientation coherence；
- `K_1,K_3` zero-locus 在完整 order-six atlas 上只落入 Fourier / transposed Fourier / `X` sectors；
- all-strict-X triangle 必然退化或不可能；
- 六维不存在四个 MUB。

任何精确 quartet `I,H,C,D` 都会同时反驳这些拟议全局排除路线。任何 branch-specific exact parameter witness 满足所有 MUB equations，也会反驳对应 branch certificate。

## 13. 研究主线冻结

当前主线冻结为：

```text
Hadamard atlas
 -> fixed-edge completion fiber
 -> double-completion cross-Gram
 -> centered-plane / feature-kernel invariants
 -> Fourier/F^T/X support
 -> strict-X finite symmetry skeleton
 -> exact branch exclusion
 -> global four-MUB exclusion
```

后续理论推理统一追加到本卷。只有经过数学推理得到稳定、可复用、边界清晰的命题，才进入 Lean 真源。
