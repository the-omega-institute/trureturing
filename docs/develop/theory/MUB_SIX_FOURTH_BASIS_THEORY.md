# MUB Six Fourth-Basis Research Theory

> **统一理论卷规则。** 六维四互无偏基 research lane 的新增推理统一追加到本卷。Lean 真源、Scribe 和 Blueprint 可以按节点拆分，理论叙事只维护这一份主卷。
>
> **状态边界。** 本卷区分已证明恒等式、文献输入、条件归约、待证猜想和长期目标。当前没有宣称解决六维四 MUB 开放问题。

## 0. 总目标与先库后证审计

目标是判断是否存在四个两两 mutually unbiased orthonormal bases in `C^6`。

固定第一基为坐标基后，另外三个基可以写成六阶 complex Hadamard matrices。仓库已经建立：

```text
RankOneContext
centeredProjector / centeredContextPlane
commutator / incompatibility / tomography
ComplexHadamard
HadamardEquivalent
HadamardUnbiased
exact Hadamard atlas
lifted four-MUB compatibility
```

本轮形式化前的库检索还确认可以直接复用：

```text
Mathlib.LinearAlgebra.Matrix.Circulant
D5/S3/Fourier/FinitePoisson.lean
D5/S3/Observer/WindowRegister.lean
```

其中 `WindowRegister` 已经定义 `windowRoot M`，证明其 primitive-root 性质，并提供 cyclic shift、clock、Weyl relation 和 unitary 结论。后续三阶 Fourier mode、cube root of unity 和 circulant diagonalization 不再自行引入另一套根单位定义。

2026 年 order-six Hadamard 完整分类 claim 提供单矩阵 atlas。2026 年 centered-projector SoS 结果说明正确坐标能够恢复一般 `m <= d+1` 上界，但在 `d=6,m=4` 时一般 rank certificate 严格为正。因此 fourth-basis obstruction 必须使用六阶专属代数结构。

## 1. 固定 edge 与 double-completion locus

设四个 MUB 为

```math
B_0,B_1,B_2,B_3.
```

共同酉规范令 `B_0=I`，固定第二基对应六阶 Hadamard `H`。第三、第四基应视为同一 edge `(I,H)` 上的两个 completions。

记合法 completion fiber 为

```math
\mathfrak C(H).
```

定义

```math
\mathcal E_6^{(1)}=\{H:\mathfrak C(H)\neq\varnothing\},
```

以及 double-completion locus

```math
\mathcal E_6^{(2)}=
\{H:\exists C,D\in\mathfrak C(H),\ C^*D=6J_6\}.
```

六维 four-MUB 问题等价于

```math
\boxed{\mathcal E_6^{(2)}=\varnothing.}
```

这比分类所有 MUB triplets 更窄，因为 quartet 自带额外的 cross-completion 方程。

## 2. Hadamard cube cross-Gram

对固定 edge 的两个 factorized cube completions 写

```math
C_{ijk}=H_{ij}X_{jk}Y_{ik},
\qquad
D_{ij\ell}=H_{ij}X'_{j\ell}Y'_{i\ell}.
```

若 `H` entrywise unimodular，则直接展开得到

```math
\boxed{
C^*D=(X^*X')\circ(Y^*Y').
}
```

这里 `circ` 是 entrywise Hadamard product。这条恒等式已经进入机器真源：

```text
D5/S3/Quantum/Tomography/MUBCubeCompatibility.lean
factorizedCube_crossGram_apply
factorizedCube_crossGram
```

归一化

```math
U=X/\sqrt d,\quad U'=X'/\sqrt d,
\quad V=Y/\sqrt d,\quad V'=Y'/\sqrt d
```

以后，quartet gluing 要求

```math
A\circ B=d^{-1}J,
\qquad
A=U^*U',\quad B=V^*V'.
```

因为 `A,B` 都是 unitary，逐行 Cauchy-Schwarz 取等强制

```math
|A_{kl}|=|B_{kl}|=d^{-1/2},
```

并由 `A_{kl}B_{kl}=1/d` 得

```math
\boxed{B=\overline A.}
```

所以两个 completion 的两个 relative transitions 不独立。quartet gluing 消掉了一个完整相对矩阵。

## 3. cube geometry 与 centered projector plane 的统一

completion slices 满足

```math
C^*C=d^2I,
\qquad D^*D=d^2I.
```

若第四基也与第三基互无偏，则

```math
C^*D=dJ.
```

定义

```math
\widehat C=C/d,
\qquad
\widehat D=D/d,
\qquad
u=d^{-1/2}\mathbf 1.
```

则

```math
\widehat C^*\widehat D=uu^*.
```

因此

```math
\widehat C(u^\perp)\perp\widehat D(u^\perp).
```

在 `d=6`，两个空间都是五维。这正是 centered rank-one projector context planes 的正交结构。Hadamard cube 与 centered-projector SoS 共享同一个去掉全一方向后的信息几何。

## 4. centered rank-one projector variety

对纯态投影 `P` 定义

```math
Q=P-I/d.
```

由 `P^2=P` 得

```math
Q^2=(1-2/d)Q+(d-1)d^{-2}I.
```

六维特化为

```math
\boxed{Q^2=\frac23Q+\frac5{36}I.}
```

并且

```math
Tr(Q)=0,
\qquad Tr(Q^2)=5/6.
```

同一基的六个 `Q_i` 构成 regular 5-simplex：

```math
Tr(Q_iQ_j)=-1/6\quad(i\neq j).
```

不同 MUB 之间：

```math
Tr(Q_iQ_j)=0.
```

所以固定两个基以后，共同无偏纯态属于

```math
\mathcal P_1\cap(V_I\oplus V_H)^\perp,
```

其中 `P_1` 是 rank-one quadratic variety。固定三个基后则属于

```math
\mathcal P_1\cap(V_I\oplus V_H\oplus V_C)^\perp.
```

一般 linear packing 只能证明 `m<=7`。第四基问题需要 quadratic rank-one variety 与 order-six branch equations 的交。

## 5. 三三分割 moments 的 feature-kernel 压缩

对六阶 Hadamard `H`，对三元素子集 `I` 定义

```math
\mu(I)_r=+1\ (r\in I),
\qquad
\mu(I)_r=-1\ (r\notin I).
```

定义列乘积

```math
\delta_k(H)=\prod_r H_{rk}.
```

对奇数 `q` 定义 `20 x 6` feature matrix

```math
V_q(H)_{I,k}=
\left(\prod_{r\in I}H_{rk}\right)^{2q}.
```

unimodularity 给出

```math
\boxed{
g_H(q\mu(\cdot))
=V_q(H)\overline{\delta(H)^q}.
}
```

因此全部三三分割 moment vanishing 等价于 prescribed-kernel condition

```math
V_q(H)\overline{\delta(H)^q}=0.
```

定义

```math
K_q(H)=V_q(H)^*V_q(H).
```

则

```math
V_q(H)x=0\iff K_q(H)x=0.
```

于是 20 个 feature equations 被压成 `6 x 6` PSD kernel。

## 6. Newton-Gram 与 cubic square-free identities

定义 entrywise-power Gram matrices

```math
G_m(H)=(H^{\circ m})^*H^{\circ m}.
```

利用三阶 Newton identity

```math
6e_3=p_1^3-3p_1p_2+2p_3
```

得到

```math
\boxed{
K_q(H)=\frac16\left[
G_{2q}(H)^{\circ3}
-3G_{2q}(H)\circ G_{4q}(H)
+2G_{6q}(H)
\right].
}
```

再定义

```math
T_H(I,k)=\prod_{r\in I}H_{rk},
\qquad |I|=3.
```

对六阶 complex Hadamard `H`：

```math
\boxed{
T_H^*T_H
=18I_6+\frac13(H^{\circ3})^*H^{\circ3}.
}
```

更一般的 polarized identity 为

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

这些技术 lemma 独立于 MUB-six conjecture。后续应在有限子集与 elementary-symmetric polynomial 库检索后单独形式化。

## 7. 2026 cubic orientation 的逻辑边界

需要严格区分：

```math
\forall\pi,\ a_\pi b_\pi=0
```

和

```math
(\sum_\pi a_\pi)(\sum_\pi b_\pi)=0.
```

对非负 `a,b`，第二式推出第一式。第一式允许零侧随 `pi` 改变，因此一般不能推出第二式。

机器真源已经加入一个 `Fin 2` 精确反例：

```text
pointwise_product_zero_does_not_force_global_orientation
```

以及安全的正向蕴含：

```text
pointwise_product_zero_of_global_sum_product_zero
```

后续必须显式区分：

```text
pointwise cubic product vanishing
orientation coherence
global one-sided cubic vanishing
```

真正缺失的 coherence 命题应写为

```math
supp(a)\cap supp(b)=\varnothing
\Longrightarrow
a=0\ \text{or}\ b=0.
```

quartet 的 double-completion 条件可能提供 triplet-only 情形没有的额外刚性。

## 8. 2-circulant seed 与 Zauner factorization 的准确文献边界

Szöllősi 的 2-circulant order-six seed 使用

```math
H=\begin{pmatrix}A&B\\B^*&-A^*\end{pmatrix},
```

其中 `A,B` 是 entrywise-unimodular `3 x 3` circulant matrices。其 Hadamard 条件收缩为

```math
\frac ab+\frac bc+\frac ca+
\frac de+\frac ef+\frac fd=0.
```

Zauner factorization 将任意 `2m x 2m` 2-circulant unitary 写成

```math
T=Z_1^*Z_2,
```

其中

```math
Z_1(X)=\frac1{\sqrt2}
\begin{pmatrix}
F_m&XF_m\\
F_m&-XF_m
\end{pmatrix}
```

和相应的 `Z_2(U,V,Y)` 都是 flat unitaries。对 `m=3`，这从一个 2-circulant Hadamard seed 产生 MUB triplet。

需要保持文献边界：该 proposition 证明每个 2-circulant unitary 至少有一个这类 flat factorization。它没有证明固定 edge 的每个 MUB completion 都来自该 canonical factorization。因此 canonical fibre exclusion 不能直接升级为整个 strict-`X` family exclusion。

## 9. 一个 Fourier mode 的 exact two-point fibre

Fourier diagonalization 把 `6 x 6` 2-circulant unitary 分成三个 `2 x 2` modes

```math
S_k=\begin{pmatrix}a_k&b_k\\c_k&d_k\end{pmatrix}.
```

Zauner 的局部参数化为

```math
S=\frac12
\begin{pmatrix}
u+v & y(u-v)\\
(u-v)/x & y(u+v)/x
\end{pmatrix},
```

其中 `u,v,x,y` 为单位相位。清除除法后：

```math
u+v=2a,
\qquad y(u-v)=2b,
\qquad u-v=2cx,
\qquad y(u+v)=2dx.
```

已经形式化的二次后果是

```math
\boxed{cd\,x^2=ab,}
\qquad
\boxed{ac\,y^2=bd.}
```

前一版理论将 `x` 与 `y` 的符号视为彼此独立。进一步消元表明它们必须同步。

定义局部 involution

```math
\tau(u,v,x,y)=(v,u,-x,-y).
```

它保持四个局部 factorization equations。若 `cd\neq0` 且 `x\neq0`，那么同一 `2 x 2` mode 的任意两个 Zauner factors `z,w` 满足

```math
\boxed{w=z\quad\text{or}\quad w=\tau(z).}
```

证明结构如下：

1. `cd x^2=ab` 给出 `w.x=\pm z.x`。
2. 由 `b=ycx` 和 `cx\neq0`，`x` 的符号唯一决定 `y` 的同一符号。
3. 固定 `u+v` 与 `u-v` 后，正号给出 `(w.u,w.v)=(z.u,z.v)`，负号给出 `(w.u,w.v)=(z.v,z.u)`。

所以 local canonical fibre 是一个二点 cover，其 deck transformation 正是 `tau`。三个 Fourier modes 的 labelled canonical fibre至多为

```math
(\mathbb Z/2\mathbb Z)^3,
```

即八个点。之后还要再除以 mode relabeling、basis column gauge 和 family equivalence。

## 10. fixed-edge completion 的方向修正

这是上一版理论中必须修正的矩阵方向。

Zauner factorization 给出

```math
T=Z_1^*Z_2.
```

原 triplet 是

```math
\{I,Z_1,Z_2\}.
```

若把 edge `(Z_1,Z_2)` 共同左乘 `Z_1^*` 固定为 `(I,T)`，第三个基变为

```math
W=Z_1^*.
```

因此两个 factorization branches `Z_1,Z_1'` 对应的 fixed-edge completions 是

```math
W=Z_1^*,
\qquad W'=Z_1'^*.
```

它们的 relative transition 应检查

```math
W^*W'=Z_1Z_1'^*,
```

而不是 `Z_1^*Z_1'`。

现有 Lean theorem 关于 `Z_1^*Z_1'` 的零 off-diagonal block 仍是正确的 factor-relative 恒等式，但不能单独作为 fixed-edge completion 结论。后续真源必须增加正确方向。

## 11. canonical fixed-edge completions 的 24-zero obstruction

对

```math
Z_1(X)=\frac1{\sqrt2}
\begin{pmatrix}
F&XF\\
F&-XF
\end{pmatrix}
```

和 `F F^*=I`，直接 block multiplication 得

```math
\boxed{
Z_1(X)Z_1(X')^*
=\frac12
\begin{pmatrix}
I+XX'^*&I-XX'^*\\
I-XX'^*&I+XX'^*
\end{pmatrix}.
}
```

`X,X'` 都是 diagonal。于是四个 `3 x 3` blocks 全部 diagonal。任意不同 Fourier-mode indices `i\neq j` 都给出零 entry。

在 `m=3` 时，每个 `3 x 3` block 有六个 off-diagonal zeros，总计至少

```math
4\times6=24
```

个精确零 entry。因此：

```math
\boxed{
\text{任意两个 Zauner canonical fixed-edge completions
都不可能彼此 mutually unbiased.}
}
```

这个结论甚至不需要先使用 `X'=EX` 的 sign-branch 关系。只要两个 completion 都来自相同 Fourier block 的 Zauner canonical factorization，sparsity 已经足够排除 flat relative transition。

## 12. 2-circulant Hadamard seed 没有退化 Fourier mode

上一版理论把 local fibre jump 与 cubic discriminant `D[alpha]` 联系起来。进一步推理表明，局部 Zauner mode 在整个合法 2-circulant Hadamard seed 上都不能退化。以下是精确论证。

设 `rho^3=1`，假设 circulant block `A` 的某个 Fourier coefficient 为零：

```math
a+\rho b+\rho^2c=0.
```

三个 summands 都有单位模。三个单位圆点之和为零时，它们构成正三角形。因此存在 cube root `mu`，使三组 cyclic ratios 相等。等价地，存在 `t^3=1` 使

```math
\frac ab=\frac bc=\frac ca=t.
```

所以

```math
\frac ab+\frac bc+\frac ca=3t.
```

Hadamard condition 强制

```math
\frac de+\frac ef+\frac fd=-3t.
```

右侧模长为 `3`。三个单位复数之和达到 triangle inequality equality，只能三者全等：

```math
\frac de=\frac ef=\frac fd=-t.
```

但左侧三个 ratios 的乘积恒为 `1`，右侧乘积为

```math
(-t)^3=-1,
```

矛盾。因此 `A` 的任何三阶 Fourier coefficient都非零。交换 `A,B` 得到同样结论。

所以每个 `2 x 2` Fourier mode 的四个 entries 都非零。Zauner local factorization 始终处于上述二点 generic fibre，不存在由某个 block Fourier coefficient 消失所产生的连续 local phase。

这条 no-degenerate-mode lemma 是新的高价值中间定理。形式化时应复用：

```text
windowRoot 3
windowRoot_isPrimitiveRoot
FinitePoisson.character
Mathlib Matrix.circulant
```

并把证明拆为三个通用 lemma：

```text
three unit phases summing to zero form an equilateral triple
three unit phases with sum of norm three are equal
2-circulant Hadamard ratio condition forbids a zero Fourier mode
```

## 13. discriminant 路线的纠正与隔离

Szöllősi parameterization 的 cubic

```math
f_\alpha(x)=x^3-\alpha x^2+\bar\alpha x-1
```

具有 discriminant

```math
D[\alpha]
=|\alpha|^4+18|\alpha|^2-8\Re(\alpha^3)-27.
```

`D[alpha]=0` 描述的是 `X_6(alpha)` 构造参数的 root collision。第 12 节说明 local Zauner Fourier modes 在该 family 上仍不会因 block coefficient 消失而退化。

因此下面的旧推测目前没有支持：

```math
Ram(\pi_{completion})
\subseteq\{D[\alpha]D[-\alpha]=0\}.
```

本卷撤回其高优先级地位，并把它隔离为未证研究猜想。parameterization discriminant 与 MUB completion-map discriminant 是不同对象。除非建立明确的 morphism、Jacobian 或 fibre comparison theorem，不能把二者等同。

## 14. 真正剩余的是 noncanonical completion locus

对一个 normalized 2-circulant edge `T`，定义抽象 flat factorization fibre

```math
\mathcal F(T)=
\{F:\ F\text{ flat unitary and }FT\text{ flat unitary}\}.
```

若 `T=F^*(FT)`，则固定 edge `(I,T)` 的 completion 为 `F^*`。

Zauner construction 给出一个显式子集

```math
\mathcal Z(T)\subseteq\mathcal F(T),
```

称为 canonical factorization fibre。

第 9 节与第 12 节说明，`Z(T)` 在 labelled Fourier-mode 层面是有限二进 cover。第 11 节说明，任意两个 `Z(T)` 元素对应的 fixed-edge completions不能彼此 MUB。

因此若 strict-`X` edge 出现在 quartet 中，则至少一个额外 completion 必须位于

```math
\boxed{
\mathcal N(T)=\mathcal F(T)\setminus\mathcal Z(T),
}
```

即 noncanonical completion locus。

当前最准确的剩余命题是：

```math
\boxed{
T\in X_6(\alpha)
\Longrightarrow
\mathcal N(T)=\varnothing\ ?
}
```

这不是 Szöllősi Proposition 4.2 的直接推论。它接近 2026 triplet classification conjecture 在固定 strict-`X` edge 上的相对版本。

战略意义仍然很强。我们已经将此前“寻找任意两个 completions”的问题压缩为：

```text
canonical fibre: finite and internally excluded
residual problem: prove the noncanonical locus empty,
                  or prove every noncanonical point incompatible with the canonical fibre
```

## 15. strict-X 的 finite symmetry fallback

`X` family 的 `3 x 3` circulant blocks 带有 order-three monomial symmetry，其 permutation part 是 `(3)(3)`。

固定

```text
s=(123)(456).
```

另一条同型 permutation 在 `s` 的 centralizer 下，40 个候选分成六个 orbit：

```text
1 + 1 + 2 + 9 + 9 + 18 = 40,
```

对应生成 permutation groups 的阶：

```text
3, 3, 9, 12, 12, 60.
```

因此如果 noncanonical completion locus 无法整体消去，仍可把其 permutation alignment 分成六个有限 skeleton。

共同 `Z3` aligned branch 可进一步分解环境空间为三个二维 eigenspaces：

```math
E_0\oplus E_1\oplus E_2,
\qquad \dim E_r=2.
```

兼容基可参数化为三个 `U(2)` matrices `A_r`，两基 MUB 条件化为

```math
\left|\sum_{r=0}^2
\omega^{rn}(A_r^*B_r)_{st}\right|^2=\frac32.
```

这提供了 noncanonical residual 的有限对称性 fallback。

## 16. 形式化队列，严格一模块推进

### M01. local two-point Zauner fibre

落点：

```text
D5/S3/Quantum/Tomography/MUBCubeCompatibility.lean
```

先复用当前 `ZaunerTwoByTwoFactor`，加入：

```text
ZaunerTwoByTwoFactor.swap
zaunerTwoByTwo_swap_swap
zaunerTwoByTwo_same_or_swap
```

目标是把两个独立 sign lemmas升级为相关符号的完整二点 fibre theorem。

### M02. fixed-edge completion-adjoint cross-Gram

落点：

```text
D5/S3/Quantum/Tomography/ZaunerCompletionFibre.lean
```

在现有 `zaunerLeftFactor` 上证明正确方向：

```text
zaunerLeftFactor_mul_conjTranspose_apply
zaunerCompletion_crossGram_offMode_zero
zaunerCanonicalCompletions_not_unbiased
```

先用抽象 `F*F^*=I`，暂时不新建 Fourier matrix。

### M03. no degenerate Fourier mode

先库检索和复用：

```text
D5/S3/Observer/WindowRegister.lean
D5/S3/Fourier/FinitePoisson.lean
Mathlib.LinearAlgebra.Matrix.Circulant
```

再建立三单位相位的 equilateral / triangle-equality lemmas，最后证明 order-six 2-circulant Hadamard ratio condition 排除零 mode。

### M04. noncanonical completion interface

只有在 M01 至 M03 machine-green 后才定义 `FlatFactorizationFibre` 与 `ZaunerCanonicalFibre`。定义前再次检索仓库和 Mathlib 的 flat matrix、unitary matrix、factorization carrier，避免重复建模。

### M05. Newton-Gram truth source

与 noncanonical fibre 分支并行，但仍单模块排队。先复用 finite-subset、elementary symmetric polynomial 和 Gram matrix 库，再形式化 polarized cubic identity。

## 17. 当前证明链与真实边界

当前路线更新为：

```text
order-six Hadamard atlas
 -> fixed-edge completion fibre
 -> Zauner canonical subfibre
 -> local exact two-point involution
 -> no degenerate Fourier mode
 -> correct completion-adjoint cross-Gram sparsity
 -> canonical subfibre cannot supply a quartet
 -> isolate noncanonical completion locus
 -> prove it empty or incompatible
 -> feature-kernel / finite-symmetry branch certificates
 -> global four-MUB exclusion
```

已证明或已有 Lean source：

```text
lifted Hadamard-atlas reduction
independent-representative quotient obstruction
cube cross-Gram factorization
local x^2 and y^2 equations
pointwise/global orientation separation
factor-relative Zauner zero blocks
```

本轮理论推导稳定、等待逐模块形式化：

```text
local factor fibre is exactly {z, swap z}
fixed-edge completion product uses Z1 Z1'^*
canonical completion relative matrix has 24 structural zeros in order six
2-circulant Hadamard seeds have no zero Fourier mode
```

仍开放：

```text
all fixed-edge completions are canonical
noncanonical completion locus is empty or incompatible
quartet-specific moment kernel
strict-X residual exclusion
all-branch four-MUB exclusion
```

## 18. 可证伪边界

以下任一精确对象都会推翻相应中间命题：

- 同一非退化 `2 x 2` mode 的第三个 Zauner factor，不等于原 factor 或其 swap；
- 两个 canonical Zauner fixed-edge completions，其 relative transition 没有预测的 structural zeros；
- 一个满足 2-circulant Hadamard ratio condition 的 seed，某个 block Fourier coefficient为零；
- 一个 strict-`X` edge，拥有可参与 quartet 的 noncanonical completion；
- 一个 exact quartet `I,H,C,D`。

后续推理继续追加到本卷。形式化只承接已经得到稳定数学陈述的节点。