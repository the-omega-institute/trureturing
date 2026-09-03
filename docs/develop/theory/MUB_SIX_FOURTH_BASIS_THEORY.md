# MUB Six Fourth-Basis Research Theory

> **统一理论卷规则。** 六维四互无偏基 research lane 的新增推理统一追加到本卷。Lean 真源、Scribe 和 Blueprint 可以按节点拆分，理论叙事只维护这一份主卷。
>
> **状态边界。** 本卷包含已证明恒等式、文献输入、条件归约、待证猜想与长期目标。当前没有宣称解决六维四 MUB 开放问题。

## 0. 总目标

目标是判断是否存在四个两两 mutually unbiased orthonormal bases in `C^6`。

固定第一基为坐标基后，另外三个基可以写成六阶 complex Hadamard matrices。仓库已经建立：

```text
RankOneContext
centered projector plane
commutator / incompatibility
ComplexHadamard
HadamardEquivalent
HadamardUnbiased
exact Hadamard atlas
lifted four-MUB compatibility
```

2026 年 order-six Hadamard 完整分类 claim 提供单矩阵 atlas。2026 年 centered-projector SoS 结果说明正确坐标能够恢复一般 `m <= d+1` 上界，但在 `d=6,m=4` 时一般 rank certificate 严格为正，因此真正的 fourth-basis obstruction 必须使用六阶专属代数结构。

## 1. 固定 edge，而不是同时搜索三个 Hadamard matrices

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

这比分类所有 MUB triplets 更窄，因为 quartet 自带一个额外的 cross-completion 方程。

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

这里 `circ` 是 entrywise Hadamard product。

这条恒等式已经进入机器真源：

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

所以两个 completion 的两个 relative transitions 并不独立。quartet gluing 消掉了一个完整相对矩阵。

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

在 `d=6`，两个空间都是五维。这正是 centered rank-one projector context planes 的正交结构。Hadamard cube 与 centered-projector SoS 因而共享同一个去掉全一方向后的信息几何。

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

## 6. Newton-Gram identity

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

特别地，`q=1` 和 `q=3` 的大规模 permutation moment 条件都可变为六阶小矩阵的指定核向量问题。这为 exact determinant factorization、resultant、rational SDP dual 与 branch-wise SoS 提供了低维入口。

## 7. cubic square-free Gram identity

定义

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

这是独立于 MUB-six conjecture 的技术 lemma，后续应作为单独 Lean 真源验证。

## 8. 2026 cubic orientation 的逻辑边界

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

因此后续必须显式区分：

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

## 9. 新主线：completion fibre 的离散化与 ramification locus

这是目前最有希望的新压缩。

Szöllősi/Zauner 的 `2`-circulant construction 把一个 `6 x 6` 2-circulant unitary 经过 `F_3` block diagonalization 分裂成三个独立的 `2 x 2` unitaries

```math
S_k=\begin{pmatrix}a_k&b_k\\c_k&d_k\end{pmatrix}.
```

每个 block 使用 unimodular 参数 `u,v,x,y` 表示：

```math
S=\frac12
\begin{pmatrix}
u+v & y(u-v)\\
(u-v)/x & y(u+v)/x
\end{pmatrix}.
```

清除除法后，固定 block entries 会强制

```math
\boxed{cd\,x^2=ab,}
```

以及

```math
\boxed{ac\,y^2=bd.}
```

所以在 `cd != 0` 与 `ac != 0` 的 generic locus 上，两个 factorization 的 `x` 或 `y` 至多相差一个符号。

这些结论已经形式化为：

```text
ZaunerTwoByTwoFactor
zaunerTwoByTwo_x_quadratic
zaunerTwoByTwo_y_quadratic
zaunerTwoByTwo_x_eq_or_eq_neg
zaunerTwoByTwo_y_eq_or_eq_neg
```

这意味着 generic `2`-circulant edge 的 canonical Zauner factorization fibre 不是连续二维自由度。每个 Fourier mode 只有二值 branch，三个 mode 最多先产生 `2^3` 型离散分支，再继续除去 basis permutations、phase gauges 与 mode relabeling。

### 9.1 更强的候选结论

quartet 需要同一 edge 上存在两个彼此无偏的 distinct completions。因此值得定义

```math
\mathrm{Mult}(H)=
\text{completion fibre modulo the MUB-preserving gauge}.
```

如果能证明 generic strict-`X` edge 满足

```math
|\mathrm{Mult}(H)|=1,
```

则 quartet 只能落在 completion map 的 fibre-jump locus。

即：

```math
\boxed{
\text{quartet}
\Longrightarrow
H\in\mathrm{Ram}(\pi_{completion}).
}
```

这里 `Ram` 表示 completion projection 的非泛型多重 fibre / discriminant locus。

Szöllősi 的 `X_6(alpha)` 构造本身已经由 cubic

```math
f_\alpha(x)=x^3-\alpha x^2+\bar\alpha x-1
```

控制，且 discriminant 为

```math
D[\alpha]
=|\alpha|^4+18|\alpha|^2-8\Re(\alpha^3)-27.
```

其边界正由 root collision `D[alpha]=0` 或 `D[-alpha]=0` 描述。因而 completion fibre jump 与既有 cubic discriminant geometry 之间存在一个非常自然的接口。

当前尚未证明 `Ram(pi_completion)` 与 `D[alpha]D[-alpha]=0` 完全一致。这个关系现在应成为高优先级研究问题。

## 10. canonical Zauner completions 之间出现 block-zero obstruction

Zauner factorization 的一个左因子具有 block form

```math
Z_1(X)=\frac1{\sqrt2}
\begin{pmatrix}
F_3 & XF_3\\
F_3 & -XF_3
\end{pmatrix},
```

其中 `X` 为 diagonal phase matrix。

若同一个固定 `2`-circulant block 的另一离散 factor branch 只改变局部二值选择，则可写成 `X'=EX`，其中 `E` 是 diagonal sign matrix。

直接矩阵乘法得到

```math
\boxed{
Z_1(X)^*Z_1(X')
=
\begin{pmatrix}
I_3 & 0\\
0 & F_3^*EF_3
\end{pmatrix}.
}
```

所以两个这样的 canonical completions 的 relative transition 含整个 zero off-diagonal block，绝不可能是 flat Hadamard transition。

这是非常重要的局部排除：

```text
同一 2-circulant edge 的 Zauner canonical discrete branches
彼此不能成为 quartet 中的第三、第四基。
```

它还没有排除“一个固定 strict-X edge 存在非-Zauner-form 的额外 completion”。真正剩余的主问题因而进一步缩小为：

```math
\boxed{
\text{Every completion of a generic strict-X edge is gauge-equivalent
 to a Zauner canonical completion?}
}
```

如果该 completeness statement 成立，generic strict-X sector 会被一次性排除。

## 11. strict-X 的 finite symmetry skeleton

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

因此 all-strict-X triangle 的 permutation alignment 是有限六分支问题。

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

因此 fibre-completeness 失败时，仍可回退到六个有限 symmetry skeleton 上逐分支建立精确排除证书。

## 12. 当前优先证明链

现在研究优先级调整为：

```text
A. cube cross-Gram identity                         [Lean source exists]
B. local Zauner 2x2 quadratic rigidity            [Lean source exists]
C. canonical sign-branch cross transition has zero blocks
D. characterize all completions of a generic 2-circulant edge
E. identify fibre-jump / discriminant locus
F. exclude the discriminant locus using Fourier seams, exceptional points,
   or exact branch certificates
G. in parallel formalize Newton-Gram / feature-kernel identities
H. only if needed, use six strict-X symmetry skeletons
```

这一顺序比直接解决 2026 triplet Conjecture 2 更窄。它直接利用 quartet 必须在同一 edge 上拥有两个兼容 completions 这一额外信息。

## 13. 可证伪边界

以下任一精确对象都会推翻相应中间猜想：

- 一个 generic strict-X edge，拥有两个 gauge-inequivalent completions；
- 两个 canonical Zauner sign branches，其 relative transition 实际 flat；
- 一个 completion fibre jump 出现在候选 discriminant locus 之外；
- 一个 exact quartet `I,H,C,D`。

因此每一步都可通过 exact symbolic calculation、interval certification 或 Lean theorem 独立检验。

## 14. 冻结后的研究主线

```text
order-six Hadamard atlas
 -> fixed-edge completion fibre
 -> local 2x2 Fourier-mode rigidity
 -> discrete canonical completion branches
 -> cross-branch zero-block obstruction
 -> fibre completeness or ramification locus
 -> centered-projector / feature-kernel certificate
 -> exceptional branch exclusion
 -> global four-MUB exclusion
```

后续推理继续追加到本卷。形式化只承接已经得到稳定数学陈述的节点。