# MUB Six Fourth-Basis Research Theory

> **统一理论卷规则。** 六维四互无偏基 research lane 的新理论推理统一追加到本文件。Lean 节点继续拥有独立 GID、Scribe 与 Blueprint 投影，不再为每一个局部 obstruction 建立新的 theory 文档。
>
> **状态约定。** 本卷明确区分机器已证、直接推导、文献输入、条件归约和开放猜想。任何局部分支证书都不得被表述为六维四 MUB 已经解决。

## 0. 开放目标与仓库接口

目标是判断是否存在四个两两 mutually unbiased orthonormal bases in `C^6`。

固定第一基为坐标基以后，另外三个基可表示为六阶 complex Hadamard matrices。仓库当前已经具有：

```text
RankOneContext
centeredProjector
centeredContextPlane
overlap / incompatibility
rank-one commutator conservation
tomography and purity Pythagoras
complex Hadamard and Hadamard-unbiased transitions
exact Hadamard atlas consumer contract
```

本研究线复用这些对象。有限 Fourier 与三循环 character 运算优先复用：

```text
D5/S3/Fourier/FinitePoisson.lean
D5/S3/Observer/WindowRegister.lean
```

不在 MUB 文件中重新建立一套离散 Fourier 库。

当前总路线是：

```text
order-six Hadamard atlas
  -> fixed-edge completion fibre
  -> two compatible completions
  -> centered-projector / symmetry-plane sharp bound
  -> Fourier and strict-2-circulant branch certificates
  -> global atlas aggregation
```

## 1. 标准 Hadamard 归约与规范边界

固定 `B0 = I`，其余三个基写为无归一化 Hadamard matrices：

```math
H_r H_r^\dagger = 6I,
\qquad |(H_r)_{ij}|^2=1.
```

两基互无偏等价于：

```math
|(H_r^\dagger H_s)_{ij}|^2=6.
```

单矩阵标准等价允许独立行列置换与单位相位：

```math
H\mapsto D_rP_rHP_cD_c.
```

多矩阵 compatibility 只允许一个共同 ambient left gauge。独立选择三个 Hadamard 等价类的 canonical representatives 会丢失相对左规范。仓库已经用二维精确反例机器证明 MUB compatibility 不下降到独立 Hadamard classes。

因此 2026 order-six classification 的正确消费者是带显式 lifts 的 atlas compatibility，而不是 class-name triple。

## 2. fixed-edge completion fibre

设固定边为：

```math
(I,T).
```

定义 factor fibre：

```math
\mathcal F(T)=
\{F\in U(6):F\text{ flat},\ FT\text{ flat}\}.
```

若 `F in F(T)`，则：

```math
W=F^\dagger
```

给出同时无偏于 `I` 与 `T` 的第三基。反过来也成立。因此 completion fibre 可以用 factor fibre 表示。

若 `F,F' in F(T)` 对应两个 completions `W=F^dagger` 与 `W'=F'^dagger`，则：

```math
W^\dagger W'=FF'^\dagger.
```

所以 quartet 条件是：

```math
\boxed{
F,F'\in\mathcal F(T),
\qquad FF'^\dagger\text{ flat}.
}
```

定义：

```math
\mathcal E_6^{(1)}=
\{T:\mathcal F(T)\ne\varnothing\},
```

以及：

```math
\mathcal E_6^{(2)}=
\{T:\exists F,F'\in\mathcal F(T),\ FF'^\dagger\text{ flat}\}.
```

四 MUB 问题等价于：

```math
\boxed{\mathcal E_6^{(2)}=\varnothing.}
```

`E_6^(2)` 比全部 MUB triplet support `E_6^(1)` 更小。quartet-specific cross condition 应当在第一步就参与消元。

## 3. Hadamard-cube cross Gram

对共享底面 `H` 的两个 factorized cube slices：

```math
C_{ijk}=H_{ij}X_{jk}Y_{ik},
```

```math
D_{ij\ell}=H_{ij}X'_{j\ell}Y'_{i\ell},
```

entrywise unimodularity of `H` 给出：

```math
\boxed{
C^\dagger D=(X^\dagger X')\circ(Y^\dagger Y').
}
```

这里 `circ` 是 entrywise Hadamard product。该恒等式已经写入 Lean 真源。

若归一化后的两个相对矩阵 `A,B` 都 unitary，且：

```math
A\circ B=d^{-1}J,
```

则逐行 Cauchy equality 迫使：

```math
|A_{ij}|=|B_{ij}|=d^{-1/2},
\qquad B=\overline A.
```

这说明 double completion 的两个方向不能独立变化。一个相对 transition 由另一个决定。

## 4. cube 与 centered projector plane 的同一性

归一化写：

```math
\widehat C=C/d,
\qquad
\widehat D=D/d,
\qquad
u=d^{-1/2}\mathbf 1_d.
```

quartet cross Gram 化为：

```math
\widehat C^\dagger\widehat D=uu^\dagger.
```

于是：

```math
\widehat C(u^\perp)\perp\widehat D(u^\perp).
```

在 `d=6`，两个 image 都是五维空间。它们正是去掉 identity direction 后的 centered rank-one context planes。

所以 Hadamard cube、projector-coordinate SoS 和 tomography Pythagoras 描述的是同一 geometry：

```text
common all-one direction
  + orthogonal five-dimensional information planes.
```

## 5. centered rank-one quadratic variety

对 rank-one projector `P` 定义：

```math
Q=P-I/d.
```

由 `P^2=P` 直接得到：

```math
Q^2=(1-2/d)Q+(d-1)d^{-2}I.
```

在六维：

```math
\boxed{
Q^2=\frac23Q+\frac5{36}I.
}
```

同时：

```math
\operatorname{Tr}Q=0,
\qquad
\operatorname{Tr}(Q^2)=5/6.
```

同一 basis 的六个 centered projectors 构成 regular `5`-simplex：

```math
\operatorname{Tr}(Q_iQ_j)=-1/6
\quad(i\ne j).
```

不同 MUB contexts 之间：

```math
\operatorname{Tr}(Q_iR_j)=0.
```

一般 `m<=d+1` 上界只利用 plane packing。六维 `m=4` 必须进一步利用 rank-one quadratic variety 与 order-six branch equations 的交。

## 6. feature kernels 与 Newton-Gram 压缩

对六阶 Hadamard `H`，对三元素子集 `I subset {1,...,6}` 定义：

```math
\mu(I)_i=1\quad(i\in I),
\qquad
\mu(I)_i=-1\quad(i\notin I).
```

定义列乘积：

```math
\delta_k(H)=\prod_iH_{ik}.
```

对奇数 `q` 定义 square-free feature matrix：

```math
V_q(H)_{I,k}
=
\left(\prod_{i\in I}H_{ik}\right)^{2q}.
```

由 unimodularity：

```math
\boxed{
g_H(q\mu(\cdot))
=V_q(H)\overline{\delta(H)^q}.
}
```

定义：

```math
K_q(H)=V_q(H)^\dagger V_q(H).
```

则：

```math
V_q(H)x=0
\iff
K_q(H)x=0.
```

令：

```math
G_m(H)=(H^{\circ m})^\dagger H^{\circ m}.
```

Newton identity `6e_3=p_1^3-3p_1p_2+2p_3` 给出：

```math
\boxed{
K_q(H)=\frac16
\left[
G_{2q}(H)^{\circ3}
-3G_{2q}(H)\circ G_{4q}(H)
+2G_{6q}(H)
\right].
}
```

所以 20 个三三分割 feature equations 可压缩为一个 `6 x 6` prescribed-kernel condition。

这条路线保留为 exceptional-locus certificate。当前不把它作为 generic strict-X 分支的唯一入口。

## 7. cubic orientation 的逻辑边界

对非负 families `a_pi,b_pi`，必须区分：

```math
\forall\pi,\ a_\pi b_\pi=0
```

与：

```math
\left(\sum_\pi a_\pi\right)
\left(\sum_\pi b_\pi\right)=0.
```

第二式推出第一式。第一式一般不推出第二式，因为零的一侧可以随 `pi` 改变。仓库已经用 `Fin 2` 非负反例机器证明这一点。

因此任何依赖 global orientation 的论证都必须额外证明 orientation coherence：

```math
\operatorname{supp}(a)\cap\operatorname{supp}(b)=\varnothing
\Longrightarrow
a=0\text{ or }b=0.
```

该 coherence 当前仍是开放桥。

## 8. strict 2-circulant edge 的三模式分解

令 strict-X edge `T` 与 order-three shift：

```math
S=\operatorname{diag}(P_3,P_3)
```

交换。令 block Fourier unitary `Q` diagonalize `S`。则：

```math
D=QTQ^\dagger
=
T_0\oplus T_1\oplus T_2,
```

其中每个：

```math
T_k\in U(2).
```

对 factor `F in F(T)` 定义 mode-coordinate matrix：

```math
U=FQ^\dagger.
```

则 fixed-edge equations 精确化为：

```math
U\text{ unitary},
\qquad UQ\text{ flat},
\qquad UDQ\text{ flat}.
```

对第二个 factor `F'`，令 `U'=F'Q^dagger`。两 completions 互无偏等价于：

```math
UU'^\dagger\text{ flat}.
```

这里 cross condition 不再含 `Q` 或 `D`。这是 strict-X quartet 的最小 mode-coordinate carrier。

## 9. Zauner local fibre

一个 mode block 可参数化为：

```math
S(u,v,x,y)
=
\frac12
\begin{pmatrix}
u+v&y(u-v)\\
(u-v)/x&y(u+v)/x
\end{pmatrix}.
```

对固定 matrix entries `a,b,c,d`，直接消元得到：

```math
\boxed{cdx^2=ab,}
```

```math
\boxed{acy^2=bd.}
```

在非零 generic locus，若两组参数表示同一 block，则：

```math
x'=\pm x,
\qquad
y'=\pm y.
```

继续利用 `u+v` 与 `u-v` 可得到更强的二点 fibre：

```math
(u',v',x',y')=(u,v,x,y)
```

或：

```math
(u',v',x',y')=(v,u,-x,-y).
```

这些 local identities 已写入 Lean。它们将每个 generic mode 的 factor ambiguity 降到一个 involution。

## 10. fixed-edge 方向修正与 canonical sparsity

若：

```math
T=Z_1^\dagger Z_2,
```

则固定边 `(I,T)` 的 completion 是：

```math
W=Z_1^\dagger.
```

所以两个 branches 的真实 transition 是：

```math
W^\dagger W'=Z_1Z_1'^\dagger.
```

必须检查 `Z_1Z_1'^dagger`，不能误用 `Z_1^dagger Z_1'`。

对 normalized three-Fourier block `F_3` 和 diagonal phases `X,X'`：

```math
Z_1(X)=
\frac1{\sqrt2}
\begin{pmatrix}
F_3&XF_3\\
F_3&-XF_3
\end{pmatrix}.
```

直接计算：

```math
Z_1(X)Z_1(X')^\dagger
=
\frac12
\begin{pmatrix}
I+XX'^\dagger&I-XX'^\dagger\\
I-XX'^\dagger&I+XX'^\dagger
\end{pmatrix}.
```

四个 `3 x 3` blocks 都 diagonal。因此所有 distinct-mode entries 为零。在 order six 中有 24 个结构零，故两个 canonical Zauner completions 不可能 mutually unbiased。

当前 PR 已加入正确 adjoint direction 的 Lean theorem。其 admission 状态必须以最新 CI 为准。

## 11. canonical completion 的 Fourier/Diţă 身份

`Z_1(X)` 是 `F_2 tensor F_3` 的 Diţă deformation。对 row/column phases 与 permutations 取商以后，diagonal `X` 只留下两个独立 phase ratios，因此属于 order-six Fourier two-parameter family。

fixed-edge canonical completion 是 `Z_1(X)^dagger`。pair unextendibility 在 adjoint 下保持：若 quartet 含 `I` 与 `Z_1^dagger`，左乘 `Z_1` 并交换前两基，就得到含 `I` 与 `Z_1` 的 quartet。

所以已有 Fourier-family quartet exclusion 可推出：

```math
\boxed{
\text{假想 strict-X quartet 的两个 extra completions
都必须落在 noncanonical mode-mixing locus。}
}
```

这是文献输入与直接 gauge 推导的组合。Fourier-family exclusion 在 Lean 中仍应作为待移植外部定理，不应无证明 postulate 进入主真源。

## 12. mode-local 的 intrinsic characterization

令：

```math
\Lambda=QSQ^\dagger,
```

其中 `Lambda` 有三个不同 eigenvalues，每个 multiplicity 为 2。

对 `U=FQ^dagger`，以下条件等价：

1. 每一行 `U_r` 只支持一个 Fourier mode；
2. 在行置换后，`U=L_0 direct-sum L_1 direct-sum L_2`；
3. `FSF^dagger=U Lambda U^dagger` 是 diagonal，且三个 eigenvalues 各出现两次。

如果 `F` 与 `FT` 都 flat，则每个 `L_k` 和 `L_kT_k` 都是 flat `2 x 2` unitaries。接入第 9 节的 local two-point fibre 后，mode-local factor 正是 canonical Zauner factor，直到允许的 monomial gauges。

因此真正剩余的 fibre 是：

```math
\mathcal N(T)
=
\mathcal F(T)\setminus\mathcal F_{mode-local}(T).
```

它由 genuinely mode-mixing solutions 构成。

## 13. 三循环 DFT 的 exact row equations

把 `U` 的一行写成：

```math
u_{r,a,k},
\qquad
a\in\{0,1\},
\quad k\in\mathbb Z_3.
```

`UQ` flat 当且仅当每个 channel 的 length-three Fourier output 具有常模。利用 character orthogonality，这等价于：

```math
\sum_k|u_{r,a,k}|^2=1/2,
```

以及唯一独立的 nonzero cyclic autocorrelation：

```math
\boxed{
\sum_k u_{r,a,k}\overline{u_{r,a,k+1}}=0.
}
```

令 transformed mode row：

```math
\widetilde u_{r,\cdot,k}=u_{r,\cdot,k}T_k.
```

`UDQ` flat 等价于对 `tilde u` 重复同一组 energy 与 autocorrelation equations。

再加：

```math
\sum_{a,k}u_{r,a,k}\overline{u_{s,a,k}}=\delta_{rs},
```

以及 pair condition：

```math
\left|
\sum_{a,k}u_{r,a,k}\overline{u'_{s,a,k}}
\right|^2=1/6,
```

就得到 strict-X double-completion 的 compact polynomial system。

这一步应通过 `FinitePoisson` 和 `WindowRegister` 的 primitive character 复用完成。只在现有库没有 constant-modulus/autocorrelation adapter 时增加薄层 theorem。

## 14. mode probabilities 与 mixing energy

定义 rank-two mode projections：

```math
E_0,E_1,E_2,
\qquad
E_0+E_1+E_2=I.
```

对 completion basis `C={P_i}`，定义：

```math
p_{ik}=\operatorname{Tr}(P_iE_k).
```

每个 `p_i=(p_i0,p_i1,p_i2)` 是 probability vector。

定义 total mode mixing：

```math
M_S(C)=
\sum_i\left(1-\sum_kp_{ik}^2\right).
```

它满足：

```math
0\le M_S(C)\le4.
```

`M_S(C)=0` 当且仅当每个 basis vector 只支持一个 mode。结合 unitarity，每个 mode 正好容纳两个 vectors，因此这正是 mode-local locus。

`M_S(C)=4` 当且仅当：

```math
p_{ik}=1/3
```

对全部 `i,k` 成立。

## 15. symmetry-plane affinity

定义 centered mode projectors：

```math
X_k=E_k-I/3.
```

它们张成二维 symmetry plane：

```math
V_S=\operatorname{span}\{X_0,X_1,X_2\}.
```

对 completion context plane `V_C` 定义 chordal affinity：

```math
\alpha_S(C)=
\operatorname{Tr}(\Pi_{V_C}\Pi_{V_S}).
```

由于 `{X_k}` 是 frame bound `2` 的 regular two-simplex，而 centered basis projectors 是 `V_C` 的 Parseval simplex frame，可得：

```math
\boxed{
\alpha_S(C)
=
\frac12
\sum_{i,k}
\left(p_{ik}-\frac13\right)^2.
}
```

展开得到：

```math
\boxed{
\alpha_S(C)
=
\frac12\left(\sum_{i,k}p_{ik}^2-2\right).
}
```

因此：

```math
\boxed{
M_S(C)=4-2\alpha_S(C).
}
```

`alpha=2` 是 mode-local。`alpha=0` 是对 mode PVM 完全均匀。

## 16. order-three symmetry expectation 与 commutator 表达

令：

```math
S=E_0+\omega E_1+\omega^2E_2,
\qquad
1+\omega+\omega^2=0.
```

对 probability vector `p_i`：

```math
\left|
\operatorname{Tr}(P_iS)
\right|^2
=
\frac{3\sum_kp_{ik}^2-1}{2}.
```

求和得到：

```math
\boxed{
\alpha_S(C)
=
\frac13
\sum_i
\left|
\operatorname{Tr}(P_iS)
\right|^2.
}
```

对 rank-one `P_i` 与 unitary `S`：

```math
\|[P_i,S]\|_{HS}^2
=
2\left(1-
|\operatorname{Tr}(P_iS)|^2
\right).
```

所以：

```math
\boxed{
\alpha_S(C)
=
2-
\frac16
\sum_i\|[P_i,S]\|_{HS}^2.
}
```

这把 symmetry affinity 直接接到仓库现有 commutator conservation 语言。

## 17. 两个 MUB completions 的 symmetry budget

若 completion contexts `C,D` 彼此 mutually unbiased，则：

```math
V_C\perp V_D.
```

对二维 `V_S` 使用 Bessel/Pythagoras：

```math
\boxed{
\alpha_S(C)+\alpha_S(D)\le2.
}
```

等价地：

```math
\boxed{
M_S(C)+M_S(D)\ge4.
}
```

更精确的 residual identity 是：

```math
2-\alpha_S(C)-\alpha_S(D)
=
\operatorname{Tr}
\left(
\Pi_{V_S}
(I-\Pi_{V_C}-\Pi_{V_D})
\right)
\ge0.
```

如果 `C` mode-local，则 `alpha_S(C)=2`。任何与它 MUB 的 `D` 必须满足 `alpha_S(D)=0`，即所有 mode probabilities 都为 `1/3`。

这一结论独立于 Fourier-family exclusion，且可以通过仓库现有 `mutually_unbiased_diagonal_planes` 与 purity Pythagoras 形式化。

## 18. 新的 strict-X sharp-bound target

对固定 strict-X edge `T`，定义：

```math
\alpha_{min}(T)
=
\inf_{C\in\mathfrak C(T)}
\alpha_S(C).
```

若证明：

```math
\boxed{
\alpha_{min}(T)>1,
}
```

则任意两个 completions `C,D` 都满足：

```math
\alpha_S(C)+\alpha_S(D)>2,
```

与第 17 节的 MUB budget 矛盾。因此整个 fixed-edge branch 被排除。

这个目标明显弱于“所有 completions 都 canonical”或“noncanonical fibre 为空”。它只要求一个标量下界。

对闭 branch domain，还可以采用：

```math
\alpha_S(C)\ge1+\varepsilon(T)
```

或统一：

```math
\alpha_S(C)\ge1+\varepsilon
```

其中 `epsilon>0` 由 exact algebraic certificate 验证。

如果只能得到 `alpha>=1`，则继续分类 equality locus，并证明两个 equality completions 不能兼容，也足以闭合。

## 19. 为什么该目标适合 centered-projector SoS

在 projector coordinates 中：

```math
p_{ik}=\operatorname{Tr}(P_iE_k)
```

是线性的，`alpha` 是二次多项式。rank-one 条件：

```math
P_i^2=P_i
```

也是二次。orthogonality、completeness 和 fixed-edge unbiasedness 都可以写成低次 polynomial constraints。

因此 branch-specific sharp bound 可以寻找 exact certificate：

```math
\alpha_S(C)-1-\varepsilon
=
\sum_a s_a^2
+
\sum_j q_jf_j
+
\sum_kt_kg_k,
```

其中：

```text
f_j = 0
```

是 rank-one、basis、MUB 与 Hadamard branch equations，

```text
g_k >= 0
```

是 compact parameter-domain constraints。

数值 SDP 负责发现 Gram matrix。最终使用 rational reconstruction、algebraic-number reduction 或 interval enclosure，把证书转成 Lean 可检查的 polynomial identity。

这正是 2026 projector-coordinate SoS 结果给出的编码教训。一般 `m<=d+1` certificate 在 `m=4,d=6` 不足，branch-specific symmetry affinity 提供缺失的 order-six information。

## 20. no-degenerate Fourier-mode lemma

在 2-circulant construction 中，设一个 circulant row 由 unit phases `a,b,c` 给出。若某个 three-Fourier coefficient 消失：

```math
a+\rho b+\rho^2c=0,
\qquad \rho^3=1,
```

则三个 unit numbers `a,rho b,rho^2c` 构成 equilateral triple。纯代数地，若 unit `z_0+z_1+z_2=0`，则：

```math
z_0/z_1=z_1/z_2=z_2/z_0,
```

且公共 ratio 是非平凡 cube root。

因此：

```math
a/b=b/c=c/a=t,
\qquad t^3=1.
```

结合 2-circulant ratio equation，另一组三个 unit ratios 的和被迫等于 `-3t`。triangle equality 迫使三者均为 `-t`，其乘积为 `-1`，与 cyclic ratio product `1` 矛盾。

所以 generic 2-circulant Hadamard seed 的三个 Fourier modes都非零。该 lemma 可消除 local fibre quadratic 中的 denominator-degenerate cases。

形式化时先检索项目和 Mathlib 是否已有：

```text
three unit vectors summing to zero
triangle equality for unit complex numbers
primitive cube-root ratio lemmas
```

若没有，再建立通用小 lemma。不得把它埋入 order-six 专用证明中。

## 21. finite symmetry skeleton 作为备用分支

strict-X edge 携带 cycle type `(3)(3)` 的 monomial symmetry。固定一个 permutation：

```text
s=(123)(456).
```

另一个同 cycle type permutation 在 `s` 的 centralizer 下分成六个 orbits：

```text
1 + 1 + 2 + 9 + 9 + 18 = 40.
```

相应生成群阶：

```text
3, 3, 9, 12, 12, 60.
```

如果 scalar affinity bound 在某 exceptional locus 取 equality，这六个 finite permutation skeleton 提供第二层分解。aligned `Z3` 情形可降到三个 `U(2)` blocks；transitive order-12 和 order-60 情形可利用有限群 representation constraints。

## 22. 形式化队列与先库后证要求

### M02. 正确 fixed-edge canonical sparsity

目标：

```text
zaunerLeftFactor_mul_conjTranspose_offMode_zero
zaunerCanonicalCompletion_crossGram_not_nonzero_flat
```

状态：Lean source 已写入当前 PR。最终状态以 admission CI 为准。

### M03. finite three-Fourier autocorrelation adapter

先复用：

```text
FinitePoisson.character
windowRoot
windowRoot_isPrimitiveRoot
```

证明 normalized length-three transform constant-modulus 与 nonzero cyclic autocorrelation vanishing 的等价。该 theorem 服务于第 13 节，不重建通用 DFT 理论。

### M04. symmetry affinity algebra

证明：

```math
\alpha_S(C)
=\frac12(\sum p_{ik}^2-2),
```

```math
M_S(C)=4-2\alpha_S(C),
```

以及 order-three expectation formula。

### M05. MUB symmetry budget

复用：

```text
mutually_unbiased_diagonal_planes
PurityPythagorasDecomposition
```

证明：

```math
\alpha_S(C)+\alpha_S(D)\le2.
```

### M06. branch-specific lower bound

先进行 symbolic/numerical discovery，再提交 exact certificate。证书必须验证完整 compact branch domain，不接受 optimizer failure 或 floating-point dual 作为结论。

### M07. exceptional/equality locus

只有 M06 无法得到 strict inequality 时才进入 feature kernels、Fourier seams、finite symmetry skeletons 和 exact interval covering。

## 23. 当前研究边界

### 已机器化或已进入机器验证

```text
standard complex Hadamard carrier
Hadamard-unbiased transition
lifted exact-atlas reduction
independent-class quotient obstruction
cube cross-Gram factorization
orientation-logic separation
Zauner local quadratic fibre
Zauner two-point involution
correct fixed-edge canonical zero pattern
```

### 已直接推导，等待分层形式化

```text
mode-coordinate autocorrelation system
mode-local intrinsic characterization
canonical Fourier/Diţă identity
symmetry affinity formulas
commutator expression
MUB symmetry budget
no-degenerate Fourier-mode lemma
```

### 关键开放命题

```text
strict-X completion affinity lower bound alpha > 1
quartet-specific cubic orientation coherence
feature-kernel zero-locus on the complete order-six atlas
exceptional strict-X equality-locus exclusion
global branch aggregation
```

## 24. 主线冻结

下一阶段冻结为：

```text
fixed strict-X edge
  -> mode-coordinate completion equations
  -> symmetry-plane affinity alpha
  -> prove alpha > 1 on each generic branch
  -> use alpha(C)+alpha(D) <= 2
  -> isolate equality/ramification locus
  -> exact exceptional certificates
```

这条路线不要求先解决所有 MUB triplets，也不要求先证明 noncanonical fibre 为空。它把 quartet-specific obstruction 压缩为一个 centered-projector sharp bound，并保留 Hadamard atlas、feature kernels 和 finite symmetry skeleton 作为 branch-complete 后端。
