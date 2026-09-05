# MUB Six Fourth-Basis Research Theory

> **统一理论卷规则。** 六维四互无偏基 research lane 的新理论推理统一追加到本文件。Lean 节点继续拥有独立 GID、Scribe 与 Blueprint 投影，不再为每一个局部 obstruction 建立新的 theory 文档。
>
> **状态约定。** 本卷区分机器已证、直接推导、文献输入、条件归约和开放猜想。局部分支证书不得被表述为六维四 MUB 已经解决。历史段落中“已写入 Lean”只表示有源码；完整机器状态以绑定具体提交的 admission 为准。
>
> **2026-09-05 主线修正。** 第 30 节的列谱定理保留为条件代数结果。将 context affinity 等于一直接升级为逐行 collision 等于 `2/3`，需要额外逐行下界；该逐行下界已有数值反例线索，不得继续作为 strict-X 主桥。第 31 节用三阶酉算子的直接矩阵刚性替代这一依赖。第 33 节修复 dihedral partner 推导中未证明的逐模等范数假设。

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

多矩阵 compatibility 只允许一个共同 ambient left gauge。独立选择三个 Hadamard 等价类的 canonical representatives 会丢失相对左规范。仓库中的二维精确反例记录了 MUB compatibility 不下降到独立 Hadamard classes。

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

第二式推出第一式。第一式一般不推出第二式，因为零的一侧可以随 `pi` 改变。仓库已经写入 `Fin 2` 非负反例。

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

这些 local identities 已写入 Lean。它们将每个 generic mode 的 factor ambiguity 降到一个 involution。`x` 与 `y` 的符号相互关联，不能把二者独立相乘以推出 labelled fibre degree `4^3=64`。完整 completion fibre 的次数仍需独立消元和 gauge 记账。

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

它由 genuinely mode-mixing solutions 构成。上述 intrinsic characterization 与完整 basis adapter 仍需在指定规范下独立形式化。

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

如果只能得到 `alpha>=1`，则继续分类 equality locus，并证明两个 equality completions 不能兼容，也足以闭合。第 31 节完成了所需的条件矩阵刚性；第 32 节给出理论上的小幅稳健改进。实际 completion 下界本身仍然未证。

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

其中 `f_j = 0` 是 rank-one、basis、MUB 与 Hadamard branch equations，`g_k >= 0` 是 compact parameter-domain constraints，并且乘子 `t_k` 必须带有非负性证书。

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

所以该 2-circulant Hadamard seed 的三个 Fourier modes 都非零。该 lemma 可消除 local fibre quadratic 中的 denominator-degenerate cases。

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

只有 M06 无法得到 strict inequality 时才进入 feature kernels、Fourier seams、finite symmetry skeletons 和 exact interval covering。第 31 节的直接矩阵定理替代逐行 collision 驱动的主线。

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
strict-X completion affinity lower bound at context level
quartet-specific cubic orientation coherence
feature-kernel zero-locus on the complete order-six atlas
noncanonical strict-X completion exclusion
global branch aggregation
```

## 24. 主线冻结

历史主线为：

```text
fixed strict-X edge
  -> mode-coordinate completion equations
  -> symmetry-plane affinity alpha
  -> prove alpha > 1 on each generic branch
  -> use alpha(C)+alpha(D) <= 2
  -> isolate equality/ramification locus
  -> exact exceptional certificates
```

第 31 节后，只需 context-level `alpha>=1` 就可用 order-three rigidity 排除两个 completions。这里仍未证明这个 branch lower bound。

这条路线不要求先解决所有 MUB triplets，也不要求先证明 noncanonical fibre 为空。它把 quartet-specific obstruction 压缩为一个 centered-projector sharp bound，并保留 Hadamard atlas、feature kernels 和 finite symmetry skeleton 作为 branch-complete 后端。

## 25. support-face flatness defect 的锐化

本节区分两个缩放。令 normalized relative unitary 为 `U`，令未归一化 Hadamard multiplier 为 `K=sqrt(6)U`，令当前 Lean 使用的有理 scaled relative Gram 为：

```math
P=6U=\sqrt6K.
```

仓库中的第一 defect 是：

```math
D_{Lean}(P)
=\frac1{36}\sum_{a,b}
\left(|P_{ab}|^2-6\right)^2.
```

它与未平均的 Hadamard entrywise defect 相同：

```math
D_{Lean}(P)
=\sum_{a,b}\left(|K_{ab}|^2-1\right)^2.
```

概率坐标中的平均 defect 为：

```math
\widehat\Delta(U)
=\sum_{a,b}
\left(|U_{ab}|^2-\frac16\right)^2
=\frac1{36}D_{Lean}(P).
```

若一行只允许两个 active coordinates，row-Gram 给出这两个位置的 squared norm 总和为 `36`。设其值为 `a,b`，则：

```math
(a-6)^2+(b-6)^2+4(0-6)^2
=432+\frac12(a-b)^2.
```

所以每行 raw defect 至少为 `432`。六行求和并乘以 `1/36`：

```math
\boxed{D_{Lean}(P)\ge72.}
```

等价地：

```math
\boxed{\widehat\Delta(U)\ge2.}
```

这比只累计 24 个结构零所得的：

```math
D_{Lean}(P)\ge24,
\qquad
\widehat\Delta(U)\ge\frac23
```

更强。额外裕量来自剩余 12 个 active positions 必须承载全部 row mass。

锐等号要求每个 active pair 平分质量：

```math
|P_{a,b_0}|^2=|P_{a,b_1}|^2=18.
```

当前 PR 已新增：

```text
D5/S3/Quantum/Tomography/SupportFaceFlatnessDefect.lean
```

以及：

```text
row_normSq_sum_of_cardSq_rowGram
sixRowRawDefect_ge_four_hundred_thirty_two
twoModeSupport_scaledRelativeGramDefect_ge_seventy_two
twoModeSupport_completionThreeFramePotential_ge_seventy_two
```

`ZaunerAggregateFlatnessCertificate.lean` 已接入该通用真源，并加入 row-Gram 显式前提下的 `72` 裕量。该状态在 admission 完成前应记为“Lean source 已提交，等待机器裁决”。

## 26. robust leakage certificate

精确结构零适合 canonical branch。noncanonical branch 更需要稳定的近似版本。

对 normalized unitary `U`，固定每行的 two-mode active set `S_a`，定义 off-mode leakage：

```math
\eta_a=\sum_{b\notin S_a}|U_{ab}|^2.
```

一行总质量为 `1`。在给定 `eta_a` 时，row defect 的最小值在 active 两项均匀、off-mode 四项均匀时取得。直接投影到 probability simplex 得：

```math
\boxed{
\sum_b\left(|U_{ab}|^2-\frac16\right)^2
\ge
\frac{(2-3\eta_a)^2}{12}.
}
```

令总 leakage：

```math
L=\sum_a\eta_a.
```

对六行使用 Cauchy 得：

```math
\boxed{
\widehat\Delta(U)
\ge
\frac{(4-L)^2}{8}.
}
```

在 Lean scaled 坐标中：

```math
\boxed{
D_{Lean}(P)
\ge
\frac92(4-L)^2.
}
```

canonical support face 对应 `L=0`，恢复 `D_Lean>=72`。完全 flat transition 对应 `L=4`，下界降到零。

所以 branch exclusion 不必始终证明精确结构零。只要 exact interval、SOS 或代数证书给出：

```math
L\le4-\delta
```

其中 `delta>0`，就得到：

```math
\boxed{
D_{Lean}(P)\ge\frac92\delta^2>0.
}
```

这提供了从 canonical component 向 noncanonical component 延伸的稳健证书。

## 27. commutator 与 coarse mode transport

令三阶 symmetry 为：

```math
S=E_0+\omega E_1+\omega^2E_2,
```

其中每个 `E_i` 的 rank 为 `2`。因为任意两个不同 cube roots 的 squared distance 都为 `3`：

```math
\|[S,U]\|_{HS}^2
=3\sum_{i\ne j}\|E_iUE_j\|_{HS}^2
=3L.
```

因此 robust leakage bound 也可以写成：

```math
\boxed{
\widehat\Delta(U)
\ge
\frac18
\left(
4-\frac13\|[S,U]\|_{HS}^2
\right)^2.
}
```

canonical mode-local relative transition 与 `S` commute，commutator energy 为零，defect 至少为 `2`。flat transition 的 coarse mode mass 完全均匀，commutator energy 达到 `12`。

还可定义 `3 x 3` coarse mode transport：

```math
q_{ij}
=\frac12\sum_{r,s\in Fin 2}
|U_{(r,i),(s,j)}|^2.
```

unitarity 使 `q` doubly stochastic。对每个 `2 x 2` block 使用 Cauchy：

```math
\boxed{
\widehat\Delta(U)
\ge
\sum_{i,j}
\left(q_{ij}-\frac13\right)^2.
}
```

canonical mode-local transition 对应 `q=I_3`，右侧为 `2`。flat transition 对应 `q=J_3/3`，右侧为零。

`q` 也有 fusion-frame 解释。它记录两个由 rank-two mode PVM 诱导的 decomposition 之间的 overlap。quartet 所需的 flat relative transition 会迫使这两个 coarse decompositions mutually unbiased。

该 coarse inequality 与现有：

```text
threeModeCenteredSquare
modeCenteredSquareTotal
modeAffinityTotal
threeModeCharacterSquare
```

处于同一坐标系。下一层 Lean 应建立一个薄桥，而不重建 mode-affinity 库：

```text
relativeModeProbability
relativeModeTransport
scaledRelativeGramDefect_ge_modeCenteredEnergy
scaledRelativeGramDefect_ge_commutatorGap
```

## 28. 对 global atlas 路线的新影响

现在有两条互补的 scalar route。

第一条针对 individual completions：

```math
\alpha_S(C)+\alpha_S(D)\le2.
```

若每个 completion 都满足 `alpha>1`，则 quartet 被排除；第 31 节处理等号。

第二条针对 relative multiplier：

```math
\widehat\Delta(U)
\ge\|q-J_3/3\|_F^2.
```

quartet 要求右侧为零。只要 branch compatibility 强制 `q` 与 uniform coarse transport 保持正距离，该 branch 即被排除。

第二条更直接接入 single-relative-Gram 系统，因为未知量已经压缩为一个 `P`。它还揭示一个强制迁移：

```text
canonical factor pair: q = I, commutator energy = 0
quartet-compatible pair: q = J/3, commutator energy = 12
```

所以任何从 canonical fibre 走向 quartet 的代数 component 都必须发生宏观 mode mixing。它不能通过小扰动绕过 structural-zero certificate。

这建议把 generic strict-X 攻击拆为：

```text
1. 用 Jacobian 或 finite-fibre theorem 建立 canonical points 的局部完备性。
2. 用 robust leakage bound 给每个 canonical neighborhood 一个显式正裕量。
3. 把所有剩余候选推到 fibre ramification 或 separate component。
4. 在剩余 component 上优化 coarse transport distance，而非完整 36-entry potential。
5. 只有 coarse center 仍可达时，才启用 phase kernel 或高次数 Positivstellensatz。
```

新的 branch compiler 优先输出：

```text
support graph
coarse mode transport constraints
off-mode leakage interval
Jacobian nonvanishing certificate
residual phase equations
```

这将减少需要进入完整 real-algebraic elimination 的变量和次数。上述局部完备性和全覆盖当前仍未建立，不能从已有局部裕量直接推出。

## 29. 更新后的形式化顺序

历史队列：

```text
SupportFaceFlatnessDefect
  -> exact row-mass certificate
  -> six-row sharp margin 72

ZaunerAggregateFlatnessCertificate
  -> instantiate structural zeros
  -> require scaled row-Gram explicitly
  -> sharp three-frame margin 72

RelativeModeTransportDefect
  -> coarse 2 x 2 block averaging
  -> defect >= centered mode energy
  -> robust leakage and commutator forms

ZaunerThreeFramePotentialDecomposition
  -> exact phase remainder
  -> equality locus e_i in {+i,-i}
  -> paired-column binary constraints

FiniteAtlasPotentialCover
  -> branchwise support/coarse certificates
  -> positive finite minimum
  -> global no-zero theorem
```

`72` 证书只排除 canonical two-mode support face。六维四 MUB 全局结论仍依赖 noncanonical branch、exceptional loci 和 complete atlas cover。为避免增加同义包装，当前优先级转向第 31 节的矩阵主定理及第 33 节尚未闭合的 orthogonal-pair 证书。

## 30. 饱和列谱排除：保留为条件结果

### 输入假设的修正

此前从 context affinity 等于一直接写出逐行 collision 等于 `2/3`，省略了必要的逐行下界。现有 `row_collision_eq_two_thirds_of_affinity_eq_one` 明确要求：

```math
\forall i,\quad\sum_kp_{ik}^2\ge2/3.
```

没有这条假设，只有总平方和等于 `4`，不能让每行都等于 `2/3`。strict-X 共同无偏向量的数值探测已发现低于 `2/3` 的行，所以不再把此逐行假设作为一般 strict-X 证明目标。

下面的列谱排除本身仍是合法的条件代数命题。

假设 column sums 为 `2`，每个 row collision 等于 `2/3`，并且：

```math
(p_{ik}-p_{jk})(p_{ik}+p_{jk}-1)=0.
```

固定一列，写 `x_i=p_ik`，则：

```math
\sum_i x_i=2.
```

相对任一 reference value，饱和二次关系迫使其余五个值分别等于该 reference，或者等于其补数 `1-reference`。消去 reference 后，整列只能具有以下三种谱，直到排列：

```math
\left(\frac13,\frac13,\frac13,\frac13,\frac13,\frac13\right),
```

```math
\left(\frac34,\frac14,\frac14,\frac14,\frac14,\frac14\right),
```

或：

```math
(1,1,0,0,0,0).
```

相应 column collision 只可能是：

```math
\boxed{\frac23,\quad\frac78,\quad2.}
```

另一方面，六个 row collisions 的总和为：

```math
6\cdot\frac23=4.
```

它也等于三个 column collisions 的总和。三个元素从 `{2/3,7/8,2}` 中任取并带重复时，可能的总和只有：

```math
2,\ \frac{53}{24},\ \frac{29}{12},\ \frac{21}{8},\
\frac{10}{3},\ \frac{85}{24},\ \frac{15}{4},\
\frac{14}{3},\ \frac{39}{8},\ 6.
```

其中不含 `4`。因此这些假设共同定义的 equality locus 为空。

该结论已经集中写入一个公共 Lean 定理：

```text
D5/S3/Quantum/Tomography/MUBModeAffinityEqualityObstruction.lean
no_saturated_mode_probability_table
```

形式声明有意更强。最终矛盾只需要 column sums、row collision values 与 saturation quadratic，非负性和 row normalization 在这一阶段已经冗余。

### 定量间隙

允许总和集合与目标 `4` 的最小距离为：

```math
\boxed{\frac14.}
```

定义 column-spectrum polynomial：

```math
q(t)=\left(t-\frac23\right)\left(t-\frac78\right)(t-2).
```

对任意实数 `t`，令 `r` 为其到三个根的最小距离，则 `r^3 <= |q(t)|`。所以若三个 column collisions 满足 `s_0+s_1+s_2=4`，至少一列满足：

```math
\boxed{|q(s_k)|\ge\frac1{1728}.}
```

否则每个 `s_k` 都距离某个允许根小于 `1/12`，三个最近根的和距离 `4` 小于 `1/4`，与离散间隙矛盾。这是条件 equality obstruction 的稳定版本，不能用于补足已撤回的 rowwise lower bound。

### projector saturation quadratic 的历史桥

令 rank-two mode projector 为 `E_k`，并定义 `X_k=E_k-I/3`。则：

```math
X_k^2=\frac13X_k+\frac29I.
```

当 MUB symmetry budget 取等时，若几何 adapter 证明 `X_k=A_k+B_k`，其中两项属于两个相互正交的 centered context planes，在第一 completion 的 rank-one projector 上取期望得到：

```math
a_{ik}^2+\frac16\sum_jb_{jk}^2=\frac13a_{ik}+\frac29.
```

两行相减并代入 `a_ik=p_ik-1/3` 可得上述二次关系。这条桥保留为独立核验；主线由下面不使用逐行 collision 的定理代替。

## 31. 三阶酉算子在互补 context 中不能非平凡分裂

### 完整矩阵陈述

令 `d>0`，`C={P_i}` 和 `D={Q_j}` 是两个 complete orthogonal rank-one contexts，满足：

```math
\operatorname{Tr}(P_iQ_j)=1/d.
```

取复系数 `a_i,b_j`，满足 `sum a_i=sum b_j=0`，并令：

```math
A=\sum_i a_iP_i,\qquad B=\sum_jb_jQ_j,\qquad S=A+B.
```

如果：

```math
SS^\dagger=I,\qquad S^3=I,
```

则：

```math
\boxed{(\forall i,\ a_i=0)\quad\lor\quad(\forall j,\ b_j=0).}
```

因此 `S` 整体属于其中一个对角代数。结论适用于实际矩阵与实际 rank-one contexts，不把核心矩阵关系隐藏为一个未证明的 scalar hypothesis。

### 二次范数证书

写 normalized trace 为 `tau=Tr/d`，定义：

```math
\beta=\tau(BB^\dagger),\quad\alpha=1-\beta,\quad\mu=\tau(B^2).
```

MUB overlap 和两个 zero-sum coefficient 条件使 mixed diagonal expectations 消失。在 `P_i` 上对 `SS^dagger=I` 取期望：

```math
|a_i|^2+\beta=1.
```

所以所有 `a_i` 有相同平方模 `alpha`，且 `alpha,beta>=0`。

由三阶关系和 unitarity，`S^2=S^dagger`。再次投影到 `P_i`：

```math
\boxed{a_i^2+\mu=\overline{a_i}.}
```

对这个式子取模平方并平均，使用 `sum a_i=0`：

```math
\begin{aligned}
\alpha^2
&=\frac1d\sum_i|\overline{a_i}-\mu|^2\\
&=\alpha+|\mu|^2-\frac2d\Re\left(\mu\sum_i a_i\right)\\
&=\alpha+|\mu|^2.
\end{aligned}
```

结合 `alpha+beta=1`：

```math
\boxed{\alpha\beta+|\mu|^2=0.}
```

两项均非负，所以 `alpha beta=0`。`alpha=0` 强制全部 `a_i=0`；`beta=0` 强制全部 `b_j=0`。

该证明不需要谱分类、三次迹的 Cauchy 估计、逐行碰撞下界或枚举 completion roots。

### 精确有理 Positivstellensatz

写 `mu=u+iv`。令：

```math
f_1=\alpha+\beta-1,\qquad
f_2=\alpha^2-\alpha-u^2-v^2,\qquad
f_3=\alpha-1/2.
```

系数恒等式为：

```math
\alpha\beta+u^2+v^2=\alpha f_1-f_2.
```

balanced split 的直接反证证书为：

```math
\boxed{
-1=(2u)^2+(2v)^2+4f_2-4(\alpha-1/2)f_3.
}
```

该恒等式已用 Python 标准库 `fractions.Fraction` 对全部单项式系数逐项核对，无浮点输入。证书数据位于：

```text
docs/develop/certificates/order_three_no_split_certificate.json
```

这是 scalar polynomial identity 的精确审计。它不能取代上面的矩阵到 scalar 归约，也不能代替 Lean elaboration。

### 本轮唯一公共 Lean 主定理

```text
D5/S3/Quantum/Tomography/OrderThreeComplementaryContextRigidity.lean
orderThree_complementary_contexts_no_split
```

直接复用 `RankOneContextCommutator` 中的 `RankOneContext`、`overlap`、rank-one projection laws，以及 Mathlib 的 `Matrix.trace`、有限谱和、complex conjugation。内部计算 lemma 保持 private，没有新建 basis、pinching、unitary 或 affinity carrier。

Scribe 说明位于：

```text
Blueprint/D5/S3/Quantum/Tomography/OrderThreeComplementaryContextRigidity.scribe.cs
```

公共 theorem 的假设明确包括两个 context 的正交性、MUB overlap、两个 coefficient sums 为零、矩阵 unitarity 和三阶关系。结论是至少一整组 coefficient 为零。

### 对六维 symmetry budget 的意义

对 `S=E_0+omega E_1+omega^2 E_2` 和两个 MUB contexts，如果几何饱和 adapter 给出：

```math
S=\mathsf E_C(S)+\mathsf E_D(S),
```

则本定理推出：

```math
\boxed{(\alpha_S(C),\alpha_S(D))\in\{(2,0),(0,2)\}.}
```

特别排除 `(1,1)`。因此实际 branch certificate 若能证明每个 completion 的 context affinity 至少一，就足以排除 quartet。这里不再需要从总 affinity 推出逐行 collision。实际 strict-X 下界本身仍是开放目标。

## 32. 近饱和的定量刚性：理论推导

本节使用 normalized Hilbert-Schmidt norm：

```math
\|Z\|_2^2=\tau(Z^\dagger Z),\qquad\tau=\operatorname{Tr}/d.
```

设 `S` 是 trace-zero order-three unitary，`C,D` 为两个互补 contexts。令：

```math
A=\mathsf E_C(S),\quad B=\mathsf E_D(S),\quad R=S-A-B,
```

```math
a=\|A\|_2^2,\quad b=\|B\|_2^2,\quad r=\|R\|_2^2.
```

正交投影性质给出 `a+b+r=1`。pinching 在 operator norm 下收缩，所以 `||A||op,||B||op<=1`，进而 `||R||op<=3`。

从投影后的 `SS^dagger=I` 得到：

```math
H:=AA^\dagger-aI
=rI-\mathsf E_C(BR^\dagger+RB^\dagger+RR^\dagger).
```

因为 `R` 与两个 context 正交，mixed trace 为零。centered Hilbert-Schmidt contraction 给出：

```math
\|H\|_2\le2\sqrt r+\|RR^\dagger-rI\|_2\le5\sqrt r.
```

从 `S^2=S^dagger` 得到：

```math
A^2+\mu I+F=A^\dagger,\qquad
\mu=\tau(B^2),\qquad F=\mathsf E_C(BR+RB+R^2),
```

且 `||F||2<=5 sqrt(r)`。`A` normal，所以：

```math
\|A^2\|_2^2=a^2+\|H\|_2^2.
```

zero trace 还给出：

```math
\|A^\dagger-\mu I\|_2^2=a+|\mu|^2\le a+b^2\le1.
```

展开平方并用 Cauchy：

```math
\begin{aligned}
a(1-a)+|\mu|^2
&=\|H\|_2^2-\|F\|_2^2
 +2\Re\langle A^\dagger-\mu I,F\rangle\\
&\le25r+10\sqrt r.
\end{aligned}
```

因此得到可量化的非平衡约束：

```math
\boxed{a(1-a)\le25r+10\sqrt r.}
```

六维中 `alpha_S(C)=2a`、`alpha_S(D)=2b`。若两者均至少 `2499/2500`，令 `epsilon=1/2500`，则：

```math
r\le\epsilon,\qquad
a(1-a)\ge\frac{1-\epsilon^2}{4},
```

但：

```math
25\epsilon+10\sqrt\epsilon=\frac{21}{100}
<\frac{6249999}{25000000}
=\frac{1-\epsilon^2}{4}.
```

产生矛盾。故对于这类 `S,C,D`：

```math
\boxed{\min\{\alpha_S(C),\alpha_S(D)\}<\frac{2499}{2500}.}
```

这条定量结果目前是完整的数学推导；未加入本轮 Lean 公共 API。JSON 证书只审计最后的有理数比较，不声称已经核验全部 operator-norm 估计。若将来证明某一 strict-X completion branch 的 context affinity 至少 `2499/2500`，这一稳健版本就足够排除该 branch 中的 MUB pair。当前没有证明该 branch 下界。

## 33. dihedral partner 路线：补齐幅度缺口

### 反酉对称性与有限轨道

标准 2-circulant block mode 有形式：

```math
T_k=\begin{pmatrix}a_k&b_k\\\overline b_k&-\overline a_k\end{pmatrix},
\qquad |a_k|^2+|b_k|^2=1,\qquad\det T_k=-1.
```

定义 `J=[[0,-1],[1,0]]` 和 `Theta(z)_k=J conjugate(z_k)`。直接计算：

```math
\Theta^2=-I,\qquad\Theta T=-T\Theta.
```

对 `R(z)_k=omega^k z_k`，还有：

```math
R^3=I,\qquad\Theta R=R^{-1}\Theta.
```

在 projective rays 上得到六阶 dihedral action。在原坐标中，`R` 是三循环 permutation，`Theta` 是 conjugation 后接 monomial action，因此共同无偏集合在这些操作下保持。

二维反对称性给出：

```math
\langle R^a v,R^b\Theta v\rangle=0
\quad\text{for all }a,b\in\mathbb Z_3.
```

同一个三循环轨道内部正交，当且仅当三个 mode weights 都为 `1/3`。因此一个 uniform-mode common-unbiased vector 会生成六元正交 orbit basis。

### 前一版未证明的假设

从 `v_k perp w_k` 只能得到：

```math
w_k=\lambda_kJ\overline{v_k},\qquad\lambda_k\in\mathbb C.
```

它不能直接推出 `|lambda_k|=1`。本轮曾尝试使用由 mode mass、输入 channel imbalance、输出 channel imbalance 组成的实三阶行列式来控制幅度，但数值样本中该行列式退化。这条额外 generic guard 不再作为有效入口。

### 一个复三阶行列式足以同时处理相位和幅度

设每个 `v_k` 非零，`v,w` 都 normalized 且 coordinate-flat。写 `v_k=(u_k,z_k)`，定义：

```math
c_k=\overline{u_k}u_{k+1},\qquad
 d_k=\overline{z_k}z_{k+1},
```

下标模三。由 length-three constant-modulus Fourier 条件，`sum c_k=sum d_k=0`。

令：

```math
\Delta(v)=\det\begin{pmatrix}
c_0&c_1&c_2\\d_0&d_1&d_2\\1&1&1
\end{pmatrix}.
```

假设 `Delta(v) != 0`，则前两行独立，它们的共同 kernel 恰为 `span(1,1,1)`。

对逐模正交的 `w_k=lambda_k J conjugate(v_k)`，令：

```math
r_k=\lambda_k\overline{\lambda_{k+1}}.
```

`w` 的两条 autocorrelation equations 给出 `sum r_k c_k=sum r_k d_k=0`，故：

```math
r_0=r_1=r_2=\rho.
```

必须保留两个分支：

**第一分支：`rho=0`。** 三循环上任意相邻两个 `lambda` 的乘积为零，因此最多一个 `lambda` 非零。由于 `w` normalized，恰好一个非零，`w` 是 mode-local vector。

**第二分支：`rho!=0`。** 三个 `lambda` 都非零，三个相邻模长乘积相等，强制：

```math
|\lambda_0|=|\lambda_1|=|\lambda_2|.
```

利用 `||v||=||w||=1`，公共模长为一。于是：

```math
\rho^3=\prod_k|\lambda_k|^2=1,\qquad
\lambda_{k+1}=\overline\rho\lambda_k.
```

所以：

```math
\boxed{w\sim R^m\Theta v\quad\text{for some }m\in\mathbb Z_3.}
```

正确的 conditional partner theorem 因而是：

```math
\boxed{
\text{modewise orthogonality}+\text{coordinate flatness}+\Delta(v)\ne0
\Longrightarrow\text{mode-local partner or dihedral partner}.
}
```

这里没有预设逐模范数相同；它在非零乘积分支中由方程推出。该结果仍属于理论推导，尚未新增 Lean 文件。

### 真正缺失的排除证书

尚未证明的是：对于指定 generic strict-X branch，两个共同无偏向量的全局正交是否强制逐模正交。需要发现并精确验证：

```math
G(\alpha,v,w)^N\sum_{k=0}^2|\langle v_k,w_k\rangle|^2
\in I_{UB}(T;v,w),
```

或适当的 real-radical / Positivstellensatz 版本。`G` 的每个非零 guard 都必须与实际 branch 对应，并覆盖其补集。不能用“generic”一词跳过 `Delta=0`、零 mode 或 Fourier seams。

此 ideal-membership statement 目前仍是待寻找的证书；本轮没有得到它。也没有证明所有共同无偏向量已被枚举。

## 34. 本轮计算、写回和证明边界

### 可复核的精确结果

`order_three_no_split_certificate.json` 的两个多项式恒等式，已在本地使用有理系数字典进行展开并逐项比较。输出为：

```text
PASS: nonnegative identity, balanced refutation, robust rational constants
Lean elaboration: not executed in this runtime
```

这不是以数值残差替代恒等式。`fractions.Fraction` 没有浮点舍入。但它仅验证列出的 scalar algebra，Lean admission 仍负责完整矩阵 theorem。

本轮 Lean 主文件真实创建于提交：

```text
65ea169f452a94f2de77d5c4d66c12747939634f
```

Scribe 说明创建于：

```text
244ff1274f0e73f42582b2f3b582d10a77bfd56
```

本地运行环境没有可用的 Lean/lake 或完整 checkout，所以没有执行本地 elaboration、Scribe reconciliation 或完整 import closure。原 PR 仍有 canonical report 失败历史；本轮不把源码提交描述成 kernel 已接受。

### 新执行的一组数值探测

为检验第 33 节的 guards，本轮用固定 seed `502820260905` 生成一个 floating-point 2-circulant Hadamard candidate，进行了 `80` 个 least-squares starts，恢复 `41` 条 distinct candidate rays。应用 projective dihedral symmetry 并去重后得到 `60` 条 rays。

在 inner-product threshold `1e-7` 下，显式检验 bipartiteness 和全部边后，这个已恢复子图由：

```math
K_6\sqcup9K_{3,3}
```

组成。最大 coordinate/common-unbiased residual 约 `8.59e-12`；在检测到的正交对上，逐模内积平方和最大约 `1.98e-20`。

这些数值只描述一个样本的已恢复点集合。没有证明：

```text
该参数点严格避开所有 Fourier seams；
共同无偏方程恰好只有 60 条 rays；
阈值下的零内积为精确代数零；
整个连续 strict-X branch 有相同图；
所有 noncanonical completions 都被排除。
```

因此 `K6 + 9 K3,3` 继续作为有针对性的证书发现线索，不作为文献事实或全分支定理。完整输入、seed、求解和图检验代码保留在本轮可下载的研究包中。

### 下一次写入的准入标准

不再新增零元下界的同义版本、逐行 collision 的初等推论或无消费者的证书包装。优先闭合本轮矩阵主定理的 admission；之后只有两类实际进展值得进入主线：

```text
1. 用现有 pinching/Pythagoras 接口接通真实饱和几何，
   并对指定 strict-X branch 构造 context-level affinity 下界证书。
2. 找到并验证全局正交到逐模正交的具体 polynomial certificate，
   同时处理非零 guards 和 exceptional locus。
```

三阶刚性已经给出等号障碍，但仍未提供 strict-X completion 下界或 noncanonical orthogonality 分类。六维四 MUB 的全局不存在性仍然开放于本研究线。

## 35. 2026-09-05 勘误：正则 strict-X 点上的全局到逐模桥反例

本节取代第 33 节中以已列 guards 为前提的全 strict-X 逐对证书目标。旧理论和源码保留为历史；不得继续把这个已被反例否定的蕴含用于排除证明。

取精确数域 `Q(i,sqrt(21))` 中的参数：

```math
b=(-3+4i)/5,\qquad e=(-2+i\sqrt{21})/5.
```

令 `A=circ(1,b,1)`、`B=circ(1,e,1)`，并令 `H=[A B; B* -A*]`。精确域运算核验所有 entry 平方模为一，且 `HH*=H*H=6I`。去相位后的每行 `-1` 个数是 `(0,0,0,1,1,2)`，每列是 `(0,0,0,2,1,1)`。Matszangosz–Szöllősi 2024, DOI `10.1007/s10623-024-01503-w`, Corollary 23 给出 normalized Fourier/transposed-Fourier 的行列判据，因此这是真实的 strict-X 点；该分类定理是明确的文献输入，不由 Python checker 冒领。

实 signed permutation `M` 由：

```math
M\bar u=(\bar u_5,\bar u_3,\bar u_4,-\bar u_1,-\bar u_2,-\bar u_0)^T
```

给定，满足 `M^T=-M`、`MM^T=I`，且 `H* M=N H^T`，其中 `N=[0 -I; I 0]`。因此 `v=u/sqrt(6)` 与 `w=M conjugate(u)/sqrt(6)` 只要一方共同无偏，另一方也共同无偏，而且 `v*w=0` 是精确反对称恒等式。

本轮重放了五实变量 signed Cayley chart 的有理区间证书。`u_0=1`，其余 `u_j=i^q_j(1+i t_j)/(1-i t_j)`，quarter-turn tuple 为 `(0,3,2,0,0,1)`。五个方程是 `|H* u|^2-6` 的前五个分量；第六个由 Gram 恒等式推出。半径 `10^-8` 的 box 具有严格 Krawczyk 包含，预条件 Jacobian 的 infinity contraction 小于 `1/1000`，位移小于 box 半径的 `1/1000`。由 Banach 不动点定理，box 内有唯一真实根。

在整个 box 上，有理区间运算认证：

```math
|\langle v,Sw\rangle|^2+|\langle v,S^2w\rangle|^2>7/10,
```

两个 phase determinants 的平方模均大于 `1/200`，所有六个 mode weights 均大于 `1/5`。构造参数 `alpha=-1/5` 的两个 discriminants 是 `-16384/625` 与 `-16464/625`，均非零。因此第 33 节列出的非零 guards 全部成立，但逐模正交结论失败。

行置换 `L` 取 indices `(2,0,1,4,5,3)` 后，矩阵变为：

```math
H_0=LH=\begin{pmatrix}
J_3+(b-1)I_3&J_3+(e-1)I_3\\
J_3+(\bar e-1)I_3&-J_3-(\bar b-1)I_3
\end{pmatrix}.
```

它与全部同步 `S3` permutations 交换，并有额外反酉 `Theta0(zL,zR)=(-conjugate(zR),conjugate(zL))`。这类操作可以交换非平凡 Fourier modes，解释了全局正交中保留非零逐模项的相消机制。

上一轮已认证一个十二射线对称轨道的完整诱导图：十二个顶点、二十四条边、每点度数四、二分、clique number 二。所有边由 signed-permutation skewness 证明；所有非边有严格有理区间正下界。它只排除该轨道内部的正交三角形，不排除其与盒外未知射线拼成六元基。

对应源码和证书已在提交 `60c09dd8f75e53f7f2ab605e0305cf0187e45249` 同步到 PR #5028。该提交以 `14a3f29e965650438500fecac9fbac35d899ebd5` 为 parent，保留其他 agents 的全部 seed/seam 提交，未强推。

```text
D5/S3/Quantum/Tomography/TwoCirculantExtraAntiunitary.lean
Blueprint/D5/S3/Quantum/Tomography/TwoCirculantExtraAntiunitary.scribe.cs
scripts/research/check_strict_x_counterexample.py
docs/develop/certificates/strict_x_counterexample_certificate.json
docs/develop/certificates/strict_x_counterexample_verification.json
```

Lean 主定理 `conjugate_block_common_unbiased_orthogonal_partner` 只证明实际 conjugate-block 矩阵的反酉保持与精确正交。它不声称验证 Banach/Krawczyk analytic adapter。新的运行环境仍无 Lean/lake，故源码提交不等于 kernel admission。

## 36. 实参数反例点的六十射线完整诱导图与下一项覆盖义务

### 八个根盒生成六十条真实射线

继续沿第 35 节的同一精确 `H0`，本轮选择八个有理 uniqueness boxes，分别验证五维 Cayley root equations 的严格压缩与内部包含。每个 box 的半径为 `2^-26`，中心及预条件矩阵为 dyadic rationals。验证阶段只使用 `fractions.Fraction`，必要的 dyadic rounding 始终向外。

八个精确根通过同步 `S3` permutations 与 `Theta0` 生成大小为：

```text
6, 6, 12, 12, 4, 12, 2, 6
```

的八个轨道，共六十条射线。逐对 inner-product 区间上界严格小于一，认证了所有射线彼此不同。

### 全部 1770 对关系的分类

本轮检查全部 `choose(60,2)=1770` 个无序对。共 `114` 条正交边，其中 `104` 条由精确 skew-symmetry identities 得到，另外 `10` 条由不同三循环特征值的正交性得到。其余 `1656` 对均有：

```math
|\langle v,w\rangle|^2>10^{-8}.
```

非边不能通过数值阈值伪装成零；边也不由小数值残差决定。三循环固定射线通过“对称像落回同一个唯一性 box”证明，随后用精确 unitary eigenspace orthogonality 认证跨特征值的边。

完整诱导图的 connected-component signature 为：

```text
3 components: 6 vertices, 9 edges, bipartite (K3,3)
3 components: 12 vertices, 24 edges, bipartite
1 component: 6 vertices, 15 edges (K6)
```

因此这个六十射线集合中唯一的六元 orthogonal clique 是最后的 `K6`。其六个向量均为三循环特征向量，所以相对同一 rank-two mode decomposition：

```math
\boxed{\alpha_S(C_{known})=2.}
```

这里的等式是精确的特征向量结论，不由 floating-point affinity 接近二推出。其余五十四个已认证顶点形成二分子图，不能从其中选出三个两两正交向量。

### 精确范围

已完成的是全部已认证射线之间的边审计，包括不同轨道之间的所有 nonedges。未完成的是共同无偏方程的全局根覆盖。八个 boxes 证明至少有这些根，不能证明盒外没有其他根。因此不得将以下条件句省略前提：

```text
IF the 60-ray collection is exhaustive,
THEN the fixed edge has a unique completion and cannot extend to a quartet.
```

同样，已认证集合上的唯一 completion affinity 等于二，不是对所有实际 completions 的无条件下界。

checker 复用第 35 节的有理区间内核和种子域运算，不新建第二套 interval arithmetic。拟定真源文件：

```text
scripts/research/check_real_x_complete_induced_graph.py
docs/develop/certificates/real_x_orbit_cover_certificate.json
docs/develop/certificates/real_x_induced_graph_verification.json
```

上述计算证书不属于 Lean kernel 证明。源码、数据和重放日志的实际提交以及 admission 状态必须单独记录。

### 进一步的主线缩减：只需覆盖能进入正交三元组的根

令 `U(T)` 是全部共同无偏射线。定义：

```math
U_\triangle(T)=\{v\in U(T):\exists w,z\in U(T),\ (v,w,z)\text{ pairwise orthogonal}\}.
```

完整 completion 中的每个向量都属于 `U_triangle(T)`。因此，除了全局覆盖 `U(T)` 之外，还有一个更窄的可接受覆盖目标：

```math
\boxed{U_\triangle(T)\subseteq C_{known}.}
```

该命题成立就足以证明 completion 唯一，不需要枚举不能进入任何正交三角形的孤立 roots 或二分 components。当前的六十射线诱导图为这个目标提供了严格的正控制，但尚未证明盒外的 triangle-bearing roots 被覆盖。

在 projector coordinates 中，三元组证书只需三个 Hermitian rank-one projectors `P0,P1,P2`，两两乘积为零、分别对两个固定基无偏。一个更弱的待证 inequality 是：

```math
\sum_{r=0}^2\sum_{k=0}^2\operatorname{Tr}(E_kP_r)^2\ge2.
```

若它对所有实际共同无偏正交三元组成立，则将任意六元 completion 分成两组三元组，得到总 collision 至少四，亦即 `alpha_S(C)>=1`。随后第 31 节排除两个 MUB completions 的预算等号。此三元组 inequality 当前仅是明确的下一项证书目标，不是本轮已经证明的下界。

主线继续避免逐行下界和已被反例否定的全局到逐模蕴含。真正下一步是：精确全局 root cover、triangle-bearing locus 的排除证书，或实际三元组/完整基的 projector-affinity certificate。
