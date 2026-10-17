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

先固定 2-circulant Hadamard 的实际块方程，而不使用未声明的 ratio equation。令

```math
H=\begin{pmatrix}A&B\\ B^*&-A^*\end{pmatrix},
```

其中 `A,B` 是 `3 x 3` circulant，且 `H H^*=6I`。设 `A`、`B` 的第一行分别为 unit phases `(a,b,c)`、`(d,e,f)`，取固定 primitive cube root `\omega`，并定义未归一化的 three-Fourier coefficients

```math
\lambda_r=a+\omega^r b+\omega^{2r}c,
\qquad
\mu_r=d+\omega^r e+\omega^{2r}f,
\qquad r\in\mathbb Z_3.
```

由 `HH^*=6I` 的左上块和 circulant 的 Fourier 对角化，得到逐模预算

```math
\boxed{|\lambda_r|^2+|\mu_r|^2=6.}
```

**Unit-triple 子引理。** 若 `z_0,z_1,z_2` 都是 unit 且 `z_0+z_1+z_2=0`，则三者构成 equilateral triple：存在 primitive cube root `q` 使

```math
z_j=z_0q^j.
```

因此，如果某个 `\lambda_r=0`，令
`(z_0,z_1,z_2)=(a,\omega^r b,\omega^{2r}c)`，便有

```math
(a,b,c)=u(1,t,t^2),
\qquad |u|=1,
\qquad t^3=1.
```

这里 `t=1` 的 constant-row edge case 必须保留；不能声称公共 ratio 一定是非平凡 cube root。该 geometric character 的 Fourier transform 只在一个 mode 非零，且该 mode 的系数为 `3u`。于是存在 `s` 使 `|\lambda_s|^2=9`，与逐模预算 `|\lambda_s|^2+|\mu_s|^2=6` 矛盾。故

```math
\boxed{\lambda_r\ne0\quad\text{for every }r.}
```

交换 `A,B` 同理得到 `\mu_r\ne0`。特别地，constant row `a=b=c` 虽然会使两个非平凡 Fourier coefficients 消失，却被其 zero-mode modulus `3` 与预算一并排除。

该结论只消除 local fibre quadratic 的 denominator-degenerate Fourier charts；它本身不推出 `\alpha_{\min}(T)>1`，也不完成 `\alpha=1` equality classification。后续 SoS/branch 证书仍须单独验证完整 compact branch。

形式化建议分层：

```text
unit_sum_zero_is_cube_character
cube_character_fourier_support_singleton
circulant_hadamard_mode_budget
no_zero_three_fourier_mode
```

先证明前两个通用复数/`Fin 3` 小引理，再由 `AA^*+BB^*=6I` 的 Fourier adapter 提供逐模预算；不引入未在块方程中声明的 off-diagonal ratio equation。


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

## 37. 2026-09-07：实际残差导数与完整覆盖推导记录

本节推进局部排除的认证链，不扩大已排除的 Hadamard 参数区域。此前的 `real_x_balanced_sublevel` 证书覆盖同一精确种子的全部六残差子水平集 `|r_a|<=1/64`，外管半径为 `1/16`。其 4,900,318 个节点统计只是执行诊断，不能单独充当 Lean 的穷尽证明。

### 37.1 从实际 signed-Cayley 表达式推导方向导数

写 `x_i(q)=m_i+q v_i`，并沿用既有紧坐标图的实虚部：

```math
u_i(q)=s_i\frac{1-x_i(q)^2+2i x_i(q)}{1+x_i(q)^2}.
```

分母在整个实轴严格为正。实际导数为：

```math
\dot u_i(q)=
\frac{-4s_i x_i(q)v_i+2i s_i(1-x_i(q)^2)v_i}
     {(1+x_i(q)^2)^2}.
```

对实际矩阵 `H` 令 `y=H^dagger u`、`dot y=H^dagger dot u`，则：

```math
\frac{d}{dq}(|y_a(q)|^2-6)
=2\left(\Re y_a\Re\dot y_a+\Im y_a\Im\dot y_a\right).
```

新真源 `CayleyHadamardDifferential.lean` 的公共定理 `signed_cayley_hadamard_residual_hasDerivAt` 从 Mathlib 的商、乘积、有限和求导规则证明这个实际标量路径导数。没有提供 Jacobian 正确性的假设。取 `s_0=1,m_0=v_0=0` 得到验证器的五变量去相位情形。这里证明的是所有指定方向上的路径导数，尚未单独构造一个完整 Frechet-Jacobian 数据接口。

第二个公共定理 `signed_cayley_balanced_sublevel_row_enclosure` 把实际导数接入原有六残差守恒对偶和 scalar mean-value inequality。令 `f_a(q)=|y_a(q)|^2-6`、`g(q)=m_k+qv_k-sum_a c_a f_a(q)`。若在整个闭区间上 `|g'(q)|<=R`，且端点残差在 `lo,hi` 中，则：

```math
m_k-c\cdot f(0)-R+L\le m_k+v_k
\le m_k-c\cdot f(0)+R+U,
```

其中 `L,U` 正是 `hadamard_residual_box_dual` 的平移系数端点界。`HH^dagger=6I` 和 `s_i^2=1` 是实际矩阵与相位条件。数值区间对上述实际导数的包含性仍须证明，不能由有限测试代替。

### 37.2 有限的是证明节点，连续候选空间保持不变

检索并读取 `FiniteExhaustion` 与 `FiniteBranchAtlas` 后，确认其有限性前提作用在 Candidate。不能把共同无偏向量空间换成观测到的六十个标签来调用它们。

新的 `D5/S0/Certificates/FiniteSublevelCover.lean` 只把证明节点编号限制为 `Fin n`。实际候选类型 `X` 可以是连续相位空间。`LocalStep` 的每个构造都要求对应的 Lean 证明：目标集合包含、残差区间排除、守恒区间排除、完整二分，或保留全部小残差点的收缩。子节点编号必须严格小于父节点，避免循环论证。

主定理 `sublevel_mem_target_of_local_steps` 通过自然数强归纳推出：

```math
x\in B_{root},\quad\forall a\ |f_a(x)|\le\varepsilon
\quad\Longrightarrow\quad x\in T.
```

它不假设全局覆盖，不要求根唯一或存在，也不要求 `X` 有限。分裂必须覆盖整个父集合，包括公共边界。收缩必须保留整个闭子水平集，不能只保留精确零点。

这是局部证明的逻辑组合定理，不是区间求值器、文件解析器，也不是具体轨迹已经满足 `LocalStep` 的证明。具体实例仍需要构造每个节点的证明项。

### 37.3 全部 32 图的推导轨迹已经导出并逐条重放

新增 `scripts/research/check_real_x_cover_trace.cpp`，直接包含现有 balanced-sublevel owner，复用其种子、40 位向外取整区间、残差求值、Cayley 图转换与守恒对偶。导出时每个新计算的收缩像都与未修改的 `balanced_krawczyk` 逐端点比较。

推导文件记录六种操作：直接入管 `G`、残差排除 `R`、收缩后空交 `E`、收缩后入管 `K`、继续收缩 `C`、闭二分 `S`。预条件矩阵以 25 个精确 dyadic 整数记录，作为不可信建议。重放不调用搜索或浮点逆矩阵建议，重新计算每一步的区间界，且要求所有分支终结后才接受 `END`。

本轮实际执行全部 32 图的导出与重放，共 4,900,318 个节点，零待处理、零未决；原始轨迹共 323,067,709 字节。完整轨迹已生成并随本轮交付包提供，仓库保留生成器、检查器、逐图摘要与哈希，可重新生成。哈希只用于字节识别。

八类损坏轨迹均被拒绝：缺结束标记、截断分支、额外指令、错误残差阈值、边界处非法二分、错误入管、错误空交、错误残差排除。另一个 `Fraction` dual-number 实现检查了 640 个残差值和 3,200 个 Jacobian 条目的点包含，以及 300 个商求导恒等式实例。这些是有限开发诊断；C++ 重放仍共享原区间算术与求值器，不是独立作者审稿或内核证明。

本轮轨迹只覆盖外管。标签 5 的 945 节点残差保持细化尚未导出成同一轨迹格式，有限图实例仍需该细化。没有把旧报告重新命名成新的认证结果。

### 37.4 内核闭合边界

本轮 Lean 证明源码已配套 Scribe，但执行环境没有 Lean/lake。直接下载失败，已尝试的官方 Linux 构建 artifact 又超过连接器大小上限，所以未执行 elaboration、kernel checking 或传递公理审计。源码中的 `#print axioms` 不是已经运行的审计记录。

当前还需要同时闭合：

1. 有理区间四则运算、向外取整及实际残差与导数的普遍包含性。
2. 轨迹解码、坐标互换与每条具体指令到 `LocalStep` 证明的转换。
3. 与 C++ 实际使用的 `Fin 6` 种子逐项一致的 Gram/常数证明，以及标签 5 细化记录。
4. 通过既有 `FlatProjectorDephasing`、紧 Cayley 覆盖和 `RealXFinitePartnerCertificate`，将实际投影与全部局部证据组合成最终实例。

所以本轮没有得到“整个 PR 已经内核接受”，也没有扩大局部排除区域。它补出了实际导数的证明源码，并把此前只留下统计数的搜索变成完整可逐节点审计的证明数据。有限局部规则的归纳，不应被宣传为具体 490 万条数值指令已经通过 Lean。

### 37.5 接下来只接受真实实例的消元

下一项应以一条真实 `R` 或 `E` 叶为最小内核实例，完整证明其精确常数、区间计算与排除结论，然后按同一经证明的解释器覆盖全部记录。只增加一个接受“每叶正确”假设的封装不会消除剩余义务。

经典商求导、均值不等式和有限强归纳不主张数学首创。研究价值来自它们在具体 MUB 局部排除证书中的完整、可复核实例化。整个 strict-X 家族及六维四 MUB 全局问题仍未闭合。

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

## 38. 2026-09-07：补入完整候选的幅度输运

本节补入此前已完成但未写回的数学内容。真源仍归 `HadamardResidualBarrier.lean` 所有；原有精确根和列扰动定理保持不变。新公开定理为 `near_unit_entry_families_admit_controlled_phase_replacement`，其配套说明追加在原 Scribe 中。实际交付提交为 `570c05455f7c55bc2350af113de407672f0cfb28`。

设任意索引族 `z_a in C^6` 满足：

```math
0\le\rho\le1/4,\qquad
\big||z_{a,i}|^2-1\big|\le\rho,\qquad
\big||(H^\dagger z_a)_j|^2-6\big|\le\rho.
```

若 `|H_ij|<=M` 且 `M>=0`，存在同一个单位元素族 `u_a` 满足：

```math
|u_{a,i}|=1,\qquad |z_{a,i}-u_{a,i}|\le\rho,
```

```math
\big||(H^\dagger u_a)_j|^2-6\big|
\le\rho+6M\rho(5+6M\rho).
```

令 `p(x,y)=(1/6) sum_i conjugate(x_i)y_i`，同一替换还满足：

```math
|p(u_a,u_b)-p(z_a,z_b)|\le3\rho,\qquad
\big||p(u_a,u_b)|^2-|p(z_a,z_b)|^2\big|\le15\rho.
```

原向量不必单位化，所以原始 `p(z_a,z_b)` 只是固定目标缩放下的代数量，不能预先解释成归一化量子态的 Born 概率。所有结论使用同一个构造族，不允许为不同约束分别选择相位替代。

### 39.1 证明与既有真源的连接

对非零坐标取 `u=z/|z|`，对零坐标取 `u=1`。由平方差恒等式：

```math
|z-u|=\big||z|-1\big|\le\big||z|^2-1\big|.
```

测量幅度改变不超过 `6M rho`，所以已有 private `squared_modulus_residual_transfer` 给出测量界。小坐标误差保证 `|z_ai|<=2`。再使用完整乘积差：

```math
\overline{u_{a,i}}u_{b,i}-\overline{z_{a,i}}z_{b,i}
=\overline{u_{a,i}-z_{a,i}}z_{b,i}
 +\overline{u_{a,i}}(u_{b,i}-z_{b,i}),
```

得到逐项 `3rho`，从而得到 `p` 的误差。最后 `|p(u_a,u_b)|<=1`、`|p(z_a,z_b)|<=4` 给出 squared-overlap 界 `15rho`。这些常数没有被宣称为最优；经典相位归一化本身也不是新的数学发现。

### 38.2 全幅度误差间隙的条件消费者

既有圆弧/单点扩展排除使用：

```math
\tau=1/256,\quad\epsilon=1/128,\quad\sigma=3/4096.
```

在 `max_ij |H_ij-(H0)_ij|<=1/8192` 的矩阵球中，`|H_ij|<=8193/8192`，列 l1 距离至多 `sigma`。取 `rho=1/8192`，有精确预算：

```math
\rho+6M\rho(5+6M\rho)
=\frac{4261715001353}{1125899906842624}<\frac1{256},
\qquad4\rho<\tau,\quad16\rho<\tau.
```

对任意复矩阵 U,V，定义：

```math
A(W)=\sum_{ij}(|W_{ij}|^2-1)^2,
```

```math
D_H(W)=\sum_{aj}(|(H^\dagger W)_{aj}|^2-6)^2,\qquad
O(W)=\frac1{36}\sum_{i<j}|(W^\dagger W)_{ij}|^2,
```

```math
B(U,V)=\sum_{ij}\left(\frac{|(U^\dagger V)_{ij}|^2}{36}-\frac16\right)^2.
```

若既有完整残差覆盖、圆弧包含与强不可扩展实例成立，则：

```math
A(U)+A(V)+D_H(U)+D_H(V)+O(U)+O(V)+B(U,V)\ge2^{-26}.
```

反设总误差小于 `rho^2`，逐项非负性给出各幅度误差、测量误差和 cross squared-overlap 偏差小于 rho，内部缩放内积模长也小于 rho。对十二个向量同时作相位替换，就进入原等模证书的预算，矛盾。

本节扩大候选 U,V 的量词域，没有扩大 H 的已排除半径。这个全幅度下界也不被描述为对原等模 `2^-16` 常数的数值改进。最终数值实例依赖外部完整覆盖，尚未在 Lean 内核实例化。

本次重新执行了 1200 个精确 Gaussian-rational 相位/成对误差实例、280 个近平方模六的测量扰动实例和具体有理预算核对。有限检查不替代普遍 Lean 证明。旧轮次中的较小范围试验、未完成的大阈值覆盖均不在本次作为新成果重复主张。

## 39. 2026-09-07：将强不可扩展性的有限前提化为六十份具体证书

### 38.1 精确定位尚缺的一环

已有 `RootTubeStrongUnextendibility.six_frame_has_cross_error_to_any_covered_point` 接受两个实际 overlap 的保守关系 O 和 B，以及一个全称的 `hNoPartner` 前提：任何 O 中的六元 clique 都没有与全体顶点保持 B 关系的共同伴随标签。

此前的计算程序通过枚举 2403 个第一组六元 clique 检查这个前提。本节交换两个全称量词。对每个可能的额外向量标签 l，令：

```math
V_l=\{i:B(i,l)\}.
```

只需为 `O[V_l]` 提供五着色。假如六元 clique 的全部标签都属于 `V_l`，着色就给出 `Fin 6` 到 `Fin 5` 的单射。由此得到 hNoPartner。

这个量词重排和着色原理是标准组合论。实质性新增量是为当前经过几何计算得到的全部六十个邻域提供具体整数证书，并把有限计算从公共定理的假设中移除。

### 38.2 数据与几何来源

固定种子、六十个 signed-Cayley 中心和标号与第 35、36 节一致。中心取自已经提交的 `docs/develop/certificates/real_x_two_relation/centers.txt`。普通管半径为 `1/16`，标签 5 使用原强不可扩展程序已处理的 `1/32` 细管。阈值为：

```math
\tau=1/256,\quad\eta=\tau^2,\quad\mu=3/4.
```

本次使用另一份同作者实现，重新计算全部 1830 对圆弧整管包含和 60 对标签 5 的不等半径包含。所有圆弧端点、支持函数对偶检验、平方根上界和取整均采用有理数。它不是独立作者审稿，也不替代圆弧包含的分析证明。

重算所得关系为：

```text
O: 372 undirected edges
B before refinement: 875 undirected edges
B after refinement: 859 undirected edges
removed B-neighbors of label 5:
14,15,19,23,24,27,31,32,42,45,46,48,49,52,56,59
```

O 仍保留未细化的大管上界，故允许比实际更多的边。B 的十六条删除必须由已有残差保持的标签 5 局部覆盖以及不等半径的真实包含支持。本次没有重跑该局部覆盖或数百万盒的完整全域遍历，不把旧报告的成功标记变成新执行。

### 38.3 一个具体 Lean 消费者

新增：

```text
D5/S3/Quantum/Tomography/RealXFinitePartnerCertificate.lean
Blueprint/D5/S3/Quantum/Tomography/RealXFinitePartnerCertificate.scribe.cs
```

O、B 各由六十个自然数 bit masks 定义。六十行颜色用 base-five 自然数无损存储；颜色解码是 `(code / 5^i) % 5`。没有采样状态、未列出顶点或外部搜索结果进入证明假设。

两个公开关系是 `realXOrthogonalityCandidate` 和 `realXUnbiasednessCandidate`。唯一公共结论是：

```text
realX_six_frame_has_cross_error_to_any_covered_point
```

内部 `partner_colors_separate` 使用 `decide +kernel` 对字面数据证明：

```math
\forall l,i,j,\quad
B(i,l)\land B(j,l)\land O(i,j)
\Longrightarrow\operatorname{color}_l(i)\ne\operatorname{color}_l(j).
```

该结果供应原 owner 所需的 hNoPartner。新的公共 theorem 不再要求用户提交颜色正确性、clique 枚举完整性或有限无伴随命题。

实际残差管覆盖、同管 overlap 下界、两个有限关系对真实 trace overlap 的一侧包含仍然显式保留。对于满足这些前提的实际六元组 C 和实际被覆盖矩阵 Q，结论是：

```math
\exists i,\quad
\left|\Re\operatorname{Tr}(C_iQ)-\frac16\right|\ge\frac1{256}.
```

实际用途是 normalized rank-one outer products。这是具体有限证书的实例化，没有重新定义矩阵、Hadamard、语境、interval 或 frame potential。

### 38.4 六十张二次 Boolean Positivstellensatz 证书

固定 l，把五个独立颜色类记为 `I_0,...,I_4`，为每个 `i in V_l` 引入 Boolean 选择变量 x_i。一个六元 clique 必须满足：

```math
x_i^2-x_i=0,\qquad
x_ix_j=0\quad(i\ne j\text{ 且 }\neg O(i,j)),\qquad
\sum_{i\in V_l}x_i-6=0.
```

令 `S_t=sum_(i in I_t) x_i`。有精确多项式恒等式：

```math
\boxed{
-1=\sum_{t=0}^{4}(1-S_t)^2
-\sum_{i\in V_l}(x_i^2-x_i)
-2\sum_{t=0}^{4}\sum_{i<j,\ i,j\in I_t}x_ix_j
+\left(\sum_{i\in V_l}x_i-6\right).
}
```

同颜色顶点不相邻，故每个二次项都有真实 nonedge 方程支持。该证书的最大次数为二，所有系数都是整数。它针对已通过连续几何包围的 Boolean 选择问题，不能据此声称普通 vector-coordinate degree-two SoS 已解决六维 MUB。

本次对六十份恒等式逐单项式核验，残差恒为常数 -1。合计涉及 1718 个邻域顶点出现和 4920 个 nonedge 乘子。这个计数只是具体证书的规模，没有被当作数学新颖性或准入分数。

### 38.5 有限审计与下一步不能继续压缩的部分

从实际 Lean 字面量重新读入并验证的结果：

```text
216000 ordered label/color cases checked
60 quadratic polynomial refutations checked coefficientwise
2403 first six-cliques in an independent diagnostic enumeration
0 first six-cliques with a common partner
```

活动边的颜色碰撞、截断行表、擅自添加邻域边三类损坏都被拒绝。打包为十进制自然数时曾有一个未挂到分支的 blob 出现数字转录错误，Git blob 与本地已核验字节的对照检出了它；修正后的 blob 才进入实际研究提交。

进一步用独立 maximal-clique 路径搜索，并逐边复核输出见证，发现：

```text
41 neighborhoods contain an explicit K5
18 have maximum clique size 4 in the diagnostic search
1 has maximum clique size 3 in the diagnostic search
```

每个邻域都有五着色，故其中 41 个的 chromatic number 确为五。这个有限上界图不能仅通过把五色证书改写成四色证书而得到更强排除。其余诊断中的最大值不作为 Lean theorem 导入。K5 是保守图中的候选，不代表五个真实向量可被同时实现。

这标定了后续有意义的方向：针对这些 K5 候选检查共享变量的联合测量/正交/无偏方程，或用更紧的实际管几何删去其中至少一条边；不要继续只优化同一张图的颜色记账。

### 38.6 文献和跨作者复用

Matolcsi、Matszangosz、Varga、Weiner，*Triplets of mutually unbiased bases*，Journal of Algebraic Combinatorics 63, 26 (2026)，DOI `10.1007/s10801-026-01506-x`，Conjecture 3 仍以整个 Szollosi X 家族为目标。本节既没有扩大已认证矩阵球，也没有完成全家族覆盖。

Gocht、McBride、McCreesh、Nordstrom、Prosser、Trimble，*Certifying Solvers for Clique and Maximum Common (Connected) Subgraph Problems*，CP 2020, pp.338-357，DOI `10.1007/978-3-030-58475-7_20`，说明 clique 求解可以输出由 pseudo-Boolean/cutting-planes 检查的证书。本节采用已有的“发现与验证分离”思想，并针对实际六十标签图给出可读的五色和二次恒等式。没有把着色证明或 proof logging 声称为新算法。2026 论文的猜想陈述及这篇方法文献的作者版摘要在本轮重新核对。

跨作者审查包含 loning 研究线 #5892 的实际 `CoefficientDrivenJacobiCharacteristicPolynomial` 公共 theorem：其 hSymmetric 显式保留，未被伪装成由其他假设推得。这里相应地保留真实区间到矩阵包含和全覆盖前提，只消去确实已经实例化的有限 no-partner 前提。

还读取了 AlyciaBHZ #5897 的 `RadiusFourCertificates.lean`：具体整数表先由内核归约验证，再交给既有一般消费者，几何闭包与路径计数输运分开。这里沿用同样的依赖方向，复用 RootTubeStrongUnextendibility 而非再抄一遍相同的图论消费者。两条外部研究线的定理都没有被当作 MUB 的数学假设。

### 38.7 准确的完成边界

本次实际完成的是先前幅度 Lean/Scribe 的远端交付、六十标签图及颜色的精确重建、二次 refutation 的逐系数核验，以及将有限 hNoPartner 消去的 Lean/Scribe 源码。没有运行 Lean/lake、Scribe emitter 或 transitive axiom report，所以 `decide +kernel` 仍是待实际 elaboration 的证明脚本，不是已执行的 kernel verdict。

完整解析覆盖和区间表达式可靠性仍需内核桥接；新参数区间的覆盖也仍未完成。颜色标签没有被证明与全部真实共同无偏投影一一对应；只能在显式的解析覆盖与 overlap 包含前提下使用。

## 40. 去相位结构给出的固定种子统一迹缺陷改进

### 40.1 定义与假设

沿用 [openai2026maximum](../../../Library/QuantumBounds/openai2026maximum.md) 的固定种子块与固定补空间标架。以下只使用其 `completion.tex` 的精确块恒等式，不以全局计算结论作为假设。

令六阶去相位复 Hadamard 矩阵为

```math
H'=\begin{pmatrix}E'&B'\\C'&D'\end{pmatrix},\qquad
H'^*H'=H'H'^*=6I,\qquad
E'=\begin{pmatrix}1&1\\1&a'\end{pmatrix}.
```

种子中心的单位模块为

```math
E_0=\begin{pmatrix}1&1\\1&a_0\end{pmatrix},\quad
B_0=\begin{pmatrix}1&1&1&1\\b_0&b_1&b_2&b_3\end{pmatrix},\quad
C_0=(\mathbf1\ c_0).
```

不假设种子中心存在 Hadamard 补全。设 `B_0,C_0` 均秩二，固定列正交标架 `K_B,K_C`，其像分别为 `ker B_0`、`ker C_0^*`。记

```math
Y=K_C^*D'K_B,\quad S=\mathbf1^*c_0,\quad v=|S|<4,\quad
\Delta=16-v^2.
```

九个种子相位的弧度位移属于闭球 `||s||≤R`，`R≥0`。记各块弦位移范数为

```math
e=\|E'-E_0\|_F,\quad b=\|B'-B_0\|_F,\quad c=\|C'-C_0\|_F.
```

单位圆弦长不超过弧长，故 `e²+b²+c²≤R²`。此处标量 `c` 与种子列 `c_0` 不同。

定义实对称矩阵及其最大特征值

```math
K(v)=\begin{pmatrix}
1+\dfrac2{4-v}&\dfrac{\sqrt6}{4-v}\\[3pt]
\dfrac{\sqrt6}{4-v}&\dfrac{24}{16-v^2}
\end{pmatrix},\qquad
\lambda(v)=\frac{K_{11}+K_{22}+
\sqrt{(K_{11}-K_{22})^2+4K_{12}^2}}2.
```

### 40.2 命题：秩一坐标扰动的迹界

在 40.1 的假设下，有

```math
0\le q_{\rm act}:=\operatorname{tr}(6I-Y^*Y)
\le \lambda(v)(b^2+c^2)\le\lambda(v)R^2.
```

证明。去相位固定第一行与第一列，因此存在行向量 `d_b` 与列向量 `d_c` 使

```math
B'-B_0=e_2d_b,\qquad C'-C_0=d_ce_2^*,\qquad e_2=(0,1)^T.
```

置 `r=d_bK_B`、`t=d_c^*D'K_B`、`u=E'^*e_2=(1,overline(a'))^T`。列正交关系给出

```math
C_0^*D'K_B=-ur-e_2t.
```

令 `M=C_0^*C_0`。由

```math
M^{-1}=\Delta^{-1}\begin{pmatrix}4&-S\\-\overline S&4\end{pmatrix},\qquad
P_C=C_0M^{-1}C_0^*,
```

以及文献的精确压缩缺陷恒等式，得到

```math
6I-Y^*Y=K_B^*B'^*B'K_B+K_B^*D'^*P_CD'K_B\succeq0,
```

```math
q_{\rm act}=\|r\|^2+
\operatorname{tr}\big((ur+e_2t)^*M^{-1}(ur+e_2t)\big).
```

令

```math
\kappa=\frac{8-2\Re(S\overline{a'})}{\Delta},\qquad
\eta=\frac4\Delta,\qquad
\gamma=\frac{4a'-S}{\Delta}.
```

展开上式为

```math
q_{\rm act}=(1+\kappa)\|r\|^2+\eta\|t\|^2
+2\Re\big(\gamma\operatorname{tr}(r^*t)\big).
```

利用 `|a'|=1`，有 `κ≤2/(4−v)`、`|γ|≤1/(4−v)`。又由 `B'^*B'+D'^*D'=6I` 得 `||D'||op≤√6`，故 `||r||≤b`、`||t||≤√6 c`。Cauchy–Schwarz 与 Rayleigh 商界遂给出

```math
q_{\rm act}\le
\left(1+\frac2{4-v}\right)b^2+
\frac{24}{\Delta}c^2+\frac{2\sqrt6}{4-v}bc
=\begin{pmatrix}b&c\end{pmatrix}K(v)\binom bc
\le\lambda(v)(b^2+c^2).
```

### 40.3 命题：对原统一界的严格改进

定义

```math
A_* =\min(2,\|E_0\|_{\rm op}+R),\qquad
Q_{\rm src}=R^2\left(1+\frac{A_*^2+6}{4-v}\right),\qquad
Q_{\rm new}=R^2\lambda(v).
```

若 `R>0`，则 `Q_new<Q_src`；若 `R=0`，二者均为零。

证明。直接计算

```math
\det K(v)=\frac{30}{16-v^2}>0,\qquad
\operatorname{tr}K(v)=1+\frac2{4-v}+\frac{24}{(4-v)(4+v)}.
```

因 `K11>0`，矩阵 `K(v)` 正定，故 `λ(v)<tr K(v)`。同时

```math
\operatorname{tr}K(v)\le1+\frac8{4-v}
\le1+\frac{A_*^2+6}{4-v},
```

其中末步使用 `||E_0||op=√(2+|1+a_0|)≥√2`，所以 `A_*≥√2`。乘以 `R²` 即得结论。

### 40.4 推论：同一极分解的更小统一半径

若 `Q_new<6`，则 `Y` 的酉极因子 `V` 满足

```math
\|Y-\sqrt6 V\|_F\le
\frac{Q_{\rm new}}{\sqrt6+\sqrt{6-Q_{\rm new}}}.
```

证明。缺陷矩阵的特征值 `ℓ_1,ℓ_2` 非负，且和不超过 `Q_new<6`。故 `Y` 可逆，其奇异值为 `√(6−ℓ_j)`。逐项有

```math
\sqrt6-\sqrt{6-\ell_j}
=\frac{\ell_j}{\sqrt6+\sqrt{6-\ell_j}}
\le\frac{\ell_j}{\sqrt6+\sqrt{6-Q_{\rm new}}}.
```

平方求和并用 `√(ℓ_1²+ℓ_2²)≤ℓ_1+ℓ_2`。这一步复用文献的极分解估计；40.2 改进的是统一迹上界，不是固定实际迹缺陷时的极分解公式。

### 40.5 推论：伴随方向与可行种子约束

40.2 还可用 `v_B=|Σb_j|` 代替 `v`；因此可取两个方向所得界的较小者。若 `R<1`，任意可行种子进一步满足

```math
q_{\rm act}\le R^2\lambda(2+2R).
```

证明。对 `H'^*` 取交换后的标架 `K_{B,adj}=K_C`、`K_{C,adj}=K_B`，其压缩块恰为 `Y^*`，新的 `C_0` 为 `B_0^*`。列和模为 `|Σoverline(b_j)|=v_B`，而 `tr(Y^*Y)=tr(YY^*)`。

另一方面，可行补全满足 `1+a'+Σc'_j=0`，所以

```math
v=\left|\sum c_{0j}\right|
\le |1+a'|+\left|\sum(c_{0j}-c'_j)\right|
\le2+2c\le2+2R<4.
```

`b` 方向同理。矩阵 `K(v)` 的元素在 `[0,4)` 上均非减且非负，其最大特征值由非负向量的 Rayleigh 商取得，故 `λ(v)` 非减。应用 40.2 得结论。超过 `2+2R` 的种子和模本身即排除可行补全；此推论不为秩亏的不可行种子构造标架。

### 40.6 推论：既有必要条件的单调加强

在文献的同一固定种子、同一酉参数单元下，将原极分解半径换成 40.4 的较小上界，会减小或保持块位移界 `z` 与线性余项界 `E_r`。因此以这些精确实数界形成的范数排除与方向排除不丢失原先成立的证书。

证明。原式中 `z` 对极分解半径 `p` 非减；`e_off` 对 `z` 非减；`E_r` 对 `e_off,p` 非减。范数必要条件的右侧为 `z²`。方向必要条件中 `E_r` 与 `z²` 的系数分别为范数和非负负部权重，故其右侧亦非减。极因子 `V` 由同一个 `Y` 唯一决定，更换统一界不改变参数单元归属。

这些精确算术下必要条件的加强，本身不认证舍入实现，也不建立全部种子与参数单元的完整覆盖。

### 40.7 命题：一个原范数检验未排除的闭参数单元

以下星号表示共轭转置。取精确去相位种子

```math
H_0=\begin{pmatrix}
1&1&1&1&1&1\\
1&i&-1&i&-i&-i\\
1&-1&i&-i&-i&i\\
1&-i&i&-1&i&-i\\
1&-i&-i&i&-1&i\\
1&i&-i&-i&i&-1
\end{pmatrix},
```

并在前两行与前两列后分块。置 `r=√7` 及

```math
N_B=\begin{pmatrix}0&-2(1+i)\\0&2i\\r&1\\-r&1\end{pmatrix},\qquad
N_C=\begin{pmatrix}0&-2(1-i)\\r&1\\-r&1\\0&-2i\end{pmatrix},\qquad
K_B=N_B/\sqrt{14},\quad K_C=N_C/\sqrt{14}.
```

种子半径取 `R=2π·0.0320001`。按 40.1 所引文献的酉参数化，令闭单元为

```math
\alpha\in[1/16,2/16],\quad t\in[2/16,3/16],\quad
\beta\in[12/16,13/16],\quad\gamma\in[3/16,4/16],
```

其中相位以周为单位，

```math
V(\alpha,t,\beta,\gamma)=e^{2\pi i\alpha}
\begin{pmatrix}
e^{2\pi i\beta}\cos(2\pi t)&e^{2\pi i\gamma}\sin(2\pi t)\\
-e^{-2\pi i\gamma}\sin(2\pi t)&e^{-2\pi i\beta}\cos(2\pi t)
\end{pmatrix}.
```

**结论。** 不存在九坐标种子距离不超过 `R`、且压缩补全的极因子在该闭单元中有上述表示的可行 Hadamard 补全。同一种子、标架、半径及单元下，原文献的范数必要条件却严格成立，因而该原范数检验不能排除这一单元。本结论不涉及其余检验或继续细分后的判定。

证明。精确相乘得

```math
H_0^*H_0=H_0H_0^*=6I,\quad
N_B^*N_B=N_C^*N_C=14I,\quad B_0N_B=C_0^*N_C=0.
```

故标架满足 40.1 的假设，且种子球本身非空。两种子和的模均为 `√2`，因此

```math
m_B=m_C=m=\sqrt{4-\sqrt2},\qquad
A_0=\sqrt{2+\sqrt2},\qquad A_*=2.
```

单元中点为 `(3,5,25,7)/32`；记其中点矩阵为 `U`，并令

```math
D=D_{\rm span}+\frac{\sqrt6}{14}N_CUN_B^*,\qquad
D_{\rm span}=-C_0E_0^*(B_0B_0^*)^{-1}B_0.
```

明确地，

```math
7D_{\rm span}=\begin{pmatrix}
2+i&2-3i&-2+i&-2+i\\
-2+i&-3+2i&-1+2i&-1+2i\\
-2+i&-3+2i&-1+2i&-1+2i\\
2-3i&-3-8i&-3+2i&-3+2i
\end{pmatrix}.
```

取 `h=π/16` 并定义

```math
F=\sum_{i,j=0}^3(|D_{ij}|-1)^2,\qquad
p(Q)=\frac{Q}{\sqrt6+\sqrt{6-Q}},\qquad
z^2(Q)=\frac{R^2(\sqrt6+2)^2}{4-\sqrt2}+(6h+p(Q))^2.
```

原、新迹界分别为

```math
Q_{\rm old}=R^2\left(1+\frac{10}{4-\sqrt2}\right),\qquad
Q_{\rm new}=R^2\lambda(\sqrt2).
```

两者均小于六。下列端点全是所显示的有限十进制有理数：

```math
1.773287283035\le F\le1.773287283036,\\
1.750505279656\le z^2(Q_{\rm new})\le1.750505279657,\\
1.794499073566\le z^2(Q_{\rm old})\le1.794499073567.
```

这些包围只需有理运算与正平方根。具体取 `ω=exp(iπ/16)`，利用半角公式

```math
\Re\omega=\tfrac12\sqrt{2+\sqrt{2+\sqrt2}},\qquad
\Im\omega=\tfrac12\sqrt{2-\sqrt{2+\sqrt2}},
```

则四个中点相位因子是 `ω³,ω⁵,ω²⁵,ω⁷`。逐次四则区间运算，并在每次平方根处以分母 `10^45` 的有理数向外取整，即得上述包围；`π` 由 Machin 恒等式 `16 arctan(1/5)−4 arctan(1/239)` 及分别截断一百项、三十项的交错级数余项包围。因此

```math
F-z^2(Q_{\rm new})>0.02278,\qquad z^2(Q_{\rm old})-F>0.02121.
```

若该闭单元关联一个可行补全，40.4 的极分解界和文献的正交比较分解对整个闭单元给出 `||D'−D||_F²≤z²(Q_new)`；单元边界的每个弧度偏移仍不超过 `h`。逐项反三角不等式与 `|D'ij|=1` 给出

```math
F\le\|D'-D\|_F^2\le z^2(Q_{\rm new}),
```

矛盾。另一方面 `F<z²(Q_old)`，故原范数必要条件不构成排除。更换统一迹界不改变同一压缩矩阵的极因子，两个检验确实比较同一单元。

此命题只针对明确给出的精确种子、固定标架与单元，不将它们认作某次存档计算的种子记录或标架选择；它既不认证舍入实现，也不建立全域覆盖。

## 41. 互补三相位 Fourier 预算的精确全局下界

### 41.1 定义与极值命题

固定 `ω=exp(2πi/3)`。对单位模三元组定义未归一化 Fourier 系数及能量

```math
\lambda_r(z)=z_0+\omega^rz_1+\omega^{2r}z_2,\qquad
E_r(z)=|\lambda_r(z)|^2,\qquad r\in\mathbb Z_3.
```

定义实际双行预算可行集

```math
\mathcal P_6=\{(z,w)\in\mathbb C^3\times\mathbb C^3:
|z_j|=|w_j|=1,\ E_r(z)+E_r(w)=6\quad(j,r\in\mathbb Z_3)\}.
```

令

```math
\gamma=3-3\sqrt{2\sqrt3-3},\qquad 0<\gamma<1.
```

Matolcsi–Weiner，*An improvement on the Delsarte-type LP-bound with application to MUBs*，Theorem 4.1 的证明 pp.8–9，DOI [10.1142/S1230161215500018](https://doi.org/10.1142/S1230161215500018)，已给出单行约束 `E_r≤6` 下的精确下界 `m=(3/2)(1−√(16√6−39))`。本节保留两行的互补约束，而不只逐行使用该松弛。相反 deltoid 的交域、判别式及六个最大径向极值点与 `C_6` 的联系，见 Szöllősi，*A two-parameter family of complex Hadamard matrices of order 6 induced by hypocycloids*，式 (15) 与 Lemma 3.2，DOI [10.1090/S0002-9939-09-10102-8](https://doi.org/10.1090/S0002-9939-09-10102-8)。以下对已知交域推导 Fourier 能量的定向全局支撑界及等号谱（`repo-derived`）；交域、径向极值点及其 Hadamard 构造不作为新增结果。

**命题 41.1。** 对每个 `(z,w)∈P_6` 及每个模式 `r`，

```math
\boxed{\gamma\le E_r(z),E_r(w)\le6-\gamma.}
```

上下端点均可达到。因此

```math
\min_{(z,w)\in\mathcal P_6}\min_{r\in\mathbb Z_3}E_r(z)
=3-3\sqrt{2\sqrt3-3}=0.956249884100\ldots.
```

若某个 `E_r(z)=γ`，则该行的其余两个能量为 `3` 和 `6−γ`，另一行的能量逐模与之互补。

证明。分别除去两行的公共相位，不改变预算。可设 `z=(1,a,b)`、`w=(1,c,d)`。其自相关和分别为

```math
s=a+b/a+1/b,\qquad h=c+d/c+1/d.
```

展开 Fourier 能量，逐模预算等价于

```math
\Re\bigl(\omega^r(s+h)\bigr)=0\qquad(r=0,1,2),
```

故 `h=−s`。为验证所需判别式不等式，令 `u=a`、`v=b/a`、`w_0=1/b`。三个数均为单位模且乘积为一，因此是 `T³−sT²+overline(s)T−1` 的根。对 `V=(u−v)(u−w_0)(v−w_0)` 有 `overline(V)=−V`，故此三次多项式的判别式为 `V²=−|V|²≤0`。对另一行重复同一计算，得到

```math
F(s)\le0,\qquad F(-s)\le0,\qquad
F(s)=|s|^4+18|s|^2-8\Re(s^3)-27.
```

对两行作同一循环调制即可将所考察模式移到零模式。记 `E=E_0(z)`。若 `E>1`，则 `E>γ`；否则 `0≤E≤1`，写

```math
s=-A+iy,\qquad A=(3-E)/2\in[1,3/2],\qquad Y=y^2\ge0.
```

两个判别式的较大者为

```math
\max(F(s),F(-s))=G_A(Y),
```

其中

```math
G_A(Y)=(A^2+Y)^2+18(A^2+Y)-27+8A|3Y-A^2|.
```

在 `0≤Y≤A²/3` 上，

```math
G_A'(Y)=2(A^2+Y)+18-24A
\le\frac83A^2+18-24A\le-\frac{10}{3}<0.
```

最后一步使用右侧二次式在 `[1,3/2]` 上递减且在 `A=1` 取值 `−10/3`。在 `Y≥A²/3` 上，

```math
G_A'(Y)=2(A^2+Y)+18+24A>0.
```

因此 `G_A` 在非负实轴上的唯一最小点是 `Y=A²/3`，故

```math
0\ge G_A(Y)\ge G_A(A^2/3)
=\frac{16}{9}A^4+24A^2-27.
```

令 `R=4A²/3`，右端为 `R²+18R−27`。其唯一非负根为 `6√3−9`，所以

```math
A^2\le\frac94(2\sqrt3-3),\qquad
E=3-2A\ge3-3\sqrt{2\sqrt3-3}=\gamma.
```

交换两行并对所有模式应用此下界，再由预算得到上界 `6−γ`。

若 `E=γ`，严格单调性迫使 `Y=A²/3`，且两个判别式都为零。此时

```math
E_1(z)=3+A-\sqrt3\,y,\qquad
E_2(z)=3+A+\sqrt3\,y,
```

而 `|√3y|=A`，故其余两个能量恰为 `3` 和 `3+2A=6−γ`。为证明可达，取已知最大径向极值点中的 `s=−A+iA/√3`，其中 `A=(3/2)√(2√3−3)`。它等于上述 Szöllősi Lemma 3.2 的 `√(−9+6√3) exp(5πi/6)`。下列显式相位验证这一点同时达到所求定向支撑界。置

```math
\psi=\arccos\frac{\sqrt3-1}{2},\qquad
\vartheta=\frac{4\pi}{3}-\psi,\qquad q=e^{i\vartheta},
```

并定义两条单位模行

```math
z_*=(1,q,q^{-1}),\qquad
w_*=(1,\omega q^{-1},\omega^2q).
```

则 `(z_*,w_*)∈P_6`，且其能量分别为

```math
(E_0(z_*),E_1(z_*),E_2(z_*))=(\gamma,3,6-\gamma),
```

```math
(E_0(w_*),E_1(w_*),E_2(w_*))=(6-\gamma,3,\gamma).
```

若 `A,B` 是以这两行为首行的三阶 circulant 矩阵，则

```math
H=\begin{pmatrix}A&B\\B^*&-A^*\end{pmatrix}
```

为六阶复 Hadamard 矩阵，即所有矩阵元模长为一且 `HH*=6I`。

具体地，由三角恒等式，第一行的 Fourier 系数均为实数，且

```math
\lambda_0(z_*)=\frac{3-\sqrt3-\sqrt{6\sqrt3}}2,\qquad
\lambda_1(z_*)=\sqrt3,\qquad
\lambda_2(z_*)=\frac{3-\sqrt3+\sqrt{6\sqrt3}}2.
```

利用

```math
(3-\sqrt3)^2(6\sqrt3)=36(2\sqrt3-3),
```

平方得到第一条能量等式。第二行由第一行共轭再作一次循环调制得到，因此

```math
E_r(w_*)=E_{-r-1}(z_*),
```

即其模式顺序为 `(E_2(z_*),E_1(z_*),E_0(z_*))`。这给出第二条能量等式及全部逐模预算。

最后，circulant 矩阵可由同一 Fourier 矩阵酉对角化，故 `A,B` 正规并交换。逐模预算给出 `AA*+BB*=6I`，所以

```math
HH^*=\begin{pmatrix}
AA^*+BB^*&AB-BA\\
B^*A^*-A^*B^*&B^*B+A^*A
\end{pmatrix}=6I.
```

所有块的矩阵元模长均为一，因此 `H` 是所述复 Hadamard 矩阵。证毕。

此处的全局极值针对完整单位模双行预算集合 `P_6`，并由实际六阶 circulant 块矩阵达到。它将第 20 节的非零模式结论定量化，但没有给完成基的 symmetry affinity 加入任何新不等式；特别地，`γ<1` 不是第 18 节的 `α_min(T)>1`，两者既非同一变量，也非同一可行集。本构造不声称属于任意预先固定的 strict-X edge 或其 completion context。

### 41.2 能量谱的精确凸包与线性支撑函数

**推论 41.2。** 定义实际双行预算的第一行能量谱集合

```math
\mathcal S=\{(E_0(z),E_1(z),E_2(z)):(z,w)\in\mathcal P_6\}.
```

则

```math
\operatorname{conv}(\mathcal S)
=\{e\in\mathbb R^3:e_0+e_1+e_2=9,\
\gamma\le e_j\le6-\gamma\ (j=0,1,2)\}
=\operatorname{conv}\{\sigma(\gamma,3,6-\gamma):\sigma\in S_3\}.
```

特别地，对任意实数权重 `c_0,c_1,c_2`，有精确支撑函数

```math
\max_{e\in\mathcal S}\sum_{j=0}^2c_je_j
=3\sum_{j=0}^2c_j+(3-\gamma)\bigl(\max_jc_j-\min_jc_j\bigr),
```

而最小值等于右端第二项取负号后的表达式。令 `D={u+v+w:|u|=|v|=|w|=1,uvw=1}`，即上述 Szöllősi 使用的 deltoid 单位相位参数像。该参数化对自相关像是满射：给定 `(u,v,w)`，取 `a=u,b=uv` 即有 `a+b/a+1/b=u+v+w`。两行相位可独立选取，所以实际互补自相关集合恰为 `D∩(−D)`。通过 `e_j=3+2Re(ω^j s)` 的实仿射同构，其凸包就是以上述 Szöllősi 六个已知最大径向极值点为顶点的正六边形。

证明。记右侧由坐标界定义的多边形为 `P`。Parseval 恒等式与 41.1 给出 `S⊆P`。`P` 的每个顶点至少有两个坐标处于区间端点，否则可在保持坐标和及所有已激活坐标约束的情况下作非零双向微扰。两个坐标同时等于 `γ` 时，第三个为 `9−2γ>6−γ`，不可行；两个同时等于 `6−γ` 时，第三个为 `2γ−3<γ`，也不可行。因此顶点恰为 `(γ,3,6−γ)` 的六个排列。

41.1 的显式可达对给出其中一个顶点。对两行同时循环调制使能量坐标作三循环；同时共轭使模式指标 `r` 变成 `−r`，提供一个换位。这两个操作保持单位模与逐模预算并生成全部六个排列，故所有顶点均属于 `S`。于是 `P⊆conv(S)`，证明凸包等式。

每个顶点都可写为 `3(1,1,1)+(3−γ)(e_j−e_i)`，其中 `i≠j`，而这里 `e_i` 表示标准坐标向量。线性泛函的最大值由最大权重处的正偏移与最小权重处的负偏移取得，给出支撑函数公式；取负权重给出最小值。证毕。

本推论只把线性能量目标的极值化为六个顶点。它不把原可行集 `S` 认作整个凸包，也不允许将任意非线性目标的最小值或含额外 completion 变量的优化直接限制到这六点。

## 42. 正则 strict-X 种子附近的扩大矩形与正交三元组覆盖

### 42.1 精确参数分支与结论

令

```math
\delta=2^{-24},\qquad
\mathcal P=\{\alpha=a+ib:\ |a+1/5|\le\delta,\ |b|\le\delta\},
\qquad c(t)=\frac{1+it}{1-it}.
```

对

```math
p_\alpha(t)=(1+a)t^3+bt^2+(a-3)t+b,
```

将三个实根从小到大排列后按 `(最小,最大,中间)` 取序；对 `p_{-alpha}` 同样将三个实根从小到大排列后按 `(最小,最大,中间)` 取序。它们的 Cayley 像分别记为 `r0,r1,r2` 与 `s0,s1,s2`。定义

```math
A=\operatorname{circ}(r_0r_1,r_1,1),\quad
B=\operatorname{circ}(s_0s_1,s_1,1),\quad
H=\begin{pmatrix}A&B\\B^*&-A^*\end{pmatrix},\quad H_0=LH,
```

其中 `L` 将行按零起始索引 `(2,0,1,4,5,3)` 排列。中心参数 `alpha=-1/5` 给出

```math
r_1=(-3+4i)/5,\qquad s_1=(-2+i\sqrt{21})/5,
```

因此 `H0` 正是第 35、36 节的对称块种子。以下只讨论这个固定构造分支，不把其他根的排列或其他 Hadamard 参数默认为同一分支。

令 `S` 在两个坐标三元组内分别作循环位移，`E0,E1,E2` 为其秩二谱投影。

**命题 42.1。** 对每个 `alpha in P`，若三个单位向量 `v0,v1,v2` 两两正交，并各自对坐标基与 `H0/sqrt(6)` 无偏，则

```math
\boxed{\sum_{r=0}^2\sum_{k=0}^2
\langle v_r,E_kv_r\rangle^2=3.}
```

特别地，第 36 节提出的 collision 小于二的区域为空。任意实际六元共同无偏 completion `C` 均满足

```math
\boxed{\alpha_S(C)=2.}
```

该矩形中的固定边至多具有一个 completion，按射线排列与相位等价计，因而不能扩展为四 MUB。这里的证明结合精确区间证书与下述解析解释；结论不覆盖整个 strict-X 家族。

### 42.2 完整射线覆盖所使用的精确有限证据

复用的区间程序、原始中心与允许边资料，以及扩大矩形的可重放证书，固定在[实验真源](https://github.com/the-omega-institute/trureturing-experiments/tree/623073ea4a922fa7154a5b45797822a56ab6f9d7/experiments/mub-strict-x-rectangle)。原 `2^-32` 矩形的全局覆盖来自[保留的研究提交](https://github.com/the-omega-institute/trureturing/tree/63a005da4c695c3136da0bac01e3c138e7338840/docs/develop/certificates/real_x_global_cover)。本节复用其种子、六十中心、允许图和区间算术；新增量是明确扩大后的连续参数范围及下面的对称分支传播论证，不将旧矩形的结论重新认作新发现。

多项式系数恒等式为

```math
(1-it)^3\big(c(t)^3-\alpha c(t)^2+
\overline\alpha c(t)-1\big)=-2i p_\alpha(t).
```

参数区间上的端点符号与非零导数区间隔离每个三次多项式的三个实根。由 Vieta 关系，Cayley 像均为单位模，乘积为一，两个和分别为 `alpha` 与 `-alpha`。循环行比的和相消，且 circulant 块相互交换，故 `H0 H0*=6I`。三十个正的平方子式见证进一步排除任意两条平方行或平方列成比例。Fourier 族与其转置族的标准代表分别具有相应的比例对；该性质在 Hadamard 单项式等价下保持，因此整个矩形保持在两类 Fourier 接缝之外。

每条共同无偏射线均可去相位为 `u0=1, |uj|=1`，单位向量为 `u/sqrt(6)`。五个剩余坐标由全部三十二个紧图覆盖：

```math
u_j=\varepsilon_j\frac{1+it_j}{1-it_j},\qquad
\varepsilon_j\in\{-1,1\},\quad t_j\in[-1,1].
```

图边界包含在内；符号改变处使用精确变换 `t -> -1/t`，仅在非零坐标上使用。残差取 `|H0* u|²-6` 的前五项，第六项由 Gram 恒等式推出。

所有紧图的闭二分覆盖只接受三种终止情形：残差区间排除零、Krawczyk 像与原盒不交，或剩余盒经正确图变换进入已验证的根唯一性盒。若 `m` 是盒 `X` 的中心，`C` 是任意提出的有理预条件矩阵，则

```math
K=m-Cf(m)+(I-CJ(X))(X-m)
```

包含 `X` 中的每个实际零点；因此以 `X intersect K` 收缩不会丢失零点。这个零点保持性质不预设 `C` 可逆。闭二分的两个子盒覆盖父盒。全部三十二图终结且没有待处理或未决盒，遂证明全部共同无偏射线进入六十个根盒。

六十个盒的半径为 `r=2^-12`。每个盒另有严格包含 `K subset interior X` 和

```math
\|I-CJ(X)\|_\infty<1.
```

故对每个固定的实际参数，Newton 映射都是该闭盒内的压缩映射；此范数界也强制 `C` 可逆，因此其唯一不动点是残差的唯一零点。所有包围对同一个完整参数矩形成立。

扩大矩形的精确安全界包括

```math
\|I-CJ(X)\|_\infty
\le\frac{385012914919}{2^{40}}<\frac{351}{1000},
\qquad
\|K-m\|_\infty
\le\frac{206508646}{2^{40}}<\frac{77}{100}r.
```

根盒进一步收缩后，独立有理区间计算检查全部 `choose(60,2)=1770` 对：所有射线不同，且 `1656` 个禁止对满足

```math
|\langle v_i,v_j\rangle|^2>1/500000.
```

剩余 `114` 条允许边只是实际正交图的上图，不以小残差断言某条边存在。该上图由六顶点完全块 `K` 与其余五十四顶点的二分图不交并组成，两块之间没有边。因此每个实际正交三元组的三个标签都属于 `K`。

### 42.3 不依赖扩大后区间像的对称分支传播

这里补足六个标签始终 mode-local 的解析步骤，避免把过宽的区间像当作实际分支。

先使用连续唯一根分支的标准传播事实。设连通参数域上的方程族连续，并由一个固定根盒中的一致严格压缩产生连续唯一根分支。设连续对称作用保持每个参数处的方程。若该分支在一个参数处被对称作用固定，且根始终在唯一性盒内部，则它在整个参数域上被固定。

证明。固定参数集合由连续性为闭集。在一个固定参数处，作用后的根就在原根盒内部；由连续性，邻近参数处作用后的根仍在同一盒中。局部唯一性使它与原分支相等，故固定参数集合相对开。它非空，而参数域连通，所以等于整个参数域。证毕。

在本命题中，作用是射线上的

```math
\sigma(u)=Su/(Su)_0.
```

所有坐标为单位模，所以分母始终非零。参数化矩阵始终与同步三循环交换，故该作用保持共同无偏根。根分支连续性由连续残差与固定盒内的一致压缩得到。

中心的六条射线先通过原小矩形的根包含与位移验证重新确认是 `S` 的特征射线。旧唯一性盒半径为 `2^-16`，新盒半径为 `2^-12`，使用完全相同的有理中心，故旧盒严格包含在相应新盒内。中心根因唯一性而得到实际识别；不能只凭标签名称相同作此识别。上述传播事实于是证明六个新分支在整个扩大矩形中都是特征射线。

每条这样的单位射线的三个 mode probabilities 是 `(1,0,0)` 的某个排列，collision 恰为一。结合上述全覆盖和二分上图，任意三个实际共同无偏正交向量的总 collision 恰为三。六元 completion 的总 collision 因而为六，故

```math
\alpha_S(C)=\tfrac12(6-2)=2.
```

任何 completion 只能使用六个规范射线，故两个 completions 的射线集合相同，不能相互无偏。命题 42.1 得证。

此处保留同一参数下三个实际向量的全部无偏与两两正交条件，没有以独立相位见证替换共同变量，也没有复用第 35 节已否定的全局正交到逐模正交蕴含。扩大后的每个半边长是旧值的 `256` 倍；绝对矩形仍很小，六维四 MUB 与全 strict-X 覆盖仍未解决。

## 43. 互补三相位谱端点的最优线性稳定性

第 41 节确定了实际互补相位行的 Fourier 能量端点。本节进一步控制接近端点时的自相关位置。所用 deltoid 参数像与判别式仍归于 Szöllősi，*A two-parameter family of complex Hadamard matrices of order 6 induced by hypocycloids*，式 (15) 与 Lemma 3.2，DOI [10.1090/S0002-9939-09-10102-8](https://doi.org/10.1090/S0002-9939-09-10102-8)。以下最优线性误差界由该域上的多项式估计推出（`repo-derived`），不把已知参数域和第 41 节的端点重新作为新结果。

### 43.1 参数、结论与实际相位可达性

记

```math
k=\sqrt3,\qquad M=6k-9,\qquad C=\frac{3M}{4},\qquad
\kappa=\frac{56+24k}{11}=\frac{M-1}{C-1}.
```

对第 41 节的实际单位模互补行 `(z,w) in P_6`，令

```math
s=z_1\overline{z_0}+z_2\overline{z_1}+z_0\overline{z_2}=x+iy,
\qquad \delta=M-x^2-y^2,\qquad g=C-x^2.
```

**命题 43.1。** 对上述每个实际互补相位对，

```math
\boxed{0\le\delta\le\kappa g,\qquad g\ge0.}
```

常数 `kappa` 不能减小。等号 `delta=kappa g` 恰在以下两种情况下成立：

```math
(x^2,y^2)=(1,0)
\quad\text{或}\quad
(x^2,y^2)=(C,C/3).
```

第二种是第 41 节的四个定向支撑等号点。第一种可由实际相位行

```math
z=(1,-1,1),\qquad w=(1,1,i)
```

达到：它们的自相关分别为 `-1` 和 `1`，能量谱分别为 `(1,4,4)` 和 `(5,2,2)`，逐模相加为六。这里 `g=C-1>0`，且 `delta=M-1=kappa(C-1)`，故已在实际相位可行集上证明常数最优。

### 43.2 正权多项式证书与线性误差界

证明。先令

```math
F(x,y)=(x^2+y^2)^2+18(x^2+y^2)-8(x^3-3xy^2)-27.
```

实际单位模行的三个循环比均为单位模，乘积为一，和为 `s`。若它们为 `U,V,W`，则 `UV+UW+VW=conj(s)`。对 `D=(U-V)(U-W)(V-W)`，有 `conj(D)=-D`，而三次多项式的判别式恒等式给出

```math
F(x,y)=-|D|^2\le0.
```

互补行的自相关为 `-s`，所以同时有 `F(-x,-y)<=0`。以下只从这两个必要不等式推导结论，不假定任意四次不等式可行点都已有相位实现。

置 `u=x²,v=y²,r=u+v,p=2k+4`。两个不等式取平均给出

```math
B(r)=r^2+18r-27\le0,
\qquad B(r)=(r-M)(r+M+18).
```

第二因子为正，故 `r<=M`、`delta>=0`。由 `k²=3` 及 `(2k-3)²>=0`，有 `k<=7/4`，所以

```math
p^2x^2\le p^2M=24k+36\le78<81.
```

因此 `9-px` 和 `9+px` 均为正。直接展开得到正权证书

```math
\frac{(9-px)F(x,y)+(9+px)F(-x,-y)}2
=9\delta^2-8pg(3\delta+4u)\le0.
```

若 `g<0`，则 `u>C>0`，右端严格为正，矛盾。故 `g>=0`。若 `g=0`，证书立即给出 `delta=0` 及 `v=u/3`。这个代数步骤也单独给出第 41 节定向界的无微分证明。

下面证明最优线性界。恒等式

```math
\kappa(C-1)=M-1,\qquad
\kappa(14-6k)=32
```

均由 `k²=3` 得到，且 `kappa>1`。

若 `u<=1`，则

```math
\kappa g-\delta
=(\kappa-1)(1-u)+v\ge0.
```

等号当且仅当 `u=1,v=0`。

若 `u>=1`，记 `a=|x|`，于是 `a>=1`、`a²=u<=C`。在两个四次约束中选取带 `+8a(u-3v)` 的一个，并代入 `r=M-delta`、`u-3v=3delta-4g`，得到

```math
P(\delta):=\delta^2+12(2a-k)\delta-32ag\le0.
```

又有精确因式分解

```math
P(\kappa g)
=g(a-1)\bigl[24\kappa-32-\kappa^2(a+1)\bigr].
```

为确定方括号的符号，只需以下有理界：

```math
\frac53<k\le\frac74,\qquad
\frac{96}{11}<\kappa\le\frac{98}{11},\qquad
1\le a\le a^2\le C\le\frac98.
```

因此

```math
24\kappa-32-\kappa^2(a+1)
\ge\frac{1952}{11}-\left(\frac{98}{11}\right)^2\frac{17}{8}
=\frac{2127}{242}>0.
```

故 `P(kappa g)>=0`。如果 `delta>kappa g`，则

```math
P(\delta)-P(\kappa g)
=(\delta-\kappa g)\bigl(\delta+\kappa g+12(2a-k)\bigr)>0,
```

与 `P(delta)<=0` 矛盾。所以 `delta<=kappa g`。若线性界取等号，上述分解迫使 `g=0` 或 `a=1`；前者给出 `(u,v)=(C,C/3)`，后者结合等号给出 `(u,v)=(1,0)`。反向代入可直接验证。命题得证。

### 43.3 谱端点附近的显式位置控制

令 `A=sqrt(C)`、`b=sqrt(C/3)`，并从四个定向等号点中选择与 `x,y` 同号的点。恒等式

```math
 y^2-C/3=g-\delta
```

及 `kappa>2` 给出

```math
\left||x|-A\right|\le\frac{g}{A},\qquad
\left||y|-b\right|\le\frac{(\kappa-1)g}{b}.
```

因此到四个等号点的欧氏距离至多为

```math
\frac{g}{A}\sqrt{1+3(\kappa-1)^2}.
```

对于靠近下端点的模式零能量 `E0=gamma+epsilon`，若 `0<=epsilon<=2A`，则

```math
x=-A+\varepsilon/2,\qquad
 g=A\varepsilon-\varepsilon^2/4\le A\varepsilon.
```

故到对应下端点等号点的距离至多为

```math
\varepsilon\sqrt{1+3(\kappa-1)^2}.
```

同时循环调制两行可将任意模式化为模式零；交换两行则将上端点化为另一行的下端点。因此同样适用于任一能量端点。本结论控制的是实际互补相位行的谱与自相关，不把它自动提升为共同无偏 completion 的 symmetry-affinity 下界；后者仍需保留完整共享相位和正交约束。

## 44. 非 Fourier 双循环边上的完整低 affinity 反例

第 18 节以整个 completion fibre 定义 `alpha_min(T)`，没有附加相位判别式非零的条件。下面给出一个非 Fourier 双循环边及其完整 completion，满足 `alpha_S=2/9`。因此，该边所在的闭分支不能使用“所有 completions 均有 `alpha_S>=1`”作为统一目标。第 18 节的条件蕴含仍然正确；本节修正的是下界目标的适用域。

本例处于一个相位判别式为零的边界，不否定非零判别式内域的下界。所得 completion 本身又属于 Fourier 等价类，故第 11 节的文献排除仍可将其从假想 quartet 中移除。Diţă 六阶矩阵存在多个 completions 已是已知事实，见 Brierley–Weigert，*Constructing Mutually Unbiased Bases in Dimension Six*，[arXiv:0901.4051，§4.1](https://arxiv.org/abs/0901.4051)。本节不把 completion 的存在重新列为新结果，而给出当前三循环下的精确 affinity 及其对本卷目标的限制。

### 44.1 固定边、三循环与 conference 规范

使用一基索引，固定

```math
P=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},
\qquad S=\operatorname{diag}(P,P).
```

取

```math
A=\begin{pmatrix}1&-1&1\\1&1&-1\\-1&1&1\end{pmatrix},\qquad
B=\begin{pmatrix}1&1&i\\i&1&1\\1&i&1\end{pmatrix},
\qquad H=\begin{pmatrix}A&B\\B^\dagger&-A^\dagger\end{pmatrix},
\qquad T=H/\sqrt6.
```

两条首行的自相关分别为 `-1,1`，Fourier 能量谱分别为 `(1,4,4)` 和 `(5,2,2)`。这是第 43 节 `delta=kappa g` 且 `g>0` 的实际相位等号例。第一行的循环相位比为 `(-1,-1,1)`，故其判别式为零；所有 Fourier 系数仍然非零。

令

```math
R=\operatorname{diag}(-i,-i,-i,i,i,i),\qquad
K=(e_6\ e_4\ e_5\ e_2\ e_3\ e_1),
```

以及

```math
C=\begin{pmatrix}I_3-J_3&2I_3-J_3\\2I_3-J_3&J_3-I_3\end{pmatrix}.
```

直接相乘得到

```math
RHK=I+iC,\qquad C=C^T,\qquad C^2=5I_6.
```

最后一个恒等式由 `J3²=3J3` 得到。因此

```math
T_c=RTK=(I+iC)/\sqrt6
```

是 flat unitary，原固定边 `T` 亦然。`R,K` 都与 `S` 交换。

### 44.2 保持两组 flatness 的显式 completion

**命题 44.1。** 上述固定边有完整 completion `W`，其每列相对 `S` 的三个 mode probabilities 是 `(1/9,4/9,4/9)` 的一个置换，并且

```math
\boxed{\alpha_S(W)=2/9.}
```

证明。定义实正交 signed permutation

```math
M=\begin{pmatrix}
1&0&0&0&0&0\\
0&0&0&0&1&0\\
0&0&0&-1&0&0\\
0&-1&0&0&0&0\\
0&0&0&0&0&1\\
0&0&1&0&0&0
\end{pmatrix}.
```

有 `MCM^T=C`，故 `MTc=TcM`。一个直接验证是令 `E=diag(1,-1,-1,1,-1,-1)`；`ECE` 的第一行、列非对角元全为一，其余五点的正号边恰组成循环 `(2,4,3,6,5)`。该循环的置换矩阵 `Pr` 保持 `ECE`，且 `M=EPrE`。

令 `omega=exp(2 pi i/3)`，并置

```math
q_k=(1,\omega^k,\omega^{2k}),\qquad
(a_0,b_0)=(-2,-1),\quad(a_1,b_1)=(a_2,b_2)=(1,2),
```

```math
t_k=\frac{1+ia_k}{\sqrt{1+a_k^2}},\qquad
 t_0=\frac{1-2i}{\sqrt5},\quad t_1=t_2=\frac{1+i}{\sqrt2}.
```

令 `F0` 的六行是

```math
f_{k,\varepsilon}=\frac1{\sqrt6}(q_k,\varepsilon t_kq_k),
\qquad k=0,1,2,\quad\varepsilon=\pm1.
```

不同 `k` 的正交来自三阶 Fourier 正交性；相同 `k` 的两行内积是 `(3-3)/6=0`。因此 `F0` unitary 且 flat。记 `Ac=I3-J3,Bc=2I3-J3`，有 `qk Ac=ak qk`、`qk Bc=bk qk`，故

```math
f_{k,\varepsilon}T_c
=\frac16\bigl((1+ia_k+\varepsilon ib_kt_k)q_k,
(ib_k+\varepsilon(1-ia_k)t_k)q_k\bigr).
```

由于 `ak²+bk²=5`，且

```math
(a_k-i)\overline{t_k}=-i\sqrt{1+a_k^2},
```

两个括号内系数的平方模均为六。因此 `F0 Tc` 也 flat。

现在置

```math
F=F_0MR,\qquad W=F^\dagger.
```

`F` 是 flat unitary，并且

```math
FT=F_0MRT=F_0MT_cK^\dagger=F_0T_cMK^\dagger
```

仍然 flat。故 `W` 确实是同时无偏于 `I,T` 的完整正交基。特别地，对第 8 节的同一个 `Q,D`，令 `U=FQ^dagger`，就同时保留

```math
U\text{ unitary},\qquad UQ=F\text{ flat},\qquad UDQ=FT\text{ flat}.
```

下面计算 affinity。`R` 与 `S` 交换，所以只需计算 `F0 M` 的行期望。写 `w=omega^k`、`t=epsilon tk`，其对应未归一化行是

```math
(1,w,w^2,t,tw,tw^2)M=(1,-t,tw^2,-w^2,w,tw).
```

利用 `|t|=|w|=1,w³=1`，该行与 `S` 的二次型为

```math
-\overline t-w+tw^2-w+\overline t-tw^2=-2w.
```

因而

```math
(FSF^\dagger)_{(k,\varepsilon),(k,\varepsilon)}=-\omega^k/3.
```

由第 16 节的同一归一化，

```math
\alpha_S(W)=\frac13\sum_{k,\varepsilon}
|(FSF^\dagger)_{(k,\varepsilon),(k,\varepsilon)}|^2
=\frac13\cdot6\cdot\frac19=\frac29.
```

三阶 Fourier 反演还给出每行的 mode probabilities 为 `(1/9,4/9,4/9)` 的置换，每种位置出现两次。作为独立的归一化核对，

```math
\sum_{r,k}p_{rk}^2=6\frac{1+16+16}{81}=\frac{22}{9},\qquad
\alpha_S(W)=\frac12\left(\frac{22}{9}-2\right)=\frac29.
```

命题得证。

### 44.3 排除 Fourier 固定边与修正目标的范围

对未归一化 Hadamard 矩阵定义交比集合

```math
\Lambda(G)=\{G_{ij}G_{k\ell}\overline{G_{i\ell}}\overline{G_{kj}}\}.
```

行列相位在交比中抵消，置换只重排指标，转置也不改变集合。由于 `H` 全部元素为四次单位根，其交比都在 `{1,-1,i,-i}` 中。另一方面，第 11 节 Fourier 两参数族的标准块代表包含完整的三阶 Fourier 子矩阵；其前两行、前两列的交比为 primitive cube root `omega`。转置族亦然。因此 `H` 与这两个 Fourier 族都不等价。本例是非 Fourier 双循环边，而不是 Fourier 中心的重述。

每个 completion 行的 collision 是 `11/27`，故任选三行都构成实际共同无偏正交三元组，但其总 collision 为 `11/9<2`。这阻止把第 36、37 节的三元组目标无条件推广到全部非 Fourier 双循环边；不反驳那两节针对 `-1/5` 固定种子的目标，也不影响第 42 节在该种子邻域上的结论。

按正负号排列 `F0` 的行后，它正是第 10、11 节的 Fourier 型块构造；`F=F0MR` 只再乘右单项式矩阵。因此这个低 affinity completion 仍是 Fourier 等价类的伴随，已由第 11 节的 quartet 文献归约排除。它说明“相对于指定 `S` 非 mode-local”不等于“已排除所有 Fourier-equivalent completions”：固定边自同构可以显著改变前一性质而保持后一等价类。

所以，若继续以 affinity 攻击剩余 quartet fibre，必须明确限制 completion 等价类，排除整个已知 Fourier locus 及其固定边自同构轨道；仅去掉 mode-local 子集不够。非零判别式内域、以及去除已知排除类后的剩余 completion 下界均未由本例解决。第 17、18、31 节的条件预算与刚性论证保持有效；六维四 MUB 问题也未由本例解决。

## 45. 实际互补 contexts 的交叉 pinching 与联合 affinity 缺口

第 31 节已经排除了 order-three symmetry 在两个互补 contexts 中的非平凡饱和分裂；第 32 节进一步给出近饱和定量界。本节保留实际互补基的等模重叠，改进其中的交叉项估计，得到更强的联合约束。这里不主张常数最优，也不假设单个 residual completion 的 affinity 下界。

### 45.1. 定义与结论

设 `d` 为正整数，`C,D` 是 `C^d` 的两个互相无偏正交基，`E_C,E_D` 是对应的 rank-one diagonal pinching。采用第 32 节的归一化：

```math
\tau(X)=\frac{\operatorname{Tr}(X)}d,\qquad
\langle X,Y\rangle_2=\tau(X^\dagger Y),\qquad
\|X\|_2^2=\tau(X^\dagger X).
```

令 `S` 为 `Tr(S)=0`、`S^3=I` 的 unitary，并置

```math
A=\mathsf E_C(S),\quad B=\mathsf E_D(S),\quad R=S-A-B,
\qquad a=\|A\|_2^2,\quad b=\|B\|_2^2,\quad r=\|R\|_2^2.
```

**命题 45.1。** 有 `a+b+r=1`，且

```math
\boxed{\sqrt a(1-a)\le4\sqrt{br}+2\sqrt d\,r,\qquad
\sqrt b(1-b)\le4\sqrt{ar}+2\sqrt d\,r.}
```

特别地，在六维令 `alpha=alpha_S(C)=2a`、`beta=alpha_S(D)=2b`，则

```math
\boxed{ab\le22r,\qquad
\alpha\beta\le44(2-\alpha-\beta).}
```

这两个乘积不等式在 `r>0` 时严格，并且总有

```math
\boxed{\min\{\alpha,\beta\}<\sqrt{2024}-44<\frac{989}{1000}.}
```

### 45.2. 交叉项与 order-three 恒等式

互相无偏性给出

```math
\mathsf E_C\mathsf E_D(X)=\mathsf E_D\mathsf E_C(X)=\tau(X)I.
```

故 `A,B` trace zero 且 Hilbert–Schmidt 正交，`E_C(R)=E_D(R)=0`，从而 `a+b+r=1`。`A,B` 分别在自己的基中对角，因此 normal。

在 `C` 基中，`B` 在互补的 `D` 基中对角，所以

```math
(BB^\dagger)_{ii}=(B^\dagger B)_{ii}=b.
```

也就是说，`B` 的每一行、每一列的 Euclidean norm 平方都恰为 `b`。逐行或逐列用 Cauchy–Schwarz，再求和除以 `d`，得到

```math
\|\mathsf E_C(BR)\|_2,\quad\|\mathsf E_C(RB)\|_2,\quad
\|\mathsf E_C(BR^\dagger)\|_2,\quad
\|\mathsf E_C(RB^\dagger)\|_2\le\sqrt{br}.
```

例如 `d^{-1} sum_i |(BR)_{ii}|^2 <= b d^{-1} sum_{i,j}|R_{ji}|^2=br`。这一步使用实际 MUB 重叠，而不只使用 `||B||op<=1`。

再令 `q_i=(RR^dagger)_{ii}>=0`。由 `sum_i q_i=dr` 可得

```math
\|\mathsf E_C(RR^\dagger)-rI\|_2^2
=\frac1d\sum_iq_i^2-r^2\le(d-1)r^2.
```

同时，pinching 的 Hilbert–Schmidt 收缩性与 `||R||op<=sqrt(d)||R||2` 给出

```math
\|\mathsf E_C(R^2)\|_2\le\|R^2\|_2
\le\|R\|_{\mathrm{op}}\|R\|_2\le\sqrt d\,r.
```

这里没有假定 `R` normal。投影 `SS^dagger=I`，利用 diagonal pinching 的 bimodule 性质消去含单个 `A` 的混合项，得

```math
H:=AA^\dagger-aI
=rI-\mathsf E_C(BR^\dagger+RB^\dagger+RR^\dagger),
\qquad \|H\|_2\le2\sqrt{br}+\sqrt{d-1}\,r.
```

又由 `S^2=S^dagger`，置

```math
\mu=\tau(B^2),\qquad J=\mathsf E_C(BR+RB+R^2),
\qquad f=2\sqrt{br}+\sqrt d\,r,
```

则

```math
A^2+\mu I+J=A^\dagger,\qquad
\|J\|_2\le f,\qquad\|H\|_2\le f.
```

令 `t=|mu|^2`、`u=||J||2`、`h=||H||2`。由 `A` normal 且 trace zero，

```math
\|A^2\|_2^2=a^2+h^2,\qquad
\|A^\dagger-\mu I\|_2^2=a+t.
```

展开 `A^2=(A^dagger-mu I)-J` 的平方范数并用 Cauchy–Schwarz，保留负的 `-u^2` 项，得到

```math
a(1-a)+t\le h^2-u^2+2\sqrt{a+t}\,u.
```

若 `a=0`，所求不等式成立。若 `a>0` 且 `f>sqrt(a)`，由 `a<=1` 得 `sqrt(a)(1-a)<=sqrt(a)<2f`。余下情形 `f<=sqrt(a)` 中，`0<=u<=f<=sqrt(a+t)`，因此

```math
h^2-u^2+2\sqrt{a+t}\,u\le2f\sqrt{a+t}.
```

这里用了 `f^2-u^2=(f-u)(f+u)<=2sqrt(a+t)(f-u)`。此外

```math
2f\bigl(\sqrt{a+t}-\sqrt a\bigr)
=\frac{2ft}{\sqrt{a+t}+\sqrt a}\le t.
```

消去 `t`，得 `a(1-a)<=2f sqrt(a)`；除以 `sqrt(a)>0` 即为第一条交叉 pinching 界。交换 `C,D` 得第二条。

### 45.3. 六维的多项式联合界

交换两基后可设 `a<=b`，于是 `a<=1/2`。把第一条交叉界乘以 `sqrt(a)`，用 `a(1-a)=ab+ar`，记 `p=ab`，得到

```math
p\le4\sqrt{pr}+(2\sqrt{6a}-a)r.
```

在 `0<=a<=1/2` 上，

```math
(a+3)^2-24a=a^2+9-18a>0.
```

确实，`a<1/2` 时 `9-18a>0`，端点 `a=1/2` 时右侧为 `1/4`。故 `2sqrt(6a)-a<3`，从而 `p<=4sqrt(pr)+3r`，且 `r>0` 时严格。另一方面，

```math
\tfrac12(\sqrt p-4\sqrt r)^2\ge0
\quad\Longrightarrow\quad
4\sqrt{pr}\le\tfrac12p+8r.
```

合并得 `p<=22r`，严格性保持。代入 `alpha=2a`、`beta=2b` 和 `2-alpha-beta=2r`，得到命题中的联合 affinity 乘积界。

令 `m=min(alpha,beta)`。若 `r=0`，乘积界给出 `alpha beta=0`，所以 `m=0`。若 `r>0`，则

```math
m^2\le\alpha\beta<88r\le88(1-m),
```

因此 `(m+44)^2<2024`，即 `m<sqrt(2024)-44`。最后

```math
\left(44+\frac{989}{1000}\right)^2-2024
=\frac{10121}{1000000}>0
```

给出所述有理数上界。命题得证。

### 45.4. 对实际 residual completion 的用途与范围

沿用第 16、44 节的行约定，要求 `T,F,FT,G,GT,FG^dagger` 全部是 flat unitary；额外两个基分别是 `F^dagger,G^dagger` 的列。固定 two-circulant 边的 simultaneous three-cycle symmetry `S` 满足 `Tr(S)=0`、`S^3=I`，且三个特征空间的秩均为二。实际 pinching 为

```math
\mathsf E_C(X)=F^\dagger\operatorname{diag}(FXF^\dagger)F,\qquad
\mathsf E_D(X)=G^\dagger\operatorname{diag}(GXG^\dagger)G.
```

这里 `diag` 保留对角元并把其余元素置零。`F,G` 的 unitarity 给出完整正交性，`FG^dagger` 的 flatness 给出两基互相无偏。第 16 节的实际 mode 恒等式给出

```math
a=\frac16\sum_i|(FSF^\dagger)_{ii}|^2=\frac{\alpha_S(C)}2,
\qquad b=\frac{\alpha_S(D)}2.
```

因此命题 45.1 对实际 quartet 的两个额外基成立，也对所有六条相对边均排除 Fourier 两种取向的 residual 子类成立。若在某个这样的 branch 上能证明每个 completion 都满足 `alpha_S>=sqrt(2024)-44`，特别是 `alpha_S>=989/1000`，便足以排除该 branch 中的 MUB pair。这把第 32 节的充分下界阈值 `2499/2500` 降低了。

本节没有证明这个单 completion 下界。`F,FT` 与 `G,GT` 的共同 flatness 仍是实际 completion 域的条件，但没有在本节进一步加强联合界。六条边的 Fourier 排除、以及剩余 fibre 的单 completion 几何，仍须另行处理；本节不推出六维 quartet 不存在。

## 46. 实参数支上共同无偏向量的退化 autocorrelation 排除

### 46.1 实参数种子与非退化结论

令 `-1<a<1`，并取正平方根：

```math
p=\frac{a-1}{2}+i\sqrt{1-\frac{(a-1)^2}{4}},\qquad
q=\frac{-a-1}{2}+i\sqrt{1-\frac{(a+1)^2}{4}}.
```

于是 `|p|=|q|=1`、`Re(p+q)=-1`。记 `S` 为三循环矩阵，约定其第一行为 `(0,1,0)`，`J` 为三阶全一矩阵，并令：

```math
A=\operatorname{circ}(1,p,1)=J+(p-1)S,\qquad
B=\operatorname{circ}(1,q,1)=J+(q-1)S,
\qquad
H=\frac1{\sqrt6}\begin{pmatrix}A&B\\B^*&-A^*\end{pmatrix}.
```

这里 `H` 始终表示归一化矩阵。此 block construction 是 Szöllősi 的已知构造，见 [*A two-parameter family of complex Hadamard matrices of order 6 induced by hypocycloids*，§2，式 (1)–(7)](https://arxiv.org/abs/0811.3930)，DOI `10.1090/S0002-9939-09-10102-8`。本节研究的是其实际共同无偏向量上的额外非退化结论。

取 `omega=exp(2 pi i/3)`，按 `S` 的特征值 `1,omega,omega²` 排列酉 Fourier 坐标。对两个三元单位相位向量 `x,y`，记其 Fourier 坐标为 `u,z`，并循环定义：

```math
c_k=\overline{u_k}u_{k+1},\qquad d_k=\overline{z_k}z_{k+1},\qquad
\Delta(x,y)=\det\begin{pmatrix}
c_0&c_1&c_2\\d_0&d_1&d_2\\1&1&1
\end{pmatrix}.
```

**命题 46.1。** 若 `H(x,y)^T` 的六个分量也都具有模一，则：

```math
\left(\prod_{k=0}^2u_kz_k\ne0\right)
\quad\Longrightarrow\quad \Delta(x,y)\ne0.
```

等价地，在这些实际共同平坦向量上，`Delta(x,y)=0` 必迫使 `x,y` 至少有一个是单一 Fourier mode。该命题适用于整个所述实参数区间。

**证明。** 首先，`AA*+BB*=6I`，因为其非对角相关系数为 `2+2 Re(p+q)=0`；circulant 矩阵交换又给出其余 block Gram 恒等式。因此 `H` 确为平坦酉矩阵。

反设 `u,z` 都有满支撑而 `Delta=0`。单位相位条件给出 `sum c_k=sum d_k=0`。两非零向量 `c,d` 位于二维零和子空间，退化行列式使它们成比例，故可写 `d=eta c`。令 `z_k=lambda_k u_k`，则：

```math
\overline{\lambda_k}\lambda_{k+1}=\eta.
```

三个相邻模长乘积相等，故三个 `|lambda_k|` 相等。由 `||u||²=||z||²=3`，公共模长是一。因此 `eta³=1`，存在同一个单位相位 `gamma` 及 `m in {0,1,2}`，使：

```math
z_k=\gamma\omega^{mk}u_k,\qquad y=\gamma S^m x.
\tag{46.1}
```

以下分别排除三种位移，始终保留同一相位 `gamma`。

### 46.2 实参数恒等式与非零循环位移

写 `p+q=-1+ih`，并令 `P=p-1`、`Q=q-1`。由 `p,q` 均在开第二象限，其辐角之差的绝对值小于 `pi/2`；故 `|p+q|²>2`，即 `h>1`。又 `|p+q|<=2`，所以 `h<=sqrt(3)`。直接由两个单位模条件及实部之和得到：

```math
pq=\frac{1-ih}{1+ih},\qquad
 a^2=\frac{h^2(3-h^2)}{1+h^2},\qquad
\operatorname{Re}(Q^2-P^2)=4a,
\qquad I_0:=\operatorname{Im}(P^2+Q^2)=-\frac{4h^3}{1+h^2}.
```

因此有严格不等式：

```math
I_0^2-4a^2
=\frac{4h^2(h^2-1)(5h^2+3)}{(1+h^2)^2}>0.
\tag{46.2}
```

`A,B` 未归一化的 mode 特征值分别为：

```math
a_0=2+p,\quad a_k=P\omega^k\ (k=1,2),\qquad
b_0=2+q,\quad b_k=Q\omega^k\ (k=1,2).
```

固定式 (46.1) 的 `m`，令：

```math
K_k=a_k+\gamma\omega^{mk}b_k,\qquad
L_k=\overline{b_k}-\gamma\omega^{mk}\overline{a_k}.
```

输出的两个 Fourier channel 为 `K_k u_k/sqrt(6)` 和 `L_k u_k/sqrt(6)`。它们与 `x` 的 constant-modulus 条件共同给出：

```math
\sum_kc_k=
\sum_k\overline{K_k}K_{k+1}c_k=
\sum_k\overline{L_k}L_{k+1}c_k=0.
```

由于 `c` 非零，三个方程的系数行列式必须为零。但对 `m=1,2`，其确切展开为：

```math
\det\begin{pmatrix}
1&1&1\\
\overline{K_0}K_1&\overline{K_1}K_2&\overline{K_2}K_0\\
\overline{L_0}L_1&\overline{L_1}L_2&\overline{L_2}L_0
\end{pmatrix}
=18\omega^m\left(a\frac pq\gamma^{-2}-iI_0-a\frac qp\gamma^2\right).
\tag{46.3}
```

式 (46.3) 可逐个 Laurent 系数展开得到：以 `conjugate(p)=1/p`、`conjugate(q)=1/q`、`conjugate(omega)=omega²` 代入，乘以 `p²q²gamma²` 后使用：

```math
\omega^2+\omega+1=0,\qquad
p^2q+pq^2+2pq+p+q=0.
```

其中两个奇次系数为零，其余三个系数即为式 (46.3) 右侧。由于 `p/q` 和 `gamma` 都有模一，若右侧为零，三角不等式就给出 `|I_0|<=2|a|`，与式 (46.2) 矛盾。两个非零循环位移均被排除。

### 46.3 零位移中的相位一致性与范数矛盾

现在令 `y=gamma x`，并记 `sigma=x_0+x_1+x_2`。满支撑保证 `sigma!=0`，且 `x` 不是常向量。未归一化的输出 channel 为：

```math
(P+\gamma Q)Sx+(1+\gamma)\sigma\mathbf1,
\qquad
(\overline Q-\gamma\overline P)S^2x+(1-\gamma)\sigma\mathbf1.
\tag{46.4}
```

若 `x` 的三个单位相位彼此不同，实线性泛函在这三个圆周点上取同一个值就必须为零。比较式 (46.4) 的分量平方模，因 `sigma!=0`，便有：

```math
(P+\gamma Q)(1+\overline\gamma)=0,\qquad
(\overline Q-\gamma\overline P)(1-\overline\gamma)=0.
```

`gamma=1` 或 `-1` 与 `P+Q=-3+ih!=0` 矛盾；其余情形使两个第一因子均为零，消去 `gamma` 得到 `-|P|²=|Q|²`，仍然矛盾。因此 `x` 恰有两个不同分量。乘以公共相位并作循环置换后可设 `x=(1,1,xi)`，其中 `|xi|=1`、`xi!=1`。

令：

```math
U=(P+\gamma Q)(1+\overline\gamma),\qquad
V=(\overline Q-\gamma\overline P)(1-\overline\gamma),\qquad
Z=\overline\sigma(1-\xi)\ne0.
```

两种分量平方模的差给出 `Re(UZ)=Re(VZ)=0`，从而 `Im(U conjugate(V))=0`。写 `gamma=cos(phi)+i sin(phi)`，展开得：

```math
\operatorname{Im}(U\overline V)
=2\sin\phi\bigl(I_0\sin\phi-4a\cos\phi\bigr).
\tag{46.5}
```

再记 `Z_1=Q conjugate(P)`、`Z_0=(2+q)(2+conjugate(p))`，则：

```math
\operatorname{Re}Z_0=\operatorname{Re}Z_1=\frac{h^2+3}{2},\qquad
\operatorname{Im}Z_1=\frac a2(h+3/h),\qquad
\operatorname{Im}Z_0=\frac a2(h-3/h).
\tag{46.6}
```

当 `gamma=±1` 时，`Re(gamma Z_0)` 和 `Re(gamma Z_1)` 同号且非零。式 (46.5) 的另一分支使：

```math
\gamma=\pm\frac{I_0+4ia}{\sqrt{I_0^2+16a^2}}.
```

利用实参数恒等式和式 (46.6)，此时两个实部的分子分别满足：

```math
I_0\operatorname{Re}Z_1-4a\operatorname{Im}Z_1
=-\frac{6h(h^2+3)}{1+h^2}<0,
```

```math
I_0\operatorname{Re}Z_0-4a\operatorname{Im}Z_0
=-\frac{18h(h^2-1)}{1+h^2}<0.
```

所以这两个实部仍同号且非零。另一方面：

```math
|K_0|^2=6+2\operatorname{Re}(\gamma Z_0),\qquad
|K_1|^2=|K_2|^2=6+2\operatorname{Re}(\gamma Z_1).
```

三个平方模必同时严格大于六，或同时严格小于六。由 `sum |u_k|²=3`，输出第一 channel 的平方范数：

```math
\frac16\sum_k|K_ku_k|^2
```

便不能等于三。这与其三个分量均有模一矛盾，排除了最后一个位移。

因此满支撑时必有 `Delta!=0`。最后，三元单位相位向量若有一个 Fourier 分量为零，便有三个单位复数之和为零；它们必构成等边三角形。在三个位置上，这些相位只能按两个循环方向排列，所以原向量为单一 Fourier mode。这也证明了命题中的等价表述。证毕。

### 46.4 实际列基方向与第 33 节的适用结论

**推论 46.2。** 保持命题 46.1 的归一化 `H`。令 `L` 为分块循环行置换，并置 `H_0=LH`。若归一化向量 `v` 共同无偏于实际列基 `(I,H_0)`，设：

```math
w=H_0^*v,\qquad \binom{x}{y}=\sqrt6\,w.
```

则 `x,y` 都是单位相位向量，且：

```math
H\binom{x}{y}=\sqrt6\,L^*v
```

也逐项有模一。因此，只要 `w` 的两个 channel Fourier transforms 均有满支撑，第 33 节的输出侧行列式就满足 `Delta(w)!=0`。特别地，这适用于第 35 节使用的行置换 indices `(2,0,1,4,5,3)`。

继续假设 `w` 的两个 channel Fourier transforms 均有满支撑。若另一实际共同无偏向量 `v'` 与 `v` **逐模正交**，则令 `w'=H_0^*v'` 后，第 33 节的 conditional partner theorem 给出：`w'` 是 mode-local，或 `w'~R^m Theta w`。返回原坐标，即：

```math
v'\text{ 是 mode-local},\qquad\text{或}\qquad
v'\sim H_0R^m\Theta H_0^*v
\quad(m\in\mathbb Z_3).
```

**证明。** 共同无偏的定义保证 `v` 与 `H_0*v` 的每个分量均有模 `1/sqrt(6)`，上述缩放恒等式直接给出命题 46.1 的两个实际平坦条件。缩放使 `Delta` 乘以非零因子，故非零性不变。`L` 为分块循环置换，而 `H` 为两 circulant block 矩阵，所以 `H_0` 保持每个二维 mode 子空间，并在其上酉作用；故它保持逐模正交和 mode-local 性质。对 `w,w'` 应用第 33 节，再以 `H_0` 传回即可。证毕。

此推论不把输入侧 `Delta(v)` 与输出侧 `Delta(H_0*v)` 视为同一个量，也不将全局正交替换为逐模正交。命题 46.1 留下的退化情形，是至少一个 channel 为单一 Fourier mode；它未断言另一个 channel 也为单一 mode。这一排除结论本身尚不给出实际 completion 的 affinity 下界。

## 47. 实参数支的常值 channel 纤维与两个例外参数

### 47.1 常值第一 channel 的精确分类

沿用第 46 节的 `a,p,q,H,S`，令 `L=diag(S²,S)`、`H_0=LH`，并记 `P=p-1`、`Q=q-1`、`A_0=2+p`、`B_0=2+q`。于是：

```math
\sqrt6 H_0=\begin{pmatrix}
J+PI&J+QI\\J+\overline QI&-J-\overline PI
\end{pmatrix}.
```

这里仍使用第 46 节所引的 Szöllősi block construction；本节分类其实际共同平坦方程中第一 channel 为常值的纤维。

**命题 47.1。** 固定 `-1<a<1`。对单位相位向量 `x,y`，要求 `x` 为常值且 `H(x,y)^T` 逐项有模一。以公共相位把 `x` 归一为 `(1,1,1)` 后，所有可能的 `y` 恰为：

1. 对每个参数都有的两个常值向量 `y=gamma(1,1,1)`，其中：

   ```math
   |\gamma|=1,\qquad \operatorname{Re}(\overline{A_0}B_0\gamma)=0.
   ```

2. 仅在以下两个参数出现的三个额外非恒定向量：

   ```math
   a=\pm\sqrt{\frac{37-\sqrt{73}}{72}}.
   \tag{47.1}
   ```

   此时置：

   ```math
   s=\frac{11+\sqrt{73}}8,\quad h=\sqrt s,\quad
   t=\frac{2a^2}{3},\quad
   \eta=-\frac{a(5s-3)}{6h(2s-3)},
   ```

   ```math
   d=\eta h-i\left(\frac{a\eta(s+1)}s+\frac{3t}{2h}\right),\qquad
   m=d\left(\frac12+i\frac\eta t\right),\qquad
   \alpha=m+d,\quad\beta=m-2d.
   \tag{47.2}
   ```

   三个额外向量是 `(alpha,alpha,beta)` 的三个不同置换。

因此，第一 channel 为常值的 projective 纤维通常恰有两个点，在式 (47.1) 的两个参数处恰有五个点。三个额外点的第二 channel 均有完整的三模 Fourier 支撑。

**证明。** 由于 `L` 只置换行，输出逐项模一对 `H` 与 `H_0` 等价。设 `sigma=sum y_j`，则两个未归一化输出 channel 为：

```math
(A_0+\sigma)\mathbf1+Qy,\qquad
(\overline{B_0}-\sigma)\mathbf1-\overline Py.
```

若 `y` 有三个不同的单位相位，两个输出 channel 各自等模迫使对应实线性泛函为零。`P,Q` 非零，故：

```math
\sigma=-A_0,\qquad \sigma=\overline{B_0}.
```

这与 `Re(A_0+conjugate(B_0))=3` 矛盾。若 `y` 为常值，输出条件就是命题第一项；`A_0B_0!=0`，所以恰有两个相反的相位解。

非恒定情形中，`y` 必恰有两个不同分量。`H_0` 与同步坐标置换交换，所以可写：

```math
y=(m+d,m+d,m-2d),\qquad d\ne0.
```

记 `t=|d|²`、`eta=Im(m conjugate(d))`。输入分量模一等价于：

```math
\operatorname{Re}(m\overline d)=t/2,\qquad
|m|^2+2t=1,\qquad \eta^2=t-\frac94t^2.
\tag{47.3}
```

像第 46 节那样写 `p+q=-1+ih`，则：

```math
1<h\le\sqrt3,\qquad
p=\frac{a-1+i(h+a/h)}2,\quad
q=\frac{-a-1+i(h-a/h)}2,\qquad
 a^2=\frac{h^2(3-h^2)}{1+h^2}.
\tag{47.4}
```

两个输出 channel 的等模条件为：

```math
\operatorname{Re}\bigl(\overline Q(A_0+3m)\overline d\bigr)=0,
\qquad
\operatorname{Re}\bigl(P(3m-\overline{B_0})\overline d\bigr)=0.
\tag{47.5}
```

写 `d=X+iY`，代入 `m conjugate(d)=t/2+i eta`，解这个实二元线性系统得到：

```math
X=\eta h,\qquad
Y=-\frac{a\eta(1+h^2)}{h^2}-\frac{3t}{2h}.
\tag{47.6}
```

这里没有除以可能为零的参数：未约分的分母所含因子满足：

```math
a^2h^2-a^2+h^4-9h^2=-\frac{4h^2(h^2+3)}{1+h^2}<0.
```

令 `N=A_0+B_0m`，第一输出 channel 的范数条件为 `|N|²+2|Q|²t=6`，亦即：

```math
\operatorname{Re}(\overline{A_0}B_0m)=-3at.
\tag{47.7}
```

把式 (47.6) 代入 `|d|²=t` 和式 (47.7)，再用式 (47.3)–(47.4)，由于 `t>0`，得到：

```math
9h(1+h^2)t-6a(1+h^2)\eta-2h(h^2+3)=0,
```

```math
9a(1+h^2)t-6h^3\eta-a(7h^2+3)=0.
\tag{47.8}
```

具体地，`|d|²-t` 的展开余项是第一个左侧乘以 `-t/(2h³)`；式 (47.7) 左侧移项后乘以 `t`，展开余项是第二个左侧乘以 `-t/(2h²)`。

若 `2h²=3`，消去式 (47.8) 中的 `t` 就给出 `a(5h²-3)=0`，与式 (47.4) 矛盾。否则唯一解为：

```math
\eta=-\frac{a(5h^2-3)}{6h(2h^2-3)},\qquad
 t=\frac{3h^4-4h^2-3}{3(1+h^2)(2h^2-3)}.
\tag{47.9}
```

此时式 (47.3) 中最后一个条件的余项恰为：

```math
\eta^2-t+\frac94t^2
=-\frac{h^2(h^2+3)(4h^4-11h^2+3)}{9(1+h^2)^2(2h^2-3)^2}.
```

故 `4h⁴-11h²+3=0`。二次多项式 `4s²-11s+3` 的两个根中，只有 `s=(11+sqrt(73))/8` 落在 `(1,3]`。式 (47.4) 随即给出式 (47.1)，而 `t=(37-sqrt(73))/108=2a²/3`。式 (47.6) 和 (47.9) 唯一确定 `d`，再由 `m=d(1/2+i eta/t)` 唯一确定 `m`。这证明非恒定解至多是命题中三个置换。

反过来，对式 (47.1) 的任一符号，式 (47.2) 满足：

```math
4s^2-11s+3=0,\quad 9a^2+s-6=0,\quad
|d|^2=t,\quad \eta^2=t-\frac94t^2,\quad |m|^2=1-2t.
```

因此 `|alpha|=|beta|=1`。式 (47.5) 保证两个输出 channel 各自等模；式 (47.7) 保证第一个归一化输出 channel 的平方范数为三，酉性又使第二个的平方范数为三。故两个 channel 均逐项模一，三个置换都可达。由于 `t>0`、`t<1/2`，`d,m` 均非零，故三个置换彼此不同，且其第二 channel 的 Fourier 分量模为 `sqrt(3)|m|,sqrt(3)|d|,sqrt(3)|d|`，全部非零。证毕。

### 47.2 例外射线的精确正交图

**推论 47.2。** 固定式 (47.1) 的任一参数，令 `y_j` 为命题 47.1 的三个非恒定向量，并置：

```math
v_j=\frac1{\sqrt6}(\mathbf1,y_j),\qquad
w_j=\Theta_0v_j=\frac1{\sqrt6}(-\overline{y_j},\mathbf1),
\qquad \Theta_0(x,y)=(-\overline y,\overline x).
```

这六条实际共同无偏射线的诱导正交图恰为 `K_{3,3}`。加入六条 canonical mode-local 射线后，十二条射线的诱导正交图恰为不相交并 `K_6 ⊔ K_{3,3}`。

**证明。** 第 35 节的反酉恒等式在此 `I+J` block 形式中为 `H_0 Theta_0=-Theta_0 H_0`，所以 `v_j,w_j` 均共同无偏于实际列基对 `(I,H_0*)`。两个不同位置的 `(1,1,-2)` 型向量内积为 `-3`，故当 `j!=k` 时：

```math
\langle y_j,y_k\rangle=3|m|^2-3t=3-9t,\qquad
\langle v_j,v_k\rangle=1-\frac32t=1-a^2>0.
```

`w_j,w_k` 的内积是其共轭，也非零。又 `sum y_j=3m` 与 `j` 无关，所以所有交叉内积都为零：

```math
\langle v_j,w_k\rangle
=\frac{\overline{\sum y_j}-\overline{\sum y_k}}6=0.
```

这就给出六个不同顶点的 `K_{3,3}`，特别是其中没有正交三角形。

为核对与 canonical 射线的关系，令 `f_l` 为逐项模一的第 `l` 个 Fourier mode，`A_l,B_l` 为归一化 `H_0` 的相应 mode entries，取两个相反相位 `gamma_l^±` 满足 `Re(conjugate(A_l)B_l gamma_l^±)=0`。这里 `A_lB_l!=0`。六条 canonical 射线为：

```math
c_l^\pm=\frac1{\sqrt6}(f_l,\gamma_l^\pm f_l),\qquad l=0,1,2.
```

它们在同一 mode 内成正交对，不同 mode 之间也正交，故给出 `K_6`。对 `l=0`：

```math
\langle v_j,c_0^\pm\rangle=\frac{1+\gamma_0^\pm\overline m}{2},\qquad
\langle w_j,c_0^\pm\rangle=\frac{\gamma_0^\pm-m}{2},
```

因 `|m|<1` 均非零。对 `l=1,2`，`v_j` 的第一 channel 与 `f_l` 正交，但第二 channel 的对应 Fourier 分量非零，所以 `v_j` 与 `c_l^±` 不正交；`w_j` 则由共轭 Fourier 分量得到同样结论。因此两个子图之间没有边。证毕。

### 47.3 基方向与结论范围

对三个额外非恒定点，`(x,y)/sqrt(6)` 共同无偏于 `(I,H*)`。在第 46 节的实际列基方向 `(I,H_0)` 中，应使用 `v=H_0(x,y)^T/sqrt(6)`，于是 `H_0*v=(x,y)^T/sqrt(6)`。其输出侧 `Delta` 为零，而六维向量的总 mode 支撑仍是完整的。因此第 46 节的“两条 channel 均满支撑”不能弱化为“向量不是 mode-local”。对推论 47.2 的全部射线同时乘以 `H_0`，所有内积和图结论保持。

命题 47.1 只分类第一 channel 为零 Fourier mode 的纤维；它没有分类第一 channel 为另外两个单模的情形，也没有分类两条 channel 都满支撑的情形。推论 47.2 只给出这十二条显式射线的诱导图，不排除它们与其余共同无偏射线之间的边，因而尚不排除由其他射线参与的 completion 或 quartet。

## 48. 实参数支上完整的零自相关行列式层

### 48.1 非零单模 channel 的刚性

沿用第 46–47 节的实参数 `-1<a<1`、`p,q,H,H_0`，其中 `H_0=diag(S²,S)H`。写 `p+q=-1+ih`、`s=h²`，并记 `P=p-1`、`Q=q-1`。则：

```math
1<s\le3,\qquad a^2=\frac{s(3-s)}{1+s},\qquad
P=\frac{a-3+i(h+a/h)}2,\quad Q=\frac{-a-3+i(h-a/h)}2.
```

令 `omega=exp(2 pi i/3)`、`f_l=(1,omega^l,omega^{2l})`。单位相位向量 `x,y` 的酉 Fourier 坐标分别记为 `u,z`，即 `x=sum_l u_l f_l/sqrt(3)`，`y=sum_l z_l f_l/sqrt(3)`。本节继续采用 Szöllősi 的 paired-circulant construction；所分类的是该实参数支的实际共同平坦方程。

**命题 48.1。** 若 `x,y` 逐项有模一，`H(x,y)^T` 也逐项有模一，且 `x` 只支撑于 Fourier mode `1` 或 `2`，则 `y` 必支撑于同一个 mode。

**证明。** 因 `H_0` 与同步坐标置换交换，反射置换交换 modes `1,2`，故只需处理第一个。用公共相位归一化 `x=f_1`，于是 `u_1=sqrt(3)`、其余 `u_l=0`。

单位相位三元组的 Fourier 支撑只能是单模或完整三模：若一个 Fourier 分量为零，对应三个单位复数之和为零，它们必组成等边三角形，从而原三元组为某个单模。若 `y` 是不同于 `1` 的单模，则第一个输出 channel 有且仅有两个非零 Fourier 分量，与上述支撑性质矛盾。这里涉及的 mode entries 都非零：`P,Q,2+p,2+q` 均非零。

剩下只需排除 `z_0 z_1 z_2!=0`。令：

```math
\zeta=\frac{z_2}{\overline{z_0}},\qquad r=|\zeta|^2>0.
```

`H_0(x,y)^T` 的两个 Fourier channel 在除以 `sqrt(6)` 前分别为：

```math
\bigl((2+q)z_0,\ P\sqrt3+Qz_1,\ Qz_2\bigr),
```

```math
\bigl(-\overline{(2+p)}z_0,\ \overline Q\sqrt3-\overline Pz_1,
-\overline Pz_2\bigr).
```

令 `X=conjugate(z_0)z_1`、`Y=conjugate(z_2)z_0`。从两个输出 channel 的循环自相关方程中分别减去 `|Q|²`、`|P|²` 倍的输入自相关方程，得到：

```math
QX+\overline QY
=-\frac{P\overline{(2+q)}\overline{z_0}+\overline P Qz_2}{\sqrt3},
```

```math
\overline PX+PY
=\frac{(2+p)\overline Q\overline{z_0}+Q\overline Pz_2}{\sqrt3}.
\tag{48.1}
```

该系统的行列式 `QP-conjugate(QP)` 非零，因为：

```math
\operatorname{Im}(PQ)=-\frac{h(s+3)}{1+s}<0.
```

解得：

```math
\sqrt3z_1=A+B\zeta,\qquad
\sqrt3\overline{z_2}z_0=(C+D\zeta)\overline{z_0},
\tag{48.2}
```

其中本证明内的标量 `A,B,C,D` 为：

```math
A=\frac{a(5s^2+2s-3)+ih(5s^2-12s-9)}{2s(s+3)},\qquad
B=-\frac{a(s+1)-ih(s+3)}{2s},
```

```math
C=-\frac{a(s^2+4s+3)+ih(s^2-12s-9)}{2s(s+3)},\qquad
D=\frac{a(s+1)-ihs}{s}.
```

输入自相关、输入范数和第一个输出 channel 的范数分别给出：

```math
A+C+(B+\overline A+D)\zeta+\overline Br=0,
\tag{48.3}
```

```math
|C+D\zeta|^2(1+r)+|A+B\zeta|^2r-9r=0,
\tag{48.4}
```

```math
2\operatorname{Re}\bigl(\overline P Q(A+B\zeta)\bigr)r
-a|C+D\zeta|^2=0.
\tag{48.5}
```

具体地，式 (48.2) 给出 `|z_0|²=|C+D zeta|²/(3r)`，而输入平方范数为三。第一个输出 channel 的平方范数条件是 `2 Re(conjugate(P)Q sqrt(3)z_1)=3a|z_0|²`。因此三式保留的是同一个实际 `y` 和同一个 `zeta`，没有独立放松各个相位。

若 `a=0`，则 `s=3`、`p=q=omega`，以及：

```math
A=0,\qquad B=i\sqrt3,\qquad C=i\sqrt3,\qquad D=-i\sqrt3.
```

式 (48.3) 给出 `r=1`，式 (48.4) 给出 `|1-zeta|²=1`，故 `Re(zeta)=1/2`。因 `conjugate(P)Q=3`，式 (48.5) 又迫使 `Im(zeta)=0`，与 `|zeta|²=1` 矛盾。

现设 `a!=0`，故 `1<s<3`。式 (48.3) 中 `zeta` 的系数是非零数：

```math
B+\overline A+D
=\frac{3(s+1)[ah+i(3-s)]}{h(s+3)}.
```

解得：

```math
\operatorname{Re}\zeta
=\frac{(2s^2+9s+9)r-8s^2+6s}{6(2s+3)},
```

```math
\operatorname{Im}\zeta
=-\frac{a[(2s^3+7s^2-9)r-8s^3+14s^2-18]}{6h(s-3)(2s+3)}.
\tag{48.6}
```

定义：

```math
F(s,r)=(s+3)^2(2s+3)r^2+(5s^3-48s^2-99s-54)r
+20s^3-21s^2-18s+27.
```

将式 (48.6) 代入 `|zeta|²=r` 后，余项恰为：

```math
|\zeta|^2-r=-\frac{F(s,r)}{9(s-3)(s+1)(2s+3)}.
```

因此 `F(s,r)=0`。再将式 (48.6) 代入式 (48.4)、(48.5) 的左侧，各乘以共同的非零分母：

```math
9s(s-3)(s+1)(s+3)^2(2s+3),
```

并在变量 `r` 上对 `F` 取多项式余式，依次得到：

```math
-27s(s-3)(s+1)\,[K(s)r-L(s)],\qquad
9a(s+1)\,[J(s)r-M(s)],
\tag{48.7}
```

其中：

```math
K(s)=(s+3)^2(s+6),\qquad L(s)=16s^3+30s^2+72s+54,
```

```math
J(s)=(s+3)^2(2s+3)(2s^2+3s+9),\qquad
M(s)=28s^5+207s^4-108s^3-918s^2-324s+243.
```

这里仅使用 `h²=s` 与 `a²=s(3-s)/(1+s)`。式 (48.7) 中消去的因子均非零，故必须同时有 `Kr=L` 与 `Jr=M`。然而：

```math
JL-KM=9s(s+3)^3(4s^4-19s^3+51s^2+279s+189)>0.
\tag{48.8}
```

最后的不等式来自 `s>0` 及：

```math
4s^4-19s^3+51s^2+279s+189
=s^2(4s^2-19s+51)+279s+189>0,
```

其中二次式 `4s²-19s+51` 首项系数为正、判别式为 `-455`。这与 `Kr=L`、`Jr=M` 矛盾，完成全部情形。证毕。

### 48.2 完整的零行列式层及 completion 的必要条件

对上述实际单位相位向量，定义循环自相关行：

```math
c_k=\overline{u_k}u_{k+1},\qquad
d_k=\overline{z_k}z_{k+1},\qquad k\in\mathbb Z/3\mathbb Z,
\qquad
\Delta(x,y)=\det\begin{pmatrix}c_0&c_1&c_2\\d_0&d_1&d_2\\1&1&1\end{pmatrix}.
```

**推论 48.2。** 固定 `-1<a<1`。实际共同平坦射线中 `Delta=0` 的全部解恰为六条 canonical mode-local 射线；仅当：

```math
a=\pm\sqrt{\frac{37-\sqrt{73}}{72}}
```

时，还包括第 47 节的六条额外射线。因此完整零行列式层的正交图通常为 `K_6`，在这两个参数处恰为 `K_6 ⊔ K_{3,3}`。

任一不同于 canonical mode-local 基的正交 completion 至少包含三条 `Delta!=0` 射线。若它使用了上述任一额外零行列式射线，则至少包含四条 `Delta!=0` 射线。

**证明。** 每个输入 channel 的 Fourier 支撑只能是完整三模或单模。第 46 节排除两个 channel 均满支撑时的 `Delta=0`。第一 channel 为零模时，命题 47.1 给出全部解；第一 channel 为另外两个单模时，命题 48.1 说明两个 channel 必在同一 mode，故只能是 canonical 射线。

若只有第二 channel 为单模，则应用第 35、47 节的反酉对称 `Theta_0(x,y)=(-conjugate(y),conjugate(x))`。它交换 channel 并保持实际共同平坦条件；此情形中的非 canonical 解恰为常值第一 channel 的三个例外点的 Theta_0 像，与前一种情形合起来正好是第 47 节的六条额外射线。反过来，每条列出的射线都有一个自相关行为零，故确实满足 `Delta=0`。完整图即推论 47.2 已计算的图。

完全落在该层中的六射线正交基只能是 canonical `K_6`。因此非 canonical completion 必包含一条 `Delta!=0` 射线。该射线在三个 rank-two mode 子空间中均有非零投影，所以不可能同时正交于某一 mode 中的两条 canonical 射线。一个含此射线的 completion 至多使用三条 canonical 射线。若 completion 没有额外零行列式射线，就至少有三条非零行列式射线。

若 completion 含有一条额外零行列式射线，则根据两个子图间没有边的事实，它不能包含任何 canonical 射线。又 `K_{3,3}` 的团数为二，所以它至多使用两条额外零行列式射线，从而至少有四条非零行列式射线。这也蕴含一般的三条下界。证毕。

在实际列基方向 `(I,H_0)` 中，对每条共同无偏单位射线 `v` 应把上述 `Delta` 施于单位相位坐标 `sqrt(6)H_0*v` 的两个 channel。对所有射线同时作这一酉基变换并恢复共同归一化，内积及正交图不变，故以上分类和计数原样适用。`Delta!=0` 亦强迫两个 channel 都满支撑。

本节把非 canonical completion 的剩余问题限制到至少三条实际满 channel 支撑射线的正交兼容性。它不把全局正交替换为第 33 节所要求的逐模正交，也没有分类 `Delta!=0` 的全部射线、建立 affinity 下界或排除 quartet。

## 49. 实参数支上 canonical 射线的显式隔离半径

### 49.1 实际相位 Jacobian 与射线间距

沿用第 46–48 节的归一化矩阵 `H_0` 和参数 `-1<a<1`。令 `omega=exp(2 pi i/3)`、`f_l=(1,omega^l,omega^{2l})`，故 `f_l` 逐项模一、范数为 `sqrt(3)`。写 `s=h²`、`P=p-1`、`Q=q-1`、`A=2+p`、`B=2+q`。`sqrt(6)H_0` 的三个 Fourier blocks 是：

```math
T_0=\begin{pmatrix}A&B\\\overline B&-\overline A\end{pmatrix},
\qquad
T_1=T_2=\begin{pmatrix}P&Q\\\overline Q&-\overline P\end{pmatrix}.
```

记 `(a_0,b_0)=(A,B)`、`(a_1,b_1)=(a_2,b_2)=(P,Q)`，并置：

```math
n_l=|a_l|^2,\qquad m_l=|b_l|^2,\qquad k_l=\sqrt{n_lm_l}>0.
```

于是 `(n_0,m_0)=(3+2a,3-2a)`，另两个 mode 均为 `(3-a,3+a)`。六个 canonical 单位相位代表是：

```math
z_{l,\varepsilon}=(f_l,g_{l,\varepsilon}f_l),\qquad
 g_{l,\varepsilon}=\frac{\varepsilon i a_l\overline{b_l}}{k_l},
\qquad \varepsilon\in\{1,-1\}.
```

**命题 49.1。** 设 `a!=0`。对任一 canonical 单位射线 `c=z_{l,epsilon}/sqrt(6)`，以及与其不同的、共同无偏于 `(I,H_0*)` 的单位射线 `v`，有：

```math
\min_{|\lambda|=1}\|v-\lambda c\|_2\ge\frac{|a|}{80}.
\tag{49.1}
```

同一结论经公共酉变换 `H_0` 后适用于实际列基对 `(I,H_0)`。常数不声称最优。

一般的非退化相位 Jacobian 所给出的局部唯一性可见 Jaming–Matolcsi–Móra–Szöllősi–Weiner，[arXiv:0902.0882v2，Theorem 4.1 与 Corollary 4.2](https://arxiv.org/abs/0902.0882v2)。这里计算该实参数支的实际 Jacobian，并直接给出式 (49.1) 的统一定量半径。

**证明。** 固定 `l,epsilon`，简记 `g=g_{l,epsilon}`，定义实际残差映射：

```math
R(\theta)=\left|H_0\bigl(z_{l,\varepsilon}\odot e^{i\theta}\bigr)\right|^2-\mathbf1,
\qquad \theta\in\mathbb R^6.
```

绝对值、平方和指数均逐项作用。每个实相位 channel 都唯一写为：

```math
\theta_x(j)=t_x+\xi\omega^j+\overline\xi\omega^{-j},\qquad
\theta_y(j)=t_y+\eta\omega^j+\overline\eta\omega^{-j}.
```

公共相位不改变 `R`。在均值零的五维子空间中 `t_x+t_y=0`。置 `d=t_y-t_x`、`w=(xi,eta)`，有：

```math
\|\theta\|_2^2=\frac32d^2+6\|w\|_2^2.
\tag{49.2}
```

令 `U=a_l+b_lg`、`V=conjugate(b_l)-conjugate(a_l)g`，则 `|U|²=|V|²=6`。下标按三循环取值，并记 `(a_+,b_+)=(a_{l+1},b_{l+1})`、`(a_-,b_-)=(a_{l-1},b_{l-1})`。两个输出残差中 `omega^j` 的系数，其导数为 `(i/6)Mw`，其中：

```math
M_{11}=\overline U a_+-U\overline{a_-},\qquad
M_{12}=\overline U b_+g-U\overline{b_-}\overline g,
```

```math
M_{21}=\overline V\overline{b_+}-Vb_-,\qquad
M_{22}=-\overline V\overline{a_+}g+Va_-\overline g.
\tag{49.3}
```

两个零频率导数分别为 `-epsilon k_l d/3` 与其相反数。于是实际 Jacobian `J=DR(0)` 满足：

```math
\|J\theta\|_2^2=\frac{2k_l^2}{3}d^2+\frac16\|Mw\|_2^2.
\tag{49.4}
```

这保留了全部五个去公共相位方向；第六个残差只由总范数守恒消去。

以下给出 `M` 的精确行列式。为展开方便，暂记 `alpha=a_l`、`beta=b_l`、`n=|alpha|²`、`m=|beta|²`、`k=sqrt(nm)`。代入 `g=epsilon i alpha conjugate(beta)/k`，得到 `M=M_0+(epsilon/k)M_1`，其中：

```math
M_0=\begin{pmatrix}
\overline\alpha a_+-\alpha\overline{a_-}&\overline\beta b_+-\beta\overline{b_-}\\
\beta\overline{b_+}-\overline\beta b_-&\alpha\overline{a_+}-\overline\alpha a_-
\end{pmatrix},
```

```math
M_1=\begin{pmatrix}
-im(\overline\alpha a_++\alpha\overline{a_-})&in(\overline\beta b_++\beta\overline{b_-})\\
in(\beta\overline{b_+}+\overline\beta b_-)&-im(\alpha\overline{a_+}+\overline\alpha a_-)
\end{pmatrix}.
```

在 `det(M_0+(epsilon/k)M_1)` 中，一次交叉项：

```math
(M_0)_{11}(M_1)_{22}+(M_1)_{11}(M_0)_{22}
-(M_0)_{12}(M_1)_{21}-(M_1)_{12}(M_0)_{21}
```

恒为零。将 `p=(a-1+i(h+a/h))/2`、`q=(-a-1+i(h-a/h))/2` 和 `a²=s(3-s)/(1+s)` 代入剩余的 `det M_0+det M_1/(nm)`，化简得：

```math
l=0:\quad\det M=\frac{72a(s+3)^2}{4s^2-3s+9},
\qquad
l=1:\quad\det M=-36a.
\tag{49.5}
```

mode `2` 由同步反射 `j -> -j` 得到相同的奇异值。因此去公共相位的实际 Jacobian 恰在 `a!=0` 时可逆；`a=0` 时式 (49.5) 为零。第一分母是 `(1+s)(9-4a²)>0`，而：

```math
\frac{(s+3)^2}{4s^2-3s+9}\ge1
```

来自 `3s(3-s)>=0`。所以三个 mode 都有 `|det M|>=36|a|`。

每个 `sqrt(6)H_0` 的 mode coefficient 的模不超过 `sqrt(5)`，故式 (49.3) 的每个矩阵元的模不超过 `2sqrt(30)`。于是：

```math
\|M\|_{op}\le\|M\|_F\le4\sqrt{30}<24,
\qquad \sigma_{\min}(M)\ge\frac{36|a|}{24}=\frac32|a|.
```

均值方向的奇异值为 `2k_l/3>1`；由式 (49.2)–(49.4)，其余四个实方向的最小奇异值为 `sigma_min(M)/6`。因此在均值零子空间上：

```math
\|J\theta\|_2\ge\frac{|a|}{4}\|\theta\|_2.
\tag{49.6}
```

为控制真实非线性残差，令 `Z(t)=H_0(z_{l,epsilon} odot exp(i t theta))`。酉性给出：

```math
\|Z(t)\|_2=\sqrt6,\quad
\|Z'(t)\|_2=\|\theta\|_2,\quad
\|Z''(t)\|_2=\|\theta\odot\theta\|_2\le\|\theta\|_2^2.
```

逐项平方模的二阶导数是 `2|Z'|²+2 Re(conjugate(Z) odot Z'')`，所以对所有 `t`：

```math
\left\|\frac{d^2}{dt^2}R(t\theta)\right\|_2
\le2(1+\sqrt6)\|\theta\|_2^2<8\|\theta\|_2^2.
```

积分形式的 Taylor 公式遂给出：

```math
\|R(\theta)-R(0)-J\theta\|_2\le4\|\theta\|_2^2.
\tag{49.7}
```

若 `theta` 均值为零、非零且 `R(theta)=R(0)=0`，式 (49.6)–(49.7) 强迫 `||theta||_2>=|a|/16`。

最后令 `z=sqrt(6)v`，选公共相位使 `rho=||z-z_{l,epsilon}||_2` 最小，并取主值相位差 `beta_j in [-pi,pi]`。弧弦不等式给出：

```math
|\beta_j|\le\frac\pi2|e^{i\beta_j}-1|\le2|e^{i\beta_j}-1|,
\qquad\|\beta\|_2\le2\rho.
```

减去 `beta` 的均值所得 `theta` 满足 `||theta||<=||beta||`，且只改变 `z` 的公共相位，故仍有 `R(theta)=0`。因两射线不同，`theta!=0`。因此 `rho>=|a|/32`，除以 `sqrt(6)<5/2` 即得式 (49.1)。证毕。

### 49.2 完整 completion 的定量分离

**推论 49.2。** 设 `a!=0`，`C` 为实际列基对 `(I,H_0)` 的非 canonical unitary completion，`C_can` 为同一参数的 canonical completion。对全部 unitary monomial 矩阵 `M` 取下确界，有：

```math
\inf_M\|C-C_{can}M\|_F\ge\frac{\sqrt3\,|a|}{80}.
\tag{49.8}
```

若 `C` 含有第 47 节的一条例外零行列式射线，则右侧可加强为 `sqrt(6)|a|/80`。

**证明。** 第 48 节保证非 canonical completion 至少含三条非 canonical 射线。无论如何指定列置换和各列相位，这三列与分配给它们的 canonical 列之间的距离都至少为 `|a|/80`。平方求和再开方，得到式 (49.8)。若含例外射线，由第 47 节两个子图间没有边，`C` 不能含任何 canonical 列，因而六列都可使用同一距离下界。证毕。

式 (49.8) 排除 canonical completion 周围的明确邻域，但没有排除更远的 completion。该界在 `a=0` 退化；它既不控制两条非 canonical 射线之间的距离，也不建立 affinity 下界或排除三条满 channel 支撑射线的正交兼容性。

## 50. 实参数支上两条 canonical 射线的共同正交刚性

本节沿用第 46–49 节的实参数支与 [Szöllősi 的 paired-circulant 构造，§2](https://arxiv.org/abs/0811.3930)，取 `-1<a<1, a!=0`。它约束同一个实际共同无偏向量与两条 canonical 射线的正交关系，不以逐模正交替代全局正交。

### 50.1 参数、实际基方向与结论

沿用 `h>0, s=h²`，并置

```math
P=p-1=\frac{a-3+i(h+a/h)}2,\qquad
Q=q-1=\frac{-a-3+i(h-a/h)}2,\qquad A=P+3,\quad B=Q+3.
```

此时 `1<s<3, a²=s(3-s)/(1+s)`，三个归一化 Fourier 块为

```math
T_0=\frac1{\sqrt6}\begin{pmatrix}A&B\\\bar B&-\bar A\end{pmatrix},
\qquad
T_1=T_2=\frac1{\sqrt6}\begin{pmatrix}P&Q\\\bar Q&-\bar P\end{pmatrix}.
```

记其未归一化首行为 `(alpha_l,beta_l)`，并定义

```math
g_l^\varepsilon=
\frac{\varepsilon i\alpha_l\overline{\beta_l}}{|\alpha_l||\beta_l|},
\qquad b_l^\varepsilon=(1,g_l^\varepsilon)^T,
\qquad \varepsilon\in\{1,-1\}.
```

所有分母均非零，因为

```math
|A|^2=3+2a,\quad |B|^2=3-2a,\quad
|P|^2=3-a,\quad |Q|^2=3+a.
```

令 `f_l=(1,omega^l,omega^(2l))`。输入侧六条 canonical 射线由单位向量 `(f_l,g_l^epsilon f_l)/sqrt(6)` 代表；它们组成正交基，且每个 `T_l b_l^epsilon` 的两个分量均有模一。

**命题 50.1。** 对这个实参数支，若单位相位输入 `(x,y)` 与 `H0(x,y)` 都逐项有模一，且其射线正交于两条不同的 canonical 输入射线，则该射线本身是 canonical。因而：

1. 含两条 canonical 射线的实际共同无偏正交三元组全部由 canonical 射线组成。
2. 任一非 canonical 六元正交 completion 至多包含一条 canonical 射线。
3. 在第 47、48 节的两个例外参数之外，任一非 canonical completion 至少包含五条 `Delta!=0` 的射线；在整个 `a!=0` 实支上，至少包含四条。

在实际列基对 `(I,H0)` 中，对单位向量 `v` 使用输入 `sqrt(6)H0* v`。公共酉变换 `H0` 保持全部内积，把上述 canonical 输入基传为实际 canonical completion。因此命题中的正交性与计数也成立于这个列基约定；`Delta` 始终在上述输入侧计算。

### 50.2 两个全局正交条件强制八个三维子空间之一

**证明。** 单位相位三元组若有一个 Fourier 系数为零，就必为单模。若共同平坦输入的一个完整二维 mode 投影为零，则两个 channel 都是单模。它们只能取同一个 mode：否则某个输出 channel 恰有两个非零 Fourier 系数，这不可能是单位相位三元组。这里使用了所有 `T_l` 的四个矩阵元非零。因此，整个 mode 投影为零的输入必为 canonical。

反设有非 canonical 射线满足命题的两个正交条件。它在三个 mode 上均非零。两条给定 canonical 射线不能来自同一个 mode，否则它们张成该完整 mode，导致上述矛盾。因此它们来自两个不同的 mode。

在这两个 mode 内，输入分量必须分别沿另一个 canonical 方向，故两个输入 channel 的逐模质量相等。两条输入 channel 的总平方范数都为三，遂使第三个 mode 的两条输入质量也相等。前两个 mode 的两个输出质量同样相等；输出 channel 的总平方范数也都为三，故第三个 mode 的两个输出质量相等。

非零二维向量 `(u,z)` 若满足 `|u|=|z|`，且在 `T_l` 下的两个输出质量相等，则

```math
\operatorname{Re}\bigl(\alpha_l\overline{\beta_l}
 u\overline z\bigr)=0,
\qquad \frac zu=g_l^\varepsilon
```

对某个符号 `epsilon` 成立。因此该输入必落在选定每个 mode 一个 canonical 方向的八个三维子空间之一：

```math
z_l=g_lu_l,\qquad
 g_l=g_l^{\varepsilon_l},\qquad
(\varepsilon_0,\varepsilon_1,\varepsilon_2)\in\{1,-1\}^3.
```

以下证明每个这样的子空间内，共同平坦射线只能是单模。

### 50.3 四条实际 channel 的 autocorrelation 满秩证书

写 `T_l b_l=(U_l,V_l)^T`。四条实际 Fourier channel 系数分别为

```math
(u_l),\qquad(g_lu_l),\qquad(U_lu_l),\qquad(V_lu_l),
```

其中 `g_l,U_l,V_l` 均为单位复数。令 `c_l=conjugate(u_l)u_(l+1)`，下标模三。四条相位条件给出 `Lc=0`，矩阵 `L` 的第 `l` 列为

```math
L_{\cdot l}=\begin{pmatrix}
1\\\overline{g_l}g_{l+1}\\
\overline{U_l}U_{l+1}\\\overline{V_l}V_{l+1}
\end{pmatrix}.
```

先设 `epsilon_2=-epsilon_1`。此时 `b1,b2` 正交，平方范数均为二。分别相加 `L` 的前两行与后两行，得到

```math
(A_0,0,B_0),\qquad(C_0,0,D_0),
```

其中

```math
A_0=\langle b_0,b_1\rangle,\quad B_0=\langle b_2,b_0\rangle,
\qquad C_0=\langle T_0b_0,T_1b_1\rangle,\quad
D_0=\langle T_1b_2,T_0b_0\rangle.
```

令

```math
C=\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad
K=\begin{pmatrix}-a/h&-h-ia\\-h+ia&a/h\end{pmatrix}.
```

直接相乘给出

```math
C^*(\sqrt6T_1)=-3I-iK,\qquad
\sqrt6T_0=\sqrt6T_1+3C,\qquad
R:=T_0^*T_1=-\frac{I+iK}{2}.
```

这里 `K*=K, Tr(K)=0`。取酉矩阵 `E=(b1/sqrt(2),b2/sqrt(2))`，记 `K'=E*KE`。在此基中展开 `R* b0`，利用 `||b0||²=2` 与 `Tr(K')=0`，恰得

```math
A_0D_0-B_0C_0=2iK'_{21}.
```

该量非零。否则 Hermitian 性使 `K'` 为 `diag(k,-k)`；而 `E` 的四个矩阵元平方模均为 `1/2`，所以 `K=E diag(k,-k) E*` 的两个对角元都为零，与 `K11=-a/h!=0` 矛盾。因此两条行和强制 `c0=c2=0`，再由第一行得到 `c1=0`。

现在设 `epsilon_1=epsilon_2`。此时 `b1=b2`、`T1b1=T2b2`，所以 `L` 的每行都有形式 `(rho,1,conjugate(rho))`，对应四个单位复数

```math
1,\qquad r=\overline{g_0}g_1,\qquad
u=\overline{U_0}U_1,\qquad v=\overline{V_0}V_1.
```

三个不同的 `rho` 已足以使秩为三：将每行乘以 `rho`，就得到行形 `(rho²,rho,1)` 的 Vandermonde 矩阵。

置 `k0=|A||B|, k1=|P||Q|, e=epsilon_0 epsilon_1`。由二维输出的显式公式，

```math
r=\frac{eP\overline Q\overline A B}{k_0k_1},\qquad
\frac{V_l}{U_l}=
-\frac{\varepsilon_l i\overline{\alpha_l\beta_l}}
 {|\alpha_l||\beta_l|},\qquad
t:=\frac vu=\frac{e\overline{PQ}AB}{k_0k_1}.
```

下列精确虚部恒等式给出 `r!=1` 及 `t notin {1,r,r^(-1)}`：

```math
\operatorname{Im}(P\overline Q\overline A B)
=-\frac{3a(s+3)}{2h}\ne0,
```

```math
\operatorname{Im}(P\overline A)=3\operatorname{Im}P>0,\qquad
\operatorname{Im}(\overline Q B)=-3\operatorname{Im}Q<0,
```

```math
\operatorname{Im}(AB\overline{PQ})
=\frac32\bigl((3-a)\operatorname{Im}Q+(3+a)\operatorname{Im}P\bigr)>0.
```

其中 `Im P=(h+a/h)/2, Im Q=(h-a/h)/2` 在本支均为正。第一式也可由 `P conjugate(A)=-(3-a)/2+3i Im P` 与 `conjugate(Q) B=-(3+a)/2-3i Im Q` 直接得到。中间两式分别结合

```math
\frac rt=\frac{P\overline A}{\overline P A},\qquad
rt=\frac{\overline Q B}{Q\overline B}
```

排除 `t=r`、`t=r^(-1)`；最后一式排除 `t=1`。

若四个 `rho` 只有至多两个值，因为 `r!=1`，必有 `u,v in {1,r}`，从而 `v/u in {1,r,r^(-1)}`，矛盾。因此这一符号情形也有 `rank L=3`。

两种情形穷尽八个选择。于是 `c0=c1=c2=0`，在三循环上这意味着至多一个 `u_l` 非零；该射线必为 canonical，完成核心刚性证明。

### 50.4 对实际 completion 的约束

若非 canonical completion 包含两条 canonical 射线，其余每条都正交于这两条，因而也必 canonical，矛盾。所以它至多含一条 canonical 射线。

除第 47、48 节的两个参数 `a=±sqrt((37-sqrt(73))/72)` 外，`Delta=0` 射线恰是 canonical 六条，故任一非 canonical completion 至少含五条 `Delta!=0` 射线。在例外参数处，若它含一条 canonical 射线，其他五条也均有 `Delta!=0`，因为例外射线与 canonical 射线之间没有正交边；若它不含 canonical 射线，其 `Delta=0` 部分位于 `K3,3`，最多只能取两条，故至少四条满足 `Delta!=0`。命题得证。

此外，结合第 49 节已证的逐射线距离，对任一非 canonical completion `C`，至多一列为 canonical，故至少五列与任意 canonical 射线的 projective 距离不小于 `|a|/80`。因此，在全部列相位与排列构成的单项式酉矩阵 `M` 上，

```math
\inf_M\|C-C_{\mathrm{can}}M\|_F\ge\frac{\sqrt5\,|a|}{80}.
```

若含例外射线，第 49 节的 `sqrt(6)|a|/80` 下界仍然成立。

本节没有排除只含一条 canonical 射线的混合正交三元组，也没有排除三条 `Delta!=0` 射线的正交兼容性；没有由这些计数推出 affinity 下界或 quartet 排除。

## 51. 实分支上反射对称三点轨道的正交排除

本节保留 §46 的实际共同平坦条件，排除一个含三条共享相位向量的满支撑子情形。配对 circulant 构造沿用 [Szöllősi, §2](https://arxiv.org/abs/0811.3930)；以下结论只涉及同步坐标置换轨道，不把不同轨道的三条实际射线替换为独立概率变量。

### 51.1 参数、轨道与命题

取 \(-1<a<1\)，令 \(p,q\) 为虚部为正的单位复数，满足
\[
\Re p=(a-1)/2,\qquad \Re q=(-a-1)/2.
\]
写 \(p+q=-1+ih\)、\(s=h^2\)，则
\[
h>0,\quad 1<s\le3,\quad a^2=\frac{s(3-s)}{1+s},
\quad p=\frac{a-1+i(h+a/h)}2,\quad
q=\frac{-a-1+i(h-a/h)}2.
\]
本节允许 \(a=0\)。定义
\[
C=\begin{pmatrix}1&1\\1&-1\end{pmatrix},\quad
D=\begin{pmatrix}p&q\\\bar q&-\bar p\end{pmatrix},\quad
N=D-C,\quad T_0=\frac{D+2C}{\sqrt6},\quad T_1=T_2=\frac N{\sqrt6}.
\]
它们是实际矩阵
\[
H_0=\frac1{\sqrt6}
\begin{pmatrix}J+(p-1)I&J+(q-1)I\\
J+(\bar q-1)I&-J-(\bar p-1)I\end{pmatrix}
\]
的 Fourier mode 块，其中 \(J\) 为三阶全一矩阵。各 \(T_\ell\) 酉且行列式为 \(-1\)，并有 \(C^*C=D^*D=2I\)、\(N^*N=6I\)。同步置换同时作用于两个 channel 的三个坐标，与 \(H_0\) 交换；记三循环为 \(S\)。

**命题 51.1。** 设单位向量 \(v\) 与 \(H_0v\) 的所有坐标模均为 \(1/\sqrt6\)。若 \([v]\) 被一个同步换位固定，则其同步 \(S_3\) 轨道中的不同射线两两不正交。特别地，\(v,Sv,S^2v\) 不可能构成正交三元组。

换位在每个 channel 中都有一个不动坐标，且这些坐标非零，因此这里的射影不动必为向量本身不动。适当同步置换及调整一个整体相位后可写
\[
\sqrt6v=(x,y),\qquad x=(r,1,1),\quad y=g(t,1,1),
\qquad |r|=|t|=|g|=1.
\]
轨道中不同向量的内积均为实数
\[
\langle v,Sv\rangle=\langle v,S^2v\rangle
=\frac{1+\Re r+\Re t}{3}.
\]
故只要存在一个正交对，就有 \(\Re(r+t)=-1\)，且三条循环平移全部正交。这一条件还蕴含 \(r,t\ne1\)；两个 channel 的 Fourier 值分别正比于
\((r+2,r-1,r-1)\) 和 \((t+2,t-1,t-1)\)，所以它们均为满支撑。下面直接排除此实际共享相位情形。

### 51.2 由假设轨道得到实际配对 completion

令 \(L(z)=J+(z-1)I\)、\(X=L(r)\)、\(Y=gL(t)\)，并定义
\[
K=\frac1{\sqrt6}\begin{pmatrix}X&-\bar Y\\Y&\bar X\end{pmatrix}.
\]
前三列是 \(v\) 的三个循环平移；后三列是其在
\(\Theta(x,y)=(-\bar y,\bar x)\) 下的像。恒等式
\(H_0\Theta=-\Theta H_0\) 保证这六列及其 \(H_0\) 像全部平坦，所用相位始终来自同一个 \(r,t,g\)。

\(K\) 的 mode 块为
\[
U_0=\frac1{\sqrt6}\begin{pmatrix}r+2&-\bar g(\bar t+2)\\
g(t+2)&\bar r+2\end{pmatrix},\qquad
U_1=U_2=\frac1{\sqrt6}\begin{pmatrix}r-1&-\bar g(\bar t-1)\\
g(t-1)&\bar r-1\end{pmatrix}.
\]
由 \(\Re(r+t)=-1\)，各块均形如
\(\bigl(\begin{smallmatrix}u&-\bar z\\z&\bar u\end{smallmatrix}\bigr)\)，且 \(|u|^2+|z|^2=1\)。因此 \(U_0,U_1\in SU(2)\)，\(K\) 酉，\(K\) 与 \(H_0K\) 均为归一化复 Hadamard 矩阵。

mode 块为 \(W_0,W_1,W_1\) 的矩阵，其空间对角二阶块为 \((W_0+2W_1)/3\)，非对角二阶块为 \((W_0-W_1)/3\)。平坦性遂给出
\[
\|U_0-U_1\|_F^2=6,\qquad
\|T_0U_0-T_1U_1\|_F^2=6.
\]
设 \(Q=T_1^*T_0\)、\(R=U_0U_1^*\)。两者属于 \(SU(2)\)，其迹为实数；上述等式以及 \(H_0\) 的非对角块平坦性给出
\[
\operatorname{tr}R=\operatorname{tr}(QR)=\operatorname{tr}Q=-1.
\]
Cayley–Hamilton 恒等式给出 \(Q^2+Q+I=0\)、\(Q^*=-I-Q\)，从而
\[
\operatorname{tr}(Q^*R)=2,\qquad
\|Q-R\|_F^2=4-2\Re\operatorname{tr}(Q^*R)=0.
\]
故 \(R=Q\)、\(U_0=QU_1\)。这一步依赖实际酉 mode 块，不能由各 mode 的独立模长条件替代。

### 51.3 三个实际 Bloch 约束的矛盾

由 \(Q=T_1^*T_0\) 及 \(Q^2+Q+I=0\)，有 \(T_0Q=-T_0-T_1\)。代回空间块后，\(K\) 的对角、非对角块分别为
\(T_1^*DU_1/\sqrt6\)、\(T_1^*CU_1/\sqrt6\)；\(H_0K\) 的相应块分别为
\(-CU_1/\sqrt6\)、\(-DU_1/\sqrt6\)。因此
\[
CU_1,\quad DU_1,\quad T_1^*CU_1,\quad T_1^*DU_1
\]
的每个元素模均为一。

取 \(U_1\) 的第一列 \(\eta=(\eta_0,\eta_1)^T\)，则 \(\|\eta\|=1\)。令 \(Z=\operatorname{diag}(1,-1)\)，并用通常的 Pauli 矩阵 \(\sigma_x,\sigma_y,\sigma_z\)。上述平坦性蕴含
\[
\eta^*B_0\eta=\eta^*B_1\eta=\eta^*B_2\eta=0,
\quad B_0=C^*ZC,\quad
B_1=(N^*C)^*Z(N^*C),\quad B_2=(N^*D)^*Z(N^*D).
\]
只使用 \(s=h^2\)、\(a^2=s(3-s)/(1+s)\) 展开可得
\[
\begin{aligned}
B_0&=2\sigma_x,\\
B_1&=-4a\sigma_x-\frac{4h(s+3)}{s+1}\sigma_y
                  +\frac{4(s+3)}{s+1}\sigma_z,\\
B_2&=8a\sigma_x+\frac{8h^3}{s+1}\sigma_y
                  +\frac{4(s+3)}{s+1}\sigma_z.
\end{aligned}
\]
定义来自同一实际列的实坐标
\[
b_x=2\Re(\bar\eta_0\eta_1),\quad
b_y=2\Im(\bar\eta_0\eta_1),\quad
b_z=|\eta_0|^2-|\eta_1|^2.
\]
其满足 \(b_x^2+b_y^2+b_z^2=1\)。\(B_0\) 方程给出 \(b_x=0\)，\(B_1\) 方程给出 \(b_z=hb_y\)；代入 \(B_2\) 方程得到 \(12hb_y=0\)。由于 \(h>0\)，这强制 \(b=0\)，与单位长度矛盾。对应三个系数行的行列式为
\[
-\frac{96h(s+3)}{s+1}\ne0.
\]
命题 51.1 得证。

上述矛盾也有明确的平方和形式。令
\[
L_0=b_x,\quad L_1=-\frac{a(s+1)}{s+3}b_x-hb_y+b_z,\quad
L_2=\frac{2a(s+1)}{s+3}b_x+\frac{2hs}{s+3}b_y+b_z,
\quad d=3h(s+1)(s+3)>0.
\]
三个平坦性方程等价于 \(L_0=L_1=L_2=0\)，而恒等式
\[
\begin{aligned}
db_x&=dL_0,\\
db_y&=(s+3)^2(L_2-L_1)-3a(s+1)(s+3)L_0,\\
db_z&=2sh(s+3)L_1+h(s+3)^2L_2-6ah(s+1)L_0
\end{aligned}
\]
平方相加后，左边为 \(d^2\|b\|^2=d^2>0\)，右边在三个约束上为零。所有分母在该分支严格为正，故可直接清除分母形成多项式证书。

### 51.4 一般同步置换轨道中的限制

若一个同步 \(S_3\) 轨道中的正交三元组使用了两种奇偶性的置换，统一左乘一个置换后，可写成 \(v,R_{12}v,R_{13}v\)，其中后两者为不同换位。用单位模坐标写 \(\sqrt6v=(x,y)\)，设 \(z_j=(x_j,y_j)\)、\(A_{jk}=\langle z_j,z_k\rangle\)，则 \(\|z_j\|^2=2\)。前两条正交关系给出
\(\Re A_{12}=\Re A_{13}=-1\)；第三条是三循环正交关系，给出
\(\Re(A_{12}+A_{13}+A_{23})=0\)。于是 \(\Re A_{23}=2\)，故
\[
\|z_2-z_3\|^2=4-2\Re A_{23}=0.
\]
因此 \(v\) 被剩余换位固定，命题 51.1 排除此情形。

所以，同一个同步 \(S_3\) 轨道若包含实际正交三元组，它只能来自无换位稳定子的六点轨道中的三个循环平移。本节尚未排除这一剩余情形，也未排除由不同轨道选出的三条射线。对实际 column pair \((I,H_0)\)，统一施加 \(H_0\) 即得到相同结论，因为它保留正交性并与同步置换交换。

### 51.5 一般循环正交三元组的严格换位正性

**命题 51.2。** 在命题 51.1 的同一实分支上，设 \(v\) 与 \(H_0v\) 均平坦，且 \(v,Sv,S^2v\) 正交归一。则对每个同步换位 \(R\)，
\[
\langle v,Rv\rangle>0.
\]
该内积因 \(R=R^*\) 而为实数。结论也约束无换位稳定子的六点轨道，但不声称此类循环正交三元组一定存在或已被全部排除。

**证明。** 写 \(\sqrt6v=(x,y)\)，令 \(X,Y\) 为首列分别为 \(x,y\) 的 circulant 矩阵，改用
\[
K=\frac1{\sqrt6}\begin{pmatrix}X&-Y^*\\Y&X^*\end{pmatrix}.
\]
其后三列是 \(\Pi\Theta v\) 的循环平移，其中 \(\Pi\) 同步交换坐标 \(1,2\)。由于 \(\Pi H_0=H_0\Pi\)、\(H_0\Theta=-\Theta H_0\)，\(K,H_0K\) 的每个元素模均为 \(1/\sqrt6\)。定义
\[
\lambda_{x,k}=\sum_{j=0}^2x_j\omega^{-jk},\qquad
U_k=\frac1{\sqrt6}\begin{pmatrix}\lambda_{x,k}&-\overline{\lambda_{y,k}}\\
\lambda_{y,k}&\overline{\lambda_{x,k}}\end{pmatrix}.
\]
循环正交关系恰好给出 \(|\lambda_{x,k}|^2+|\lambda_{y,k}|^2=6\)，故三个实际 \(U_k\) 都属于 \(SU(2)\)，\(K\) 酉。

若任一 channel 有一个 Fourier 坐标为零，单位模三元组的单模性质会使剩余某 mode 的平方模为九，与上述总能量六矛盾。因此这里的两个 channel 自动满支撑；结合实际双平坦性，§46 还给出 \(\Delta\ne0\)。

形如 \(\bigl(\begin{smallmatrix}u&-\bar z\\z&\bar u\end{smallmatrix}\bigr)\) 的矩阵构成实四元数代数；记 \(|A|_q^2=\det A\)，则 \(A^*A=|A|_q^2I\)。设
\[
V=(U_1+U_2)/2,\quad W=(U_1-U_2)/2,\quad
R_0=VU_0^*,\quad S_0=WU_0^*,\quad t^2=\det V.
\]
有 \(0\le t^2\le1\)、\(|R_0|_q^2=t^2\)、\(|S_0|_q^2=1-t^2\) 及 \(\Re\operatorname{tr}(R_0^*S_0)=0\)。\(K,H_0K\) 的空间对角二阶块平坦性给出
\[
|I+2R_0|_q^2=|Q+2R_0|_q^2=3,\qquad Q=T_1^*T_0.
\]
写 \(Q=-I/2+i n\cdot\sigma\)、\(R_0=bI+i r\cdot\sigma\)，其中 \(n,r\in\mathbb R^3\)，则
\[
|n|^2=3/4,\quad b=1/2-t^2,\quad n\cdot r=3b/2,
\quad |r|^2=t^2-b^2.
\]
实 Cauchy–Schwarz 不等式遂给出
\[
\frac94b^2\le\frac34(t^2-b^2),\qquad
(1-2t^2)^2\le t^2,\qquad
(4t^2-1)(t^2-1)\le0.
\]
由于 \(t^2\le1\)，必有 \(t^2\ge1/4\)，从而
\[
k=\tfrac12\Re\operatorname{tr}(U_1^*U_2)=2t^2-1\ge-1/2.
\]
令 \(z_j=(x_j,y_j)\)、\(r_{jk}=\Re\langle z_j,z_k\rangle\)，并令 \(\eta_k\) 为 \(U_k\) 第一列。循环正交性蕴含 \(r_{01}+r_{12}+r_{20}=0\)，直接 Fourier 展开给出
\[
\langle\eta_1,\eta_2\rangle
=\frac{\omega r_{01}+r_{12}+\omega^2r_{20}}3,\qquad
k=r_{12}/2,\qquad
\langle v,R_{12}v\rangle=\frac{1+2k}{3}\ge0.
\]

下面排除等号。若 \(k=-1/2\)，则 \(t^2=b=1/4\)，Cauchy–Schwarz 等号强制 \(r=n/2\)。因此
\[
R_0=(I+Q)/2,\qquad A=I-R_0=(I-Q)/2,
\qquad |A|_q^2=|S_0|_q^2=3/4.
\]
\(K\) 的两个非对角空间块为 \(M_+/3,M_-/3\)，其中
\[
M_\pm=(A\pm i\sqrt3S_0)U_0.
\]
\(H_0K\) 的相应块为 \(-T_1M_-/3,-T_1M_+/3\)，因为 \(Q-R_0=-A\)。故 \(M_+\) 及 \(T_1M_+\) 的每个元素模均为 \(\sqrt{3/2}\)。每一列 \(\xi\) 必满足同一实际 \(T_1\) 的双平坦方向条件
\[
\Re\bigl((p-1)\overline{(q-1)}\xi_0\bar\xi_1\bigr)=0.
\]
由于 \(p-1,q-1\ne0\)，这里只有两条可能的复直线，其 component ratios 为相反的单位复数，故两条直线正交。而
\[
\Re\det(A+i\sqrt3S_0)=|A|_q^2-3|S_0|_q^2=-3/2
\]
说明 \(M_+\) 可逆，两列必须选择不同直线。每列范数为 \(\sqrt3\)，所以 \(M_+^*M_+=3I\)。展开得到 \(A^*S_0=S_0^*A\)；Hermitian 四元数矩阵只能是实标量，故 \(S_0=cA\)，\(c\in\mathbb R\)，等范数进一步给出 \(c=\pm1\)。于是
\[
\{U_1,U_2\}=\{U_0,QU_0\},\qquad
M_+=(1\pm i\sqrt3)AU_0,\qquad
A=-\frac{\sqrt{3/2}}2T_1^*C.
\]
\(M_+,T_1M_+\) 的平坦性强制 \(T_1^*CU_0,CU_0\) 的元素模均为一；\(K\) 的对角块为
\((2I+Q)U_0/3=T_1^*DU_0/\sqrt6\)，故 \(T_1^*DU_0\) 也有该性质。\(U_0\) 第一列遂满足 §51.3 中三个矛盾的实际 Bloch 约束，排除等号。对 \(Sv,S^2v\) 重复同一论证即覆盖全部三个同步换位。证毕。

### 51.6 一个被严格符号条件排除的满支撑相位族

**命题 51.3。** 取 \(c=(\sqrt3-1)/2\)，令 \(0<\theta<\pi\)、\(\cos\theta=c\)，并设
\[
x=(1,e^{i\theta},e^{-i\theta}),\qquad
y=(1,e^{-i\theta},e^{i\theta}),\qquad v=(x,y)/\sqrt6.
\]
这三条循环平移 \(v,Sv,S^2v\) 正交归一，两个 channel 的 Fourier transforms 均为满支撑，但对上述实分支的任何参数，\(H_0v\) 都不平坦。

**证明。** 等式 \(2c^2+2c-1=0\) 给出两 channel 的总循环相关
\(2(2\cos\theta+\cos2\theta)=0\)，故循环平移正交；但
\[
\langle v,R_{12}v\rangle=1-\frac{2\sqrt3}{3}<0,
\]
与命题 51.2 的必要条件矛盾。各 channel 的零 mode 值为 \(1+2c=\sqrt3\)，其余两 mode 值的乘积为
\((1-c)^2-3(1-c^2)=-6c\ne0\)，因此满支撑也成立。证毕。

第 52 节及后续推导见同主题[理论续卷](MUB_SIX_FOURTH_BASIS_THEORY_CONTINUATION.md)。
