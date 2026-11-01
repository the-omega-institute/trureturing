<a id="auric-convergent-residual-certificates"></a>

# AURIC Convergent Residual Certificates, Unitary Error Recursion, and Tolerant Robin Criterion

> **Reader-visible source and scope note.** The manuscript body below is the complete user-supplied source, retained in its original order, including all opening prose, eight ordered numbered sections, the final section, every proof and derivation, all 35 original equation tags, and all six literal URL targets. The body adaptations are conversion of the supplied backslash math delimiters to portable dollar delimiters and relocation of each original equation number into its immediately following ordinary-flow caption. Mathematical expressions, the two internal row-spacing commands, and author sentences are preserved; necessary qualifications are separate adjacent editorial notes.
>
> **Source and provenance.** The input is an AI/user-supplied continuation manuscript. The title above is descriptive editorial metadata; no author, version, or date is invented. Source SHA-256: <code style="overflow-wrap:anywhere">2de87858a3a093afd9abecdb49ece42789610e0eebb9b7683663e79b49cb7a5a</code>; source size 23,219 bytes and 1,350 logical lines. Inventory: 210 math regions (84 inline, 126 display), 35 numbered displays, and nine main units (eight numbered sections plus the final section).
>
> **Navigation.** [Section I](#section-1-fixed-arithmetic-object) · [Section II](#section-2-strict-detail-positivity) · [Section III](#section-3-residual-error-theorem) · [Section IV](#section-4-finite-frequency-envelope) · [Section V](#section-5-unitary-error-conservation) · [Section VI](#section-6-relative-tolerance) · [Section VII](#section-7-robin-transfer) · [Section VIII](#section-8-zeckendorf-ordering) · [Final position](#section-final-position)
>
> **Bounded whole-paper review.** `CHECKED` below means that the supplied local algebra, stated convention, or source correspondence was read and is internally aligned at the displayed level. `ASSUMED-UNVERIFIED` names a premise or bridge that the supplied text does not itself establish. No fresh Lean/kernel build, mathematical program, numerical computation, CAS, simulation, gate search, or native physical-access test is claimed.
>
> - `CHECKED — inventory and source fidelity:` the exact source hash, 210-region inventory, 35 tags, six URLs, opening, all sections, proofs, and ending were read; the six URL targets and query strings remain byte-for-byte present.
> - `CHECKED — kernel and Fourier interface:` the definitions of $K$, $P$, $S$, $p_0$, the finite atomic quadratic forms, the window, the Fourier weight $m$, and the stated logarithmic scale are retained with their signs and conjugation.
> - `ASSUMED-UNVERIFIED — coercive detail space:` (3)–(5) require the completed Hilbert/energy space, the exact Fourier normalization, a self-adjoint bounded remainder realization, and the stated operator constants.
> - `ASSUMED-UNVERIFIED — nested variational spaces:` residual convergence requires nested finite spaces containing the fixed coarse grid and dense in the full completed $Z$; mere node-density prose does not supply that inclusion or the normal/derivative domain.
> - `ASSUMED-UNVERIFIED — variational existence and convergence:` uniqueness of each constrained minimizer, continuity on the moving-atom fibers, and operator-norm convergence of the finite cores are retained claims whose common completed-space proof is not reproduced here.
> - `ASSUMED-UNVERIFIED — residual identity:` the sign and conjugation in the derivative residual, endpoint/distribution terms, Schur identity (10), and the Loewner constant require one common completed-space derivation.
> - `ASSUMED-UNVERIFIED — weighted residual decay:` (11) needs an explicit $A_2$ verification for $W$, the interval-truncation plus cell-mean operator composition, duality, and a diagonal density argument with a fixed smooth target. The cited weighted Hilbert theorem is not itself that composition proof.
> - `ASSUMED-UNVERIFIED — finite envelope:` (12)–(16) need the full denominator/tail Loewner estimates and a diagonal choice despite possible growth of $\mathcal E_k^{(0)}$. Finite integrals are not finite certified arithmetic.
> - `CHECKED — abstract unitary algebra:` assuming the stated self-adjoint operator hypotheses, (17)–(22) give the positive contraction, Neumann expansion, two-output norm split, block Gram positivity, and geometric remainder.
> - `CHECKED WITH SCOPE — AURIC convention:` v37 uses $\rho=\begin{pmatrix}A&C^*\\C&B\end{pmatrix}$, so $C$ is lower-left; the corresponding choice for $\mathbb G_j$ is recorded locally below. This abstract unitary grants no native/free physical control.
> - `ASSUMED-UNVERIFIED — finite RKHS certificate:` (24)–(26) require the endpoint exponential extension, Fourier/RKHS identification, and positive-definiteness of $M$ on the stated completion.
> - `CHECKED WITH SCOPE — tolerance:` (23), (27), and eventual strict passage are for $\varepsilon\ge0$, fixed $D$, and fixed $\varepsilon>0$ in the strict step; they do not yield a uniform expanding-window certificate.
> - `ASSUMED-UNVERIFIED — inherited Robin premises:` the same-n decomposition (28), $\mathcal D(n)\ge0$, strict optimizer/equality-layer and 5040 boundary bridge, complete $\mathcal B(T)$, and weighted root-correction passage (32) remain open as recorded by the merged predecessor.
> - `CHECKED WITH SCOPE — PNT tail and margin:` the cited Kedlaya chapter is an unconditional PNT-error source, while the rational inequalities for $\varepsilon_*=1/8$ are a separate paper calculation; neither discharges the inherited Robin bridge.
> - `CHECKED WITH SCOPE — Zeckendorf:` the exact pin is <code style="overflow-wrap:anywhere">9ceb721e13c64eb4b1c71a43238a2b2fc4770093</code>; it supplies ordering/permutation only. Density, node skipping, nested inclusion, and window-uniform bounds remain separate obligations.
> - `ASSUMED-UNVERIFIED — RH forward and reverse bridges:` (35) requires an actual-zero expansion and its normal convergence that imply global positivity of $K$ under RH and hence $\mathcal S_D\succeq0$; separately, its reverse direction needs meromorphic Laplace continuation, multiplicity/noncancellation, and identity-theorem steps. No RH proof or global all-window inequality is claimed.
>
> **External-source scope.** The Lacey–Petermichl–Reguera paper was read as the cited $A_2$ Hilbert-transform theorem; the Kedlaya page was read for the unconditional PNT-error setting; the Ramanujan–Robin paper was read as historical/criterion context. These reads establish source scope, not the missing manuscript-specific compositions.

/sshx 继续。这一轮可以补上前面一个真正缺失的环节：

> **不仅证明递归误差可和，还构造一个确实趋于零的误差读数，并用它给每一步有限核心附上严格下界。这个下界允许直接接入 AURIC 的酉守恒结构和 Robin 不等式。**

下面给出定义、定理和证明。**这些结论仍未完成黎曼猜想的证明；尚待证明的是，实际算术核心在窗口不断扩大时，始终满足最后给出的统一不等式。** 但现在，“继续递归”已经有了明确的误差控制和停止条件。

项目依据仍取已经核对过的 [AURIC v37](https://github.com/the-omega-institute/trureturing/blob/18ab178472d8c29eb90d5e5f4e6c8b4c89038e84/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)：其第 6 节允许用保留上下文的算子值三轴递归表示完整关系，第 9 节给出酉误差的可和控制。下文的残差定理、有限积分下界和 Robin 接入，是在这个接口上继续作出的纸面推导。

---

<a id="section-1-fixed-arithmetic-object"></a>
## 一、固定实际算术对象，不改变原整数和原尺度

沿用前面建立的实际核。对 $t\geq0$，令

$$
\begin{aligned}
K(t)
={}&(1+\gamma-t)e^{t/2}
-\log(2\pi)e^{-t/2}\\
&+\sum_{j\geq1}
\frac{e^{-(2j+\frac12)t}}{2j(2j+1)}
+\sum_{m\leq e^t}
\frac{\Lambda(m)}{\sqrt m}\,
2\sinh\frac{t-\log m}{2},
\end{aligned}
$$

并偶延拓到整个实轴。这里

$$
S:=K(0)=2+\gamma-\log(4\pi)>0.
$$

将其中明确为正核的部分记为

$$
P(t)=\sum_{j\geq1}c_j e^{-\lambda_j|t|},
\qquad
c_j=\frac1{2j(2j+1)},
\qquad
\lambda_j=2j+\frac12.
$$

其总量为

$$
p_0:=P(0)=1-\log2.
$$

对有限原子复测度

$$
\mu=\sum_i a_i\delta_{t_i},
$$

定义实际二次型

$$
Q_K(\mu)=
\sum_{i,j}\overline{a_i}a_jK(t_i-t_j).
$$

$Q_P$ 同理。这里允许带符号和复系数读出，才能保留全部关系方向。

固定窗口

$$
I=[0,D].
$$

把读出写成

$$
\mu=a\delta_0+F',
\qquad a=\mu(I),
$$

其中 $F$ 支撑于 $I$。正核给出精确能量

$$
Q_P(F')
=
\frac1{2\pi}\int_{\mathbb R}
m(\xi)|\widehat F(\xi)|^2\,d\xi,
$$

其中

$$
\boxed{
m(\xi)=
2\sum_{j\geq1}
c_j\lambda_j
\frac{\xi^2}{\lambda_j^2+\xi^2}.
}
$$
<a id="eq-1"></a>
<div class="equation-caption">Equation (1).</div>

这个权重具有三个关键性质：

$$
m(\xi)\geq0,
\qquad
m(\xi)\longrightarrow\infty\quad(|\xi|\to\infty),
$$

以及

$$
\boxed{
1+m(\xi)\asymp \log(e+|\xi|).
}
$$
<a id="eq-2"></a>
<div class="equation-caption">Equation (2).</div>

最后一个关系可直接将级数按 $j\leq|\xi|$ 与 $j>|\xi|$ 分开证明：前一部分产生调和和，后一部分有界。

这说明，实际核的细节能量自然对应一个**对数频率权重**。后面的误差也应当使用这个尺度。

---

<a id="section-2-strict-detail-positivity"></a>
## 二、先把细节空间的严格正性固定下来

> **Editorial note — completion and coercivity scope.** The displayed Fourier estimate is retained as supplied. Its conclusion is conditional on the completed energy space, Fourier normalization, and the precise bounded self-adjoint realization of the truncated remainder $R_D$ on the full detail space $Z=\ker C$. The bound $M_D=\|R_D''\|_{\mathrm{TV}}$ alone is not a cited operator-norm computation; any missing realization or constant is `ASSUMED-UNVERIFIED`. Later finite node spaces must be nested, must contain the fixed coarse grid, and must be dense in that same completed $Z$. Those requirements are not replaced by the statement that a node set merely becomes dense.

取一个足够细的固定粗网格

$$
0=x_0<x_1<\cdots<x_N=D,
$$

记 $\varphi_i$ 为对应的分段线性帽函数，并定义粗读出

$$
C_i\mu=\int\varphi_i\,d\mu.
$$

令

$$
Z=\ker C.
$$

对于 $\mu=F'\in Z$，有

$$
\int_{x_{i-1}}^{x_i}F(t)\,dt=0
\qquad(1\leq i\leq N).
$$
<a id="eq-3"></a>
<div class="equation-caption">Equation (3).</div>

把 $K-P$ 在所需差值范围外作光滑截断，记截断后的函数为 $R_D$，并令

$$
M_D=\|R_D''\|_{\mathrm{TV}}<\infty.
$$

有限性来自：除原点外的光滑背景项和有限个实际素数幂导数跳跃，都已经保留在这里。

### 引理 1：粗网格可以使细节能量具有任意大的 $L^2$ 下界

给定任意 $\beta>0$，可以把粗网格取得足够细，使

$$
\boxed{
Q_P(F')\geq\beta\|F\|_2^2
\qquad(F'\in Z).
}
$$
<a id="eq-4"></a>
<div class="equation-caption">Equation (4).</div>

**证明。**

若最大网格宽度为 $h$，由每格零均值，

$$
|\widehat F(\xi)|
\leq \frac{h|\xi|}{2}\sqrt D\,\|F\|_2.
$$

因此

$$
\frac1{2\pi}
\int_{-R}^{R}|\widehat F(\xi)|^2\,d\xi
\leq
\frac{Dh^2R^3}{12\pi}\|F\|_2^2.
$$

先选 $R$，使 $m(R)\geq2\beta$；再选 $h$，使右侧系数不超过 $1/2$。至少一半 Fourier 质量落在 $|\xi|>R$，于是

$$
Q_P(F')
\geq
\frac12m(R)\|F\|_2^2
\geq\beta\|F\|_2^2.
$$

证毕。

以下固定

$$
\beta=2(M_D+1),
\qquad
\theta=\frac{M_D}{\beta}<\frac12.
$$

在 $Z$ 上，以 $Q_P$ 为参考内积，实际形式可写为

$$
B_K(z,w)=\langle z,\mathcal A w\rangle_P,
\qquad
\mathcal A=I-\mathcal V,
\qquad
\|\mathcal V\|\leq\theta.
$$

所以

$$
\boxed{
(1-\theta)I
\preceq\mathcal A
\preceq(1+\theta)I.
}
$$
<a id="eq-5"></a>
<div class="equation-caption">Equation (5).</div>

这一步已经无条件证明了细节空间的正性。

---

<a id="section-3-residual-error-theorem"></a>
## 三、新的误差定理：构造一个确实趋于零的残差读数

上一轮的有限核心记为 $\mathcal S_k$，完成全部细节消去后的核心记为 $\mathcal S_D$。

具体地，令有限节点集合逐步增加、并在窗口中稠密。对每个粗坐标 $e_i$，取有限节点上的实际变分最小化读出

$$
\nu_{k,i}=\sum_s d_{i,s}\delta_s,
\qquad
C\nu_{k,i}=e_i.
$$

其核心矩阵为

$$
\mathcal S_k(i,j)=B_K(\nu_{k,i},\nu_{k,j}).
$$

前面已经证明

$$
\mathcal S_k\downarrow\mathcal S_D.
$$

现在补上一个**由实际核导数直接构造、并且能够证明趋零**的误差矩阵。

### 定义 1：去除粗均值后的实际残差

令

$$
f_{k,i}(t)
=
-\sum_s d_{i,s}K'(t-s),
\qquad 0<t<D.
$$

记 $\Pi_{\mathrm{cell}}$ 为对每个固定粗网格小区间取平均的 $L^2$ 投影，定义

$$
g_{k,i}
=
\mathbf 1_I
(I-\Pi_{\mathrm{cell}})f_{k,i},
$$

并在窗口外取零。

由于

$$
K'\in L^2_{\mathrm{loc}},
$$

这些都是合法的 $L^2$ 函数。原点处的对数奇性和实际素数幂处的导数跳跃都包括在内。

定义误差矩阵

$$
\boxed{
\mathcal E_k(i,j)
=
\frac1{2\pi}
\int_{\mathbb R}
\frac{
\overline{\widehat g_{k,i}(\xi)}
\widehat g_{k,j}(\xi)
}{
1+m(\xi)
}\,d\xi.
}
$$
<a id="eq-6"></a>
<div class="equation-caption">Equation (6).</div>

它显然正半定。

### 定理 1：可靠且收敛的残差下界

有

$$
\boxed{
\mathcal S_k-c_D\mathcal E_k
\preceq
\mathcal S_D
\preceq
\mathcal S_k,
}
$$
<a id="eq-7"></a>
<div class="equation-caption">Equation (7).</div>

其中明确可取

$$
\boxed{
c_D=\frac{1+\beta^{-1}}{1-\theta}.
}
$$
<a id="eq-8"></a>
<div class="equation-caption">Equation (8).</div>

并且

$$
\boxed{\mathcal E_k\longrightarrow0.}
$$
<a id="eq-9"></a>
<div class="equation-caption">Equation (9).</div>

这比单纯知道 $\mathcal S_k$ 收敛更强：每一步都有一个能控制真实极限的下界。

### 证明第一步：可靠性

用 $\mathcal R_k$ 表示全细节空间上的残差算子：

$$
\langle z,\mathcal R_k c\rangle_P
=
B_K\!\left(z,\sum_i c_i\nu_{k,i}\right),
\qquad z\in Z.
$$

精确变分消去给出

$$
\boxed{
\mathcal S_k-\mathcal S_D
=
\mathcal R_k^*\mathcal A^{-1}\mathcal R_k.
}
$$
<a id="eq-10"></a>
<div class="equation-caption">Equation (10).</div>

对 $z=F'\in Z$，分部积分及式 (3) 给出

$$
B_K\!\left(F',\sum_i c_i\nu_{k,i}\right)
=
\int_I\overline{F(t)}
\sum_i c_i g_{k,i}(t)\,dt.
$$

使用带权 Cauchy–Schwarz，

$$
\left|
\int_I\overline F\sum_i c_i g_{k,i}
\right|^2
\leq
\left[
\frac1{2\pi}
\int(1+m)|\widehat F|^2
\right]
c^*\mathcal E_kc.
$$

而式 (4) 给出

$$
\frac1{2\pi}\int(1+m)|\widehat F|^2
=
\|F\|_2^2+Q_P(F')
\leq
(1+\beta^{-1})Q_P(F').
$$

因此

$$
\mathcal R_k^*\mathcal R_k
\preceq
(1+\beta^{-1})\mathcal E_k.
$$

再由式 (5)，

$$
\mathcal A^{-1}\preceq\frac1{1-\theta}I.
$$

代入式 (10)，即得式 (7)。

### 证明第二步：为什么这个误差确实趋于零

> **Editorial note — equation (11) remains a qualified bridge.** The cited Lacey–Petermichl–Reguera paper supplies a weighted Hilbert-transform theorem for $A_2$ weights, but $W(\xi)\asymp\log(e+|\xi|)$ by itself does not instantiate the $A_2$ test or the exact interval-truncation/finite-cell-mean composition used here. A complete proof must show the Fourier-side truncation identity, boundedness of the finite-rank cell-mean correction on the chosen $H_W$ completion, and the duality map into the $P$-energy space. The density sentence also needs a fixed smooth target, approximation in the completed norm, and a diagonal passage through the nested atomic/step spaces; an arbitrary uniform bounded-variation assertion is insufficient. The signs and conjugations in the integration-by-parts residual identity require the distributional $K'$, endpoint terms, and the zero-cell constraints to be checked together. Accordingly, $\mathcal E_k\to0$, (11), and the downstream lower bound are retained as author claims but remain `ASSUMED-UNVERIFIED` pending those bridges.

这里需要区分两个命题：

$$
\mathcal R_k\to0
$$

已经由变分逼近的能量收敛得到；但它本身不能直接推出未加权的 $L^2$ 残差趋零。

式 (6) 的权重恰好补上这一点。

令

$$
W(\xi)=1+m(\xi),
$$

并定义

$$
\|F\|_{H_W}^2
=
\frac1{2\pi}\int W(\xi)|\widehat F(\xi)|^2\,d\xi.
$$

考虑投影

$$
\mathcal T_0F
=
\mathbf1_I F
-
\sum_{\text{粗格 }J}
\mathbf1_J\frac1{|J|}\int_JF.
$$

这个算子把全线函数送入“支撑在 $I$、每个粗格均值为零”的空间。

由 $W(\xi)\asymp\log(e+|\xi|)$，$W$ 是 $A_2$ 权重。区间截断在 Fourier 端可表示为调制后的 Hilbert 变换之差，所以它在 $H_W$ 上有界；有限个格均值修正也是有界算子。这里使用的加权 Hilbert 变换定理，可以在 Lacey–Petermichl–Reguera 的论文中找到直接证明。[arxiv.org](https://arxiv.org/pdf/0906.1941?utm_source=chatgpt.com)

因此存在固定常数 $C_{\mathcal T_0}<\infty$，使

$$
\|\mathcal T_0F\|_P
\leq C_{\mathcal T_0}\|F\|_{H_W}.
$$

对偶化后，

$$
\boxed{
\mathcal E_k
\preceq
C_{\mathcal T_0}^2\mathcal R_k^*\mathcal R_k.
}
$$
<a id="eq-11"></a>
<div class="equation-caption">Equation (11).</div>

于是 $\mathcal R_k\to0$ 蕴含 $\mathcal E_k\to0$。

这里没有遗漏完成空间：先用光滑函数逼近，再截断到窗口、去除粗格均值，最后用阶梯函数逼近，即可得到原有限原子读出的能量稠密性。阶梯逼近的统一有界变差给出 $O(|\xi|^{-1})$ 的 Fourier 尾，足以支配对数权重积分。

定理得证。

**一个实用的细节是：式 (7) 中的常数已经明确给出，并不需要知道上述 Hilbert 变换算子的具体范数。后者只用于证明误差最终趋零。**

---

<a id="section-4-finite-frequency-envelope"></a>
## 四、把无限频率积分进一步换成有限积分上界

> **Editorial note — finite envelope versus finite certification.** Equation (14) is a pointwise/Loewner estimate only after the denominator replacement and tail comparison are proved with the stated Fourier convention. Choosing $J_k,\Omega_k$ requires a diagonal argument that uses the actual finite value of $\mathcal E_k^{(0)}$ at each $k$, even if those values grow without bound. Thus (16) is a conditional finite-envelope statement. A finite interval integral and a finite sum are mathematical finite objects; they are not, by themselves, a finite certified arithmetic computation or an algorithmic sign check.

式 (6) 仍有一个全频率积分。这个无穷尾也可以严格控制。

定义有限和

$$
m_J(\xi)
=
2\sum_{j=1}^{J}
c_j\lambda_j
\frac{\xi^2}{\lambda_j^2+\xi^2}.
$$

由级数逐项估计，

$$
\boxed{
0\leq m(\xi)-m_J(\xi)
\leq\frac{\xi^2}{8J^2}.
}
$$
<a id="eq-12"></a>
<div class="equation-caption">Equation (12).</div>

再定义

$$
\mathcal E_k^{(0)}(i,j)
=
\int_I
\overline{g_{k,i}(t)}g_{k,j}(t)\,dt.
$$

给定有限频率截止 $\Omega>0$，令

$$
\begin{aligned}
\mathcal U_{k,J,\Omega}(i,j)
={}&
\frac1{2\pi}
\int_{-\Omega}^{\Omega}
\frac{
\overline{\widehat g_{k,i}(\xi)}
\widehat g_{k,j}(\xi)
}{
1+m_J(\xi)
}\,d\xi\\
&+
\frac{\mathcal E_k^{(0)}(i,j)}
{1+m_J(\Omega)}.
\end{aligned}
$$
<a id="eq-13"></a>
<div class="equation-caption">Equation (13).</div>

### 定理 2：完全有限积分的误差包络

有

$$
\boxed{
0\preceq\mathcal E_k
\preceq\mathcal U_{k,J,\Omega},
}
$$

以及

$$
\boxed{
0\preceq
\mathcal U_{k,J,\Omega}-\mathcal E_k
\preceq
\left(
\frac{\Omega^2}{8J^2}
+
\frac1{1+m_J(\Omega)}
\right)\mathcal E_k^{(0)}.
}
$$
<a id="eq-14"></a>
<div class="equation-caption">Equation (14).</div>

**证明。**

在 $|\xi|\leq\Omega$ 内，用式 (12) 控制分母替换的误差；在 $|\xi|>\Omega$ 内，用 $m$ 随 $|\xi|$ 增加以及 Plancherel 等式控制尾部。对任意粗向量 $c$ 应用这个标量估计，即得矩阵不等式。证毕。

因此，

$$
\boxed{
\mathcal S_k-c_D\mathcal U_{k,J,\Omega}
\preceq\mathcal S_D.
}
$$
<a id="eq-15"></a>
<div class="equation-caption">Equation (15).</div>

而且可以逐步选择有限的 $J_k,\Omega_k$，使

$$
\mathcal U_{k,J_k,\Omega_k}\to0.
$$

这不要求 $\mathcal E_k^{(0)}$ 有界或趋零：每一步只需把式 (14) 的标量系数取得足够小。

至此，我们得到一对真正收敛的有限步上下界：

$$
\boxed{
\mathcal S_k-c_D\mathcal U_{k,J_k,\Omega_k}
\preceq
\mathcal S_D
\preceq
\mathcal S_k.
}
$$
<a id="eq-16"></a>
<div class="equation-caption">Equation (16).</div>

它们只涉及有限实际关系矩阵、有限和，以及有限区间上的积分。

---

<a id="section-5-unitary-error-conservation"></a>
## 五、把误差递归写成严格的酉守恒

现在回应你反复强调的核心结构：

> 结果、误差及总量守恒，能否继续作为二元关系归一化，并递归放进 AURIC 三轴？

在这里，可以给出明确的肯定定理。

由

$$
\mathcal A=I-\mathcal V,
\qquad \|\mathcal V\|\leq\theta,
$$

定义

$$
\mathcal T=
\frac{\theta I+\mathcal V}{1+\theta}.
$$

则

$$
\boxed{
0\preceq\mathcal T\preceq\rho I,
\qquad
\rho=\frac{2\theta}{1+\theta}<1,
}
$$
<a id="eq-17"></a>
<div class="equation-caption">Equation (17).</div>

并且

$$
\mathcal A=(1+\theta)(I-\mathcal T).
$$

于是

$$
\boxed{
\mathcal A^{-1}
=
\frac1{1+\theta}\sum_{j=0}^{\infty}\mathcal T^j.
}
$$
<a id="eq-18"></a>
<div class="equation-caption">Equation (18).</div>

这里每项都是正算子，余项有显式几何界。

令 $\mathcal R_0$ 表示初始粗读出与整个细节空间的耦合。实际核心满足

$$
\mathcal S_D
=
\mathcal S_0-
\mathcal R_0^*\mathcal A^{-1}\mathcal R_0.
$$

所以

$$
\boxed{
\mathcal S_D
=
\mathcal S_0-
\frac1{1+\theta}
\sum_{j=0}^{\infty}
\mathcal R_0^*\mathcal T^j\mathcal R_0.
}
$$
<a id="eq-19"></a>
<div class="equation-caption">Equation (19).</div>

### 定理 3：每一步都可实现为保范数的二元分解

定义

$$
X_j=
\mathcal T^{j/2}\mathcal A^{-1/2}\mathcal R_0,
$$

$$
Y_j=
\frac1{\sqrt{1+\theta}}
\mathcal T^{j/2}\mathcal R_0.
$$

则有精确关系

$$
\boxed{
X_j^*X_j
=
Y_j^*Y_j+X_{j+1}^*X_{j+1}.
}
$$
<a id="eq-20"></a>
<div class="equation-caption">Equation (20).</div>

它对应一个明确的酉算子：

$$
\boxed{
\mathcal U=
\begin{pmatrix}
\sqrt{I-\mathcal T}&-\sqrt{\mathcal T}\\
\sqrt{\mathcal T}&\sqrt{I-\mathcal T}
\end{pmatrix},
\qquad
\mathcal U^*\mathcal U=I.
}
$$
<a id="eq-21"></a>
<div class="equation-caption">Equation (21).</div>

**证明。**

$\mathcal T$ 与它的各个连续函数交换，因此直接相乘即可验证式 (21)。

同时，

$$
Y_j=\sqrt{I-\mathcal T}\,X_j,
\qquad
X_{j+1}=\sqrt{\mathcal T}\,X_j.
$$

所以

$$
\mathcal U
\binom{X_j}{0}
=
\binom{Y_j}{X_{j+1}},
$$

保范数性就是式 (20)。证毕。

这时：

- $Y_j^*Y_j$ 是第 $j$ 层已经分离出的正能量；
- $X_{j+1}^*X_{j+1}$ 是仍需递归处理的剩余能量；
- $X_j^*X_j$ 是该层保留的原总量。

余量满足

$$
\boxed{
X_{j+1}^*X_{j+1}
\preceq
\frac{\rho^{j+1}}{1-\theta}
\mathcal R_0^*\mathcal R_0.
}
$$
<a id="eq-22"></a>
<div class="equation-caption">Equation (22).</div>

因此这里已经证明了**总量守恒、酉实现、误差递归以及几何衰减**。

### 对应的 AURIC 三轴

> **Editorial note — block convention and physical boundary.** In AURIC v37 §6 the block convention is $\rho=\begin{pmatrix}A&C^*\\ C&B\end{pmatrix}$, so $C$ is the **lower-left** block. For the displayed $\mathbb G_j$, the matching choice is $A=Y_j^*Y_j$, $B=X_{j+1}^*X_{j+1}$, and $C=X_{j+1}^*Y_j$; with that choice the stated $X=C+C^*$ and $Y=i(C^*-C)$ signs agree with v37. The block matrix $\mathcal U$ is an abstract unitary on a completed Hilbert-space direct sum. Its existence does not grant native AURIC control, a free physical gate, state preparation, measurement access, or an implementation/resource certificate.

把两个输出的完整关系保留为

$$
\mathbb G_j=
\begin{pmatrix}
Y_j^*Y_j&Y_j^*X_{j+1}\\
X_{j+1}^*Y_j&X_{j+1}^*X_{j+1}
\end{pmatrix}\succeq0.
$$

它的总量算子恰为

$$
Y_j^*Y_j+X_{j+1}^*X_{j+1}=X_j^*X_j.
$$

这正好可以使用项目 v37 的算子值三轴：

$$
S=A+B,\quad
Z=A-B,\quad
X=C+C^*,\quad
Y=i(C^*-C),
$$

并由

$$
\mathbb G_j
=
\frac12
\left(
I\otimes S+
\sigma_x\otimes X+
\sigma_y\otimes Y+
\sigma_z\otimes Z
\right)
$$

完整重建。总迹非零时可以归一化，同时保存原总迹。

**这个酉递归严格控制的是被消去的正细节能量。实际剩余核心仍是式 (19) 的差，其最终符号需要继续证明。**

---

<a id="section-6-relative-tolerance"></a>
## 六、给“允许多大负误差”一个明确的归一尺度

> **Editorial note — tolerance domain.** Equations (23), (27), and the strict-completeness paragraph require $\varepsilon\ge0$, with the eventual strict passage using a fixed $\varepsilon>0$ and a fixed window $D$. This is pointwise in $D$; it supplies no uniform choice of $k,J,\Omega$ as $D\to\infty$, and it does not establish the $\varepsilon=0$ case. The positive-definiteness of $M$ and the endpoint exponential extension used in (24)–(26) also remain conditional on the stated completion and Fourier/RKHS identification.

接下来不必要求有限核心每一步都已经精确正定。我们可以允许一个由实际正核度量的负误差。

希望得到

$$
\boxed{
Q_K(\mu)\geq-\varepsilon Q_P(\mu)
\qquad
(\operatorname{supp}\mu\subset[0,D]).
}
$$
<a id="eq-23"></a>
<div class="equation-caption">Equation (23).</div>

这等价于 $K+\varepsilon P$ 在该窗口上正半定。

为避免把误差尺度藏在另一个无限维最小化里，下面构造一个完全明确的有限矩阵。

取

$$
\lambda=\frac52,
$$

定义

$$
\begin{aligned}
M_{ij}
={}&
\frac1{2\lambda}
\int_0^D
\left(
\varphi_i'(t)\varphi_j'(t)
+\lambda^2\varphi_i(t)\varphi_j(t)
\right)\,dt\\
&+\frac12
\left[
\varphi_i(0)\varphi_j(0)
+\varphi_i(D)\varphi_j(D)
\right].
\end{aligned}
$$
<a id="eq-24"></a>
<div class="equation-caption">Equation (24).</div>

这是明确的正定矩阵。令

$$
\boxed{G_*=\frac16M^{-1}.}
$$
<a id="eq-25"></a>
<div class="equation-caption">Equation (25).</div>

### 引理 2：这个有限矩阵保留了实际正能量尺度

对所有窗口内读出，

$$
\boxed{
Q_P(\mu)\geq(C\mu)^*G_*(C\mu).
}
$$
<a id="eq-26"></a>
<div class="equation-caption">Equation (26).</div>

**证明。**

$P$ 的第一项为

$$
\frac16e^{-\lambda|t|},
$$

其余各项仍是正核，所以

$$
Q_P(\mu)\geq\frac16Q_{e^{-\lambda|\cdot|}}(\mu).
$$

指数核的 Fourier 变换为

$$
\frac{2\lambda}{\lambda^2+\xi^2}.
$$

将帽函数在窗口外以端点指数函数延拓，其对偶能量正好是式 (24)。Fourier Cauchy–Schwarz 给出

$$
|z^*C\mu|^2
\leq
Q_{e^{-\lambda|\cdot|}}(\mu)\,z^*Mz.
$$

对 $z$ 取上确界，

$$
Q_{e^{-\lambda|\cdot|}}(\mu)
\geq
(C\mu)^*M^{-1}(C\mu).
$$

乘以 $1/6$ 即得。证毕。

### 定理 4：有限核心的带误差充分条件

如果某个有限阶段满足

$$
\boxed{
\mathcal S_k
-c_D\mathcal U_{k,J,\Omega}
+\varepsilon G_*
\succeq0,
}
$$
<a id="eq-27"></a>
<div class="equation-caption">Equation (27).</div>

那么整个窗口都满足式 (23)。

**证明。**

由式 (15)，

$$
\mathcal S_D\succeq-\varepsilon G_*.
$$

对任意实际读出 $\mu$，令 $c=C\mu$。变分定义和式 (26) 给出

$$
\begin{aligned}
Q_K(\mu)
&\geq c^*\mathcal S_Dc\\
&\geq-\varepsilon c^*G_*c\\
&\geq-\varepsilon Q_P(\mu).
\end{aligned}
$$

证毕。

还有一个关键的完备性结论：

> **如果该固定窗口实际满足 $\mathcal S_D\succeq0$，那么对任意固定 $\varepsilon>0$，式 (27) 最终都会严格成立。**

因为

$$
\mathcal S_k-c_D\mathcal U_{k,J_k,\Omega_k}
\longrightarrow\mathcal S_D,
$$

而 $\varepsilon G_*\succ0$。

因此，允许一个保留尺度的正容差后，即使极限核心存在零特征值，也不会妨碍这个有限步条件最终成立。

---

<a id="section-7-robin-transfer"></a>
## 七、把这个容差直接接到 Robin 不等式

> **Editorial note — inherited Robin bridges remain open.** The author text preserves the same-$n$ decomposition (28), the assertion $\mathcal D(n)\ge0$, and the complete budget term $\mathcal B(T)$. The merged predecessor <code style="overflow-wrap:anywhere">AURIC_FIXED_VARIATIONAL_CORES_SUMMABLE_SCHUR_RECURSION_AND_FINITE_WINDOW_ROBIN_TRANSFER.md</code>, at exact commit <code style="overflow-wrap:anywhere">3919f1b0fbb64e472f77a130b5c422b7d242a56d</code>, records these as `ASSUMED-UNVERIFIED`: the strict optimizer/equality-layer convention, the inactive 5040 boundary, identification of the strict inventory with the same original integer, the full definition of $\mathcal B$, and the weighted insertion of the root correction into the integral are not supplied by `EulerLayerRootCorrection` alone. The exact same-$n$ identity, its sign, and the weighted error needed for (32) must therefore be supplied before (30)–(34) can be read as unconditional Robin conclusions. The PNT-tail estimate and the rational margin calculation are separate conditional components.

> **Editorial note — transfer and tail applicability.** Equations (29)–(34) are restricted to the same original integer $n$ sufficiently large, with $T=\log n>1$, $L=\log T>0$, and $D\ge L$. This restriction applies to Theorem 5 as well as to its asymptotic use: without it, the displayed integral can cross $u=1$ and diverge. Fix positive constants $c,C$ and a cutoff $u_0>1$ for which the cited unconditional PNT estimate holds for every $u\ge u_0$. The bound (31) additionally requires $e^D\ge u_0$; an extension below that cutoff would require separate evidence and is not supplied here. In the choice $D=A(\log T)^2$, fix $A>1/(4c^2)$ independently of $n$, and take the original $n$ sufficiently large that all these domain and cutoff conditions hold. These conditions do not discharge the inherited same-$n$ identity or weighted budget (32); the Robin conclusions (30)–(34) remain conditional on those `ASSUMED-UNVERIFIED` bridges.

保持原整数 $n$，令

$$
T=\log n,\qquad L=\log T,
$$

$$
R(n)=\frac{\sigma(n)}{e^\gamma n\log\log n}.
$$

沿用已建立的实际分解

$$
-\log R(n)
=
\mathcal D(n)+I_\psi(T)+\mathcal B(T),
$$
<a id="eq-28"></a>
<div class="equation-caption">Equation (28).</div>

其中 $\mathcal D(n)\geq0$ 是原整数的实际 Euler 层偏离量，$\mathcal B(T)\geq0$ 是完整库存修正，全部素数指数层仍保留。

其有符号部分为

$$
I_\psi(T)
=
\int_T^\infty
\frac{\log u+1}{u^2\log^2u}
(\psi(u)-u)\,du.
$$

记

$$
Q(T)=\sqrt T\log T\,I_\psi(T).
$$

前面证明的精确传输公式为

$$
\begin{aligned}
Q(T)
={}&-\left(1+\frac1L\right)K(L)\\
&+
L\int_0^\infty
e^{-v/2}
\frac{L+v+2}{(L+v)^3}
K(L+v)\,dv
+E_{\mathrm{arch}}(T),
\end{aligned}
$$
<a id="eq-29"></a>
<div class="equation-caption">Equation (29).</div>

且

$$
E_{\mathrm{arch}}(T)\geq
-\frac{\log(2\pi)}{\sqrt T}.
$$

### 定理 5：相对近正性只消耗 $\varepsilon p_0$ 的主裕量

若式 (23) 在所需窗口 $[0,D]$ 成立，$D\geq L$，则

$$
\boxed{
Q(T)\geq
-(S+\varepsilon p_0)
\left(1+\frac3L+\frac4{L^2}\right)
-\frac{\log(2\pi)}{\sqrt T}
-\mathfrak r(T,D),
}
$$
<a id="eq-30"></a>
<div class="equation-caption">Equation (30).</div>

其中 $\mathfrak r(T,D)$ 是实际远尾的无条件上界。

**证明的关键。**

令

$$
K_\varepsilon=K+\varepsilon P.
$$

窗口正性给出两点约束

$$
|K_\varepsilon(s)|
\leq S+\varepsilon p_0
\qquad(0\leq s\leq D).
$$

将 $K=K_\varepsilon-\varepsilon P$ 代入式 (29)。其中来自 $-\varepsilon P$ 的有限窗口修正为

$$
\varepsilon\left[
\left(1+\frac1L\right)P(L)
-
L\int_0^{D-L}
e^{-v/2}
\frac{L+v+2}{(L+v)^3}
P(L+v)\,dv
\right].
$$

这个量非负。因为 $P$ 正且递减，并且

$$
L\int_0^\infty
e^{-v/2}
\frac{L+v+2}{(L+v)^3}\,dv
<
1+\frac1L.
$$

所以它可以安全地作为有利项保留，或丢去。

其余有限窗口积分的权重总量不超过

$$
\frac2L+\frac4{L^2}.
$$

加上端点项、拱形项和远尾，得到式 (30)。证毕。

### 远尾没有使用 RH

无条件素数定理给出某些固定 $C,c>0$，使

$$
|\psi(u)-u|
\leq Cu e^{-c\sqrt{\log u}}
$$

在充分大 $u$ 上成立。[kskedlaya.org](https://kskedlaya.org/ant/chapter-8.html?utm_source=chatgpt.com)

由它可取

$$
\begin{aligned}
\mathfrak r(T,D)
={}&
L\sqrt T\left(\frac1D+\frac1{D^2}\right)\\
&\times
\left[
\frac{2C}{c^2}(1+c\sqrt D)e^{-c\sqrt D}
+\log(2\pi)e^{-D}
\right].
\end{aligned}
$$
<a id="eq-31"></a>
<div class="equation-caption">Equation (31).</div>

选择

$$
D=A(\log T)^2,
\qquad A>\frac1{4c^2},
$$

就有

$$
\mathfrak r(T,D)\to0.
$$

另一方面，项目的[严格 Euler 库存根修正定理](https://github.com/the-omega-institute/trureturing/blob/08e8767227de53351c42cb35028e01de5e88287d/Blueprint/D5/S3/Arith/Robin/EulerLayerRootCorrection.md)保留了全部高层和严格端点规则。接入前文的积分恒等式后给出

$$
\sqrt T\log T\,\mathcal B(T)
\longrightarrow
C_{\mathrm{inv}}
:=2(\sqrt2-1).
$$
<a id="eq-32"></a>
<div class="equation-caption">Equation (32).</div>

因此只要

$$
\boxed{
\varepsilon(1-\log2)
<
2\sqrt2-4-\gamma+\log(4\pi),
}
$$
<a id="eq-33"></a>
<div class="equation-caption">Equation (33).</div>

就保留了严格的渐近 Robin 裕量。

右侧常数正是经典 Ramanujan–Robin 分析中出现的主裕量；这里并不把它当作新发现的常数。[arxiv.org](https://arxiv.org/pdf/1211.6944?utm_source=chatgpt.com)

### 一个完全不用数值估计的明确选择

可以直接选

$$
\boxed{\varepsilon_*=\frac18.}
$$

确实，由

$$
\sqrt2>\frac75,\qquad
\gamma<\frac34,\qquad
\log(4\pi)>2,
$$

得到

$$
2\sqrt2-4-\gamma+\log(4\pi)>\frac1{20}.
$$

又因为 $\log2>2/3$，

$$
\varepsilon_*(1-\log2)<\frac1{24}.
$$

因此至少保留

$$
\frac1{20}-\frac1{24}
=\frac1{120}>0
$$

的主裕量。

于是得到本轮的具体推进：

$$
\boxed{
\begin{gathered}
D=A(\log\log n)^2,\\[2mm]
\mathcal S_k
-c_D\mathcal U_{k,J,\Omega}
+\frac18G_*
\succeq0
\\[2mm]
\Longrightarrow
\frac{\sigma(n)}
{e^\gamma n\log\log n}<1
\qquad(n\text{ 充分大}).
\end{gathered}
}
$$
<a id="eq-34"></a>
<div class="equation-caption">Equation (34).</div>

这里的前提只涉及一个有限实际矩阵和有限积分误差上界。没有把原整数换成别的对象，也没有删去高素数层。

---

<a id="section-8-zeckendorf-ordering"></a>
## 八、A370630 怎样真正参与递归，以及全局还差什么

> **Editorial note — ordering only.** The exact Zeckendorf source pin is <code style="overflow-wrap:anywhere">9ceb721e13c64eb4b1c71a43238a2b2fc4770093</code> (the full hash is retained in the author URL). Its theorem supplies a permutation/order. To use it for refinement, the fixed dyadic rational list must be explicitly dense, omit already-used nodes, and be inserted into nested finite spaces that contain the coarse grid. This ordering does not provide a uniform bound in $k$ or $D$, nor does it establish the sign condition (27).

项目的 [Zeckendorf 贪心排列定理](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.md)证明，该实际贪心序列遍历每个正整数恰好一次。

它在这里可以承担两个明确作用。

第一，按

$$
n=a_1,a_2,\ldots
$$

遍历需要研究的原整数，并保留每个整数自己的 $T=\log n$、Euler 层和窗口。

第二，固定一个不重复的二进有理点列表

$$
d_1,d_2,\ldots\in(0,1),
$$

按

$$
t_j=Dd_{a_j}
$$

安排窗口中的细化节点。因为 $a_j$ 是排列，这些节点的并集仍然稠密，所以上面的变分收敛和残差收敛定理都适用。

这里，“相邻项恰有一个共同 Zeckendorf 项”仍是该贪心排列的实际规则；它保证了一个合法的遍历来源。**实际关系矩阵的符号则由式 (27) 控制。**

### 定理 6：得到一个有限步条件形式的 RH 等价命题

> **Editorial note — RH criterion boundary.** For the reverse implication, the supplied proof requires a normally convergent actual-zero expansion for $K$ in the relevant domain, a meromorphic Laplace-transform continuation, the exact pole locations, nonzero residues after multiplicity (no cancellation), and an identity-theorem argument linking the transform of the bounded kernel to that continuation. These reverse-direction analytic suppliers remain `ASSUMED-UNVERIFIED` and separate from the forward-direction premise below and from the inherited Robin decomposition (28) and budget limit (32). The cited six links do not establish these manuscript-specific bridges. Consequently (35) is retained as the author's proposed equivalence, conditional on both directions' premises; it does not prove RH, and the all-window matrix inequality remains unproved.

> **Editorial note — forward RH premise.** The forward direction $\mathrm{RH}\Rightarrow K\text{ positive semidefinite}\Rightarrow\mathcal S_D\succeq0$ requires an actual-zero expansion equal to this arithmetic $K$, with normal convergence in the domain needed to pass to finite Gram forms and with the coefficients/signs that make RH imply positivity. Neither v37's block algebra nor the predecessor's finite-core discussion supplies that analytic identification. This actual-zero-expansion/normal-convergence and RH-to-positive-core premise remains `ASSUMED-UNVERIFIED`; the fixed-window convergence and strict tolerance argument use it conditionally. It is distinct from the reverse Laplace/pole/multiplicity/noncancellation premises in the adjacent note.

固定

$$
\varepsilon_*=\frac18.
$$

对每个正整数窗口长度 $D$，按上述方式固定粗网格和稠密细化。则：

$$
\boxed{
\mathrm{RH}
\iff
\forall D\in\mathbb N_{>0},\
\exists\text{有限 }k,J,\Omega:
\quad
\mathcal S_k-c_D\mathcal U_{k,J,\Omega}
+\frac18G_*\succeq0.
}
$$
<a id="eq-35"></a>
<div class="equation-caption">Equation (35).</div>

**证明。**

若 RH 成立，实际核 $K$ 全局正定，因此每个窗口的

$$
\mathcal S_D\succeq0.
$$

由式 (16) 的收敛和 $G_*\succ0$，每个固定窗口最终满足式 (35) 中的有限条件。

反过来，若每个整数窗口都有这样的有限条件，由定理 4，

$$
K+\frac18P
$$

在所有有限窗口上正定，从而在整个实线上正定。两点测试给出

$$
\left|K(t)+\frac18P(t)\right|
\leq S+\frac18p_0.
$$

所以

$$
|K(t)|\leq S+\frac14p_0
\qquad(t\in\mathbb R).
$$

实际核因而全局有界。

而实际零点展开的 Laplace 变换具有极点

$$
s=\rho-\frac12,
$$

对应留数为

$$
\frac{\operatorname{mult}(\rho)}{\rho(1-\rho)}\ne0.
$$

有界的 $K$ 使其 Laplace 变换在 $\Re s>0$ 解析，因此不能有 $\Re\rho>1/2$ 的零点；再用函数方程对称性，全部非平凡零点只能位于 $\Re\rho=1/2$。证毕。

---

<a id="section-final-position"></a>
## 本轮推进到的准确位置

> **Editorial note — delivery scope.** The displayed chain is the supplied paper's conditional program. The implementation establishes a faithful standalone manuscript and records the local analytic checks and the unresolved bridges; it does not claim a global positive core, a Robin proof, RH, native physical realization, or a fresh Lean/kernel certification.

现在已经证明了：

$$
\boxed{
\begin{aligned}
&\text{实际细节空间严格正}\\
&\Longrightarrow
\text{误差可以作酉守恒递归}\\
&\Longrightarrow
\text{有显式几何尾界}\\
&\Longrightarrow
\text{实际有限核心有趋零的残差下界}\\
&\Longrightarrow
\text{允许固定相对容差的 Robin 充分条件。}
\end{aligned}
}
$$

下一步需要攻击的算术命题已经非常具体：

$$
\boxed{
\forall D,\quad
\exists\text{有限 }k,J,\Omega:
\quad
\mathcal S_k-c_D\mathcal U_{k,J,\Omega}
+\frac18G_*\succeq0.
}
$$

**递归表示、归一化、酉守恒和剩余误差的收敛，这一轮都已经获得了严格控制；仍未证明的是，上述实际算术不等式对不断扩大的全部窗口成立。** 这正是继续证明 RH 时需要新增的全局估计。
