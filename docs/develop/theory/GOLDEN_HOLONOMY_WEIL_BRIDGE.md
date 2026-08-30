# 黄金 Holonomy 与 Weil 奇校正桥
## 素数顺序曲率、观察起源规范与离线零点奇偶能量

**文档地位。** 本文件与两个 Lean 节点属于同一候选增量。合并以后，数学真值以对应 GID 和 Lean 声明为准。本文负责说明定义来源、精确边界和下一批开放桥，不把路线图写成已证结论。

**基线。** 本轮建立在 `dev` 中已有的黄金观察器路线、带记忆素数观察器纸面源、Weil 卷积平方轨道分解和内部曲率判据之上。仓库已经有：

- prime 和 Archimedean jump energy 的精确显式公式分解；
- 临界线卷积平方项的逐项非负性；
- 离线四点轨道总贡献为实数；
- 复频率卷积平方因子分解；
- interior curvature 消失当且仅当全部非平凡零点位于临界线。

本轮没有证明 RH，也没有证明黄金局部因子经过全部 ζ 因子抽取后一定趋平。它完成两端的有限代数真源，并把剩余桥压缩成一个明确的支配问题。

---

# 1. 两条路线的共同目标

此前得到的总构造为：

\[
\mathbf U_{r,p}(s)
=
\begin{pmatrix}
\mathbf F & (L_p^{\langle r\rangle}(s)-1)v_p\\
0 & L_p^{\langle r\rangle}(s)
\end{pmatrix}.
\]

标量通道交换。记忆通道保存素数观察词的顺序信息。

将 Fibonacci 记忆投影到稳定特征通道后，稳定乘子记为：

\[
a=-\varphi^{-1}.
\]

对一个局部因子，记：

\[
\lambda_p=L_p^{\langle r\rangle}(s),
\qquad
b_p=b_{r,p}^{-}(s).
\]

稳定通道更新成为：

\[
\boxed{
U_p(x,z)=(ax+b_pz,\lambda_pz).
}
\]

本轮形式化的两端是：

\[
\boxed{
\text{prime side}:
\quad
C_{p,q}=U_qU_p-U_pU_q,
}
\]

以及：

\[
\boxed{
\text{zero side}:
\quad
Q_{\operatorname{orb}(\rho)}
=E_{\rho}^{\mathrm{even}}-E_{\rho}^{\mathrm{odd}}.
}
\]

其中两个能量都非负。真正的下一步是证明 prime-side 的规范约化二阶曲率可以支配 zero-side 的离线奇能量，并证明前者随抽取深度消失。

---

# 2. 已形式化的 prime-side 定理

Lean GID：

`D5/S3/PrimeObserver/GoldenHolonomy/PrimeSwapCurvature`

主声明：

`D5.S3.PrimeObserver.GoldenHolonomy.PrimeSwapCurvature.prime_swap_curvature_spec`

两个更新顺序满足：

\[
U_qU_p(x,z)
=
\bigl(a^2x+(ab_p+b_q\lambda_p)z,
\lambda_q\lambda_pz\bigr),
\]

\[
U_pU_q(x,z)
=
\bigl(a^2x+(ab_q+b_p\lambda_q)z,
\lambda_p\lambda_qz\bigr).
\]

因此标量坐标完全相同，而记忆坐标之差为：

\[
\boxed{
C_{p,q}z,
}
\]

其中：

\[
\boxed{
C_{p,q}
=(a-\lambda_q)b_p-(a-\lambda_p)b_q.
}
\]

Lean 同时证明：

\[
C_{q,p}=-C_{p,q}.
\]

改变共同记忆原点 \(c\) 时：

\[
\boxed{
b_p\mapsto b_p+(a-\lambda_p)c.
}
\]

Lean 证明 \(C_{p,q}\) 在该变换下不变。所以单个 \(b_p\) 不是对象层量，交换曲率才是规范不变量。

远离共振：

\[
a-\lambda_p\ne0,
\]

定义局部观察起源估计：

\[
\boxed{
c_p=\frac{b_p}{a-\lambda_p}.
}
\]

Lean 证明精确分解：

\[
\boxed{
C_{p,q}
=(a-\lambda_p)(a-\lambda_q)(c_p-c_q).
}
\]

因此在两个局部通道都非共振时：

\[
\boxed{
C_{p,q}=0
\iff
c_p=c_q.
}
\]

这给出一个比“局部记忆振幅趋零”更自然的完成判据。所有 \(b_p\) 可以保留一个共同 archive，只要它们最终来自同一个 coboundary 原点：

\[
b_p=(a-\lambda_p)c.
\]

此时顺序 holonomy 已经消失。

---

# 3. 已形式化的 zero-side 定理

Lean GID：

`D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition`

主声明：

`D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition.off_line_orbit_parity_decomposition`

对 `ZeroData` 中一个非实、离线的零点索引 \(n\)，记：

\[
z=\gamma_n,
\qquad
A=\widehat f(z),
\qquad
B=\widehat f(\overline z).
\]

定义偶、奇谱通道：

\[
\boxed{
A_{\mathrm{even}}=\frac{A+B}{2},
}
\]

\[
\boxed{
A_{\mathrm{odd}}=\frac{A-B}{2}.
}
\]

仓库已有复频率卷积平方恒等式：

\[
\widehat{f*\widetilde f}(z)=A\overline B.
\]

本轮 Lean 节点补上：

\[
\boxed{
\Re(A\overline B)
=|A_{\mathrm{even}}|^2-|A_{\mathrm{odd}}|^2.
}
\]

仓库已有离线四点轨道公式：

\[
Q_{\operatorname{orb}(\rho)}(f)
=4m_\rho\Re(A\overline B).
\]

所以本轮机器证明：

\[
\boxed{
Q_{\operatorname{orb}(\rho)}(f)
=E_{\rho}^{\mathrm{even}}(f)
-E_{\rho}^{\mathrm{odd}}(f),
}
\]

其中：

\[
E_{\rho}^{\mathrm{even}}(f)
=4m_\rho|A_{\mathrm{even}}|^2\ge0,
\]

\[
E_{\rho}^{\mathrm{odd}}(f)
=4m_\rho|A_{\mathrm{odd}}|^2\ge0.
\]

因此：

\[
\boxed{
Q_{\operatorname{orb}(\rho)}(f)
+E_{\rho}^{\mathrm{odd}}(f)
=E_{\rho}^{\mathrm{even}}(f)\ge0.
}
\]

这给出了离线轨道的规范正校正。该校正由复频率对的反对称通道独立构造，没有通过目标正性倒推定义。

---

# 4. 两端现在精确同形

prime side 的顺序奇量为：

\[
C_{p,q}
=(a-\lambda_p)(a-\lambda_q)(c_p-c_q).
\]

zero side 的谱奇量为：

\[
A_{\mathrm{odd}}
=\frac{\widehat f(z)-\widehat f(\overline z)}{2}.
\]

二者都满足：

1. 交换相应的两个端点后变号；
2. 线性标量完成不能以一阶不变量读取该符号；
3. 第一个规范非负对象是其 Hermitian 平方；
4. 该平方充当完成校正。

所以当前候选应写为两个正算子族：

\[
\boxed{
\mathcal V_{r,L,N}^{\mathrm{hol}}
=\sum_{p,q}C_{r;p,q}^{*}\Gamma_\varphi C_{r;p,q},
}
\]

以及：

\[
\boxed{
\mathcal O_{L,N,T}^{\mathrm{off}}
=\sum_{\rho\ \mathrm{off-line}}
4m_\rho
|A_{\mathrm{odd},\rho}\rangle
\langle A_{\mathrm{odd},\rho}|.
}
\]

本轮没有定义无限和，也没有声明两个算子相等。有限窗口、有限 Galerkin 深度和有限零点截断应先分别建立。

---

# 5. 新的中心开放桥

固定空间窗口 \(L\) 和有限测试深度 \(N\)。由于支撑限制，prime explicit formula 只读取有限个活动素数幂。对这些活动通道，目标定义为：

\[
\mathcal V_{r,L,N}^{\mathrm{hol}}
=\frac{1}{2W_{r,L}}
\sum_{p,q}C_{r;p,q}^{*}\Gamma_\varphi C_{r;p,q}.
\]

黄金稳定乘子给出自然 Lyapunov 权：

\[
\Gamma_\varphi
=\sum_{j\ge0}\varphi^{-2j}=\varphi.
\]

第一项开放义务是把当前标量稳定通道提升到实际有限测试空间上的算子。

随后需要证明抽取平坦化：

\[
\boxed{
\forall L,N,
\qquad
\|\mathcal V_{r,L,N}^{\mathrm{hol}}\|_{\mathrm{op}}
\longrightarrow0
\quad(r\to\infty).
}
\]

仅证明 \(b_{r,p}\to0\) 还不够。观察起源因子化显示还必须控制共振条件数：

\[
\boxed{
\chi_{r,L}
=\max_{p\in\mathcal P_L}|a-\lambda_{r,p}|^{-1}.
}
\]

一个可操作的充分条件是：

\[
\chi_{r,L}
\max_{p,q\in\mathcal P_L}|C_{r;p,q}|
\longrightarrow0.
\]

核心谱桥应写成有限支配：

\[
\boxed{
P_{L,N}\mathcal O_{L,T}^{\mathrm{off}}P_{L,N}
\preceq
C_{L,N,T}\mathcal V_{r,L,N}^{\mathrm{hol}}
+\varepsilon_{r,L,N,T}I.
}
\]

要求：

\[
\varepsilon_{r,L,N,T}\to0
\quad(r\to\infty),
\]

随后再依次完成：

\[
T\to\infty,
\qquad
N\to\infty,
\qquad
L\to\infty.
\]

若该支配成立并且 prime-side holonomy 能量趋零，则离线奇能量必须消失。若测试空间能分离每个离线轨道，内部曲率随之为零，最后由仓库已有 `InteriorCurvatureCriterion` 得到 RH。

---

# 6. 严格非主张

本轮不主张：

1. 已经构造 \(L_p^{\langle r\rangle}\) 的全部抽取塔；
2. 已经证明交换曲率随 \(r\) 趋零；
3. 已经证明 prime holonomy 支配离线奇能量；
4. 已经证明测试类对全部离线轨道完备；
5. 已经构造 canonical `ZeroData` inhabitant；
6. 已经证明 RH。

本轮机器层完成的是：

\[
\boxed{
\text{prime-side 顺序缺陷的规范不变量和零曲率判据},
}
\]

以及：

\[
\boxed{
\text{zero-side 离线轨道的偶能量减奇能量分解}.
}
\]

---

# 7. 后续形式化顺序

1. `GoldenPrimeMemoryInstantiation`：将 \(a=-\varphi^{-1}\)、\(b_{r,p}^{-}\) 和 \(L_p^{\langle r\rangle}\) 接入 `PrimeSwapCurvature`；
2. `FiniteHolonomyEnergy`：在固定活动素数幂窗口上定义有限正半定 holonomy Gram 算子；
3. `ExtractionCurvatureBound`：把现有 residual local factor 上界运输到交换曲率上；
4. `ResonanceConditionedFlattening`：加入 \(|a-\lambda_{r,p}|^{-1}\) 的统一控制；
5. `FiniteOffLineOddEnergy`：对有限对称零点 cutoff 求和本轮逐轨道奇校正；
6. `PrimeArchimedeanHolonomyDomination`：建立两端之间的有限 Galerkin 支配；
7. `HolonomySqueezeToInteriorCurvature`：在全部误差预算闭合后组合到内部曲率消失判据。

其中第 6 项是新的 hard heart。前五项都应产生独立的有限失败证书，不应直接以 RH 为目标写一个空洞 wrapper。

---

# 8. 本轮之后允许的真源推理

机器真源现在允许我们无条件使用：

\[
\boxed{
\text{顺序差异不等于共同记忆 archive。}
}
\]

共同 archive 是 coboundary。只有不同 prime channel 对观察起源的判断不一致时，交换曲率才非零。

机器真源也允许无条件使用：

\[
\boxed{
\text{离线轨道的危险符号全部集中在奇谱通道。}
}
\]

一个离线轨道的实贡献精确等于非负偶能量减去非负奇能量。

所以两条路线真正需要识别的对象已经唯一化：

\[
\boxed{
\text{prime-side 规范约化交换曲率平方}
\quad\longleftrightarrow\quad
\text{zero-side 离线奇谱能量}.
}
\]

任何未来桥若不经过这两个已固定对象，就需要说明它增加了什么新的 escape depth，而不是仅换了一套观察坐标。
