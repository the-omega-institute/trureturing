## 31.13 建议形式化模块

建议按以下顺序进入 Lean：

1. `HermitianTracelessDimension`
   \[
   \dim_{\mathbb R}\operatorname{Herm}_d^0=d^2-1.
   \]

2. `BasisDephasingOrthogonalProjection`
   \[
   \mathbb E_{\mathcal B}^2=\mathbb E_{\mathcal B}
   =
   \mathbb E_{\mathcal B}^*.
   \]

3. `SingleContextVisibleRemainderDimension`
   \[
   \dim\mathcal D_{\mathcal B}^0=d-1,
   \quad
   \dim R_{\mathcal B}=d^2-d.
   \]

4. `PureStateProbabilityFiber`
   内点纤维
   \[
   q_{\mathcal B}^{-1}(p)\cong\mathbb T^{d-1}.
   \]

5. `MUBDiagonalSubspaceOrthogonal`
   \[
   \mathcal B\perp_{\mathrm{MUB}}\mathcal C
   \iff
   \mathcal D_{\mathcal B}^0
   \perp
   \mathcal D_{\mathcal C}^0.
   \]

6. `MUBDephasingComposition`
   \[
   \mathbb E_{\mathcal B}\mathbb E_{\mathcal C}(X)
   =
   \operatorname{Tr}(X)I/d.
   \]

7. `SharpIncompatibilityCommutatorSum`
   \[
   \sum_{jk}\|[P_j,Q_k]\|_2^2
   =
   2(d-1)\mathcal I.
   \]

8. `MUBTowerDimension`
   \[
   \dim R_m=(d-1)(d+1-m).
   \]

9. `MUBProbabilityPythagoras`
   \[
   \operatorname{Tr}\rho^2-\frac1d
   =
   \sum_{\ell,j}(p_{\ell j}-1/d)^2+r_m^{(2)}(\rho).
   \]

10. `CompleteMUBTomography`
    \[
    \rho
    =
    I/d+\sum_{\ell,j}(p_{\ell j}-1/d)P_{\ell j}.
    \]

11. `ResidualControlsNaturality`
    \[
    \partial_mF(X)
    \le
    L_F\|(I-P_m)X\|_2.
    \]

12. `NaturalityDefectComposition`
    \[
    \partial_m(FG)
    \le
    \partial_mF\circ G
    +
    L_m(F)\partial_mG.
    \]

13. `RepeatedDephasingEntropyProduction`
    \[
    S(\rho_{n+1})-S(\rho_n)
    =
    D(U\rho_nU^*\|
    \mathbb E_{\mathcal B}(U\rho_nU^*)).
    \]

14. `RepeatedDephasingUnistochastic`
    \[
    p_{n+1}=Tp_n,
    \qquad
    T_{kj}=|\langle b_k,Ub_j\rangle|^2.
    \]

MUB 完整集的存在应在素数幂维数中通过具名经典接口接入；一般维数中不得无条件实例化。

---

## 31.14 最终统一式

本节得到一个比“概率是投影”更精确的层次：

\[
\boxed{
\text{量子态}
=
\text{最大混合原点}
+
\text{全部算子 Hilbert 方向}.
}
\]

\[
\boxed{
\text{一个测量坐标系}
=
\text{到一个 }(d-1)\text{-维经典对角平面的正交投影}.
}
\]

\[
\boxed{
\text{概率}
=
\text{该对角投影的坐标}.
}
\]

\[
\boxed{
\text{相干}
=
\text{仍留在其正交余空间中的状态分量}.
}
\]

\[
\boxed{
\text{MUB}
=
\text{彼此正交、冗余为零的局部经典坐标平面}.
}
\]

\[
\boxed{
\text{完整 MUB 层析}
=
\text{用 }d+1\text{ 个局部经典对角完成全部量子状态方向}.
}
\]

\[
\boxed{
\text{自然性缺陷}
\le
\text{尚未被坐标塔捕获的余质量}.
}
\]

\[
\boxed{
\text{重复测量熵增}
=
\text{每轮投影删除的相干相对熵之和}.
}
\]

而最重要的修正是：

\[
\boxed{
\text{锐利不兼容}
\neq
\text{去相干顺序缺陷}
\neq
\text{层析冗余}
\neq
\text{全局 contextuality}.
}
\]

因此，量子力学不能只解释为“多个投影不交换”，也不能只解释为“概率来自投影”。更完整的结构是：

\[
\boxed{
\text{量子力学}
=
\text{一族局部经典对角坐标}
+
\text{这些坐标的余相干}
+
\text{它们之间的互补几何}
+
\text{无法由单一全局经典坐标同时实现的拼接结构}.
}
\]

在这个意义上，坐标系、概率、熵、时间、逃逸率、Hilbert 空间与对角化确实属于同一个研究对象的不同投影；但它们只有在各自的类型、缺陷量与完成条件被严格区分以后，才构成可检验的新数学，而不是词语上的统一。

## 31.15 参考接口与严格非主张

参考接口：

- I. D. Ivanović, *Geometrical description of quantal state determination*, 1981.
- W. K. Wootters and B. D. Fields, *Optimal state-determination by mutually unbiased measurements*, 1989.
- R. B. A. Adamson and A. M. Steinberg, *Improving Quantum State Estimation with Mutually Unbiased Bases*, 2010.
- D. McNulty and S. Weigert, *Mutually Unbiased Bases in Composite Dimensions — A Review*, 2026.
- J. H. Selby et al., *Contextuality without Incompatibility*, 2023.

严格非主张：

1. 本节不声称一般维数都存在完整 \(d+1\) 组 MUB。
2. 本节不把层析精化指标 \(m\) 等同于物理时间。
3. 本节不把 Hilbert–Schmidt 余质量等同于 Shannon 熵、von Neumann 熵或任意操作性资源单调量。
4. 本节不把 dephasing 通道交换当作锐利测量兼容性。
5. 本节不把 pairwise measurement incompatibility 等同于 generalized contextuality。
6. 本节不把重复投影模型中的熵增解释为所有封闭量子宇宙的基本时间箭头。
7. 本节不从有限维层析完成推出无限维正常状态空间的自动完成。
8. 本节新增结论均为纸面定理；在 Lean proof term、依赖闭包、admission 与冻结收据齐备前不得标记为 `Closed`。
