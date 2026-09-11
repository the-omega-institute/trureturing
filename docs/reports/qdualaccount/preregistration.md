# §17.2 对偶账全额条款：陈述与预登记

产地：Codex 主循环，lean4 skill，单点实施与自查；独立评审由调用方负责。
源 atom：`observer-quantum-v1` / `1e28ba01c5fc682ea2d77c4eb6673e9fb3de4ca5b6fbd2f26553e26b737a6cd0`。

精确陈述（先于数值探针和证明）：以下使用已有 `DensityState`、`RankOneContext`、
`IsRecordMeasurement`、`overlap`、`unreadState`、`vonNeumannEntropy`、
`quantumRelativeEntropy` 与 `gibbsState`。`sigma` 由等式约束为真实 X 捏合输出，
不是独立的熵参数。共轭性取互无偏条件，涵盖 Fourier 共轭基。

```lean
theorem dual_account_full
    {d : ℕ} [NeZero d] (Z X : RankOneContext d)
    (hZ : IsRecordMeasurement Z.projector)
    (hX : IsRecordMeasurement X.projector)
    (hZX : ∀ j k, overlap Z X j k = (d : ℝ)⁻¹)
    (rho sigma : DensityState (Fin d))
    (hFixed : unreadState Z.projector rho.1 = rho.1)
    (hPinch : unreadState X.projector rho.1 = sigma.1) :
    let omega := gibbsState (0 : CStarMatrix (Fin d) (Fin d) ℂ)
      (IsSelfAdjoint.zero _)
    sigma = omega ∧
      quantumRelativeEntropy rho sigma = quantumRelativeEntropy rho omega ∧
      quantumRelativeEntropy rho sigma = Real.log d - vonNeumannEntropy rho ∧
      vonNeumannEntropy sigma - vonNeumannEntropy rho =
        quantumRelativeEntropy rho sigma ∧
      (unreadState X.projector rho.1 = rho.1 ↔ rho = omega)
```

自由量是 `D(rho || omega)`，不定义成 `log d - S(rho)` 再以 rfl 交付。
税是 `D(rho || sigma)`；以上同时将它连接到真实捏合和被杀相干的熵差。
“免双税”按用户明文解释为两个捏合都不改变态。
全体态（故也包括任意选择轨迹逐点）另须证明：

```lean
theorem entropy_freedom_segment
    {d : ℕ} [NeZero d] (rho : DensityState (Fin d)) :
    let omega := gibbsState (0 : CStarMatrix (Fin d) (Fin d) ℂ)
      (IsSelfAdjoint.zero _)
    0 ≤ vonNeumannEntropy rho ∧
      0 ≤ quantumRelativeEntropy rho omega ∧
      vonNeumannEntropy rho + quantumRelativeEntropy rho omega = Real.log d
```

准入预登记 v1：拟议 `escape-witness` 候选为
`conjugate_pinching_eq_uniform`：Z 不变态经 X 捏合等于 I/d。
**证明前的仓内检索已否决该候选见证**：
`MutuallyUnbiasedDiagonalPlanes.mutually_unbiased_diagonal_planes` 的末个 iff
直接给出双捏合退极化，代入 Z 不变与 trace=1 即得；不能重证充当新内容。
`GibbsVariationalIdentity.entropy_uniform_identity` 亦直接给出全体态的守恒轴。

因此在探针前登记 v2：预计 `proof_shape: bind-only`，
`admission_basis: atom-required-bridge`，`utility: none`。
新增边是实际互无偏捏合输出 → Gibbs 极大混态 → 相对熵税/自由/熵差，
atom 明文要求该边；具名消费者为本模块 `dual_account_full`，
其前置 `conjugate_pinching_eq_uniform` 只作同模块引理。
`entropy_freedom_segment` 是源 atom 相图子句的伴随结果，与同一自由量相连。
若核验/门不接受该依据，则交付证明及该阻塞，不改标签制造新内容。
全部量化维数任意、谱任意，无枚举器/检查器/数值归约/有限实例，故 utility 为 none。

数值判据：固定种子；d=1,2,3,4,5,8，含纯态、均匀态、非均匀混态与随机谱。
身份对照逐项核对 d=2 的 diag(1,0)、diag(3/4,1/4)、I/2 的已知矩阵、熵、税、自由。
判别力对照仅把税=自由改为税=-自由；纯 Z 态必须报错。
另检验去掉互无偏条件（X=Z）的故意错误命题必须报错。
成立标准为原式残差小于 1e-10，身份对照逐项通过，两种错误均被抓住。
数值读数不是 kernel 证明；原命题若翻，必须另给 kernel 反例。

落点预查：Quantum 域已在 Meta/domains.yaml 注册，stratum=S3；
D5/S3/Quantum/Divergence 现有 8 个 Lean 单元，新增后 9 < 48；
Blueprint 同目录现有 8 个 scribe 单元，md 不计；全部拟用前置为 generality G。

停止判据：完整精确陈述及指定门链通过为“成”；原陈述的 kernel 反例为“翻”；
否则为 blocked，记录已完成部分、失败路线与最锐剩余义务。不得以弱命题代替目标。
