# Monster 短支持代表的有限二次自旋数据

本页把 PR [#10310](https://github.com/the-omega-institute/trureturing/pull/10310) 中的有限 Monster 标签段落接到可核验的 Lean 声明。它只处理

\[
F=\mathbf F_2,\qquad E=F^{\mathrm{Fin}\,3},\qquad
\mathrm{Label}=E\times E,
\]

以及七个非零地面截面在六比特标签空间中的关系。这里的二次函数是有限标签上的

\[
Q(g,\xi)=g_0\xi_0+g_1\xi_1+g_2\xi_2.
\]

它是有限极化数据，不能单独解释为 VOA 模的最低共形权。

## 已形式化的声明

源码为 [`D5/S3/VertexAlgebra/MonsterShortSupportSpin.lean`](../../../D5/S3/VertexAlgebra/MonsterShortSupportSpin.lean)。

* `labelQuadratic` 独立定义在 `Label` 上；它不展开 `fullMap`，因此不是把支持谓词改名。
* `labelQuadratic_groundSection` 证明
  \(Q(s_f(g))=f(g,g)\)。因此 `labelQuadratic_groundSection_nonzero` 使用
  `IsSignTable.diagonal` 得到所有非零地面截面的奇偶值为 1。
* `labelQuadratic_groundSection_polar` 使用
  `IsSignTable.opposite` 证明不同非零地面截面的极化配对为 1。这是二次律真正消耗的符号表几何。
* `shortWeight` 将七段支持大小公开为可复用 API；唯一支持至多 3 的结论继续由
  `MonsterShortSupport.unique_short_support` 提供。
* `labelQuadratic_fullMap` 将七段系数和的二次值形式化为
  \(\binom{\operatorname{shortWeight}(c)+1}{2}\bmod 2\)。证明先对有限支持集合归纳，
  再使用每个地面截面的二次值为 1、不同截面的极化值为 1，以及七段补集关系。

这些声明的 `#print axioms` 只包含 Lean 的 `propext`、`Classical.choice` 和 `Quot.sound`，没有 `sorryAx`、自定义公理或 `native_decide`。

## 尚未冒领的部分

本轮没有把

\[
Q(\operatorname{fullMap}(f,c))
 = \binom{\operatorname{shortWeight}(c)+1}{2}\pmod 2
\]

作为已冻结定理。要完成该式，还需把七个截面的逐项极化展开和支持计数连接起来；当前 Lean 结果已经提供了其两个负载接口（单截面值和两截面极化），但没有把这一步隐藏在未检查的 `simp` 或有限枚举中。也没有声明模块存在、\(M_x\boxtimes M_y\simeq M_{x+y}\)、最低共形权、非零 OPE 系数、Monster 作用或完整 VOA。

因此，\(Q/2\) 作为共形自旋模 1 的解释仍然带条件：必须先给出满足 PR #10310 所列强有理、CFT 型、自对偶等前提的实际 VOA 及其模块族。

## Fano 闭包的首个形式化关联前提

PR #10310 §30.1 的 Fano 闭包论证首先需要不同块不能共含两个不同点。
`MonsterFanoReconstruction.block_intersection_le_one` 将这一关联前提形式化：
对七点集上的有限块族，若任意不同点对恰属于一个块，则任意不同的块
$A,B$ 满足 $|A\cap B|\leq 1$。证明从交集中的两个不同点出发，分别以
$A$、$B$ 见证经过该点对的唯一块，得到 $A=B$，与不同块的前提矛盾。
这里不假设块有三个点，不假设标签加法或对称差补集闭包，也不枚举块族。

该声明位于 `D5/S3/VertexAlgebra/MonsterFanoReconstruction.lean`；
它只给出有限关联界，单独并不推出 Fano 闭包。三元性和七点条件参与后续
闭包论证，不能从这个界删去其余义务。Basak 2017 提供八元数与扭群代数背景，
van Ekeren–Möller–Scheithauer 2020 提供满足其假设时的 VOA 扩展接口；
两者都不把此关联界变成模块存在、融合律、最低共形权、OPE 或完整 CFT 的证明。
相关来源沿用本页参考文献；既有 VOA、融合与共形自旋的未解边界保持不变。

## 理论问卷（下一轮入口）

| 问题 | 当前状态 | 需要的可审查证据 |
| --- | --- | --- |
| 七段系数是否有唯一短支持代表？ | **已形式化** | `MonsterShortSupport.unique_short_support`；支持界为 3。 |
| 地面截面是否形成统一的有限二次数据？ | **已形式化** | `labelQuadratic_groundSection` 与 `labelQuadratic_groundSection_polar`。 |
| 全 `fullMap` 二次律是否成立？ | **已形式化** | `MonsterShortSupportSpin.labelQuadratic_fullMap`；证明消耗七段支持集合归纳、单截面值和两两极化值。 |
| 标签是否已经是 VOA 模的索引？ | **开放** | 具体模块构造及模块公理；有限标签本身不提供此证据。 |
| 标签加法是否是 VOA 融合？ | **开放** | 实际 intertwiner、结合/编织相容性和非零 OPE 见证。 |
| `Q/2` 是否是最低共形权模 1？ | **开放** | 真实 `L₀` 谱与标签到模块的识别；不能由有限二次函数推出。 |
| 相关文献中的简单流扩展能否实例化本标签？ | **开放** | 把 [VEMS20] 的假设逐项映射到仓内构造，而不是只引用其背景。 |

## 参考文献与定位

* [PR #10310](https://github.com/the-omega-institute/trureturing/pull/10310)：Monster-defect 与 fusion-chain 理论卷；本页只把其中可独立验证的有限标签部分形式化。
* [Basak 2017, *The octonions as a twisted group algebra*](https://arxiv.org/abs/1702.05705)：符号表/扭群代数背景；不提供本页的 VOA 实现。
* [van Ekeren–Möller–Scheithauer 2020, *Construction and Classification of Holomorphic Vertex Operator Algebras*](https://doi.org/10.1515/crelle-2017-0046)：简单流扩展接口及其假设；这里只作后续构造的文献定位。
* [Kirillov 2002, *Modular categories and orbifold models*](https://arxiv.org/abs/math/0104242)：实际模块范畴存在后才适用的范畴背景。

仓内对应的来源定位文件为 [`Library/VertexAlgebra/basak2017monstercharactercarry.md`](../../../Library/VertexAlgebra/basak2017monstercharactercarry.md)、[`Library/VertexAlgebra/vanekeren2020atomicmonstercompletion.md`](../../../Library/VertexAlgebra/vanekeren2020atomicmonstercompletion.md) 和 [`Library/VertexAlgebra/carnahan2016mixeddefectselection.md`](../../../Library/VertexAlgebra/carnahan2016mixeddefectselection.md)。
