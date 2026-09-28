---
bibkey: sutherland2021chebotarev_erdos699_cubic
authors: Andrew V. Sutherland
year: 2021
title: "Chebotarev density and cubic transport for Erdős 699"
url: https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf
claim: Classical density theorem applied after explicit radical-independence and field-intersection proofs; no claim of unrestricted Erdős 699 closure.
strata_touched: []
license: citation-only
triage: anchor
---

# 三次特征、广义二面体群与任意二次符号图

入口：issue #9670，Draft PR #9769。
完整新书面证明和标准库检查器：
`tools/scripts/agent/openproblem/erdos699-cubic-kummer-transport.py`。

## 1. 实际读取的经典输入

A. V. Sutherland, MIT 18.785, Fall 2021, Lecture 28, Theorem 28.9，印刷第6页。
本轮实际读取了解析文本及该页截图。准确结论是：有限 Galois 扩张的群 G 中，若 C 共轭稳定，则非分歧 Frobenius 共轭类落在 C 内的素数集合具有 Dirichlet 密度 |C|/|G|。本轮使用这个无条件定理，没有 GRH 假设；没有把有限素数采样频率当成密度。

经典根式背景另读取 Stacks Project 的 09I6/09DX：
https://stacks.math.columbia.edu/tag/09I6
https://stacks.math.columbia.edu/tag/09DX
以及官方 Mathlib 文档：
https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/KummerExtension.html

Stacks 的循环 Kummer 设置不直接证明本轮多根式满秩；也没有使用同节另外的子扩张引理。本轮用范数和有限线性代数补齐多根式独立性。

## 2. 原始列结论与外部定理严格分开

有限 S 若满足每个 p≡13(mod24)、2不是模p三次幂、3是模p三次幂，且不同支撑素数在彼此域中互为三次幂，则其全部列 j=2^b∏p^a_p≥4 对所有n≥2j满足i=3共同奇素数结论。

这个新输运步骤只用有限域三阶特征标、继承的原始参数接口、准确gcd收缩和纯2的四阶部分，不需要Chebotarev。实例S={661,853,2389}的二次符号为(+,+,−)，旧二次同步条件不成立；源码保留了全部三次根见证及原参数对照。

Chebotarev只用于证明每个合格S可按任意指定的二次符号向量继续增加素数，以及相应密度。原始二项式反例的规范化/mixed-support书面前提仍须独立复核和形式化。

## 3. 没有假设独立性的相容性证明

令K=Q(ζ3)、L=K(∛2,∛3,∛p：p∈S)。若一个素数幂乘积在K中是三次幂，取K/Q范数可知各指数乘2后均被3整除。因此这些有理素数的三次方类独立。

Gal(L/K)嵌入(C3)^(|S|+2)。若像为真子空间，一个非零消去泛函会产生属于K的根式乘积，与范数独立性矛盾。故该嵌入满射。

复共轭按反演作用于这个三次群，所以Gal(L/Q)=V⋊C2。换位子[τ,σ_v]=σ_(−2v)=σ_v，导出子群恰为V。因此最大阿贝尔子域仅为K。

对M=24∏p及F=Q(ζM)，F/Q阿贝尔且含K，得到L∩F=K。此后才能把模M的CRT条件和独立的三次根式Frobenius条件一起施加。

## 4. 密度的准确计数

旧支撑大小m，指定每个新旧二次符号ε_p。在模p的三次幂子群中，每个二次符号各有(p−1)/6个单位类。再指定q≡13(mod24)。

在根式群中，要求∛2有非平凡Frobenius，∛3和全部∛p被固定。共有两个互为逆的元素，在合成群中形成两元共轭类。CRT选项给出互不相交的分圆分量。

合成群阶为3^(m+2)·8∏(p−1)，所选元素数为2∏((p−1)/6)，所以扩展集合的Dirichlet密度是1/(36·18^m)。每个符号向量都成立，未限制为同号。

这得到任意可数对称±1图的递增素数实现，同时保留全部有限支撑列结论。它不把任意已经给定的素数集变成合格支撑；三次数据仍受限制。

## 5. 远端形式化对应及边界

本轮重新读取dev：
- `GeneralPowerCharacterLayer.lean`，blob79c32483be14a2333e043f151744877c4ea30fb8，复用k=3幂子群与特征标共同核接口；
- `QuadraticCompositeRank.lean`，blobe1032eaff92f53700f639ceb3bab3292b151651c，其具体双二次秩不能替代本轮任意三次秩证明。

官方KummerExtension文档有单根式autEquivRootsOfUnity、autEquivZmod；固定仓库版本的接口可用性仍需本地核对。未在当前环境编译这些源。多根式范数独立性、满秩、半直积、数域交、Frobenius兼容和Chebotarev应用均有单独形式化义务，未引入私有Lean公理。

有限群、CRT、根式符号恒等式和具体原参数检查都是自审；它们不证明Chebotarev，也不取代无限论证。完整i=3及原始i=4..324的余留仍未闭合，旧书面结论保留各自审阅范围。没有真值、解决计数、冻结源或CI规则变更。
