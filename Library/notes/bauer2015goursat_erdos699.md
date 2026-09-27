---
bibkey: bauer2015goursat_erdos699
authors: Kristine Bauer; Debasis Sen; Peter Zvengrowski
year: 2015
title: "A generalized Goursat lemma: context for the Erdos 699 common cyclic quotient"
doi: null
url: https://arxiv.org/abs/1109.0024
claim: Classical common-quotient interpretation; the cyclic kernel identity and its Erdos applications are proved explicitly in the companion research module.
strata_touched: []
license: citation-only
triage: anchor
---

# 共同循环商、幂特征标与 Erdős 699

入口：issue #9670，PR #9769。
本轮完整证明与可执行自审：
`tools/scripts/agent/openproblem/erdos699-common-quotient-check.py`。
本条不登记新 Lean 真值、独立审稿或整题解决。

## 外部经典背景及实际读取范围

Bauer, Sen and Zvengrowski, *A generalized Goursat lemma*, Tatra Mountains Mathematical Publications 64 (2015); arXiv:1109.0024.
公开期刊摘要：https://www.mat.savba.sk/ojs/index.php/TATRA/article/view/374 。
本轮读取了作者、摘要和出版元数据。摘要明确讨论有限直积中的子直积、循环群与 Sylow 子群。没有声称读取或重证该文全部定理，也没有将其一般结论计作本项目新发现。

本题只需初等且自包含的特例：m,n>0，g=gcd(m,n)，

    (C_m x C_n)/<(1,1)> ≅ C_g,
    (a,b) -> a-b modg.

核等式用 Bezout/广义中国剩余条件直接证明。因此该文是结构背景，不是未展开的证明黑箱。所有群比较保留被指定的元素2以及3的位置，不能任意选抽象循环群同构后遗失这些标记。

## 本仓库已有形式化真源

本轮实际读取 dev：
`D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.lean`，
Git blob `79c32483be14a2333e043f151744877c4ea30fb8`。
其中已有

- `power_character_joint_kernel_eq_power_subgroup`；
- `power_quotient_has_exponent_dividing`；
- `power_subgroup_le_iff_quotient_pow_eq_one`。

其结论分别给出有限交换群的 μ_k 特征标共同核等于 G^k、商的指数整除 k，以及相应的商群泛性质。本轮读取该源，未重新编译它。新应用在 F_p^*/(F_p^*)^2 或 F_p^*/(F_p^*)^4 中消去共同奇平方/四次幂，同时保留2、-1、-4的非平凡像。共同指数的对角商与幂子群的商是不同对象，不能混同。

## 本题新增应用和继承义务

新应用一：完整共同商把旧二元 chi 条件升级成 a_q-a_p 不等于 ±1 mod gcd(ord_p(2),ord_q(2))，排除新的无界双素数列，例如11与211，以及零二进阶层的7与73。结合简单的3幂分圆值，得到无须素数生成猜想的无限基底族。

新应用二：任意多个端点奇素数同属 mod24 的11或19类，且 gcd(n,j)的奇数部分为平方，或者同属5或13类且该奇数部分为四次幂时，原题 i=3 成立。这是带明确 gcd 条件的原参数定理，不是任意共同因子的整列结论。

这些应用仍继承原规范化、三次式与 mixed-support 的书面证明；上述已有群论 Lean 源不认证它们或新应用的全链条。没有使用上一轮 Bugeaud-Laurent 对数估计，也没有引入新的解析假设。有限计算为自审，新增无界结论由已写出的群论和算术反证承担。
