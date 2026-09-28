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

## 同轮加强：用子群闭合性消去所有共同因子分配

新增完整证明：`tools/scripts/agent/openproblem/erdos699-power-support-closure.py`。
先把整数完全幂前提弱化为局部条件：对每个 p|j、p不整除d，oddpart(d)属于 F_p^* 的相应幂子群。根可以随p变化，不要求全局整数开根。

若有限素数集S同属5或13模24，且每个不同p,q∈S都满足 q∈(F_p^*)^4，则任意共享奇因子都是S中素数的幂乘积。在任何p不整除d处，这些因子的像全部在同一个四次幂子群里；子群对乘积和幂闭合，因而所有gcd分配、所有幂次同时满足局部条件。

于是所有 j=2^b*product(p^e_p)、b,e_p>=0、j>=4，对全部n>=2j满足原题i=3，不再对gcd加任何限制。明确非空的三素数支持是 {13,61,2557} 和 {5,101,12821}；源码提供两方向共十二个直接四次根证书。未断言任意三素数集合都满足互为四次幂剩余的条件，也未声称整个Erdos699解决。

这个加强复用了同一幂子群核接口，未增加外部定理。有限乘积闭合性的形式化可直接对接现有powerSubgroup。新的局部整数联系及原题结论仍须独立形式化和复核。

## 继续结合形式化：允许非零共同相位的对角商

续接实际读取的提交 `69acdc55ce0e68b7ce974b9ed9d81b2ab1094122`。新完整书面证明及标准库核验器是 `tools/scripts/agent/openproblem/erdos699-diagonal-phase-check.py`。本轮重新读取上述 GeneralPowerCharacterLayer 真源，其 blob 未变；也读取 Erdos699DenominatorGap 真源，blob `982eb26f0fcd5b1363961f8023f2558bee790855`。登记或Scribe变化不等于新的原题算术结论。未在当前环境重新编译这些源，也不宣称新结论已经Lean验证。

对 p 同属5或13模24，取指定2归一化的四次特征标：

    phi_p(z) in Z/4,
    z^((p-1)/4) = (2^((p-1)/4))^phi_p(z) modp.

phi_p的核为四次幂子群；phi_p(2)=1、phi_p(-1)=2。旧前提要求共同奇因子e在所有phi_p下为0。新局部算术引理只要求phi_p(e)彼此相同，允许非零。令nu=N+lambda，则n-1的端点素数要求nu=0，n-2的角色要求nu=1。两个特殊比值theta=1/3、2/3分别由-1的特征值和原始模4/模16等式排除。非零lambda时不能从nu=0推出4|N；模16步骤改由准确的N>=v2(j)+2及v2(j)=2得到N>=4。三倍二次幂分支用共同的二次特征符号排除。

对活跃指标集U，(Z/4)^U的常向量组成Diag。差映射v->(v_p-v_p0)满射，其核恰好是Diag。新条件就是共同因子之像落在Diag，而不是落在零子群。差特征标共同核对乘积和幂闭合，提供了与已有幂子群真源相邻的形式化接口。这一初等抽象群论事实不作历史新颖性主张。

新的完整支撑定理：若有限S同属5或13模24，且对每个q∈S存在lambda_q，使所有p≠q的phi_p(q)=lambda_q，那么任意j=2^b*product(q^e_q)>=4对所有n>=2j满足原题i=3。各lambda_q可以不同，也可以非零。对实际共同因子e，phi_p(e)=sum_q v_q(e)*lambda_q与p无关，因此所有gcd分配和指数被统一处理。

明确例子：{5,53,173,10733}和{13,37,1597}的全部非对角值为3，所以每对都是二次非剩余；{5,29,1301,18701}的列值为(2,2,0,0)。它们不满足旧的互为四次幂剩余条件。对第一组，j=492054385、n=5*2^N、N>=28时，gcd(n,j)=5且全部活跃phi_p(5)=3，展示了一个旧局部核条件不覆盖的新无界参数族。没有声称所有其他旧判据也都不覆盖它。

形式化分层：指定2的有限域特征标；对角差映射之核；保留原规范化/mixed-support前提的局部同步算术引理；有限乘积推论。新的原题结论仍继承未在本轮独立认证的数论前提，不得从旧群论声明直接绑定全结论。一般差矩阵不为零时仍未得到统一矛盾；完整i=3及i=4..324没有由此闭合。

## 受限整数对角像：混合剩余类与更细的循环商

2026-09-28，续接读取的 `8447379da0347640911c37e491745ba07a5d6a09`。新完整证明与核验器：`tools/scripts/agent/openproblem/erdos699-restricted-diagonal-check.py`。重新读取 GeneralPowerCharacterLayer.lean，其 blob 未变，未重新编译。

对任意有限素数支撑 S（素数均>=5）及有序不同 p,q，定义 K_pq(S) 为 F_p^* x F_q^* 中由 (2,2) 及所有 (r,r)、r∈S\{p,q} 生成的子群，坐标在各自域中约化。它是受限有理数乘法群的对角像。不能误称无限制整数的对角约化存在相同阻碍：后者由中国剩余定理满射。

新的目标分离定理：若每个K_pq都不含(1,2)、(1,-1)、(1,-4)、(3^{-1},2*3^{-1})，则整个S支撑列对全部n成立。若S全部为1模4，可删除(1,-4)，因为原式theta=2/3由oddpart(j)=1 mod4及v2(n)>=v2(j)+2产生独立的模4/模16矛盾。其余三个目标分别来自n-1/n-2、n-1/n+1、三倍分支的两种原始素数角色。

这保留任意共享因子的全部幂乘积，而不再要求它们的四次相位相等或同一个模24类。有限交换群对偶性把t不属于K等价为某个消去K而不消去t的特征标。经典接口是Mathlib的 `CommGroup.forall_monoidHom_apply_eq_one_iff`，上述现有Lean文件已经用于幂子群；本轮用于一般生成子群。官方文档已读取：https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/FiniteAbelian/Duality.html 。此为经典输入，不作新发现声明。

两个经过准确证书验证的完整支撑是{5,101,569}与{61,541,701}。前者使用C4、C8、C8商及不等权重；后者使用C4、C20、C20商。在(5,569)处，目标(1,-1)的C8值为4，模4投影丢失它；在(61,701)处，一个三倍分支目标的C20值为4，其C5像非零而C4像为零。它们分别展示更高二次幂商和奇数阶商的实际用途。

完整一般结论仍是带目标分离前提的支撑定理，不是全部Erdős699。反向控制S={5,29,53}在p5,q29处的K已充满112阶直积；2^21*53同时为1模5、2模29。这种局部相容不代表二项式反例，原参数仍有共同素数3。本輪沒有宣稱任意不相容支撑都已分类。

形式化接口：受限指数映射及像、一般特征标分离、原题角色到目标的完整分支、独立二分之三整数排除、有限例子资格。新书面证明仍继承规范化和mixed-support的独立义务；没有借用旧群论源码或对偶性直接认证数论全链条，也没有新增私有Lean公理。旧来源与证明保留。
