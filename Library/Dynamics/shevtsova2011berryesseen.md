---
bibkey: "shevtsova2011berryesseen"
authors: "Irina Shevtsova"
year: 2011
title: "On the absolute constants in the Berry–Esseen type inequalities for identically distributed summands"
doi: null
url: "https://arxiv.org/abs/1111.6554v1"
claim: "The uniform Berry–Esseen bound for iid summands with a finite third absolute moment supplies the quantitative central approximation used inside the actual compensated-model second-order Hamming proof."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# On the absolute constants in the Berry–Esseen type inequalities for identically distributed summands

原始正文为 [arXiv:1111.6554v1](https://arxiv.org/abs/1111.6554v1)，
版本日期 2011 年 11 月 28 日，共七页，作者为 Irina Shevtsova。
这里定位于这一预印本，不将近似标题的期刊文献自动认作同一版本。

## 引用的不等式与量词

第 1 页定义 $`\mathcal F_3`$ 为均值零、方差一、三阶绝对矩
$`\beta_3`$ 有限的分布类，采用左连续分布函数。式 (1) 陈述经典 Berry–Esseen 界：
对每个 $`k\ge1`$ 及每个 $`F\in\mathcal F_3`$，独立同分布的
$`X_1,\ldots,X_k\sim F`$ 满足

```math
\sup_z\left|\mathbb P\left\{\frac{X_1+\cdots+X_k}{\sqrt k}\lt z\right\}
 -\Phi(z)\right|\le\frac{C_0\beta_3}{\sqrt k}.
```

常数 $`C_0`$ 与分布和样本数无关；第 3 页推论 1 给出可取
$`C_0=0.4748`$。该数值的最优性不是本文所用结论，第 23 章只需有限的统一常数。
原文将经典不等式归于 Berry（1941）与 Esseen（1942）。
本条核对的是 Shevtsova 正文中所列量词与不等式，不以其参考文献表代替对早期论文的逐页核验。

## 对 Hamming 二阶差的实际用途

[支持恢复卷第 23 章](../../docs/develop/theory/PARITY_HIDDEN_ARROW_RECOVERY.md#23-两种-hamming-风险在共同极限之下的分离)
将比较得分的复合 Poisson 总强度 $`\lambda`$ 等分为
$`k=\lfloor\lambda\rfloor`$ 份。每份强度属于 $`[1,2]`$，因此在每个维数上
确实是独立同分布的和；允许共同分布随维数变化，是因为上述常数统一且标准化三阶矩有统一界。
这一分解避免把独立同分布版本未经说明地用于非同分布的余项。

固定宽度区间的全局上界由分布函数误差直接得到；在有界标准化中心内，
选择足够大的固定宽度，还可使高斯区间质量超过两端误差而得到正的下界。
随后精确换测度与几何分段提供背景尾和截断二阶矩的数量级。
这是经典正态近似及其推论在新证明中的内部步骤，不作为新的局部极限定理。

原论文不提供实际 Markov 行之间的概率比较、完整支持后验或受约束与无约束 Hamming 风险差。
这些对应与误差累加由第 23 章针对补偿核另行证明；格点振幅可以使用此处区间论证，
但没有因此得到格点相位的精确余项或参数趋近端点时的一致性。
