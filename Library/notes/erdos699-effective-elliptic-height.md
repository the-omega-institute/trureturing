---
bibkey: berczesevertsegyory2013effective
authors: Attila Bérczes; Jan-Hendrik Evertse; Kálmán Győry
year: 2013
title: "Effective results for hyper- and superelliptic equations over number fields"
doi: null
url: https://arxiv.org/abs/1301.7168
claim: Explicit height bound for squarefree polynomial equations f(x)=b*y^2, specialized to the bounded-quotient elliptic curves in the Erdős 699 continuation.
strata_touched: []
license: citation-only
triage: anchor
---

# Erdős 699：有界商椭圆曲线的显式高度输入

研究关联：issue #9670，PR #9723。
推导正文：`docs/develop/theory/ERDOS_699_BINOMIAL_COMMON_PRIME.md`，§§21–24。
这里只记录来源和应用边界，不登记 Lean/Scribe 真值或整题解决状态。

## 已核对来源

Attila Bérczes, Jan-Hendrik Evertse, Kálmán Győry,
*Effective results for hyper- and superelliptic equations over number fields*, arXiv:1301.7168v1 (2013-01-30).

- 元数据：https://arxiv.org/abs/1301.7168
- 全文：https://arxiv.org/pdf/1301.7168
- 读取日期：2026-09-24。
- 已读取印刷页 3 的对数高度定义、印刷页 4 的前提和 Theorem 2.2，并成功取得第 4 页截图核对 (2.6) 的指数及符号。其他页面截图请求未成功，不声称已逐页图像审查全文。

设 r>=3，f 属于 O_S[X] 且无重根，b 为非零 S-整数。Theorem 2.2 对 f(x)=b*y^2 的 S-整数解给出

    h(x),h(y) <= (4*r*s)^(2^12*r^4*s) * |D_K|^(8*r^3)
                 * Q_S^(20*r^3) * exp(50*r^4*d*hhat).

这里 d=[K:Q]、s=|S|；只有无穷位置时 Q_S=1。hhat 是同时包含 b 和 f 全部系数的对数高度。它是已有的显式定理，本轮没有重新证明。

## 本次准确代入

在 i=3 的反例假设下，新耦合不等式先限制

    kappa <= floor((729*k^3-1)/(8*c^8*49^2)),
    kappa 是 c 的正奇倍数，c 属于 {1,3}。

再构造整数点

    Y^2 = X^3 + 18*kappa*k*X - 8*kappa^3*k.

该三次多项式判别式为

    -864*kappa^3*k^2*(2*kappa^3+27*k) != 0。

取数域 Q、S={infinity}、b=1、r=3，可将上述外部界准确化为

    log max(1,|X|,|Y|) <= 12^331776 * M^4050,
    M=max(1,18*kappa*k,8*kappa^3*k)。

331776=2^12*3^4，4050=50*3^4。无需已知 Mordell–Weil 基或假定曲线秩。

对于给定正整数 K，若 k<=K，则 kappa<K^3、M<=18*K^10，理论卷给出

    H_K=12^331776*(18*K^10)^4050,
    n < 3^(2*H_K)。

这是显式但极大的截止，未实际枚举它。它只证明每个有界商区域可以有效归约为有限集合，不证明全体 k 有界，不证明 i=3 的全体反例有限或不存在。椭圆曲线整数点必须再还原 A,B,d 并检查光滑分母、合法范围、系数整性及完整 Kummer 条件。

与 `erdos699-quartic-s-parts.md` 的 Bugeaud–Evertse–Győry 2017 非有效 S-part 输入区分：作者首位、论文、定理、使用前提和有效性均不同。来源归原作者；本轮不作优先权声明。
