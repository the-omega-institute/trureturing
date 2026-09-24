---
bibkey: cremona2007goodreduction
authors: J. E. Cremona; M. P. Lingham
year: 2007
title: "Finding All Elliptic Curves with Good Reduction Outside a Given Set of Primes"
doi: 10.1080/10586458.2007.10129002
url: https://johncremona.github.io/papers/egros.pdf
claim: Complete upper count of 83 rational j-invariants with good reduction outside 2 and 3, and Weierstrass/twist discriminant rules used in the Erdős 699 essential-support continuation.
strata_touched: []
license: citation-only
triage: anchor
---

# Erdős 699：二次扭曲下不可去的坏素数与完整分类输入

关联：issue #9670，已合并 #9755 的续接分支。唯一推导正文为
`docs/develop/theory/ERDOS_699_BINOMIAL_COMMON_PRIME.md`，§§36–39。
本条记录外部来源及其使用边界，不是 Lean/Scribe 证明收据或整题解决声明。

## 1. 已核对原始论文

J. E. Cremona and M. P. Lingham, *Finding All Elliptic Curves with Good Reduction Outside a Given Set of Primes*, Experimental Mathematics 16(3) (2007), 303–312.

作者 PDF：https://johncremona.github.io/papers/egros.pdf 。
核对日期：2026-09-25。本轮读取 §3 的模型变换和二次扭曲规则，实际截图核对作者版印刷页 9 的 §5.1。

- 不同 Weierstrass 模型的判别式相差有理数的十二次幂；二次扭曲使判别式乘以扭曲因子的六次幂。
- Lemma 3.1 和 Proposition 3.2 给出好约化与判别式赋值、j 的局部整数性之间的必要条件。
- §5.1 给出好约化于 `{2,3}` 之外的 83 个可能 j 不变量及 752 个 Q 同构类。本卷只需要完整 j 列表的上界 83，不重新证明这个经典分类。

## 2. 83 个实现的独立可复算证书

Rafael von Känel and Benjamin Matschke (2015) 的作者数据：

https://github.com/bmatschke/solving-classical-diophantine-equations/blob/master/elliptic-curve-database/curves__S_2_p_pMax250.txt

源 Git blob：`ae99430519ac37dae02a6512e4fccbde53858801`。
源文件署名许可为 **CC BY-NC 3.0**：https://creativecommons.org/licenses/by-nc/3.0/ 。
检查器中的 `MODELS_23` 选自此数据，每个不同 j 只取一个 `(c4,c6)` 实现，并把 c6 改为绝对值。这个数值选集保留作者署名、来源和许可；新证明与检查逻辑不声称改变源数据许可。

每项准确检查 `D=(c4^3-c6^2)/1728` 为非零整数且只有 2、3 素因子，并构造整曲线 `y^2=x^3-27c4*x-54c6`，其判别式为 `6^12 D`。83 个 j 两两不同，结合论文的外部上界 83，得到所需完整性。

其中 32 个 j 大于 1728；准确最小二进赋值是 -9，在 `1193859/512` 取得。这里不要求重新认证源数据库全部 9416 行、每个最小模型或曲线秩。83 上界与有限实现检查承担不同角色，不能混称为本项目重证分类。

## 3. 本卷实际增加的接口

在原 i=3 反例假设下，`k=ur`、`ell=ue`、`Delta=u^2 delta`。
新赋值引理证明，对于 p>=5，p|u 时 v_p(Delta)=2v_p(u)，而 delta 与 ur 互素。
写 `u=u0*s^3`，u0 为无立方因子的正整数。显式扭曲

    E_flat: Y^2=X^3-u0*s*e*X+2*u0*r

在 p>=5 处的判别式为 `2^(2a+4)*c^6*u0^2*delta`。
所有二次扭曲都无法去掉的坏素数恰为 `T0={p>=5:p|u0*delta}`。
若 T0 为空，分类的 v2(j)>=-9 与原模型 v2(j)=8-2a-v2(delta) 矛盾，除非 a<=8；后者的五个完整行、481 个合法 j 又由准确算术证书全部排除。

这是对原题的一项受限排除，未证明 T0 或中点因子 r 在全体反例中有界。

## 4. 有效有限性外部依赖保持分列

固定有限集合 T 包含 2、3 和 T0 时，本卷将 `W_flat=D*V^6` 代入
Bérczes–Evertse–Győry (2013) Theorem 2.1。原始来源和高度定义见既有 canonical note
`Library/notes/berczes2013effective.md`，https://arxiv.org/pdf/1301.7168 。
本轮重新读取前提并截图核对印刷页 4 的公式 (2.4)。代入次数 2、幂指数 3、Q 上的 T-整数，得 `a<3+2*(12*sigma)^(3024*sigma)*Q^2988`，其中 Q 为 T 中素数乘积、sigma=|T|+1。

截止有效但巨大，未被穷举；固定每个 T 的有限性不使所有 T 的无穷并集有限。issue 评论 5817135127 已提出未扭曲曲线的坏素数接口，本卷明确致谢并给出更小的不可去支持；未把该评论当成独立审稿。
