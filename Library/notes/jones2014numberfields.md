---
bibkey: jones2014numberfields
authors: John W. Jones; David P. Roberts
year: 2014
title: "A database of number fields"
doi: 10.1112/S1461157014000424
url: https://arxiv.org/abs/1404.0266
claim: Background on complete prescribed-ramification number-field tables; the two totally real cubic fields used in the Erdos 699 continuation are reconstructed by an explicit finite certificate.
strata_touched: []
license: citation-only
triage: anchor
---

# Erdős 699：处方分歧数域与小三次域分类

研究入口：issue #9670，PR #9769。
唯一推导正文：`docs/develop/theory/ERDOS_699_BINOMIAL_COMMON_PRIME.md`，§§45–48。
本条保存文献背景与实际读取边界，不登记 Lean/Scribe 真值或整题解答。

## 已核对来源

John W. Jones and David P. Roberts, *A database of number fields*, LMS Journal of Computation and Mathematics 17 (2014), 595–618。

- arXiv：https://arxiv.org/abs/1404.0266
- DOI：10.1112/S1461157014000424
- 作者处方分歧表入口：https://hobbes.la.asu.edu/numberfields-old/driver/FieldTables.html
- 本轮日期：2026-09-25。

本轮实际读取论文的元数据、摘要和作者表入口的完备性说明。其 Cubics 子表未成功取得，论文完整 PDF 也未作为本轮已逐页复核的来源。因而没有把未读取的具体分类表当成下面两种三次域分类的前提。

## 本轮重新构造的证书

对在 2、3 之外不分歧的全实三次域，局部不同理想界给出 `D_K<=2^3*3^5=1944`。将整数环格投影到迹零平面，并用二维最短向量界，可取得最小多项式

    X^3-tX^2+bX+c,
    t in {0,1}, -15<=b<=0, -32<=c<=32。

检查器完整枚举2080个多项式：451个不可约且正判别式；23个在 p>=5 处无奇数判别式赋值的候选；15个有明确的 p>=5 Eisenstein 平移排除证书；余下8个通过商环中的精确根像，归入 `X^3-3X-1` 和 `X^3-9X-6`。两者的局部不同理想计算分别给出域判别式81和1944。

因此完备性来自理论卷的有效盒子和完整算术证书，不来自有限数据库搜索的默认完备性，也不来自 SymPy 的抽样极大序检查。经典分类及其背景归原有数论研究；本轮不主张历史优先权。

## 本题应用与边界

对原假想反例的三次域，准确的 p>=5 分歧集合为

    T_cub={p>=5: p|u0 or v_p(delta) is odd}。

它可以严格小于椭圆曲线的不可去坏素数集合 `{p>=5:p|u0*delta}`。若 T_cub 为空，本轮的小分类与原系数的局部约束强迫 `c=1,d` 奇数、域判别式1944，并产生明确的迹零二元三次式和指数形式。

本輪没有由固定域推出原反例有限或不存在。其余 T_cub 非空的无界情形仍在研究范围内。Newton 多边形、Hensel 分解、Eisenstein 扩张的不同理想公式是经典局部事实；理论卷逐项列明了其在本题的使用条件。检查器的有限局部回归不承担全部素数的证明义务。
