---
bibkey: farnik2016initial
authors: Łucja Farnik; Janusz Gwoździewicz; Beata Hejmej; Magdalena Lampa-Baczyńska; Grzegorz Malara; Justyna Szpond
year: 2016
title: "Initial sequences and Waldschmidt constants of planar point configurations"
doi: null
url: https://arxiv.org/abs/1607.01031
claim: Background on initial degrees, multiplicities, and the known value 9/4 for a six-point configuration; not an external premise for the explicit six-point proof used in the Erdős 699 continuation.
strata_touched: []
license: citation-only
triage: anchor
---

# 六点重数与固定三次系数消去的来源边界

关联：issue #9670，PR #9755；唯一推导正文为 `docs/develop/theory/ERDOS_699_BINOMIAL_COMMON_PRIME.md`，§31。

2026-09-24 已读取 arXiv:1607.01031 的摘要、Definitions 1.1–1.2、Theorem 2.3(d) 和相关讨论。文献明确记录六点配置 H(6,9) 的 Waldschmidt 常数为9/4，并回溯此前点配置分类。这个几何常数不能作为本项目首次发现的数字。PDF第4页图像请求未成功，故没有把未见图形用作配置等同的证据。

本项目使用的具体六点，在仿射坐标中为

    顶点 (0,0),(0,2),(2,2)，中点 (0,1),(1,2),(1,1)。

§31.2 给出独立的初等证明：任意在六点重数均至少D的非零平面齐次多项式，次数R满足4R>=9D。方法为除尽三条边和三条中点连线，分别限制到六条直线上统计零点重数，再作准确的非负线性组合。九次的“三边平方乘三内线”达到四重零点，证明常数尖锐。

将该引理应用于三次系数参数化的四个三次齐次坐标，可得固定齐次系数表达式的消去阶m<=floor(3D/4)，并给出所有次数的达到构造。这个应用和其证明写于理论卷，不依赖外部点配置图或未复核分类。没有宣称该方法界的历史优先权，也没有把它提升成Erdős699的不可解性。

本条仅作来源记录，不新增Lean/Scribe数学真值、开放问题解决状态或形式化覆盖声明。
