---
bibkey: vonkanel2016solving
authors: Rafael von Känel; Benjamin Matschke
year: 2016
title: "Solving S-unit, Mordell, Thue, Thue–Mahler and generalized Ramanujan–Nagell equations via the Shimura–Taniyama conjecture"
doi: null
url: https://arxiv.org/abs/1605.06079
claim: Unconditional explicit minimal-discriminant versus conductor bound, applied after an explicit dyadic minimal-model construction in the Erdos 699 continuation.
strata_touched: []
license: citation-only
triage: anchor
---

# Erdős 699：模性、最小判别式与导子

研究入口：issue #9670，PR #9769。
唯一推导正文：`docs/develop/theory/ERDOS_699_BINOMIAL_COMMON_PRIME.md` §§40–44。
本条记录外部依赖及其准确使用位置，不登记 Lean/Scribe 真值或整题解决。

## 主来源和实际核对范围

Rafael von Känel and Benjamin Matschke, arXiv:1605.06079v1 (2016)。
元数据：https://arxiv.org/abs/1605.06079 。正文：https://arxiv.org/pdf/1605.06079v1 。

本轮读取成功：§10.2 的最小判别式/导子记号；印刷页 98 的 f2<=8、f3<=5；Proposition 10.8(ii)，印刷页 107；式 (10.16)，印刷页 111。相关 PDF 页截图请求返回 Internal Error，没有宣称已成功图像核对。

设 E/Q 是椭圆曲线，N 为其导子，D_min 为其最小判别式。式 (10.16) 给出

    log |D_min| <= nu*log N + (3/8)*nu*log log log N
                   + (2/3)*nu + 115.1,
    nu=N*nu_star(N) <= N.

nu_star 是乘法函数，nu_star(p)=1；b>=2 时 nu_star(p^b)=1-1/p^2。这一界是无条件的经典模性/高度输入；没有使用 abc、Szpiro 或 GRH。原论文标题中的 Shimura–Taniyama conjecture 在这里指已知模性定理及其方法来源，并非本应用额外假设。

## 本题新增构造

原假想 i=3 反例给出 E_flat:y^2=x^3-Lx+2K，L、K 奇数，W=L^3-27K^2 的二进赋值至少8。选择符号扭曲，使 epsilon*K=3 mod4。正文显式构造一个2-进整模型，其c4=3L为单位、D=W/64，所以在2处最小且乘法约化。此步骤不能用原非最小短模型的判别式替代。

令U=product_{p>=5,p|u0}p，V=product_{p>=5,p|delta}p，Q=U^2 V。准确的局部赋值分离与经典导子规则给出 N=2*3^f3*Q，0<=f3<=5；Q<=Delta。因此 N<=486Delta。原文界简化为 log|D_min|<2NlogN+116，结合精确二进赋值得

    a<91+729*Q*log(486Q)<=91+729*Delta*log(486Delta).

这是本题应用；原文没有声称解决Erdős699。新检查器只检查模型、恒等式和常数应用，不重证模性界或Tate算法。

## 局部约定的直接参考

LMFDB, reviewed entry *Conductor of an elliptic curve*：
https://www.lmfdb.org/knowledge/show/ec.conductor 。
指数为好约化0、乘法约化1、p>=5加法约化2；在Q的素数3处不超过5。本轮交叉核对这些定义和边界。

## 边界

没有计算每个潜在反例的曲线导子，没有扫描新的大曲线数据库，没有获得Delta或不可去素数乘积的全局上界，也没有枚举文中巨大截止。原分类数据只复用了先前的83个j实现，实窗口交集仅含1944，改写了已有空支持排除的证明；不重复计为新排除区域。
