# Erdős 699：共同指数的素数平方提升

入口：issue #9670、Draft PR #9769。完整书面证明和标准库复算程序：
`tools/scripts/agent/openproblem/erdos699-cross-prime-lift-check.py`。

本条记录可复核的跨方向接口，不登记新的 Lean 真值、独立评审、WSS 素数排除或整题解决。新的原题结论是全部 `j=2^b*11^s*23^t`、`b>=0,s,t>=1` 对所有 `n>=2j` 满足 i=3 的共同奇素数断言。它继承已有 normal-form/mixed-support 书面前提，并使用完整的8064项周期算术引理。

## 1. 实际读取的 loning 最新理论

2026-09-29 合并的 PR #11272：
https://github.com/the-omega-institute/trureturing/pull/11272

文件：`docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md`，
读取提交 `277f3f1abd115c17edc2e0c3b7e3cdfce18df2c8`，
blob `0d715c89db1e9a0b936954d212727c6301014cf0`。
本轮读取 §§113–115 的完整新增补丁，并专门回读 §115 的实际提升纤维、整数进位和完整历史条件。

定理115.2把真实 Fibonacci 方向的 p² 提升写成仿射纤维；其增长与否由实际 F_(3k) 的 p² 整除决定，不能假设所有素数均增长。定理115.4先除整个整数再模p约化，保留高位系数。定理115.5要求所有历史条件在同一实际源上取交。PR 明确是普通理论正文，本轮不把它升级为整体 Lean 认证。

本轮的迁移是：另一个素数提供的指数条件也必须保留在原提升参数中。分别找得到两个局部指数，不表示存在一个指数同时实现两者。

## 2. 实际读取的 WSS 形式化真源

PR #9761：
https://github.com/the-omega-institute/trureturing/pull/9761

文件：`D5/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod.lean`，
读取提交 `d1ee521e3dce669f093a334dc0806548871204ee`，
blob `c197fa923c43e4cae9f1ab28866f0185966d2643`。

`golden_matrix_prime_power_period` 对 p>5 和所有正深度，保留首次返回深度 h，构造 Q^tau=I+p^h A、A模p非零，并给出精确返回条件 a<=h+v_p(m) 和周期 tau*p^(a-h)。这里指数差为自然数截断。这个源码的实际声明已读取，未在当前环境重新编译。

本轮在整数单位中另证相同的二项式提升机制。没有把黄金单位与整数2等同，也没有假设首次深度恒为1。真实的底数2控制 p=1093 具有 ord=364、首次深度2；检查器明确保留它。底数2的 Wieferich 条件不是 Fibonacci 的 WSS 条件。

## 3. 新的共同群商阻碍

若 a^m=1+p^h U、c*a^r=delta+p^h V，则

    c*a^(r+m*z) = delta+p^h*(V+delta*U*z) mod p^(h+1).

对其它所有条件允许的实际 z 集合 Z，先取其模p像 B，再与这条仿射方程的零集合相交。空交把相关估值准确锁在 h；U模p为零时，必须保留全纤维/空纤维两个分支，不许求逆。

具体地，ord_11(2)=10 与 ord_23(2)=11 互素，模素数时的两个循环群不会阻止目标(1,2)。但首次提升后 ord_121(2)=110，与11的最大公因数变为11。共同指数的对角循环商因此出现 C11，目标(1,2)在其中非零。这使23处的相邻返回禁止11处继续提升。

同样保留c=3的平移目标；四个原始角色组合的121提升余类与23余类全部不相容。由此得到 v11(n-1)=1 或 v11(n-2)=1，绝非仅给一个松的上界。

## 4. 与已有原题形式化连接

实际回读 dev `D5/S3/Arith/Erdos699DenominatorGap.lean`，
blob `982eb26f0fcd5b1363961f8023f2558bee790855`。
其前提含 n-1=L*R、j=1+m*R 和准确整数比值，结论4(n-2)<D*L²。新证明先从全部低位无进位构造这些前提，再使用提升锁定把 L 限到33、D限到69。因此一个角色方向产生 n<=18787，与必要指数余类矛盾。

其它方向把 D 锁到11、33或3。8064个完整分子/指数剩余类由22个已验证素数的平方非剩余证书排空，共同周期27720。它覆盖无界指数，不是原始n的截断扫描。

官方 Mathlib 文档已核对 `padicValNat_factorial`、`padicValNat_choose` 的 Legendre/Kummer 接口：
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Padics/PadicVal/Basic.html
该网页不证明本轮继承的规范化或新整列定理。新证明不需要额外的解析估计、Chebotarev 或未形式化的私有公理。

## 5. 尚未完成

一般素数对可能仍允许共同的高位提升。本轮未证明所有支撑、所有i=3或i=4..324，也没有证明黄金域中的初始商零集合缩小。可继续复用的接口是精确首次深度、共同指数的仿射纤维交，以及原始整数分母间隙；它们的实例化前提必须逐题检查。
