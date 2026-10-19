---
bibkey: mishra2026finiterobin
authors: Challenger Mishra; Rahul Sarkar
year: 2026
title: A finite arithmetic form of Robin's inequality and its equivalence to the Riemann hypothesis
doi: null
url: https://arxiv.org/abs/2609.26787v1
claim: The preprint introduces an omega(n)-truncated exponential Robin bound, proves it for several arithmetic classes, and claims equivalence with Robin's inequality; it supplies no bridge from a FIB address to a bounded distinct-prime count.
strata_touched: []
license: citation-only
triage: anchor
---

# A finite arithmetic form of Robin's inequality

The source is [arXiv:2609.26787v1](https://arxiv.org/pdf/2609.26787v1), submitted 22 September 2026. This card records the stated theorem interfaces from that version. It is a preprint; the proofs and the Appendix B computations were not independently audited here, and no Lean verification is claimed.

## The truncated criterion

For $n>5040$, put

$$
P_K(x)=\sum_{j=0}^{K}\frac{x^j}{j!},
\qquad
C_\omega(n)=e^\gamma P_{\omega(n)}(\log\log\log n).
$$

The paper calls

$$
\frac{\sigma(n)}n<C_\omega(n)
$$

the $\omega$-inequality. Since $P_K(x)<e^x$ for $x>0$, this is pointwise stronger than Robin's bound. Theorem 1 claims the inequality unconditionally for $\omega(n)\le6$ and for primorials; the paper derives the square-free and odd cases. Its Appendix B reports a finite check through $10^9$, which is source data rather than a project verification.

The same paper claims that the $\omega$-inequality is equivalent to Robin's inequality, hence to RH, and that a minimal counterexample would have initial prime support, non-increasing exponents, and be superabundant. The CA restriction is a reduction of the claimed equivalent criterion, not a proof that any CA number is a counterexample.

## Boundary for the FIB route

The truncation order is the distinct-prime count $\omega(n)$, while a FIB five-window address records additive Zeckendorf inclusion states. No statement in the source bounds $\omega(N_g)$ for the canonical FIB family $N_g=1+F_r g$, and the local labels $[null,2,3,2\,5,5]$ do not encode the prime factorization of $N_g$. Thus the $\omega\le6$ theorem cannot be applied to that family without a new arithmetic bound.

The source's superabundant/CA reduction also requires the actual integer to be an extremizer for $\sigma(n)/n$. A FIB address, a congruence $N_g\equiv1\pmod{F_r}$, or a reversible composition coordinate does not establish that extremality. The result is therefore a candidate-class filter and an alternative Robin criterion, not the missing same-price bridge or a proof of RH.


## Primary proof locators and their unpaid premises

In the versioned PDF, Lemma 4 supplies the $\omega(n)\le6$ case;
Theorem 1 concerns primorials. These are the precise separate locators
for the two unconditional source claims described above.

Lemma 20, printed p.13, states that a hypothetical **least counterexample
to the $\omega$-inequality** has $K=\omega(n)\ge21$.
It uses the author's finite candidate check (L.5), with the candidate
exponent bounds from Corollary 17. This is a statement about that least
counterexample, not a stated factor-count bound on every arbitrary FIB
integer $N_g$ or on a least Robin counterexample. Such an application
must retain the source's minimality condition for the same inequality.

For that same hypothetical least counterexample, Lemma 21, printed
pp.13–14, sets $t=\log\log\log n$, $\tau_K=\log\log(6K\log K)$ and
uses the preceding structural bound $\log n<6K\log K$ to obtain

$$
\begin{aligned}
T_K(t)&:=\log\log n-P_K(t)\\
&<E_K:=\frac{\tau_K^{K+1}}{(K+1)!}
 \left(1-\frac{\tau_K}{K+2}\right)^{-1}
<\frac{6.4\times10^{-15}}{\sqrt{\log n}}.
\end{aligned}
$$

This controls the truncation tail at the source's specified integer.
It supplies no unconditional lower bound for the Robin margin
$\log\log n-e^{-\gamma}\sigma(n)/n$.

Theorem 4, printed p.16, proves the converse implication from RH
by combining this tail bound with Lemma 23, equation (25): **under RH**,
for every $n>5040$,

$$
\frac{\sigma(n)}n
<e^\gamma\left(\log\log n-\frac{0.095}{\sqrt{\log n}}\right).
$$

The source attributes this input to Corollary 1.2 of Nicolas,
*The sum of divisors function and the Riemann hypothesis*,
*The Ramanujan Journal* **58** (2022), 1113–1157,
[DOI 10.1007/s11139-021-00491-y](https://doi.org/10.1007/s11139-021-00491-y).
The Nicolas original proof has not been inspected here; the
[existing source-access boundary](axler2024primorialcounting.md#fixed-price-finiteness-and-the-actual-finite-application)
also records that its publisher PDF endpoint returned an access page.
This 2022 input is distinct from the
[unconditional envelope comparisons in Nicolas's 2025 manuscript](nicolas2025comparison.md).

Thus the published equivalence proof uses an RH-conditional margin;
the small truncation tail cannot be used to remove that premise.
Theorem 4 uses Lemma 21, while the separate superabundance conclusion
in Theorem 3 also uses Lemma 22 and its finite check (L.6).
The author's finite checks and supporting analytic estimates remain
external premises; no notebook or old computation is rerun or certified
by this note. This dependency map identifies the relevant source
statements and quantifiers, with no new criterion, unconditional
signed estimate, cofinal theta sign or Lean result.

## Fixed-r affine applicability of the Chinese remainder theorem

The Chinese remainder theorem is the established input; see the pinned Mathlib [natural-number CRT interface](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/ChineseRemainder.html). The following application retains every fixed Fibonacci rank, arbitrary prescribed factor count and arbitrarily large multiplier. It identifies a limitation of applying the source’s low-omega criterion; it is not a new general CRT theorem, a CA/SA identification or a Robin/RH proof. The section reference below is to [the FIB audit, §258.6](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#2586-omega).

## 461. 固定秩仿射族的素因子复杂度无界

§258.6 把 Mishra--Sarkar 的低 \(\omega\) 条件正确投影到了

$$
N_{r,g}=1+F_rg,\qquad r\ge3,\quad g\ge1,
$$

但那里没有给出这个条件在固定秩族上的统一上界。下面的简单 CRT 事实说明，
这种上界不可能由 Fibonacci 同余本身产生。

### 命题 461.1（任意固定秩都有任意高的 \(\omega\)）

固定 \(r\ge3\)。对任意整数 \(k\ge1\) 和 \(Y\ge1\)，存在整数 \(g\ge Y\)，使得

$$
N_{r,g}=1+F_rg>5040,\qquad
\boxed{\omega(N_{r,g})\ge k.}
\tag{461.1}
$$

甚至可以要求这 \(k\) 个互异素因子全部大于预先给定的 \(Y\)。

**证明。** 置 \(m=F_r>1\)。选取 \(k\) 个互异素数

$$
q_1,\ldots,q_k>Y,\qquad q_i\nmid m.
$$

这是可能的，因为素数无穷，而 \(m\) 只有有限个素因子。对每个 \(i\)，\(m\)
在模 \(q_i\) 下可逆；令 \(a\) 满足

$$
a\equiv-m^{-1}\pmod {q_i}\qquad(1\le i\le k).
$$

中国剩余定理给出模

$$
Q=q_1\cdots q_k
$$

的解 \(a_0\)。取 \(t\) 足够大并置 \(g=a_0+tQ\)，则 \(g\ge Y\) 且

$$
1+mg\equiv0\pmod {q_i}\qquad(1\le i\le k).
$$

增大 \(t\) 还可保证 \(1+mg>5040\)。这些 \(q_i\) 两两不同且都整除
\(N_{r,g}\)，故 \(\omega(N_{r,g})\ge k\)。证毕。 \(\square\)

### 推论 461.2（低 \(\omega\) 筛不能覆盖固定秩仿射族）

对每个固定 \(r\ge3\)，不存在常数 \(C_r\) 使全部 \(N_{r,g}\) 都满足

$$
\omega(N_{r,g})\le C_r.
$$

因此，任何只覆盖 \(\omega(n)\le C\) 的 Robin 判据，作用到 FIB 仿射族时都只能
删除一个条件子族。特别地，接受 Mishra--Sarkar 预印本中 \(\omega\le6\) 的外部
条件，只能得到低复杂度候选的安全性；命题 461.1 说明不能把它提升为固定秩
FIB 族的统一覆盖。

这条 CRT 结论与 §450 的严格库存筛并不冲突：命题 461.1 的 \(N_{r,g}\) 是
一般仿射整数，不要求它等于某个严格库存 \(N^-(t)\)，也不声称它是 CA/SA。
它同样不产生 Robin 反例；它只排除“先由 FIB 同余得到统一低 \(\omega\)，再用有限截断
完成全称估计”的路线。要推进 Robin，仍需在同一个实际来源上补 CA/价格源识别
或有符号点值界。
