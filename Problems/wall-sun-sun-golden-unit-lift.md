---
slug: wall-sun-sun-golden-unit-lift
bibkey: shi2026second
doi: 10.48550/arXiv.2603.25343
triage: wall
motivation_gids:
  - D5/S0/Carrier/Ring
  - D5/S0/Carrier/Conj
  - D5/S0/Carrier/Norm
  - D5/S0/Carrier/Units
  - D5/S1/Scale/Units
  - D5/S1/Scale/UnitGroup
  - D5/S1/Scale/Fibonacci
  - D5/S3/Arith/FibonacciRank
  - D5/S3/Arith/GoldenApparition
  - D5/S3/Arith/GoldenPrimeSplitting
  - D5/S3/Arith/GoldenPell
---

# Wall-Sun-Sun primes as a golden-unit lift problem

## Problem

Let `pi(m)` be the Pisano period, the least positive period of the Fibonacci
recurrence modulo `m`. The primary problem is whether there exists a prime `p`
with `pi(p) = pi(p^2)`. The paper also records the stronger conjecture that
infinitely many such primes exist.

Quoted from the introduction of arXiv:2603.25343v1:

> “A natural question was asked by Wall in his paper: Can there be a prime
> \(p\) such that \(\pi(p)=\pi(p^2)\)?”

> “It is known that up to \(10^{14}\), there are no such primes (cf. [16]).
> Still, using heuristics and probabilistic arguments, some authors conjecture
> the existence of infinitely many primes \(p\) satisfying
> \(\pi(p)=\pi(p^2)\) [7, 11].”

The same paper identifies the classical case with `d = 5` and says there are no
known `WSS(5)` primes.

Candidate formal statement, after defining `pisanoPeriod`:

```text
Existence:  ∃ p : Nat, Nat.Prime p ∧ pisanoPeriod p = pisanoPeriod (p^2)
Stronger:   Set.Infinite {p | Nat.Prime p ∧ pisanoPeriod p = pisanoPeriod (p^2)}
```

The paper states the difficulty:

> “The question of Wall for these sequences is related to certain deep
> arithmetic properties of real quadratic fields.”

It makes this precise for its generalized recurrence: equality of the periods
modulo `p` and `p^2` corresponds, subject to stated hypotheses, to failure of
`p`-rationality of the associated real quadratic field. This is why the global
existence question is not a routine finite-period exercise.

## Motivation

- Multiplication by `phi` on the basis `(1, phi)` is the Fibonacci matrix.
  Frozen `Scale/Fibonacci` already expresses powers of `phi` in Fibonacci
  coordinates.
- `GoldenApparition` and `FibonacciRank` control the first Fibonacci zero modulo
  a prime and the `p ± 1` Frobenius index; `GoldenPrimeSplitting` supplies the
  split/inert division according to 5 modulo `p`.
- The period can therefore plausibly be re-expressed as an order of the reduced
  golden unit or Fibonacci matrix. Equality at `p` and `p^2` is then an
  exceptional failure of the usual order multiplication by `p` under lifting.
- The first reachable theorem is not existence. It is an exact bridge among the
  pair recurrence period, the order of the Fibonacci matrix, and the order of
  `phi` in an appropriate golden algebra modulo `p^e` for `e = 1, 2`.

## Gap

- No frozen `pisanoPeriod` or recurrence-period API.
- `GoldenApparition` works modulo a prime; there is no golden algebra modulo
  `p^2` and no Hensel or p-adic order-lift theorem.
- There is no `p`-rational field or p-adic logarithm machinery.
- PID/UFD facts and the global unit classification alone do not decide the
  exceptional local lift.

## Route

1. Define the Fibonacci matrix `A = [[0,1],[1,1]]` over `ZMod m`; prove that
   `pi(m)` is its multiplicative order by tracking `(F_n, F_{n+1})`.
2. Define the reduction of `GoldenInt` over `ZMod m` and identify multiplication
   by `phi` with `A`.
3. For `r = pi(p)`, write the first lift as `A^r = I + pB (mod p^2)`. Prove
   `pi(p^2) = pi(p)` if and only if `B = 0 (mod p)`, and that otherwise the
   period acquires the expected factor `p`.
4. Use the frozen split/inert and apparition results to reduce the required
   congruence to a Fibonacci/Lucas quotient modulo `p`, separately in the two
   Legendre-symbol cases.
5. Only after those bridge theorems exist should a theorist choose between a
   conditional nonexistence theorem for a prime class, a density heuristic, or
   the global Wall question. Do not jump from a finite scan to existence.

## Falsifier

The existential Wall question has no honest finite falsifier. A proof that no
prime can satisfy the equality would refute it; a proof of finiteness would
refute only the stronger infinitely-many conjecture.

The proposed bridge is finitely falsifiable: find a prime `p` for which the
directly computed pair period disagrees with the order of the Fibonacci
matrix/golden unit, or for which `A^pi(p) = I (mod p^2)` disagrees with
`pi(p^2) = pi(p)`.

## Evidence

Implement three independent exact calculations for every prime `p < 10^6`,
excluding and separately reporting ramified and small cases:

1. direct pair-state Pisano periods modulo `p` and `p^2`;
2. fast-doubling checks of `F_r mod p^2` and `F_{r+1} mod p^2` at `r = pi(p)`;
3. matrix exponentiation of `A^r mod p^2` and the first-lift matrix `B mod p`.

Receipt fields should include `p`, `legendreSym 5 p`, `rank`, `pi_p`, `pi_p2`,
`F_r mod p^2`, `F_(r+1)-1 mod p^2`, and agreement of all three formulations.
This is bridge validation, not evidence that the global existential is false.

## Triage

`wall`. The repository is unusually close to the mod-`p` side, but the decisive
`p` to `p^2` lift is exactly the missing deep layer.

## ASSUMED-UNVERIFIED

- Whether the open problem was resolved after arXiv v1 is unverified; this
  records the paper's statement, not the entire later literature.
- The order of the reduced golden unit matches the chosen Pisano-period
  convention without a factor of 2 or a special case; that must be proved, not
  assumed.
- A useful local quotient criterion can be stated entirely with the current
  `GoldenInt` coordinate model.
- Any novelty of the proposed bridge lemmas is unassessed and belongs to the
  theorist's search step.

## PH. 固定黄金 Pell 曲线与初始 WSS 深度的高度预算

### PH.1 原对象与精确秩成对分块

**定义。** 保留原域 $K=\mathbb Q(\sqrt5)$、$\phi=(1+\sqrt5)/2$、$\psi=1-\phi$，以及 $F_n=(\phi^n-\psi^n)/(\phi-\psi)$、$L_n=\phi^n+\psi^n$。对素数 $p\ne2,5$，令 $r(p)$ 为 Fibonacci 首现秩，并令

$$h_p=v_p(F_{r(p)})=v_p(F_{p-(5/p)}),\qquad q_p=F_{p-(5/p)}/p\pmod p.$$

第二个等式由经典秩界 $r(p)\mid p-(5/p)$ 和估值提升公式得到；其指标倍率与 $p$ 互素。因此 $q_p=0$ 当且仅当 $h_p\ge2$。以下不假设 $h_p=1$。

对每个素数 $\ell\ge7$，定义实际整数

$$A_\ell=F_\ell,\quad B_\ell=L_\ell,\quad M_\ell=A_\ell B_\ell=F_{2\ell},\quad C_\ell=5A_\ell^2.$$

**定理 PH1。** $A_\ell,B_\ell$ 是互素奇数，且 $\gcd(M_\ell,10)=1$。每个 $p\mid A_\ell$ 恰有 $r(p)=\ell$；每个 $p\mid B_\ell$ 恰有 $r(p)=2\ell$。对两种情形均有

$$v_p(M_\ell)=h_p.$$

不同素数指标 $\ell$ 给出的 $M_\ell$ 两两互素。

**证明。** 黄金范数恒等式给出 $B_\ell^2-5A_\ell^2=-4$。Fibonacci 和 Lucas 的模二递推周期均为三，故两数为奇数。模五由 $L_n=2\cdot3^n$ 和 $F_n=n3^{n-1}$ 得二者都与五互素。共同奇素因子会整除四，故两数互素。

由强整除性，$p\mid F_{2\ell}$ 蕴含 $r(p)\mid2\ell$；秩一和二不可能，因为 $F_1=F_2=1$。所以秩为 $\ell$ 或 $2\ell$，而互素分解将两个秩准确分配给两因子。秩界还排除 $p=\ell$。若秩为 $\ell$，从 $F_\ell$ 到 $F_{2\ell}$ 的倍率二不改变奇素数估值；若秩为 $2\ell$，定义直接给出初始深度。最后，$\gcd(F_{2\ell},F_{2\ell'})=F_2=1$ 对不同素数指标成立。

### PH.2 几何等式与独立的高度假设

**命题 PH2。** 对全部上述指标，

$$B_\ell^2+4=C_\ell=5A_\ell^2,\qquad
A_\ell<B_\ell<\sqrt5 A_\ell,$$

且 $(B_\ell^2,4,C_\ell)$ 为两两互素的正整数加法三元组。记

$$R_\ell=\operatorname{rad}(4B_\ell^2C_\ell),$$

其中 $\operatorname{rad}$ 为不同素因子的乘积，则

$$R_\ell=10\operatorname{rad}(M_\ell),\qquad C_\ell>\sqrt5 M_\ell.$$

**证明。** 第一式由 $\phi\psi=-1$ 和奇指标得到。$L_\ell=F_\ell+2F_{\ell-1}>F_\ell$，而 Pell 等式给出右侧严格界。两数皆奇且 $B_\ell$ 与 $5A_\ell$ 互素，所以三元组两两互素；取根基得到最后的等式。由 $B_\ell<\sqrt5 A_\ell$ 得高度的严格下界。

**定义。** 给定实数 $\kappa>1$，称这条素指标 Pell 族满足 $\mathrm{PH}(\kappa)$，若存在常数 $H>0$ 和 $\ell_0$，使全部素数 $\ell\ge\max(7,\ell_0)$ 满足

$$\boxed{C_\ell\le H R_\ell^{\kappa}.}$$

这是额外的统一算术假设。Pell 曲线方程本身不包含该不等式。对正互素三元组的有理数 abc 猜想会对每个 $\kappa>1$ 给出这个假设；以下条件性结论只需要所显示的限制族，而不假设一般数域 abc 或任意别的二次域结论。

### PH.3 原始零集合的精确整数账目

**定义。** 在同一个 $M_\ell$ 的实际素因子上，令

$$U_\ell=\prod_{p\mid M_\ell,\ h_p=1}p,\qquad
W_\ell=\prod_{p\mid M_\ell,\ h_p\ge2}p^{h_p},\qquad
E_\ell=\prod_{p\mid M_\ell,\ h_p\ge3}p^{h_p-2}.$$

空乘积为一。$W_\ell$ 恰好由原 WSS 初始商零集合、在精确秩 $\ell$ 和 $2\ell$ 上的实际贡献组成。它不是由后来的指标倍乘产生的平方因子。$U_\ell$ 只保留估值恰为一的素数，与按奇数估值定义的平方自由核不同。

**定理 PH3。** 无条件地有

$$\boxed{M_\ell=U_\ell W_\ell,\qquad
R_\ell^2E_\ell=100M_\ell U_\ell,\qquad
W_\ell E_\ell=100M_\ell^2/R_\ell^2.}$$

对任意整数 $d\ge2$，进一步令 $W_{\ell,\ge d}=\prod_{p\mid M_\ell,h_p\ge d}p^{h_p}$，则

$$\boxed{W_{\ell,\ge d}^{\,d-1}\le
\left(M_\ell/\operatorname{rad}(M_\ell)\right)^d.}$$

**证明。** 逐素数比较指数。估值为一时，$\operatorname{rad}(M)^2E$ 与 $MU$ 的指数均为二；估值为二时均为二；估值 $h\ge3$ 时均为 $h$。其余两个恒等式由分解与 PH2 得到。对于最后的不等式，若 $h\ge d$，有 $h(d-1)\le d(h-1)$；若 $h<d$，左侧该素数指数为零，右侧非负。将这些整数整除关系相乘即可。

### PH.4 条件性异常深度质量界

**定理 PH4。** 假设 $\mathrm{PH}(\kappa)$，取其常数 $H,\ell_0$。令

$$K_{\kappa,H}=100(H/\sqrt5)^{2/\kappa}.$$

则全部足够大的素数指标满足

$$\boxed{
W_\ell\le K_{\kappa,H}M_\ell^{\,2-2/\kappa}/E_\ell,
\qquad
U_\ell\ge K_{\kappa,H}^{-1}E_\ell M_\ell^{\,2/\kappa-1}.
}$$

更一般地，对每个整数 $d\ge2$，

$$\boxed{
W_{\ell,\ge d}\le
\left(10(H/\sqrt5)^{1/\kappa}\right)^{d/(d-1)}
M_\ell^{\,(1-1/\kappa)d/(d-1)}.
}$$

**证明。** 高度假设给出 $R_\ell\ge(C_\ell/H)^{1/\kappa}$。代入 PH3，并使用 $C_\ell>\sqrt5 M_\ell$，得到首个上界。用 $U_\ell=M_\ell/W_\ell$ 得下界。深度阈值版本使用 PH3 最后一式与同一个根基下界。常数对全部允许指标统一；未将逐点选择的常数当成统一高度界。

**推论 PH5。** 如果对每个 $\kappa>1$ 都有 $\mathrm{PH}(\kappa)$，则

$$\lim_{\ell\to\infty,\ \ell\ \mathrm{prime}}
\frac{\sum_{p\mid F_{2\ell},\ q_p=0}h_p\log p}{\log F_{2\ell}}=0.$$

**证明。** 分子恰为 $\log W_\ell\ge0$。对每个固定 $\kappa>1$，PH4 将上极限控制为 $2-2/\kappa$；让 $\kappa$ 从上方趋于一。这里是按整数因子大小加权的质量比例，不是 WSS 素数在全部素数中的自然密度或计数密度，也未假设不同素数独立。

### PH.5 每个精确秩通道的条件性非零见证

**定理 PH6。** 若对某个 $1<\kappa<2$ 有 $\mathrm{PH}(\kappa)$，则每个足够大的素数指标 $\ell$ 都有一个素数 $p$，满足

$$r(p)\in\{\ell,2\ell\},\qquad q_p\ne0.$$

若更强地 $1<\kappa<4/3$，则两个通道分别都有这样的素数：存在 $p_\ell\mid F_\ell$ 和 $s_\ell\mid L_\ell$，使

$$\boxed{r(p_\ell)=\ell,\quad r(s_\ell)=2\ell,\quad
q_{p_\ell}\ne0,\quad q_{s_\ell}\ne0.}$$

可以同时得到实际简单素因子乘积的下界

$$U(F_\ell)\ge c_1F_\ell^{\,4/\kappa-3},\qquad
U(L_\ell)\ge c_2L_\ell^{\,4/\kappa-3},$$

其中 $U(X)=\prod_{p\parallel X}p$，$c_1,c_2>0$ 与指标无关。

**证明。** 当 $\kappa<2$ 时，PH4 中 $U_\ell$ 的幂指数为正，所以最终 $U_\ell>1$。对逐通道结论，置 $\delta=2-2/\kappa$。每个通道的异常部分都不超过 $W_\ell\le K_{\kappa,H}M_\ell^\delta$。PH2 给出 $M_\ell<\sqrt5 F_\ell^2$ 及 $M_\ell<L_\ell^2$。因此分别除以异常部分后，下界幂指数均为 $1-2\delta=4/\kappa-3>0$。两个简单素因子乘积最终均大于一，再由 PH1 识别其精确秩和原商非零性。

**推论。** 在 PH6 的第二种假设下，这两族见证彼此无重复。Lucas 通道的每个见证均在原黄金域中分裂，并满足 $s_\ell\equiv1\pmod{2\ell}$。Fibonacci 通道的见证满足 $p_\ell\equiv1\pmod4$，但没有由此确定它分裂还是惰性。

**证明。** 不同指标的块互素，同一指标的两通道也互素。Lucas 素因子满足 $5F_\ell^2\equiv4\pmod{s_\ell}$，其中 $F_\ell$ 可逆，故 $(5/s_\ell)=1$；秩界给出显示的同余。Fibonacci 素因子满足 $L_\ell^2\equiv-4\pmod{p_\ell}$，故 $-1$ 为平方。存在某个简单素因子不等于存在惰性的简单素因子。

**具体强度。** 仅假设 $\mathrm{PH}(5/4)$，即可得到 $W_\ell\le K M_\ell^{2/5}$，以及两个通道各自的简单素因子乘积至少为常数乘其 $1/5$ 次幂。这些均为条件性结论。

### PH.6 全异常覆盖会迫使怎样的高度反例

**定义。** 对上述互素三元组，令 $\mathcal Q_\ell=\log C_\ell/\log R_\ell$。

**定理 PH7。** 固定整数 $d\ge2$。若一个无界素数指标子族的 $M_\ell$ 的全部素因子均有 $h_p\ge d$，则沿该子族

$$\liminf\mathcal Q_\ell\ge d.$$

若只要求 $F_\ell$ 的全部素因子有 $h_p\ge d$，或只要求 $L_\ell$ 的全部素因子有 $h_p\ge d$，则相应子族满足

$$\liminf\mathcal Q_\ell\ge\frac{2d}{d+1}.$$

**证明。** 全块条件给出 $\operatorname{rad}(M_\ell)\le M_\ell^{1/d}$，所以 $R_\ell\le10M_\ell^{1/d}$，而 $C_\ell>\sqrt5 M_\ell$；取对数比值的下极限。

若只有 Fibonacci 通道满足条件，则 $R_\ell\le10F_\ell^{1/d}L_\ell<10\sqrt5 F_\ell^{1+1/d}$，而 $C_\ell=5F_\ell^2$。Lucas 通道的情形使用 $R_\ell\le10F_\ell L_\ell^{1/d}<10L_\ell^{1+1/d}$ 与 $C_\ell=L_\ell^2+4$。两者均给出 $2/(1+1/d)$。

取 $d=2$，全部原始零因子覆盖成对块会迫使质量至少二，只覆盖一个通道会迫使质量至少 $4/3$。这证明为何 PH6 的两个阈值不同，但未构造任何这样的全异常子族。

### PH.7 不能从这一条件证明中删除的内容

**命题。** PH1–PH3 和 PH7 无需高度猜想；PH4–PH6 明确依赖 $\mathrm{PH}(\kappa)$。这些结论均允许原 WSS 零集合为空，也允许它非空。上述条件性非零见证不能推出存在某个 $q_p=0$。

**证明。** 零集合为空时所有 $W_\ell=E_\ell=1$，整数恒等式及质量上界仍成立；任何上界都不强制正贡献。若存在零，则它在相应块中的实际贡献受条件上界约束，但上界不指定或生成该素数。几何方程与统一高度不等式是不同命题，后者未由前者的代数恒等式或实嵌入的伸缩性推出。

**边界实例。** 指标换成任意合数而不移除旧素因子，会破坏 PH1 的原始深度解释：$v_{13}(F_7)=1$，$v_{13}(F_{91})=2$，而 $F_{14}/13\equiv3\pmod{13}$。这里的平方来自指标乘以十三，十三仍非 WSS。固定素数指标的两通道选择正是为了排除此类自动提升。
