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

### PH. 固定黄金 Pell 曲线与初始 WSS 深度的高度预算

#### PH.1 原对象与精确秩成对分块

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

#### PH.2 几何等式与独立的高度假设

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

#### PH.3 原始零集合的精确整数账目

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

#### PH.4 条件性异常深度质量界

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

#### PH.5 每个精确秩通道的条件性非零见证

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

#### PH.6 全异常覆盖会迫使怎样的高度反例

**定义。** 对上述互素三元组，令 $\mathcal Q_\ell=\log C_\ell/\log R_\ell$。

**定理 PH7。** 固定整数 $d\ge2$。若一个无界素数指标子族的 $M_\ell$ 的全部素因子均有 $h_p\ge d$，则沿该子族

$$\liminf\mathcal Q_\ell\ge d.$$

若只要求 $F_\ell$ 的全部素因子有 $h_p\ge d$，或只要求 $L_\ell$ 的全部素因子有 $h_p\ge d$，则相应子族满足

$$\liminf\mathcal Q_\ell\ge\frac{2d}{d+1}.$$

**证明。** 全块条件给出 $\operatorname{rad}(M_\ell)\le M_\ell^{1/d}$，所以 $R_\ell\le10M_\ell^{1/d}$，而 $C_\ell>\sqrt5 M_\ell$；取对数比值的下极限。

若只有 Fibonacci 通道满足条件，则 $R_\ell\le10F_\ell^{1/d}L_\ell<10\sqrt5 F_\ell^{1+1/d}$，而 $C_\ell=5F_\ell^2$。Lucas 通道的情形使用 $R_\ell\le10F_\ell L_\ell^{1/d}<10L_\ell^{1+1/d}$ 与 $C_\ell=L_\ell^2+4$。两者均给出 $2/(1+1/d)$。

取 $d=2$，全部原始零因子覆盖成对块会迫使质量至少二，只覆盖一个通道会迫使质量至少 $4/3$。这证明为何 PH6 的两个阈值不同，但未构造任何这样的全异常子族。

#### PH.7 不能从这一条件证明中删除的内容

**命题。** PH1–PH3 和 PH7 无需高度猜想；PH4–PH6 明确依赖 $\mathrm{PH}(\kappa)$。这些结论均允许原 WSS 零集合为空，也允许它非空。上述条件性非零见证不能推出存在某个 $q_p=0$。

**证明。** 零集合为空时所有 $W_\ell=E_\ell=1$，整数恒等式及质量上界仍成立；任何上界都不强制正贡献。若存在零，则它在相应块中的实际贡献受条件上界约束，但上界不指定或生成该素数。几何方程与统一高度不等式是不同命题，后者未由前者的代数恒等式或实嵌入的伸缩性推出。

**边界实例。** 指标换成任意合数而不移除旧素因子，会破坏 PH1 的原始深度解释：$v_{13}(F_7)=1$，$v_{13}(F_{91})=2$，而 $F_{14}/13\equiv3\pmod{13}$。这里的平方来自指标乘以十三，十三仍非 WSS。固定素数指标的两通道选择正是为了排除此类自动提升。

### CG. 原黄金单位在连续、有限与整数几何中的同一缺陷

#### CG.1 固定代数环面与原初始商

**定义。** 令 $\mathcal O=\mathbb Z[\phi]$，$\phi^2=\phi+1$，$\psi=1-\phi$，$d=2\phi-1=\sqrt5$，并令 $u=\phi/\psi=-\phi^2$。对 $p>5$ 素数，记 $\chi=(5/p)$、$N=p-\chi$、$h_p=v_p(F_N)$、$q_p=F_N/p\pmod p$。对 $\mathcal O\otimes\mathbb Z_p$，用 $v_p(x)=\sup\{j:x\in p^j(\mathcal O\otimes\mathbb Z_p)\}$；分裂情形这是两个局部估值的最小值。

**定义。** 在 $\mathbb Z[1/10]$ 上，令 $T$ 是 $\mathcal O$ 的范数一群。其点以坐标写成 $a+b\phi$，满足 $a^2+ab-b^2=1$。这是一个一维代数环面，$u\in T(\mathbb Z[1/10])$。它与实紧致二维环面 $\mathbb R^2/\mathbb Z^2$ 是不同对象。

**命题。** $|T(\mathbb F_p)|=N$，且对每个正整数 $n$，

$$u^n-1=dF_n\psi^{-n}.$$

特别地，$v_p(u^N-1)=h_p$，并有

$$\boxed{(u^N-1)/p\equiv\chi q_p d\pmod p.}$$

**证明。** 分裂时范数一群为 $\{(x,x^{-1}):x\in\mathbb F_p^\times\}$，阶为 $p-1$；惰性时为 $\mathbb F_{p^2}^\times$ 到 $\mathbb F_p^\times$ 的范数核，阶为 $p+1$。Binet 恒等式给出 $u^n-1=(\phi^n-\psi^n)\psi^{-n}$。$d$ 和 $\psi$ 在 $p$ 处都是单位，得到估值。$N$ 偶数且黄金 Frobenius 给出 $\phi^N\equiv\chi\pmod p$，所以 $\psi^{-N}=\phi^N\equiv\chi$；将已整除的等式除以 $p$ 再降模即得末式。

#### CG.2 光滑切空间中恰有一个保周期提升

**定理。** 在模 $p^2$ 的范数一群中，固定 $u\bmod p$，其全部提升恰可写成

$$u(1+pz),\qquad z\in\mathcal O/p\mathcal O,\quad\operatorname{Tr}(z)=0.$$

这样的提升有 $p$ 个，且其中恰有一个满足 $[u(1+pz)]^N=1$。这不确定原来的 $u$ 是否就是该提升。

**证明。** 两个单位提升之比唯一写成 $1+pz$。其范数模 $p^2$ 为 $1+p\operatorname{Tr}(z)$。迹零空间在二维 $\mathbb F_p$ 代数中维数为一，因为 $\operatorname{Tr}(1)=2\ne0$。写 $u^N=1+pb\pmod{p^2}$，则 $b$ 迹零；二项式展开给出

$$[u(1+pz)]^N=1+p(b+Nz)\pmod{p^2}.$$

因 $p\nmid N$，唯一解为 $z=-b/N$。原来的固定提升对应 $z=0$，它保周期当且仅当 $b=0$，亦即 $q_p=0$。将提升作为变量时的比例 $1/p$，不是固定黄金单位在变动素数上的频率定理。

#### CG.3 一维 p-进流与准确轨道闭包

**定义。** 令 $\mathcal O_p=\mathcal O\otimes\mathbb Z_p$，$T_1=\ker(T(\mathbb Z_p)\to T(\mathbb F_p))$。使用主单位上的收敛幂级数定义 $\log$ 与 $\exp$。

**定理。** $\log$ 给出群同构 $T_1\cong p\mathbb Z_p d$。令 $\beta_p=\log(u^N)$，则 $v_p(\beta_p)=h_p$。映射

$$\Phi_p(t)=\exp(t\beta_p),\qquad t\in\mathbb Z_p$$

连续且解析，并在非负整数 $t$ 处等于 $u^{Nt}$。对 $s\ne t$，

$$\boxed{v_p(\Phi_p(s)-\Phi_p(t))=h_p+v_p(s-t).}$$

此外，

$$\boxed{\overline{\{u^{Nn}:n\ge0\}}=\exp(p^{h_p}\mathbb Z_p d),\qquad
[T_1:\overline{\{u^{Nn}:n\ge0\}}]=p^{h_p-1}.}$$

**证明。** 对 $z\in p\mathcal O_p$，对数级数首项的估值严格低于其余项；指数级数亦然。于是 $v_p(\log(1+z))=v_p(z)$，且指数与对数在主单位上互逆。范数的对数是迹，因此范数一对应迹零。$\mathcal O_p$ 的迹零部分为 $\mathbb Z_p d$。将 $\beta_p$ 写为 $p^{h_p}cd$，其中 $c\in\mathbb Z_p^\times$，得到估值公式。非负整数在 $\mathbb Z_p$ 中稠密，所以 $\{n\beta_p:n\ge0\}$ 的闭包为 $p^{h_p}\mathbb Z_p d$，指数映射与一维格指数给出结论。

**推论。** WSS 条件等价于上述真实 p-进轨道闭包在 $T_1$ 中具有非平凡有限指数。局部流的完整描述以实际 $h_p$ 为参数，尚未决定变动素数 $p$ 上哪些 $h_p\ge2$。该流的参数空间是 $\mathbb Z_p$，没有把它作为实连通时间区间到全不连通空间的非平凡连续路径。

#### CG.4 Fibonacci 多项式的单根与固定参数偏移

**定义。** 令 $U_0(X)=0,U_1(X)=1$、$V_0(X)=2,V_1(X)=X$，两列都满足 $P_{n+2}(X)=XP_{n+1}(X)+P_n(X)$。

**命题。** 对所有 $n\ge0$，在 $\mathbb Z[X]$ 中有

$$(X^2+4)U_n'(X)=nV_n(X)-XU_n(X).$$

**证明。** 在 $\mathbb Q(X,\sqrt{X^2+4})$ 中，取二次方程的两根 $\alpha,\beta$，令 $D=\alpha-\beta$。有 $D^2=X^2+4$、$D'=X/D$、$\alpha'=\alpha/D$、$\beta'=-\beta/D$。对 $U_n=(\alpha^n-\beta^n)/D$ 求导，得到显示公式。两端为整数多项式，故该恒等式回到 $\mathbb Z[X]$。

**定理。** 对每个 $p>5$，

$$\boxed{U_N'(1)\equiv-2/5\not\equiv0\pmod p.}$$

在 $1+p\mathbb Z_p$ 中，$U_N$ 恰有一个根 $a_p$，并且

$$v_p(a_p-1)=h_p,\qquad
(a_p-1)/p\equiv(5/2)q_p\pmod p.$$

**证明。** $U_N(1)=F_N\equiv0$、$V_N(1)=L_N\equiv2\chi$，而 $N\equiv-\chi\pmod p$。导数恒等式给出 $5U_N'(1)\equiv-2$。Hensel 单根提升定理给出唯一根。对于 $x,y\in1+p\mathbb Z_p$，多项式差商模 $p$ 恒为这个非零导数，所以 $v_p(U_N(x)-U_N(y))=v_p(x-y)$。取 $x=1,y=a_p$ 得估值等式。最后 Taylor 展开给出

$$U_N(1+pt)\equiv p(q_p-2t/5)\pmod{p^2},$$

得到首位偏移。

**实例。** $p=7$ 时 $N=8,q_7=3$，唯一参数提升为 $a_7\equiv29\pmod{49}$。这不使七成为 WSS 素数，因为原序列固定参数 $X=1$。WSS 判定是该固定参数是否已经落在根上至模 $p^2$，而不是根是否存在或是否光滑。

#### CG.5 真实三维黄金映射环面的同调接口

**定义。** 令

$$A=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
B=A^2=\begin{pmatrix}2&1\\1&1\end{pmatrix},\qquad
S=2A-I=\begin{pmatrix}1&2\\2&-1\end{pmatrix}.$$

$B$ 在实紧致环面 $\mathbb R^2/\mathbb Z^2$ 上定义自同构。对正偶数 $n$，令 $M_n$ 为 $B^n$ 的映射环面。

**定理。** 对每个正偶数 $n$，

$$B^n-I=F_nSA^n,$$

$$\boxed{H_1(M_n;\mathbb Z)\cong\mathbb Z\oplus\mathbb Z/F_n\oplus\mathbb Z/(5F_n).}$$

因此，对 $n=p-(5/p)$、$p>5$，

$$\boxed{\operatorname{Tor}H_1(M_n;\mathbb Z)[p^\infty]
\cong(\mathbb Z/p^{h_p})^2.}$$

**证明。** $A^n=F_nA+F_{n-1}I$，且 $I-A=-A^{-1}$。偶数 $n$ 时，将两者相减得到 $A^n-A^{-n}=F_n(2A-I)$，再乘以 $A^n$。矩阵 $A^n$ 整数可逆，而 $S$ 的元素最大公约数为一、行列式为 $-5$，所以 Smith 对角为 $(1,5)$，返回矩阵的 Smith 对角为 $(F_n,5F_n)$。映射环面的基本群为 $\mathbb Z^2\rtimes_{B^n}\mathbb Z$，阿贝尔化为时间方向 $\mathbb Z$ 与 $B^n-I$ 的余核之直和。取 $p$-初等部分得到末式。

**推论。** 原 WSS 条件等价于这个指定三维覆盖的一阶同调中存在阶为 $p^2$ 的元素。等价式依赖随 $p$ 变化的同一个覆盖次数 $N$；它没有从实双曲伸缩或三维拓扑分类中得到额外的素数深度约束。

#### CG.6 算术微分与被迹删除的一阶信息

**定义。** 在 $\mathcal O_p$ 上令 $\sigma_p$ 为 Frobenius 提升：$\chi=1$ 时取恒等，$\chi=-1$ 时取黄金共轭。定义

$$\delta_p(x)=\frac{\sigma_p(x)-x^p}{p}.$$

分子在 $p\mathcal O_p$ 中，所以此定义在除以 $p$ 后仍取值于 $\mathcal O_p$。

**命题。** 对任意 $x,y\in\mathcal O_p$，

$$\delta_p(xy)=x^p\delta_p(y)+y^p\delta_p(x)+p\delta_p(x)\delta_p(y).$$

并有

$$\boxed{\delta_p(\phi)\equiv-(d/2)\phi^\chi q_p\pmod p.}$$

**证明。** 将 $\sigma_p(x)=x^p+p\delta_p(x)$ 代入乘法保持关系，展开即得第一式。由 $(L_N-2\chi)(L_N+2\chi)=5F_N^2$ 且第二因子模 $p$ 为单位，得到 $L_N\equiv2\chi\pmod{p^2}$。因此 $\phi^N\equiv\chi+(d/2)pq_p\pmod{p^2}$。若 $\chi=1$，乘以 $\phi$；若 $\chi=-1$，乘以 $\phi^{-1}$，并使用 $-\phi^{-1}=\psi$。两种情形均得到显示公式。

**推论。** $q_p=0$ 当且仅当 $\delta_p(\phi)=0\pmod p$。另一方面，

$$v_p(L_N-2\chi)=2h_p.$$

所以普通返回迹在模 $p^2$ 上对所有这些素数都返回，已经删除了原缺陷的一阶信息。算术微分的乘积律与实导数不同，不能未证明地移入实几何流的微分方程或估计。

#### CG.7 切空间读数、圆周等分布与精确零点

**定义。** 令 $c_p\in\{0,\ldots,p-1\}$ 为 $\chi q_p$ 的整数代表，$w_p=c_p/p\pmod{\mathbb Z}\in\mathbb R/\mathbb Z$。以 $\mathbb Z d$ 为 $T$ 的迹零 Lie 格，CG.1 表明这正是由 $u^N\bmod p^2$ 的切空间缺陷除以 $p^2$ 得到的圆周读数。$u$ 不是扭元素，因此在一维环面的几何泛纤维中生成 Zariski 稠密子群。

**命题。** $w_p=0$ 当且仅当 $p$ 为原 WSS 素数。圆周上 Haar 等分布的性质本身，不推出这种零点至少出现一次。

**证明。** 第一项由 $\chi$ 是单位直接得到。为说明后一项，按递增顺序记素数为 $p_j$，取任意无理实数 $\theta$，令

$$b_{p_j}=1+\lfloor(p_j-1)\{j\theta\}\rfloor.$$

有 $1\le b_{p_j}\le p_j-1$，且 $|b_{p_j}/p_j-\{j\theta\}|\le2/p_j\to0$。无理旋转的等分布和连续函数在紧圆周上的一致连续性，说明 $b_{p_j}/p_j$ 仍等分布，然而它永不为零。这只是对一般推理的反例，没有把这列人工余数当成 Fibonacci 余数。

**恒等式。** 令 $Z(X)=\#\{5<p\le X:p\text{ 素且 }q_p=0\}$。字符正交性给出

$$Z(X)=\sum_{5<p\le X}\frac1p+
\sum_{5<p\le X}\frac1p\sum_{a=1}^{p-1}\exp(2\pi i a c_p/p).$$

若第二项能被独立证明为 $o(\log\log X)$，则 Mertens 素数调和和公式将给出 $Z(X)\sim\log\log X$。本节没有证明这个误差估计。固定频率的宏观等分布只控制每个固定 $a$ 的平均，不能直接替代同时到 $a=p-1$ 的精确零点尺度。

#### CG.8 不同接口的共同假设边界

**命题。** CG.1–CG.7 保留原黄金单位，但没有强制任何变动素数满足 $h_p\ge2$。其中局部流、唯一提升、根位置和三维同调都容许 $h_p=1$ 与 $h_p\ge2$；将它们互相代换不产生新的素数存在结论。

**证明。** CG.2 在同一个约化点上同时构造一个保周期提升及 $p-1$ 个不保周期提升。CG.3 的公式以原 $h_p$ 为输入，CG.4 将同一个深度记为固定参数到唯一根的距离，CG.5 将它记为同调挠阶，CG.6 将它记为算术微分的零阶。上述等价关系均不排除原固定点始终选中非零的一阶缺陷。CG.7 又排除了仅由宏观均匀性推出精确零点的推理。因此跨素数的深度控制仍需独立命题。


### RNI. Constructive normalization of the fixed-golden radical tower

#### RNI.1 The fixed unit, canonical orders, and local depth

**Definition.** Retain K=Q(sqrt(5)), O=Z[phi], phi^2=phi+1, and psi=1-phi=-phi^(-1). For a positive n coprime to ten, choose the positive real root theta_n of X^n-phi, and set

$$
E_n=K(\theta_n)=\mathbb Q(\theta_n),\qquad
R_n=O[\theta_n]=\mathbb Z[\theta_n],\qquad
I_n=[O_{E_n}:R_n].
$$

The notation E_n denotes a number field, not a Fibonacci or Lucas value. For p odd and different from five, put epsilon_p=(5/p), N_p=p-epsilon_p, and retain the actual depth h_p=v_p(F_(N_p)) and quotient q_p=F_(N_p)/p modulo p.

**Theorem RNI1.** The polynomial X^(2n)-X^n-1 is irreducible, [E_n:Q]=2n, and

$$
|\operatorname{disc}(R_n)|=5^n n^{2n}.
$$

**Proof.** If b^r=phi in K for an odd prime r, then b is an algebraic unit, N_(K/Q)(b)=-1, and its chosen real value lies strictly between one and phi. Its integral trace b-b^(-1) lies strictly between zero and phi-phi^(-1)=1, a contradiction. Capelli's binomial criterion now makes X^n-phi irreducible for odd n; the exceptional fourth-power case does not occur. The degree-two composition is irreducible as well. The relative order has O-basis 1,theta_n,...,theta_n^(n-1), with discriminant a unit times n^n. The tower formula and disc(K)=5 give the absolute magnitude. For n=1 the assertions hold directly. The Capelli criteria and the degree-p discriminant are recorded in Jones, arXiv:2302.10357, Theorems 2.3-2.4 and Proposition 2.5.

**Lemma.** Let P be a prime of K above p, F=K_P, and f=[F:Q_p]. Then F is unramified, f is one or two, and, with v(p)=1,

$$
v\bigl(\phi^{p^f-1}-1\bigr)=h_p.
\tag{RNI2}
$$

This equality holds at every completion above p. If a=phi when epsilon_p=1 and a=psi when epsilon_p=-1, then also

$$v(a^p-\phi)=h_p.\tag{RNI3}$$

**Proof.** For N=N_p, the identity u^N-1=sqrt(5)F_N psi^(-N), with u=-phi^2, shows v(phi^(2N)-1)=h_p at each completion. Since phi^N reduces to epsilon_p, the factor phi^N+epsilon_p is a unit; hence v(phi^N-epsilon_p)=h_p. This proves RNI2 in the split case. In the inert case raise phi^(p+1)=-1+O(p^h_p) to the even exponent p-1, which is a p-adic unit. Factoring a power difference, or the principal-unit logarithm, preserves the valuation. RNI3 is immediate in the split case. In the inert case psi^p-phi=-phi^(-p)(1+phi^(p+1)), giving the same valuation. All depths are finite since phi is not a root of unity.

#### RNI.2 Local field factors and the full normalization index

**Lemma RNI4.** Let F/Q_p be a finite unramified extension, p odd, with ring O_F, residue cardinality p^f, and v(p)=1. Let u be a unit with finite h=v(u^(p^f-1)-1). For a>=0, let B be the integral closure of A=O_F[X]/(X^(p^a)-u) in its finite etale F-algebra. Then

$$
\boxed{\operatorname{length}_{O_F}(B/A)
=\sum_{i=1}^{\min(a,h-1)}p^{a-i}.}\tag{RNI4}
$$

**Proof.** Remove the Teichmueller part of u by scaling X. This is possible because taking a p^a-th power is an automorphism on the roots of unity of order prime to p in F. Thus assume u is a principal unit. The logarithm is an isomorphism from 1+pO_F to pO_F and preserves valuation. This follows directly because in its convergent series the linear term has smaller valuation than all higher terms; the exponential supplies its inverse. Consequently a p^b-th root in F exists exactly when b<=h-1. This criterion also follows for arbitrary units by restoring the Teichmueller factor.

Put s=min(a,h-1), t=a-s, and choose beta in 1+pO_F with beta^(p^s)=u. If t>0, then v(beta-1)=1. Factor the binomial over F as

$$
X^{p^a}-u=(X^{p^t}-\beta)
\prod_{j=1}^s\left[\prod_{\zeta\ \mathrm{primitive}\ p^j\mathrm{th}}
(X^{p^t}-\beta\zeta)\right].\tag{RNI5}
$$

For j>=1 put F_j=F(zeta_(p^j)) and e_j=p^(j-1)(p-1). After shifting X by one, X^(p^t)-beta*zeta_(p^j) is Eisenstein over F_j when t>0: the constant term has uniformizer valuation one, and all intermediate binomial coefficients are divisible by p. Indeed beta-1 has valuation at least e_j there, whereas zeta_(p^j)-1 has valuation one. Its root alpha_j contains F_j because zeta_(p^j)=alpha_j^(p^t)/beta. Thus each bracket in RNI5 is irreducible of degree p^t*e_j. The first factor is Eisenstein of degree p^t if t>0 and is linear otherwise. When t=0, the brackets are scaled cyclotomic polynomials. These factors exhaust the algebra because their degrees sum to p^a.

The maximal order in each Eisenstein component is generated by the shifted root. The cyclotomic discriminant exponent over F is

$$d_j=p^{j-1}\bigl(j(p-1)-1\bigr).$$

For completeness, Phi_(p^j)(X)=(X^(p^j)-1)/(X^(p^(j-1))-1). At zeta_(p^j) its derivative has valuation j*e_j-p^(j-1) in F_j. The shifted cyclotomic polynomial is Eisenstein, so this derivative computes the different and hence the stated discriminant exponent. The formula remains valid after unramified base change.

In the further degree p^t extension over F_j the derivative is p^t*alpha_j^(p^t-1). As alpha_j is a unit, its relative discriminant has exponent t*p^t*e_j at the prime of F_j. Discriminant transitivity gives the exponent p^t*d_j+t*p^t*e_j over F. The first factor contributes t*p^t. Using

$$
\sum_{j=1}^s e_j=p^s-1,\qquad
\sum_{j=1}^s d_j=s p^s-2\sum_{j=1}^s p^{s-j},
$$

the product of all maximal component discriminants has exponent

$$a p^a-2\sum_{i=1}^s p^{a-i}.$$

The polynomial order has discriminant exponent a*p^a. The discriminant-index identity therefore proves RNI4. The case a=0 is the identity algebra. The Eisenstein integral-generator and different facts used here are classical; see Sutherland, MIT 18.785 Lecture 11, Lemma 11.4 and Theorem 11.5, and Lecture 12, Proposition 12.24 and Proposition 12.28.

**Theorem RNI6.** For n coprime to ten, and p|n, write a_p=v_p(n) and s_p=min(a_p,h_p-1). Then

$$
\boxed{v_p(I_n)=2\frac{n}{p^{a_p}}
\sum_{j=1}^{s_p}p^{a_p-j}.}\tag{RNI6}
$$

No prime not dividing n divides I_n. Consequently

$$\boxed{|\operatorname{disc}(E_n)|=5^n n^{2n}/I_n^2.}\tag{RNI7}$$

**Proof.** At a completion F of K above p, write n=p^a*m with p not dividing m. The algebra O_F[X]/(X^m-phi) is finite etale because phi and m are units. It is a product of unramified valuation rings with residue degrees summing to m. At every component root b, the principal-unit logarithm satisfies m*log(<b>)=log(<phi>), so the depth remains h_p under this unramified extension. Apply RNI4 to adjoining its p^a-th root. The total O_F-index length is m times the sum in RNI4. The residue degrees of the completions of K above p sum to two, giving RNI6 as an absolute Z-index exponent. At primes not dividing n, the relative order is finite etale over the local ring of O, hence integrally closed. This includes the prime above five. RNI1 and the discriminant-index identity prove RNI7.

#### RNI.3 An explicit global integral basis in the exceptional case

**Definition.** For p odd and different from five, set

$$
a_p=\begin{cases}\phi,&(5/p)=1,\\\psi,&(5/p)=-1,\end{cases}
\qquad z_p=\theta_p-a_p,\qquad
\eta_p=\frac{z_p^{p-1}}p.
$$

Here a_p is a shift element and is distinct from the exponent notation in RNI6.

**Theorem RNI8.** The element eta_p is an algebraic integer if and only if q_p=0. If q_p=0, then

$$
\boxed{O_{E_p}=R_p+O\eta_p,\qquad
O_{E_p}/R_p\cong O/pO,\qquad I_p=p^2.}\tag{RNI8}
$$

An integral Z-basis is

$$
\boxed{\{z_p^i,\phi z_p^i:0\le i\le p-2\}
\ \cup\ \{\eta_p,\phi\eta_p\}.}\tag{RNI9}
$$

If q_p is nonzero, R_p is already the full ring of integers.

**Proof.** At each unramified completion F of K above p, RNI3 gives the constant-term valuation h_p of (X+a_p)^p-phi. If h_p=1, this polynomial is Eisenstein. Therefore v(z_p)=1/p and v(eta_p)=-1/p, which proves nonintegrality. RNI6 also gives I_p=1.

If h_p>=2, the unit-root criterion in RNI4 gives b in F with b^p=phi. Its residue is the same as a_p, because Frobenius on the residue field is injective and a_p^p=phi there. The local algebra is F times F(zeta_p). On the first component z_p=b-a_p has valuation at least one. On the cyclotomic component z_p=b(zeta_p-1)+(b-a_p) has valuation 1/(p-1). Thus eta_p is integral in both components. It is integral away from p because its only denominator is p.

The O-lattice obtained by replacing z_p^(p-1) in the power basis by eta_p has quotient O/pO over R_p. It has absolute index p^2 and is contained in O_(E_p). Formula RNI6 gives precisely the same full index, so equality holds. Multiplying this O-basis by the Z-basis 1,phi of O proves RNI9. This specifies a maximal order and its entire missing lattice, not merely a divisibility test for its index.

Jones, *A new condition for k-Wall-Sun-Sun primes*, Theorem 1.1, already identifies q_p=0 with failure of the specified power basis to be integral-maximal. RNI8-RNI9 give the displayed explicit replacement basis. Failure of this power basis does not assert that E_p has no other power integral basis.

#### RNI.4 Exact composition and the absence of a mixed-prime defect term

**Theorem RNI10.** If gcd(m,n)=1 and gcd(mn,10)=1, then

$$\boxed{I_{mn}=I_m^n I_n^m.}\tag{RNI10}$$

If b_a=v_p(I_(p^a))/2 and b_0=0, then

$$\boxed{b_a-pb_{a-1}=\mathbf1_{a<h_p}.}\tag{RNI11}$$

**Proof.** At p|m, the exponent in RNI6 for mn is n times the exponent for m, while p does not divide I_n. The roles reverse at p|n, and other primes divide none of the indices. This proves RNI10. Subtract the two finite geometric sums in RNI6 to obtain RNI11, including a=1.

**Corollary.** For squarefree n coprime to ten,

$$
I_n=\prod_{p\mid n,\ q_p=0}p^{2n/p},\qquad
\log\operatorname{rd}(E_n)=\tfrac12\log5+\log n
-2\sum_{p\mid n,\ q_p=0}\frac{\log p}{p}.
$$

**Proof.** Set a_p=1 in RNI6 and take logarithms of RNI7 divided by [E_n:Q]=2n. These formulas depend on the actual zero set. They do not establish that the sum is positive, nor an independent bound for that set.

#### RNI.5 The canonical unramified Kummer extension and a global character target

**Definition.** For p>5 put H_p=K(zeta_p), V_p=H_p(theta_p), and Delta_p=Gal(H_p/Q). Identify Delta_p with Gal(K/Q) times (Z/pZ)^times. Let chi_5 be the sign character on the first factor and omega_p the tautological character on the second, both valued in F_p^times. Put lambda_p=chi_5*omega_p. Let

$$
C_p=\bigl(\operatorname{Cl}(H_p)/p\operatorname{Cl}(H_p)\bigr)
\big/\langle[\mathfrak p]:\mathfrak p\mid p\rangle.
$$

The final span is over F_p and denotes the images of the indicated ideal classes.

**Theorem RNI12.** The extension V_p/H_p is cyclic of degree p. It is unramified at every prime if and only if q_p=0. In that case all primes of H_p above p split completely in V_p. If q_p is nonzero, V_p/H_p is totally ramified of degree p at each prime above p.

**Proof.** The intersection of K and Q(zeta_p) is Q: the cyclotomic field is unramified away from p, whereas the nontrivial quadratic field K ramifies at five. Hence [H_p:K]=p-1. If c^p=phi in H_p, then b=N_(H_p/K)(c) would satisfy b^p=phi^(p-1), and (phi/b)^p=phi in K, contradicting RNI1. Kummer theory therefore gives degree p and cyclicity.

Away from p, X^p-phi has unit derivative over the local rings of H_p and is finite etale, so no ramification occurs. At p, if h_p>=2, phi has a p-th root in the unramified completion of K by RNI4. Since H_p also contains all p-th roots of unity, the polynomial splits completely at each such completion of H_p.

If h_p=1, the shifted degree-p polynomial is Eisenstein over each completion F of K. The extension F(theta_p) is totally ramified of degree p, while F(zeta_p)/F is totally ramified of degree p-1. Their compositum has degree p(p-1) because the degrees are coprime, and its ramification index is divisible by both p and p-1. Thus it is totally ramified, giving relative ramification index p over F(zeta_p). Finally H_p has only complex infinite places, so there is no additional infinite ramification to consider.

**Corollary RNI13.** If q_p=0, there is a Delta_p-equivariant surjection

$$\boxed{C_p\longrightarrow\mathbb F_p(\lambda_p).}\tag{RNI13}$$

In particular the lambda_p component of C_p is nonzero. Its vanishing is a sufficient condition for q_p to be nonzero.

**Proof.** The automorphism tau(theta_p)=zeta_p theta_p generates Gal(V_p/H_p). The lift of delta_a in the cyclotomic factor fixes theta_p and sends zeta_p to zeta_p^a, so delta_a tau delta_a^(-1)=tau^a. The golden conjugation lifts by theta_p mapping to -theta_p^(-1) and zeta_p fixed; it conjugates tau to tau^(-1). These formulas show that Gal(V_p/H_p), as an F_p[Delta_p]-module, is F_p(lambda_p).

For an everywhere-unramified abelian extension, global Artin reciprocity gives a surjection from the ideal class group onto its Galois group. The quotient has exponent p, and splitting of the primes above p puts their classes in its kernel. Equivariance gives the stated map. Since p does not divide |Delta_p|=2(p-1), the character decomposition over F_p is semisimple, so the lambda_p component must be nonzero. This uses the classical Hilbert class field theorem, as stated in J. S. Milne, *Class Field Theory*, version 4.03 (2020), Chapter V, https://www.jmilne.org/math/CourseNotes/CFT.pdf . No converse for arbitrary nonzero class-group components is asserted.

**Proposition.** RNI12 constructs a specific extension from the original golden unit. RNI13 requires a class-group estimate with the character lambda_p varying with p to yield a new prime-family exclusion; nonvanishing or vanishing of that component has not been proved here.

**Proof.** The extension and its character are explicitly given by the displayed generators and conjugations. RNI13 is an implication from q_p=0, and supplies an exclusion only after its nonzero quotient is contradicted by independent information. RNI6 and RNI10 give no such contradiction, since their indices are expressed in terms of the same h_p. Consequently these constructions alone neither supply a WSS prime nor a new family of non-WSS primes.

**Proposition.** The quotient by the classes of primes above p in the definition of C_p does not change the lambda_p component of Cl(H_p)/pCl(H_p).

**Proof.** The cyclotomic subgroup Gal(H_p/K) fixes every prime above p, since the extension is totally ramified at each prime of K above p. Thus it fixes their class span. Its action on F_p(lambda_p) is the nontrivial character omega_p. As this subgroup has order p-1 prime to p, the fixed span has zero lambda_p component, proving the assertion.


### RCR. Norm descent, the exact reflected class component, and conductor two

#### RCR.1 A one-dimensional global radical

**Definition.** Fix p>5. Retain K=Q(sqrt(5)), O=Z[phi], H=K(zeta_p), V=H(phi^(1/p)), and the actual initial quotient q_p from RNI. Let J=Gal(H/K), Delta=Gal(H/Q), chi=chi_5, omega=omega_p, and lambda=chi*omega as in RNI. All character spaces in this subsection are over F_p. Define

$$
\mathcal V(H)=\{[a]\in H^\times/H^{\times p}:
                v_{\mathfrak P}(a)\equiv0\pmod p
                \text{ for every finite }\mathfrak P\}.
$$

The condition is independent of the representative. Define D_unr(H) to be the radical of the maximal elementary abelian everywhere-unramified p-extension of H. Kummer duality identifies that extension's Galois group with Cl(H)/pCl(H), with a pairing into mu_p. The Kummer correspondence and Hilbert class field theorem used here are classical; see J. S. Milne, *Class Field Theory*, Chapter VII, Appendix A, Proposition A.2 and Theorem A.3, and Chapter V, Theorems 3.5-3.6 and Example 3.9, https://www.jmilne.org/math/CourseNotes/CFT.pdf .

**Lemma RCR1.** The inclusion K^*/K^{*p} -> H^*/H^{*p} identifies the J-invariant subspace with K^*/K^{*p}. On this subspace its inverse is [a] -> [N_(H/K)(a)^(-1)]. Moreover

$$
\boxed{\mathcal V(H)^J=\mathbb F_p\cdot[\phi].}\tag{RCR1}
$$

This line has Delta-character chi.

**Proof.** If b in K is a pth power in H, norming gives b^(p-1) a pth power in K; since p and p-1 are coprime, b is a pth power in K. Thus inclusion is injective. For a J-invariant class [a], all its p-1 conjugate classes coincide, so

$$[N_{H/K}(a)]=[a]^{p-1}=[a]^{-1}$$

in H^*/H^{*p}. This gives both the asserted descent and its explicit inverse.

Let a virtual-unit class descend to b in K. For every prime v of K and every prime P of H above it, e(P/v) divides p-1. From p|v_P(b)=e(P/v)v_v(b), conclude p|v_v(b). Hence (b)=a_0^p for a fractional ideal a_0 of K. The golden ring is norm-Euclidean and therefore a PID, so a_0=(c) and b=epsilon*c^p. Its units are +/-phi^Z. The sign is a pth power since p is odd. Thus every such class lies in the displayed line. Conversely phi is a unit, so its class is a virtual unit and is J-invariant. It is nonzero by RNI1 and the norm argument above. Golden conjugation sends [phi] to [psi]=[phi]^(-1), since psi=-phi^(-1), giving character chi.

The two elementary golden-ring facts can also be justified directly. Rounding the two coefficients of a quotient leaves a norm of absolute value at most 5/16, giving Euclidean division. For unit classification, make a unit positive in the chosen real embedding and multiply by a power of phi to put its value in [1,phi). A value strictly between one and phi would have integral trace strictly between zero and one if its norm is -1, or strictly between two and sqrt(5) if its norm is +1. Both are impossible. Thus the normalized unit is one.

#### RCR.2 The converse to RNI13 and exact multiplicity

**Theorem RCR2.** Put A=Cl(H)/pCl(H). Then

$$
\boxed{\dim_{\mathbb F_p} A^{(\lambda)}
=\begin{cases}0,&q_p\ne0,\\1,&q_p=0.\end{cases}}\tag{RCR2}
$$

If the component is nonzero, the elementary class field corresponding to the quotient A^(lambda) is exactly V. In particular there cannot be two independent unramified elementary p-extensions with this Delta-character.

**Proof.** Take the maximal unramified elementary extension W/H corresponding to the lambda quotient of A. It is stable under Delta. Its Kummer radical D has character omega*lambda^(-1)=chi: in the equivariant pairing Gal(W/H) x D -> mu_p, the two input characters multiply to omega. Thus D is J-invariant.

For every finite prime P, an unramified pth-root extension has integral valuation group, so p divides v_P(a) for any radical representative a. Therefore D is a subspace of the virtual-unit space V(H)^J. By RCR1 it is contained in the one-dimensional line generated by phi. RNI12 proves that this line is unramified exactly when q_p=0. It follows that D is zero in the non-WSS case and is the full line in the WSS case. Kummer duality proves the dimension statement and the field equality.

This completes the converse not asserted in RNI13, using the PID and unit-group properties of the fixed golden field. It is a specialization of the classical Kummer/reflection mechanism, not an independent nonvanishing estimate for the original quotient.

**Corollary.** Let A_lambda be the lambda component of the full p-primary ideal class group, using the Teichmueller lift of lambda to Z_p. Then A_lambda is cyclic. It is trivial exactly when q_p is nonzero. The order of A_lambda in the nontrivial case is not determined by RCR2.

**Proof.** Since p does not divide |Delta|=2(p-1), the lifted character idempotent is integral over Z_p. Reduction modulo p identifies A_lambda/pA_lambda with A^(lambda). A finite abelian p-group with mod-p dimension at most one is cyclic; if that quotient is zero the finite group is zero.

**Proposition RCR3.** Let d=sqrt(5) and let <phi> be the principal-unit part of phi in O tensor Z_p, componentwise in the split case. Under the bases [phi] and d, localization of the line in RCR1 into principal units modulo pth powers is the scalar map

$$
\boxed{\frac1p\log\langle\phi\rangle
       \equiv-\frac{q_p}{2}d\pmod p.}\tag{RCR3}
$$

Its kernel is D_unr(H)^(chi).

**Proof.** The principal-unit logarithm identifies U_1/U_1^p with pO_p/p^2O_p. The trace of log<phi> is zero because the norm of phi is -1, a root of unity. Thus the image lies on the line generated by d. Put epsilon=(5/p), N=p-epsilon, and u=-phi^2. CG.1 gives

$$\log(u^N)/p\equiv\epsilon q_p d\pmod p.$$

On the other hand log(u^N)=2N log<phi>. Since N=-epsilon modulo p, division by 2N gives RCR3. The kernel consists of the classes whose representative is a pth power in every completion of K at p. The norm argument for the prime-to-p local extension to H shows that this is equivalent to being a local pth power after adjoining zeta_p. RNI12 and RCR2 identify precisely the same kernel with the unramified radical. This states a formula for the scalar; it does not prove that the scalar is zero or nonzero at a new prime.

#### RCR.3 Exact ramification conductors

**Definition.** At a prime P of H above p, the conductor exponent of a local abelian extension is the least c>=0 for which local reciprocity kills 1+P^c, with c=0 in the unramified case. A trivial local extension also has exponent zero.

**Lemma RCR4.** Let F/Q_p be unramified, p odd, H_0=F(zeta_p), and b in F^*. For a unit b, its depth means v_F(log< b >), where < b > is its principal-unit part; a root of unity has infinite depth. If p does not divide v_F(b), the cyclic degree-p extension H_0(b^(1/p))/H_0 has conductor exponent p+1. If b is a unit with v_F(log< b >)=1, its conductor exponent is two. If b is a unit of depth at least two, it is a pth power in F and the local extension is trivial.

**Proof.** In the first case replace b by b^r times a pth power, choosing r prime to p to make its valuation exactly one. This does not change its Kummer line. Set E=F(b^(1/p)), L=E(zeta_p). The polynomial X^p-b is Eisenstein; its derivative gives different exponent 2p-1 for E/F. Both E/F and H_0/F are totally ramified, of coprime degrees p and p-1. Their compositum has degree p(p-1) and ramification index divisible by both, so is totally ramified. The extension L/E is tame of degree p-1 and has different exponent p-2, while H_0/F also has different exponent p-2. Transitivity of differents, with valuations normalized separately in each top field, gives

$$
 d(L/H_0)=(p-1)(2p-1)+(p-2)-p(p-2)=p^2-1.
$$

For a cyclic extension of prime degree p, all p-1 nontrivial characters have the same conductor c, and the conductor-discriminant formula gives d(L/H_0)=(p-1)c, since the residue degree is one. Therefore c=p+1.

For a unit of depth one, choose a unit a in F lifting its residue pth root. The polynomial (X+a)^p-b is Eisenstein, and its derivative has different exponent p because the original root is a unit. The same tower argument yields

$$d(L/H_0)=(p-1)p+(p-2)-p(p-2)=2(p-1),$$

so c=2. At depth at least two the principal-unit logarithm constructs a pth root in F, including the unique pth root of the Teichmueller part. The local Kummer extension is then trivial.

The different and its tower law are classical; see A. V. Sutherland, MIT 18.785, Lecture 12, Proposition 12.24, Theorem 12.27 and Proposition 12.28, https://math.mit.edu/classes/18.785/2021fa/LectureNotes12.pdf . The conductor-discriminant formula is the classical local abelian formula, also discussed by Milne, *Class Field Theory*, Chapter V, Theorem 3.27.

**Corollary RCR5.** Put m_p=product_(P|p) P^2 as a modulus of H. The canonical extension V/H has conductor one when q_p=0 and conductor exactly m_p when q_p is nonzero. In the second case its local lower ramification groups satisfy G_0=G_1=C_p and G_2=1 at each prime above p.

**Proof.** RNI2 identifies the local unit depth of phi with h_p. RCR4 gives exponent zero or two at every prime above p; RNI12 rules out ramification elsewhere. In a cyclic degree-p totally ramified local extension with a single ramification break b, the different exponent is (b+1)(p-1). The computed exponent 2(p-1) forces b=1, proving the ramification-group statement.

#### RCR.4 The first ray layer is a cyclic extension of the class component

**Definition.** Let B_lambda be the Teichmueller-lambda component of the p-primary ray class group Cl_(m_p)(H), and retain A_lambda from RCR.2. There is no infinite part in the modulus, since H has only complex infinite places.

**Theorem RCR6.** There is an exact sequence of finite Z_p[Delta]-modules

$$
\boxed{0\longrightarrow\mathbb F_p(\lambda)
 \longrightarrow B_\lambda\longrightarrow A_\lambda\longrightarrow0.}\tag{RCR6}
$$

The group B_lambda is cyclic and B_lambda/pB_lambda has dimension exactly one. Its unique degree-p ray class extension is V. Consequently, for some c_p>=0,

$$
\boxed{A_\lambda\simeq\mathbb Z/p^{c_p}\mathbb Z,\qquad
B_\lambda\simeq\mathbb Z/p^{c_p+1}\mathbb Z,\qquad
c_p=0\iff q_p\ne0.}\tag{RCR7}
$$

**Proof.** The ray class exact sequence has kernel given by residue units modulo the image of global units. At each P|p, the p-primary part of (O_H/P^2)^* is (1+P)/(1+P^2), the additive residue field. With local uniformizer zeta_p-1, the cyclotomic subgroup acts on this layer by omega. The golden conjugation on the sum of the residue fields has a one-dimensional + part and a one-dimensional - part, in both the split and inert cases. The total residue-unit module is therefore F_p(omega) plus F_p(lambda).

Global units have zero image in its lambda part. Indeed H is a CM field, and for any unit epsilon, epsilon/bar(epsilon) is a root of unity: every conjugate has absolute value one, so Kronecker's theorem applies. The p-primary roots of unity of H are exactly mu_p; a primitive p^2-th root cannot lie in H because the local ramification index is only p-1. Golden conjugation fixes mu_p, while lambda is nontrivial on golden conjugation and is odd under complex conjugation. Projecting epsilon/bar(epsilon) into lambda gives 2 times the projected unit on one side and zero on the other. Since p is odd, that image is zero. Character projection of the ray class exact sequence proves RCR6. The exact sequence itself is stated in Milne, Chapter V, Theorem 1.7 and its proof on printed pages150-151.

To prove cyclicity, let W/H be the maximal elementary subextension of the lambda part of this ray class field. Its radical has character chi and descends to b in K by RCR1's norm argument. At primes not over p, it is unramified, so the valuations of b in K are multiples of p. At a prime over p, a valuation not divisible by p would, by RCR4, force conductor exponent p+1>2, contradicting the modulus. Thus all its valuations in K are multiples of p. Golden principality and the unit classification again force the entire radical into the line F_p*[phi]. Hence dim(B_lambda/pB_lambda)<=1. Conversely V is nontrivial and has conductor dividing m_p by RCR5, so the dimension is at least one. This proves cyclicity, uniqueness of the degree-p extension, and its identity with V.

Write |A_lambda|=p^{c_p}. RCR6 gives |B_lambda|=p^{c_p+1}, and cyclicity gives the displayed group isomorphisms. The final equivalence is RCR2. If c_p>=1, this exact sequence is nonsplit as a sequence of abelian groups: B_lambda is cyclic, whereas a splitting would have mod-p dimension two.

**Proposition.** The first-degree ramification distinction in RCR5 is compatible with RCR6 in both branches. If c_p=0, the order-p kernel in RCR6 is the entire ray component. If c_p>=1, it lies in pB_lambda and is killed by the unique elementary quotient, even though it is nontrivial in the full ray component.

**Proof.** In a cyclic group of order p^{c_p+1}, the unique order-p subgroup is p^{c_p}B_lambda. It equals the whole group when c_p=0 and is contained in pB_lambda otherwise. Local Artin reciprocity identifies it with the lambda residue-unit inertia image. Thus the elementary quotient is ramified in the first case and unramified in the second, as already computed directly.

**Proposition.** The preceding constructions do not determine c_p for WSS primes, do not identify c_p with h_p-1, and do not bound the number of primes with q_p=0. RCR2 identifies exact vanishing of the reflected class component with the original WSS decision.

**Proof.** RCR2 and RCR7 determine only whether c_p is zero, and their proofs use the original h_p solely through its threshold h_p>=2. No step compares the full class-group order with higher p-adic logarithmic precision. RCR3 displays the unresolved scalar explicitly. Therefore neither the bound on the number of generators nor existence of the ray class extension selects a previously unresolved zero or nonzero prime family.

#### RCR.5 An explicit second radical and the complete elementary conductor profile

**Definition.** For an integer c>=0 let m_c=product_(P|p) P^c, with m_0 the unit modulus. Let r_p(c) be the dimension over F_p of the lambda component of Cl_(m_c)(H)/pCl_(m_c)(H). For c=0 this is the ordinary class group. Count degree-p extensions inside a fixed algebraic closure of H, with the specified Delta-character lambda.

**Theorem RCR8.** For every p>5 and c>=0,

$$
\boxed{r_p(c)=
\begin{cases}
\mathbf1_{q_p=0},&c=0,1,\\
1,&2\le c\le p,\\
1+\mathbf1_{(5/p)=1},&c\ge p+1.
\end{cases}}\tag{RCR8}
$$

If p is inert in K, the only degree-p extension of this character unramified away from p is V. If p splits, there are exactly p+1 such extensions. One is V, of conductor one or m_2 according to q_p. Each of the other p extensions has conductor exactly m_(p+1).

**Proof.** The radical of any elementary extension of character lambda unramified away from p has character chi, so its classes descend by the norm map to K. At every prime of K not over p, the valuation is a multiple of p. Principality writes each such class as a unit times a product of generators of the primes above p. Thus its chi subspace is the chi part of the S-unit classes, with S the set of primes above p.

If p is inert, its sole prime ideal has rational generator p. This generator has trivial golden character and makes no contribution to chi. The remaining chi space is the line generated by phi.

If p splits as v*v', choose pi in O with (pi)=v. Then (sigma(pi))=v', where sigma is golden conjugation. The element

$$\beta_p=\pi/\sigma(\pi)$$

has valuations one and minus one at v,v', no other nonzero valuations, and sigma(beta_p)=beta_p^(-1). Consequently the chi space is exactly the two-dimensional space spanned by [phi] and [beta_p]. The classes are independent because the first has zero valuations and the second does not. This description uses an actual prime-ideal generator supplied by the golden PID, rather than a postulated auxiliary extension.

All these Kummer classes define extensions unramified away from p, since their valuations there are multiples of p and the residual characteristic is prime to the Kummer exponent. The line generated by phi has the conductor already calculated in RCR5. Every other line in the split case is generated by phi^i beta_p^j with j nonzero modulo p; it has valuations j and -j modulo p at the two primes of K above p. RCR4 gives conductor exponent p+1 at each prime of H above p. This proves the full filtration. A two-dimensional space over F_p has p+1 lines, whereas a one-dimensional space has one, proving the stated counts. Choosing a different generator pi multiplies beta_p by a power of phi and does not change the two-dimensional radical or the set of its lines.

RCR8 determines the elementary ramified extensions of the specified character without deciding q_p. In particular, passing from the first ray layer to arbitrarily large conductors introduces no further elementary characters in the inert family and precisely one further independent character in the split family. The WSS decision remains the conductor-zero versus conductor-two position of the same canonical golden line.
