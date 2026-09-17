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

### FPD. Recurrence-level square transport and maximal-prime descent

#### FPD.1 Original objects and the square-factor threshold

Use the original Fibonacci recurrence F_0=0, F_1=1 and
F_(n+2)=F_n+F_(n+1). A positive integer M is powerful when every prime
p dividing M also satisfies p^2|M. Thus one is powerful.
Put E={1,2,6,12}. For an odd prime p different from five, write
chi(p)=(p/5)=(5/p), and N(p)=p-chi(p). The standard WSS square condition
is p^2|F_(N(p)). Index primes and value-primes are different variables.

**Theorem FPD1.** （文献：T. Lengyel, Fibonacci Quart. 33 (1995) 234–239；L. A. Medina, E. Rowland, Fibonacci Quart. 53 (2015) 265–271, Theorem 1.4） For every prime p, positive n, and natural k, if
p|F_n, then

$$
\boxed{p^2\mid F_{nk}\quad\Longleftrightarrow\quad
       p^2\mid F_n\ \text{or}\ p\mid k.}
$$

This includes p=2 and k=0. It does not assume any initial valuation.

**Proof from the recurrence.** In R=Z/(p^2), put f=F_n, g=F_(n+1) and
c=F_(n-1). Then g=c+f and f^2=0. The Fibonacci addition formulas imply,
by simultaneous induction on k>=0,

$$
F_{n(k+1)}=(k+1)fg^k,\qquad
F_{n(k+1)+1}=g^{k+1}\quad\text{in }R.
$$

For the first induction step the new coordinate is
(k+1)fg^k c+g^(k+1)f. Replacing c by g-f gives
(k+2)fg^(k+1)-(k+1)g^k f^2, as required. The second new coordinate is
(k+1)f^2g^k+g^(k+2), also as required. The initial pair is (f,g).
Consecutive Fibonacci coprimality shows gcd(p,g)=1. Consequently, for
positive k, p^2|F_(nk) exactly when p^2|k F_n. Write F_n=p u and cancel
one p in the integers. Primality gives p|ku exactly when p|k or p|u.
The latter is equivalent to p^2|F_n. At k=0 both sides are true.

In particular, if p does not divide k, square divisibility is exactly
preserved between F_n and F_(nk). If p divides F_n simply and p does
not divide k, it still divides F_(nk) simply. A square produced solely
by multiplying the index by p is not an initial WSS exception.
For example F_7=13, 13^2|F_91, but F_14/13=29=3 modulo thirteen.

#### FPD.2 The small-support case is completely eliminated

**Lemma FPD2.** If m>0 has no prime divisor greater than five, then

$$
\boxed{F_m\text{ powerful}\quad\Longleftrightarrow\quad m\in E.}
$$

**Proof.** The exact small values are

$$
F_5=5,\quad F_8=3\cdot7,\quad F_9=2\cdot17,
\quad F_{25}=5^2\cdot3001.
$$

The number 3001 is prime, by trial division through its square root,
which is less than55. If 25|m, the factor3001 remains simple in F_m by
FPD1, since it cannot divide this small-support index. Thus 25 does not
divide m. If 5|m, write m=5k. The preceding exclusion makes 5 not divide
k; FPD1 at F_5 then gives another simple factor, a contradiction.
Likewise 9|m preserves the simple prime17 from F_9, and 8|m preserves
seven from F_8. Hence a powerful value forces 5 not dividing m,
9 not dividing m and 8 not dividing m. Unique factorization now gives
m|12. The six positive divisors of12 are1,2,3,4,6,12. Indices3 and4
give the simple values2 and3, and the four remaining values are1,1,8,144,
all powerful. This proves both directions without an external valuation
formula or a classification of perfect powers.

#### FPD.3 Prime-index factors escape the index support

**Lemma FPD3.** Suppose ell>=7 is prime and p is a prime divisor of
F_ell. Then the least positive Fibonacci zero index for p is ell, and
p>ell.

**Proof.** If p|F_j, strong divisibility gives
p|gcd(F_ell,F_j)=F_(gcd(ell,j)). Unless ell|j, primality of ell makes
that greatest common divisor one, impossible for p. Thus every zero
index is a multiple of ell. The initial zero at ell proves exact rank.

The cases p=2,5 are excluded by their zeros at indices3,5 respectively.
The existing golden Frobenius/rank theorem gives ell|p-1 or ell|p+1.
In the first case p>ell immediately. In the second, if p<=ell, the only
positive multiple of ell that can equal p+1 is ell itself. This gives
p+1=ell, impossible because both primes are odd. Thus p>ell in both
cases. No lower bound on the value-primes is assumed as an input.

#### FPD.4 Constructive descent to a maximal prime-index WSS block

**Theorem FPD4.** （方法先例：N. Robbins, Fibonacci Quart. 21 (1983) 215–218；V. Andrejić, Univ. Beograd Publ. Elektrotehn. Fak. Ser. Mat. 17 (2006) 38–44） If m>0, m is outside E, and F_m is powerful, then
there exists a prime ell>=7 such that

$$
\boxed{
\ell\mid m,\qquad
\forall q\text{ prime},\ q\mid m\Longrightarrow q\le\ell,
\qquad F_\ell\text{ is powerful}.
}
$$

Moreover every prime p dividing F_ell satisfies

$$
\boxed{p>\ell,\qquad p^2\mid F_{N(p)}.}
$$

**Proof.** By FPD2, m has a prime factor greater than five. Choose its
largest prime factor ell. It is at least seven. For each prime p|F_ell,
FPD3 gives p>ell, so p does not divide m. Write m=ell k. Fibonacci
divisibility gives p|F_m; powerfulness gives p^2|F_m. In FPD1 the
alternative p|k is impossible because k|m. Therefore p^2|F_ell.
This proves powerfulness of the entire prime-index block.

FPD3 gives its actual entry point ell. Apply the golden rank bound to
obtain ell|N(p), and then F_ell|F_(N(p)). Thus the square divisibility
also holds at p's own signed Frobenius index. Since p>ell>=7, the small
and ramified primes are automatically absent from this endpoint.
The theorem does not assert that the index-prime ell is WSS.

#### FPD.5 Consequences and the remaining open arithmetic

**Corollary.** The following two assertions are equivalent:

$$
\begin{aligned}
&\forall m>0,\quad F_m\text{ powerful}\Longrightarrow m\in E;\\
&\forall\ell\ge7\text{ prime},\quad F_\ell\text{ is not powerful}.
\end{aligned}
$$

If the first assertion fails, its least counterexample index is prime
and at least seven.

**Proof.** The forward implication specializes to prime indices. For
the reverse, a nonclassical counterexample would descend by FPD4 to a
prime-index counterexample. For the least one, the descending prime
ell satisfies ell<=m and is itself a counterexample, so minimality
forces ell=m. Neither assertion is established by this equivalence.

For a prime index ell>=7, the existence of a simple prime divisor of
F_ell is equivalent to the existence of a non-WSS prime of exact rank
ell. Indeed, FPD3 supplies the exact rank, and ell|N(p) with p not
dividing N(p)/ell allows FPD1 to identify the two square-divisibility
conditions. Thus a remaining target is an independent simple-factor
existence theorem at prime indices. A primitive-prime theorem only
supplies a prime with that rank and does not assert exponent one.

Absence of all WSS primes would imply the first classification above,
since every nontrivial prime-index Fibonacci value has a prime divisor.
The classification's failure would produce WSS primes by FPD4. The
converse implication from a single WSS prime to failure of the powerful
classification is not asserted: the other factors of its rank block
may still be simple.

A prospective stronger lifting theorem is preservation of the entire
p-valuation under a multiplier coprime to p. The square-zero argument
already identifies its mechanism: at an actual initial depth e>=1,
F_n^2 vanishes modulo p^(e+1). Proving the corresponding depth theorem
requires retaining the nondivisibility at p^(e+1), the nonzero index and
the coprime multiplier. The present public transfer theorem certifies
the square threshold only; it does not silently assert that extension.

#### FPD.6 Source roles and mathematical scope

FPD1 is a recurrence proof of a classical special case of the Fibonacci
valuation theory of Lengyel, recorded in Medina and Rowland,
*p-regularity of the p-adic valuation of the Fibonacci sequence*,
The Fibonacci Quarterly53(2015),265-271, Theorem1.4,
https://arxiv.org/abs/0910.2907 . The source proof here does not use that
theorem as an axiom or a lifting hypothesis.

Bates, Jesubalan, Lee, Lu and Shim, *Powerful Fibonacci polynomials over
finite fields*, arXiv:2601.02664v1 (2026), Theorem1.2 and Section2.1,
https://arxiv.org/html/2601.02664v1 , classify a polynomial problem over
finite fields and explicitly distinguish the conditional integer
powerful-number problem. A finite-field polynomial multiplicity does
not determine divisibility of an evaluated integer by p squared.
Their theorem is contextual prior work, not an input to FPD1-FPD4.

The full classification and WSS
existence remain open targets of this line, not conclusions of FPD4.


### THS. Exact theta sieving and the principal-orbit coefficient

#### THS.1 The integer Fourier condition

**Definition.** Put phi=(1+sqrt(5))/2, O=Z[phi], and retain the original Fibonacci and Lucas numbers. For z=x+iy with y>0, define

$$
\Theta(z)=\sum_{n\in\mathbb Z}e^{2\pi i n^2z},\qquad
V_d(z)=\sqrt y\,\Theta(5d^2z)\overline{\Theta(z)}\quad(d\ge1),
$$

$$
C_d(b;y)=\int_0^1\Theta(5d^2z)\overline{\Theta(z)}e^{-2\pi i b x}\,dx
\quad(b=4,-4).
$$

**Theorem THS1.** For every positive integer d,

$$
C_d(b;y)=\sum_{5d^2u^2-v^2=b}e^{-2\pi y(5d^2u^2+v^2)},
$$

$$
C_d(4;y)=4e^{8\pi y}\sum_{\substack{n\ge1\text{ odd}\\d\mid F_n}}
 e^{-20\pi yF_n^2},
$$

$$
C_d(-4;y)=2e^{-8\pi y}+4e^{-8\pi y}
 \sum_{\substack{n\ge2\text{ even}\\d\mid F_n}}e^{-20\pi yF_n^2}.
\tag{THS1}
$$

**Proof.** Gaussian decay gives absolute uniform convergence on each compact horizontal segment. Termwise integration retains exactly the pairs with 5d^2u^2-v^2=b. For w=d|u|>0 and |v|>0, the equation v^2-5w^2=+/-4 implies that (|v|+w sqrt(5))/2 is a positive golden unit greater than one. Its two coordinates have the same parity, so it belongs to O. The classification O^*={+/-phi^n:n in Z} gives (|v|,w)=(L_n,F_n). The norm selects even n for +4 and odd n for -4. Each positive solution has four sign choices. When b=-4 there are additionally u=0,v=+/-2; their combined weight is 2e^(-8pi y). There are no other zero-coordinate solutions. Substituting v^2=5w^2-b gives the exponential factors shown. The two indices with F_1=F_2=1 belong to different norm equations and are counted separately.

The Pell-to-theta mechanism is classical and is used by E. Assaf, C. I. Kuan, D. Lowry-Duda and A. Walker, *The Fibonacci Zeta Function and Modular Forms*, arXiv:2502.01415v1, Proposition 2 and Section 3. THS1 retains an additional exact divisibility condition on the integer coordinate; no congruence approximation to the Pell equation is used.

#### THS.2 All square-conductor levels and inert Hecke operators

**Definition.** Let chi_5 denote the quadratic character of conductor five. The standard theta transformation law makes V_d a weight-zero automorphic function of level 20d^2 and character chi_5 induced to that level. It has moderate growth; membership in L^2 is not assumed. At a prime ell not dividing 10d, use the good Hecke normalization

$$
(T_\ell f)(z)=\ell^{-1/2}\left[
\chi_5(\ell)f(\ell z)+\sum_{j=0}^{\ell-1}f((z+j)/\ell)\right].
$$

**Theorem THS2.** If chi_5(ell)=-1, then T_ell V_d=0. Consequently V_p-V_(p^2), viewed at common level 20p^4, is killed by every such good inert operator with ell not dividing 10p.

**Proof.** Expanding the translation sum introduces

$$
\sum_{j=0}^{\ell-1}e^{2\pi i j(5d^2u^2-v^2)/\ell}.
$$

It equals ell or zero, according as 5d^2u^2-v^2 is zero or nonzero modulo ell. Inertness and ell not dividing d force both u and v to be multiples of ell in the first case. Replacing them by ell*u_0,ell*v_0 turns the surviving exponential into its value at ell*z; the scalar factor is ell*sqrt(y/ell)=sqrt(ell*y). Thus the translation sum is V_d(ell*z), and chi_5(ell)=-1 gives cancellation. Gaussian convergence justifies the interchanges. This proof uses no squarefreeness of 5d^2. The last statement follows by linearity.

**Corollary THS3.** If a simultaneous good-Hecke Maass cusp eigenform g has a nonzero Petersson pairing with V_d, its cuspidal representation satisfies

$$\pi_g\simeq\pi_g\otimes\chi_5.$$

It is therefore dihedral. The same conclusion holds for a nonzero cusp pairing with V_p-V_(p^2).

**Proof.** The cusp decay of g and moderate growth of V_d make the pairing convergent. Hecke adjointness, with the nonzero character scalar included, and THS2 force g's eigenvalue at every good inert ell to vanish. At a good split prime twisting leaves its eigenvalue unchanged; at an inert prime the zero eigenvalue is also unchanged. The local determinant is multiplied by chi_5(ell)^2=1. Strong multiplicity one gives the self-twist, and the classical quadratic-self-twist characterization gives the dihedral conclusion. Both inputs are stated in N. Walji, *Further refinement of strong multiplicity one for GL(2)*, arXiv:1308.1469. This argument concerns cuspidal projections, including oldvectors, and does not assert disappearance of all continuous or residual terms in a regularized expansion.

#### THS.3 The heat coefficient with a uniform error

**Definition.** For p>5 set r=rho(p), R=rho(p^2), where rho denotes the least positive Fibonacci zero index. Define

$$
K_p(t)=\sum_{\substack{n\ge1\\p\parallel F_n}}e^{-tF_n^2},\qquad
S_a(t)=\sum_{k\ge1}e^{-tF_{ak}^2}\quad(t>0).
$$

**Theorem THS4.** The exact Fourier difference

$$
\tfrac14\left[e^{-8\pi y}(C_p(4;y)-C_{p^2}(4;y))
 +e^{8\pi y}(C_p(-4;y)-C_{p^2}(-4;y))\right]
$$

is K_p(20pi*y). Moreover K_p(t)=S_r(t)-S_R(t), and for every a>=3 and 0<t<=1,

$$
\left|S_a(t)-\frac{\log(1/t)}{2a\log\phi}\right|\le2,
$$

$$
\boxed{\left|K_p(t)-\kappa_p\log(1/t)\right|\le4,\qquad
\kappa_p=\frac{1/r-1/R}{2\log\phi}.}\tag{THS4}
$$

**Proof.** Subtract THS1 at d=p and d=p^2; the zero-coordinate terms cancel. The zero indices modulo each positive modulus are precisely the multiples of its least zero index, by strong Fibonacci divisibility. This proves the two exact identities.

For the estimate, phi^(n-2)<=F_n<=phi^(n-1) for n>=2. Put Q=phi^(2a) and A(v,Q)=sum_(k>=1)exp(-vQ^k). Then

$$A(t\phi^{-2},Q)\le S_a(t)\le A(t\phi^{-4},Q).$$

For the decreasing function x mapping to exp(-vQ^x), the integral test gives

$$E_1(v)/\log Q-1\le A(v,Q)\le E_1(v)/\log Q,\qquad
E_1(v)=\int_v^\infty e^{-u}\,du/u.$$

For 0<v<=1, splitting the integral at one gives |E_1(v)+log v|<=1: the integral of (e^(-u)-1)/u from v to one lies in [-1,0], and the remaining tail lies in [0,e^(-1)]. With L=log(phi)>1/3, the resulting upper error is at most (4L+1)/(2aL)<2 and the lower error is at least -1-1/(2aL)>-2. This proves the uniform constant two; subtracting the two estimates proves the constant four.

**Corollary.** With the actual initial depth h_p=v_p(F_r), one has

$$
\kappa_p=0\text{ and }K_p\equiv0\quad(h_p\ge2),\qquad
\kappa_p=\frac{1-1/p}{2r\log\phi}>0\quad(h_p=1).
$$

**Proof.** The classical valuation theorem gives R=r in the first case and R=pr in the second. In the first case the exact difference of S-series is zero; in the second case n=r itself supplies a positive term. This uses Lengyel's valuation theorem as recorded in Medina-Rowland, *p-regularity of the p-adic valuation of the Fibonacci sequence*, Fibonacci Quarterly 53 (2015), Theorem 1.4, arXiv:0910.2907. No branch is chosen in THS4 without this actual arithmetic input.

#### THS.4 The pole and the local density

**Theorem THS5.** For a>=3, the series Z_a(s)=sum_(k>=1)F_(ak)^(-s), initially on Re(s)>0, has the representation

$$Z_a(s)=\frac{5^{s/2}}{\phi^{as}-1}+H_a(s),$$

where H_a is holomorphic on Re(s)>-2 and H_a(0)=0. Thus D_p(s)=Z_r(s)-Z_R(s) satisfies

$$\operatorname{Res}_{s=0}D_p(s)=\frac{1/r-1/R}{\log\phi},\qquad
\int_0^\infty K_p(t)t^{s-1}\,dt=\Gamma(s)D_p(2s)\quad(\Re s>0).$$

**Proof.** Use F_(ak)=5^(-1/2)phi^(ak)(1-(-1)^(ak)phi^(-2ak)). The last factor is positive. After subtracting its leading value one, the summands are normally bounded on a compact subset of Re(s)>-2 by a constant times phi^(-ak(Re(s)+2)). This proves normal convergence and holomorphy of H_a; each remainder vanishes at s=0. The residue follows from the geometric term. Absolute convergence justifies Mellin integration term by term. Other geometric poles on the imaginary axis are not excluded by this representation.

**Theorem THS6.** For every p>5 and k>=2, the number of pairs (v,w) modulo p^k with

$$v^2-5w^2=4,\qquad p\mid w,\quad p^2\nmid w$$

is 2(p-1)p^(k-2). Replacing four by minus four gives the same count when p=1 modulo four and zero otherwise.

**Proof.** There are (p-1)p^(k-2) choices for w. In the first equation v has the two simple roots +2,-2 modulo p; each uniquely lifts for each w by Hensel's lemma. For minus four, the two roots exist precisely when -1 is a square modulo p, and are again simple. These are local solutions; the count does not assert that any chosen solution is a reduction of a global pair (L_n,F_n) in the simple-divisor window.


### ROC. Fixed-golden orders, mixed-conductor kernels, and zero-parameter dihedral forms

#### ROC.1 The ordinary order class group and the unit image

**Definition.** Fix K=Q(sqrt(5)), O=Z[phi]. For a positive integer f coprime to ten define

$$O_f=\mathbb Z+fO,\qquad P_f=\operatorname{Pic}(O_f),\qquad H(f)=|P_f|,$$

$$C_f=(O/fO)^\times/(\mathbb Z/f\mathbb Z)^\times,\qquad
r(f)=\min\{n\ge1:f\mid F_n\},\quad r(1)=1.$$

P_f is the ordinary group of invertible ideal classes, with no positivity restriction on principal ideals. It is not the narrow class group. The field K remains fixed as f varies. At f=1 all finite quotient groups in the formulas are trivial.

**Theorem ROC1.** There is a natural isomorphism

$$\boxed{P_f\simeq C_f/\langle[\phi]\rangle,\qquad
\operatorname{ord}_{C_f}([\phi])=r(f).}\tag{ROC1}$$

If f and g are coprime, r(fg)=lcm(r(f),r(g)).

**Proof.** The classical exact sequence for an order and its conductor is

$$O^\times\longrightarrow (O/fO)^\times/(O_f/fO)^\times
\longrightarrow\operatorname{Pic}(O_f)\longrightarrow\operatorname{Pic}(O)
\longrightarrow1.$$

Here O_f/fO=Z/fZ. The golden ring is norm-Euclidean, hence Pic(O)=1. For example rounding the two coefficients in the basis (1,phi) leaves norm of absolute value at most 5/16, which proves Euclidean division. Its unit group is {+/-phi^n:n in Z}. One proof normalizes a positive real unit into [1,phi); a strictly interior value would have an integral trace strictly between zero and one for norm -1, or between two and sqrt(5) for norm +1. Thus the normalized unit is one. The sign -1 is already scalar in C_f, so the unit image is generated by [phi].

The coordinate identity phi^n=F_(n-1)+F_n*phi makes its class scalar precisely when f|F_n. If scalar, it is a scalar unit because phi^n is a unit and O/fO is free over Z/fZ. Thus its order is r(f). Existence follows from finiteness of C_f. For coprime f,g, divisibility by fg is simultaneous divisibility by f and g; equivalently the two cyclic components must return at the same exponent. This gives the least common multiple.

The order exact sequence and its class-field interpretation are classical inputs: C. Lv and Y. Deng, *On Orders in Number Fields: Picard Groups, Ring Class Fields and Applications*, Sci. China Math. 58 (2015), 1627-1638, Proposition 2.3(e), Theorems 3.11 and 4.2, DOI 10.1007/s11425-015-4979-3, arXiv:1405.5776.

#### ROC.2 The complete prime-power conductor tower

**Theorem ROC2.** For p>5, a>=1, and chi_p=(5/p), the group C_(p^a) is cyclic of order (p-chi_p)p^(a-1). With the actual h_p and

$$M_p=(p-\chi_p)/r(p),$$

one has p not dividing M_p and

$$\boxed{P_{p^a}\simeq
\mathbb Z/\bigl(M_p p^{\min(a-1,h_p-1)}\bigr)\mathbb Z.}\tag{ROC2}$$

The extension-of-ideals map P_(p^(a+1))->P_(p^a) is surjective, and its kernel has order p when a<h_p and order one when a>=h_p. In particular

$$\boxed{q_p=0\iff\ker(P_{p^2}\longrightarrow P_p)\ne1.}\tag{ROC3}$$

**Proof.** In the split case O tensor Z_p=Z_p x Z_p, and division by scalar units identifies the quotient with (Z/p^aZ)^*. In the inert case the Teichmueller-unit quotient is cyclic of order p+1. The principal-unit logarithm identifies the remaining quotient with

$$pO_p/(p\mathbb Z_p+p^aO_p),$$

a cyclic group of order p^(a-1). The two factors have coprime orders, so their product is cyclic. Reduction from a+1 to a is surjective with a cyclic order-p kernel.

The classical Fibonacci valuation formula gives r(p^a)=r(p)p^max(a-h_p,0). Indeed any zero index is r(p) times an integer j, and its valuation is h_p+v_p(j); r(p) divides p-chi_p and is prime to p. Dividing the order of C_(p^a) by this unit-image order proves ROC2. This use of the full valuation formula retains h_p, as in Medina-Rowland, Theorem 1.4. Quotient reduction stays surjective since the same generator phi maps to phi. Taking the ratio of the displayed orders proves the kernel assertions and ROC3.

**Corollary.** The p-primary parts of P_(p^a) stabilize to a cyclic group of order p^(h_p-1). This assertion concerns the nonmaximal orders O_(p^a) in K; it makes no claim about the full class group of the different field K(zeta_p).

**Proof.** The prime-to-p factor is M_p, and min(a-1,h_p-1) becomes constant at a=h_p.

#### ROC.3 The mixed-conductor kernel

**Theorem ROC4.** For coprime f,g, both coprime to ten, there is a natural exact sequence

$$\boxed{
1\longrightarrow\mathbb Z/\gcd(r(f),r(g))\mathbb Z
\longrightarrow P_{fg}\longrightarrow P_f\times P_g\longrightarrow1.
}\tag{ROC4}$$

In particular H(fg)=H(f)H(g)gcd(r(f),r(g)).

**Proof.** CRT gives C_(fg)=C_f x C_g. The subgroup generated by the global unit is diagonal: it consists of ([phi]^n,[phi]^n) with a single integer n. Therefore the map to the two separate quotients is surjective and its kernel is

$$(\langle\phi_f\rangle\times\langle\phi_g\rangle)/
\langle(\phi_f,\phi_g)\rangle.$$

On the numerator, send (phi_f^u,phi_g^v) to u-v modulo gcd(r(f),r(g)). This is well-defined and surjective. Its kernel consists precisely of pairs for which the simultaneous congruences n=u modulo r(f), n=v modulo r(g) are soluble, hence is the diagonal subgroup. This proves the group statement, including trivial ranks, and counting proves the formula.

**Theorem ROC5.** Fix p>5 and m coprime to 10p. Put b=v_p(r(m)). For every a>=1,

$$\boxed{
\left|\ker(P_{mp^{a+1}}\longrightarrow P_{mp^a})\right|
=\begin{cases}p,&a<h_p+b,\\1,&a\ge h_p+b.\end{cases}
}\tag{ROC5}$$

Every nontrivial kernel here is cyclic.

**Proof.** The ambient C-group has a cyclic order-p reduction kernel. The p-exponent of the image of the global unit at level mp^a is

$$\max\{b,\max(a-h_p,0)\},$$

because its order is lcm(r(m),r(p)p^max(a-h_p,0)) and p does not divide r(p). The unit-image size increases by p at the next level exactly when a>=h_p+b; all its other prime-exponents remain unchanged. The Picard-group size ratio is consequently one in that case and p otherwise. The Picard kernel is a quotient of the ambient cyclic reduction kernel: any element mapping into the lower unit image can be multiplied by a lifted power of phi to enter that reduction kernel. This proves cyclicity as well as its exact size.

**Proposition ROC6.** The increase H(mp^2)>H(mp) at a mixed conductor does not imply p is WSS. In fact

$$r(7)=8,\quad h_7=1,\quad r(13)=7,\quad H(91)=2,\quad H(637)=14.$$

**Proof.** F_8=21 and F_1=1,F_2=1,F_4=3 show r(7)=8 and h_7=1. F_7=13 and the prime-index argument show r(13)=7. For coprime prime powers ROC1-ROC2 give

$$H(91)=\frac{8\cdot14}{\operatorname{lcm}(8,7)}=2,\qquad
H(637)=\frac{56\cdot14}{\operatorname{lcm}(56,7)}=14.$$

The order-seven kernel is caused by v_7(r(13))=1 in ROC5, although seven is non-WSS. Thus the correction b cannot be omitted when inferring initial depths from mixed-conductor growth.

#### ROC.4 Finite-order characters and exact conductor

**Definition.** An ordinary ring-class character of conductor dividing f is a character of P_f, inflated along the natural maps for larger conductors. Its least rational conductor is the smallest positive f through which it factors. Through classical ring class field theory it defines a finite Hecke character of K trivial at both real places and on rational ideles. For k>=1 let X_(p,k) be the set of such characters of exact order p^k whose conductor is a power of p, identifying repeated inflations of the same character.

**Theorem ROC7.** For all p>5 and k>=1,

$$\boxed{|X_{p,k}|=
\begin{cases}p^{k-1}(p-1),&h_p\ge k+1,\\0,&h_p<k+1.\end{cases}}\tag{ROC7}$$

When present, every character in X_(p,k) has least rational conductor p^(k+1) and Hecke conductor ideal p^(k+1)O. It satisfies eta^sigma=eta^(-1), where sigma is golden conjugation.

**Proof.** By ROC2 the p-primary part of P_(p^a) is cyclic of order p^min(a-1,h_p-1), and all transition maps are surjective. A character of exact order p^k exists exactly when h_p>=k+1 and a>=k+1. At a=k+1 its number is the Euler totient p^(k-1)(p-1). At every later level all characters of that order factor uniquely through this quotient, since a cyclic p-group has a unique subgroup of each order. The prime-to-p factor contributes no nontrivial values to a p-power-order character. This proves both the count and least rational conductor.

Conjugation acts by inversion on C_f, since x*sigma(x) is a scalar unit, and hence on P_f. The attached Hecke characters are therefore anticyclotomic. Their finite conductors are supported above p. If p splits, the two local conductor exponents are equal because the conjugate character is the inverse; if p is inert there is one exponent. Triviality on local scalar units and on global units shows that such a character has conductor dividing p^aO precisely when it factors through P_(p^a). Its least a is k+1, proving the stated ideal conductor in both cases. The ordinary class-group convention permits all real units at infinity, so the real components are trivial. Rational ideles are generated by rational principal ideles, the real factor, and scalar finite units; the character is trivial on each. The class-field interpretation is the one in Lv-Deng, Theorem 4.2.

#### ROC.5 A precisely specified spectral family at eigenvalue one quarter

**Definition.** Let D_(p,k) be the set of cuspidal GL(2)/Q representations obtained by automorphic induction from X_(p,k), up to isomorphism. Only this fixed-K, finite p-power-order, ordinary ring-class family is included in D_(p,k).

**Theorem ROC8.** Every representation in D_(p,k) has weight zero, Laplace eigenvalue 1/4, central character chi_5, and exact arithmetic conductor 5p^(2k+2). Moreover

$$\boxed{|D_{p,k}|=
\frac{p^{k-1}(p-1)}2\,\mathbf1_{h_p\ge k+1}.}\tag{ROC8}$$

In particular p is WSS if and only if D_(p,1) is nonempty, in which case its size is (p-1)/2 and its exact conductor is 5p^4.

**Proof.** Classical Hecke-Maass automorphic induction attaches a normalized eigenform to eta, and is cuspidal when eta is not equal to eta^sigma. Here eta^sigma=eta^(-1) and eta has odd order greater than one, so cuspidality holds. The induced two-dimensional finite-image representation sends complex conjugation to the identity, because K is real and both real components of eta are trivial. Its Maass eigenvalue is therefore 1/4. The central character is chi_5 times the restriction of eta to rational ideles, hence is chi_5. These classical finite-order induction statements, including the eigenvalue, are stated in W.-C. W. Li and Z. Rudnick, *Pair arithmetical equivalence for quadratic fields*, arXiv:2007.13147v2, Section 1.3.

The conductor-discriminant formula for automorphic induction gives the exact conductor |disc(K)|*N_(K/Q)(cond eta)=5p^(2k+2). See P. Humphries, *Archimedean Newform Theory for GL_n*, Theorem 3.12 and Remark 3.13, DOI 10.1017/S1474748024000227. For the same quadratic field, two induced irreducible representations are isomorphic precisely when their inducing characters agree or are conjugate: restrict the induced representation back to K to get eta plus eta^sigma. Thus the fixed-point-free pairing eta with eta^(-1) accounts for the factor two in ROC8.

An explicit normalization of the corresponding even Maass form is

$$
g_\eta(x+iy)=2\sqrt y\sum_{\substack{\mathfrak a\subset O\\
(\mathfrak a,p)=1}}\eta(\mathfrak a)
 K_0(2\pi N\mathfrak a\,y)\cos(2\pi N\mathfrak a\,x).
$$

The term of norm one has coefficient one in the normalized exponential Fourier expansion, so the constructed form is not zero. The sum converges for y>0 by the exponential decay of K_0. This is the classical Fourier construction in Li-Rudnick, Section 1.3, applied after the ring-class characters have been obtained. It does not establish their existence without the condition in ROC7.

**Corollary.** Forms in D_(p,1), when they exist, can be viewed as oldforms at the theta-sieve level 20p^4. ROC8 does not count all cusp forms, all dihedral forms from other quadratic fields, or forms induced from characters with nontrivial archimedean parameter.

**Proof.** Their exact conductor 5p^4 divides 20p^4, so oldform inclusion applies. The exclusions follow from the defining restrictions on D_(p,k); no assertion about other spectral components is used in the count.

#### ROC.6 The class-growth coefficient and the remaining independent condition

**Theorem ROC9.** The coefficient in THS4 has the exact expression

$$\boxed{\kappa_p=
\frac{pH(p)-H(p^2)}{2p(p-\chi_p)\log\phi}.}\tag{ROC9}$$

The family D_(p,1) is nonempty exactly in the branch where K_p is identically zero. Nonemptiness of this family therefore does not imply nonvanishing of the particular Fourier difference in THS4.

**Proof.** ROC1-ROC2 give H(p)=(p-chi_p)/r and H(p^2)=p(p-chi_p)/R. Substitute in THS4. ROC3 and ROC8 identify nonemptiness with h_p>=2; the exact S-series difference in THS4 is then zero. This does not assert that each individual spectral projection of V_p-V_(p^2) vanishes: contributions to a selected Fourier functional may cancel, and a nonzero representation need not occur in that theta projection at all.

**Proposition.** The identities THS1-THS6 and ROC1-ROC9 leave the actual set of primes with h_p>=2 undetermined. In particular, a vanishing theorem for D_(p,1) on a specified prime family would exclude WSS in that family, while an independently constructed member would give a WSS prime; neither existence nor vanishing on a new family follows from the displayed counts alone.

**Proof.** ROC8 expresses the count in terms of the same actual h_p, and ROC9 expresses the heat coefficient in terms of its unit-image size. No inequality choosing a branch is among the hypotheses or conclusions used to prove those identities. The logical implications in the proposition follow directly from ROC8, but their antecedents require information additional to the formula. The fixed eigenvalue is 1/4 at every conductor, so estimates that only treat growing archimedean spectral parameter do not by themselves supply either antecedent.


### SGN. Spectral Galois arithmetic, exact congruence ideals, and packet norms

#### SGN.1 Fixed fields and Fourier normalization

**Definition.** Retain the fixed golden field K=Q(sqrt(5)), O=Z[phi], the original depth h_p, and the ordinary ring-class families X_(p,k), D_(p,k) of ROC. For this section take p>5, k>=1, and assume h_p>=k+1. Choose eta in X_(p,k), put m=p^k, d_k=p^(k-1)(p-1)/2, and N_k=5p^(2k+2). Let L_(p,k)/K be the cyclic class-field extension cut out by eta. All primitive characters of this cyclic quotient have the same kernel. Write sigma for golden conjugation.

The extension L_(p,k)/Q is totally real and dihedral of degree 2m. Indeed its kernel is stable under sigma, which acts by inversion on its cyclic group. A lift s of sigma satisfies s^2=tau^j for a rotation tau. Commutation of s with s^2 and inversion of rotations imply 2j=0 modulo the odd number m, so s^2=1. Let M_(p,k) be the fixed field of a chosen reflection. It is totally real of degree m. Choose the reflections compatibly in the tower, and put M_(p,0)=Q. These fields are different from the radical fields E_n of RNI and the coefficient fields below.

Define the integral ideal coefficients, with eta extended by zero on ideals not coprime to p, by

$$
A_\eta(n)=\sum_{N\mathfrak a=n}\eta(\mathfrak a),\qquad
 g_\eta(z)=\sqrt y\sum_{n\ne0}A_\eta(|n|)K_0(2\pi|n|y)e^{2\pi inx}.
\tag{SGN1}
$$

Thus A_eta(1)=1 and this g_eta is the form normalized in ROC8. Its Petersson norm at the minimal level is the unscaled integral with measure dx dy/y^2 over Gamma_0(N_k)\H. Daichi Tanaka, *Explicit Construction of Maass Wave Forms and Their Petersson Inner Products*, arXiv:2601.21588v3 (February 3, 2026), Theorem 1.1, uses the cosine sum Theta_eta=g_eta/2. The construction theorem is classical input; all norm constants below are derived with the normalization in SGN1.

#### SGN.2 The exact coefficient field and its first congruence ideal

**Theorem SGN2.** Choose a primitive mth root of unity zeta, identify the image of eta with its powers, and put

$$B_m=\mathbb Q(\zeta+\zeta^{-1}),\qquad
\lambda_m=2-\zeta-\zeta^{-1},\qquad\mathfrak l_m=(\lambda_m)\subset O_{B_m}.$$

Every A_eta(n) is integral and belongs to B_m. The field generated by the good-prime coefficients is exactly B_m, of degree d_k. The d_k forms g_(eta^j), with j in (Z/mZ)^*/{+1,-1}, form one coefficientwise Galois orbit. Moreover l_m is the unique prime of B_m above p, its norm is p, and pO_(B_m)=l_m^(d_k).

**Proof.** Conjugation of ideals pairs eta(a) with eta(a)^(-1). A fixed ideal coprime to p under sigma has character value equal to its inverse, hence one because its order is odd. Thus the ideal sum is real and integral in Q(zeta). For a good rational prime ell not dividing 5p, if ell is inert the coefficient is zero. If ell splits as q*sigma(q), then

$$A_\eta(\ell)=\zeta^b+\zeta^{-b},\qquad \eta(\mathfrak q)=\zeta^b.$$

Chebotarev applied to the already-defined L_(p,k)/Q supplies primes with Frobenius the conjugacy class of a generator rotation. For one such ell the coefficient is zeta+zeta^(-1), proving equality of coefficient fields. The action zeta mapping to zeta^j gives the stated Galois orbit; equality of two induced forms forces the characters to agree or be inverse, as in ROC8.

The shifted polynomial Phi_(p^k)(1+X) is Eisenstein at p. Hence p is totally ramified in Q(zeta), with uniformizer 1-zeta and norm p. Since lambda_m=(1-zeta)(1-zeta^(-1)), its valuation in that cyclotomic field is two. Passing to the real subfield divides the valuation by two; its absolute norm there is p, using Phi_(p^k)(1)=p. Total ramification and the displayed degree give the ideal assertions. Chebotarev is used only after the extension exists; see A. V. Sutherland, MIT 18.785 Lecture 28 (2021), Theorem 28.9. It is not an existence theorem for the missing ring-class character at an arbitrary target p.

**Theorem SGN3.** Put b(n)=sum_(a|n)chi_5(a). Then for (n,5p)=1,

$$A_\eta(n)\equiv b(n)\pmod{\mathfrak l_m}.$$

The ideal generated by all good-prime discrepancies is exactly

$$\boxed{\bigl(A_\eta(\ell)-1-\chi_5(\ell):\ell\nmid5p\bigr)
=\mathfrak l_m.}\tag{SGN2}$$

For a split good prime, write eta(q)=zeta^b. If b is nonzero modulo p^k and j=v_p(b)<k, then

$$\boxed{v_{\mathfrak l_m}(A_\eta(\ell)-2)=p^j,\qquad
\bigl|N_{B_m/\mathbb Q}(A_\eta(\ell)-2)\bigr|=p^{p^j}.}\tag{SGN3}$$

When p does not divide b, one additionally has

$$\boxed{\frac{A_\eta(\ell)-2}{\lambda_m}\equiv-b^2\pmod{\mathfrak l_m}.}\tag{SGN4}$$

**Proof.** Reduction of every root of unity eta(a) modulo 1-zeta gives one. The number of ideals of norm n in K is sum_(a|n)chi_5(a); pairing with the real subfield gives the first congruence. At an inert good prime the discrepancy is zero. At a split prime,

$$A_\eta(\ell)-2=(\zeta^b-1)^2/\zeta^b.$$

The cyclotomic valuation of 1-zeta^b is p^j: zeta^b is a primitive p^(k-j)th root, whose cyclotomic subfield has ramification index smaller by p^j. Its ideal has no support outside p. Squaring and passing to B_m proves both assertions in SGN3. For p not dividing b the ratio (1-zeta^b)/(1-zeta) reduces to b. Since lambda_m=-(zeta-1)^2/zeta, the quotient in SGN4 reduces to -b^2. Every discrepancy therefore belongs to l_m, while a generator Frobenius from SGN2 gives the exact discrepancy -lambda_m. This proves the ideal equality, including the fact that no larger common power of l_m is forced.

**Corollary SGN4.** As the auxiliary good rational prime ell varies, the set on which the discrepancy in SGN2 has finite l_m-valuation p^j has Dirichlet density

$$\frac{p-1}{2p^{j+1}}\quad(0\le j<k).$$

The set on which that discrepancy is zero has density 1/2+1/(2p^k).

**Proof.** In the dihedral group of order 2p^k there are (p-1)p^(k-j-1) rotations with exponent of p-valuation j. The union is stable under conjugation, so Chebotarev gives its size divided by 2p^k. All reflections and the identity rotation give zero discrepancy, with combined size p^k+1. These densities concern auxiliary primes in one existing number field. They are not a density theorem for WSS as the target p varies.

#### SGN.3 An explicit residual lattice

**Theorem SGN5.** Let t=zeta+zeta^(-1). The matrices

$$R=\begin{pmatrix}0&-1\\1&t\end{pmatrix},\qquad
S=\begin{pmatrix}0&1\\1&0\end{pmatrix}$$

give an integral realization over O_(B_m) of the dihedral representation attached to eta: R^m=I, S^2=I, SRS=R^(-1). After reduction modulo l_m and pullback along Gal(L_(p,k)/Q), the associated Galois representation has a nonsplit exact sequence

$$\boxed{0\longrightarrow\mathbb F_p(\chi_5)
\longrightarrow\overline\rho_\eta\longrightarrow\mathbb F_p
\longrightarrow0.}\tag{SGN5}$$

Its semisimplification is 1 plus chi_5, and complex conjugation acts as the identity.

**Proof.** R has distinct eigenvalues zeta,zeta^(-1) in the cyclotomic field and therefore order m. Direct multiplication proves the two relations involving S. Modulo l_m one has t=2, R not equal to I, and (R-I)^2=0. Its fixed space is the line generated by (1,-1); S acts by minus one on that line and by plus one on the quotient. This identifies the two characters. A direct sum of those characters would make every rotation act trivially, whereas the displayed residual R is nontrivial unipotent. Thus the sequence does not split. The totally real field L_(p,k) makes complex conjugation trivial. For k>1 the residual rotation has order p, although the characteristic-zero rotation has order p^k. This does not retain all higher order in the residual image.

The congruence is an Eisenstein-type coefficient congruence, but the representation is even. No theorem whose hypotheses require an odd holomorphic two-dimensional Galois representation is invoked by SGN5.

#### SGN.4 A normalized Rankin-Selberg calculation at spectral parameter zero

**Lemma SGN6.** For Re(s)>0, with the standard modified Bessel function K_0,

$$\boxed{\int_0^\infty y^{s-1}K_0(y)^2\,dy
=2^{s-3}\frac{\Gamma(s/2)^4}{\Gamma(s)}.}\tag{SGN6}$$

In particular the value at s=1 is pi^2/4.

**Proof.** Schlaefli's representation is

$$K_0(y)=\tfrac12\int_0^\infty e^{-u-y^2/(4u)}\,du/u,$$

as in NIST DLMF 10.32.10. For real s>0, Tonelli's theorem applies to the square. The y-integral is Gamma(s/2)/2 times (4uv/(u+v))^(s/2). The remaining double integral is

$$2^{s-3}\Gamma(s/2)\int_0^\infty\int_0^\infty
 e^{-u-v}u^{s/2-1}v^{s/2-1}(u+v)^{-s/2}\,du\,dv.$$

Set w=u+v and x=u/(u+v). The w-integral is Gamma(s/2) and the x-integral is Beta(s/2,s/2). This gives SGN6. Absolute convergence on Re(s)>0 and holomorphic continuation within that half-plane prove the complex statement.

**Theorem SGN7.** With N=N_k and the exact Fourier normalization SGN1,

$$\boxed{\langle g_\eta,g_\eta\rangle_N
=\frac N2\left(1-\frac{\chi_5(p)}p\right)
 L(1,\chi_5)L_K(1,\eta^2).}\tag{SGN7}$$

All Euler factors at five and p are included in this formula.

**Proof.** The coefficients A_eta(n) are real. Put D_eta(s)=sum_(n>=1)A_eta(n)^2 n^(-s). The ideal Euler factors give

$$D_\eta(s)=\frac{\zeta(s)L(s,\chi_5)L_K(s,\eta^2)}{\zeta(2s)}
\frac1{1+5^{-s}}\frac{1-\chi_5(p)p^{-s}}{1+p^{-s}}.\tag{SGN8}$$

To check this at every prime, write x=ell^(-s). At a good split prime with eta(q)=z, the squared-coefficient series is

$$\frac{1+x}{(1-x)(1-z^2x)(1-z^{-2}x)}.$$

This follows by squaring sum_(j=0)^a z^(a-2j) and summing geometric series; as a rational identity it includes z=+1,-1 by continuation. At a good inert prime it is (1-x^2)^(-1). At the prime five, its unique prime ideal q has q^2=(5), so eta(q)=1 because eta has odd order and is trivial on rational ideles. The squared-coefficient factor is (1-5^(-s))^(-1), producing the factor (1+5^(-s))^(-1) in SGN8. At p, eta and eta^2 are ramified at every prime above p, so the ideal series has local factor one. Comparison with zeta(s)L(s,chi_5)/zeta(2s) gives the final correction in SGN8.

Let E_infinity(z,s) be the standard weight-zero Eisenstein series for Gamma_0(N), with the stabilizer including both signs. Its residue at s=1 is 1/vol=3/(pi*i_N), where i_N=N product_(ell|N)(1+1/ell). Unfolding and SGN6 give

$$\int_{\Gamma_0(N)\backslash\mathbb H}
 E_\infty(z,s)|g_\eta(z)|^2\,\frac{dx\,dy}{y^2}
=\frac{\Gamma(s/2)^4}{4\pi^s\Gamma(s)}D_\eta(s).\tag{SGN9}$$

The scalar at s=1 is pi/4. Taking residues and using zeta(2)=pi^2/6, the factor 5/6 from the prime five, and the factor (1-chi_5(p)/p)/(1+1/p), cancels i_N down to the right side of SGN7. All unfolding operations first take place on Re(s)>1; cusp decay permits the residue passage. The standard Eisenstein residue and this Rankin-Selberg normalization are also recorded in P. Humphries and R. Khan, *On the Random Wave Conjecture for Dihedral Maass Forms*, GAFA 30 (2020), proof of Lemma 4.4 and equation (4.8), DOI 10.1007/s00039-020-00526-4. The present bad-prime factors are computed above and are not taken from a squarefree-level specialization.

**Proposition SGN8.** In the standard K_0 convention, the coefficient 2^(s-2) in Tanaka, arXiv:2601.21588v3, Lemma 4.2, must be replaced by 2^(s-3) when nu=0. For the family in SGN1 the cosine normalization Theta_eta=g_eta/2 therefore has

$$\boxed{\langle\Theta_\eta,\Theta_\eta\rangle_N
=\frac N8\left(1-\frac{\chi_5(p)}p\right)
 L(1,\chi_5)L_K(1,\eta^2).}\tag{SGN10}$$

This is half the expression obtained by specializing the printed Theorem 1.3 of that version to this family.

**Proof.** At nu=0,s=1, SGN6 gives pi^2/4, whereas the stated factor 2^(s-2) gives pi^2/2 with the same K_0 integral. The cosine definition in that paper has first exponential Fourier coefficient 1/2, so its norm is one quarter of SGN7. In its printed constants C_1 C_2 C_3, put nu=0 and conductor ideal p^(k+1)O. Then C_2=pi, the first product in C_3 is empty, and the other Euler factors cancel the totient in C_1, yielding N/4 times (1-chi_5(p)/p) times the two L-values. This differs from SGN10 by exactly two. SGN7 was derived independently from the standard Bessel integral and the width-one Eisenstein residue; the uncorrected printed norm is not a premise. This proposition concerns that normalization and specialization, not the validity of the construction theorem or all other assertions of the paper.

#### SGN.5 The Galois-packet Gram determinant and a global regulator identity

**Definition.** Let G_(p,k) be the d_k by d_k Gram matrix of the forms g_(eta^j) for j in (Z/p^kZ)^*/{+1,-1}, all at their common minimal level N_k, with no L^2 rescaling. For a totally real field M let h(M) be its ordinary ideal class number and Reg(M) its standard Dirichlet regulator; put h(Q)=Reg(Q)=1. These class numbers are not the order class numbers H(f) of ROC and are not the initial depths h_p.

**Theorem SGN9.** The Gram matrix is diagonal and

$$\boxed{\det G_{p,k}
=\left[\frac{N_k}{2}\left(1-\frac{\chi_5(p)}p\right)L(1,\chi_5)\right]^{d_k}
\frac{\operatorname{Res}_{s=1}\zeta_{M_{p,k}}(s)}
     {\operatorname{Res}_{s=1}\zeta_{M_{p,k-1}}(s)}.}\tag{SGN11}$$

In particular it has the explicit form

$$\boxed{\det G_{p,k}
=\bigl[4p^k(p-\chi_5(p))\log\phi\bigr]^{d_k}
\frac{h(M_{p,k})\operatorname{Reg}(M_{p,k})}
     {h(M_{p,k-1})\operatorname{Reg}(M_{p,k-1})}.}\tag{SGN12}$$

**Proof.** Choose a good split Frobenius generating the rotation group as in SGN2. Its Hecke operator is self-adjoint since chi_5(ell)=1. Its eigenvalues zeta^j+zeta^(-j) on the displayed primitive forms are pairwise distinct, so those forms are orthogonal.

For a dihedral group D_m, the permutation representation on cosets of a reflection is the trivial representation plus each two-dimensional irreducible representation once. The quotient field M_(p,k-1) contributes exactly the representations whose rotation characters factor through the quotient of order p^(k-1). Subtraction leaves precisely the primitive characters indexed by j above. The induction property of Artin L-functions therefore gives the identity, including ramified Euler factors,

$$\frac{\zeta_{M_{p,k}}(s)}{\zeta_{M_{p,k-1}}(s)}
=\prod_{j\in(\mathbb Z/p^k\mathbb Z)^*/\{\pm1\}}L_K(s,\eta^j).\tag{SGN13}$$

Multiplication by two permutes these classes of exponents. Multiply SGN7 over all j and then take s=1 in SGN13 to obtain SGN11.

The conductor-discriminant formula for the same permutation representation gives

$$\frac{\operatorname{disc}(M_{p,k})}{\operatorname{disc}(M_{p,k-1})}
=N_k^{d_k}.\tag{SGN14}$$

Here every remaining irreducible constituent has exact conductor N_k by ROC8; both discriminants are positive. Since [M_(p,k):Q]-[M_(p,k-1):Q]=2d_k and both fields are totally real with only two roots of unity, the analytic class number formula gives

$$\frac{\operatorname{Res}\zeta_{M_{p,k}}}{\operatorname{Res}\zeta_{M_{p,k-1}}}
=\frac{2^{2d_k}}{N_k^{d_k/2}}
\frac{h(M_{p,k})\operatorname{Reg}(M_{p,k})}
     {h(M_{p,k-1})\operatorname{Reg}(M_{p,k-1})}.$$

Finally L(1,chi_5)=2log(phi)/sqrt(5), since K has class number one and fundamental unit phi. Inserting this and sqrt(N_k)=sqrt(5)p^(k+1) into SGN11 proves SGN12. The analytic class number formula is classical; see Sutherland, MIT 18.785 Lecture 19 (2021), Theorem 19.12. The Artin induction and conductor-discriminant identities are classical class-field inputs, also used in Tanaka, Section 4.2, for low-degree dihedral examples. No regulator approximation is used in this equality.

**Corollary.** At the WSS threshold k=1, put d=(p-1)/2. The reflection field satisfies

$$\operatorname{disc}(M_{p,1})=5^{(p-1)/2}p^{2(p-1)},$$

and the normalized packet has

$$\det G_{p,1}=[4p(p-\chi_5(p))\log\phi]^d
 h(M_{p,1})\operatorname{Reg}(M_{p,1}).$$

**Proof.** Specialize SGN12-SGN14 and use M_(p,0)=Q. The fields and the packet in these formulas have been constructed under h_p>=2; the formula does not assert that such a field exists at a target prime without that hypothesis.

#### SGN.6 Exact scope of the spectral constraints

**Proposition.** SGN2-SGN12 give necessary coefficient-field, congruence, residual-representation and norm identities for each member of the finite-order family D_(p,k). None supplies an independent existence or vanishing theorem for that family at a new target prime. In particular positivity of SGN7 does not imply h_p>=k+1.

**Proof.** The field L_(p,k), its primitive character eta, and hence all forms and matrices in those theorems were defined only after choosing eta in X_(p,k). By ROC7 this is equivalent to h_p>=k+1. Chebotarev in SGN2-SGN4 describes auxiliary primes in that already-existing field, rather than creating it. The positive norm in SGN7 is the norm of an already-existing normalized cusp form; it is not a lower bound for the number of such forms. An independent construction satisfying these spectral specifications would, via ROC8, decide a WSS depth, while an independent obstruction would exclude that depth. The displayed identities do not choose either alternative. Estimates in a large archimedean-parameter limit have additional hypotheses to check here, since every form under discussion has parameter zero and varying level.
