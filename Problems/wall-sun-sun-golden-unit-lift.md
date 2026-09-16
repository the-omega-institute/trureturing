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

### CF. Carlitz degree-five exactness within the same Wieferich family

The integer WSS target and the following function-field subproblem share
this single problem dossier. The CF proof was previously delivered in
PR8170 and is preserved here without recounting it as a new result.
Its independent primary source remains `niedbala2026carlitz`.

#### CF.0 Problem and literal orbit definitions

David Niedbala Giraudin, *A counterexample to a conjecture of Thakur on
Carlitz-Wieferich primes*, arXiv:2607.15305v2 (22 July 2026), Conjecture 4.2,
asks whether, for q=19^3,

$$\gcd(T^{q^5}-T,M_{5,q}(T))=\mu(T^q-T),$$

where

$$\mu(X)=X^5+5X^3+3X^2-4X-9\in\mathbb F_{19}[X]$$

and, with [i]_q=T^(q^i)-T,

$$M_{5,q}=1-[4]_q(1-[3]_q(1-[2]_q(1-[1]_q))).$$

The gcd is monic. Version 2 explicitly corrects the former exactness theorem
to a conjecture. The known factor is a product of 6859 distinct monic
Carlitz-Wieferich primes of degree five. The remaining possibility described
in the paper is an associated difference of degree fifteen over F19, outside
the known quintic difference field. The original counterexample and the
known-factor theorem are prior results, not new claims here.

For a commutative ring define

$$R(a,b,c,d)=1-d(1-c(1-b(1-a))).$$

For indeterminates a,b,c,d put

$$\begin{aligned}
f_0&=R(a,b,c,d),\\
f_1&=R(b-a,c-a,d-a,-a),\\
f_2&=R(c-b,d-b,-b,a-b),\\
f_3&=R(d-c,-c,a-c,b-c),\\
f_4&=R(-d,a-d,b-d,c-d).
\end{aligned}$$

These are the five residuals obtained by changing the origin successively
around the ordered five-point cycle (0,a,b,c,d). Each has total degree four.

#### CF1. A polynomial certificate valid in every characteristic-19 ring

**Theorem.** If a,b,c,d lie in any commutative ring of characteristic nineteen
and f_0=f_1=f_2=f_3=f_4=0, then mu(a)=0.

**Proof.** There are explicit integer polynomials A_0,...,A_4,H satisfying

$$\boxed{\sum_{i=0}^4 A_i f_i-19H=\mu(a)}. \tag{CF1}$$

Their total degrees are respectively 8,8,8,8,7,12. The coefficients A_i
are the centered representatives in [-9,9] of a finite-field elimination
certificate. Their nonzero monomial counts are 382,135,203,182,131.
The five complete Horner expressions A_i occur in the companion Lean proof.
Expanding their weighted sum minus mu gives integer coefficients all
divisible by nineteen. Dividing those coefficients by nineteen defines H,
which has 591 nonzero monomials. This is the integer identity CF1; the
Lean proof instead checks the equivalent identity directly in characteristic
nineteen. No assertion about a search range is involved. Under the five
residual hypotheses both terms on the left of CF1 vanish, proving the result.

The certificate can be found by linear algebra: multiply the five quartics
by every monomial of degree at most eight, then solve for the coefficient
vector of mu(a) in their span over F19. Degree twelve suffices. The direct
identity CF1 is the proof certificate; the elimination program or its claimed
Groebner basis is not an additional mathematical assumption.

#### CF2. Closure under all five conjugate equations

**Theorem.** Let K be a field of characteristic nineteen, sigma a ring
endomorphism of K, and theta an element with sigma^5(theta)=theta. If

$$R(\sigma\theta-\theta,\sigma^2\theta-\theta,
     \sigma^3\theta-\theta,\sigma^4\theta-\theta)=0,$$

then mu(sigma(theta)-theta)=0.

**Proof.** Set a=sigma(theta)-theta, b=sigma^2(theta)-theta,
c=sigma^3(theta)-theta and d=sigma^4(theta)-theta. The given equation
is f_0=0. Apply sigma successively. It preserves the integer coefficients,
addition and multiplication. The closing equation sigma^5(theta)=theta
identifies the next four resulting residuals with f_1,...,f_4. Apply CF1.
No pairwise-distinctness premise or root-counting hypothesis is required.

**Corollary.** For every s>=1 and q=19^s, every common root theta of
T^(q^5)-T and M_(5,q) satisfies mu(theta^q-theta)=0.

**Proof.** In an algebraic closure use sigma(x)=x^q, an actual Frobenius
endomorphism, and apply CF2. In particular the degree-fifteen difference
case left open in the source cannot occur: every such difference has
minimal polynomial dividing the quintic mu.

#### CF3. The five-dimensional difference field

**Lemma.** The polynomial mu is irreducible over F19. In F19[X]/(mu), write
x for the residue of X. The successive nineteenth powers are

$$\begin{array}{c|l}
i&x^{19^i}\\\hline
0&x\\
1&-3x^4+x^3-9x^2-4x-7\\
2&3x^4-9x^3+x^2-6x+7\\
3&4x^4-6x^3+5x^2+7x-8\\
4&-4x^4-5x^3+3x^2+2x+8\\
5&x.
\end{array} \tag{CF2}$$

**Proof.** Repeated binary exponentiation and division by the displayed
monic mu gives the table. The Euclidean algorithm gives

$$\gcd\bigl(\mu,-3X^4+X^3-9X^2-5X-7\bigr)=1.$$

Thus mu divides X^(19^5)-X and is coprime to X^19-X. Every irreducible
factor consequently has degree dividing five and different from one.
As five is prime and mu has degree five, mu is irreducible. These are
exact polynomial remainder computations of degree at most four, not
enumerations of field elements.

#### CF4. All characteristic-19 extension degrees

**Theorem.** For every s>=1, q=19^s,

$$\boxed{
\gcd(T^{q^5}-T,M_{5,q})=
\begin{cases}
\mu(T^q-T),&s\equiv3\pmod5,\\
1,&s\not\equiv3\pmod5.
\end{cases}} \tag{CF3}$$

In particular Conjecture 4.2 of the cited version 2 holds.

**Proof.** Let theta be a common root and eta=theta^q-theta. CF2 makes
eta a root of mu, so its nineteenth-power orbit has length five by CF3.
The action eta->eta^q depends only on e=s modulo five. Put

$$u_j=\sum_{i=0}^{j-1}\eta^{q^i}\quad(1\le j\le5).$$

The closing condition is u_5=0 and the residual condition is
R(u_1,u_2,u_3,u_4)=0. If e=0, u_5=5eta is nonzero. For e=1,2,3,4,
the trace u_5 vanishes and reduction using CF2 gives the following
residuals, as polynomials in eta of degree at most four:

$$\begin{array}{c|l}
e&R(u_1,u_2,u_3,u_4)\\\hline
1&6\eta^4-6\eta^3+\eta^2+\eta-2\\
2&-3\eta^4+9\eta^3+6\eta^2+7\eta+1\\
3&0\\
4&-4\eta^4+7\eta^3+6\eta^2+4\eta+9.
\end{array} \tag{CF4}$$

Irreducibility of mu implies that none of the three nonzero polynomials
can vanish at eta. Hence a common root is possible only for e=3.

Conversely assume e=3 and take any root theta of mu(T^q-T). Its
eta=theta^q-theta is a root of mu. The same table proves both u_5=0
and R(u_1,...,u_4)=0. The telescoping identities
u_j=theta^(q^j)-theta then prove that theta is a common root.
Thus the common-root sets are exactly those asserted in CF3.

The polynomial T^(q^5)-T is squarefree since its derivative is -1.
The polynomial mu(T^q-T) is also squarefree: its derivative is
-mu'(T^q-T), and mu and mu' are coprime. Both relevant polynomials
are monic, so equality of their root sets gives the stated monic gcd.

#### CF5. Exact count and construction of the degree-five primes

**Corollary.** For q=19^s, s>=1, there are exactly q monic degree-five
Carlitz-Wieferich primes if s=3 modulo five, and none otherwise.

**Proof.** The criterion P|M_(5,q) for a monic irreducible polynomial P
of degree five is the standard Carlitz-Wieferich criterion of Thakur
and Bamunoba-Bergstrom, recorded as Lemma 2.1 in the cited paper.
For s=3 modulo five, the gcd has degree 5q. Every irreducible factor
has degree dividing five because it divides T^(q^5)-T. It has no
linear factor: for theta in F_q, eta=theta^q-theta=0 and mu(0)=-9
is nonzero. All its factors therefore have degree five, and their
number is q. They are distinct by squarefreeness. The other cases
have gcd one by CF4.

**Theorem.** Define the polynomial with prime-field coefficients

$$P_0(T)=T^5-6T^3+3T^2-9T-4\in\mathbb F_{19}[T].$$

For every s=3 modulo five, q=19^s, the complete set of monic degree-five
Carlitz-Wieferich primes over F_q is

$$\boxed{\{P_0(T-a):a\in\mathbb F_q\}.} \tag{CF5}$$

**Proof.** Choose a root eta of mu. Since s is coprime to five, eta has
degree five over F_q and its q-trace is zero. Put

$$\theta_0=\frac15\sum_{j=1}^4 j\eta^{q^j}
=6+8\eta^3-8\eta^4.$$

The first expression gives theta_0^q-theta_0=eta by telescoping: the
numerator difference is 5eta minus the trace. The second expression
follows from the table CF2 with q acting as the third Frobenius power.
Reduction modulo mu verifies P_0(theta_0)=0. The element theta_0 lies
in F_(19^5) and is not in F_q because its q-difference eta is nonzero;
hence it has degree five over F_q. Thus P_0 is its irreducible monic
polynomial and is Carlitz-Wieferich by CF4.

All q translates are distinct: translation by a nonzero gamma changes
the T^4 coefficient by 5gamma. They are irreducible and retain the
Carlitz residual because q-Frobenius differences are unchanged under
translation by F_q. The count already proved makes this the complete set.
For q=19^3 the polynomial in the source is translated to P_0 by replacing
T with T-(6+11c+17c^2), using c^3=8c^2+4c+11. This is a canonical member
of the previously known class, not an additional translation class.
The same P_0 is not Carlitz-Wieferich for the prime-field Carlitz action
q=19. The field defining the Carlitz Frobenius must be kept fixed.

#### CF.6 Sources and boundaries

Primary target: https://arxiv.org/html/2607.15305v2, Conjecture 4.2.
Its version date is 22 July 2026. The companion *Effective determination
of Carlitz-Wieferich primes of given degree* is listed there as in
preparation. The already proved counterexample and the known factor
in Theorem 4.1 are not counted as new results.

The original criterion is from D. S. Thakur, *Fermat versus Wilson
congruences, arithmetic derivatives and zeta values*, Finite Fields and
Their Applications 32 (2015), 192-206; see also A. S. Bamunoba and
J. Bergstrom, *A search for c-Wieferich primes*, International Journal
of Number Theory 17 (2021), 1599-1616, arXiv:2011.11727.

CF1-CF5 concern function-field Carlitz-Wieferich primes. They do not
establish an integer Wall-Sun-Sun prime. The finite five-orbit closure
and the additive Frobenius coordinate are specific arithmetic inputs;
replacing them with an integer Fibonacci congruence requires a separate
proved construction. The reusable method is simultaneous conjugate
closure followed by an explicit low-degree elimination identity, not
an identification of distinct Wieferich problems.

The formal companion proves CF2 with the actual residual equations and
an explicit coefficient certificate. The gcd and all-extension-degree
classification above are ordinary mathematical consequences with the
small polynomial remainders exposed. They are not asserted to have
received Lean kernel certification merely because the certificate has
an authored Lean representation.

### CX. Global characteristic support and two additional Carlitz families

This subsection belongs to the same Wieferich lifting-and-elimination problem
family as the integer WSS question and CF1-CF5. Throughout CX, the letter
r denotes the prime 519555805809266011. It is a field characteristic,
not an asserted integer WSS prime. Characteristic five is deliberately
excluded from the final nonconforming degree-five classification.

#### CX.1 A nonzero integer in the orbit ideal

Retain the five literal residual polynomials f_0,...,f_4 from CF, now in
Z[a,b,c,d]. Put tau(a,b,c,d)=(b-a,c-a,d-a,-a). Then tau^5 is the identity
and f_i=tau^i(f_0).

**Theorem CX1.** There is an explicitly specified integer polynomial S of
total degree ten such that

$$\boxed{\sum_{i=0}^{4}\tau^i(S)f_i=D,\qquad
D=4673196650932024062540600
=2^3 3^2 5^2\cdot19\cdot263\cdot r.}$$

There is also an integer polynomial S_3 of degree ten such that

$$\boxed{\sum_{i=0}^{4}\tau^i(S_3)f_i\equiv1\pmod3.}$$

**Proof.** The complete Horner expressions for S and S_3 are supplied on
the proof path of `CarlitzFiveCharacteristic.result`. They have508 and340
nonzero monomials respectively. Expand the five substitutions and multiply
by their quartics. For the first certificate every nonconstant integer
coefficient cancels and the constant coefficient is D. For the second,
every coefficient of the difference from one is divisible by three.
These are polynomial identities, independent of field size or any tested
prime range. The independent verifier parses the authored expressions
and checks their integer coefficients. A successful Groebner command is
not used as a mathematical premise.

**Corollary CX2.** If K is a field of odd prime characteristic p and an
actual ring endomorphism sigma and theta satisfy sigma^5(theta)=theta
and the degree-five residual, then

$$\boxed{p\in\{5,19,263,r\}.}$$

**Proof.** Applying sigma to the original residual yields all five
polynomials f_i=0. CX1 forces D=0 in K, hence p divides D. Its second
certificate excludes p=3. Factoring D leaves the asserted list. The
factor r is prime: a recursive Lucas primality certificate uses

$$r-1=2\cdot3\cdot5\cdot31\cdot71\cdot7868481081467.$$

The witness two has order r-1 modulo r, as verified by the congruence
2^(r-1)=1 and the gcd conditions for each distinct prime factor of r-1.
The recursive primality tree has19 nodes and is checked from the base2.
For the new Lean declaration the output is the exact divisibility
p | 8*25*19*263*r; it does not assume or certify the primality of r.
The full finite prime support is the ordinary corollary using the
separately supplied primality certificate.

#### CX.2 Explicit upper difference polynomials in the two new characteristics

Define the following monic polynomials, each over its indicated prime field:

$$m_{263}(X)=X^5+118X^3-29X^2-57X-11,$$

$$m_r(X)=X^5-126121936908049079X^3
-20709279787633690X^2+49850011469824031X
-48822819797228934.$$

**Theorem CX3.** Every common zero of f_0,...,f_4 in characteristic p,
for p=263 or p=r, satisfies m_p(d)=0.

**Proof certificate.** In each characteristic there are five polynomial
multipliers V_i of total degree at most eight with

$$\sum_{i=0}^4 V_i f_i=m_p(d).$$

The exact coefficient lists are supplied in the accompanying mathematical
verification bundle as `upper_certificate_263.json` and
`upper_certificate_519555805809266011.json`. Their nonzero term counts
are (268,129,288,267,204) and (269,129,288,268,204). Each entry consists
of its four nonnegative exponents and its integer coefficient; the
coefficientwise difference from m_p(d) is zero modulo p. A separate
standard-library polynomial implementation expands and checks these
identities; it does not run the discovery elimination. Thus the identity
excludes every hidden higher-degree difference, rather than certifying
only a set of sampled roots.

The coefficient search itself can be reproduced using the explicit
ansatz: take all495 monomials in four variables of degree at most eight,
multiply each by each of the five quartics, and compare the1820 coefficient
positions of degree at most twelve. The certificate consists of2475
coefficients with the above nonzero supports. This is a finite coefficient
space; no enumeration of a finite field or prime candidate space occurs.

#### CX.3 Irreducibility and all extension-degree cases

**Lemma.** Both m_p are irreducible over F_p. In the degree-five quotient,

$$X^{p^5}=X,\qquad \gcd(m_p,X^p-X)=1.$$

**Proof.** Binary powering and Euclidean division of the displayed monic
polynomials give the two exact remainders. Since five is prime, every
irreducible factor of a divisor of X^(p^5)-X has degree one or five;
the gcd excludes degree one. This proves irreducibility. The verification
bundle gives every arithmetic operation in a standard-library checker.

For e in {1,2,3,4}, in F_p[d]/(m_p), set

$$A_e=-d^{p^e},\quad B_e=-d^{p^e}-d^{p^{2e}},\quad
C_e=-d^{p^e}-d^{p^{2e}}-d^{p^{3e}}.$$

Let R_e=R(A_e,B_e,C_e,d). The coefficient lists below are in ascending
powers of d, with all entries taken modulo p. Empty means the zero
polynomial.

For p=263:

| e | coefficients of R_e |
|---|---|
|1|(183,220,12,4,154)|
|2|(30,211,26,167,232)|
|3|()|
|4|(154,204,206,168,178)|

For p=r:

| e | coefficients of R_e |
|---|---|
|1|(190517489712118051,453954193719581280,337654280384855023,339436209018876665,455577831796691642)|
|2|(508627157208596802,212497064539069456,291781918141666170,234967044749037575,344791609743198488)|
|3|(275489135042958680,277163834281479958,495778609882052580,289423878907630600,131513161327939832)|
|4|()|

**Theorem CX4.** Let p=263 or r, q=p^s, s>=1, and put

$$\nu_p(X)=-m_p(-X),\qquad e_{263}=3,\quad e_r=4.$$

Then

$$\boxed{
\gcd(T^{q^5}-T,M_{5,q})=
\begin{cases}
\nu_p(T^q-T),&s\equiv e_p\pmod5,\\
1,&s\not\equiv e_p\pmod5.
\end{cases}}$$

**Proof.** For a common root theta, let d=theta^(q^4)-theta. CX3 gives
m_p(d)=0. Its degree over F_p is five. The Frobenius action consequently
depends only on e=s mod5. Closedness gives

$$\theta^q-\theta=-d^q,\quad
\theta^{q^2}-\theta=-d^q-d^{q^2},\quad
\theta^{q^3}-\theta=-d^q-d^{q^2}-d^{q^3}.$$

It also gives Tr(d)=0. If e=0, that trace is5d, nonzero because p!=5
and m_p(0)!=0. If e!=0, the trace vanishes since the X^4 coefficient
of m_p is zero. The remainder table and irreducibility now force
exactly e=e_p: all other residuals are nonzero of degree less than five.
The formulas also imply nu_p(theta^q-theta)=0.

Conversely, suppose nu_p(theta^q-theta)=0 and s=e_p modulo five. Write
a=theta^q-theta and d=-a^(q^4). Then d is a root of m_p, a=-d^q,
and the trace of a over five Frobenius steps is zero. Telescoping gives
theta^(q^5)=theta. The same remainder table gives the required residual.
Thus the common-root set is exactly the one asserted. Both polynomials
whose roots are compared are squarefree: the derivative of T^(q^5)-T
is-1, and the derivative of nu_p(T^q-T) is -nu_p'(T^q-T), coprime to
it because nu_p is irreducible and separable. Monicity finishes the gcd.

#### CX.4 Actual prime polynomials and the complete nonconforming classification

Define

$$P_{263}(T)=T^5-25T^3-96T^2+67T-48,$$

$$P_r(T)=T^5-161075390461176250T^3+236246748108143654T^2
-67033555198929295T+76181904805977016.$$

**Theorem CX5.** For p=263 or r and s=e_p modulo five, the entire set
of monic degree-five Carlitz-Wieferich primes in F_(p^s)[T] is

$$\boxed{\{P_p(T-a):a\in\mathbb F_{p^s}\}.}$$

**Proof.** For p=263, a root d of m_p gives

$$\theta_0=42d^4-16d^3+13d^2+115d+123.$$

For p=r use

$$\theta_0=228292315964840347d^4+128383604335500605d^3
-185913959198815567d^2-41306496497157789d
+63808001016856156.$$

Exact reduction gives P_p(theta_0)=0 and theta_0^q-theta_0=-d^q.
The difference is nonzero, and theta_0 lies in F_(p^5), so its degree
over F_q is five when gcd(s,5)=1. Thus P_p is irreducible over each
admissible F_q. CX4 and the residual criterion make it Carlitz-Wieferich.
Alternatively, direct Horner evaluation of the original Carlitz action
verifies rho_(P_p)(1)=1 modulo P_p^2. Translation preserves all q-Frobenius
differences. The q translates are distinct because their T^4 coefficients
differ by5a. CX4 has degree5q and no linear factor, so all factors have
degree five and these q translates exhaust them.

For independent direct verification at all extension degrees, the five
residue tests s=1,...,5 suffice only after proving their periodicity:
if P_p is irreducible over F_p, then in F_p[T]/(P_p^2),

$$T^{p^{s+5}}-T^{p^s}=(T^{p^5}-T)^{p^s}=0\quad(s\ge1).$$

Indeed P_p divides T^(p^5)-T and p^s>=2. Every element of that quotient
is a polynomial in T, so its p^s-Frobenius has the same period five.
This is an exact algebraic reduction, not an extrapolation from ten tests.

**Theorem CX6.** For EVERY odd prime p!=5 and EVERY s>=1, the number
of monic degree-five Carlitz-Wieferich primes over F_(p^s) is

$$\boxed{
\begin{cases}
p^s,&p=19\text{ and }s\equiv3\pmod5,\\
p^s,&p=263\text{ and }s\equiv3\pmod5,\\
p^s,&p=r\text{ and }s\equiv4\pmod5,\\
0,&\text{otherwise}.
\end{cases}}$$

**Proof.** CX2 restricts the characteristics to19,263,r under the
stated domain. CF4-CF5 classify19, and CX4-CX5 classify the other two.
In particular the count is zero at s=1 for every odd prime p!=5.
This closes the degree-five nonconforming prime-field question uniformly
in p, beyond the finite table in Proposition5.2 of the source. It does
not exclude higher-degree nonconforming examples over prime fields,
and it makes no assertion for the conforming characteristic-five case.

#### CX.5 What this does and does not transfer to integer WSS

The integer constant D was derived before choosing a characteristic.
Its prime factors produced the two new candidate characteristics; explicit
Frobenius compatibility then selected the allowed extension classes and
constructed the actual prime polynomials. Both existence and nonexistence
are certified in this fixed degree, without a field-element scan.

This supplies a successful characteristic-independent elimination pattern
inside the unified Wieferich problem family. An integer-WSS transfer would
need a fixed or controlled-complexity integer system genuinely implied by
the ORIGINAL golden lifting condition, together with a nonzero integer
in its elimination ideal. The known finite logarithm polynomial instead
has degree p-1, and the existing golden-unit relations leave q_p free.
There is no proved map from those equations to the five residuals here.
In particular19,263,r are not claimed to be integer WSS primes, and
CX2 cannot be applied to them as an integer-WSS exclusion theorem.

The known nineteen family and its Conjecture4.2 proof are prior results
of this PR. The two new families, all-characteristic obstruction and
prime-field degree-five exclusion form one continuation, not several
independently counted open-problem solutions. Exact-characteristic and
polynomial searches did not locate the new families in the checked
primary literature. The companion paper listed as in preparation in
arXiv:2607.15305v2 could contain related work; priority and external
acceptance remain unconfirmed.
