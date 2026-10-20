# Fibonacci 原子关系生成理论：异奇偶来源与偶秩 Robin 切面

本卷沿用[原卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md)的定义、记号与第 1–440 节；第 441–444 节的编号在本卷继续。下文未附卷名的第 1–440 节引用均指原卷，第 441–444 节引用均指本卷。各节保留其所列文献、适用条件与未解范围。

## 441. 异奇偶倍增双项的乘法切面与 Robin 尾段

本节记录经典乘积恒等式与 §172.1 在同一个加法来源上的参数对应。保持标准 Fibonacci、Lucas 指标，固定正整数 $c$，取奇数 $b\ge3$，并记 $V_b=F_{2b}+F_b$。两个实际占位的间距为 $b$，均随 $b$ 增长；它们异奇偶，因此不是 §169 的同奇偶双项。以下复用既有解析输入，不新增一般乘积估计或 Lean 声明。

**应用 441.1（实际倍增来源的消失比值）。** 写 $b=2m+1$。经典恒等式

$$
F_{2b}=F_bL_b,\qquad
L_mL_{m+1}=L_{2m+1}+(-1)^m,\qquad
5F_mF_{m+1}=L_{2m+1}-(-1)^m
$$

给出同一整数的精确分解

$$
V_b=
\begin{cases}
F_bL_mL_{m+1},&m\text{ 为偶数},\\
5F_bF_mF_{m+1},&m\text{ 为奇数}.
\end{cases}
\tag{441.1}
$$

所有因子都为正，其最大实际指标恰为 $b$。直接应用定理 172.1：两支分别取固定乘子 $c$、$5c$，因子数上限均取三。对任意 $\varepsilon>0$，取两个既有阈值的最大值，即得

$$
\lim_{\substack{b\to\infty\\b\text{ 为奇数}}}
\frac{\sigma(cV_b)}{e^\gamma cV_b\log\log(cV_b)}=0.
\tag{441.2}
$$

因而包括 $c=5040$ 在内的每个固定乘子，都有对这两支共同有效的严格 Robin 尾段。这不允许 $c$ 随 $b$ 自由增长，也不认证未计算的有限初段。

**应用 441.2（固定局部停止不能替代该乘法切面）。** 固定非空有限素数集 $S$，令 $R=\prod_{p\in S}p$。沿用 §170.5 的矩阵周期提升，选 $12\mid P_0$、$P_0\ge12$ 且 $M^{P_0}=I\pmod R$，并令

$$
P_t=P_0R^{t-1},\qquad b_t=P_t-1,\qquad n_t=5040V_{b_t}.
$$

既有提升给 $M^{P_t}=I\pmod{R^t}$。负指标读数 $F_{-2}=-1$、$F_{-1}=1$ 因而给

$$
F_{2P_t-2}\equiv-1,\qquad F_{P_t-1}\equiv1\pmod{R^t},
\qquad R^t\mid V_{b_t}.
\tag{441.3}
$$

这些都是该倍增射线内的合法异奇偶双项，所有 $S$ 方向的赋值同时至少为 $t$。对同一个 $n_t$，记 $\Lambda_t=\log\log n_t$ 和 $\eta_S(n_t)=\prod_{p\in S}(1-p^{-v_p(n_t)-1})$，则

$$
\Lambda_t=(t-1)\log R+O(1),\qquad
0\le1-\eta_S(n_t)\le |S|2^{-t-1}.
$$

直接复用 §170.5 的指数与多项式比较，得到最终有

$$
\eta_S(n_t)\left(1+\frac{a_0}{\Lambda_t^3}\right)>1,
\qquad a_0=0.0094243.
\tag{441.4}
$$

所以固定赋值阈值以及这一固定 $S$ 的局部乘积充分条件，均不能认证整条射线；式（441.2）却控制了它的完整 Robin 比值。这里没有 Robin 反例，也没有对所有有限信息方法作不可能性断言。

**来源与边界。** 式（441.1）使用经典 Fibonacci–Lucas 乘积恒等式；统一估计与周期提升分别直接复用 §§172、170。新增内容是这一实际异奇偶加法族与已有乘法估计、局部高赋值构造之间的参数衔接，不主张恒等式、秩估计或 Robin 方法的原创性。一般异奇偶双项和、任意五模式历史及全部整数的 Robin 判据仍未由此解决；本节为纸面应用，没有新增 Lean 核验。

## 追加锚（本行以下为增补区）

## 442. 异奇偶双项的可变小约数切面与完整 Robin 尾段

本节在同一个实际来源上复用 §175.1 的素数秩排除、[尺度几何卷命题 8.1](AURIC_FIB_ROBIN_DIVISOR_SCALE_GEOMETRY.md) 的加层倍率与 §160.1 的 Axler 上界。固定正整数 $c$，记 $\varphi=(1+\sqrt5)/2$、$a_0=0.0094243$、$Z(n)=\sigma(n)/n$。这里控制完整约数响应，而不把五模式区间长度当成 Euler 权重。以下为已有结果的纸面应用，没有新增 Lean 声明或解析上界的原创性主张。

**应用 442.1（指标差含可变小约数时的一致严格估计）。** 存在仅依赖 $c$ 的 $A_c$，使所有满足下列条件的整数 $a,b,d$，在 $a\ge A_c$ 时都有式（442.2）：

$$
a>b\ge2,\qquad k=a-b\ge3\text{ 为奇数},\qquad g=\gcd(a,b),
$$

$$
d\ge5\text{ 为奇数},\qquad d\mid k,\qquad\gcd(d,g)=1,
\qquad d\le\frac{\log\log a}{\log\varphi}.
\tag{442.1}
$$

令 $V=F_a+F_b$、$n=cV$，则

$$
\boxed{\frac{Z(n)}{e^\gamma\log\log n}
<1-\frac1{8c\log a}<1.}
\tag{442.2}
$$

阈值对满足（442.1）的全部 $b,d$ 共同有效；$d$ 无须固定，$k$ 也无须为 $o(\log a)$。结论不认证 $a<A_c$ 的有限部分，也不允许 $c$ 随 $a$ 自由增长。

证明。先从同一对指标提取一个实际缺失素数。奇数 $d\ge5$ 时 $F_d$ 有奇素因子：若 $3\nmid d$，则 $F_d>1$ 为奇数；否则 $d\ge9$，标准模四周期给 $F_d\equiv2\pmod4$ 且 $F_d>2$。选任意奇素数 $p\mid F_d$。若同时 $p\mid V$，由 $z(p)\mid d\mid k$ 与 §175.1，必有 $z(p)\mid g$，这与 $\gcd(d,g)=1$ 矛盾。因此

$$
p\nmid V,\qquad p\le F_d<\varphi^d\le\log a,
\qquad v_p(n)=v_p(c)=:J.
\tag{442.3}
$$

不向 $n/\varphi(n)$ 的真实乘积插入缺失素数。改为使用真实整数 $np$，直接将既有加层倍率用于指数 $J=v_p(c)$，得到

$$
\begin{aligned}
\frac{Z(np)}{Z(n)}
&=\frac{1-p^{-J-2}}{1-p^{-J-1}}\\
&=1+\frac{(1-p^{-1})p^{-J-1}}{1-p^{-J-1}}
\ge1+\frac1{2cp}
\ge1+\frac1{2c\log a}.
\end{aligned}
\tag{442.4}
$$

这里使用 $p^J\le c$；$J=0$ 同样允许。对 $m=np$ 直接应用 §160.1 所引用的 [Axler 作者稿 v3](https://arxiv.org/pdf/2110.13478v3) 式（3.4）—（3.5）：当 $a$ 足够大时，$m$ 超过既有固定阈值，因而

$$
Z(m)\le\frac m{\varphi(m)}
<e^\gamma\left(\Lambda_m+\frac{a_0}{\Lambda_m^2}\right),
\qquad\Lambda_m=\log\log m.
\tag{442.5}
$$

Binet 的标准增长界对全部 $2\le b<a$ 一致给出

$$
\log n=a\log\varphi+O_c(1),\qquad
\Lambda_n=\log a+\log\log\varphi+O_c(a^{-1}).
$$

又由 $p\le\log a$，

$$
0<\Lambda_{np}-\Lambda_n
=\log\left(1+\frac{\log p}{\log n}\right)
=O_c\left(\frac{\log\log a}{a}\right).
$$

故对同一个实际 $n,p$，一致有

$$
\frac{\Lambda_{np}+a_0/\Lambda_{np}^2}{\Lambda_n}
=1+O_c((\log a)^{-3})
 +O_c\left(\frac{\log\log a}{a\log a}\right)
=1+o_c((\log a)^{-1}).
\tag{442.6}
$$

令 $\delta=1/(2c\log a)$。扩大仅依赖 $c$ 的阈值，使（442.6）至多为 $1+\delta/4$，且 $0<\delta\le1$。结合（442.4）—（442.5），有

$$
\frac{Z(n)}{e^\gamma\Lambda_n}
<\frac{1+\delta/4}{1+\delta}
\le1-\frac\delta4
=1-\frac1{8c\log a},
$$

即得（442.2）。所有误差界只依赖固定的 $c$，没有把分别可达的局部最优值组合成共同实现。$\square$

**应用 442.2（同一区域可保留任意指定有限集的高赋值）。** 固定非空有限素数集 $S$，令 $R=\prod_{p\in S}p$。从 §170.5 取固定 $P_0\ge12$，满足 $12\mid P_0$、$M^{P_0}=I\pmod R$。取趋于无穷的素数 $d\nmid RP_0(P_0-2)$，并对每个 $d$ 选整数 $T$，满足

$$
T\equiv1\pmod{\operatorname{ord}_d(R)},\qquad
T\ge\exp(2d\log\varphi).
$$

设 $P=P_0R^{T-1}$，并选唯一 $1\le u<d$ 使 $uP\equiv-1\pmod d$。定义实际指标

$$
a=(u+1)P-1,\qquad b=P-2.
\tag{442.7}
$$

它们分别为奇数、偶数。由 $P\equiv P_0\pmod d$，有 $d\nmid b$；同时

$$
a-b=uP+1\equiv0\pmod d,
\qquad\gcd(d,\gcd(a,b))=1.
$$

且 $\log\log a=\log T+O_{S,P_0}(1)$，所以（442.1）的小约数条件最终成立。既有周期提升给 $M^P=I\pmod{R^T}$；沿用负指标 $F_{-1}=1$、$F_{-2}=-1$，得到

$$
F_a\equiv1,\qquad F_b\equiv-1\pmod{R^T},
\qquad R^T\mid F_a+F_b.
\tag{442.8}
$$

因此（442.2）适用，同时每个 $S$ 中素数的真实赋值至少为 $T$。对 $n=5040(F_a+F_b)$，令 $\Lambda=\log\log n$，有

$$
\Lambda=(T-1)\log R+\log(u+1)+O_{S,P_0}(1)\asymp_{S,P_0} T,
\qquad
0\le1-\eta_S(n)\le |S|2^{-T-1}.
$$

直接复用 §441.2 的指数与多项式比较，得到最终有

$$
\eta_S(n)\left(1+\frac{a_0}{\Lambda^3}\right)>1.
\tag{442.9}
$$

所以这一指定固定 $S$ 的 Axler 局部乘积充分条件不能认证这些实际来源，而（442.2）的可变素数切面仍给出完整 Robin 估计。它没有排除其他充分条件。

此外，$P_0u+1$ 是 $d$ 的正倍数，故 $u\ge(d-1)/P_0\to\infty$。从（442.7）可得

$$
\frac ab\longrightarrow\infty,\qquad
\frac{a-b}{\log a}\longrightarrow\infty,\qquad
 a-2b=(u-1)P+3>0.
$$

这些来源超出 §180.3 的小间距条件与 §441 的倍增射线；这里没有断言它们不满足任何其他已知来源条件。

**来源与未解范围。** Fibonacci 强整除性、奇偶性、Binet 增长与负指标恒等式是经典输入；秩排除、周期提升和解析上界分别直接复用 §§175、170、160，加层倍率直接引用尺度几何卷命题 8.1。新增内容是可变小约数条件与同一实际双项、真实素数增广及完整预算之间的参数对应，不是新的通用 Robin 判据。固定 $S$ 的失败只针对（442.9）中的指定充分条件，不是有限信息方法的一般不可能性结果。一般异奇偶双项、任意五模式历史、严格全整数 Robin 与 RH 仍未解决；本节未做数值阈值计算或 Lean 核验。

## 追加锚（本行以下为增补区）

## 443. 偶指标的小偶约数切面与可变缺失素数

固定正整数 $c$，沿用 $F_0=0,F_1=1$、$\varphi=(1+\sqrt5)/2$、$Z(n)=\sigma(n)/n$ 与素数的首次 Fibonacci 整除秩 $z(p)$。本节直接复用 §299 所引用的 Carmichael 本原素因子定理，以及 §442.4—§442.6 对真实整数加层后的完整 Robin 估计。新的来源条件放在偶指标本身；不要求指标差含有与共同指标互素的小约数。以下为已有定理的纸面应用，没有新增 Lean 核验或文献优先权主张。

**应用 443.1（偶指标含可变小偶约数的一致严格估计）。** 存在仅依赖 $c$ 的 $A_c$，使所有满足

$$
a>b\ge3,\qquad a-b\ge3\ \text{为奇数},\qquad e\in\{a,b\}\ \text{为偶数},
$$

$$
d>0,\qquad d\mid e,\qquad 2\mid d,\qquad d\notin\{2,6,12\},
\qquad d\le\frac{\log\log a}{\log\varphi}
\tag{443.1}
$$

的整数 $a,b,d,e$，在 $a\ge A_c$ 时均有

$$
\boxed{\frac{Z(c(F_a+F_b))}
 {e^\gamma\log\log(c(F_a+F_b))}
 <1-\frac1{8c\log a}<1.}
\tag{443.2}
$$

阈值对 $b,d$ 共同有效，$d$ 可以增长。指标差至少三，故这确实允许同一个规范 Zeckendorf 来源中的两个非相邻占位；单位字段为零。

证明。直接引用 §299 已采用的 [Yabuta, *A Simple Proof of Carmichael’s Theorem on Primitive Divisors*, Theorem 3，pp. 439、441—442](https://www.fq.math.ca/Scanned/39-5/yabuta.pdf)。该文的本原因子定义明确指素数；定理给出一个本原素数 $p\mid F_d$，其首次秩恰为 $z(p)=d$。这里保留本原素数定理的全部例外；$d$ 为偶数还排除了指标一。由于 $z(2)=3$、$z(5)=5$，这个 $p$ 不是二或五。

令 $o$ 为 $a,b$ 中的奇指标。由 $d\mid e$ 与 Fibonacci 强整除性，$p\mid F_e$。若 $p\mid F_o$，秩性质将给出偶数 $d\mid o$，与 $o$ 为奇数矛盾。因此，对同一个实际来源 $V=F_a+F_b$，

$$
p\nmid V,\qquad p\le F_d<\varphi^d\le\log a,
\qquad v_p(cV)=v_p(c).
\tag{443.3}
$$

这不同于把一个未出现的素数插入 $n/\varphi(n)$ 的乘积。令 $n=cV$，使用真实整数 $np$；§442.4 的既有加层倍率直接给出

$$
\frac{Z(np)}{Z(n)}
\ge1+\frac1{2cp}
\ge1+\frac1{2c\log a}.
\tag{443.4}
$$

§442.5—§442.6 的 Axler 上界与 Binet 参数估计只使用 $c$ 固定、$2\le b<a$ 和实际 $p\le\log a$，不使用小约数来自指标差这一条件。故以式（443.3）的同一个 $p$ 直接代入那里的已证比较，得到式（443.2）。其中 $p\mid c$ 允许发生，其强制指数已由 $p^{v_p(c)}\le c$ 支付；没有更换原整数或遗漏 Euler 因子。

### 443.2 与指标差小约数切面的独立来源

令 $d$ 满足式（443.1）的偶数条件，取任意足够大的奇数 $g\ge3$，并设

$$
a=dg,\qquad b=(d-1)g.
\tag{443.5}
$$

此时 $\gcd(a,b)=a-b=g$。每个 $h\ge5$、$h\mid a-b$ 都满足 $\gcd(h,\gcd(a,b))=h>1$，所以 §442.1 的小约数条件对这些来源没有可用的 $h$。它们也不属于 §441 的倍增射线，因为 $d\ge4$ 时 $a\ne2b$。

选择奇数 $g>\exp(\varphi^d)$ 即保证 $d<\log\log a/\log\varphi$。因而这里同时允许 $d$ 无界增长、两项指标共同增长以及指标差无界增长；结论没有把参数冻结成一条固定射线。这些比较只说明所列来源超出 §§441、442 的指定条件，不断言它们不满足任何其他已知充分条件。

### 443.3 任意固定有限素数切面仍可共同处于高赋值

设 $S$ 为任意非空有限素数集，$R=\prod_{q\in S}q$，$T\in\mathbb Z_{\ge1}$。复用 §170 的有限模周期，取一个偶数 $P>0$，使

$$
M^P=I\pmod{R^T},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

选取任意奇素数 $q\ge7$ 且 $q\nmid P$，令 $d=2q$。由于 $\gcd(2q,P)=2$，经典 CRT 使下面两个条件有任意大的共同正整数解 $a$：

$$
a\equiv-2\pmod P,\qquad a\equiv0\pmod{2q}.
\tag{443.6}
$$

对这样的 $a$，置

$$
b=1+P\left\lfloor\frac a{2P}\right\rfloor.
\tag{443.7}
$$

于是 $b$ 为奇数且 $b=a/2+O_P(1)$；令 $a$ 沿该同余类充分增大，就同时满足 $a>b\ge3$、$a-b\ge3$、式（443.1）的大小限制与式（443.2）的共同起点。两个指标都趋于无穷。

由同一个周期与 §442 已使用的负指标恒等式 $F_{-2}=-1$、$F_1=1$，有

$$
F_a+F_b\equiv F_{-2}+F_1=0\pmod{R^T}.
\tag{443.8}
$$

故任意预选有限集合 $S$ 中的素数都可在实际来源中达到任意指定深度，而式（443.2）仍成立。这里提供缺失素数的是式（443.3）的可变偶秩切面。该素数必不属于 $S$：若 $p\in S$，$M^P=I\pmod p$ 将给出 $d=z(p)\mid P$，与 $q\nmid P$ 矛盾。

对任意预设的有限阈值表 $(H_p)_{p\in S}$，取 $T>\max_{p\in S}H_p$，便使这些来源不满足指定充分条件 $\exists p\in S:\ v_p(n)\le H_p$。这只限定这张固定阈值表的适用范围，不是有限信息方法的一般不可能性结论。也可以让所选 $q$ 无界增长，并在每一步令 $a$ 足够大；不需要固定 $d$ 或固定缺失素数。

**来源与范围。** 本原素因子的存在与精确秩直接引用 §299 的 Carmichael—Yabuta 输入；完整加层与解析预算直接引用 §442.4—§442.6 的 Axler 应用；强整除性、负指标、有限模周期与 CRT 均为既有结果。新增的是偶指标约数、同一实际双项和完整 Robin 预算之间的参数对应，以及这些来源与指定固定素数阈值表的共同高赋值对应。一般异奇偶双项、任意五模式历史、所有 $n>5040$ 的严格 Robin 不等式与 RH 仍未解决。本节没有计算数值起点，也没有执行数值实验或 Lean 编译。

## 追加锚（本行以下为增补区）

## 444. 偶秩相位切面对任意长五模式来源的完整 Robin 估计

固定正整数 $c$，沿用 $F_0=0,F_1=1$、$\varphi=(1+\sqrt5)/2$ 和 $Z(n)=\sigma(n)/n$。本节只研究单位字段为零的实际规范 Zeckendorf 来源。令 $I\subset\mathbb Z_{\ge3}$ 为非空有限集合，任意不同 $i,j\in I$ 满足 $|i-j|\ge2$，并记

$$
V_I=\sum_{j\in I}F_j,\qquad a=\max I.
$$

因此这些占位可直接分成合法的 $[null,2,3,2\,5,5]$ 三位窗口；模素数读数为零的占位仍是实际占位，不会被改成语法上的 null。本节复用 §§47、163 的矩阵回返与素数秩界、§299 的 Carmichael—Yabuta 本原素数定理，以及 §442.4—§442.6 的完整加层估计；不新增一般秩定理或 Robin 判据。以下为纸面应用，没有 Lean 核验或文献优先权主张。

**应用 444.1（无界占位数与增长偶秩的一致严格估计）。** 存在仅依赖 $c$ 的 $A_c$，使所有满足下列条件的实际来源在 $a\ge A_c$ 时均满足式（444.2）。存在正偶数 $d\notin\{2,6,12\}$，使

$$
d\le\frac{\log\log a}{\log\varphi},\qquad
j\bmod 2d\in\{0,1,2d-1\}\quad(j\in I),
$$

$$
1\le h:=\#\{j\in I:j\equiv1\text{ 或 }-1\pmod{2d}\}\le d-2.
\tag{444.1}
$$

则

$$
\boxed{\frac{Z(cV_I)}{e^\gamma\log\log(cV_I)}
<1-\frac1{8c\log a}<1.}
\tag{444.2}
$$

同一个起点对 $I,d,h$ 有效；实际占位总数 $|I|$ 无须有界，$d,h$ 也可增长。该结论针对整个实际整数 $cV_I$，没有逐项使用或假定 $\sigma$ 对加法具有乘法性。

证明。直接复用 §299 已引用的 [Yabuta, Theorem 3，pp. 439、441—442](https://www.fq.math.ca/Scanned/39-5/yabuta.pdf)，选本原素数 $p\mid F_d$，使 $z(p)=d$。偶指标及已列例外给出 $p\ne2,5$。§163 的既有秩界 $z(p)\mid p-1$ 或 $z(p)\mid p+1$ 直接给

$$
p\ge d-1>h.
\tag{444.3}
$$

§47 的矩阵公式 $M^d=F_{d-1}I+F_dM$ 给 $M^d=\lambda I\pmod p$。这里 $M=\begin{pmatrix}0&1\\1&1\end{pmatrix}$；因 $d$ 为偶数，$\det M^d=1$，故 $\lambda^2=1$，从而 $M^{2d}=I\pmod p$。由同一周期以及 $F_0=0,F_1=F_{-1}=1$，得到这个实际来源的逐项读数

$$
F_j\equiv
\begin{cases}
0,&j\equiv0\pmod{2d},\\
1,&j\equiv1\text{ 或 }-1\pmod{2d}.
\end{cases}
\pmod p.
$$

于是全部占位共同满足

$$
V_I\equiv h\not\equiv0\pmod p,\qquad
p\le F_d<\varphi^d\le\log a,\qquad
v_p(cV_I)=v_p(c).
\tag{444.4}
$$

这里的非零性是同一个和的计数与同一个素数下界共同给出的；并未把若干分别缺失素数的加项相加。

规范表示的最高占位给出经典区间 $F_a\le V_I<F_{a+1}$，所以对全部合法 $I$ 一致有

$$
\log(cV_I)=a\log\varphi+O_c(1).
\tag{444.5}
$$

这正是 §442.6 的规模接口。令 $n=cV_I$，对式（444.4）的实际 $p$ 直接复用 §442.4 的合法整数 $np$ 加层倍率与 §442.5 的 Axler 上界。式（444.5）使 §442.6 的全部误差比较仍仅依赖固定 $c$，不依赖占位数、$h$ 或 $d$。由该处已经给出的完整预算比较即得式（444.2），包括 $p\mid c$ 的情形。$\square$

### 444.2 来源确实允许任意多实际占位

给定任意符合上述偶数条件的 $d$、$1\le h\le d-2$ 和充分大的整数 $K\ge h+2$，先占用

$$
I_1=\{2dj+1:1\le j\le h\},
$$

再从

$$
\{2dj:h+1\le j\le K\}
$$

中任意选取包含 $2dK$ 的子集 $I_0$，令 $I=I_0\cup I_1$。所有相邻实际占位至少相差二，最大占位为 $a=2dK$，并且满足式（444.1）的计数条件。取 $K$ 足够大即可满足小偶约数的截止条件。

固定 $d,h,K$ 时，这里有 $2^{K-h-1}$ 个不同的规范来源；其中的实际占位总数可以随 $K$ 无界增长。也可令 $d,h$ 增长后再选择共同适用的 $K$。这些来源无需只有两个占位，也无需填满一条等差占位串。§172 的有界 Fibonacci/Lucas 乘积定理及 §§174、176 的特定求和分解仍按其原条件使用；这里没有为任意子集假定同样的有界因子分解，也不声称排除了每一种其他充分条件。

**来源与未解范围。** 素数的存在、秩界、矩阵标量回返、Zeckendorf 最高位区间与解析加层比较均复用既有结果。新增衔接是：偶秩周期中的零／一占位读数、严格小于该素数的实际占位计数，以及对任意长规范来源有效的同一完整 Robin 估计。普通五模式历史不必满足式（444.1）；全部整数 $n>5040$ 的严格 Robin 不等式及 RH 仍未解决。没有计算数值起点、执行科学实验或 Lean 编译。

## 追加锚（本行以下为增补区）
