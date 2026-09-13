# 元素周期树(Periodic Tree of Mathematical Elements)· 章程与施工册 v1.0
*(**项目第四文档(正典)**,第 335 版记事立;PZG–GICT 项目附属工程;ZFC 内定义,零新公理;账本 27.417,2026-07-20。配套机读注册表:PERIODIC_TREE_registry.jsonl)*

## 0. 名与地契
树干为 **Stern–Brocot / Farey 树**(Stern 1858, Brocot 1861)——$(2,3,\infty)$ 基本直角三角形之反射递归;节点 = $SL_2(\mathbb Z)$ 矩阵,路径 = $L/R$ 词 = 连分数,叶叶既约(树上素性之原型定理)。本工程不植树,只立**挂载协议**:凡具"递归 + 二次"双结构之数学对象,经函子标注入册。

## 1. 挂载协议(四标签)
每个对象登记:**地址**(树路径/典范词——递归坐标);**素性位**(该层不可约判据之输出);**度量荷**(二次型脸:迹 $T$、内容 $g$、判别式 $d=(T^2-1)/g^2$、勾股恒等 $D=3A^2+(A+B)^2$、辐角 $\arg z$);**组合荷**(行走脸:$\Psi$、城色 $m\bmod36$、Jacobi 位)。附加:**流指针**(三明治后继 $T'=6c+7T$)与**核籍**(奇核者附核词与 $j=\mathrm{tr}/12$)。

## 2. 门卫手册(素性三级判据)
- **一级(地址级,线性时间)**:典范词非偶长词之 $k\ge2$ 次幂(奇词平方**豁免**——类-本原判据,GICT E.38)。
- **二级(代数级,完全判定)**:$(T,g)$ 为 Pell $p^2-dq^2=1$ 之**基本解**(本原判定定理,GICT E.45;120/120)。奇核双覆盖判据:$m=x^2$ 且 $2x\mid g$(E.44;114/114)。
- **三级(层际级)**:素性沿商余机之降解指纹(D3)——素在上层未必素在下层,降解模式入册,不视为矛盾。
- **复杂度注记**:二级判据可判但基本解可指数大;一级为快速预筛。

## 3. 周期律(树之"周期"为何是定理)
- **流回归律**:$\Psi\bmod12$ 沿三明治流恰步 $-2$、周期 $6$(恰等传播律,E.42/E.37;正锥无条件)。
- **城色轮转律**:$m\bmod36$ 决定 $\Psi\bmod12$(城同余定理 B,E.27),色沿流按定周期轮转。
- **塔律**:$\Psi$ 之 $2$-adic 逐层由站队/互反位驱动(定理 A 与站队塔,E.23/E.27)。
门捷列夫之"周期"在此非排版,是**模不变量沿流的回归定理**。

## 4. 免检预言制度(周期表之空格传统)
已运行案例:$Z_k$ 之 $k{=}5\Rightarrow m{=}35316$(定理背书);$j$-筛处决表($j\in\{2,5,7,8,12\}$ 无核,范数一行);预言制度战绩:两中一败一尸检(败诉产出第二层楼)。

## 5. 承重三牌与壳层墓志铭
牌一(**平四律国籍检验**):组合荷非勾股(Jordan–von Neumann 判定出界),不得冒充度量荷。牌二(**反例层**):无 D1-长度者(拟同态层)为树之边界批注,非节点。牌三(**王虹条款**):逐尺度归纳为普适问法;结构涌现带维数/测度前提。**墓志铭**:本树周期律多为已证之"是什么";"为什么恰是 12、−2、Pell"之壳层理论未知——残核统计案(基本性频率)为其第一考题。

## 6. 空格册(候认领)
残核统计律;混居城真偶精判;$G$ 全群;$j$-密度;$d$-平方退化员;Markov 树层际字典(W-树3);Herglotz 虚姊妹;scl-刺客。

## 7. 施工日志(v1.0 首期)
注册域 $m\le3000$;**141 类节点**(真偶 136、奇核 5);**$\Psi{=}0$ 节点 12**;素性位:141/141 本原(城册按类去重后天然本原);城色谱 $\{0{:}30,\ 3{:}45,\ 12{:}45,\ 27{:}21\}$——恰为定理 B 可实现残类 $\{0,3,12,27\}$ 之谱(其余残类 $8,23,32,35$ 于此域未现,与实现性条件一致)。注册表:PERIODIC_TREE_registry.jsonl(逐行 JSON,四标签全字段)。

---

## Appendix U. WSS, valuation parity, and the prime values of A250093

### U.1. Scope and inspected mathematical sources

This supplement gives a complete ordinary proof of the conjecture in OEIS A250093, using explicitly cited classical theorems. It also derives exact trace-depth and half-index interfaces for the WSS problem, and proves a stronger obstruction to the multiple-root lifting construction in arXiv:2603.25343v1. It does not decide whether a Wall-Sun-Sun prime exists.

The repository objects inspected together were:

- PR #7446, head `a2035252665fc865072ce5793b60658b40374e97`: actual Fibonacci return period, the signed Frobenius index, the unit quotient bridge, and prime-power period towers. In particular `eta_p = -pi(p)*q_p` and `pi(p^2)=pi(p)` iff `q_p=0`. This PR is a Draft with proof scripts, not newly certified kernel output.
- PR #7607, head `2bdc4c88f7e54ab18dbde80b4c38750e8f9f9229`: for every odd n, evaluation of `X^(2n)-X^n-1` at the existing golden unit is exactly `(L_n-1)*phi^n`. Scalar divisibility and its squared norm are established at the source level; a number-field index theorem is not supplied.
- PR #7600, head `5b791c42b2d6541a7d4543fe504f7c2320d6b7aa`: odd-index Lucas-square Fibonacci-divisor rigidity. Its two A339669 claims are existing work and are not counted again here.
- Existing `D5/S1/Scale/Lucas.lean`: actual golden trace, Fibonacci coordinates, and `L_n^2-5F_n^2=4*(-1)^n`.
- The parity families in #7330 and #7475: characteristic-two and characteristic-three coefficient descent. Both previously considered targets already have later work, so neither is a new claim in this supplement.

The mathematical connection used below is parity of prime valuations. This differs from parity of a coefficient or index. A square multiplier changes an applicable valuation by an even amount, independently of the unknown initial valuation that could encode a WSS exception.

### U.2. External target and classical inputs

For a positive integer M, write

\[
\operatorname{core}(M)=\prod_{r\ \mathrm{prime},\ v_r(M)\ \mathrm{odd}}r.
\]

This is the squarefree part modulo squares, not the radical. It is the unique squarefree d for which M=d*s^2 with s a positive integer. The OEIS sequence is

\[
a(n)=\operatorname{core}(F_{n^2}),\qquad n\ge1.
\]

Its conjecture says that its only prime values are 3 and 3001. The stronger index classification proved here is

\[
\boxed{\operatorname{Prime}(a(n))\ \Longleftrightarrow\ n=2\ \text{or}\ n=5.}
\tag{U.1}
\]

Two classical inputs are essential, and are not claimed as new results.

**Square-class classification.** For positive indices, Fibonacci numbers have distinct square classes except for the index classes `{1,2,12}` and `{3,6}`. Equivalently, the only repeated values of `core(F_n)` are 1 at indices 1,2,12 and 2 at indices 3,6. See Ribenboim, *Square classes of Fibonacci and Lucas numbers*, Portugaliae Mathematica 46(2) (1989), 159-175. The theorem was checked directly in the author's accessible restatement, *FFF: (Favorite Fibonacci Flowers)*, Fibonacci Quarterly 43(1) (2005), 3-14, section 3.4, printed page 8: https://www.fq.math.ca/Papers1/43-1/paper43-1-1.pdf . In particular a Fibonacci number is a square only at indices 1,2,12.

**Valuation formula.** If r is an odd prime and r divides F_d, then for k>=1,

\[
v_r(F_{dk})=v_r(F_d)+v_r(k).
\tag{U.2}
\]

For r=5 one has `v_5(F_t)=v_5(t)`. At r=2, the values are 0 if 3 does not divide t, 1 if t is 3 modulo 6, and `v_2(t)+2` if t is 0 modulo 6. These are Lengyel's formulas, recorded with all exceptions in Medina and Rowland, *p-regularity of the p-adic valuation of the Fibonacci sequence*, Fibonacci Quarterly 53 (2015), 265-271, Theorem 1.4: https://arxiv.org/abs/0910.2907 . Their Theorem 1.2 supplies the rank divisibility by `r-(5/r)` for r different from 2 and 5. Formula (U.2) follows by subtracting the same initial rank valuation in the two applications of Theorem 1.4. It does not assume this initial valuation is one.

### U.3. Proof of A250093

Let n>=1 and suppose `core(F_(n^2))=P` is prime.

**Even n.** Since 4 divides n^2 and F_4=3, (U.2) gives

\[
v_3(F_{n^2})=1+v_3(n^2/4)=1+2v_3(n).
\]

This is odd, so 3 divides the squarefree core. Primality forces P=3. Since `core(F_4)=3`, the square-class classification forces n^2=4, hence n=2.

**Odd n divisible by 5.** Here 25 divides n^2. The exact factorization

\[
F_{25}=75025=5^2\cdot3001
\]

has 3001 prime. Therefore

\[
v_{3001}(F_{n^2})=1+v_{3001}(n^2/25)=1+2v_{3001}(n).
\]

This is odd. Thus P=3001, which is also `core(F_25)`. The square-class classification now forces n^2=25 and n=5.

**Odd n coprime to 5.** If n=1, its core is 1, contradicting primality. For n>1 choose any prime q dividing n. Then q is odd and q!=5. The standard Fibonacci Frobenius congruence `F_q = (5/q) (mod q)` shows q does not divide F_q.

Let r be any odd prime whose valuation in F_q is odd. In particular r!=q. Since q divides n^2, formula (U.2) gives

\[
v_r(F_{n^2})=v_r(F_q)+v_r(n^2/q)
             =v_r(F_q)+2v_r(n),
\]

which is odd. If 2 divides F_q, then q=3; both q and n^2 are odd multiples of 3, so the explicit 2-adic formula gives valuation 1 for both. Hence every prime in `core(F_q)` remains in `core(F_(n^2))`, and

\[
\operatorname{core}(F_q)\mid\operatorname{core}(F_{n^2})=P.
\]

Since q is an odd prime, q is not in `{1,2,12}`. Thus F_q is not a square and its core is greater than one. It follows that `core(F_q)=P=core(F_(n^2))`. But `n^2>=q^2>q`, and the larger index is odd and at least 9. Neither exceptional square class can contain these two indices. This contradiction finishes the necessity direction.

Conversely F_4=3 and F_25=25*3001 give prime cores at n=2 and n=5. This proves (U.1) for all positive n. There is one externally stated conjecture here; the three cases and supporting lemmas are not additional solved-open-problem counts.

**A useful general consequence.** For all m>=1 and all odd t>1,

\[
\operatorname{core}(F_m)\ \text{properly divides}\
\operatorname{core}(F_{m t^2}).
\tag{U.3}
\]

At every odd prime already dividing F_m, (U.2) adds `2*v_r(t)` to its valuation. The 2-adic formula is unchanged because t is odd. Hence divisibility of cores holds. Equality would give two distinct indices in one of the two exceptional classes. Their possible ratios are 2,6,12, none an odd square greater than one. Equality is impossible. This consequence uses the same classical inputs and is not a second external conjecture.

### U.4. What transfers to WSS, and what parity does not determine

For p prime different from 2 and 5, put `epsilon=(5/p)`, `N=p-epsilon`, and `q_p=F_N/p (mod p)`. The signed index and division convention are those of #7446. The initial valuation `v_p(F_N)` remains arbitrary in (U.2); the proofs in U.3 are therefore valid even if WSS primes exist.

The exact all-depth trace identity is

\[
\boxed{v_p(L_N-2\epsilon)=2v_p(F_N).}
\tag{U.4}
\]

Indeed N is even, `p|F_N`, `L_N=2*epsilon (mod p)`, and

\[
(L_N-2\epsilon)(L_N+2\epsilon)=5F_N^2.
\]

The second factor is `4*epsilon (mod p)`, a unit. All factors whose valuations are taken are nonzero; N>0 and F_N>0. Thus the even-index trace has an automatic second-order zero for every p. The WSS condition is instead equivalent to

\[
p^4\mid L_N-2\epsilon.
\tag{U.5}
\]

At the odd prime index, the recurrence gives

\[
2L_p=\epsilon L_N+5F_N.
\]

Multiplying by `L_N+2*epsilon` yields

\[
2(L_p-1)(L_N+2\epsilon)
 =5F_N(L_N+2\epsilon+\epsilon F_N).
\]

Both parenthesized factors are units modulo p. Consequently

\[
\boxed{v_p(L_p-1)=v_p(F_N).}
\tag{U.6}
\]

At first normalized order this becomes `2*(L_p-1)/p = 5*q_p (mod p)`. Coupling (U.6) to #7607 gives the exact valuation of its actual golden scalar defect, and twice that valuation for its norm. An arbitrary trace readout at the wrong index can lose the first obstruction; the prime-index trace retains it.

**Half-index parity split.** Set h=N/2. Since `F_N=F_h*L_h` and their gcd divides 2, exactly one factor vanishes modulo p. The discriminant `L_h^2-5F_h^2=4*(-1)^h`, together with `phi^N=epsilon (mod p)`, identifies the branch:

\[
\begin{array}{ll}
p\equiv1\pmod4:&p\mid F_h,\quad p\nmid L_h,\quad
\mathrm{WSS}(p)\iff p^2\mid F_h;\\
p\equiv3\pmod4:&p\mid L_h,\quad p\nmid F_h,\quad
\mathrm{WSS}(p)\iff p^2\mid L_h.
\end{array}
\tag{U.7}
\]

For a direct branch check, write x=phi^h in the golden algebra over F_p. It satisfies x^2=epsilon and norm(x)=(-1)^h. If its Fibonacci coordinate is zero, x is scalar and norm(x)=x^2=epsilon. If its trace is zero, its conjugate is -x and norm(x)=-x^2=-epsilon. Exactly one case occurs since p is odd. Computing the parity of `(p-epsilon)/2` gives the two residue classes in (U.7). This is a classical-style localization, not an exclusion of either infinite prime class.

Parity of a valuation only distinguishes its even and odd values. It cannot separate depth 1 from depth 3, or depth 2 from depth 4. A WSS existence proof must control actual depths across primes, or establish a genuine zero of q_p. Neither the square-class theorem nor the one-prime lifting tower supplies that missing global assertion.

### U.5. No intermediate multiple-root lift

Let p be prime and R=Z/p^2Z. Reduction rho:R->F_p has square-zero kernel: if rho(a)=rho(b)=0, then ab=0 in R.

Suppose polynomials f,g over R reduce to `(X-1)^d,(X-1)^e`, with d,e>=2. Their values and first derivatives at 1 all lie in ker(rho). The product rule therefore gives

\[
(fg)'(1)=f'(1)g(1)+f(1)g'(1)=0.
\]

But `(X^p-1)'(1)=p`, which is nonzero in R. Thus fg cannot equal X^p-1.

More explicitly, if `2<=d<=p-2` and `bar(f)=(X-1)^d`, then

\[
\boxed{f\nmid X^p-1\quad\text{in }(\mathbb Z/p^2\mathbb Z)[X].}
\tag{U.8}
\]

Otherwise reduce a cofactor g. In F_p[X], Frobenius gives `X^p-1=(X-1)^p`; cancellation forces `bar(g)=(X-1)^(p-d)`. Both exponents are at least two, giving the contradiction above.

In particular, for every p>=5, no monic quadratic reducing to `(X-1)^2` can be the proposed divisor, regardless of its lifted coefficients. The boundary is necessary: at p=3, `X^2+X+1` divides `X^3-1` and reduces to `(X-1)^2`.

Section 4.3 of Shi, Wang, Bouazzaoui, Kim and Sole, *Second order Recurrences, quadratic number fields and cyclic codes*, arXiv:2603.25343v1, proposes this multiple-root lift. The fixed coefficients a=-2,b=1 were already excluded in #7446; (U.8) rules out every coefficient choice in the specified intermediate-degree range. This is an elementary first-order obstruction to that construction. It is not a new WSS nonexistence theorem: the golden polynomial has discriminant 5 and is separable modulo p for p!=5. No claim is made that every theorem in the cited paper is false. Source: https://arxiv.org/html/2603.25343v1 .

### U.6. Prior-art and formalization boundary

The official OEIS daily mirror was read directly: `oeis/oeisdata/time.txt` reports `2026-09-13T03:00:24-04:00`; `seq/A250/A250093.seq` is version #27, September 8, 2022, blob `c195389dcc38357b4ba12a60c2c76b16df6ff5a9`. It still explicitly calls the prime-value assertion a conjecture and lists no proof.

The searches included A250093 with proof/conjecture keywords, the squarefree-Fibonacci-square-index description and the pair 3/3001, repository PR search, and global GitHub code search. The global code hit in `archmageirvine/joeis` is a sequence implementation, not a proof. No earlier proof of this exact assertion was found in that searched scope.

The recent OEIS Open frontend points to `epoch-research/LeanOpenProblems-results` at `8669ff224d86543fcc3ce192b2768ce175b734dd`. Its complete `metadata/oeis/conjectures.json` was fetched and searched for A250093, with no match. This checks that recorded corpus only. It does not exclude later unindexed work or a theorem written without the A-number. The two classical theorems used in U.3 are long-established, explicitly credited, and not counted as discoveries. Priority for this application and acceptance by OEIS remain unconfirmed.

The ordinary proof in U.3 is complete relative to its stated, published classical inputs. The full square-class classification has not been constructed in Lean in this work. In particular there is no custom axiom, claimed kernel theorem, or frozen resolution marker for A250093. Lean/Scribe companions in this line cover the separately stated local algebraic results; they do not silently promote an externally cited theorem to a Lean proof. The current work environment has no Lean/lake executable, so authored proof scripts require elaboration and kernel checking elsewhere. No CI or Scribe execution is claimed.

The next WSS obligation is to derive information about the zero set `{p : q_p=0}` that is not merely a reformulation of q_p itself. The tractable completed foundation here is square-class support transport, whose correctness is independent of unknown WSS depths. The global existence and infinitude questions remain separate open targets.
