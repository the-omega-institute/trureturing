# FIB 增益零平面与因果观测策略

本卷承接 [FIB 同父历史的采样零层坍缩与失效核心](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md) 的第 1—30 节及 《FIB 仿射增益恢复与早期动作分离》 的第 31 节。本卷续编号为第 32—36 节；未展开的早期编号依此约定。引用只是数学出处，不构成额外前提的核验。

全文是未经执行、可出错的符号数学，未取得算术执行或 Lean/kernel 认证。五项相连结果分别是一个已知时钟六零平面的充分逆、双末零平面的早期自适应逆、二次类交替 M 前缀的完整局部障碍、第六 J 后两个要求相反末动作的完整二次纤维，以及整个二次 JMJMJ 父的分类、基数与二世界续行。每项结果的证明、全部竞争者和适用边界均在正文给出。旧有限中心、矩阵、区间、导数、收缩及合法性前提保持原来的条件地位和指定极限；这里不重新认证它们，也不依赖它们建立本卷的结论。

正文公式中的 ASCII 星号仅表示乘法；系数、矩阵和多项式表达式均为文字数学，不是执行程序。全文计数单位始终是不同的整个三元组。

## 32. 已知时钟六零平面的充分恢复条件

### 32.1. 完整模型、外部承诺与充分定理

**定义 32.1（完整世界与实际采集）。** 每个世界只有一个从开始固定的整个目标

$$
W=(P,g,d),\qquad
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
0<r<1,\quad b,c>0,\quad bc=r(1-r),\qquad
0\ne g\in\mathbb R[t],\quad\deg g\le3,\quad d\in\mathbb R.
\tag{32.1}
$$

源逐项正、秩一、迹一，不要求对称，正非对角元无上界。增益可带任意符号、降次、有采样零及重根。令

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+g(i)\operatorname{tr}(Q_iP),\quad a_0=y_0=d+g(0).
\tag{32.2}
$$

初读计数，七个动作后的立即读数使用原时钟 1—7，共八次总读。一条轨迹不能重置、复制、跳读、加空动作、重编号或增加端口。可选动作的函数值只比较已固定世界；不同时取得两个互择观察。确定性策略可依实际历史停止或选动作，目标必须恢复整个 P、g、d；精确实数规则不附可计算性条件。

**定理 32.1（已知二维零平面的充分逆）。** 外部预先给定二维实多项式平面 V，次数均至多三，记 e_i 为在 i 的评价泛函。对任意基 f,h 令

$$
\Delta_{ij}=f(i)h(j)-f(j)h(i).
\tag{32.3}
$$

若 e_6 在 V 上恒零，且

$$
\Delta_{57}\Delta_{24}\Delta_{13}\Delta_{15}\Delta_{35}
\Delta_{02}\Delta_{04}\ne0,
\tag{32.4}
$$

则固定时间词 J,M,J,M,J,J,J 的八次总读，在所有严格源、所有整个非零 g 属于 V、所有 d=a_0-g(0) 的完整类上单射，并有必要且充分的完整逆。这是充分条件，不主张其必要性或最小性。

For any basis f,h, Deltaij=f(i)h(j)-f(j)h(i). Replacing the basis by an invertible two-by-two coefficient change multiplies every such determinant by the same nonzero determinant. Thus each nonvanishing requirement is basis independent. Deltaij nonzero means that the evaluation map q -> (q(i),q(j)) on the entire V is bijective. Its simultaneous kernel contains only the zero polynomial. These are sufficient assumptions; no minimality or necessity assertion is approved.

**trace identity.**

For A=[[a,u],[v,e]], tr(AP)=e+(a-e)r+v b+u c. This follows by taking the two diagonal entries of AP and collecting coefficients. In particular, the coefficient of b is the lower-left entry of A; left multiplication and source transposition must not be confused.

**complete table.**

clock: 0 ; action: initial ; Q: [[1,0],[0,1]] ; trace: 1

clock: 1 ; action: J ; Q: [[0,1],[1,0]] ; trace: j=b+c

clock: 2 ; action: M ; Q: [[1,0],[1,1]] ; trace: 1+b

clock: 3 ; action: J ; Q: [[1,1],[1,0]] ; trace: j+r

clock: 4 ; action: M ; Q: [[1,0],[2,1]] ; trace: 1+2b

clock: 5 ; action: J ; Q: [[2,1],[1,0]] ; trace: j+2r

clock: 6 ; action: J ; Q: [[1,0],[2,1]] ; trace: 1+2b

clock: 7 ; action: J ; Q: [[2,1],[1,0]] ; trace: j+2r

**independent multiplication check.**

Starting at I, J gives J; M applied to J gives [[1,0],[1,1]]; J exchanges its rows to give [[1,1],[1,0]]; M applied there gives [[1,0],[2,1]]; J gives [[2,1],[1,0]]; the last two J actions alternate these last two matrices. Applying the trace identity to each displayed matrix gives exactly the table. Consequently Q6=Q4 and Q7=Q5 as matrices, while their gains are still evaluated at 6 and 7 respectively.

**strict trace check.**

J and M are nonnegative invertible matrices. A product remains nonnegative and invertible, hence has no zero row. Pairing each of its rows with a strictly positive column of P gives a strictly positive entry of QP. Thus every actual trace is strictly positive. In the table this also follows directly from 0<r<1 and b,c>0. No assertion about the sign of the gain follows or is needed.

**clock and drift check.**

The actual read at clock 6 is always y6=d, because every gain in V vanishes there. The clock-6 action and acquisition are both required and retained. Q7=Q5 permits a repeated-source-trace identity using two distinct gain samples; it never permits replacing g(7) by g(5). Interpreting saved earlier responses after y6 reveals d is legal because all earlier actions were fixed.

### 32.2. 整个前缀与逐分支完整逆

**exact parameterization.**

Choose a basis f,h of the known V. For any actual prefix through clock k, retain every real coefficient pair (A,B) other than (0,0), with the single whole polynomial q=A f+B h, and set its single drift delta=a0-q(0). Retain every source (r,b,c) satisfying 0<r<1, b,c>0 and bc=r(1-r). Simultaneously impose yi=delta+q(i)T_i(r,b,c) for every acquired i=1,...,k, with the actual table above and with the initial equation a0=delta+q(0). Equivalently, when q(i)=0 require yi=delta; when q(i) is nonzero require T_i=(yi-delta)/q(i). At an acquired clock 6 the condition is y6=delta. Every preceding ancestor equation remains imposed.

**both directions.**

A promised compatible world has a unique basis coefficient pair and its own strict source, so it appears in this set. Conversely every retained pair and source supplies one whole nonzero degree-at-most-three gain, one constant drift, and one strict rank-one trace-one source reproducing every acquired response. Hence the set is the ENTIRE promised compatible fiber. The same source satisfies all gain and record equations; no gain coefficient is assigned its own source.

**cardinality and actions.**

This parameterization can have infinite components before the final inverse. No finite-prefix bound is assumed. The next action is the next fixed letter for the entire fiber, so action legality requires no artificial candidate-list argument. Empty fibers describe incompatible records. An optional stop is allowed only when this entire promised fiber is a singleton. The demonstrated protocol can simply acquire all eight readings.

**1. Determine the drift and the exhaustive intercept branch.**

Put d=y6, gamma=a0-d and z_i=yi-d, including z0=gamma. Since the initial trace is one, every compatible world has g(0)=gamma. Delta02 nonzero implies e0 is a nonzero functional. Therefore gamma nonzero and gamma zero are the two exhaustive branches, determined by the actual record. All later recovery must stay within that same branch and the same entire V.

**2. In the nonzero-intercept branch recover a positive repeated trace and then the entire gain.**

Fix any basis f,h and let D=Delta57, which is known nonzero. The unique coefficients expressing e0=u e5+v e7 are u=(f(0)h(7)-f(7)h(0))/D and v=(f(5)h(0)-f(0)h(5))/D: substituting either basis element verifies both equations. Thus this identity holds for every polynomial in V, with no unknown-world choice. Let T=j+2r, strictly positive. The actual table gives z5=T g(5), z7=T g(7), and hence u z5+v z7=T gamma. When gamma is nonzero, define T=(u z5+v z7)/gamma, check T>0, and only then set s5=z5/T, s7=z7/T. The unique whole gain is g=((s5 h(7)-s7 h(5))/D)f+((f(5)s7-f(7)s5)/D)h. Substitution at 5 and 7 verifies its two values; bijectivity makes this the only possible polynomial. Check its intercept gamma and nonzeroness. A true world recovers its original T and gain and passes. Either s5 or s7 may be zero; neither is divided out. They cannot both vanish for a legal nonzero gain. Neither u nor v is divided out, so their individual vanishing causes no omitted branch.

**3. In the zero-intercept branch identify its whole one-dimensional gain space and recover the scale.**

A nonzero functional on a two-dimensional space has a one-dimensional kernel. For a concrete basis-dependent representative choose h0=h(0)f-f(0)h. Since e0 is nonzero, its coefficients are not both zero; independence of f,h makes h0 nonzero. It has h0(0)=0 and h0(i)=-Delta0i. In particular h0(2) and h0(4) are nonzero by the two assumed determinants. Every compatible nonzero gain with gamma=0 is exactly eta h0 for one nonzero real eta. Set A2=z2/h0(2) and A4=z4/h0(4). The actual even traces give A2=eta(1+b), A4=eta(1+2b). Therefore eta=2 A2-A4 and eta b=A4-A2. Check eta nonzero before defining b=(A4-A2)/eta and g=eta h0. Negative eta is allowed. A true world passes and is recovered. A formal eta=0 is an incompatible record, not an excluded legal gain. The kernel direction was determined by V, rather than supplied as a hidden true-gain label. Both even physical samples are nonzero in this branch, as a consequence of the assumptions and eta nonzero.

**4. Once the gain is known, recover the off-diagonal coordinate and retain all even equations.**

For a nonzero gain, g(2) and g(4) cannot both vanish because their simultaneous evaluation kernel is zero. In the nonzero-intercept branch, if g(2) is nonzero set b=z2/g(2)-1. If g(2)=0, then g(4) is nonzero and set b=(z4/g(4)-1)/2, while retaining z2=0. If both samples are nonzero either formula gives the same b for a compatible record, and both equations must be checked. In the zero-intercept branch use the b already recovered and check these same two equations. Enforce b>0. Every division uses a now-known nonzero sample or the fixed nonzero integer two; no zero sample is canceled.

**5. Recover all remaining source coordinates using the active odd rows.**

Any two zeros among g(1),g(3),g(5) would contradict the corresponding nonzero determinant Delta13, Delta15, or Delta35. Thus at least two of these samples are nonzero. Their actual traces are j, j+r, j+2r. If g(1) and g(3) are nonzero, put t1=z1/g(1), t3=z3/g(3), r=t3-t1, j=t1. If g(1) is nonzero and g(3)=0, then g(5) is nonzero: put t1=z1/g(1), t5=z5/g(5), r=(t5-t1)/2, j=t1. If g(1)=0, then g(3),g(5) are both nonzero: put t3=z3/g(3), t5=z5/g(5), r=t5-t3, j=2t3-t5. These cases are exhaustive, and the all-active case belongs to the first. Set c=j-b and retain every unused odd equation, including z_i=0 at any zero sample. The row coefficient differences are respectively one, two, and one, always nonzero. No discriminant or diagonal-root selection is involved. Enforce 0<r<1, c>0, and bc=r(1-r). With b>0, these conditions imply a strictly positive trace-one matrix with determinant zero and hence rank exactly one.

**6. Necessity, sufficiency, and equality of the entire final fiber to a singleton.**

Require one whole nonzero g in V, the drift condition d=a0-g(0), the complete strict source conditions, and every equation y0=d+g(0), y1=d+j g(1), y2=d+(1+b)g(2), y3=d+(j+r)g(3), y4=d+(1+2b)g(4), y5=d+(j+2r)g(5), y6=d, y7=d+(j+2r)g(7). Every actual promised world follows the derivations and passes all these checks, proving necessity and nonemptiness. Conversely a passing result is itself a complete promised world and reproduces all eight acquisitions, proving sufficient membership. All competing worlds have the same d and gamma by step 1, the same entire gain by step 2 or 3, the same b by step 3 or 4, and the same r,j,c by step 5. Hence there is at most one passing world. Together with nonemptiness this closes the ENTIRE promised eight-read fiber, including every source, gain, and drift, to exactly one world.

**7. Check all signs, degrees, roots, and divisions.**

The proof uses the known nonzero determinants, nonzero gamma only in its declared branch, the recovered T only after checking its positivity, h0(2),h0(4) only after proving them nonzero, eta only after checking nonzeroness, and physical gain samples only after whole-gain recovery and an explicit nonzero branch. All other scalar denominators are fixed nonzero integers or known nonsingular linear systems. It never divides by g(6), g(0) in the zero-intercept branch, a possibly zero g(5) or g(7), a leading coefficient, a discriminant, a source determinant, or a drift difference. Zero-sample equations survive undivided. No exact degree or square-free assumption enters: polynomial evaluation and two-dimensional linear algebra include lower degrees and repeated roots automatically. Both signs of gain scale, r=1/2, both possible diagonal branches, symmetric or nonsymmetric sources, and arbitrary positive off-diagonal sizes are included. Illegal boundary sources never substitute for an interior source.

### 32.3. 一族不属于公共因子乘仿射旧类的平面

**推论 32.2（统一三次平面族）。** 对每个实数 tau≥0，平面 V_tau=(t-6)span{1,t²+tau t} 满足定理 32.1 的全部充分条件。

**plane and basis.**

For every real tau>=0, let f=t-6, h=(t-6)(t^2+tau t), and V_tau=span{f,h}. The quotient polynomials 1 and t^2+tau t are independent because the latter has leading quadratic coefficient one. Multiplication by nonzero t-6 is injective in the real polynomial ring. Thus dim V_tau=2, both basis elements vanish at 6, and the degree bound is at most three.

**determinant derivation.**

For distinct i,j, Deltaij=(i-6)(j-6)[j^2+tau j-i^2-tau i]=(i-6)(j-6)(j-i)(i+j+tau). This follows by factoring the common evaluation factors, then the difference of squares and the linear difference. It is an identity for the entire parameter family.

**all required factored values.**

**Delta57.**

-2(12+tau)

**Delta24.**

16(6+tau)

**Delta13.**

30(4+tau)

**Delta15.**

20(6+tau)

**Delta35.**

6(8+tau)

**Delta02.**

48(2+tau)

**Delta04.**

48(4+tau)

**uniform nonvanishing.**

Each displayed nonconstant factor is strictly positive for tau>=0, and each constant multiplier is nonzero. Therefore all seven required determinants are nonzero for every tau in the declared range. No finite parameter test or genericity assertion substitutes for this factor argument.

**all worlds and both intercepts.**

Every gain is g=(t-6)[A+B(t^2+tau t)] with (A,B) not both zero. Its intercept is -6A, so d=a0+6A. The entire nonzero-intercept branch A nonzero and the entire zero-intercept branch A=0,B nonzero are included, with all strict sources. For existence, f with d=a0+6 and h with d=a0 are independent legal gains for every tau,a0. For any 0<r<1 and b>0 set c=r(1-r)/b; these are actual strict trace-one rank-one sources for both gains. Taking r and 1-r retains both diagonal branches; for instance r=1/3 or 2/3, b=1,c=2/9 gives two such branches. The familiar r=1/2,b=1,c=1/4 is also an interior example. No boundary limit is needed.

**degree and root check.**

When B=0 a legal gain has A nonzero and degree one. When B is nonzero its cubic leading coefficient is B, so the degree is three. There is no degree-two nonzero member in this particular family, although the general theorem includes degree two whenever its V permits it. For tau=0 the zero-intercept gain h=t^2(t-6) has a repeated root at zero. Other permitted repeated roots are not filtered: the proof imposes neither a discriminant condition nor square-freeness.

**source relative nonredundancy proof.**

Every supplied initial-root plane has all gains zero at zero; f(0)=-6 shows V_tau is not one of them. The cubic member h shows it is not the physical affine plane. The common polynomial divisor of the whole plane is exactly t-6 up to a nonzero scalar: t-6 divides both basis elements and every common divisor divides the basis element f=t-6. If V_tau equaled H span{1,t}, its common divisor would be H up to scalar because gcd(1,t)=1. H would therefore be proportional to t-6. Canceling this nonzero polynomial would force span{1,t^2+tau t}=span{1,t}, which is impossible by the quadratic degree on the left. This excludes every alternative common-factor-times-affine presentation, rather than only one proposed H. This is source-relative distinction, without an external priority or novelty claim.

### 32.4. 例外平面的整个转置纤维及其局部末动作修复

**命题 32.3（固定词的精确例外）。** 令 G=(t-2)(t-4)(t-6)、K=t-6、V_bad=span{G,K}。对任意严格源、任意非零 lambda 和初读 a0，取 g=lambda G、d=a0+48lambda。沿本节固定词，其时钟六前缀及末 J 完整纤维恰为原源与其转置所给世界；b=c 时只有一个世界。末 M 仅在这个已完整分类的纤维内修复二元歧义。

**plane and strict worlds.**

Let G=(t-2)(t-4)(t-6), K=t-6, V_bad=span{G,K}. Different degrees make these independent, and both vanish at 6. For every lambda nonzero, every a0 and every strict P, set g=lambda G and d=a0+48 lambda. Its transpose P^T has the same diagonal r and swaps b,c, preserving positivity, trace one and determinant zero. It is a distinct source exactly when b differs from c. Both worlds use the identical entire gain and drift. The interior example r=1/2,b=1,c=1/4 proves nonemptiness.

**independent complete sample ledger.**

clock: 0 ; gain: -48 lambda ; response minus a0: 0

clock: 1 ; gain: -15 lambda ; response minus a0: 48 lambda-15 lambda j

clock: 2 ; gain: 0 ; response minus a0: 48 lambda

clock: 3 ; gain: 3 lambda ; response minus a0: 48 lambda+3 lambda(j+r)

clock: 4 ; gain: 0 ; response minus a0: 48 lambda

clock: 5 ; gain: -3 lambda ; response minus a0: 48 lambda-3 lambda(j+2r)

clock: 6 ; gain: 0 ; response minus a0: 48 lambda

clock: 7 ; gain: 15 lambda ; response minus a0: 48 lambda+15 lambda(j+2r)

**ledger proof.**

At the nonroot integers, the three factors of G give respectively -48,-15,3,-3,15 at clocks 0,1,3,5,7; at 2,4,6 one factor is zero. Combining these values with d=a0+48 lambda and the independently checked actual trace table gives every response in the ledger. All positive even clocks read d, and every odd trace depends only on j=b+c and r. Transposition preserves both coordinates, so every actual ancestor and final-J response agrees.

**entire prefix fiber necessity.**

Take any competing strict world with gain in the whole V_bad and the same actual prefix through clock 6. The common zero at 6 first forces d'=y6=d. Write its unique whole gain as a G+s K. Since y2=d and its actual trace 1+b' is strictly positive, its gain at 2 must vanish. Here G(2)=0 and K(2)=-4, so s=0. The initial equation then gives -48a=a0-d=-48 lambda, hence a=lambda. Thus its entire gain and drift are fixed, not only a set of samples. At clock 1 the known nonzero gain -15 lambda fixes j'=j. At clock 3 the known nonzero gain 3 lambda fixes j'+r'=j+r, hence r'=r. The rank-one source equation now gives b'c'=r(1-r), together with b'+c'=j. Therefore b',c' must be the two roots of X^2-jX+r(1-r)=0, whose known roots are b,c. Only their ordered placements (b,c) and (c,b) are possible.

**entire prefix fiber sufficiency and counts.**

Both placements are strict sources and satisfy every entry of the complete prefix ledger. Thus both actually occur. If b differs from c there are exactly two complete worlds in the ENTIRE prefix fiber; no third source, gain or drift exists. If b=c the repeated root gives exactly one complete world, counted once. The proof keeps all r in (0,1), including r=1/2, and both signs of lambda. It divides only nonzero fixed constants and the known nonzero odd samples after lambda nonzero has been stated.

**entire terminal fiber for final J.**

The actual final J has product Q7=Q5 and trace j+2r, so the entire already classified prefix fiber retains its common last ledger response. Imposing a last equation cannot add worlds. Hence the terminal fiber is exactly the transpose pair, or its singleton when b=c.

**actual final M and whole fiber separation.**

Keep the actual prefix through Q6=[[1,0],[2,1]]. A final M gives M Q6=[[2,1],[3,1]], whose trace at P is 1+r+3b+c and at P^T is 1+r+3c+b. Their difference is 2(b-c). The original-clock-7 gain is still 15 lambda, so the response difference is 30 lambda(b-c). It is nonzero exactly in the two-world case. Since the entire earlier fiber has been classified, this one actual final action separates all its members. The final action alone changes; none of the preceding acquired actions or responses is retroactively altered.

**evaluation boundary precision.**

Delta24=0 because G vanishes at both 2 and 4 while the other basis vector has evaluations -4,-2. This permits one nonzero gain to erase both even source measurements. Independently, this example also has Delta15=0: (-15)(-1)-(-3)(-5)=0. Therefore it is not a demonstration that Delta24 alone is necessary while all other assumptions are held. The proposal does not claim such necessity, so this is a scope clarification, not a defect. Other determinant-zero loci and all other V_bad histories remain unclassified.

### 32.5. 任意基数、停止与同一完整共同合同

**definition and monotonicity.**

L0(K,H) means at least two distinct complete worlds. L(s+1)(K,H) requires that same cardinal guard and, for each E in {J,M}, an actual response a for which the FULL slice K intersect F(H,E,a) has Ls at the extended full history. For same-history inclusion K contained in K', L0 persists by cardinality; inductively retain each old witness response and use inclusion of its child slices to preserve Ls. This proves upward monotonicity without extracting a failing pair from a nonterminal family.

**whole plane no L7 proof.**

Suppose any finite or infinite K contained in C_V(a0) had L7. Follow the fixed first action J and its actual witnessing response, obtaining a full compatible slice with L6. Next follow M and its witness within that slice, obtaining L5; then J,M,J,J,J successively give L4,L3,L2,L1,L0. All seven selections retain the same nested ancestors and the same fixed worlds. Only at terminal L0 choose two distinct complete worlds. They have identical initial reading and all seven actual responses along the fixed word, contradicting injectivity on the entire promised class. Thus every such K has no L7, irrespective of cardinality. The contradiction never assumes a finite prefix fiber.

**stopping and scope.**

Every parent and child cardinal guard remains part of the recursive construction. A successful decoder may take all eight reads; early stopping is optional only at an entire promised singleton. This excludes gains lying collectively in any one of these particular known planes from supporting unrestricted root failure. It does not authorize deleting recoverable members from a mixed failing family, combining separate plane inverses, or selecting a same-depth failing pair at a nonterminal node.

**推论 32.4（受限完整共同核上的整个守卫恒零）。** 对任意固定的全部严格来源赋值，把同一个完整共同核同时限制到每块属于上述一个 V；至少一个整个增益守卫或适用的同源终叶整个差守卫在该交空间恒零。

**exact contract and counts.**

Keep all 256 slots q=(w,epsilon), w in {J,M}^7, epsilon in {0,1}, with one strict source at every slot and four entire gain coefficients per slot. There are 254 nonempty chronological prefixes. At depth i there are 2^i prefixes, each with 2^(8-i) descendant slots; comparing all but one representative gives 2^i(2^(8-i)-1)=256-2^i rows. For i=1,...,7 the layers are exactly 254,252,248,240,224,192,128, totaling 1538 rows; the 256 four-component blocks give 1024 columns. These are symbolic count checks, not executed enumeration, arithmetic, rank, or matrix calculations.

**actual row identity.**

With initial read normalized to zero, each block x_q defines one gain g_q(t)=sum from j=0 to 3 of x_qj t^j and drift d_q=-x_q0. At a prefix v of length i, its actual response is -x_q0+t_v(P_q)g_q(i)=ell_v(P_q)x_q, with ell_v=(t_v-1,i t_v,i^2 t_v,i^3 t_v). Thus the SAME full matrix B compares every descendant to its fixed representative at each prefix while preserving every ancestor. No row, prefix, action arm, component, source legality condition, or preceding equation can be dropped.

**whole guards and deduplication.**

On ONE simultaneous vector retain every entire gain guard G_q x=x_q nonzero and every applicable same-source terminal difference guard D_w x=x_(w,0)-x_(w,1) nonzero, each a full four-component map. Different sources already distinguish terminal worlds. Repeated slots are merged only when their ENTIRE triples (P,g,d) agree, including drift; separate gain coefficients or path witnesses cannot be combined into a world.

**precise restricted space.**

For any fixed full strict source assignment P and any one V satisfying the theorem, let U_V=ker B(P) intersect {x: every whole four-coefficient block lies in V}. The asserted entire-map identity is only on this SAME intersection. It may depend on all the sources and on V.

**independent no all guard vector proof.**

If one x in U_V satisfied all whole guards, fix every slot's one complete world as above. Each gain is a nonzero member of V and its initial read is zero. All descendants at each prefix share its actual response and every preceding ancestor, by the same matrix rows. Each terminal pair is distinct by source inequality or its applicable full coefficient-difference guard, and gives L0. At an internal node, each of its two action children has its fixed descendant support within the parent's FULL actual response slice; upward monotonicity preserves the child's failure in that slice. A distinct leaf pair below that node also prevents premature stopping there. Induction from depth seven to zero constructs L7 on the fixed union of complete worlds. This contradicts the whole-plane result. Thus the same U_V has no single vector satisfying every guard simultaneously.

**independent finite avoidance proof.**

If U_V is zero, every gain map already vanishes identically. Otherwise suppose that none of the finitely many entire G_q or applicable entire D_w vanishes identically. For each map select a coordinate linear functional whose restriction to this same U_V is nonzero. In basis coordinates of U_V these are finitely many nonzero real linear polynomials. Their product is nonzero because a real polynomial ring is an integral domain. A nonzero real polynomial has a real point where it does not vanish: for zero variables it is a nonzero constant; inductively view it as a polynomial in its last variable, use the induction hypothesis to make a nonzero coefficient polynomial nonzero on the preceding coordinates, and choose the last coordinate outside the finitely many roots of the resulting nonzero univariate polynomial. At that one point all selected coordinates and hence all original entire guard maps are nonzero, contradicting the preceding paragraph. Therefore at least one entire guard map is identically zero on U_V. This argument selects coordinates only for avoidance, without weakening the full vector guards.

**special case and boundaries.**

If no terminal pair shares a source, the list contains only gain guards, so some entire G_q is identically zero on U_V. Neither case proves that any map is identically zero on the unrestricted ker B, or that the same map works for every V or every source assignment. No smaller matrix, separate arm kernel, individual guard witness, or partial coefficient constraint supplies this conclusion.

**arbitrary initial translation.**

The bijection (P,g,d) -> (P,g,d-a0) subtracts a0 from every actual response while preserving the source, whole gain, complete-target distinctions, action choices, all ancestor equalities, full compatible slices and stops. Its inverse adds a0 back to the drift. Thus the zero-initial kernel consumer and the plane theorem have the required arbitrary-initial scope. Initial zero does not imply zero drift or an initial gain root.

这些结论仅在声明的外部已知平面内成立。V_bad 同时违反 Delta24 与 Delta15；它不证明单独 Delta24 的必要性，也不分类 V_bad 的其他记录。一般已知二维平面仍未解决。初读对任意合法增益都可令 d=a0-g(0) 达到，因而不检测平面、方向、根或漂移。

## 33. 双末零平面的早期第五动作分离与完整逆

### 33.1. 整个 V67 与八读因果定理

**定理 33.1（双末零平面的因果逆）。** 设外部预先知道

$$
H(t)=(t-6)(t-7),\qquad
V_{67}=H\operatorname{span}\{1,t\},\qquad
g=H(\alpha+\beta t)\ne0,\qquad d=a_0-42\alpha.
\tag{33.1}
$$

先实际取得 J,M,J,M 的四个立即响应，之后仅由已经取得的物理读数计算

$$
\Psi=35y_4+43y_1-63y_2-15y_0,\qquad
E_5=\begin{cases}J,&\Psi=0,\\M,&\Psi\ne0.\end{cases}
\tag{33.2}
$$

实际续行 E5,J,J，在整个声明类上恢复唯一完整世界。到实际时钟六已单射，故可选在七次总读后停止；展示的完整协议保留时钟七的第八读。不主张最少读数。

**worlds.**

For every a0 in R, retain every P=[[r,b],[c,1-r]] with 0<r<1, b,c>0 and bc=r(1-r), every nonzero F(t)=alpha+beta\*t, and d=a0-42\*alpha. Set H(t)=(t-6)(t-7) and g=H\*F. There is one fixed source, one whole gain and one constant drift per world. No known gain direction, source ratio, diagonal side, symmetry, source box, gain sign or finite-prefix hypothesis is assumed.

**coefficient check.**

H=t^2-13\*t+42. The complete four-coefficient block of g is (42\*alpha,42\*beta-13\*alpha,alpha-13\*beta,beta). Since R[t] is an integral domain and H is nonzero, H\*F is nonzero exactly when F is nonzero, and H,tH are linearly independent. Thus the plane really has dimension two. Its physical degree is two when beta=0 and alpha!=0, and three when beta!=0. Constant and linear physical gains cannot have the two required distinct roots and are therefore absent by the promise, not removed from the original unrestricted domain.

**samples and nonemptiness.**

The samples H(0),...,H(7) are 42,30,20,12,6,2,0,0. Each is obtained from the displayed two factors; in particular the five normalizing samples at 1,...,5 and H(0) are nonzero. For any strict source, a0 and nonzero F, choosing d=a0-42\*alpha gives a promised world. Both signs and arbitrary real coefficients are allowed. F may have an unsampled root or a root at any sampled clock, including a repetition of a required root at 6 or 7. The initial read determines neither drift nor a promise label.

**trace law.**

For A=[[a,h],[v,e]], multiplication gives tr(AP)=e+(a-e)\*r+v\*b+h\*c. Both J=[[0,1],[1,0]] and M=[[0,1],[1,1]] are nonnegative and invertible. Their products are nonnegative, invertible and have no zero row; pairing each row with a strictly positive column of P makes each diagonal entry of QP positive. All actual traces are positive without any sign restriction on g.

**ledger.**

clock: 0 ; action: initial ; Q: [[1,0],[0,1]] ; trace: 1 ; equation: y0=d+42\*alpha=a0

clock: 1 ; action: J ; Q: [[0,1],[1,0]] ; trace: j=b+c ; equation: y1=d+30\*(alpha+beta)\*j

clock: 2 ; action: M ; Q: [[1,0],[1,1]] ; trace: 1+b ; equation: y2=d+20\*(alpha+2\*beta)\*(1+b)

clock: 3 ; action: J ; Q: [[1,1],[1,0]] ; trace: n=j+r ; equation: y3=d+12\*(alpha+3\*beta)\*n

clock: 4 ; action: M ; Q: [[1,0],[2,1]] ; trace: u=1+2\*b ; equation: y4=d+6\*(alpha+4\*beta)\*u

clock: 5 ; action: J branch ; Q: [[2,1],[1,0]] ; trace: j+2\*r ; equation: y5=d+2\*(alpha+5\*beta)\*(j+2\*r)

clock: 5 ; action: M branch ; Q: [[2,1],[3,1]] ; trace: n+u ; equation: y5=d+2\*(alpha+5\*beta)\*(n+u)

clock: 6 ; action: J after fifth J ; Q: [[1,0],[2,1]] ; trace: u ; equation: y6=d+H(6)\*F(6)\*u=d

clock: 6 ; action: J after fifth M ; Q: [[3,1],[2,1]] ; trace: 1+2\*r+2\*b+c ; equation: y6=d+H(6)\*F(6)\*(1+2\*r+2\*b+c)=d

clock: 7 ; action: J after fifth J ; Q: [[2,1],[1,0]] ; trace: j+2\*r ; equation: y7=d+H(7)\*F(7)\*(j+2\*r)=d

clock: 7 ; action: J after fifth M ; Q: [[2,1],[3,1]] ; trace: n+u ; equation: y7=d+H(7)\*F(7)\*(n+u)=d

**product proof.**

Left multiplication by J interchanges rows; left multiplication by M replaces the first row by the former second and the second by the sum. Applying these rules successively gives every matrix in the ledger from I. Applying the trace law gives its listed trace: for example [[2,1],[3,1]] gives 1+r+3\*b+c=n+u and [[3,1],[2,1]] gives 1+2\*r+2\*b+c. The last J restores the chosen fifth matrix at clock 7, retaining gain g(7). The branch table describes alternative trajectories, not additional readings.

**chronology.**

Acquire y0 and then four immediate readings for J,M,J,M. At clock 4 the statistic uses only y0,y1,y2,y4, all actually acquired; y3 is saved and remains a required equation. Select only one fifth action. Its immediate reading is followed by an immediate J reading at clock 6 and an immediate J reading at clock 7. Drift becomes available as y6, never as an input to the fifth action. There are seven actions and eight TOTAL reads at original clocks 0,...,7, on one trajectory with no reset, copy, skip, empty action, clock change or additional port. Even if sources differ, both last responses equal d because both H samples vanish.

### 33.2. 漂移取得后的全部偶数候选与根交换

**before drift.**

The entire compatible prefix is the set of all real alpha,beta,r,b,c satisfying F!=0, d=a0-42\*alpha, every strict source condition and every already acquired physical equation for ONE P,g,d. At clock 5 impose only the chosen fifth equation and its ancestral Psi rule. This is necessary by the model and sufficient because the filters construct a positive trace-one determinant-zero source and one nonzero gain reproducing that full prefix. No finiteness or enumeration of this unknown-drift set is needed by the policy.

**after drift.**

Only after acquiring y6 set d=y6, alpha=(a0-d)/42 and z_i=(y_i-d)/H(i) for i=1,...,5. If clock 7 is acquired require y7=d. Define E(t)=alpha+L\*t+A\*t^2 from E(0)=alpha,E(2)=z2,E(4)=z4. Solving the two differences gives A=(z4-2\*z2+alpha)/8 and L=(z2-alpha-4\*A)/2: z4-2\*z2+alpha=8\*A and z2-alpha=2\*L+4\*A. All normalizers are fixed nonzero constants.

**whole identity.**

Put q=b/2>0 and e=1+q\*t. The actual traces at clocks 0,2,4 equal e at those clocks. E and F\*e have degree at most two and agree at these three distinct nodes, so their difference is identically zero. Coefficient comparison gives constant alpha, L=beta+alpha\*q and A=beta\*q. This uses actual zero samples as equations and never divides by them.

**alpha zero.**

If alpha=0, nonzero F implies beta!=0. The identity gives L=beta!=0 and A=beta\*q, so q=A/L is the sole possible candidate and must be positive. A zero L is rejected before division. This branch permits g(0)=0 and d=a0 but derives it after the actual drift read.

**alpha nonzero.**

If alpha!=0, eliminate beta to obtain alpha\*q^2-L\*q+A=0 and beta=L-alpha\*q. Retain ALL different real roots q>0, count a repeated root once, and check F!=0 and all later filters. The nonzero leading coefficient gives at most two roots. Conversely a retained algebraic root and its beta satisfy beta+alpha\*q=L and beta\*q=A, so reproduce the entire E. Every true world occurs at its own q and has b=2\*q.

**degenerate even patterns.**

For beta=0 the formal roots are the actual positive q and zero; zero is rejected by b>0 and no true source is lost. For alpha=0 both L and A are nonzero on a legal world. A repeated quadratic root still yields one candidate. E cannot be identically zero because F and e are nonzero polynomials. F(2)=0 or F(4)=0 merely makes the corresponding z sample zero and remains in these equations. A vanished coefficient of E never triggers an unsupported division.

**two positive root exchange.**

If the even polynomial has different positive roots s,k, alpha is nonzero. Its sum and product give L=alpha\*(s+k), A=alpha\*s\*k. Hence beta at q=s is alpha\*k, beta at q=k is alpha\*s, and E=alpha\*(1+s\*t)\*(1+k\*t). The two complete affine factors are F_s=alpha\*(1+k\*t) and F_k=alpha\*(1+s\*t). Each 1+v\*i is positive for v>0 and i>=0, so F(1),F(3),F(5) are nonzero for BOTH candidates. This is a consequence restricted to the two-positive-root case, not an assumption on general gains.

### 33.3. 固定第五 J 的全部坏纤维

**命题 33.2（固定 J 的充要分类）。** 对固定词 JMJMJJJ，所有非单点完整纤维恰是下述 kappa 来源曲线的两个不同正参数作因子交换；不存在其他来源或增益分支。

**per candidate inverse.**

Define o(t)=j-r/2+(r/2)\*t. The actual fifth-J odd equations at i=1,3,5 are z_i=F(i)\*o(i), with source rows (1,0),(1,1),(1,2) in (j,r). Nonzero affine F has at most one distinct root; at least two rows are active. With active rows 1,3 set T1=z1/F(1), T3=z3/F(3), r=T3-T1,j=T1. With active rows 1,5 set r=(T5-T1)/2,j=T1. With active rows 3,5 set r=T5-T3,j=2\*T3-T5. In each case c=j-b. One may consistently choose the earliest two active rows. All unused equations, including the zero row, stay imposed. Every division is by a proved nonzero F sample or by 2. Each q gives at most one strict whole world, so a full fixed-J record after the drift read has at most two.

**whole odd identity.**

Interpolate O of degree at most two from (1,z1),(3,z3),(5,z5). On every compatible world the degree-at-most-two polynomial F\*o agrees at three distinct nodes, so O=F\*o identically. This remains valid with any zero sample. Since r>0, o has genuine positive slope.

**necessity of exchange family.**

Any different pair in that fiber must use different positive q roots s,k. The preceding even lemma applies. Cancel nonzero alpha in the common O identity to obtain (1+k\*t)\*o_s=(1+s\*t)\*o_k. Evaluate at t=-1/k; 1-s/k is nonzero, forcing o_k to have that root. Thus o_k=K\*(1+k\*t), and polynomial cancellation gives o_s=K\*(1+s\*t). The coefficient K is common, and o_s(1)=j_s>0 and 1+s>0 force K>0. Comparing coefficients yields r_v=2\*K\*v,j_v=K\*(1+v),b_v=2\*v,c_v=K+(K-2)\*v for v=s,k. There is no other factor allocation or same-q source freedom.

**rank and strictness.**

For either v, bc-r(1-r)=2\*v^2\*(2\*K^2+K-2). Since v>0, rank one forces 2\*K^2+K-2=0. Its sole positive root is kappa=(sqrt(17)-1)/4; the other root is negative and contradicts K>0. Equivalently kappa^2+kappa/2=1, so 0<kappa<1 and kappa-2=-2\*kappa^2. Consequently P_v=[[2\*kappa\*v,2\*v],[kappa\*(1-2\*kappa\*v),1-2\*kappa\*v]]. All entries are strictly positive exactly when 0<v<1/(2\*kappa). Trace is one and bc=2\*kappa\*v\*(1-2\*kappa\*v)=r\*(1-r), so the matrix is nonzero of rank one. The derived parameter interval is a collision classification, not a box on arbitrary sources.

**exact classification.**

For arbitrary d, alpha!=0 and different s,k in (0,1/(2\*kappa)), the worlds (P_s,H\*alpha\*(1+k\*t),d) and (P_k,H\*alpha\*(1+s\*t),d) are precisely all possible nonsingleton fixed-J final fibers. Here fixed-J refers to the counterfactual acquisition word JMJMJJJ without the adaptive rule. The initial read is d+42\*alpha. Every compatible nonempty other fiber is a singleton; incompatible records are empty. Bounds refer to distinct complete triples.

**converse and all eight equations.**

Let B(t)=(1+s\*t)\*(1+k\*t). For each constructed source e_v=1+v\*t and o_v=kappa\*e_v. The common eight-read fixed-J ledger is (d+42\*alpha, d+30\*alpha\*kappa\*B(1), d+20\*alpha\*B(2), d+12\*alpha\*kappa\*B(3), d+6\*alpha\*B(4), d+2\*alpha\*kappa\*B(5), d, d). These are exactly the physical equations at each actual original clock. Both worlds are strict and their whole gains nonzero; distinct b values distinguish targets. Both pass every equation. The per-q source uniqueness and two-root bound exclude a third world, proving the entire fiber equality and sufficiency.

**physical M separation.**

For these worlds n_s=kappa\*(1+3\*s) and n_k=kappa\*(1+3\*k). The independently checked general M gap below reduces to alpha\*(k-s)\*(1+2\*kappa) in normalized clock-5 response and therefore 2\*alpha\*(k-s)\*(1+2\*kappa) physically. It is nonzero for either sign of alpha. This is a lawful alternative fifth choice at their common clock-4 prefix. Changing an action only at 6 or 7 cannot separate the fixed-J pair, because both gain samples are zero.

### 33.4. 固定第五 M 的全部坏纤维

**命题 33.3（固定 M 的充要分类）。** 不同正偶数候选在第五 M 已分离；同候选唯一的非单点分支是 F(1)=0 的两个严格来源根。以下证明同时给必要性、充分性和全部八个物理方程。

**ordinary rows.**

For a fixed q and F, when F(1) and F(3) are active, j=z1/F(1), n=z3/F(3), r=n-j,c=j-b. Require the actual fifth-M equation z5=F(5)\*(n+u). No division by F(5) is needed, even if that sample vanishes.

**zero third sample.**

If F(3)=0 then a nonzero affine F has nonzero F(1),F(5). More explicitly beta=-alpha/3, alpha!=0, F(1)=2\*alpha/3 and F(5)=-2\*alpha/3. Recover j=z1/F(1) and n=z5/F(5)-u from the ACTUAL fifth-M row, then r=n-j,c=j-b; retain z3=0 and every other equation. This gives at most one source without inventing a fifth-J observation.

**zero first sample.**

If F(1)=0 then alpha!=0,beta=-alpha,F(3)=-2\*alpha and F(5)=-4\*alpha. Recover n=z3/F(3); the fifth equation is z5=F(5)\*(n+u), a consistency condition. With c=n-b-r, the exact rank-one equation becomes r^2-(1+b)\*r+b\*(n-b)=0. Keep every different real root with 0<r<1 and c>0 and every physical equation. The leading coefficient is one, so there are at most two sources and a repeated root is counted once. The first equation is retained as z1=0 and never inverted. F(1)=F(3)=0 is impossible, so these three source branches exhaust all cases.

**different q gap derived.**

Suppose compatible competitors share alpha,d and even data but have q=s!=k>0. The two-positive-root lemma makes their odd F samples nonzero. The common third equation gives n_s=z3/[alpha\*(1+3\*k)]>0 and n_k=z3/[alpha\*(1+3\*s)]>0. Subtracting their ACTUAL normalized fifth-M predictions gives z3\*((1+5\*k)/(1+3\*k)-(1+5\*s)/(1+3\*s))+alpha\*((1+5\*k)\*(1+4\*s)-(1+5\*s)\*(1+4\*k)). The first cross numerator is (3\*s+5\*k)-(3\*k+5\*s)=2\*(k-s); its mixed 15\*s\*k terms cancel. In the second numerator the constants and 20\*s\*k terms cancel, leaving (5\*k+4\*s)-(5\*s+4\*k)=k-s. The gap is therefore alpha\*(k-s)\*(1+2\*n_s/(1+3\*s)). Its bracket is strictly greater than one because n_s>0 and s>0. Thus it is nonzero for both signs of alpha. The physical gap is twice this value. No positivity of alpha or of the measured z3 was assumed; z3/alpha has the sign forced by the actual positive n_s.

**count and only exception.**

Different q values cannot share a fixed-M final record. Each same-q branch has at most one source except F(1)=0, where the monic quadratic has at most two. For that exception beta/alpha=-1; indeed the even polynomial factors as alpha\*(Q-q)\*(Q+1), so there is only one positive q candidate. Consequently the ENTIRE fixed-M final fiber is at most two, with a nonsingleton fiber exactly when F(1)=0 and both different source roots are strict. This excludes mixtures of an exceptional source pair and another even candidate.

**complete exception parameters.**

Write the two roots as r,r'. Their sum is 1+b. Two roots in (0,1) imply b<r<1 and b<r'<1, hence 0<b<1. Conversely choose alpha!=0,d arbitrary,0<b<1,b<r<1,r!=(1+b)/2. Put r'=1+b-r,c=r(1-r)/b,c'=r'(1-r')/b and use the same g=alpha\*H\*(1-t),d. Both sources are strict trace-one rank-one matrices. The expression n(r)=r+b+r(1-r)/b has difference n(r)-n(r')=(r-r')\*(1+(1-r-r')/b)=0. Thus both roots give the same n and exactly the same monic source quadratic; there is no third root. The midpoint is a legitimate one-world repeated-root fiber, not a collision. These conditions are necessary and sufficient for every nonsingleton fixed-M fiber.

**all eight physical equations.**

The common fixed-M record for this full family is (d+42\*alpha, d, d-20\*alpha\*(1+b), d-24\*alpha\*n, d-18\*alpha\*(1+2\*b), d-8\*alpha\*(n+1+2\*b), d, d). The gain samples at clocks 0,...,7 are alpha\*(42,0,-20,-24,-18,-8,0,0); the actual trace ledger therefore gives each equation, despite possibly different sixth matrices' traces. These checks give sufficient complete worlds as well as necessary parameters. The full inverse and quadratic degree prove that this is the whole fiber.

**repair and strict example.**

At their common prefix, fifth J has trace j+2\*r=n+r, so the physical response difference is -8\*alpha\*(r-r'), nonzero. For the explicit example b=1/5,r=2/5,c=6/5 and r'=4/5,c'=4/5, the products bc are 6/25 and 4/25, equal to the corresponding r(1-r). Both n values are 9/5, and u=7/5. The eight common fixed-M readings are (d+42\*alpha,d,d-24\*alpha,d-216\*alpha/5,d-126\*alpha/5,d-128\*alpha/5,d,d). The fifth-J traces are 11/5 and 13/5, giving d-88\*alpha/5 and d-104\*alpha/5. All entries are strict; the pair is neither a transpose pair nor an adaptive root failure. All example calculations here are symbolic, not executed. A repair after clock 5 is unavailable because g(6)=g(7)=0.

### 33.5. 在未知漂移时选动作的完整证明

两个坏类的判据只需以下对每个声明世界都成立的恒等式：

$$
\Psi=(\alpha+\beta)(1290j-1680-840b).
\tag{33.3}
$$

不能把它用作 F(1)=0 的双向检测器。下面分别证明所有 M 坏纤维使 Psi 为零、所有 J 坏纤维使其非零，然后才证明整个策略单射。

**general statistic expansion.**

Directly expanding the ACTUAL early equations yields Psi=210\*(alpha+4\*beta)\*(1+2\*b)+1290\*(alpha+beta)\*j-1260\*(alpha+2\*beta)\*(1+b)-630\*alpha. Drift cancels since 35+43-63-15=0. The alpha coefficients outside j are 210-1260-630=-1680 and 420-1260=-840 for b; the beta coefficients are 840-2520=-1680 and 1680-2520=-840 for b. Hence the additional independent identity is Psi=(alpha+beta)\*(1290\*j-1680-840\*b). It is an identity for every promised source and gain, obtained without using d in an action.

**all M collisions force zero.**

Every nonsingleton fixed-M fiber was proved to have F(1)=alpha+beta=0. The general identity immediately gives Psi=0. Equivalently, its explicit collision ledger gives drift coefficient zero, alpha constant terms -630+1260-630=0, and alpha\*b terms -1260+1260=0. These are necessary implications for the ENTIRE M obstruction class. Psi=0 is not asserted to imply F(1)=0; the other factor may vanish.

**all J collisions force nonzero.**

For every nonsingleton fixed-J fiber, j_s=kappa\*(1+s),b_s=2\*s,F_s(1)=alpha\*(1+k). Substitution in the general identity gives Psi=alpha\*(1290\*kappa-1680)\*(1+s)\*(1+k). A separate ledger check sets S=s+k,T=s\*k and expands 210\*(1+4\*S+16\*T)+1290\*kappa\*(1+S+T)-1260\*(1+2\*S+4\*T)-630. The non-kappa coefficients of 1,S,T are respectively -1680,-1680,-1680, giving the same factorization. Since 0<kappa<1, 1290\*kappa-1680<-390<0. Since alpha!=0 and s,k>0, this is nonzero over the entire strict family, including either sign of alpha.

**injectivity through clock 6.**

Take any two promised complete worlds sharing the policy's actual record through clock 6. Their common first five readings give a common Psi and fifth action. Their common y6 gives a common d, and hence alpha and all five normalized earlier responses. If Psi=0, their fifth action was J. A different pair in the complete fixed-J fiber would force Psi!=0, contradiction. If Psi!=0, the chosen action was M. A different pair in the complete fixed-M fiber would force F(1)=0 and Psi=0, contradiction. Thus they are the same entire P,g,d. This arbitrary-pair argument proves injectivity on the entire original fiber because both fixed-word classifications exhausted all candidates and all same-q source cases.

**complete inverse necessity.**

A true promised world produces d=y6 and alpha=(a0-d)/42, is in the complete positive even-root list, occurs in its active or zero odd-row source branch, and passes every strict source, whole-gain and physical equation. Thus promised compatible data always leave at least one candidate; this is not merely an at-most-one conclusion.

**complete inverse sufficiency.**

Retain only assignments with 0<r<1,b,c>0,bc=r(1-r),F!=0,g=H\*F,d=a0-42\*alpha, every actual equation in the selected branch and the recorded Psi rule. Such an assignment is itself a complete legal promised world. Deduplicate only identical triples. The injectivity just proved makes this entire retained set a singleton for compatible input; an empty set means incompatible data. The eight-read inverse additionally enforces y7=d. No algebraic candidate is returned without the unused and zero equations.

**read count and stopping.**

The chronological rule chooses fifth J at zero Psi and fifth M otherwise, using only actual history through clock 4. It never normalizes by an unknown drift or decides from a future response. Clock 6 reveals drift and already makes the full promised compatible set a singleton, authorizing an optional stop after initial plus six actions, namely seven TOTAL reads. The displayed seventh J is a real immediate eighth read and its equation y7=d is retained. No global minimality, effective algorithm or robustness follows.

### 33.6. 零样本、降次、重根、严格源与全部除法

**affine sample zeros.**

If alpha=0,beta!=0, every positive F sample used by the source inverses is nonzero. If beta=0, all F samples are the same nonzero constant. If F(1)=0, J uses rows 3,5 and the switch chooses J. If F(3)=0, J uses rows 1,5 and the M inverse uses the actual fifth-M row. If F(5)=0, both F(1),F(3) are active; J and M use those two earlier rows and keep the fifth equation zero. If F(2)=0 or F(4)=0, the zero even equation stays inside E; the odd sample inverses remain legitimate. Two different F sample zeros are impossible for nonzero affine F. Zeros at 6 or 7 repeat a required physical root and cause no normalization or source-row exception. Unsampled roots are allowed.

**repeated and lower degree cases.**

A repeated even root is one q candidate. A repeated source root is one strict source. F constant gives physical degree two; a genuine affine F gives degree three even when its root repeats 6 or 7. No square-free assumption is used. Physical degree zero or one is incompatible with the two-root plane, not excluded from the broader original problem. Neither a leading coefficient nor a discriminant is divided out.

**source completeness.**

All source reconstruction paths impose the same strict equations 0<r<1,b,c>0,bc=r(1-r). The determinant is zero and trace one excludes rank zero. There is no division by 1-2\*r or a choice of a preferred diagonal root. The case r=1/2, symmetric and asymmetric sources, both diagonal sides and arbitrarily large positive off-diagonals remain covered. The finite intervals in collision classifications are consequences of those particular pair equations. Illegal boundaries r=0,1,b=0,c=0 are not included as limiting actual worlds.

**division inventory.**

Common inversion uses only fixed 42,H(1),...,H(5),8,2. The alpha=0 branch divides by L only after L=beta!=0. J divides only the selected active F samples and an odd-row spacing 1 or 2. M divides F(1),F(3) in the ordinary case; F(1),F(5) after proving activity in the F(3)=0 case; and F(3) in the F(1)=0 case. Its source equation is monic and kept whole. The pair proofs divide alpha only after the two-root lemma or F(1)=0 makes it nonzero, use nonzero evaluation factors when s!=k, and positive 1+3\*s,1+3\*k,b,kappa only within their proved domains. Whole polynomial cancellation uses a nonzero polynomial in an integral domain. No inverse divides H(6),H(7),g(6),g(7),a possibly zero alpha,beta,F sample,Psi,drift difference,source determinant or discriminant. All normalized responses are formed only after actual y6.

### 33.7. 任意基数的无 L7 与无 L6

**推论 33.4（整个声明类的失败排除）。** 对所有初读及任意有限或无限的完整 V67 子族，既无原根 L7，也无原根 L6。前者对应八读协议；后者仅使用已证明单射的六动作前缀。

**failure recursion.**

L0(K,H) means |K|>=2 in different complete triples. L(s+1) also requires that guard and, for EACH E in {J,M}, some actual scalar a whose FULL slice K intersect F(H,E,a) has Ls at the extended history. Same-history inclusion preserves the guard; inductively preserve each witness a and inclusion of its child slice. This proves monotonicity for any cardinality while retaining both actions and all stops. It does not supply a failing pair inside an arbitrary nonterminal set.

**no L7 proof.**

If an entirely V67 K at initial a0 had L7, follow first J,M,J,M using their recursively supplied responses in full nested slices. These give depths L6,L5,L4,L3. Compute Psi at this actual clock-4 history and choose the policy's fifth action; its guaranteed witness gives L2. Next J and its witness give L1, and the last J and its witness give L0. Only at this terminal L0 choose two different complete targets. They share the entire lawful policy record, contradicting injectivity. Every response is selected within the current complete slice and every stop guard and both-action duty is retained. Seven finite response choices work equally for infinite K; no forced late history is assumed.

**scoped no L6.**

The stronger no-L6 conclusion is also justified here, because injectivity of the entire six-action policy prefix was actually proved. Starting from L6 and following those six actual history-dependent actions gives terminal L0 after clock 6; its two different targets contradict that prefix injectivity. This does not concern unrestricted L6 and claims no optimality.

**mixed boundary.**

These consumers require all whole gains to lie in the one external V67. They neither remove V67 members from mixed failure families nor invert the unknown union of promised classes. They imply neither a general known-plane theorem nor gain span at least three.

### 33.8. 同一个完整共同核的受限恒零结论

**推论 33.5（V67 交空间的整个守卫）。** 保留全部来源、全部原矩阵和全部整个守卫，在每个整个系数块同时属于 V67 的交空间上，至少一个整个守卫恒零。

**all slots and rows.**

Fix ANY strict source assignment to all 256 slots q=(w,epsilon), w a seven-action time word and epsilon in {0,1}. Keep all 254 nonempty prefixes and their actual left products A_v. At i=|v| put t_v(P)=tr(A_v\*P) and ell_v(P)=(t_v-1,i\*t_v,i^2\*t_v,i^3\*t_v). The SAME original B(P) compares each descendant slot's ell_v(P_q)\*x_q to its prefix representative's value. Each of 2^i prefixes has 2^(8-i) slots, hence 2^i\*(2^(8-i)-1)=256-2^i rows at depth i. The layers are 254,252,248,240,224,192,128, summing to 1538; 256 entire four-coefficient blocks give 1024 columns. These are unexecuted symbolic counts. No policy-only submatrix, ancestor deletion or separate block kernel is substituted.

**restriction and guards.**

U67 is ker B(P) intersect the simultaneous restriction that EVERY whole four-coefficient block belongs to V67. The block formula already checked is (42\*alpha_q,42\*beta_q-13\*alpha_q,alpha_q-13\*beta_q,beta_q), with its own coefficients per slot. Keep every entire four-component gain map G_q(x)=x_q and every applicable same-source leaf entire difference map D_w(x)=x_(w,0)-x_(w,1). There are 256 gain guards and at most 128 applicable differences. Each must be nonzero on ONE common vector to constitute a witness. Different-source leaf targets are distinct without a difference guard.

**all guard vector impossible.**

Suppose x in this same U67 satisfies all whole guards. For each slot fix its strict P_q, whole g_q(t)=sum_{h=0}^3 x_qh\*t^h and d_q=-x_q0=-42\*alpha_q. Each is a legal promised world with initial zero. Its actual response at prefix v is -x_q0+t_v(P_q)\*g_q(i)=ell_v(P_q)\*x_q. All current and ancestor rows hold on this single x, so every prefix's fixed descendant support shares that entire actual history. Each terminal leaf has two distinct complete worlds by source inequality or the full difference guard and therefore L0. For an internal node and each action, its child's fixed descendant support lies within the parent's full actual response slice; inclusion preserves the child's inductive failure there. A descendant distinct leaf pair preserves the parent's non-singleton stop guard. Bottom-up induction gives L7 for the fixed union of complete promised worlds, contrary to the decoder consumer. Only entire equal triples are merged. Thus no single all-guard vector exists on U67.

**finite avoidance to entire identity.**

If U67={0}, every G_q is already identically zero. Otherwise suppose none of these finitely many whole vector maps vanishes identically on U67. For each map choose one coordinate whose restriction to this SAME U67 is a nonzero linear functional. In basis coordinates of U67 their finite product is a nonzero real polynomial, because a polynomial ring over R is an integral domain. A nonzero real polynomial has a point where it does not vanish: induct on its number of variables, select earlier coordinates making a nonzero coefficient in the last variable nonzero, then choose the last coordinate outside the finitely many roots of that nonzero univariate polynomial. The zero-variable case is a nonzero constant. One common vector therefore makes every selected coordinate, and hence every original whole map, nonzero, contradiction. At least one ENTIRE G_q or applicable ENTIRE D_w is identically zero on U67. If no same-source leaf exists, the conclusion must be a G_q. Coordinate choices serve this existence proof only; they do not replace the contract's whole guards.

**limits and translation.**

The identity is on U67 only, may depend on the full source assignment, and gives no fixed guard identity on unrestricted ker B. No feasible unrestricted vector is supplied. For arbitrary a0 the complete-world bijection (P,g,d)->(P,g,d-a0) subtracts a0 from every actual response and preserves gain membership, distinct triples, chronological products, full nested slices, both actions and stops. Its inverse adds a0 to drift. Psi is translation invariant since its coefficients sum to zero. Normalized initial zero means d=-42\*alpha in this class, not zero drift or an initial gain root.

母卷第 29 节要求 H(0)=0 且 H(1)—H(6) 非零，本节不满足该假设；姊妹卷第 31 节的物理仿射定理也不能在未知漂移时通过除 H 安装。因为 (y_i-a0)/H(i)=F(i)tr(Q_iP)-42alpha/H(i)，最后一项未知。本节等待实际 y6 才归一化，却在此前用原物理 Psi 决定第五动作。双末根也使第五与第七评价不能提供定理 32.1 的非零 Delta57，本节完整坏类分类正承担这项缺口。

## 34. 二次交替 M 前缀的完整纤维与双末动作障碍

### 34.1. 声明域、真实矩阵与纤维定理

**定理 34.1（e3 非零分支的整个二次纤维）。** 本节将完整增益类明确限制为所有非零、次数至多二的实多项式，严格源和任意漂移仍按式 (32.1)。实际六动作是 J,M,J,M,J,M，先取得原时钟 0—6 的七次总读。令 E 是四个偶数节点的至多三次插值，R 是三个奇数节点的至多二次插值：

$$
E=e_0+e_1t+e_2t^2+e_3t^3,\quad
R=o_0+o_1t+o_2t^2,\quad S=(t-1)(t-3)(t-5).
\tag{34.1}
$$

仅在 e3≠0 分支，整个七读纤维由下述非例外逆和例外三次根列表充要描述，至多四个不同完整世界。e3=0 不在本定理分类范围。

**original and declared domains.**

The original common model is W=(P,g,d), P=[[r,b],[c,1-r]], 0<r<1, b,c>0, bc=r(1-r), one nonzero whole real gain of degree at most three, and arbitrary real constant drift compatible with the initial reading. The theorem explicitly restricts to the ENTIRE degree-at-most-two subclass. It imposes no sign, symmetry, bounded-source, exact-degree, zero-free, simple-root, known-direction or known-drift promise. The target remains the entire triple.

**acquisition.**

J=[[0,1],[1,0]], M=[[0,1],[1,1]], Q0=I, Qi=Ei Q(i-1), yi=d+g(i)tr(Qi P). Initial acquisition counts, so clocks 0,...,6 are seven TOTAL readings after six actions, and clock 7 is the eighth TOTAL reading after exactly one final action. Each separate action is immediately read and retained on one unreset, unreplicated trajectory. Counterfactual final predictions compare fixed worlds and are not observations.

**matrix derivation.**

For a preceding matrix [[A,B],[C,D]], left multiplication by J gives [[C,D],[A,B]], and by M gives [[C,D],[A+C,B+D]]. Starting at I and applying these rules to the time word JMJMJM gives every row below. Applying J or M separately to the SAME attained Q6 gives the two final rows. This retains the actual clock-6 M product; it is not the alternative J revisit from another decoder.

**trace derivation.**

The diagonal entries of AP contribute A11\*r+A12\*c and A21\*b+A22\*(1-r), so tr(AP)=A22+(A11-A22)r+A21\*b+A12\*c. Products of J and M are nonnegative and invertible because each generator has determinant -1. Thus no row of a product vanishes. Pairing any such row with a strictly positive column of P gives a strictly positive number. In particular QP is entrywise positive and every actual trace is positive, independently of the sign or zeros of g. P itself has rank one and is never inverted.

**complete products traces and equations.**

clock: 0 ; Q: [[1,0],[0,1]] ; trace: 1 ; equation: y0=d+g(0)

clock: 1 ; action: J ; Q: [[0,1],[1,0]] ; trace: j=b+c ; equation: y1=d+j\*g(1)

clock: 2 ; action: M ; Q: [[1,0],[1,1]] ; trace: 1+b ; equation: y2=d+(1+b)\*g(2)

clock: 3 ; action: J ; Q: [[1,1],[1,0]] ; trace: j+r ; equation: y3=d+(j+r)\*g(3)

clock: 4 ; action: M ; Q: [[1,0],[2,1]] ; trace: 1+2b ; equation: y4=d+(1+2b)\*g(4)

clock: 5 ; action: J ; Q: [[2,1],[1,0]] ; trace: j+2r ; equation: y5=d+(j+2r)\*g(5)

clock: 6 ; action: M ; Q: [[1,0],[3,1]] ; trace: 1+3b ; equation: y6=d+(1+3b)\*g(6)

clock: 7 ; action: choose J from Q6 ; Q: [[3,1],[1,0]] ; trace: j+3r ; equation: y7J=d+(j+3r)\*g(7)

clock: 7 ; action: choose M from Q6 ; Q: [[3,1],[4,1]] ; trace: 1+2r+4b+c ; equation: y7M=d+(1+2r+4b+c)\*g(7)

### 34.2. 整个插值、比例二次式与逐支充分逆

**A1 acquired interpolants and degree.**

**construction.**

From the actual seven readings define E of degree at most three at the four even nodes 0,2,4,6, and R of degree at most two at the three odd nodes 1,3,5. Lagrange interpolation uses only distinct fixed node differences. Write E=e0+e1\*t+e2\*t^2+e3\*t^3 and R=o0+o1\*t+o2\*t^2. Set e(t)=1+b\*t/2 and o(t)=j-r/2+r\*t/2 for a compatible world.

**proof.**

The even trace table is precisely e(i). Since deg(g)<=2, d+e\*g has degree at most three and agrees with E at four distinct even clocks. Their difference therefore vanishes identically. Moreover b/2 is nonzero and g is nonzero, so deg(e\*g)=deg(g)+1>=1; adding the constant d cannot remove its leading term. Thus deg(E)=deg(g)+1. In the branch e3!=0 EVERY compatible world in the declared class has a genuinely quadratic gain. Constants would give degree-one E and nonconstant affine gains degree-two E, so neither can be an omitted competitor. For arbitrary incompatible readings the retained list may be empty. No executed interpolation or inference about an unrestricted cubic is used.

**A2 entire strict source chart.**

**derivation.**

Let q=r/b. Strict r,b give q>0. Rank one yields c=r(1-r)/b=q(1-qb), and r=qb. Thus strict sources are exactly q>0, b>0, qb<1 with these r,c. Conversely those conditions make r,1-r,b,c positive, give trace one and bc=r(1-r), hence determinant zero and rank exactly one. q and b are uniquely recovered from P, so the chart is a bijection. Also j=q+(1-q^2)b, whence o-q\*e=j-r/2-q=b\*(1-q^2-q/2).

**exception.**

Define eta(q)=1-q^2-q/2. Its two zeros are (-1+sqrt(17))/4 and (-1-sqrt(17))/4. Exactly one is positive: alpha=(sqrt(17)-1)/4. Since 3<sqrt(17)<5, 1/2<alpha<1, and alpha^2+alpha/2=1. In particular 1-alpha>0. All positive ratios except alpha are nonexceptional. The chart covers both sides of r=1/2, both possible diagonal branches of other charts, symmetric and asymmetric sources, and unbounded positive off-diagonals.

**A3 whole odd completion.**

**proof.**

Write g=a2\*t^2+a1\*t+a0g. The even identity gives e3=b\*a2/2. The whole polynomial O=d+o\*g has cubic coefficient r\*a2/2=q\*e3 and agrees with R at 1,3,5. Their difference has those three distinct roots. The product (t-1)(t-3)=t^2-4t+3, multiplied by t-5, gives S=t^3-9t^2+23t-15. Comparing the cubic coefficient forces O-R=q\*e3\*S; a residual polynomial of degree at most two with those three roots is zero. Thus O=R+q\*e3\*S is a necessary whole identity determined from acquired data and a candidate q. It is not a separately measured odd response.

**A4 all coefficient equations and ratio roots.**

**even coefficient ledger.**

e3=b\*a2/2

e2=a2+b\*a1/2

e1=a1+b\*a0g/2

e0=d+a0g

**K derivation.**

Subtract q times E=d+e\*g from O=d+o\*g. This gives Kq=R+q\*e3\*S-q\*E=(1-q)\*d+b\*eta(q)\*g. The cubic coefficient cancels exactly. Every remaining coefficient is k2=o2-q\*(e2+9e3), k1=o1-q\*(e1-23e3), k0=o0-q\*(e0+15e3). The whole identity requires k2=b\*eta\*a2, k1=b\*eta\*a1, and k0=(1-q)\*d+b\*eta\*a0g. The constant equation is retained and is not inferred merely from a formal ratio root.

**F derivation.**

Substitute b\*a2=2e3 in k2=b\*eta\*a2. Moving all terms to one side gives o2-q\*e2-9q\*e3-2e3+2e3\*q^2+e3\*q=0, namely F(q)=2e3\*q^2-(e2+8e3)\*q+o2-2e3. Its quadratic coefficient is nonzero. Consequently there are at most two distinct real roots, and every legal ratio is one of its positive real roots. Nonreal or nonpositive roots contribute nothing. A zero discriminant yields one distinct candidate, not two worlds by multiplicity. No discriminant is divided out.

**A5 nonexceptional ratio necessity sufficiency.**

**necessary inverse.**

Fix a positive root q of F with eta!=0. From k1=b\*eta\*a1 and e2=a2+b\*a1/2=2e3/b+k1/(2eta), obtain 2e2\*eta-k1=4e3\*eta/b. Define this left side as Lq. For every compatible strict world Lq is nonzero because e3,eta are nonzero and b>0. Thus a branch with Lq=0 is impossible, and otherwise its only possible b is 4e3\*eta/Lq. Reject it unless b>0 and qb<1.

**full reconstruction.**

For a surviving b, set a2=2e3/b, a1=2(e2-a2)/b, a0g=2(e1-a1)/b, and d=e0-a0g. Set r=qb, c=q(1-qb), j=b+c. These are the descending coefficient equations of the even identity, so they fix one whole quadratic g, one drift and one source. a2 is nonzero. Require the entire identities E=d+(1+b\*t/2)\*g and R+q\*e3\*S=d+(j-r/2+r\*t/2)\*g, all seven acquired response equations, and all strict source conditions. Equivalently the still relevant constant coefficient of K is checked along with the others; no q=1 division is used.

**proof of exactness.**

Any compatible world at this q must have the forced Lq,b and all four forced gain/drift coefficients, so none is lost. Conversely a retained candidate has a strictly positive trace-one rank-one source, a nonzero exact quadratic gain and a real drift. Its even identity at 0,2,4,6 gives the four even readings. Its whole odd identity at 1,3,5 gives the three odd readings because S vanishes there. The table of actual traces makes these precisely the seven original equations. Hence every retained candidate is a complete compatible world. There is at most one world for this q. Positivity and identity filters may delete this world but cannot create another.

**singular cases.**

q=1 is in this branch, with eta=-1/2, and never requires division by 1-q. Zero k1, a1, a0g, drift, intercepts, physical samples and responses remain allowed. None is a divisor. The inverse uses no source determinant or source discriminant and does not pick a diagonal side.

**A6 exceptional ratio complete root list.**

**entry and necessity.**

For q=alpha, eta=0. Kalpha must be the constant (1-alpha)\*d, so require k2=k1=0 and force d=k0/(1-alpha). Taking alpha only when it is a root of F is consistent with k2=0; retaining both checks is harmless. H=E-d is a cubic with leading coefficient e3. A compatible world's even source factor 1+b\*t/2 has its root zeta=-2/b. Thus H(zeta)=0. Because b>0 and alpha\*b<1, this root satisfies zeta<-2alpha. Conversely that strict inequality gives a negative nonzero zeta, b=-2/zeta>0 and alpha\*b<1. No other source parameters are free.

**sufficiency.**

For each distinct real root zeta of H with zeta<-2alpha set b=-2/zeta, r=alpha\*b, c=alpha(1-alpha\*b), and g=H/(1-t/zeta). The root condition proves exact polynomial divisibility. Its divisor is a degree-one polynomial with nonzero leading coefficient and constant coefficient one, so the quotient is a nonzero exact quadratic, with leading coefficient -zeta\*e3=2e3/b. The chart makes the source strictly legal. The root normalization fixes the scale, so there is no free factor multiplier. Also o=alpha\*e. The entry conditions give R+alpha\*e3\*S=alpha\*E+(1-alpha)\*d=d+alpha\*H=d+o\*g. The even identity is E=d+H=d+e\*g. Evaluating the two identities at their acquired clocks proves ALL seven actual equations. Therefore every listed root gives a world and every compatible exceptional world was one of these roots, with its entire g and d fixed.

**multiplicities and filters.**

H is a nonzero cubic and therefore has at most three distinct real roots. A repeated root is used once as a choice of the single source factor; any leftover multiplicity remains in g. Distinct eligible roots give different b, hence different complete worlds. Roots failing zeta<-2alpha, including zeta=0 and the boundary zeta=-2alpha, give no strict source. Other roots of H can be physical sampled roots of g, and are not suppressed. Vanishing lower coefficients, zero intercepts and repeated gain roots require no new branch or division. If there is no eligible root or the entry conditions fail, the exceptional group is empty.

**A7 exhaustion and world count.**

Every compatible world has a unique positive ratio root of F. The exhaustive dichotomy is eta!=0, treated in A5, or eta=0, whose sole positive possibility alpha is treated in A6. Both directions of each reconstruction were proved, so their filtered union is exactly the entire prefix fiber. Without alpha there are at most two worlds. With alpha there are at most three worlds in that group and at most one other root of F, which contributes at most one world. Thus the bound is four. A repeated F root at alpha leaves no second ratio. No count uses unfiltered formal roots as worlds, and no finite bound is assumed generically. The count is of distinct full triples, not readings, sources alone, labels or algebraic multiplicities. The proof precludes an infinite fiber only in the stated e3!=0 branch. It does not claim the upper bound is attained.

**A8 full eighth read filter.**

For any actual choice of final action, evaluate that action's actual trace from the same reconstructed P and the same whole g at original clock 7. Filtering the complete seven-read list by this eighth equation gives exactly the full eight-read fiber: necessity is the extra actual equation and sufficiency is the established seven-read reconstruction plus that equation. A later equation cannot add a world. No simultaneous acquisition of the other action is required.

### 34.3. 最终 J 的比例分离与最终 M 的组内分离

**J separates ratios only.**

At t=7 the odd trace is o(7)=j+3r, which is exactly the actual final-J trace. S(7)=(7-1)(7-3)(7-5)=48, so y7J=R(7)+48\*q\*e3. Different q values give different responses because e3!=0. Each nonexceptional group is already at most one world. Therefore every nonsingleton final-J fiber lies entirely in the alpha group and retains that group's entire eligible-root list, of size at most three. This is a prediction from the acquired record, not an extra measurement.

**M on the entire exceptional group.**

All members of one exceptional group have the same d and H. Since e(7)=1+7b/2>0, g(7)=H(7)/(1+7b/2). At alpha, j=alpha+alpha\*b/2 and r=alpha\*b, so the J trace is alpha(1+7b/2), yielding d+alpha\*H(7). The actual M trace is 1+2alpha\*b+4b+alpha-alpha^2\*b=1+alpha+(3+5alpha/2)b after using alpha^2=1-alpha/2. Thus y7M=d+H(7)\*[1+alpha+(3+5alpha/2)b]/[1+7b/2]. Every denominator is strictly positive.

**independent difference factor.**

Put A=1+alpha, B=3+5alpha/2 and C=7/2. Cross multiplication gives (A+B\*b1)(1+C\*b2)-(A+B\*b2)(1+C\*b1)=(B-A\*C)(b1-b2). Here B-A\*C=3+5alpha/2-7/2-7alpha/2=-1/2-alpha, which is nonzero. The difference of the rational factors is consequently (-1/2-alpha)(b1-b2)/[(1+7b1/2)(1+7b2/2)]. Hence H(7)!=0 makes M injective on the WHOLE exceptional group; H(7)=0 makes every exceptional world's J and M response equal to d.

**global action boundary.**

If every ratio group is a singleton, J separates the entire prefix fiber. If the exceptional group has multiple worlds and H(7)!=0, M separates that group, but a possible additional nonexceptional world must still be compared with every exceptional M prediction before M is called injective on the union. Pairwise existence of some separating action is not one action separating an arbitrary finite union. If H(7)=0 and the exceptional group contains at least two worlds, neither final action separates the entire fiber. These statements use the complete candidate fiber before choosing an action and claim no general successful quadratic policy.

### 34.4. 一个整个七读纤维恰为二元的严格族

**定理 34.2（两个末动作都不能修复的完整二次纤维）。** 对任意 a0、任意非零 kappa 及两个不同实数 u,v>14，令

$$
\alpha=\frac{\sqrt{17}-1}{4},\quad
H(t)=\kappa(t-7)(t+u)(t+v),\quad d=a_0+7\kappa uv.
\tag{34.2}
$$

对 a∈{u,v} 取另一个参数 a_other，置

$$
b_a=2/a,\quad r_a=\alpha b_a,\quad c_a=\alpha(1-r_a),\quad
P_a=\begin{pmatrix}r_a&b_a\\c_a&1-r_a\end{pmatrix},\quad
g_a(t)=\kappa a(t-7)(t+a_{\rm other}).
\tag{34.3}
$$

沿本节 JMJMJM 的共同七读记录，在整个次数至多二的声明类中，完整纤维恰为这两个世界。实际末 J 与实际末 M 的完整响应切片都仍恰是这对。

**quantifiers and fixed worlds.**

Fix EVERY real initial reading a0, EVERY real kappa!=0, and EVERY two distinct real u,v>14. Let alpha=(sqrt(17)-1)/4, H(t)=kappa\*(t-7)\*(t+u)\*(t+v), and d=a0+7\*kappa\*u\*v. For a=u or v let a_other be the other parameter and define b_a=2/a, r_a=alpha\*b_a, c_a=alpha(1-r_a), P_a=[[r_a,b_a],[c_a,1-r_a]], and g_a(t)=kappa\*a\*(t-7)\*(t+a_other). Fix W_a=(P_a,g_a,d) and K={W_u,W_v} before any action or response choice.

**strict legality and exact degree.**

Since 1/2<alpha<1 and a>14>2alpha>0, b_a>0 and 0<r_a=2alpha/a<1. Also c_a=alpha(1-r_a)>0. The equality b_a\*c_a=alpha\*b_a\*(1-r_a)=r_a(1-r_a) proves determinant zero. Trace one makes the source nonzero, hence rank exactly one. All four source entries are strictly positive. Each whole gain has leading coefficient kappa\*a!=0, so is exact quadratic. Its values at 0 and 7 are -7\*kappa\*u\*v and zero; the chosen d therefore gives initial reading a0. At every acquired clock 0,...,6 the factors i-7 and i+a_other are both nonzero, so these particular gains have no early sampled zero. Either sign of kappa is covered.

**different targets and independent gains.**

u!=v implies 2/u!=2/v and therefore different sources and different complete targets. If the two whole gains were proportional, cancel the common nonzero polynomial t-7. The residual affine factors kappa\*u\*(t+v) and kappa\*v\*(t+u) have the same nonzero constant kappa\*u\*v, forcing proportionality factor one. Their slopes then force u=v, a contradiction. They are linearly independent, and their span is (t-7)\*span{1,t}. This is quadratic competition with distinct sources, not a known-direction reduction.

**whole prefix identities.**

For either source e_a(t)=1+t/a. The source chart at alpha gives o_a=alpha\*e_a, since j_a=alpha+r_a/2. Multiplying the SAME g_a by e_a gives kappa\*(t+a)\*(t-7)\*(t+a_other)=H. Thus e_a\*g_a=H and o_a\*g_a=alpha\*H identically. The actual even and odd traces match these e_a and o_a at their acquired clocks. All seven ancestors are therefore simultaneously realized by the same fixed pair, source and drift.

**all eight response equations.**

clock: 0 ; actual response: d+g_a(0)=a0+7\*kappa\*u\*v-7\*kappa\*u\*v=a0

clock: 1 ; action: J ; actual response: d+j_a\*g_a(1)=d+alpha\*kappa\*(1-7)\*(1+u)\*(1+v)=d+alpha\*H(1)

clock: 2 ; action: M ; actual response: d+(1+b_a)\*g_a(2)=d+kappa\*(2-7)\*(2+u)\*(2+v)=d+H(2)

clock: 3 ; action: J ; actual response: d+(j_a+r_a)\*g_a(3)=d+alpha\*kappa\*(3-7)\*(3+u)\*(3+v)=d+alpha\*H(3)

clock: 4 ; action: M ; actual response: d+(1+2b_a)\*g_a(4)=d+kappa\*(4-7)\*(4+u)\*(4+v)=d+H(4)

clock: 5 ; action: J ; actual response: d+(j_a+2r_a)\*g_a(5)=d+alpha\*kappa\*(5-7)\*(5+u)\*(5+v)=d+alpha\*H(5)

clock: 6 ; action: M ; actual response: d+(1+3b_a)\*g_a(6)=d+kappa\*(6-7)\*(6+u)\*(6+v)=d+H(6)

clock: 7 ; action: choose J OR choose M from the same Q6 ; actual response: For J the trace is j_a+3r_a=alpha\*(1+7/a)>0; for M it is 1+2r_a+4b_a+c_a=1+alpha+(6+5alpha)/a>0. In either case g_a(7)=0, so the single acquired eighth response is d. These are alternative final equations, not two observations.

**B1 all interpolant coefficients.**

The four even readings give E=d+H by interpolation uniqueness, so e3=kappa!=0. Put s=u+v-7 and p=uv-7(u+v). Expanding only as a symbolic identity, H=kappa\*[t^3+s\*t^2+p\*t-7uv]. Thus e0=d-7\*kappa\*u\*v=a0, e1=kappa\*p, e2=kappa\*s, e3=kappa. Since H-kappa\*S has degree at most two and agrees with H at the odd nodes, R=d+alpha\*(H-kappa\*S). Its coefficients are o0=d+alpha\*kappa\*(15-7uv), o1=alpha\*kappa\*(p-23), o2=alpha\*kappa\*(s+9). These are forced by the actual acquired record; they are not additional data or adjustable parameters. The degree argument already excludes all constant and affine competitors within the entire declared class.

**B2 exact factorization of every possible ratio.**

Substituting B1 into F gives kappa\*[2q^2-(s+8)q+alpha\*(s+9)-2]. Let qstar=4-alpha+s/2. Then alpha+qstar=(s+8)/2. Also 2alpha\*qstar=alpha\*(s+8)-2alpha^2=alpha\*(s+9)-2 using 2alpha^2+alpha=2. All three coefficients consequently equal those of 2\*kappa\*(q-alpha)\*(q-qstar). Since s>21 and alpha<1, qstar>1>alpha>0. These are two distinct positive roots and the only possible real ratios. Eta(qstar)!=0 because alpha is its only positive zero.

**B3 forced nonexceptional source and all signs.**

**necessary b derivation.**

Let delta=alpha-qstar, which is nonzero. The coefficients at qstar satisfy k2=delta\*kappa\*(s+9)=2\*kappa\*eta(qstar), and k1=delta\*kappa\*(p-23). Therefore Lstar=2\*kappa\*s\*eta(qstar)-delta\*kappa\*(p-23)=delta\*kappa\*[s(s+9)-p+23]. Set D=s^2+9s-p+23. Once D>0 is proved below, delta,kappa,D are nonzero and Lstar!=0. The necessary inverse is bstar=4\*kappa\*eta(qstar)/Lstar=2\*(s+9)/D. This derivation never divides by p-23 or k1, which may vanish.

**denominator proof.**

Write u=14+x and v=14+y with x,y>0. Then p=(196+14x+14y+xy)-(196+7x+7y)=7(x+y)+xy>0, and s=u+v-7>21. Independently, s^2-p=u^2+uv+v^2-7(u+v)+49=(u^2-7u)+(v^2-7v)+uv+49>0, because u,v>14. Hence D=(s^2-p)+9s+23>0, and s+9>0. In particular bstar is positive; the fatal condition is its diagonal value, not a sign choice for kappa.

**strict diagonal contradiction.**

The forced rstar=qstar\*bstar=(s+8-2alpha)\*(s+9)/D. Subtract D from its numerator: (s+8-2alpha)\*(s+9)-(s^2+9s-p+23)=(8-2alpha)\*s+49-18alpha+p. Each summand on the right is positive: s>0, 8-2alpha>0, 49-18alpha>31>0, and p>0. With D>0 this proves rstar>1. It contradicts the strict source requirement qb<1. Every world at qstar would have exactly this source value before any remaining drift or gain equation, so no other drift, root, sign or degree can evade the exclusion. All canceled quantities delta and kappa were first known nonzero.

**B4 exact exceptional group and total exhaustion.**

At q=alpha, R+alpha\*kappa\*S-alpha\*E=(1-alpha)\*d identically. In particular k2=k1=0 and the constant equation recovers precisely this same d, without assuming it known. H=E-d is exactly the fixed cubic kappa\*(t-7)\*(t+u)\*(t+v). It has three distinct real roots 7,-u,-v, because u,v are positive and distinct. The eligible roots zeta<-2alpha are exactly -u and -v: both satisfy the strict inequality since u,v>14>2alpha, while 7 is positive. The normalized factors are 1+t/u and 1+t/v, whose whole quotients are exactly g_u and g_v. A6 proves necessity and sufficiency for ALL exceptional worlds, hence gives exactly these two sources, gains and drifts. A1 excluded all lower-degree competitors, B2 exhausted all ratios, and B3 excluded the only other ratio. Therefore the ENTIRE seven-read fiber in the full degree-at-most-two class is K, not merely a subset containing a collision pair.

**B5 both terminal fibers and every served stop.**

For either final action the actual response d is shared by both elements of K because their fixed whole gains vanish at original clock 7. An eighth equation can only restrict the already exact seven-read fiber, and here restricts neither element. Thus BOTH alternative terminal fibers are still exactly K. At clock 6, |K|=2 gives the cannot-stop guard. For EACH of J,M, its actual response d has full compatible slice K, and |K|=2 gives L0 there. These are precisely the two action clauses and guard for L1(K,H6). Every earlier served history contains the same two distinct complete targets, so stopping there cannot return a unique correct target for both worlds. A deterministic policy fixing the first six actions to this prefix sees the same records, makes the same stopping/final-action decision, and ends with that same ambiguous pair. All worlds and ancestor equations were fixed together; no pair from a different parent or action arm was substituted.

**exact policy scope.**

No policy which fixes its first six actions to JMJMJM can recover all strict degree-at-most-two worlds with at most eight TOTAL reads, even if it chooses the final action or stop from the full history. More generally any policy actually following this prefix on this common record cannot recover both displayed worlds within the budget. This does not force an arbitrary adaptive policy to take the prefix. The witness is a reached-clock-6 L1, not a root L7, not a different-history L2, and not n_det(3,0)>=9.

**parameter boundaries.**

The family allows all real a0 and either sign of nonzero kappa. Its drift is d=a0+7\*kappa\*u\*v, not a0. The assumptions u,v>14 and u!=v are sufficient for this explicit family, not a classification of all obstructions or a sharp range. If u=v the two choices coincide and the claimed pair does not apply. No impossibility at u=14 or v=14 is asserted. The number 14 is used only in this family proof and is not a source-domain bound. All actual sources are strict interior sources; no limiting boundary supplies a world.

### 34.5. 全部分支和局部失败的精确范围

**entire class coverage.**

The degree-at-most-two domain initially retains constants, affine gains, genuine quadratics, all signs, repeated roots, arbitrary sampled zeros, zero gain intercepts and arbitrary compatible drifts. Only e3!=0 then forces degree exactly two. Empty and incompatible records remain possible. The source chart includes q=1, r=1/2, both diagonal-side alternatives, equal or unequal off-diagonals and their original lack of upper bounds. The proof never assumes a positive gain.

**permitted divisions in the proof.**

The chart uses b>0. Interpolation uses fixed nonzero node differences. Nonexceptional reconstruction uses declared eta!=0, necessary Lq!=0 and accepted b>0. Exceptional drift uses 1-alpha>0; its root uses eligible zeta<-2alpha<0 and an exactly verified polynomial factor. Final exceptional rational denominators are 1+7b/2>0. The explicit B3 simplification cancels only kappa!=0 and delta=alpha-qstar!=0 and uses D>0; s+9 is positive wherever its nonzero status matters. All such facts were shown before cancellation. Polynomial cancellation of t-7 in the independence proof uses a nonzero polynomial in an integral domain, not a pointwise division at its root.

**quantities never divided out.**

No physical g(i), acquired response, gain intercept, a1, source determinant, source discriminant, repeated-root discriminant, drift difference, 1-q, p-23 or k1 is divided out. Leading gain coefficients are not silently assumed nonzero: a2!=0 is derived from e3!=0 and b>0. Kappa is nonzero by the explicit family quantifier. A sampled zero remains the undivided equation yi=d. Formal roots enter the world count only after the required real, distinctness, strict-source and whole-identity checks.

**illegal boundaries and repeated roots.**

r=0, r=1, b=0 and c=0 remain excluded by the original strict model. In the exceptional chart zeta=-2alpha gives r=1 and is correctly excluded; zeta=0 is not an eligible source factor. Repeated F and H roots are counted once, and remaining gain multiplicity is retained. No square-free assumption or diagonal-branch selection is used.

**unclassified cases.**

No classification or finite-fiber assertion for e3=0 is asserted here. For e3!=0 a successful last action, if any, must be checked on the ENTIRE reconstructed list, including any extra nonexceptional world. Internal M separation of the exceptional group does not by itself settle the union. The exact family proves a uniform-prefix obstruction, not an entire quadratic lower bound.

定理 34.2 给的是实际时钟六的 L1：父有两个不同完整目标，每个末动作都有共同响应 d 的 L0 子片。它排除把前六动作统一固定为 JMJMJM 的八读二次解码器，包括任意提前停止或依历史选末动作。它不迫使一般策略选择这个前缀，不给原根 L7，也不证明所有二次策略失败。真实三次增益的必要性仍须尚未得到的整个二次恢复结果，不能从这个局部障碍推出。

## 35. 第六 J 后要求相反末动作的两个完整二次纤维

### 35.1. 整个声明类、实际重访与共同偶数逆

**world.**

W=(P,g,d), P=[[r,b],[c,1-r]], 0<r<1, b>0, c>0, bc=r(1-r), one whole nonzero real polynomial g with degree at most two, and an arbitrary real constant d. The target is the entire triple, including all gain coefficients and drift. The source need not be symmetric; positive off-diagonal entries have no imposed upper bound.

**acquisition.**

J=[[0,1],[1,0]], M=[[0,1],[1,1]], Q0=I, Qi=Ei Q(i-1), yi=d+g(i) tr(Qi P). The actual prefix is the six actions J,M,J,M,J,J. Seven readings, including the initial reading, occur at original clocks 0 through 6. Exactly one selected last action and its immediate reading occur at clock 7, for eight TOTAL readings. Every intermediate response is acquired and retained. There is one trajectory, with no reset, copy, skip, empty action, renumbering or additional port.

**history scope.**

Each theorem begins with its entire already-acquired seven-read history. Its conclusion is about the full compatible quadratic-class fiber of that history, not merely a preselected pair and not the entire fiber of the earlier five-action parent. Unchosen action responses below are functions of the same previously fixed worlds, not additional observations.

**general identity.**

For A=[[a,e],[f,h]], tr(AP)=h+(a-h)r+f b+e c. This follows directly from (AP)11=a r+e c and (AP)22=f b+h(1-r). Write j=b+c.

**prefix.**

clock: 0 ; matrix: [[1,0],[0,1]] ; trace: 1

clock: 1 ; action: J ; matrix: [[0,1],[1,0]] ; trace: j

clock: 2 ; action: M ; matrix: [[1,0],[1,1]] ; trace: 1+b

clock: 3 ; action: J ; matrix: [[1,1],[1,0]] ; trace: j+r

clock: 4 ; action: M ; matrix: [[1,0],[2,1]] ; trace: 1+2b

clock: 5 ; action: J ; matrix: [[2,1],[1,0]] ; trace: j+2r

clock: 6 ; action: J ; matrix: [[1,0],[2,1]] ; trace: 1+2b

**left multiplication check.**

Starting from I, the successive products are J, MJ, JMJ, MJMJ, JMJMJ, JJMJMJ. Multiplying J by [[1,0],[1,1]] gives [[1,1],[1,0]]; M times this gives [[1,0],[2,1]]; J times that gives [[2,1],[1,0]]; J times that gives [[1,0],[2,1]]. Thus the sixth product really revisits Q4 at original clock 6. It uses g(6), not g(4).

**mutually exclusive last products.**

clock: 7 ; selected action: J ; matrix: J Q6=[[2,1],[1,0]] ; trace: j+2r

clock: 7 ; selected action: M ; matrix: M Q6=[[2,1],[3,1]] ; trace: 1+r+3b+c=1+j+r+2b

**positivity.**

Both J and M are nonnegative with determinant -1. Every attained product, including I, is nonnegative and invertible, hence has no zero row. Pairing each such row with either strictly positive column of P gives a positive entry of QP. In particular all displayed traces are positive. This does not impose a sign on g, and the rank-one source itself is never inverted.

**all response equations.**

y0=d+g(0)

y1=d+j g(1)

y2=d+(1+b)g(2)

y3=d+(j+r)g(3)

y4=d+(1+2b)g(4)

y5=d+(j+2r)g(5)

y6=d+(1+2b)g(6)

For the single selected last J, y7=d+(j+2r)g(7). For the single selected last M, y7=d+(1+j+r+2b)g(7).

**bijection.**

Fix arbitrary a0 in R and kappa in R excluding zero. The map (P,g,d) -> (P,G,delta) with G=g/kappa and delta=(d-a0)/kappa has inverse (P,G,delta) -> (P,kappa G,a0+kappa delta). Substitution gives yi=a0+kappa zi if and only if zi=delta+G(i) tr(Qi P), at every original clock and for every attained product. Both directions preserve strict source legality, degree at most two, the whole gain being nonzero, target distinctions, all actual history constraints and stops. This is onto the ENTIRE declared class and works for either scale sign; it is not a normalization only of the displayed examples.

**initial constraint.**

For normalized z0=0 write the arbitrary whole gain as G(t)=lambda+mu t+nu t^2. The initial equation is 0=delta+lambda, so delta=-lambda. The coefficients lambda, mu and nu are otherwise initially arbitrary; zero coefficients, constant and affine gains are retained.

**derivation.**

z2=-lambda+(1+b)(lambda+2mu+4nu)=b lambda+(2+2b)mu+(4+4b)nu

z4=-lambda+(1+2b)(lambda+4mu+16nu)=2b lambda+(4+8b)mu+(16+32b)nu

z6=-lambda+(1+2b)(lambda+6mu+36nu)=2b lambda+(6+12b)mu+(36+72b)nu

**elimination.**

Define C=(z4-2z2)/4 and D=z6-z4. Direct subtraction gives D=2(1+2b)(mu+10nu) and C=b mu+(2+6b)nu. Because b>0, 1+2b>0; set L=D/[2(1+2b)]. Then mu+10nu=L and C=bL+(2-4b)nu. At b=1/2 the necessary condition is C=L/2, before dividing by 1-2b. If b differs from 1/2, nu=(C-bL)/(2-4b), mu=L-10nu, lambda=[z2-(2+2b)mu-(4+4b)nu]/b. Conversely these forced coefficients solve the three even equations, since the operations are reversible on that branch. No gain sample or degree coefficient has been inverted.

**source bound.**

Every legal source satisfies bc=r(1-r)=1/4-(r-1/2)^2<=1/4. Equality at r=1/2 remains legal. This bound follows from the actual rank-one identity and applies to every diagonal branch. It introduces no separate bound on b or c before the candidate equations are imposed.

### 35.2. A 记录的整个纤维及末 J 逆

**定理 35.1（A 记录）。** 以下量词遍及全部严格来源、所有非零次数至多二的整个增益和任意漂移；根一、根五以及 b=1/4 均由完整记录导出，不是外部承诺。

**precise statement.**

For each a0 in R and kappa!=0, the entire degree<=2 compatible fiber of (y0,...,y6)=a0+kappa\*(0,-5,-35/4,-12,-19/2,-5,5/2) under JMJMJJ is exactly {(P_A1,kappa(t-1)(t-5),a0-5kappa),(P_A2,kappa(t-1)(t-5),a0-5kappa)}, where P_A1=[[1/2,1/4],[1,1/2]] and P_A2=[[3/4,1/4],[3/4,1/4]].

**even coefficient check.**

The record gives C=(-19/2+35/2)/4=2 and D=5/2+19/2=12, hence L=6/(1+2b). At b=1/2, L=3, so C=L/2 would require 2=3/2, impossible. In the other branch put T=(1-2b)(1+2b)=1-4b^2, which is nonzero. Substituting into the even inverse gives nu=(1-b)/T and mu=[6(1-2b)-10(1-b)]/T=-2(b+2)/T. Further, mu+2nu=-2(1+2b)/T=-2/(1-2b), so the non-lambda part of z2 is -4(1+b)/(1-2b). Therefore b lambda=-35/4+4(1+b)/(1-2b), giving lambda=(86b-19)/[4b(1-2b)]. These are the proposed coefficients, derived for an arbitrary competitor.

**odd coefficients and factors.**

Over the common nonzero denominator H=4bT, the coefficient numerators of lambda, mu, nu are respectively 172b^2+48b-19, -8b^2-16b, and -4b^2+4b. Adding them with weights (1,1,1), (1,3,9), (1,5,25) gives G(1)=[160b^2+36b-19]/H=(4b-1)(40b+19)/H, G(3)=[112b^2+36b-19]/H, and G(5)=[32b^2+68b-19]/H=(4b-1)(8b+19)/H. Also lambda-5=[40b^2+66b-19]/[4b(1-2b)]=(4b-1)(10b+19)/[4b(1-2b)], and lambda-12=[96b^2+38b-19]/[4b(1-2b)]. Thus the first and fifth samples vanish precisely at b=1/4, since b>0 and 40b+19,8b+19 are positive. No root condition was imposed on competitors.

**nonexceptional odd equations.**

Assume b!=1/4. The factorizations have proved G(1),G(5) nonzero. The actual equations are jG(1)=lambda-5 and (j+2r)G(5)=lambda-5. Division on this branch forces j=N/(40b+19), j+2r=N/(8b+19), with N=(10b+19)(1+2b). Their average gives j+r=N(24b+19)/[(40b+19)(8b+19)]. Keep the third equation (j+r)G(3)=lambda-12 undivided, even when G(3) or lambda-12 might be zero. Clearing only known nonzero factors, including the common 1+2b, yields (10b+19)(24b+19)(112b^2+36b-19)=(96b^2+38b-19)(40b+19)(8b+19). This is necessary for every nonexceptional legal competitor.

**full elimination expansion.**

**left intermediate.**

(10b+19)(24b+19)=240b^2+646b+361

**right intermediate.**

(40b+19)(8b+19)=320b^2+912b+361

**left descending coefficients.**

26880

80992

59128

722

-6859

**right descending coefficients.**

30720

99712

63232

-3610

-6859

**independent coefficient account.**

The left b^3 coefficient is 8640+72352=80992; its b^2 coefficient is -4560+23256+40432=59128 and b coefficient is -12274+12996=722. The right b^3 coefficient is 12160+87552=99712; its b^2 coefficient is -6080+34656+34656=63232 and b coefficient is -17328+13718=-3610. The leading and constant coefficients are respectively 240\*112=26880 and 361\*(-19)=-6859 on the left, 320\*96=30720 and 361\*(-19)=-6859 on the right. Thus left minus right is -3840b^4-18720b^3-4104b^2+4332b=-12b(320b^3+1560b^2+342b-361). Because b>0, equality requires f_A(b)=320b^3+1560b^2+342b-361=0. All these expressions are inert, unexecuted symbolic checks.

**all positive roots and source exclusion.**

The formal derivative f_A'(b)=960b^2+3120b+342 is strictly positive on b>0; the same strict monotonicity follows by subtracting values of its positive-coefficient nonconstant terms. The endpoint substitutions give f_A(1/3)=(320+4680+3078-9747)/27=-1669/27<0 and f_A(2/5)=(512+6240+3420-9025)/25=1147/25>0. Continuity and strict monotonicity establish exactly one positive root, lying in (1/3,2/5). For any candidate at that root, its already-forced j gives c=j-b=(-20b^2+29b+19)/(40b+19). Hence c-3/4=(-80b^2-4b+19)/[4(40b+19)]. The denominator is positive, and throughout the root interval the numerator is greater than 19-80\*(2/5)^2-4\*(2/5)=23/5>0. Thus c>3/4 and b>1/3 imply bc>1/4, contradicting every legal rank-one source, including the midpoint case. All positive nonexceptional b are therefore excluded; no conclusion about r needed a hidden diagonal choice.

**retained branch and complete source count.**

At b=1/4 the forced coefficients are lambda=5, mu=-6, nu=1, delta=-5. Thus the entire gain is G_A=(t-1)(t-5), its first and fifth samples are zero, and those response equations remain the identities -5=-5. The proved nonzero G_A(3)=-4 gives j+r=(lambda+z3)/G_A(3)=7/4. Consequently c=3/2-r. Rank one gives (3/2-r)/4=r(1-r), or r^2-(5/4)r+3/8=(r-1/2)(r-3/4)=0. These are all source roots. Both lie in (0,1), and their c values are respectively 1 and 3/4. There is exactly one whole gain and drift at this b and exactly these two legal sources; all other b have been excluded.

**survivor legality.**

For P_A1, bc=1/4=(1/2)(1/2); for P_A2, bc=3/16=(3/4)(1/4). All four entries of each are positive and the trace is one. The rank-one identity gives determinant zero, and the nonzero trace makes the rank exactly one. The sources differ in r, so the targets differ. G_A=t^2-6t+5 is a fixed nonzero quadratic; scaling by either nonzero sign of kappa preserves that fact.

**full samples and response sufficiency.**

**gain samples at 0 through 7.**

(5,0,-3,-4,-3,0,5,12)

**world 1 trace prefix.**

(1,5/4,5/4,7/4,3/2,9/4,3/2)

**world 2 trace prefix.**

(1,1,5/4,7/4,3/2,5/2,3/2)

**normalized prefix equations.**

clock 0: -5+5=0

clock 1: -5+j\*0=-5 for each source

clock 2: -5+(5/4)\*(-3)=-35/4

clock 3: -5+(7/4)\*(-4)=-12

clock 4: -5+(3/2)\*(-3)=-19/2

clock 5: -5+(j+2r)\*0=-5 for each source

clock 6: -5+(3/2)\*5=5/2

**final J.**

Its two actual traces are 9/4 and 5/2; with clock-7 gain 12, the responses are -5+27=22 and -5+30=25.

**final M.**

Both actual traces are 1+j+r+2b=13/4; with the same clock-7 gain, the responses are -5+39=34 and 34.

**transport.**

Every normalized response z in these equations becomes a0+kappa z. Thus each fixed complete world satisfies every equation on either possible eight-read word, using only one actual last read. Necessity excluded every other competitor and these checks establish sufficiency, proving equality with the entire seven-read fiber.

### 35.3. B 记录的整个纤维及末 M 逆

**定理 35.2（B 记录）。** 以下完整分类仍遍及同一全部二次类；根一、根三以及 b=1/8 由记录强制。

**precise statement.**

For each a0 in R and kappa!=0, the entire degree<=2 compatible fiber of (y0,...,y6)=a0+kappa\*(0,-3,-33/8,-3,3/4,22,63/4) under JMJMJJ is exactly {(P_B1,kappa(t-1)(t-3),a0-3kappa),(P_B2,kappa(t-1)(t-3),a0-3kappa)}, where P_B1=[[1/2,1/8],[2,1/2]] and P_B2=[[3/4,1/8],[3/2,1/4]].

**even coefficient check.**

The record gives C=(3/4+33/4)/4=9/4 and D=63/4-3/4=15, so L=15/[2(1+2b)]. At b=1/2 this is 15/4; the necessary equation C=L/2 would require 9/4=15/8, impossible. For b!=1/2 use the same nonzero T=1-4b^2. The even inverse gives nu=(9-12b)/(8T), and mu=[60(1-2b)-10(9-12b)]/(8T)=-15/(4T). Now mu+2nu=-3/[2(1-2b)], so the non-lambda part of z2 is -3(1+b)/(1-2b). Thus b lambda=-33/8+3(1+b)/(1-2b), yielding lambda=9(10b-1)/[8b(1-2b)]. These are forced for every competitor, without assuming nu nonzero.

**odd coefficients and factors.**

With common nonzero denominator H=8bT, the lambda, mu, nu numerators are 180b^2+72b-9, -30b, and -12b^2+9b. The first, third and fifth sample numerators are respectively 168b^2+51b-9=3(8b-1)(7b+3), 72b^2+63b-9=9(8b-1)(b+1), and -120b^2+147b-9. Also lambda-3=[48b^2+66b-9]/[8b(1-2b)]=3(8b-1)(2b+3)/[8b(1-2b)], and lambda+22=[-352b^2+266b-9]/[8b(1-2b)]. Because b>0 and 7b+3,b+1 are positive, G(1),G(3) vanish precisely at b=1/8 in this branch.

**nonexceptional odd equations.**

Assume b!=1/8. Only now divide the proved nonzero G(1),G(3). The first and third actual equations, both with right side lambda-3, force j=N/(7b+3) and j+r=N/[3(b+1)], with N=(2b+3)(1+2b). Therefore j+2r=2(j+r)-j=N(11b+3)/[3(b+1)(7b+3)]. Keep (j+2r)G(5)=lambda+22 undivided, including any zero fifth sample or zero right side. Cancelling only known nonzero denominators gives (2b+3)(11b+3)(-120b^2+147b-9)=3(b+1)(7b+3)(-352b^2+266b-9).

**full elimination expansion.**

**left intermediate.**

(2b+3)(11b+3)=22b^2+39b+9

**right intermediate.**

3(b+1)(7b+3)=21b^2+30b+9

**left descending coefficients.**

-2640

-1446

4455

972

-81

**right descending coefficients.**

-7392

-4974

4623

2124

-81

**independent coefficient account.**

The left b^3 coefficient is 3234-4680=-1446; its b^2 coefficient is -198+5733-1080=4455, and b coefficient is -351+1323=972. The right b^3 coefficient is 5586-10560=-4974; its b^2 coefficient is -189+7980-3168=4623, and b coefficient is -270+2394=2124. Leading coefficients are 22\*(-120)=-2640 and 21\*(-352)=-7392; both constants are 9\*(-9)=-81. Left minus right is 4752b^4+3528b^3-168b^2-1152b=24b(198b^3+147b^2-7b-48). Since b>0, compatibility requires f_B(b)=198b^3+147b^2-7b-48=0. These are unexecuted symbolic expansions.

**all positive roots and source exclusion.**

For 0<b<=2/5, dropping the strictly negative -7b and bounding the positive terms by their endpoint values gives f_B(b)<198\*(2/5)^3+147\*(2/5)^2-48=(1584+2940-6000)/125=-1476/125<0. For b>=2/5 the formal derivative f_B'(b)=594b^2+294b-7 is greater than 294\*(2/5)-7=553/5>0. The endpoint values are f_B(2/5)=(-1476-350)/125=-1826/125<0 and f_B(1/2)=(99+147-14-192)/4=10>0. Continuity, the exclusion below 2/5 and strict monotonicity from 2/5 onward therefore prove exactly one positive root, in (2/5,1/2). The competitor's forced c=j-b=(-3b^2+5b+3)/(7b+3) satisfies c-5/8=(-24b^2+5b+9)/[8(7b+3)]. This denominator is positive. On the root interval its numerator is greater than -24\*(1/2)^2+9=3, since b<1/2 and 5b>0. Thus c>5/8 and b>2/5 imply bc>1/4, impossible for every legal diagonal value. This excludes every positive nonexceptional b, including those with a zero fifth sample.

**retained branch and complete source count.**

At b=1/8 the forced coefficients are lambda=3, mu=-4, nu=1, delta=-3 and the entire gain is G_B=(t-1)(t-3). The zero first and third sample equations are retained undivided. The proved nonzero fifth sample G_B(5)=8 gives j+2r=(lambda+z5)/8=25/8. Hence c=3-2r. The actual rank-one condition is (3-2r)/8=r(1-r), equivalently r^2-(5/4)r+3/8=(r-1/2)(r-3/4)=0. These are all source roots and both are legal; c is respectively 2 and 3/2. With the unique forced gain and drift this gives exactly the displayed two complete worlds, and the other branches contain none.

**survivor legality.**

P_B1 has bc=1/4=(1/2)(1/2); P_B2 has bc=3/16=(3/4)(1/4). Every entry is positive, each trace is one and each determinant zero. Nonzero trace makes the rank exactly one. The sources differ and thus the complete targets differ. G_B=t^2-4t+3 is a fixed nonzero quadratic, also after either nonzero scale sign.

**full samples and response sufficiency.**

**gain samples at 0 through 7.**

(3,0,-1,0,3,8,15,24)

**world 1 trace prefix.**

(1,17/8,9/8,21/8,5/4,25/8,5/4)

**world 2 trace prefix.**

(1,13/8,9/8,19/8,5/4,25/8,5/4)

**normalized prefix equations.**

clock 0: -3+3=0

clock 1: -3+j\*0=-3 for each source

clock 2: -3+(9/8)\*(-1)=-33/8

clock 3: -3+(j+r)\*0=-3 for each source

clock 4: -3+(5/4)\*3=3/4

clock 5: -3+(25/8)\*8=22

clock 6: -3+(5/4)\*15=63/4

**final J.**

Both actual traces are 25/8. With clock-7 gain 24, both responses are -3+75=72.

**final M.**

The actual traces 1+j+r+2b are 31/8 and 29/8; responses are -3+93=90 and -3+87=84.

**transport.**

Every normalized z becomes a0+kappa z. Thus each fixed world satisfies all acquired equations and either possible last equation with its one fixed gain and drift. These legal survivors plus the exhaustive necessity argument prove equality with the entire seven-read fiber.

### 35.4. 所有低次数、采样零、重根、来源与除法分支

**exhaustive branch tree.**

For an arbitrary competitor, normalize bijectively and use the initial equation. In both cases first split b=1/2 versus its complement; the singular branch is inconsistent, without discarding an unresolved free-gain case. In its complement the even equations uniquely determine the entire gain and drift. A then splits b=1/4 versus every other positive b; B splits b=1/8 versus every other positive b. Each nonexceptional branch must satisfy its necessary cubic, whose entire positive-root set was established and then excluded by the source product contradiction. Each exceptional branch leaves a fully solved source quadratic with exactly two distinct legal roots. Each root gives exactly one entire triple. Thus the count two is a complete-world count, not a count of source representatives, gain labels or response values.

**constant and affine competitors.**

No assumption nu!=0 or mu!=0 entered the inverse. At every nonsingular positive b, A has mu=-2(b+2)/T!=0 and B has mu=-15/(4T)!=0, so constant competitors are excluded by the acquired equations themselves. In A an affine competitor would require nu=0, hence b=1; in B it would require b=3/4. Both lie in the nonexceptional branches already exhaustively excluded by the necessary cubic and source argument. No whole zero gain could be a legal survivor; the two retained gains have nu=1. Lambda may vanish in other formal candidates without invalidating any step. Low degree was allowed before being ruled out for these particular records.

**zero samples and repeated roots.**

A's first and fifth samples vanish in the retained legal branch; B's first and third samples vanish in its retained legal branch. They were kept as actual response equations, not inverted or ignored. In the other branches A never divides G(3), and B never divides G(5), so zeros there and simultaneous zero response offsets remain covered. All other possible sampled zeros, repeated gain roots, zero lower coefficients and signed coefficients enter the same whole polynomial equations. There is no discriminant, square-free or generic-nonzero-sample premise. The retained quadratics have distinct roots, but no such restriction was imposed on competitors.

**divisions.**

The response bijection divides only the fixed nonzero kappa; its inverse is explicit for both signs.

The even derivation uses fixed nonzero rational constants and 1+2b>0. It checks b=1/2 before dividing 2-4b, uses b>0 to recover lambda, and therefore uses T only after proving T!=0.

A divides G(1),G(5) only after the positive-factor factorizations and b!=1/4 prove them nonzero. It never divides G(3) in that branch. At b=1/4 it divides only the independently evaluated nonzero G(3)=-4.

B divides G(1),G(3) only after the positive-factor factorizations and b!=1/8 prove them nonzero. It never divides G(5) in that branch. At b=1/8 it divides only the independently evaluated nonzero G(5)=8.

The further rational denominators 40b+19,8b+19,7b+3,b+1 are positive. Eliminated equalities may be multiplied by negative nonzero 1-2b without an inequality issue. Every denominator used in an inequality is explicitly positive.

The cubic reductions divide only b>0 and fixed nonzero constants. The source polynomials are factored without dividing their discriminants or 1-2r. No gain leading coefficient, nu, lambda, drift difference, sample zero, source determinant or unproved response coefficient is inverted.

**source boundaries.**

Both diagonal roots 1/2 and 3/4 are retained in each theorem. In particular the rank-one maximum at r=1/2 is legal and passed every response check; the rejected candidates violate a strict bc>1/4, so they cannot exploit equality. No symmetry, asymmetry, fixed ratio or finite source box is assumed. The strict domain excludes r=0,1,b=0,c=0; no limiting boundary matrix is used as a world. Potential additional illegal source roots would only be removed, and here the full retained quadratic has precisely the two already-checked interior roots.

**necessity and sufficiency.**

The eliminations are necessary for every entire-class competitor; the nonexceptional contradiction need not make every necessary cubic root sufficient. The retained source roots were separately checked for complete source and gain legality and every actual response, establishing survivor sufficiency. This direction distinction prevents formal roots from being mistaken for actual worlds.

### 35.5. 从已取得读数定义局部实际逆并处理停止

**A.**

Use the actual readings to set a0=y0 and kappa=(y0-y1)/5, require kappa!=0 and check the entire A pattern for clocks 0 through 6. The entire acquired fiber is then K_A by the proof above. Choose J, acquire only its clock-7 response and return (P_A1,kappa(t-1)(t-5),a0-5kappa) if y7=a0+22kappa, or (P_A2,kappa(t-1)(t-5),a0-5kappa) if y7=a0+25kappa. The responses differ by 3kappa!=0. Recheck the returned strict triple and all eight actual equations; any other last response is incompatible in this class. If instead the last action is M, its response a0+34kappa retains exactly the entire K_A, since adding an equation cannot admit a world outside the already-complete prefix fiber.

**B.**

Use a0=y0 and kappa=(y0-y1)/3, require kappa!=0 and verify every B prefix entry. The entire acquired fiber is K_B. Choose M and read once at clock 7. Return (P_B1,kappa(t-1)(t-3),a0-3kappa) at a0+90kappa, or (P_B2,kappa(t-1)(t-3),a0-3kappa) at a0+84kappa; their difference is 6kappa!=0. Verify the strict triple and all eight actual equations. An unlisted response is incompatible. The alternative actual last J at a0+72kappa retains exactly K_B.

**no hidden label.**

Both scale and translation are recovered from already-acquired data; no unknown factor, source label or unchosen response is supplied. The two pattern families cannot conflict: A requires y2-a0=(7/4)(y1-a0), whereas B requires y2-a0=(11/8)(y1-a0), with y1-a0 nonzero in each. These parent-pattern equalities are different. The local inverse is exact-real mathematics within the declared quadratic class, with no claim of an effective or finite-precision algorithm.

**stop and failure recursion.**

Before the last read, each served acquired ancestor contains both fixed distinct worlds, hence cannot identify a unique complete target in the declared class. At clock 6 each entire fiber has L0 because it has two targets, but has NOT L1: A's J response slices are singletons and B's M response slices are singletons, so one required action existential in L1 fails. The separating last action permits a singleton return. The nonseparating last action leaves two targets and prevents a successful terminal stop. No earlier-parent L2 follows from either result.

### 35.6. 固定词失败、不同父与尚缺的统一策略桥梁

**fixed word consequences.**

JMJMJJM fails as an entire-quadratic decoder: A supplies two different legal complete worlds sharing all eight actual readings of that word. JMJMJJJ also fails: B supplies such a pair for that word. A deterministic rule stopping earlier along either colliding record returns the same output for two possible complete targets, so an earlier stop cannot repair that fixed word. These examples embed in the cubic class as lower-degree worlds but give no adaptive cubic lower bound.

**smallest local repairs.**

For the already-acquired A history, take final J and use its complete inverse above. For the already-acquired B history, take final M and use its complete inverse above. These repairs require exactly one selected last read and are justified for the full local fibers. A fixed replacement of the inherited affine word's last action cannot serve both families.

**remaining uniform bridge.**

A uniform repair after the entire five-action parent JMJMJ requires a description or other adequate proof for every possible compatible parent history and ALL constant, affine, genuine-quadratic, zero-sample, singular and potentially infinite branches. Its selected sixth action must work for EVERY actual sixth response: each resulting whole slice must either already be a singleton or admit ONE last action injective on that entire slice. An earlier choice between sixth J and M must depend only on the already-acquired parent record. This proof treats two actual sixth-J response slices and does not cover the other slices of either parent, much less all parents. It cannot choose a favorable future response.

**different histories.**

The A and B worlds share different five-action parent records, even allowing their respective nonzero response scales. Their union is not a compatible same-parent witness and cannot establish L2 by assembling their action-specific properties. Each local whole fiber actually has a separating last action. Pairwise separability in other larger fibers would also need an action that works on the entire slice, not merely a separately chosen action for each pair.

A 的末 J 与 B 的末 M 各在其整个实际切片上单射；其局部父是 L0 而不是 L1。第 34 节的实际六 M 子片与本节六 J 子片不同；本节的 A、B 也属于不同五动作父记录。因此不能把任意这些局部对象拼成同一个父的 L2，亦不能把“每对各有某个分离动作”替代“一个动作在整个切片单射”。

### 35.7. 复用、原目标与共同实现的未决边界

母卷第 27 节处理外部已知整条增益线，第 29 节处理声明的含初根公共因子平面，姊妹卷第 31 节处理整个物理仿射平面。已知标签下各自可恢复，不推出其未知并集可恢复。第 32—33 节处理两个明确的已知零平面；第 34—35 节则在整个未知二次类内穷尽各自声明记录的竞争者。例中比例来源曲线与插值、因式、秩一代数均是复用工具，不另计通用方法。

本卷新增连接只使用同一世界的源、整个增益、漂移和全部祖先方程。各充分逆的非空性来自真实合法世界必通过；至多一个结论来自全部竞争者的穷尽；反向通过全部过滤者确为该记录的合法完整世界。一个后续方程只能删世界，不能增加世界。所有局部计数均须按完整三元组去重，不按源投影、增益标签、形式根的重数或读数计数。

**entire quadratic question.**

OPEN: a legal adaptive original-root strategy recovering ALL strict nonzero degree-at-most-two worlds with arbitrary compatible constant drift in at most eight TOTAL original-clock readings, or a jointly realized original-root L7 for that class. The present exact fiber removes one natural six-action prefix from uniform use and locates its quadratic last-step failure. It supplies neither a complete quadratic decoder nor a quadratic original-root failure tree.

**original cubic question.**

OPEN: deterministic adaptive recovery of ALL original strict degree-at-most-three worlds in eight TOTAL readings at clocks 0,...,7, versus n_det(3,0)>=9. There is no root L7 witness, nine-read upper bound, missing-arm completion, unrestricted same-parent L3, forced late-history reachability or full-domain decoder here.

**no promise detector or unknown union inverse.**

The degree identity E=d+e\*g relies on the declared deg(g)<=2 class: its product then has degree at most three and four even nodes determine it. For an unrestricted cubic the product can have degree four, so agreement at those four nodes does not prove that whole identity. Thus e3!=0 does not detect the quadratic promise inside the original cubic model. Separately recoverable classes cannot be united without controlling cross-class competitors. No unknown-direction or unknown-plane detector, mixed-family deletion rule or recovered unknown union follows.

**no true cubic necessity.**

A claim that every unrestricted failure must contain a TRUE cubic gain would need the still missing entire quadratic recovery theorem. The current exact quadratic local obstruction supplies no such necessity. The candidate's already inherited affine result gives only its previously stated degree-at-least-two boundary.

**unchanged full joint contract.**

The original contract remains ALL 256 slots q=(w,epsilon), ALL 254 nonempty action prefixes, the SAME full 1538-by-1024 matrix B(P), and ONE common stacked four-coefficient vector satisfying ALL whole four-component gain guards and all applicable same-source terminal difference guards. Layer row counts remain 254,252,248,240,224,192,128. Every source is strict, every ancestor response and both actions are jointly realized, and every stop retains its guard. Repeated slots identify only entire equal triples. Any quadratic restriction must be imposed simultaneously in every block of that same contract. The local two-world path fiber is neither a solution of this joint contract nor a substitute for it; separate paths, source marginals, smaller matrices or separately chosen guard vectors do not establish it.

**support and failure limits.**

No support floor of five, all-four exclusion, original-root four-world existence, sharp support bound, gain span at least three, unrestricted failure-subfamily extraction, mixed deletion, missing-arm repair or arbitrary-policy forced-prefix result is obtained. A local L1 at the attained Q6 is not a root L7. Unknown unions and general two-dimensional gain spaces remain outside any inherited special-plane inverse.

**initial read and other limits.**

Arbitrary initial reading is retained. The usual full-world normalization only replaces d by d-a0 and subtracts a0 from all actual responses, restoring d on return; it does not make gain, drift or a root known. The results are exact-real set-theoretic reconstructions with no computability, finite-precision, noise, continuity, stability, efficiency, resource, empirical-physics, neural-network, literature-exhaustiveness or priority guarantee. There is no Lean/kernel certification.

**quadratic question.**

Entire-quadratic deterministic recovery within eight TOTAL original-clock readings remains OPEN on this evidence. There is no uniform sixth-J repair, full quadratic all-branches inverse, quadratic original-root L7 or arbitrary-cardinality no-quadratic-L7 proof here. A history-dependent last choice can choose J on A and M on B, but success on all other acquired histories has not been proved or disproved.

**cubic question.**

The original question for ALL nonzero whole real gains of degree<=3, all strict rank-one trace-one sources and arbitrary drift remains OPEN: a deterministic adaptive complete-target inverse using at most eight TOTAL readings at clocks 0 through 7 versus n_det(3,0)>=9. There is no original-root L7, nine-read upper bound, missing-arm realization, unrestricted same-parent L3, forced late-history reachability or settlement of either side. The inherited affine result gives only the existing necessity of a gain of degree at least two in an unrestricted failure family; it does not establish true-cubic necessity.

**unchanged full joint contract.**

All 256 slots q=(w,epsilon), w in {J,M}^7 and epsilon in {0,1}, retain strict sources. All 254 nonempty action prefixes v retain actual left products A_v, lengths i=|v| and descendants D_v. With t_v(P)=tr(A_v P), ell_v(P)=(t_v(P)-1,i t_v(P),i^2 t_v(P),i^3 t_v(P)), the SAME full 1538-by-1024 matrix has rows ell_v(P_q)x_q-ell_v(P_qv)x_qv for q in D_v excluding its representative qv. Layer row counts remain 254,252,248,240,224,192,128. ONE vector in that same common kernel must simultaneously satisfy every whole four-component gain guard G_q x=x_q!=0 and each applicable same-source terminal whole four-component difference guard D_w x=x_(w,0)-x_(w,1)!=0. Entire gains are g_q(t)=sum from j=0 to 3 of x_qj t^j and drifts d_q=a0-x_q0; unequal terminal sources already distinguish complete targets. Every ancestor, both action obligations and every stop guard remain. Any degree<=2 restriction would have to apply simultaneously to every block of this same contract. No new common realization is supplied, and neither local pair substitutes for it. Slots may be identified only when their entire triples agree.

**excluded inferences.**

No deletion from mixed failure families, recovery by union of separately recoverable classes, detector for an unknown gain/root/direction promise in the cubic model, arbitrary nonterminal failure-subfamily extraction, all-four-world exclusion, four-world original-root witness, support floor five or sharpness, separate source/drift marginal claim, gain span at least three, new unrestricted kernel obstruction or true-cubic necessity is established. No neural-network, empirical, noise, continuity, stability, efficiency, resource, computability, finite-precision, external-priority or Lean/kernel claim is made. Support and fiber counts are numbers of different complete worlds, not numbers of readings.

本卷第 32 与第 33 节的整个守卫恒零结论只在各自同一个完整共同核的声明平面交空间成立，恒零身份可随平面和全部来源改变。它们没有替换不受限共同核，没有给出其可行点或恒零守卫；第 34—35 节的局部二次纤维也不替代原树的联合实现。

原目标仍是：对所有严格源、任意非零次数至多三的整个实增益和任意兼容常漂移，是否存在原时钟 0—7、至多八次总读的确定性自适应完整逆，或是否 n_det(3,0)≥9。两支均 OPEN。整个二次类的自适应八读恢复或原根 L7 也 OPEN。仍无九读上界、混合族删除、未知承诺检测器、可恢复未知并集、增益跨度至少三、支持下界五、全部四世界排除、四世界原根存在性或尖锐性、原根失败树、缺失动作臂、不受限同父 L3 或强迫晚期历史。

外部文献未经检索，本卷不作穷尽、原创性或优先权主张。所有陈述均限精确实数的符号数学；没有一般神经网络、经验物理、噪声、连续性、稳定性、效率、可计算性、资源或有限精度保证，也没有算术执行或 kernel 认证。严格零边界源不以极限代替合法世界。

## 36. 整个二次 JMJMJ 父的分类、基数与二世界续行

### 36.1. 完整声明域与实际两读接口

本节补齐第 35.6—35.7 节所指的五动作父全分支分类缺口：覆盖任意已取得记录的全部常数、仿射、真正二次、零样本、奇异及无限分支。较大父上统一选择第六动作的缺口仍为 OPEN。分类与局部续行不等于原根二次策略，也不改变原始三次二择的未决地位。以下全部为未经执行、可出错的符号数学，没有算术执行或 Lean/kernel 认证。

**定理 36.1（整个父的精确分类与有限或连续统二分）。** 对任意实数记录 $y_0,\ldots,y_5$，在实际五动作 $J,M,J,M,J$ 后，所有严格来源、任意常漂移和所有非零次数至多二的整个实增益所给完整兼容父，恰为下述三个真正二次分支与整个继承仿射分支的不交并。每个所列合法参数固定唯一完整世界。父可为空；若有限，至多有 $22$ 个不同完整世界；若无限，基数恰为连续统。界为粗上界，不主张达到或尖锐性，也不主张通用恒等退化具有非空合法实例。

完整世界及目标始终是

$$
W=(P,g,d),\qquad P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
0<r<1,\quad b,c>0,\quad bc=r(1-r),
\qquad g(t)=\lambda+\mu t+\nu t^2\ne0,\quad d\in\mathbb R.
\tag{36.1}
$$

不要求对称、固定对角侧、增益为正、无根、无采样零、恰好二次、已知增益方向或已知漂移；正非对角元无上界。每个世界只有一个固定源、一个整个增益及一个漂移，不能按动作重配。

令 $J=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$、$M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$，$Q_0=I,Q_i=E_iQ_{i-1}$，$y_i=d+g(i)\operatorname{tr}(Q_iP)$。设 $a_0=y_0$、$x_i=y_i-a_0$；初读给 $d=a_0-\lambda$，故 $x_i=-\lambda+g(i)\operatorname{tr}(Q_iP)$。这是把漂移减去 $a_0$ 的整个世界双射，逆向加回 $a_0$；不把物理漂移置零，也不检测初根。

对 $A=\left(\begin{smallmatrix}a&h\\v&e\end{smallmatrix}\right)$，直接取 $AP$ 的两个对角元得

$$
\operatorname{tr}(AP)=ar+hc+vb+e(1-r)=e+(a-e)r+vb+hc.
\tag{36.2}
$$

左乘 $J$ 交换两行；左乘 $M$ 以旧第二行为第一行、旧两行之和为第二行。从 $I$ 出发给出全部已取得和互择未来乘积；记 $j=b+c$。

| 原时钟与实际动作 | $Q$ | 迹 | 读数函数 |
| --- | --- | --- | --- |
| $0$ 初读 | $\left(\begin{smallmatrix}1&0\\0&1\end{smallmatrix}\right)$ | $1$ | $y_0=d+g(0)$ |
| $1,J$ | $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ | $j$ | $y_1=d+jg(1)$ |
| $2,M$ | $\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ | $1+b$ | $y_2=d+(1+b)g(2)$ |
| $3,J$ | $\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ | $j+r$ | $y_3=d+(j+r)g(3)$ |
| $4,M$ | $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ | $1+2b$ | $y_4=d+(1+2b)g(4)$ |
| $5,J$ | $\left(\begin{smallmatrix}2&1\\1&0\end{smallmatrix}\right)$ | $j+2r$ | $y_5=d+(j+2r)g(5)$ |
| $6,J$，$n=2$ | $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ | $1+2b$ | $h_2=d+(1+2b)g(6)$ |
| $6,M$，$n=3$ | $\left(\begin{smallmatrix}1&0\\3&1\end{smallmatrix}\right)$ | $1+3b$ | $h_3=d+(1+3b)g(6)$ |
| $7,J$，在已选 $n$ 后 | $\left(\begin{smallmatrix}n&1\\1&0\end{smallmatrix}\right)$ | $j+nr$ | $f_{nJ}=d+(j+nr)g(7)$ |
| $7,M$，在已选 $n$ 后 | $\left(\begin{smallmatrix}n&1\\n+1&1\end{smallmatrix}\right)$ | $1+nb+j+(n-1)r$ | $f_{nM}=d+(1+nb+j+(n-1)r)g(7)$ |

这些表项可逐行用上述两条左乘规则及式 (36.2) 得到。例如 $Q_5=\left(\begin{smallmatrix}2&1\\1&0\end{smallmatrix}\right)$ 左乘 $J,M$ 分别给第六两行；在 $\left(\begin{smallmatrix}1&0\\n&1\end{smallmatrix}\right)$ 上再左乘，恰给末两行。因此统一记

$$
h_n=d+(1+nb)g(6),\qquad
f_{nJ}=d+(j+nr)g(7),\qquad
f_{nM}=d+(1+nb+j+(n-1)r)g(7),\quad n\in\{2,3\}.
\tag{36.3}
$$

末 $M$ 减末 $J$ 为 $(1-r+nb)g(7)$。$n$ 只表示第六动作，不改变时钟。两第六函数都在原时钟六；四个末函数都在原时钟七。重访 $Q_4$ 或 $Q_5$ 不把 $g(6)$ 或 $g(7)$ 换成旧样本。

$J,M$ 非负且可逆，其乘积非负、可逆、无零行。非零非负行与 $P$ 的严格正列配对为正，所以所有实际迹为正，不要求增益为正。$\det P=0$、迹一使来源非零且秩恰一；不求逆 $P$。

五动作父已经取得含初读的六次 TOTAL 读数，只余时钟六、七两次。每个选定动作立即采集并保留读数；互择表只是比较相同固定世界的函数，不额外采集另一臂。全程一条轨迹，无重置、复制、跳读、空动作、重编号或增加端口。

### 36.2. 已取得的插值与整个严格来源坐标

从实际记录唯一插值得

$$
E(t)=Lt+At^2,\qquad R(t)=Dt^2+Bt+C,
\tag{36.4}
$$

其中 $E$ 过 $(0,0),(2,x_2),(4,x_4)$，$R$ 过 $(1,x_1),(3,x_3),(5,x_5)$。全部系数为

$$
A=\frac{x_4-2x_2}{8},\quad L=\frac{4x_2-x_4}{4},\quad
D=\frac{x_5-2x_3+x_1}{8},\quad
B=\frac{x_3-x_1-8D}{2},\quad C=x_1-B-D.
\tag{36.5}
$$

证明：偶数两式为 $2L+4A=x_2,4L+16A=x_4$，相减给 $8A=x_4-2x_2$，回代给 $L$。奇数二阶差给 $8D=x_5-2x_3+x_1$，第一差给 $x_3-x_1=8D+2B$，第一值给 $C$。至多二次差式在三个不同节点为零即恒零，故插值唯一。只除固定非零节点差，零读数均保留。

所有严格来源有且仅有坐标

$$
q=\frac rb>0,\quad s=\frac2b>2q,\qquad
b=\frac2s,\quad r=\frac{2q}s,\quad
c=q\left(1-\frac{2q}s\right),\quad
j=q+\frac{2(1-q^2)}s.
\tag{36.6}
$$

必要性：$s-2q=2(1-r)/b>0$，秩一等式给 $c=r(1-r)/b$，代入得各式。反向 $q>0,s>2q$ 给 $s>0,b>0,0<r<1,c>0$，且 $bc=(2q/s)(1-2q/s)=r(1-r)$。逆坐标唯一，故是整个严格源的双射，未遗漏任何对角侧、对称性或非对角大小。

设

$$
\eta(q)=1-q^2-q/2,\qquad H(q)=2\eta(q)+3q=2+2q-2q^2,
\qquad e(t)=1+t/s,\qquad o(t)=q e(t)+2\eta/s.
\tag{36.7}
$$

由式 (36.6)，$o=j-r/2+(r/2)t$，故 $e$ 在已用偶节点、$o$ 在已用奇节点恰给实际迹。这是迹多项式的代数表示，不是把已取得动作外推到未取得时钟。

$\eta=0$ 的两个根为 $(-1\pm\sqrt{17})/4$，唯一正根

$$
\alpha=\frac{\sqrt{17}-1}{4},\quad 1/2<\alpha<1.
\qquad
H=0\text{ 的唯一正根为 }\phi=\frac{1+\sqrt5}{2}>1.
\tag{36.8}
$$

因为 $3<\sqrt{17}<5$ 得到 $\alpha$ 的界；$H$ 的另一根 $(1-\sqrt5)/2<0$。两正例外不同；$q=\alpha$ 时 $H=3q>0$，$q=\phi$ 时 $\eta=-3q/2\ne0$。这里没有把未知比例当成外部标签。

### 36.3. 真正二次的全部系数账与双向准入

先在 $\nu\ne0$ 支设 $T=\nu/s\ne0$，并记

$$
U_{\rm e}(t)=t(t-2)(t-4)=t^3-6t^2+8t,\qquad
S_{\rm o}(t)=(t-1)(t-3)(t-5)=t^3-9t^2+23t-15.
\tag{36.9}
$$

$-\lambda+eg-E$ 在 $0,2,4$ 为零且三次系数为 $T$；减去 $TU_{\rm e}$ 后，至多二次余式有三个不同根，故恒零。同理奇数余式的三次系数为 $qT$，得到两个整个恒等式

$$
-\lambda+eg=E+TU_{\rm e},\qquad
-\lambda+og=R+qTS_{\rm o}.
\tag{36.10}
$$

偶数式按常数至三次的系数账为

$$
(0,\ \mu+\lambda/s,\ \nu+\mu/s,\ \nu/s)
=(0,\ L+8T,\ A-6T,\ T).
\tag{36.11}
$$

从高次向下唯一逆为

$$
\nu=Ts,\qquad
\mu=sA-Ts(s+6),\qquad
\lambda=sL-s^2A+Ts(s+2)(s+4),\qquad d=a_0-\lambda.
\tag{36.12}
$$

最后一步是 $\lambda=s(L+8T-\mu)$，并用 $(s+2)(s+4)=s^2+6s+8$；没有除 $\nu$ 或某个物理样本。

奇数式左边全部系数为

$$
\left(\left(q-1+\frac{2\eta}s\right)\lambda,
q(\mu+\lambda/s)+(2\eta/s)\mu,
q(\nu+\mu/s)+(2\eta/s)\nu,
q\nu/s\right),
\tag{36.13}
$$

右边为 $(C-15qT,B+23qT,D-9qT,qT)$。三次已自动相等，余下恰为三个方程

$$
\begin{aligned}
D-qA&=HT,\\
B-qL+15qT&=2\eta A-2\eta T(s+6),\\
C-15qT&=((q-1)s+2\eta)\bigl(L-sA+T(s+2)(s+4)\bigr).
\end{aligned}
\tag{36.14}
$$

逐项核对：二次比较给 $D-9qT=q(A-6T)+2\eta T$，即第一式；一次比较给 $B+23qT=q(L+8T)+2\eta(A-T(s+6))$，即第二式；常数比较用式 (36.12) 给第三式。另从奇数式减 $q$ 倍偶数式，模型差为 $(q-1)\lambda+(2\eta/s)g$，节点多项式差为 $S_{\rm o}-U_{\rm e}=-3t^2+15t-15$，再次检查三个符号。

这些条件是必要且充分的整个父描述。必要性已由任意合法真正二次世界推出。反向取任意 $q>0,s>2q,T\ne0$ 满足式 (36.14)，用式 (36.6)、(36.12) 构造来源及整个增益、漂移。式 (36.11) 与全部奇数系数都相等，所以两个整个恒等式成立。在偶节点 $U_{\rm e}=0$，在奇节点 $S_{\rm o}=0$，故复现全部六个实际父方程，含 $y_0=d+\lambda$。来源严格，$\nu=Ts\ne0$，所以构造者确为完整合法世界。不需隐藏的漂移、来源、历史或零样本过滤；没有把不同系数交给不同来源。

### 36.4. 通用比例支的可逆消元与十四根界

在 $H\ne0,\eta\ne0$ 支定义全部显式多项式

$$
\begin{aligned}
U&=D-qA,\qquad Z=2\eta U,\\
N&=H(2\eta A-B+qL)-(12\eta+15q)U,\\
V&=LHZ^2-AHNZ+U(N+2Z)(N+4Z),\\
F&=((q-1)N+2\eta Z)V-(CH-15qU)Z^3,\\
W(q)&=N(q)-2qZ(q).
\end{aligned}
\tag{36.15}
$$

这里 $W(q)$ 只是标量多项式，与完整世界记号 $W$ 区分。整个通用真正二次集合精确为

$$
q>0,\qquad H(q)\ne0,\qquad Z(q)W(q)>0,\qquad F(q)=0,
\qquad s=\frac NZ,\quad T=\frac UH,
\tag{36.16}
$$

再用式 (36.6)、(36.12) 给完整逆。

证明必要性：第一账式强制 $T=U/H$。$T\ne0$ 给 $U\ne0$，故 $Z\ne0$。重排第二式为

$$
2\eta Ts=2\eta A-B+qL-(12\eta+15q)T.
$$

乘 $H$ 恰得 $Zs=N$。在第三式中

$$
(q-1)s+2\eta=\frac{(q-1)N+2\eta Z}{Z},\qquad
L-sA+T(s+2)(s+4)=\frac{V}{HZ^2},\qquad
C-15qT=\frac{CH-15qU}{H}.
\tag{36.17}
$$

中式的三个分子分别为 $LHZ^2,-AHNZ,U(N+2Z)(N+4Z)$，故没有省项。乘非零 $HZ^3$ 即得 $F=0$，不要求 $H,Z$ 为正。严格 $s>2q$ 给 $ZW=Z^2(s-2q)>0$。

证明充分性：式 (36.16) 的严格不等式给 $Z,W\ne0$，从 $Z=2\eta U$ 得 $\eta,U\ne0$。又 $s-2q=W/Z=ZW/Z^2>0$，所以来源严格，$T=U/H\ne0$。$T=U/H$、$Zs=N$ 分别恢复前两账式；除回非零 $HZ^3$ 恢复第三式。第 36.3 节的充分性给全部实际方程和完整世界。一个 $q$ 强制 $s,T$ 及所有源、增益、漂移系数；不同 $q$ 的源比例 $r/b$ 不同，所以此参数化单射。$\alpha$ 被 $Z\ne0$ 排除，$\phi$ 被 $H\ne0$ 排除，未漏通用合法世界。

次数账是 $\deg\eta=\deg H=2$，$\deg U\le1$，$\deg Z\le3$。$N$ 的两项次数至多 $4,3$，故 $\deg N\le4$；$V$ 的三项次数至多 $8,9,9$，故 $\deg V\le9$。因子 $(q-1)N+2\eta Z$ 次数至多五，$F$ 的另一项次数至多 $2+3\cdot3=11$，故非零 $F$ 次数至多十四。非零一元多项式至多有其次数个不同实根，合法子集及单射逆遂贡献至多十四个完整世界。降次只减小上界；非实根、非法分母根和重数不增加世界数。

### 36.5. 恒等退化的全部开区间及端点证明

因为式 (36.15) 已指定次数至多十四的整个多项式，恒等退化的充要条件正是全部十五个系数恒等式

$$
[q^k]F=0\qquad
k\in\{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14\}.
\tag{36.18}
$$

降次以上的系数仍作为零系数包含；这是关于 $A,L,D,B,C$ 的精确等式条件，不是近似检测，也未执行系数提取。

当且仅当这些恒等式成立，通用支剩下整个合法开集

$$
\mathcal O=\{q>0:H(q)\ne0,\ Z(q)W(q)>0\}.
\tag{36.19}
$$

若 $Z$ 或 $W$ 是零多项式，则严格不等式使 $\mathcal O$ 为空。否则 $q,H,Z,W$ 均非零，实多项式环为整环，故边界多项式

$$
B_{\partial}(q)=qH(q)Z(q)W(q)\ne0,\qquad
\deg B_{\partial}\le1+2+3+4=10.
\tag{36.20}
$$

将其全部不同非负实根顺序排列，含本来就是根的零。在相邻根之间和最后一个正向无界区间上，各因子均连续且不为零，若变号则由介值性必有零点，矛盾。因此各因子符号在每个区间恒定，恰保留 $H\ne0,ZW>0$ 的区间。每个有限端点都零化 $q,H,Z$ 或 $W$，故违反严格正性或分母非零条件，不能成为合法世界。每个合法点必落在某个区间，全部区间及全部端点因而穷尽；重复根只列一次，不按偶重根额外粘合非法端点。

次数十至多十个不同实根，划分至多十一个区间，限制正半轴并保留其中一部分不会增加数目。所以 $\mathcal O$ 至多十一开区间分量。它也直接是严格条件与非零条件的交，故为开集，不会遗漏孤立合法点或合法单点分量。$q=0$、$H=0$、$Z=0$、$W=0$ 的端点全不在通用支；适用的例外比例由下一两节另行完整处理，不能把端点当极限严格源补入本支。

若 $\mathcal O$ 非空，它包含实开区间，且式 (36.16) 到完整世界的映射单射，所以贡献连续统多世界；空时贡献零。此条件分类同时处理两者，没有断言存在某个合法记录使恒等退化非空，也没有区间数的达到、存在或尖锐性结论。根排序和符号描述是未经执行的集合数学。

### 36.6. 唯一正的零 eta 支：全部归一化三次因子

取 $q=\alpha$。$H=3q>0$，第一式强制

$$
T=\frac{D-qA}{3q}\ne0,\qquad
B-qL+15qT=0,\qquad
\lambda=\frac{C-15qT}{q-1}.
\tag{36.21}
$$

第二式是必需入口等式；$q<1$ 保证第三式分母非零。定义完整三次

$$
K(t)=\lambda+Lt+At^2+TU_{\rm e}(t).
\tag{36.22}
$$

必要性：偶数整个式要求 $eg=K$，$e=1+t/s$ 在 $\zeta=-s$ 为零；故 $K(\zeta)=0$。严格 $s>2q$ 恰为 $\zeta<-2q$。

充分逆：入口通过后，保留 $K$ 的所有不同实根 $\zeta<-2q$，置

$$
s=-\zeta,\qquad g(t)=\frac{K(t)}{1-t/\zeta},\qquad d=a_0-\lambda,
\tag{36.23}
$$

并用整个来源坐标式 (36.6)。根条件证明 $t+s$ 真正整除 $K$，所以式 (36.23) 是多项式商，不是把采样数据相除。除子 $(t+s)/s$ 常数系数一，固定了整个尺度。$K$ 的首项为 $T\ne0$，商为真正二次、首项 $Ts\ne0$。在零点代入恒等式 $eg=K$ 得 $g(0)=\lambda$，所以漂移正确；比较偶数系数还给式 (36.12) 的完整逆。

此处 $o=qe$。入口给 $D-qA=3qT,B-qL=-15qT,C-15qT=(q-1)\lambda$，故逐系数有

$$
R+qTS_{\rm o}=q(E+TU_{\rm e})+(q-1)\lambda=-\lambda+og.
\tag{36.24}
$$

因此两整个恒等式及全部六个父方程成立，证明每个所列根充分且每个真正世界必在列中，没有用时钟六数据或末根承诺。

非零三次 $K$ 至多三个不同实根，所以至多三个完整世界。不同根给不同 $s,b$；重根只选一次来源因子，剩余重数留在增益中。$\lambda=0$、任意采样零、重增益根和两种尺度符号均保留。等号 $\zeta=-2q$ 给 $r=1$，是非法严格源边界；$\zeta=0$ 也不满足截止。不除任何取得的增益样本。

### 36.7. 唯一正的零 H 支：非零参数三次及全部降次

取 $q=\phi>1$，此时 $\eta=-3q/2\ne0$。第一账式是入口

$$
D=qA,\qquad
v=\frac{B-qL+3qA}{3q}\ne0,\qquad
T=\frac{v}{s+1}.
\tag{36.25}
$$

第二账式化为 $B-qL+3qA=3qT(s+1)$，且 $s>2q>0$ 保证 $s+1>0$。所以 $v\ne0$ 恰保真正二次；没有合法 $s=-1$ 或被遗漏的二次 $T=0$ 支。

将偶数逆括号乘 $s+1$ 得

$$
\begin{aligned}
K_\phi(s)&=(L-sA)(s+1)+v(s+2)(s+4)\\
&=(v-A)s^2+(L-A+6v)s+L+8v,\\
\lambda&=\frac{sK_\phi(s)}{s+1},\\
P_\phi(s)&=((q-1)s-3q)K_\phi(s)-C(s+1)+15qv.
\end{aligned}
\tag{36.26}
$$

常数账式乘正的 $s+1$ 恰为 $P_\phi(s)=0$。因此保留其所有不同实根 $s>2q$，取式 (36.25) 的 $T$，用式 (36.6)、(36.12) 构造整个世界。

还须证明此参数多项式始终非零，不能以默认三次漏掉降次。令 $a_2=v-A,a_1=L-A+6v,a_0=L+8v$，$P_\phi$ 从三次至常数的全部系数为

$$
(q-1)a_2,\qquad
(q-1)a_1-3qa_2,\qquad
(q-1)a_0-3qa_1-C,\qquad
-3qa_0-C+15qv.
\tag{36.27}
$$

若全部为零，$q-1\ne0$ 先给 $v=A$，第二系数给 $L+5A=0$，故 $K_\phi=3A$。最后两个系数变为 $3A(q-1)-C$ 和 $6qA-C$。相减强制 $-3A(q+1)=0$，因 $q+1>0$ 得 $A=0$，继而 $v=0$，与入口矛盾。故 $P_\phi$ 非零，即使三次、二次或一次系数消失也成立；没有除一个可能消失的首项。

每个真世界必满足入口及此方程；反向每个合法根使前两账式成立，第三式可通过非零 $s+1$ 可逆恢复。第 36.3 节给全方程充分性，$T\ne0$ 确保整个二次。次数至多三给至多三个不同完整世界，重根计一次；不同 $s$ 给不同 $b$。非零常数多项式无根，线性、二次等降次的根也全部保留，不附符号或平方自由限制。

### 36.8. 继承的整个仿射并集，包含两种有符号半直线

本节仿射部分直接继承《FIB 仿射增益恢复与早期动作分离》第 31.2—31.5 节，尤其式 (31.5)—(31.13)、(31.17)—(31.20)。该卷的 $E,O$ 在此分别为 $E,R$，系数 $A,L,D,B,C$ 完全相同，物理漂移同为 $a_0-\lambda$。以下给其全部父条件及证明，不把继承仿射数学另计新增结果，也不把该卷固定末动作逆装成整个二次逆。

在 $\nu=0$ 时，两整个式为 $E=-\lambda+eg,R=-\lambda+og$，逐系数要求

$$
A=\mu/s=b\mu/2,\quad L=\mu+\lambda/s,\quad
D=qA,\quad B=qL+2\eta A,\quad
C=(q-1+2\eta/s)\lambda.
\tag{36.28}
$$

因 $b>0$，只在仿射部分内 $A\ne0$ 等价于非恒定仿射。此观察不排除同记录中的真正二次竞争者。

非恒定仿射的整个父如下：若 $A\ne0$，强制 $q=D/A$，要求 $q>0$ 及 $B=qL+2\eta A$，保留全部不同实根 $s>2q$ 满足

$$
(q-1)As^2+(2\eta A-(q-1)L)s+C-2\eta L=0,
\qquad \mu=As,\quad\lambda=s(L-As),\quad d=a_0-\lambda.
\tag{36.29}
$$

来源用式 (36.6)。证明：偶数系数唯一给 $\mu,\lambda$，常数式为 $C=((q-1)s+2\eta)(L-As)$，展开移项正是式 (36.29)。反向这些等式匹配两整个式的全部系数，故在三个偶、三个奇节点复现六个父方程；来源严格，$\mu=As\ne0$。每个世界必对应自己的根，每个接受根充分且唯一。$q\ne1$ 时二次项 $(q-1)A\ne0$；$q=1$ 时 $\eta=-1/2$，方程为 $-As+C+L=0$，非退化一次。所以至多两个完整世界，重根只计一次；$\eta=0$、$\lambda=0$、$L=0$ 或物理采样零均不被约去。

常数仿射支须 $A=0,D=0,L\ne0$，$\mu=0,\lambda\ne0$。定义

$$
U_c=2B=\lambda r,\qquad V_c=2L=\lambda b\ne0,\qquad
W_c=C+U_c/2=\lambda(j-1),
\tag{36.30}
$$

对候选 $\lambda\ne0$ 置

$$
R_\lambda=\begin{pmatrix}U_c&V_c\\\lambda+W_c-V_c&\lambda-U_c\end{pmatrix},\qquad
P=R_\lambda/\lambda,\quad g(t)=\lambda,\quad d=a_0-\lambda.
\tag{36.31}
$$

整个来源过滤恰为

$$
0<\frac{U_c}{\lambda}<1,\qquad \frac{V_c}{\lambda}>0,\qquad
\frac{\lambda+W_c-V_c}{\lambda}>0,\qquad
(U_c-V_c)\lambda-U_c^2-V_cW_c+V_c^2=0.
\tag{36.32}
$$

证明：缩放源的行列式为 $U_c(\lambda-U_c)-V_c(\lambda+W_c-V_c)$，展开即最后等式；其迹为 $\lambda$。过滤后的 $P$ 迹一、所有元严格正、行列式零，故秩恰一。回代有 $r=U_c/\lambda,b=V_c/\lambda,c=(\lambda+W_c-V_c)/\lambda,j=1+W_c/\lambda$，于是

$$
E(t)=V_ct/2,\qquad R(t)=W_c-U_c/2+U_ct/2.
\tag{36.33}
$$

这与已取得插值恰相同，所以全部父方程成立；任意真实常数世界也必强制这些量，证明双向完整性。正性只要求归一化的 $P$，$\lambda$ 以及辅助 $R_\lambda$ 可以为负。

全部常数奇异和符号情形为

| 条件 | 整个合法参数集 |
| --- | --- |
| $U_c\ne V_c$ | 唯一可能 $\lambda=(U_c^2+V_cW_c-V_c^2)/(U_c-V_c)$；拒绝零后，保留且仅保留式 (36.32) 通过者 |
| $U_c=V_c\ne0,W_c\ne0$ | 行列式为非零 $-V_cW_c$，空集 |
| $U_c=V_c\ne0,W_c=0$ | 行列式恒零，全部参数为 $0<U_c/\lambda<1$；$U_c>0$ 时 $\lambda>U_c$，$U_c<0$ 时 $\lambda<U_c$ |

末行令 $p=U_c/\lambda$，则 $P=\left(\begin{smallmatrix}p&p\\1-p&1-p\end{smallmatrix}\right)$，所有来源不等式恰化为 $0<p<1$，故确为整个有符号半直线，非有限截取。$U_c=0$ 被严格 $r>0$ 过滤拒绝，不除 $U_c$；$V_c=0$ 与 $L\ne0$ 矛盾，故没有遗漏 $U_c=V_c=0$。$W_c=0,U_c\ne V_c$ 仍在唯一候选支内。$L=0$ 或 $D\ne0$ 使常数部分空。有限常数部分至多一世界。

同一记录的恒定与非恒定仿射由 $A=0$ 和 $A\ne0$ 区分，不能彼此共存；有限仿射部分至多二。所有仿射成员始终与所有合法真正二次分支一同保留，不能先按一个仿射承诺剔除其他次数。

### 36.9. 不交穷尽、完整世界单射与全部基数

任意非零次数至多二的整个增益恰有 $\nu=0$ 或 $\nu\ne0$。前者是第 36.8 节的整个继承并集；后者 $T\ne0$，进入全部系数账。任意正 $q$ 若 $\eta=0$，只有 $\alpha$；否则若 $H=0$，只有 $\phi$；剩余恰为通用支。$\alpha\ne\phi$，所以三个真正二次分支互斥且穷尽。$T=0$ 不作为丢失的二次分支，而由仿射分析保留。

各支已从任意世界证明必要性，又从每个合法参数证明来源、整个增益、漂移及全部六个实际方程的充分性。因此其并集就是任意实记录的整个父，包括所有不兼容记录的空父，不依赖隐藏的历史过滤或来源标签。

通用 $q$ 固定 $s,T$ 和整个世界，不同 $q$ 来源比例不同；$\alpha$ 根固定 $s$ 和归一化整个商；$\phi$ 根固定 $s,T$ 和完整逆；两例外的不同 $s$ 给不同 $b$。非恒定仿射 $s$ 固定整个世界，常数 $\lambda$ 固定整个非零常增益及漂移。不同真正二次支比例不同，仿射与二次的 $\nu$ 不同。仅合并整个三元组相等者，形式根重数计一次，不能因来源投影或某一个相同样本合并世界。

若通用 $F\ne0$，各部分上界为 $14,3,3,2$。若 $F$ 恒零而 $\mathcal O$ 为空，则通用部分为零；若 $\mathcal O$ 非空或常数半直线出现，则整个父已无限。因此每个有限父均满足

$$
|\mathcal S|\le14+3+3+2=22.
\tag{36.34}
$$

这是粗界，没有断言各项能同时达到或总界尖锐。

例外比例、非恒定仿射始终有限；常数部分只可能空、单点或整条已证半直线；通用非零 $F$ 有限，恒零 $F$ 则空或有限个开区间。因此无限只能来自非空通用开集或常数半直线，各自单射包含实区间而给至少连续统世界。每支至多由一个实参数表示，有限个分支的并至多连续统，所以无限父基数恰为连续统，没有遗漏可数无穷。此结论不要求恒等退化真的有非空实例。定理 36.1 得证。∎

### 36.10. 独立的无二世界 L2 证明，包含全部零分支

**定理 36.2（两世界不能同时阻断两剩余动作层）。** 在任意实际 JMJMJ 父记录上，任意恰含两个不同完整次数至多二世界的集合 $K$ 都不满足 $L_2$。若整个父至多两个世界，第 36.11 节的实际续行在原始八次 TOTAL 预算内恢复完整目标。

沿用停止保留的递归：$L_0(K,\mathcal H)$ 表示 $K$ 有至少两个不同完整目标；$L_{m+1}$ 还要求同一基数守卫，并对每个动作有某个实际响应，其 FULL 兼容切片在扩展历史上具有 $L_m$。若同历史 $K\subseteq K'$，$L_0$ 由基数保持；归纳沿旧响应保留子片包含，故 $L_m$ 向上保持。任意基数均可用此归纳，不从非终端大族抽取同层失败对。

对恰二元素 $K=\{W_1,W_2\}$，任何有失败守卫的子集都必须保留这两个世界。因此 $L_2(K)$ 等价于以下六个跨世界等式同时成立：

$$
h_2(W_1)=h_2(W_2),\quad h_3(W_1)=h_3(W_2),\quad
f_{2J}(W_1)=f_{2J}(W_2),\quad f_{2M}(W_1)=f_{2M}(W_2),\quad
f_{3J}(W_1)=f_{3J}(W_2),\quad f_{3M}(W_1)=f_{3M}(W_2).
\tag{36.35}
$$

必要性来自两层实际响应片和停止守卫；充分性是每个第六臂保留整对，再在两个末动作均保留整对，恰给两个 $L_1$ 子片及父守卫。不同 $n$ 的响应不必互相相同，只要求每个函数在这对世界上相同。此六式等价只用于实际二元素集合。

假设六式成立，记 $G_i=g_i(7)$。第 $n=3$ 的末 $J$ 等式减第 $n=2$ 的末 $J$ 等式，得 $r_1G_1=r_2G_2$；对应末 $M$ 相减得 $(b_1+r_1)G_1=(b_2+r_2)G_2$，所以 $b_1G_1=b_2G_2$。在 $n=2$ 内末 $M$ 减末 $J$ 又给

$$
(1-r_1+2b_1)G_1=(1-r_2+2b_2)G_2.
$$

代入前述加权等式，无除法即得 $G_1=G_2=G$。

若 $G\ne0$，这时才除它，得到共同 $r,b$，秩一和 $b>0$ 给共同 $c=r(1-r)/b$。一个末等式再给共同 $d$。已取得来源迹都共同且严格正，所以原时钟 $0,1,2$ 的共同读数给共同三个增益值。两至多二次增益之差在三个不同节点为零，故整个增益相同，完整目标相同，矛盾。

于是只需考虑 $G=0$。任一末等式立刻给共同 $d$，不除零样本。令 $K_i=g_i(6)$；两第六等式为

$$
(1+2b_1)K_1=(1+2b_2)K_2,\qquad
(1+3b_1)K_1=(1+3b_2)K_2.
\tag{36.36}
$$

相减给 $b_1K_1=b_2K_2$，回代给 $K_1=K_2=K_6$，仍未除任何待定量。

若 $K_6\ne0$，此时才除它得到共同 $b$；共同初值 $a_0-d$、在六的共同 $K_6$、在七的共同零值，位于三个不同节点 $0,6,7$，唯一确定同一个整个至多二次增益。不是新增观察，也未把差式误作三次。

若 $K_6=0$，每个非零至多二次增益都有不同根六、七，故恰为 $\kappa_i(t-6)(t-7)$，$\kappa_i\ne0$。初读给 $42\kappa_i=a_0-d$。若 $a_0=d$ 就强制零多项式，违法；否则两者为共同非零 $\kappa$。于是 $g(2)=20\kappa\ne0$，实际时钟二方程 $y_2-d=(1+b_i)20\kappa$ 固定共同 $b$。这是任意父记录中的实际方程，不是一个特殊数值历史。两种 $K_6$ 情况都得到共同整个 $g,b,d$。

共同非零至多二次 $g$ 已有根七，在三个不同奇时钟 $1,3,5$ 中至多再有一个零；否则至少三个不同根。因此至少两奇样本活跃。取任意两活跃行，只有这时才除所选非零样本，得到共同右侧的源方程

$$
j_i g(1)=y_1-d,\quad (j_i+r_i)g(3)=y_3-d,\quad
(j_i+2r_i)g(5)=y_5-d.
\tag{36.37}
$$

在 $(j,r)$ 中任两行 $(1,0),(1,1),(1,2)$ 的行列式分别为一、二、一，均非零，所以给共同 $j,r$；共同 $b$ 再给 $c=j-b$。未用零行保持其原方程。完整三元组遂相同，矛盾。全部零与低次数支都已穷尽，故无二世界 $L_2$。它也排除大父中的某个二世界子集自身有 $L_2$，但不把大父失败转交给一对。∎

### 36.11. 整个父至多二时的具体因果规则

仅用已经取得的 $y_0,\ldots,y_5$ 按定理 36.1 构造整个父 $\mathcal S$，不能只取某个标签支或挑选一对。合法实际世界必在集合中，故空父是不可达的不兼容记录。

若 $|\mathcal S|=1$，停止并返回唯一完整世界。若 $|\mathcal S|=2$，先比较两世界的 $h_2$。不相等则现在选择第六 $J$，立即读其响应；每个可达 FULL 切片都恰为一个世界，可以停止。若 $h_2$ 相等，再比较 $h_3$；不相等则选择第六 $M$，立即读响应后在唯一完整切片停止。

若两第六函数都在整对上相等，定理 36.2 保证四个末函数中至少一个分离此对，否则式 (36.35) 会成立。按固定次序

$$
(2,J),\ (2,M),\ (3,J),\ (3,M)
\tag{36.38}
$$

取第一个分离函数。现在先选择其 $n$ 对应的第六动作，取得其共同第六响应；然后执行所选末动作并立即读时钟七，返回唯一匹配的整个世界。

证明合法性与充分性：所有比较都在第六选择之前对同一已固定完整候选进行，第一分离函数不依赖把这两个世界如何排序。前两情形每个可能实际第六响应均保留，不挑有利未来值；因为整个父只有两个，所有实际子片为单点。最后情形所选第六 FULL 片仍恰为原整对，所选末函数在此整片单射。每步真实世界仍在实际片中保证非空与必要性，单射保证至多一与完整目标唯一；全部祖先、零样本及所选新方程保留。停止只发生于整个实际承诺片单点，不能在非分离末臂留下两目标时停止成功。

使用原时钟且每动作立即读，初读加五动作已六读，再用至多两读，故总数至多八。不使用未来响应、未知漂移标签、源标签、真根标签或动作后重配增益。此为精确实数集合规则，没有可计算性、有限精度或效率保证，也不声称读数最优。定理 36.2 的续行部分得证。∎

### 36.12. 较大父的整个切片充要判据与条件联合接口

**命题 36.3（仍须统一解决的整个切片判据）。** 对一个固定完整父 $\mathcal S$ 及第六指标 $n$，写每个可达 FULL 实际响应片为

$$
\mathcal S_{n,a}=\{W\in\mathcal S:h_n(W)=a\}.
\tag{36.39}
$$

该第六臂能以剩下至多两读恢复整个父，当且仅当对每个可达 $a$，此片为单点，或 $f_{nJ}$ 在整片单射，或 $f_{nM}$ 在整片单射。

证明必要性：实际取得 $a$ 后，只能在此整个片停止或选一个末动作。停止须单点；非单点时若选 $J$ 就必须其函数在整个片单射，否则两个不同目标给相同末响应；选 $M$ 同理。不能按未知真世界另选末动作。证明充分性：在每个已取得 $a$ 的整片上，单点就停止；否则若 $J$ 单射则选 $J$，余下选择单射的 $M$。实际兼容给唯一响应原像的存在，单射给其唯一，遂返回完整目标。全体选择只依已经取得的历史，证明充要性。

有限父上这是对至多二十二完整世界的精确分片；无限父仍是同一整个集合条件，包含所有开区间族和孤立世界，须同时比较分支内、分支间、区间内、区间间以及区间与孤立者的全部竞争者。一个分支的逆或每对各有某个分离动作，均不能替代一个末动作在整片单射。

若一个第六臂失败，就有同一实际响应片中两末函数都非单射。各非单射只在该片内部提供一对不同完整世界；末 $J$、末 $M$ 的碰撞对可以不同。它们给末端两个 $L_0$ 分句及此片的非单点 $L_1$ 守卫。

仅当两个第六臂都在同一个已取得父记录上失败，才可选其各自坏片，并在每片的两个末端 $L_0$ 处选两对，取这些固定端点的并 $K$，至多八个世界。所有端点共同满足该父的全部六读祖先。每个被服务第六响应片中的两个指定终端对都属于 $K$ 的该 FULL 片；这保证其两个末动作的 $L_0$ 响应及 $L_1$ 非单点守卫。更大的该片由同历史包含保持 $L_1$。$K$ 自身含不同目标而保留父守卫，两第六臂各有这样的 $L_1$ 子片，故 $L_2(K)$。每条被服务历史都含不同目标，所有相应停止守卫保留。

反向，真正的 $L_2$ 先为各第六动作选择一个实际 $L_1$ 响应，再在各末动作的终端 $L_0$ 中才选不同目标对，恰恢复上述至多八端点接口。这个有限终端支持论证适用于任意基数原父；它没有在非终端大族抽取同层失败对，也没有声称只需一对即可失败。

此接口仅为条件性完整联合证明，没有给出一组使两个臂同时失败的共同合法世界，也没有证明任意较大父必有一个成功臂。不同父的局部失败不能取并成为同父 $L_2$；第 34 节与第 35 节的不同父或不同已取得子片仍不能拼接。待解任务恰是对全部记录和全部分支统一证明某个第六臂通过整个切片判据，或给一个可达父的两个失败臂联合实例。即使有局部 $L_2$，任意原根策略也未被迫走入 JMJMJ；被服务祖先不自动补齐其另一动作义务。∎

### 36.13. 除法、严格边界、继承与原目标

全部除法边界如下。插值只用固定非零节点差和有理常数。来源坐标用严格 $b,s>0$。通用消元只在显式 $H,Z\ne0$ 后除它们，清分母仅用非零 $HZ^3$；$Z\ne0$ 同时证明 $\eta,U\ne0$。$\alpha$ 支用 $3q>0,q-1\ne0$ 及已证明的归一化多项式因子；$\phi$ 支用 $3q>0,s+1>0$，$v\ne0$ 保证真正二次。仿射支仅在 $A\ne0$ 后除 $A$；常数唯一候选仅在 $U_c\ne V_c$ 后除其差，再于排除零后除 $\lambda$。二世界证明先无除法固定共同 $G,K_6$，只在各非零支除；还用严格正实际迹、固定不同节点、非零常数 $42$、已证非零 $20\kappa$ 和所选活跃奇样本。

没有约去未知读数、未证非零物理样本、漂移差、来源行列式、判别式、$1-2r$ 或未知首项。真正二次仅由 $T\ne0,s>0$ 得到；常数和仿射由独立次数支保留。$\lambda=0,\mu=0$、任意兼容漂移、正负尺度、采样或非采样根、重增益根均允许。零增益依原世界要求排除；重参数根只计一次，不附平方自由承诺。

来源域恰 $q>0,s>2q$，不包括 $q=0$ 的 $r=0$ 或 $s=2q$ 的 $r=1$；$r=0,1,b=0,c=0$ 不以极限补入。$r=1/2$、两对角侧、对称及非对称和无界正非对角均在内。常数负尺度半直线完整保留。恒等区间端点按自身严格条件排除；例外支不为非法边界提供替代世界。

第 31 节的整个仿射父、已知方向与已知平面结果均保持各自承诺。第 32—35 节的全部证明和旧未决边界按各自明确范围保留；本节的全父分类不把已取得 $e_3$ 或潜在 $T$ 当成原三次模型的二次检测器。原三次增益乘线性 $e$ 可为四次，仅在三个或四个偶节点相等不强制这里所用的低次整个恒等式。旧有限中心、全预条件矩阵、区间、导数、递推、收缩、合法性和精确极限前提保持其原条件性范围；本节不执行或重新认证它们，也不以它们证明此处符号分类。标准插值、因式分解、根数、迹配对与线性代数是复用工具，不另称新一般方法。

整个二次原根问题仍为 OPEN：对所有严格非零次数至多二完整世界和任意兼容漂移，原时钟零至七内至多八次 TOTAL 的确定性自适应恢复，或其原根 $L_7$，均未由这里证明。较大父可以有限至多二十二或连续统，不能因为二世界续行成功就假定所有父都小。一般二维增益空间、未知并集与混合失败族也不因本分类自动可恢复。

原始所有非零次数至多三的完整类之自适应八读逆，和 $n_{\rm det}(3,0)\ge9$，仍为 OPEN。完整联合合同保持所有 $256$ 槽 $\sigma=(w,\epsilon)$，其中 $w\in\{J,M\}^7,\epsilon\in\{0,1\}$；保留所有 $254$ 非空实际前缀 $v$、其原长度 $i$、左乘积 $A_v$ 和全部后代 $D_v$。每槽有严格来源和整个四系数块 $x_\sigma$，令

$$
t_v(P)=\operatorname{tr}(A_vP),\qquad
\ell_v(P)=(t_v(P)-1,\ i t_v(P),\ i^2t_v(P),\ i^3t_v(P)).
\tag{36.40}
$$

同一个完整 $1538\times1024$ 矩阵 $B(\mathbf P)$ 的每行比较同前缀后代与代表 $\sigma_v$：$\ell_v(P_\sigma)x_\sigma-\ell_v(P_{\sigma_v})x_{\sigma_v}$。每层行数为 $2^i(2^{8-i}-1)=256-2^i$，七层仍为 $254,252,248,240,224,192,128$；每槽四系数仍共 $1024$ 列。这些计数仅为符号表达，未执行枚举或矩阵运算。

必须在 ONE 同一堆叠向量上同时满足每个整个四分量增益守卫 $G_\sigma x=x_\sigma\ne0$，及每个适用同源终叶整个差守卫 $D_wx=x_{(w,0)}-x_{(w,1)}\ne0$，并同时满足所有严格来源、全部祖先响应、两个动作和全部停止守卫。每槽整个增益为 $\sum_{h=0}^3x_{\sigma h}t^h$，漂移为 $a_0-x_{\sigma0}$；终叶异源已区别完整目标。重复槽仅在整个三元组相等时合并。若限制二次，须同时在所有块中置三次系数为零，不能删块、删祖先或换矩阵。

这里未给不受限共同核可行向量、联合原根失败树、缺失动作臂、不受限同父 $L_3$、强迫晚期历史或九读上界；分开的路径、核、守卫见证及单路径局部标量逆都不替代该同一联合合同。第 32—33 节的恒零守卫只在各自声明平面与同一完整核的交空间上成立，不成为不受限核的恒零或可行结论。

也没有混合族删除、未知承诺/方向/根/平面检测器、可恢复未知并集、增益跨度至少三、支持下界五、全部四世界排除、四世界原根存在性或尖锐支持界。真实三次必要性仍缺整个二次原根恢复；继承仿射结果只给原来的至少二次成员边界。不存在一般神经网络、经验物理、噪声、稳定性、连续性、有限精度、效率、可计算性、资源或外部优先权保证。未作外部文献穷尽搜索，未执行公式、数值、导数、递推、枚举、CAS、矩阵/秩/核/区间算术、实验或 kernel 核验。所有结论仅为所列条件下的精确实数符号数学。

## 追加锚（本行以下为增补区）
