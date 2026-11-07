# AURIC：任意维小窗口的同一原单位桥

## 1. 固定引用与数学范围

**定义 1.1（纸面范围及外卷编号）。** 本卷为纸面数学论证（PAPER），不主张 Lean 形式验证。下文“三标签卷”指 [AURIC C128：三标签正性与同一原有向关系的刚性](AURIC_C128_THREE_LABEL_POSITIVITY_AND_ORIGINAL_RELATION_RIGIDITY.md)，“正交迹续卷”指 [AURIC C128：正交迹与整支持角续卷](AURIC_C128_ORTHOGONAL_TRACE_AND_CORNER_RELATIONS_CONTINUATION.md)，“闭三角卷”指 [C128：闭合三角形与稀疏伸缩关系](AURIC_C128_CLOSED_TRIANGLE_AND_SPARSE_SCALE_RELATIONS.md)。外卷的定义、定理与公式编号始终属于所指原卷；本卷第 2–5 章的编号只用于本卷。

本卷只从同一原平方的正性、固定点及任意指定小窗口恢复同一原 $S$ 的单位，并说明辅助完成中的镜面不必保持原域。总映射入口保持三标签卷约定 1.1、定义 8.2–8.4 与闭三角卷定义 476.1 的全部原对象和实际来源；无限维不替换为有限截面，完成仅作证明工具。一般同一 $S$ 的 JB 识别、旧 $D$ 的恢复及完整物理消费者继续承担第 3 章所列未付接口。

## 2. 任意维小窗口中的同一原单位

**定义 2.1（固定原域的两个入口）。** 固定实 Archimedean 序单位空间 $(E,C,u)$ 及原序单位范数 $N$；$C$ 为闭尖生成锥，允许 $E$ 无限维且不完备。固定一个原先指定的正有理数 $0<\theta\le1$。约化入口只给同一个对称实双线性 $S:E^2\to E$，并要求

$$
a^2:=S(a,a)\in C\quad(a\in E),\qquad u^2=u,\qquad
0\le e\le\theta u\ \Longrightarrow\ e^2\le e.
\tag{2.1}
$$

不把乘法有界性列为独立前提。总映射入口则取[闭三角卷](AURIC_C128_CLOSED_TRIANGLE_AND_SPARSE_SCALE_RELATIONS.md)定义 476.1 的同一任意维原背景、分离评价族 $\mathcal P$ 及评价定义的原 $C$，旧 $S,D:E^2\to E$ 仅为总映射；对全部原标签要求三标签卷定义 18.2 第 1 项的至多二标签复正性（表取该卷式 (18.2)）、第 2 项的实相加三角及相加零平方（该卷式 (18.3)）、第 3 项的固定点和同一 $\theta$ 小窗口（该卷式 (18.4)）。这里仅移用这些具体关系，不移用三标签卷定义 18.1 的有限维限制，也不要求该卷式 (18.5)。全部原资料仍按三标签卷约定 1.1、定义 8.2–8.4 保留。

**定理 2.2（小窗口恢复准确原 $S$ 的单位）。** 定义 2.1 的任一入口均给同一个原乘法的

$$
\boxed{S(u,a)=S(a,u)=a\quad(a\in E).}
\tag{2.2}
$$

总映射入口还自动取得同一个 $S$ 的对称实双线性。两种入口均有 $N(S(a,b))\le M_\theta N(a)N(b)$，其中 $M_\theta=2/\theta-1$。不要求有限维、原域完备、全效果收缩、Jordan 律、旧 $D$ 的正则性或实部换括号式。

证明。$E=0$ 时平凡，以下设 $E\ne0$，故 $N(u)=1$。先明确总映射入口的对应。三标签卷定理 19.1 证明中从 Hermitian 二表到该卷式 (19.1) 的整个极化前段只用原评价分离、实相加三角和零平方，不用维数：它给 $S$ 对称、全部原平方正、$S(0,a)=0$，并由平行四边形及代数极化给同一 $S$ 的双可加和有理双线性。这里原锥由评价半空间定义而闭且 Archimedean，原序界给

$$
N(c)=\sup_{\alpha\in\mathcal P,\ m_\alpha>0}
\frac{|\alpha(c)|}{m_\alpha};
\tag{2.3}
$$

零质量评价在全部 $E$ 上恒零。因此三标签卷式 (19.2)–(19.3) 的窗口估计及有理逼近也原样适用，给 $N(S(a,b))\le M_\theta N(a)N(b)$；双可加性与此界再给实双线性。这里没有应用三标签卷定理 19.1 的有限维结论，也没有使用该卷式 (19.5) 的特征积分或 Hessian。以下给出同时适用于约化入口的窗口估计，以表明有界性不是额外公理。

若 $N(x)\le1$，原 $e_\pm=\theta(u\pm x)/2$ 都在原窗口内。仅用有理双线性及 (2.1)，

$$
0\le x^2,\qquad
\frac{\theta^2}{2}(u+x^2)=e_+^2+e_-^2\le\theta u,
\qquad x^2\le M_\theta u.
\tag{2.4}
$$

取有理 $r>N(a)$ 并令 $r\downarrow N(a)$，由锥闭性得 $a^2\le M_\theta N(a)^2u$。对任意数学态 $\varphi$，平方正性使 $\varphi(S(\cdot,\cdot))$ 满足 Cauchy–Schwarz；有理双线性阶段只需检验所有有理系数的二次式，稠密性同样给判别式界。全部数学态对序单位范数 norming，故

$$
|\varphi(S(a,b))|^2\le\varphi(a^2)\varphi(b^2)
\le M_\theta^2N(a)^2N(b)^2,
\qquad N(S(a,b))\le M_\theta N(a)N(b).
\tag{2.5}
$$

在总映射入口，也可直接以原二表和 (2.3) 取得同一界，再作实数逼近；没有为使用实双线性而预先假定它。数学态仅作对偶工具，不加入原准备族。

令 $X$ 为原 $N$ 的忠实完成，$C_X=\overline C^{\,X}$，仍以 $S$ 记同一乘法的唯一有界延拓。沿[正交迹续卷](AURIC_C128_ORTHOGONAL_TRACE_AND_CORNER_RELATIONS_CONTINUATION.md)定理 446.1 证明内的序单位完成论证，$u$ 仍为内部序单位，延拓范数仍为其序单位范数，且 $C_X\cap E=C$。具体地，原 norming 态连续延拓；若它们对 $x\in X$ 全非负，取 $N(a_n-x)\le\varepsilon_n\downarrow0$，则 $a_n+\varepsilon_nu\in C$，从而 $x\in C_X$。这也给锥的尖性和忠实限制。平方正性由连续性延拓；若 $0\le e\le\theta u$ 在 $X$ 内，同样的逼近给

$$
e_n=\frac{a_n+\varepsilon_nu}{1+2\varepsilon_n/\theta}
\in[0,\theta u]\cap E,\qquad e_n\longrightarrow e.
\tag{2.6}
$$

故同一小窗口收缩传到 $X$，正是正交迹续卷定理 454.1 证明内的小窗口完成步骤。对 $c\in C_X$ 取 $r>0$ 使 $c/r\le\theta u$，得 $0\le c^2\le rc$。任意连续正泛函 $\varphi$ 若 $\varphi(c)=0$，便有 $\varphi(c^2)=0$；再以全部 $(c+ta)^2$ 的正性得

$$
\varphi(S(a,c))=0
\quad(c\in C_X,\ \varphi\ge0,\ \varphi(c)=0).
\tag{2.7}
$$

只用实平方即可得到此零支撑面关系，不需要旧 $D$ 或复三表。成熟顺序导子判据取 Niestegge，[arXiv:1402.0158v2，§4 Lemma 3](https://arxiv.org/html/1402.0158v2#S4)：有界算子 $A$ 满足 (2.7) 的零面条件，当且仅当 $e^{tA}C_X=C_X$ 对所有实 $t$ 成立。这里用其序单位空间的算子判据，不借该文 §2(A) 已经假定的乘法单位。

比较解还需同一判据的时间依赖形式。若 $A(t)$ 范数连续且逐时满足零面条件，解 $y'=A(t)y+\varepsilon u$，$y(0)=c+\varepsilon u$。有限首次触边时可取支撑态 $\varphi$，$\varphi(y)=0$，左导数非正，而方程使之等于 $\varepsilon>0$，矛盾。令 $\varepsilon\downarrow0$ 得正演化，反向时间同证其逆为正。此为正交迹续卷定理 446.1 的边界证明在连续系数下的直接应用。

置 $L_ab=S(a,b)$、$T=L_u$、$K=T-I$、$U_t=e^{tK}$。(2.7) 使每个 $L_a$ 为顺序导子；这类算子由零面条件组成范数闭实线性空间，并由共轭后范数微分对交换子封闭。$I$ 也是顺序导子，故 $K$ 是顺序导子；$Tu=u$ 给 $Ku=0$。于是 $U_t$ 与 $U_{-t}$ 互为正逆且保 $u$，均为原序单位范数的等距算子。

此时不能调用已使用单位律的正交迹续卷定理 448.1。仅对当前特定 $K=T-I$，定义

$$
B(a,b)=KS(a,b)-S(Ka,b)-S(a,Kb),\qquad
B_a=[K,L_a]-L_{Ka},\qquad B_au=KTa-TKa=0.
\tag{2.8}
$$

末式使用 $K$ 与 $T$ 通勤及 $Ku=0$，未使用 $T=I$。每个 $B_a$ 因而是零单位顺序导子，生成等距群。复用正交迹续卷定理 448.1 证明内的二次流刚性方法：对 $z'=A(t)z$，若每个 $e^{hA(t)}$ 等距，则 $z(t+h)=e^{hA(t)}z(t)+o(|h|)$ 使 $N(z(t))$ 导数为零，无须范数本身可微。用于 $x'=B(x,x)$ 得解范数恒定；有界双线性场在有界球上有统一 Lipschitz 界和有界性，故解在全部实时间存在。两解之差满足 $(x-y)'=B(x+y,x-y)$，距离也恒定。流 $\Phi_t$ 因而是保零的满射等距，逆为 $\Phi_{-t}$。成熟 Mazur–Ulam 定理（Nica，[arXiv:1306.2380v1](https://arxiv.org/html/1306.2380v1)，开篇定理）给实线性；对 $\Phi_t(2x)=2\Phi_t(x)$ 在零时微分得 $4B(x,x)=2B(x,x)$，极化得 $B=0$。因此这个尚待消去的 $K$ 已是同一 $S$ 的代数导子，且

$$
U_tS(a,b)=S(U_ta,U_tb).
\tag{2.9}
$$

现在以同一平方构造锥镜面。令 $\Psi_t(x)$ 为 Banach 空间中 $x'=-x^2$ 的局部唯一流；有界双线性给局部存在唯一性。两解差满足

$$
w'=-L_{\Psi_t(x)+\Psi_t(y)}w.
\tag{2.10}
$$

时间依赖的正演化使 $\Psi_t$ 在共同存在的正时间区间保序。标量解是 $\Psi_t(ru)=r(1+rt)^{-1}u$。对任意 $c\in\mathcal O:=\operatorname{int}C_X$，选 $0<\delta\le R$ 使 $\delta u\le c\le Ru$。比较给

$$
\frac{\delta-1}{1+(\delta-1)t}u
\le\Psi_t(c-u)\le
\frac{R-1}{1+(R-1)t}u\qquad(0\le t\le1).
\tag{2.11}
$$

两端分母在此区间严格为正，故解有统一范数界。双线性场的局部延拓遂保证它存在到 $t=1$。于是对整个 $\mathcal O$ 定义

$$
J(c)=u-\Psi_1(c-u),\qquad
R^{-1}u\le J(c)\le\delta^{-1}u.
\tag{2.12}
$$

$J$ 取值仍在 $\mathcal O$ 且反序。令 $a=c-u$、$b=-\Psi_1(a)=J(c)-u$；路径 $-\Psi_{1-t}(a)$ 同样满足 $x'=-x^2$，从 $b$ 出发到 $-a$。唯一性给 $\Psi_1(b)=-a$，故 $J(J(c))=c$；特别是 $J$ 在整个内部满射。

缩放必须保留单位缺陷。平方齐次性给 $\Psi_t(sa)=s\Psi_{st}(a)$。更一般地，若 $d=1+rt>0$，直接用 $S(u,z)=(I+K)z$ 及 (2.9) 得

$$
\Psi_t(ru+a)=\frac r d u+d^{-2}U_{-2\log d}\Psi_{t/d}(a).
\tag{2.13}
$$

准确的导数核对是：令 $z=d^{-2}U_{-2\log d}\Psi_{t/d}(a)$，则 $z'=-2(r/d)(I+K)z-z^2$，而 $(r/d)'=-(r/d)^2$，所以右端解同一初值方程。恒等式在所示解存在的连通时间区间成立。用于 $ru+a=sc-u$，即 $r=s-1$、$a=s(c-u)$、$t=1$；内层对应时间 $st/(1+(s-1)t)$ 在 $[0,1]$，故 (2.11) 已保证所需存在性。得到全部 $s>0,c\in\mathcal O$ 的精确式

$$
\Psi_1(sc-u)=(1-s^{-1})u+s^{-1}U_{-2\log s}\Psi_1(c-u),
\qquad J(sc)=s^{-1}U_{-2\log s}J(c).
\tag{2.14}
$$

固定 $h>0$，由 $e^hc\ge c$、反序性及 (2.14)，得 $e^{-h}U_{-2h}J(c)\le J(c)$。$J$ 的满射性使它对每个内部元成立；对 $y\in C_X$ 以 $y+\varepsilon u$ 逼近，得到算子序中的

$$
A_h=e^{-h}U_{-2h},\qquad 0\le A_h\le I,\qquad A_hu=e^{-h}u.
\tag{2.15}
$$

现在准确复用正交迹续卷定理 447.1 证明内（该卷式 (447.3)）的二项式正算子刚性，不复用其全效果窗口前件：若 $0\le A\le I$、$Au=\lambda u$，则正算子 $P_{n,k}=\binom nkA^k(I-A)^{n-k}$ 满足 $\sum P_{n,k}=I$、$\sum(k/n)P_{n,k}=A$，且 $\|P_{n,k}\|=\binom nk\lambda^k(1-\lambda)^{n-k}$。由二项式方差得

$$
\|A-\lambda I\|\le
\sum_{k=0}^n|k/n-\lambda|\binom nk\lambda^k(1-\lambda)^{n-k}
\le\sqrt{\lambda(1-\lambda)/n}\longrightarrow0.
\tag{2.16}
$$

所以 $A=\lambda I$。用于 (2.15)，$U_{-2h}=I$ 对每个 $h>0$ 成立；在零处范数微分给 $K=0$，即延拓的同一 $L_u=I$。对每个原 $a\in E$，$S(u,a)$ 与 $a$ 都属于原 $E$，忠实嵌入的单射性给 (2.2)，对称性给另一槽。没有以完成替换原载体，也没有要求 $J$ 的值落回原 $E$。∎

## 3. 单位桥的原公理贡献与未付接口

**定义 3.1（准确前件及文献对应）。** 在总映射入口，复二表的 Hermitian 性、对角正性和 Cauchy–Schwarz 分别供应对称、正平方和范数控制；实相加三角及其零方向供应同一 $S$ 的有理极化；原固定点供应 $Tu=u$；原任意指定的小窗口供应 (2.4)、(2.6) 和零面式 (2.7)。实部换括号式、旧 $D$ 的双线性与 $D_u=0$ 均未参与单位桥。约化入口则已给对称实双线性和正平方，不需要复二表。

序单位完成、零面方法、等距二次流方法和二项式刚性分别复用正交迹续卷定理 446.1、454.1、448.1 证明内的赋范空间子论证及定理 447.1 证明内的二项式计算；该卷定理 455.1 的旧 $D_u$ 谱桥不参与这里的证明。Niestegge §4 Lemma 3 和 Mazur–Ulam 为成熟中间工具。本处 $\texttt{repo-derived}$ 综合是同一平方流在整个完成锥内部的反序对合、保留 $K$ 的缩放公式，以及由满射性取得受 $I$ 支配的正算子从而消去缺陷；不主张历史优先权。

**定义 3.2（一般平方结构仍须识别同一乘法）。** 对完备序单位空间，Roelands–Tiersma，*An order-theoretic characterization of JB-algebras*，[arXiv:2507.09526v3](https://arxiv.org/html/2507.09526v3)，Theorem 1.1、5.34 的成熟接口，以内部锥之间的 gauge-reversing 双射为前件，给指定锥、指定单位的 JB 结构；规范化映射由其导数规定。这个接口只能接在 $K=0$、(2.14) 已成为真正 $-1$ 次齐次反序式之后，不能倒用来证明单位。若用它继续恢复本题平方背景，还须核对其规范化及逆元与这里 $J$ 的对应，并比较原平方流的二阶展开和该 JB 逆元展开，再极化证明所得乘法准确等于原 $S$。单有另一乘法的存在不能完成这项识别；这里不据此另立 JB 推论。

旧 $D$ 的中央中性、实际输出覆盖、线性动力对应及其交换子关系仍各须证明；单位桥本身不给任意旧 $D$ 的 $D(u,a)=0$。三标签卷定理 13.1 的有限 EJA 入口和定理 27.2 的已给 II₁ 背景各保原前件，不能直接升级为一般无限维恢复。完整原来源、联合、仪器、历史及动力学继续按三标签卷定理 29.2 的原消费者条件量化；数学态、$U_t$、$\Psi_t$ 和 $J$ 不供应准备、设备、物理时钟或实际返回。

## 4. 不完备原域中的镜面与平方根边界

**命题 4.1（原多项式载体不被辅助镜面保持）。** 令 $E=\mathbb R[t]|_{[0,1]}$、$C=\{p:p(t)\ge0\ (0\le t\le1)\}$、$u=1$，以原逐点评价定义此锥，$N$ 为一致范数，$S(p,q)=pq$。它满足 2.1 的约化入口，乃至任意指定 $0<\theta\le1$ 的同一窗口；但 $J(1+t)\notin E$，且原正元未必是原 $S$ 平方。因此 2.2 不蕴涵 $J(\mathcal O\cap E)\subseteq E$ 或 $C=\{S(a,a):a\in E\}$。

证明。逐点序给 Archimedean 闭尖生成锥和序单位，乘法对称双线性、平方正且 $1^2=1$；$0\le e\le\theta\le1$ 时逐点有 $e^2\le e$。多项式在 $C([0,1],\mathbb R)$ 中一致稠密，其正锥闭包为连续非负函数锥，故这里 $X=C([0,1],\mathbb R)$。逐点解方程给 $\Psi_1(c-1)=(c-1)/c$，从而 $J(c)=1/c$。特别 $1+t\ge u$ 是内部原元，但若 $J(1+t)=p(t)$ 为多项式，则 $(1+t)p(t)-1$ 在整个区间为零，故为零多项式；代入 $t=-1$ 得矛盾。此处只用多项式恒等原理，不把 $-1$ 加入原评价区间。

原 $t\in C$ 不是任何原多项式的平方：非零平方多项式的次数为偶数，不可能恒等于一次多项式 $t$；严格正的 $1+t$ 同理也无原多项式平方根。并且原多项式列 $p_n(t)=\tfrac12\sum_{k=0}^n((1-t)/2)^k$ 一致收敛到 $1/(1+t)$，显式见证原域不完备。单位等式仍准确在原 $E$ 内成立。这个例子只检验 S-only 单位桥对辅助操作及平方根范围的蕴涵，不声称满足或反驳完整原 $S,D$ 候选。∎

## 5. 完成锥镜面与原单位射线的数学图景

**定义 5.1（反序镜面的图示与直观解释）。** 图中的全部元均在忠实完成的 $\mathcal O=\operatorname{int}C_X$，不是有限维截面；箭头仅表示数学映射。由 (2.12)、(2.14) 及 $K=0$，

$$
\begin{array}{ccccc}
\delta u&\le&c&\le&Ru\\
\big\updownarrow\scriptstyle J&&\big\updownarrow\scriptstyle J&&\big\updownarrow\scriptstyle J\\
\delta^{-1}u&\ge&J(c)&\ge&R^{-1}u
\end{array}
\qquad
ru\ \xleftrightarrow{\ J\ }\ r^{-1}u,\qquad J(u)=u.
\tag{5.1}
$$

同一原平方流把正锥内部做成一面反序镜：沿单位射线，放大变成倒数缩小。证明起初允许缩小之外再带一个 $U_{-2\log s}$ 的扭转，它仅是序单位等距群，不预设 Euclidean 旋转、Hilbert 内积或物理空间维数。反序性与镜面的满射性使缩小后的扭转在整个正锥上夹于零和恒等之间；它在单位上的比例已经固定，二项式刚性遂迫使扭转完全消失。这才锁定原 $S(u,a)=a$，没有借有限对偶积分或另选乘法。

回到原域的只是这个准确单位等式；镜面值及平方根可留在完成中，4.1 给出具体区别。原两张关系中的有向部分、同一复乘法、实际联合和完整设备来源仍承担 3.2 的条件，不由这幅数学镜面代付。

## 追加锚（本行以下为增补区）

## 6. 同一原平方的忠实 JB 完成识别

**定理 6.1（原乘法、原锥与原范数的同一完成）。** 在定义 2.1 的任一原入口下，令 $i:E\to X$、$C_X=\overline{i(C)}^{\,X}$、$\bar N$ 和 $\bar S:X^2\to X$ 分别为定理 2.2 已构造的忠实范数完成、完成锥、原范数延拓和同一原乘法的唯一有界延拓；仍以 $u$ 记 $i(u)$。这些是该定理的输出，不是另加的前提。那么

$$
(X,\bar S,\bar N,u)\ \text{是含单位 JB 代数},\qquad
C_X=\{\bar S(x,x):x\in X\}.
\tag{6.1}
$$

它正是指定完成空间、指定序单位范数、指定单位和指定锥上的唯一 JB 结构，乘法在全部 $X\times X$ 上准确为 $\bar S$。原嵌入满足

$$
\begin{gathered}
i(S(a,b))=\bar S(i(a),i(b)),\qquad
\bar N(i(a))=N(a),\qquad i(C)=i(E)\cap C_X,\\
\overline{\{S(a,a):a\in E\}}^{\,E}=C.
\end{gathered}
\tag{6.2}
$$

因此同一原 $E$ 是其中的稠密含单位 Jordan 子代数；只有原 $E$ 完备时才把它本身称为这个 JB 完成。每个原正实线性评价 $\alpha$ 都有唯一连续正延拓 $\bar\alpha$，满足 $\bar\alpha\circ i=\alpha$ 及 $\bar\alpha(u)=m_\alpha=\alpha(u)$，包括零质量评价，不要求正常性。在总映射入口，三标签卷约定 1.1、定义 8.2–8.4 及定理 29.2 的全部原来源和消费者量词仍逐项保留，原质量与原 $q$ 保持其原定义和原适用域；这里不定义完成上的 $q$。无限支撑输入没有被有限截面替换，也不要求原域对逆元或平方根封闭。

证明。$E=0$ 时完成及全部等式均为零，以下设 $E\ne0$。定理 2.2 已经给出 $\bar N(u)=1$、$\bar S(u,x)=x$、$C_X\cap i(E)=i(C)$，且 $(X,C_X,u)$ 是完备 Archimedean 序单位空间，其序单位范数就是 $\bar N$。置 $M=M_\theta=2/\theta-1\ge1$，该定理的有界性给

$$
\bar N(\bar S(x,y))\le M\bar N(x)\bar N(y)
\quad(x,y\in X).
\tag{6.3}
$$

记 $\mathcal O=\operatorname{int}C_X$。原平方方程 $z'=-\bar S(z,z)$ 的流仍记 $\Psi_t$；定理 2.2 的 (2.12)、(2.14) 在已经证得 $K=0$ 后给出整个内部上的映射

$$
J(c)=u-\Psi_1(c-u),\qquad
J^2=I_{\mathcal O},\qquad J(u)=u,\qquad
J(sc)=s^{-1}J(c)\quad(s>0).
\tag{6.4}
$$

$J$ 反序且为双射，由对合性，其逆也反序。因此这里已具备原完成锥内部的反序同构和准确的 $-1$ 次齐次性；它们不是对原 $E$ 增加的假设。按 Roelands–Tiersma，*An order-theoretic characterization of JB-algebras*，[arXiv:2507.09526v3](https://arxiv.org/html/2507.09526v3)，Proposition 2.22，$J:\mathcal O\to\mathcal O$ 是 gauge-reversing 双射。

先直接从同一原平方核对规范化所需的导数，并保留足够强的余项。取 $h\in X$，令 $r=\bar N(h)<1/(8M)$，故 $u+h\in\mathcal O$。$h=0$ 时下列式子显然成立；否则令 $z(t)=\Psi_t(h)$，其积分方程为

$$
z(t)=h-\int_0^t\bar S(z(s),z(s))\,ds.
\tag{6.5}
$$

在 $0\le t\le1$ 上有 $\bar N(z(t))\le2r$：若首次达到 $2r$，此前 (6.3)、(6.5) 给 $\bar N(z(t))\le r+4Mr^2t\le3r/2$，矛盾。有界双线性场在此球上有统一 Lipschitz 界，解和导数有界；故有限端点处存在范数极限并可由局部存在定理延拓，排除了在 $t=1$ 前终止。于是整个区间还有

$$
\begin{aligned}
\bar N(z(t)-h)&\le4Mr^2t,\\
\bar N\bigl(\bar S(z(t),z(t))-\bar S(h,h)\bigr)
&\le M\bar N(z(t)-h)\bigl(\bar N(z(t))+r\bigr)
\le12M^2r^3t.
\end{aligned}
\tag{6.6}
$$

将第二行代回积分方程并积分到 $1$，得到球上一致展开

$$
J(u+h)=u-h+\bar S(h,h)+R_S(h),\qquad
\bar N(R_S(h))\le6M^2\bar N(h)^3.
\tag{6.7}
$$

这只用了原乘法的有界实双线性，没有使用 Jordan 律或幂结合性。特别地，余项及 (6.3) 给出真正的 Fréchet 导数 $\mathrm dJ_u=-I_X$；这里 $\mathrm d$ 是该数学映射的微分，和旧二元关系 $D$ 无关。

现在只在完备空间 $X$ 上调用上述文献 Theorem 5.34。其参数对应为 $V=W=X$、$V_+=W_+=C_X$、$v=w=u$、两个开锥均为 $\mathcal O$，$\Phi=J$；$J(u)=u$ 也已由 (6.4) 给出。Theorem 5.34(3)–(5) 给同一序单位空间上的唯一 JB 乘法，暂记 $\bullet$，单位为 $u$，平方锥为 $C_X$，且其内部逆元映射准确为

$$
j=-[\mathrm dJ_u]^{-1}\circ J=J.
\tag{6.8}
$$

其 JB 范数正是指定的序单位范数 $\bar N$，这也是该文 Theorem 1.1 的范数表述。这里只复用完整空间重构及其导数规范化，不应用要求原内部镜面取值仍在原域的非完备空间结论。尤其 (6.8) 还没有自行识别原 $\bar S$；下一步才补这一点。

在这个暂记乘法的 JB 代数中，$u$ 与任意单个 $h$ 生成的闭含单位子代数是结合的；这是成熟 JB 单元素生成函数演算，也是该文 Theorem 5.34 证明中使用 Hua 恒等式的同一背景。以 $h^{\bullet0}=u$、$h^{\bullet1}=h$ 记其幂。当 $r=\bar N(h)<1$ 时，Neumann 级数在此子代数收敛并给 $u+h$ 的逆元。由 JB 乘法的范数不等式，尾项满足

$$
\begin{aligned}
J(u+h)=j(u+h)
&=\sum_{n=0}^{\infty}(-1)^nh^{\bullet n}
=u-h+h\bullet h+R_J(h),\\
\bar N(R_J(h))&\le\sum_{n=3}^{\infty}r^n
=\frac{r^3}{1-r}.
\end{aligned}
\tag{6.9}
$$

此处仅对已经重构出的 $\bullet$ 使用幂结合性；没有预设原 $\bar S$ 具备它。现在 (6.7) 与 (6.9) 是同一个 $J$ 在同一个 $X$、同一个范数中的展开。在 $r<1/(8M)$ 内相减，得到

$$
\bar N\bigl(\bar S(h,h)-h\bullet h\bigr)
\le\left(6M^2+\frac1{1-r}\right)r^3.
\tag{6.10}
$$

固定任意 $a\in X$，取 $h=ta$ 并令非零实数 $t\to0$。两种乘法的实双线性使左侧等于 $t^2\bar N(\bar S(a,a)-a\bullet a)$；右侧除以 $t^2$ 后趋于零，故 $\bar S(a,a)=a\bullet a$ 对每个 $a\in X$ 成立。对任意 $x,y\in X$ 极化即得

$$
\begin{aligned}
\bar S(x,y)
&=\tfrac12\bigl(\bar S(x+y,x+y)-\bar S(x,x)-\bar S(y,y)\bigr)\\
&=\tfrac12\bigl((x+y)\bullet(x+y)-x\bullet x-y\bullet y\bigr)
=x\bullet y.
\end{aligned}
\tag{6.11}
$$

这证明的是全部完成元素对上的准确等式，而非只在正元、有限支撑或某个稠密子集上相同。成熟重构所给的 Jordan 律、JB 范数性质和平方锥现在都属于原有界延拓 $\bar S$；特别 $\bar N(\bar S(x,y))\le\bar N(x)\bar N(y)$ 及 $\bar N(\bar S(x,x))=\bar N(x)^2$。于是 (6.1) 及所述唯一性成立。

回到原域，延拓的定义已给 (6.2) 前三项：原 $S(a,b)$ 本来就在 $E$，(6.11) 说明其像正是完成的 JB 乘积，故 Jordan 恒等式由嵌入单射性返回原 $E$；范数与锥也忠实返回，没有另选原乘法或原正锥。为证明最后一项，取任意 $c\in C$，在完成的 JB 代数中取 $b$ 使 $\bar S(b,b)=i(c)$，再由稠密性取 $i(a_n)\to b$。连续性给 $i(S(a_n,a_n))\to i(c)$，等距性使 $S(a_n,a_n)\to c$ 在原 $N$ 中成立；反向包含来自原平方正性与 $C$ 在 $E$ 中闭。这里取平方根及求极限均在完成中进行，不声称 $b\in i(E)$。因此 $C$ 是原平方集在原域内的闭包，未必就是原平方集；逆元和平方根是否返回原域仍受 4.1 的边界限制。

最后，对任意原正实线性评价 $\alpha$，原序单位界给

$$
|\alpha(a)|\le m_\alpha N(a),\qquad
\bar\alpha(i(a))=\alpha(a),\qquad
\bar\alpha(u)=m_\alpha,\qquad
\bar\alpha\bigl(\bar S(i(a),i(b))\bigr)=\alpha(S(a,b)).
\tag{6.12}
$$

第一式由 $-ru\le a\le ru$ 及 $r\downarrow N(a)$ 得出，故完成的泛函延拓唯一；其在 $C_X$ 上正来自 $i(C)$ 的稠密性。$m_\alpha=0$ 时第一式强制原评价及其延拓恒零，无须也不能除以该质量。这适用于全部原正评价，而非只选一个忠实态、正常态或归一化子族。于是全部原评价、原质量及原乘积读数都逐点保留；没有改变原 $q$ 的定义、权或量词，也没有把新的数学态加入原准备。

本条 $\texttt{repo-derived}$ 内容是把原平方流的统一二阶项、其准确导数规范化和完成逆元的二阶项接在同一原载体及乘法上，支付第 1 章及 3.2 在定义 2.1 范围内留下的 JB 识别接口。一般 gauge-reversing 重构、JB 单元素生成演算与 Neumann 级数是证明内复用的成熟工具，不作为本仓新增的一般定理或历史优先权主张。结论始终是原平方前件下的纸面条件命题；不声称无这些前件的一般无限 raw $S$ 已恢复为 JB，也不声称实际物理来源满足这些前件。旧 $D$ 的中央中性、实际输出覆盖、双线性、连续性、正常性、动力对应及交换子条件均未由本条支付；同一复乘法的一般复 $C^*$ 恢复仍需自己的前件。三标签卷约定 1.1、定义 8.2–8.4 及定理 29.2 中原准备、设备、完整仪器与细记录、真实相关联合、全部合法顺序／自适应／并行历史及其全部仍合法未来、失败／拒绝／停止／销毁、真正遗忘和各类实际返回，均保其原类型、原来源及原消费者的全部量词。指定正规表示与前对偶、非离散记录、可数可加性、无限历史，以及原物理钟、强连续酉实现、Hamiltonian 能量和共同作用量单位 $\hbar$ 也仍需各自原对应；本条的数学完成、微分和逆元均不供应这些对象。∎

## 追加锚（本行以下为增补区）
