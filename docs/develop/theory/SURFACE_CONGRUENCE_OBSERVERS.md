# 曲面群的有限非交换观察与分离扭转

## 1. 曲面表示与单一动力

**定义。** 固定整数 $g\ge2$，令

$$\Pi_g=\langle a_1,b_1,\ldots,a_g,b_g\mid
[a_1,b_1]\cdots[a_g,b_g]=1\rangle,$$

其中 $[u,v]=uvu^{-1}v^{-1}$，乘积按指标递增排列。记 $h=[a_1,b_1]$，定义生成元上的映射

$$\tau(a_1)=ha_1h^{-1},\qquad \tau(b_1)=hb_1h^{-1},$$

$$\tau(a_i)=a_i,\qquad\tau(b_i)=b_i\quad(2\le i\le g).$$

**命题。** 该映射延拓为 $\Pi_g$ 的自同构。它固定 $h$；其逆将第一对生成元以 $h^{-1}$ 共轭。因此，对于每个整数 $n$，$\tau^n$ 将第一对生成元以 $h^n$ 共轭并固定其他生成元。

**证明。** 第一对像的交换子为 $h[a_1,b_1]h^{-1}=h$，其余交换子不变，故原关系保持。以 $h^{-1}$ 共轭同样保持关系；因为两映射均固定 $h$，复合在全部生成元上为恒等。由生成性质得到逆映射。正幂归纳和逆映射给出整数幂公式。

**命题。** 对任意交换群 $A$ 和同态 $f:\Pi_g\to A$，都有 $f\circ\tau=f$。

**证明。** $f(h)=1$，故第一对生成元及其余所有生成元的像不变。

## 2. 一个具有准确返回周期的有限表示族

**定义。** 对正整数 $m$，令

$$D_m=\langle r,s\mid r^{4m}=s^2=1,\ srs=r^{-1}\rangle.$$

这里旋转 $r$ 的阶为 $4m$，群的阶为 $8m$。每个元素唯一写为 $r^j$ 或 $sr^j$，指数属于 $\mathbb Z/(4m)$。

**引理。** $D_m$ 中每个交换子都是 $r^{2t}$ 的形式。因此每个交换子的 $m$ 次幂位于中心。

**证明。** 按两个元素分别为旋转或反射分类，交换子指数分别为 $0$、$2i$、$-2j$、$2(j-i)$。$r^{2tm}$ 与全部旋转交换；与反射交换的条件是其指数的两倍为 $0$ 模 $4m$，此条件成立。

**定理。** 对任意同态 $\rho:\Pi_g\to D_m$，有 $\rho\circ\tau^m=\rho$。更一般地，$m\mid n$ 推出 $\rho\circ\tau^n=\rho$。

**证明。** $\rho(h)^m$ 位于中心，故 $\rho(h)^n$ 在 $m\mid n$ 时也位于中心。代入第一对生成元的共轭公式，其像不变；其他生成元一直固定。

**定义。** 令 $\rho_m:\Pi_g\to D_m$ 的生成元像为

$$\rho_m(a_1)=s,\quad\rho_m(b_1)=r,\quad
\rho_m(a_2)=r,\quad\rho_m(b_2)=s,$$

其余生成元的像为单位元。

**命题。** 该同态良定义，且对每个整数 $n$，

$$\rho_m(\tau^n(a_1))=sr^{4n},\qquad
\rho_m(\tau^n(b_2))=s.$$

**证明。** 前两个交换子分别为 $r^{-2}$ 和 $r^2$，其余交换子为单位元，因此原关系保持。$\rho_m(h)=r^{-2}$，故第一式为 $r^{-2n}sr^{2n}=sr^{4n}$。第二个把手固定，给出第二式。

**定理。** 存在一个 $u\in D_m$ 使

$$\rho_m(\tau^n(x))=u\rho_m(x)u^{-1}\quad\text{对所有 }x\in\Pi_g$$

当且仅当 $m\mid n$。

**证明。** 若存在这样的共同共轭元，因为 $\rho_m(a_1)=\rho_m(b_2)$，变换后二者也必须有相同的像。于是 $sr^{4n}=s$，即 $4m\mid4n$，等价于 $m\mid n$。反之，上一项定理表明 $m\mid n$ 时全部像已经相等，取 $u=1$ 即可。

## 3. 从全部表示构造真正的特征商

**定义。** 令 $\mathcal R_{g,m}=\operatorname{Hom}(\Pi_g,D_m)$，定义

$$E_{g,m}:\Pi_g\longrightarrow D_m^{\mathcal R_{g,m}},\qquad
E_{g,m}(x)(\rho)=\rho(x).$$

令 $Q_{g,m}=\operatorname{im}E_{g,m}$，并将像限制映射记为 $q_{g,m}:\Pi_g\twoheadrightarrow Q_{g,m}$。其核为

$$N_{g,m}=\bigcap_{\rho\in\mathcal R_{g,m}}\ker\rho.$$

**定理。** $Q_{g,m}$ 有限，$N_{g,m}$ 在 $\Pi_g$ 的所有自同态下保持不变。特别地，$N_{g,m}$ 为特征子群。

**证明。** 每个同态由 $2g$ 个生成元的像唯一确定，因此
$|\mathcal R_{g,m}|\le(8m)^{2g}$，评价映射的目标为有限群。若 $x\in N_{g,m}$，则对每个自同态 $f$ 及每个 $\rho$，$\rho(f(x))=(\rho\circ f)(x)=1$，因为 $\rho\circ f$ 仍属于同一个表示族。故 $f(N_{g,m})\subseteq N_{g,m}$。对自同构及其逆同时应用此包含即得特征性。

**定理。** $\tau$ 在 $Q_{g,m}$ 上诱导自同构 $T_{g,m}$，满足

$$T_{g,m}q_{g,m}=q_{g,m}\tau.$$

对每个整数 $n$，有

$$\boxed{T_{g,m}^n\text{ 为内自同构}\quad\Longleftrightarrow\quad m\mid n.}$$

当 $m\mid n$ 时，$T_{g,m}^n$ 实际上为恒等映射。因此 $T_{g,m}$ 在自同构群以及外自同构群中的阶都恰为 $m$。

**证明。** 核的特征性给出良定义的诱导自同构；满射性保证唯一性。若 $m\mid n$，上一节的结论对全部表示同时成立，故评价向量不变。若 $T_{g,m}^n$ 为某个 $z\in Q_{g,m}$ 的内共轭，将评价向量投影到坐标 $\rho_m$，得到上一节所排除的共同共轭，除非 $m\mid n$。对负幂取逆，将结论化为正幂情形。

**推论。** $[\tau]$ 在 $\operatorname{Out}(\Pi_g)$ 中具有无限阶。每个子群 $m\mathbb Z$ 都恰好是由特征商 $Q_{g,m}$ 所诱导的映射

$$\mathbb Z\longrightarrow\operatorname{Out}(\Pi_g)
\longrightarrow\operatorname{Out}(Q_{g,m})$$

的核。

**证明。** 若非零整数 $n$ 给出内自同构，取 $m>|n|$，其在 $Q_{g,m}$ 上的像仍为内自同构，与准确阶判据矛盾。核的描述直接来自该判据。

## 4. 共同观察与单独选取代表的区别

**命题。** 单个 $\rho_m$ 的核无需是特征子群，亦无需被 $\tau$ 保持。其表示类的返回条件仍可用于证明特征商上的非内性。

**证明。** 特征商通过全部表示的共同核定义，故任何一个表示均经 $q_{g,m}$ 因子化。若特征商上的作用为内共轭，该因子化强制单个表示也满足同一个共轭关系。逆向推理没有被使用。特别地，只在每个生成元上分别寻找共轭元不提供所需的共同共轭关系。

**命题。** 存在所有交换目标都无法识别、但一个有限非交换特征商可以识别的自同构：对 $m>1$，$\tau$ 具有此性质。

**证明。** 第一节给出交换观察不变性，第三节给出 $T_{g,m}$ 的非内性。

## 5. 一个混合词的共轭类轨道

**定义。** 令 $w=a_1b_2^{-1}$，并令 $[q_{g,m}(w)]$ 表示其在 $Q_{g,m}$ 中的共轭类。

**定理。** 对每个整数 $n$，

$$\boxed{q_{g,m}(\tau^n(w))\text{ 与 }q_{g,m}(w)\text{ 共轭}
\quad\Longleftrightarrow\quad m\mid n.}$$

**证明。** 在已构造的表示 $\rho_m$ 下，$\rho_m(w)=1$，而

$$\rho_m(\tau^n(w))=(sr^{4n})s=r^{-4n}.$$

如果两个商元素共轭，它们经任一坐标同态后的像也共轭。单位元只与自身共轭，因此 $r^{-4n}=1$，即 $m\mid n$。反之，$m\mid n$ 时 $T_{g,m}^n$ 为恒等映射。负幂结论由诱导自同构的可逆性得到。

**推论。** 对任意整数 $p,n$，两个共轭类
$[q_{g,m}(\tau^p(w))]$ 与 $[q_{g,m}(\tau^n(w))]$ 相同，当且仅当 $p\equiv n\pmod m$。特别地，这个共轭类的轨道恰有 $m$ 个元素。

**证明。** 对两个类同时施加 $T_{g,m}^{-p}$，再应用定理。

## 6. 同一个特征商的多项式规模上界

**定义。** 令

$$K_g=\ker\left(\Pi_g\longrightarrow(\mathbb Z/2)^{2g}\right),$$

其中每个生成元映到相应的标准基向量。此映射是满射，且任一到二阶循环群的同态都经它因子化。记

$$d_g=2^{2g},\qquad s_g=1+d_g(2g-1).$$

**引理。** $K_g$ 可由至多 $s_g$ 个元素生成。

**证明。** 在 $d_g$ 个陪集上构造由 $2g$ 个原生成元标记的 Schreier 图。它连通，有 $d_g$ 个顶点及 $2g d_g$ 条生成元边。选一棵生成树，由根到每个顶点的树路径给出陪集代表。对每条非树边，先沿树走到其起点，经过该边，再沿树返回根，得到一个属于 $K_g$ 的元素。沿任意代表 $K_g$ 元素的闭路径逐边插入树路径及其逆，得到这些元素及其逆的乘积。因此非树边对应的元素生成 $K_g$，其数目至多 $2g d_g-(d_g-1)=s_g$。原曲面关系只会增加生成元素之间的关系，不会破坏这个上界。

**定义。** $K_g^{4m}$ 表示由 $K_g$ 中所有 $4m$ 次幂生成的子群，令

$$L_{g,m}=[K_g,K_g]K_g^{4m}.$$

**定理。** $L_{g,m}$ 是 $\Pi_g$ 的特征子群，而且

$$L_{g,m}\subseteq N_{g,m}.$$

因此同一个评价像商满足

$$\boxed{|Q_{g,m}|\le 2^{2g}(4m)^{1+2^{2g}(2g-1)}.}$$

**证明。** $K_g$ 是全部到 $\mathbb Z/2$ 的同态之核的交，故为特征子群。交换子子群和幂子群均为 $K_g$ 的特征子群，因此 $L_{g,m}$ 在 $\Pi_g$ 的自同构下保持不变。

对任意 $\rho:\Pi_g\to D_m$，复合 $D_m\to D_m/\langle r\rangle\cong\mathbb Z/2$ 可经定义 $K_g$ 的映射因子化，所以 $\rho(K_g)\subseteq\langle r\rangle$。旋转群交换且指数为 $4m$，因此 $\rho$ 消去 $[K_g,K_g]$ 和 $K_g^{4m}$。对全部 $\rho$ 取交，得到 $L_{g,m}\subseteq N_{g,m}$。

$K_g/L_{g,m}$ 是由至多 $s_g$ 个元素生成、指数整除 $4m$ 的交换群，所以它是 $(\mathbb Z/(4m))^{s_g}$ 的商，阶至多为 $(4m)^{s_g}$。由 $[\Pi_g:K_g]=d_g$，得到

$$|\Pi_g/L_{g,m}|\le d_g(4m)^{s_g}.$$

而 $Q_{g,m}$ 是 $\Pi_g/L_{g,m}$ 的商，故具有同一个上界。此论证只用中间商控制大小；没有断言 $\tau$ 在中间商 $\Pi_g/L_{g,m}$ 上恰有阶 $m$。

## 7. 有界整数参数的精确有限观察

**定理。** 固定整数 $H\ge0$，取 $m=2H+1$。映射

$$n\longmapsto[q_{g,m}(\tau^n(w))],\qquad -H\le n\le H,$$

是单射。实现这一观察的群可以取第 3 节的同一个 $Q_{g,m}$，其大小满足

$$|Q_{g,2H+1}|\le
2^{2g}\bigl(4(2H+1)\bigr)^{1+2^{2g}(2g-1)}.$$

**证明。** 两个观察相同，当且仅当 $m$ 整除参数差。该差的绝对值至多为 $2H<m$，因此只有差为零的可能。大小界代入上一节。此处观察是带有已固定曲面标记和自同构标记的精确共轭类数据，不含测量噪声或运行时间假设。

**命题。** 不限制整数参数时，任何固定 $m$ 的该观察均不单射；所有正整数 $m$ 的联合观察是单射。

**证明。** 固定 $m$ 时参数 $n$ 与 $n+m$ 同像。若两个整数的全部观察相同，则其差被每个正整数整除，取大于差的绝对值的模数即得差为零。

## 8. 共享未扭转把手的多方向检测

**定义。** 固定 $1\le r<g$。对 $1\le i\le r$，令 $h_i=[a_i,b_i]$，并定义 $\tau_i$ 将第 $i$ 对生成元以 $h_i$ 共轭、固定其余生成元。第 $r+1$ 个把手保持不动，作为共同参照。记

$$\tau^{\boldsymbol n}=\tau_1^{n_1}\cdots\tau_r^{n_r},\qquad
\boldsymbol n\in\mathbb Z^r.$$

**定理。** 这些自同构两两交换。它们在同一个 $Q_{g,m}$ 的外自同构群中诱导的映射具有核 $m\mathbb Z^r$，因而像同构于 $(\mathbb Z/m)^r$。

**证明。** 各自同构固定全部 $h_j$，且只作用于自己的生成元对，故在生成元上两两交换。若每个 $n_i$ 都是 $m$ 的倍数，任意二面体表示下各共轭元均位于中心，因此联合变换在评价像上为恒等。

反之，对每个 $i$，取一个表示，将第 $i$ 个把手映为 $(s,r)$，参照把手映为 $(r,s)$，其余全部映为单位元。两项非平凡交换子相消，故表示良定义。联合变换后，第 $i$ 个把手的第一个像为 $sr^{4n_i}$，参照把手的第二个像仍为 $s$。一个共同内共轭只能在 $m\mid n_i$ 时实现。逐个 $i$ 检验得到精确核。条件 $r<g$ 保证参照把手没有同时被扭转。

## 9. 轨道合同控制的剩余群论条件

**命题。** 设群 $\Lambda$ 作用于集合 $X$，$\alpha\in X$，$H=\operatorname{Stab}_\Lambda(\alpha)$。对任意子群 $\Gamma,\Delta\le\Lambda$，

$$\Delta\alpha\subseteq\Gamma\alpha
\quad\Longleftrightarrow\quad\Delta\subseteq\Gamma H.$$

当 $\Gamma$ 正规时，$\Gamma H$ 本身为子群。

**证明。** $\delta\alpha\in\Gamma\alpha$ 当且仅当存在 $\gamma\in\Gamma$ 使 $\gamma^{-1}\delta\in H$，亦即 $\delta\in\Gamma H$。正规性保证子群乘积闭合。

**命题。** 对由有限特征商定义的合同子群族，要使上述轨道包含对所有有限指数 $\Gamma$ 成立，只需且必须能为每个这样的轨道条件找到一个主合同核 $C$，使

$$C\subseteq\Gamma H.$$

只研究 $C\cap\langle\tau\rangle$ 并不能推出此包含。

**证明。** 每个合同子群都包含相应的主合同核，故从轨道包含可以缩小到主核；反向取 $\Delta=C$ 即可。交于循环子群的条件只限制该循环子群中的元素，未限制 $C$ 在其余陪集中的元素。作为纯群作用的例子，令 $\Lambda=\mathbb Z^2$ 通过平移作用于自身，$\alpha=0$，$\Gamma=2\mathbb Z\times2\mathbb Z$，$A=\mathbb Z\times\{0\}$，$C=2\mathbb Z\times\mathbb Z$；则 $C\cap A\subseteq\Gamma$，但 $C\not\subseteq\Gamma$。这里 $\Gamma,C$ 均为有限指数子群；该例只说明给定 $C$ 的交集条件不足以推出所需包含，不否定其他主核的存在。


## 10. 二面体观察族不可越过的导出层边界

**定义。** 对任意群 $G$，令 $G'=[G,G]$，$G''=[G',G']$。商 $G/G''$ 的交换子子群是交换群，称为最大亚交换商。

**命题。** 对每个正整数 $m$，都有

$$\Pi_g''\subseteq N_{g,m}.$$

因此，即使联合全部模数，第 3 节的观察仍经过同一个商 $\Pi_g/\Pi_g''$ 因子化。

**证明。** 二面体群 $D_m$ 的交换子子群包含于旋转群，因而本身交换。对每个同态 $\rho:\Pi_g\to D_m$，有 $\rho(\Pi_g')\subseteq D_m'$，于是 $\rho(\Pi_g'')\subseteq[D_m',D_m']=1$。对全部表示取核的交，再对任意正模数应用，即得结论。

**命题。** 如果 $f\in\operatorname{Aut}(\Pi_g)$ 在 $\Pi_g/\Pi_g''$ 上诱导恒等映射，那么它在每个 $Q_{g,m}$ 上也诱导恒等映射。如果它在 $\Pi_g/\Pi_g''$ 上诱导内自同构，那么它在每个 $Q_{g,m}$ 上亦诱导内自同构。特别地，

$$\ker\left(\operatorname{Out}(\Pi_g)\to\operatorname{Out}(\Pi_g/\Pi_g'')\right)
\subseteq\bigcap_{m\ge1}\ker\left(\operatorname{Out}(\Pi_g)\to\operatorname{Out}(Q_{g,m})\right).$$

**证明。** 恒等情形有 $f(x)x^{-1}\in\Pi_g''\subseteq N_{g,m}$，故 $q_{g,m}(f(x))=q_{g,m}(x)$。内自同构情形，取其在 $\Pi_g/\Pi_g''$ 上的共同共轭元，并提升为 $z\in\Pi_g$；则 $f(x)$ 与 $zxz^{-1}$ 的差属于 $\Pi_g''$。通过每个 $q_{g,m}$ 后差消失，且共同共轭元为 $q_{g,m}(z)$。特征性保证所写外自同构群映射良定义。

**推论。** 对一个具体非单位的 $u\in\Pi_g''$，任何二面体观察都满足 $\rho(u)=1$。一个同态 $\sigma:\Pi_g\to F$ 若满足 $\sigma(u)\ne1$，则 $F''\ne1$。

**证明。** 第一项由上述包含得到。若 $F''=1$，则任意同态都把 $\Pi_g''$ 映到 $F''$，与 $\sigma(u)\ne1$ 矛盾。此命题是目标群所需表达能力的必要条件；它本身不构造满足条件的有限目标，也不断言所写外自同构核中存在指定非平凡映射类。

## 11. 第二导出层中一个具体词的动力学深度

**定义。** 固定 $g\ge3$，保留第 1 节的群 $\Pi_g$、边界词 $h$ 和自同构 $\tau$。令

$$u=[[a_1,a_2],[b_1,b_3]],\qquad \delta=\tau(u)u^{-1}.$$

令 $\gamma_1G=G$，$\gamma_{j+1}G=[G,\gamma_jG]$ 为下中心列。于是 $u\in\Pi_g''\subseteq\gamma_4\Pi_g$。

**引理。** 若群自同构 $f$ 在 $G/\gamma_3G$ 上为恒等，则对每个 $j\ge1$ 和 $x\in\gamma_jG$，有

$$f(x)x^{-1}\in\gamma_{j+2}G.$$

**证明。** $j=1$ 是假设。利用 $[\gamma_rG,\gamma_sG]\subseteq\gamma_{r+s}G$，若 $x\in\gamma_jG$，则在模 $\gamma_{j+3}G$ 意义下，$f([y,x])=[y,x]$：替换 $y$ 所引入的修正属于 $\gamma_3G$，与 $x$ 的交换子属于 $\gamma_{j+3}G$；替换 $x$ 的修正属于 $\gamma_{j+2}G$，与 $y$ 的交换子也属于同一项。用交换子的乘积展开恒等式可得到这两个包含；额外共轭不会改变正规子群的包含。该性质对乘积和逆保持，故从生成 $\gamma_{j+1}G$ 的全部 $[y,x]$ 推出下一层。下中心列交换子包含本身由交换子恒等式及三子群引理归纳得到。

**定理。** 对所定义的 $u,\delta$，有

$$\delta\in\Pi_g''\cap\gamma_6\Pi_g,\qquad
\tau(\delta)\delta^{-1}\in\gamma_8\Pi_g.$$

若 $F$ 的幂零类至多为 5，则每个同态 $\sigma:\Pi_g\to F$ 对全部整数 $n$ 满足

$$\sigma(\tau^n(u))=\sigma(u).$$

**证明。** $h\in\gamma_2\Pi_g$，所以被改变的生成元的差为 $[h,a_1]$ 或 $[h,b_1]$，属于 $\gamma_3\Pi_g$；其余生成元不变。上述引理在 $j=4$ 和 $j=6$ 给出两个下中心列包含。第二导出子群为特征子群，故 $\delta\in\Pi_g''$。在 $G/\gamma_6G$ 中，$\tau$ 固定 $u$；其任意正负幂同样固定 $u$。幂零类至多为 5 的每个表示消去 $\gamma_6G$，得到结论。这一结论说像不随时间变化，不要求其值本身为单位元。

**命题。** 若 $F''=1$，则每个 $\sigma:\Pi_g\to F$ 满足 $\sigma(\tau^n(u))=1$，对所有整数 $n$ 成立。

**证明。** $\tau^n(u)$ 始终属于特征子群 $\Pi_g''$，其像属于 $F''$。

## 12. 不除以整数的七维表示族

**定义。** 对交换环 $R$，用一基指标的矩阵单位 $E_{ij}$，令

$$A=I+E_{12}+E_{23}+E_{34}+E_{56},\qquad
B=I+E_{45}+E_{67},\qquad H=[A,B],\quad N=H-I.$$

这些矩阵属于 $U_7(R)$，即对角线全为 1 的上三角矩阵群。定义

$$P(t,s)=I+tN+sN^2\qquad(t,s\in R).$$

**命题。** 有

$$N=E_{35}-E_{36}+E_{37}-E_{46}+E_{47}+E_{57},\qquad
N^2=E_{37},\qquad N^3=0,$$

$$P(t,s)P(v,w)=P(t+v,s+w+tv),\qquad
P(t,s)^{-1}=P(-t,t^2-s).$$

此外，$H=P(1,0)$，所有 $P(t,s)$ 与 $H$ 交换；对自然数 $n$，

$$H^n=P\left(n,\sum_{j=0}^{n-1}j\right).$$

**证明。** 用 $E_{ij}E_{kl}=0$（$j\ne k$）和 $E_{ij}E_{jl}=E_{il}$ 展开 $ABA^{-1}B^{-1}$，得到 $N$ 的表达式，再得其平方与立方。乘法公式由 $N^3=0$ 展开，逆矩阵公式代入即可。交换性由乘法公式和 $R$ 交换性得到；幂公式对 $n$ 归纳。公式没有用到 $2$ 的可逆性。

**命题。** 对所有 $t,s\in R$，有准确矩阵恒等式

$$\boxed{[[P(t,s)AP(t,s)^{-1},A],
[P(t,s)BP(t,s)^{-1},A]]=I-tE_{17}.}$$

**证明。** $A-I$ 的四次幂为零，$B-I$ 的平方为零，因此

$$A^{-1}=I-(A-I)+(A-I)^2-(A-I)^3,\qquad B^{-1}=I-(B-I).$$

将这些有限表达式和 $P(-t,t^2-s)$ 代入左边两个内交换子，再代入外交换子，逐项使用矩阵单位乘法。对角元均为 1，所有非对角元除 $(1,7)$ 外都为 0，该位置剩余系数为 $-t$；含 $s$ 的项相消。这是 $\mathbb Z[t,s]$ 中的矩阵多项式恒等式，经标准环同态输运到任意 $R$。

**定义。** 对任意 $t\in R$，给前三个把手指定像

$$(a_1,b_1)\mapsto(P(t,0)AP(t,0)^{-1},P(t,0)BP(t,0)^{-1}),$$

$$(a_2,b_2)\mapsto(A,I),\qquad (a_3,b_3)\mapsto(B,A),$$

其余把手的像为 $(I,I)$。

**定理。** 这些像定义同态 $\rho_t:\Pi_g\to U_7(R)$，且对全部整数 $n$ 有

$$\boxed{\rho_t(\tau^n(u))=I-(n+t)E_{17}.}$$

**证明。** 前三个像的交换子分别为 $H,1,H^{-1}$。第一项等于 $H$ 使用了 $P(t,0)$ 与 $H$ 交换，故曲面关系准确成立。同时 $\rho_t(h)=H$。对自然数 $n$，原动力学将第一对像再次以 $H^n$ 共轭，合并共轭矩阵后得到

$$H^nP(t,0)=P\left(n+t,\sum_{j=0}^{n-1}j+nt\right).$$

代入上一项双交换子恒等式即可。对负 $n$ 使用 $H^{-1}=P(-1,1)$ 和同一个乘法公式，第一坐标仍为 $n+t$；第二坐标不影响最终读数。

## 13. 全部矩阵表示给出的特征性有限时间分离

**定义。** 对正整数 $m$，令 $F_m=\operatorname{GL}_7(\mathbb Z/m)$，并定义

$$E^{\rm mat}_{g,m}:\Pi_g\longrightarrow
F_m^{\operatorname{Hom}(\Pi_g,F_m)},\qquad
E^{\rm mat}_{g,m}(x)(\rho)=\rho(x).$$

令 $Q^{\rm mat}_{g,m}=\operatorname{im}E^{\rm mat}_{g,m}$，$q^{\rm mat}_{g,m}$ 为像限制满射。

**定理。** $Q^{\rm mat}_{g,m}$ 有限，其投影核在全部自同态下保持不变。对任意整数 $p,n$，

$$q^{\rm mat}_{g,m}(\tau^n(u))\sim
q^{\rm mat}_{g,m}(\tau^p(u))
\quad\Longrightarrow\quad n\equiv p\pmod m,$$

其中 $\sim$ 表示在同一个商群中的共轭。

**证明。** $F_m$ 有限，且每个表示由 $2g$ 个生成元的像唯一决定，所以表示集合及评价像均有限。核的不变性依然来自表示族对预复合的闭合性。对假设的共轭关系，取其中坐标 $\rho_{-p}$。第 $p$ 次像成为 $I$，第 $n$ 次像成为 $I-(n-p)E_{17}$。单位元的共轭类只有单位元，故 $(1,7)$ 元强制 $n-p=0$ 模 $m$。这里不需要猜测一般非单位矩阵的共轭类。

**推论。** 对自然数 $0\le p,n<m$，上述共轭成立当且仅当 $p=n$。更一般地，固定整数 $H_0\ge0$ 并取 $m=2H_0+1$，区间 $[-H_0,H_0]$ 上的整数参数由该共轭类读出唯一确定。

**证明。** 必要性由余数相等和参数差的严格大小界得到。充分性在参数相等时取恒等共轭。

## 14. 单位上三角特征商的准确周期与六类阈值

**定义。** 用 $V_m=U_7(\mathbb Z/m)$ 替换上一节的全部可逆矩阵群，定义同样的评价像商 $Q^{\rm ut}_{g,m}$ 和满射 $q^{\rm ut}_{g,m}$。

**引理。** $U_7(R)$ 的幂零类至多为 6，其 $\gamma_6$ 包含于中心子群 $\{I+tE_{17}:t\in R\}$。当 $R=\mathbb Z/m$ 时，该子群的每个元素的阶都整除 $m$。

**证明。** 令 $J_r$ 为所有仅可能在 $j-i\ge r$ 处非零的严格上三角矩阵，则 $J_rJ_s\subseteq J_{r+s}$。由有限几何级数的逆矩阵公式，$[1+J_r,1+J_s]\subseteq1+J_{r+s}$。因此 $\gamma_r U_7(R)\subseteq1+J_r$。$J_7=0$，$J_6=R E_{17}$ 且 $J_1J_6=J_6J_1=0$，给出中心性。最后 $(I+tE_{17})^m=I+mtE_{17}=I$。

**定理。** 对每个 $\sigma:\Pi_g\to V_m$ 及每个整数 $n$，

$$\sigma(\tau^n(u))=\sigma(u)\sigma(\delta)^n,$$

其中 $\sigma(\delta)$ 位于中心，且其 $m$ 次幂为单位元。故对全部整数 $p,n$，

$$\boxed{q^{\rm ut}_{g,m}(\tau^n(u))\sim
q^{\rm ut}_{g,m}(\tau^p(u))
\quad\Longleftrightarrow\quad n\equiv p\pmod m.}$$

该共轭类轨道恰有 $m$ 个元素。

**证明。** 第 11 节给出 $\delta\in\gamma_6\Pi_g$ 和 $\tau(\delta)\delta^{-1}\in\gamma_8\Pi_g$。每个 $V_m$ 值表示都消去 $\gamma_7\Pi_g$，所以看见的增量是中心元，且在 $\tau$ 下保持不变。在 $\Pi_g/\gamma_7\Pi_g$ 中对正负幂归纳，再经 $\sigma$，得到第一式。增量的 $m$ 次幂为单位元，故参数差被 $m$ 整除时，所有表示的实际像都相等，得到充分性。必要性沿用 $\rho_{-p}$；该表示本来就在 $V_m$ 中，因此仍是此评价族的合法坐标。评价核同样完全不变，故以上是同一个实际特征商上的轨道陈述。

**定理。** 所定义的动力学差满足

$$\boxed{\delta\in\gamma_6\Pi_g\setminus\gamma_7\Pi_g.}$$

因此，对这个指定词 $u$ 和指定动力学 $\tau$，幂零类 6 是检测其变化的准确最小阈值。

**证明。** 第 11 节给出上侧包含。取 $R=\mathbb Z/2$ 和 $t=0$，第 12 节给出 $\rho_0(u)=I$，$\rho_0(\tau(u))=I-E_{17}\ne I$，所以 $\rho_0(\delta)\ne I$。但 $U_7(\mathbb Z/2)$ 消去 $\gamma_7\Pi_g$，故 $\delta\notin\gamma_7\Pi_g$。五类及以下的全部幂零表示均固定该轨道，而这个六类表示已经检测到变化。阈值针对本词的变化；它没有断言所有曲面词、所有扭转或全部有限矩阵群都需要七维表示。

## 15. 第二导出词与简单闭曲线的区别

**命题。** 在闭可定向亏格至少为 2 的曲面上，非平凡第二导出子群元素的共轭类不能由本质简单闭曲线表示。

**证明。** 非分离本质简单闭曲线具有非零的一阶同调类，因此不属于第一导出子群。对分离本质简单闭曲线，选择适配两侧子曲面的标准生成元，使其共轭类由 $c=\prod_{i=1}^h[a_i,b_i]$ 或其逆表示，其中 $1\le h<g$。取整数 Heisenberg 群中的 $X=I+E_{12}$、$Y=I+E_{23}$。将一侧的一个把手映为 $(X,Y)$，另一侧的一个把手映为 $(Y,X)$，其他把手映为单位元。全曲面关系成立，但 $c$ 映为 $[X,Y]=I+E_{13}\ne I$。Heisenberg 群的第二导出子群为平凡群，故 $c$ 不可能属于 $\Pi_g''$。共轭、取逆和改变适配标记都保持该特征子群。

**推论。** 本节的 $u$ 与 $\delta$ 都是非平凡群元素，且均不能代表本质简单闭曲线。

**证明。** $u,\delta\in\Pi_g''$。$\rho_1(u)=I-E_{17}$ 在模 2 下非平凡；$\delta$ 的非平凡性由上一节得到。应用命题。

**命题。** 令 $X_{\rm simp}$ 为由本质简单闭曲线表示的共轭类集合，则

$$\{[\tau^n(u)]:n\in\mathbb Z\}\cap X_{\rm simp}=\varnothing.$$

并且映射 $n\mapsto[\tau^n(u)]$ 在 $\mathbb Z$ 上为单射。

**证明。** 自同构保持第二导出子群及非平凡性，故其每个轨道元素都不能代表本质简单闭曲线。若两个不同整数 $p,n$ 给出相同共轭类，取 $m>|n-p|$。经第 13 节的有限商后仍共轭，强制 $m$ 整除非零整数 $n-p$，与大小界矛盾。

## 16. 在全部 Johnson 层保留的有限单群商

**定义。** 固定闭、连通、可定向曲面 $\Sigma_g$，$g\ge3$，记 $\pi=\pi_1(\Sigma_g)$，$\mathcal M_g=\operatorname{Mod}^{+}(\Sigma_g)$。以下群作用始终来自保持曲面定向的映射类。令

$$\mathcal J_c=\ker\left(\mathcal M_g\longrightarrow\operatorname{Out}(\pi/\gamma_{c+1}\pi)\right),\qquad c\ge1.$$

$\mathcal J_1$ 是 Torelli 群，$\mathcal J_2$ 是 Johnson 核。Johnson 同态给出 $\mathcal J_c/\mathcal J_{c+1}$ 为交换群；Johnson 核由所有本质分离简单闭曲线上的 Dehn 扭转生成。

**引理。** 设 $J_1\ge J_2\ge\cdots$ 是群 $\Lambda$ 的子群列，每个 $J_{c+1}$ 正规于 $J_c$ 且 $J_c/J_{c+1}$ 交换。若同态 $f:\Lambda\to F$ 满足 $F=[F,F]$ 和 $f(J_1)=F$，则 $f(J_c)=F$ 对所有 $c\ge1$ 成立。

**证明。** 归纳。若 $f(J_c)=F$，由 $[J_c,J_c]\subseteq J_{c+1}$ 及同态保持交换子，得到

$$F=[F,F]=[f(J_c),f(J_c)]=f([J_c,J_c])\subseteq f(J_{c+1})\subseteq F.$$

**已知存在定理。** 对每个 $g\ge3$，存在非交换有限单群 $F$ 和满射 $f:\mathcal M_g\twoheadrightarrow F$，使 $f(\mathcal J_1)=F$。

**证明依据。** Masbaum–Reid 的量子表示与强逼近构造给出 $\mathcal M_g$ 到任意大维数的一族 $\operatorname{PSL}(N,q)$ 的满射。Torelli 群正规，故其在同一个满射下的像为平凡群或整个单群。若像平凡，该满射将经 $\operatorname{Sp}(2g,\mathbb Z)$ 因子化；对构造中足够大的 $N$，辛群的合同子群性质排除了这一可能。这里需要的是同一个 $f$ 的限制满射，单独存在某个 Torelli 群商不够。

**推论。** 可以固定一个这样的 $f$ 和 $\Gamma=\ker f$，使

$$\boxed{f(\mathcal J_c)=F\quad\text{对所有 }c\ge1.}$$

**证明。** 非交换单群完美，应用引理。

## 17. 一条真实简单曲线对全部有限幂零观察的障碍

**定义。** 对有限特征商 $q:\pi\twoheadrightarrow Q$，记实际诱导外作用为 $a_q:\mathcal M_g\to\operatorname{Out}(Q)$，主合同核为 $C_q=\ker a_q$。这里的幂零性指 $Q$，不指其自同构群或外自同构群。

**定理。** 对每个 $g\ge3$，存在固定的有限指数正规子群 $\Gamma\triangleleft\mathcal M_g$ 和固定的本质分离简单闭曲线 $\alpha$，使对每个有限特征幂零商 $q:\pi\twoheadrightarrow Q$，都有

$$\boxed{C_q\alpha\not\subseteq\Gamma\alpha.}$$

同一个 $(\Gamma,\alpha)$ 对全部有限阶、全部幂零类及全部模数同时成立。

**证明。** 固定第 16 节的 $f$。因为 $f(\mathcal J_2)=F\ne1$ 且 $\mathcal J_2$ 由分离扭转生成，存在本质分离曲线 $\alpha$ 使 $z=f(T_\alpha)\ne1$。非交换单群的中心平凡，所以 $C_F(z)<F$。令 $H=\operatorname{Stab}_{\mathcal M_g}(\alpha)$。对于 $h\in H$，曲面定向保持性给出 $hT_\alpha h^{-1}=T_\alpha$，故

$$f(H)\subseteq C_F(z)<F.$$

若 $Q$ 的幂零类至多为 $c\ge1$，则 $q$ 消去 $\gamma_{c+1}\pi$。$\mathcal J_c$ 中的元素在 $\pi/\gamma_{c+1}\pi$ 上以内自同构作用，因而在 $Q$ 上也以内自同构作用。因此 $\mathcal J_c\subseteq C_q$，继而 $f(C_q)=F$。如果 $C_q\alpha\subseteq\Gamma\alpha$，第 9 节给出 $C_q\subseteq\Gamma H$，取 $f$ 的像将得到 $F\subseteq f(H)$，矛盾。平凡目标也可取 $c=1$。

**推论。** 用任意有限多个有限特征幂零商作联合观察仍有同一障碍。

**证明。** 联合像是有限个幂零群直积的子群，其幂零类至多为这些类的最大值，投影核是各特征核的交。应用定理。这里不需要、也不假设联合像的主合同核等于各主合同核的交；不同投影的内共轭元可能不相容。

**定理。** 对上述 $f$、$\Gamma$ 和任意这样的 $q$，令 $A_q=a_q(\mathcal M_g)$。有

$$\boxed{\operatorname{im}(f,a_q)=F\times A_q.}$$

因此，对于每个 $v\in A_q$ 和每个 $y\in F$，存在同一个映射类 $x$ 满足 $a_q(x)=v$、$f(x)=y$。此外，$C_q\alpha$ 与整个 $\mathcal M_g\alpha$ 中每个 $\Gamma$ 轨道都相交。

**证明。** 先选 $x_0$ 使 $a_q(x_0)=v$，再由 $f(C_q)=F$ 选 $c\in C_q$ 满足 $f(c)=y f(x_0)^{-1}$。取 $x=cx_0$ 即可。对于轨道结论，正规性给出 $\Gamma\backslash\mathcal M_g/H\cong F/f(H)$；而 $f(C_q)=F$，所以 $C_q$ 的元素达到全部这些陪集。轨道数恰为 $[F:f(H)]\ge[F:C_F(z)]>1$，没有把 $f(H)$ 与 $C_F(z)$ 当成相等。

**推论。** 在由全部有限特征幂零曲面商的主合同核定义的群拓扑中，$\Gamma$ 的每个陪集都稠密；$f$ 到离散有限群 $F$ 不连续。

**证明。** 主核在有限交下有来自联合像的更小主核，因而构成单位元邻域基。上一项定理说明每个这样的邻域的每个平移都与 $f^{-1}(y)$ 相交。$\Gamma$ 是真子群却稠密，故它不开放，$f$ 不连续。此拓扑是曲面幂零商所诱导的合同拓扑，不是对映射类群本身直接取幂零商所定义的拓扑。

## 18. 单群目标的轨道控制等价于完整因子化

**定理。** 设 $\Lambda$ 作用于 $X$，$\alpha\in X$，$H=\operatorname{Stab}_\Lambda(\alpha)$。令 $f:\Lambda\twoheadrightarrow F$ 为到非交换有限单群的满射，$\Gamma=\ker f$，并假设 $f(H)<F$。对任意同态 $a:\Lambda\to A$，令 $A_0=a(\Lambda)$、$C=\ker a$。则下列条件等价：

$$C\alpha\subseteq\Gamma\alpha;\qquad C\subseteq\Gamma;\qquad
\exists\,\theta:A_0\twoheadrightarrow F,\ f=\theta\circ a.$$

**证明。** 由第 9 节及 $\Gamma=\ker f$，第一条件等价于 $f(C)\subseteq f(H)$。$C$ 正规于 $\Lambda$，所以 $f(C)$ 正规于 $F$。单性及 $f(H)<F$ 强制 $f(C)=1$，即第二条件。反之第二条件直接给出第一条件。第二条件使 $\theta(a(x))=f(x)$ 良定义；乘法保持性和满射性来自 $f$。任何这样的因子化都消去 $C$。

**推论。** 对第 17 节固定的真实曲面、曲线和 $f$，某个有限特征商 $q$ 能满足该轨道要求，当且仅当这个同一个 $f$ 经 $a_q(\mathcal M_g)$ 因子化。只证明某个单独扭转被看见，或只证明 $a_q$ 的像很大，不足以给出该因子化。

**定理。** 在上述一般条件中，若 $A_0$ 有限，令

$$B=\operatorname{im}(f,a)\le F\times A_0.$$

则恰有两种可能：$B=F\times A_0$，或者 $B$ 是一个满射 $\theta:A_0\twoheadrightarrow F$ 的图像。后一种情形恰好对应轨道控制；等价的有限判据为

$$\boxed{B\cap(F\times\{1\})=\{(1,1)\}.}$$

**证明。** 该交等于 $f(C)\times\{1\}$。单性给出 $f(C)=1$ 或 $F$。前者使第二坐标投影 $B\to A_0$ 为同构，其逆的第一坐标即 $\theta$。后者使 $F\times\{1\}\subseteq B$；利用 $B\to A_0$ 满射即可得到整个直积。若给定 $\Lambda$ 的生成集，则 $B$ 由同一批生成元在 $f$ 与 $a$ 下的像对生成；不能独立生成两侧像后把它们默认视为联合像。

## 19. 状态分离与外动力学分离的两种相容性

**引理。** 设 $S_1,\ldots,S_t$ 为非交换有限单群，$B\le\prod_iS_i$ 在每个坐标上满射。若 $M\triangleleft B$ 也在每个坐标上满射，则 $M=B$。此外，$B$ 是完美群。

**证明。** 对 $t$ 归纳。向前 $t-1$ 个坐标投影，记像为 $B'$，核为 $K\le S_t$。由于 $B\to S_t$ 满射，$K$ 正规于 $S_t$，故 $K=1$ 或 $S_t$。归纳假设给出 $M$ 的前坐标像为 $B'$。若 $K=1$，结论立即成立。若 $K=S_t$，则 $[M,K]\subseteq M\cap K$，而其最后坐标为 $[S_t,S_t]=S_t$，所以 $K\subseteq M$，仍得 $M=B$。对于完美性，在 $K=1$ 时由 $B\cong B'$ 得到；在 $K=S_t$ 时 $K=[K,K]\subseteq[B,B]$，且 $[B,B]$ 满射到完美群 $B'$，故 $[B,B]=B$。

**定理。** 设 $1\to\pi\to E\to\Lambda\to1$ 是群扩张。对每个 $i$，设 $\rho_i:E\to S_i$ 是到非交换有限单群的同态，且 $\rho_i(\pi)=S_i$。对于任意有限子族，令 $q$ 为 $\pi$ 在这些坐标上的联合像满射。则 $E$ 在该联合像上的共轭作用全部为内自同构，所以 $\Lambda$ 的诱导外作用平凡。

**证明。** 令 $B$ 为 $E$ 的联合像，$M$ 为 $\pi$ 的联合像。正规性和逐坐标满射性给出引理的条件，故 $M=B$。任意 $e\in E$ 的像已经属于 $q(\pi)$，用它作为共同共轭元即可。该结论允许各 $S_i$ 同构；没有独立坐标假设。

**推论。** 若每个 $\ker(\rho_i|_\pi)$ 都是 $\pi$ 的特征子群，且其可数交为 $1$，则有限前缀交构成一条递降、交为 $1$ 的有限指数特征子群塔，且 $\Lambda$ 在每层商上的外作用都平凡。

**证明。** 有限交保持特征性和有限指数；有限联合像的核正是这个交，应用定理。交为 $1$ 保证 $\pi$ 的元素被联合状态读出分离，但外作用仍全部平凡。仅有 $E$ 下的不变性并不自动给出 $\pi$ 的完整特征性，后者在本推论中单独假设。

## 20. 加入外作用平凡的完美商不能修复幂零路线

**引理。** 设 $A$ 可解、$P$ 完美，$B\le A\times P$ 对两侧都满射，则 $B=A\times P$。

**证明。** 若 $A$ 的导出长度至多为 $d$，则 $B^{(d)}$ 的第一投影为 $1$，第二投影为 $P^{(d)}=P$，故 $\{1\}\times P\subseteq B$。结合第一投影满射得到结论。

**定理。** 设 $q_A:\pi\twoheadrightarrow A$ 与 $q_P:\pi\twoheadrightarrow P$ 是有限特征商，其中 $A$ 可解、$P$ 完美。设某群 $\Lambda\le\operatorname{Out}(\pi)$ 在 $P$ 上的诱导外作用平凡。令 $q$ 为两商的联合像投影，则该联合像为 $A\times P$，且

$$\boxed{\ker a_q=\ker a_{q_A}.}$$

**证明。** 直积结论来自引理。若一个映射类在联合像上为内自同构，其在 $A$ 上也为内自同构。反之，若它在 $A$ 上由 $a\in A$ 实现内共轭，在 $P$ 上由 $p\in P$ 实现内共轭，那么 $(a,p)$ 属于实际联合像并实现两者的共同内共轭。投影核特征，故两个坐标作用保持各自因素，不出现因素交换。

**推论。** 在第 17 节的障碍中，把任意有限多个幂零观察与第 19 节任意有限子族联合，仍不能达到 $C_q\alpha\subseteq\Gamma\alpha$。

**证明。** 幂零观察的联合像仍幂零，因而可解；第 19 节的联合像完美且外作用平凡。应用定理，主合同核与仅保留幂零联合像时完全相同。这一结论不排除一般非幂零商，也不排除具有非平凡外作用的可解商。

## 21. 从单群商的内部元素转向核集合的置换

**定义。** 令 $\pi$ 为有限生成群，$S$ 为非交换有限单群，且 $\operatorname{Epi}(\pi,S)$ 非空。设

$$\mathcal E_S=\operatorname{Epi}(\pi,S)/\operatorname{Aut}(S),\qquad
N_S=\bigcap_{\rho\in\operatorname{Epi}(\pi,S)}\ker\rho,$$

其中等价关系为在目标端复合自同构。记 $r=|\mathcal E_S|$。该集合也可识别为所有满足 $\pi/N\cong S$ 的正规子群 $N$ 的集合。

**定理。** $\mathcal E_S$ 有限，$N_S$ 特征，且 $\pi/N_S\cong S^r$。同构依赖各等价类代表的选择，而特征核与其置换作用不依赖此选择。

**证明。** 若 $\pi$ 有 $d$ 个生成元，同态由其像唯一确定，故 $|\operatorname{Epi}(\pi,S)|\le|S|^d$。两个满射核相同当且仅当相差目标自同构。选择互不等价的满射 $\rho_1,\ldots,\rho_r$，其联合像在每侧满射。归纳证明它是整个直积：若向前 $r-1$ 个坐标投影的核为 $S$，结论成立；若核平凡，最后一个坐标是满射 $S^{r-1}\to S$ 的图像。各因素像正规且两两交换，故因 $S$ 非交换单，恰有一个因素映为 $S$，其余映为 $1$。于是 $\rho_r$ 与前某个满射具有相同的核，矛盾。$N_S$ 对所有自同构不变，因为预复合置换满射族；没有因此断言它对所有自同态完全不变。

**定义。** 对 $\Lambda\le\operatorname{Out}(\pi)$，记 $a_S:\Lambda\to\operatorname{Out}(S^r)$ 为上述特征商的外作用，$b_S:\Lambda\to\operatorname{Sym}(\mathcal E_S)$ 为对核集合的置换。内自同构不改变正规子群，故 $b_S$ 良定义。与该核标记相容地，$b_S$ 是 $a_S$ 的因素置换。

**定理。** 假设 $\operatorname{Out}(S)$ 可解。对任意到非交换有限单群的满射 $f:\Lambda\twoheadrightarrow F$，有

$$\boxed{f\text{ 经 }a_S\text{ 的像因子化}
\quad\Longleftrightarrow\quad
f\text{ 经 }b_S\text{ 的像因子化}.}$$

**证明。** $S^r$ 的自同构置换其最小正规子群，即各简单因素；固定各因素的自同构逐因素来自 $\operatorname{Aut}(S)$。除以内自同构后，因素置换的核为 $\operatorname{Out}(S)^r$。因此 $a_S(\Lambda)$ 到 $b_S(\Lambda)$ 的核可解且正规。若存在满射 $\theta:a_S(\Lambda)\twoheadrightarrow F$ 给出 $f$，该核的像是 $F$ 的可解正规子群，单性强制其平凡；$\theta$ 因而继续经过置换像因子化。反向直接复合。可解性在此作为明确前提保留。

**推论。** 对第 17 节的 $(f,\Gamma,\alpha)$，上述特征商能控制该简单曲线轨道，当且仅当

$$\operatorname{im}(f,b_S)\cap(F\times\{1\})=\{(1,1)\}.$$

若 $\mathcal M_g$ 的同一组生成元为 $s_1,\ldots,s_k$，则应使用其实际像对 $(f(s_i),b_S(s_i))$ 生成联合子群。必要条件包括 $|F|\mid|b_S(\mathcal M_g)|$，进而 $|F|\mid r!$；这些阶数条件不充分。

**证明。** 依次应用第 18 节、本节定理及第 18 节的有限联合像判据。阶数条件来自满射与拉格朗日定理。

**命题。** 本节仅给出这一类特征商的准确验收条件，并不证明对任意给定的 $f$ 必有某个 $S$ 达到该条件。即使一个序列中的单群曲面商能够分离全部曲面群元素，若其核都被映射类固定、诱导外作用平凡，该序列也不满足任何非平凡 $f$ 的因子化要求。

**证明。** 验收条件以存在经实际置换像的满射为内容；有限性、状态分离和单群性本身均不提供该满射。对于后一种序列，第 19 节的条件满足时任意有限联合外作用仍平凡，故无法满射到非平凡的 $F$。


## 22. 非分离扭转的标记与共轭类稳定条件

**定义。** 对 $g\ge2$，令

$$\Pi_g=\langle a_1,b_1,\ldots,a_g,b_g\mid\prod_{i=1}^g[a_i,b_i]=1\rangle.$$

定义 $T$ 固定 $a_1$ 与所有 $a_i,b_i$（$i\ge2$），并满足 $T(b_1)=b_1a_1$。这取非分离 $a_1$ 曲线的一个有标记扭转方向；相反方向由 $T^{-1}$ 给出。

**命题。** $T$ 是自同构，且对任意整数 $n$，$T^n(b_1)=b_1a_1^n$，其余生成元保持不变。

**证明。** 恒等式 $[a,ba^n]=[a,b]$ 保证原关系在每个这样的生成元赋值下保持。正负指数相加给出复合，指数 $-1$ 给出逆。

**定义。** 对同态 $\phi:\Pi_g\to F$，记 $A=\phi(a_1)$、$B=\phi(b_1)$。称 $T^n$ 标记稳定 $\phi$，若 $\phi T^n=\phi$；称其共轭类稳定 $\phi$，若存在一个 $z\in F$，使 $\phi(T^n x)=z\phi(x)z^{-1}$ 对全部 $x\in\Pi_g$ 同时成立。

**定理。** 标记稳定的准确条件为

$$\phi T^n=\phi\quad\Longleftrightarrow\quad A^n=1.$$

**证明。** 在 $b_1$ 处比较得到 $BA^n=B$，可约去 $B$。反向由全部生成元像相等及生成性质得到。此结论不需要 $\phi$ 满射。

## 23. 阶为八的满射实例

**定义。** 令 $D_8=\langle r,s\mid r^4=s^2=1,\ srs=r^{-1}\rangle$，其中 $r$ 的阶恰为 $4$。在亏格二时定义生成元像

$$(a_1,b_1,a_2,b_2)\longmapsto(r^2,s,r,1).$$

**定理。** 这些像给出满射 $\phi:\Pi_2\twoheadrightarrow D_8$，并且

$$\boxed{\phi(a_1)=r^2\ne1,\qquad\phi T=\operatorname{Ad}_r\phi.}$$

因此共轭类稳定不推出曲线属于 $\ker\phi$。

**证明。** $r^2$ 在 $D_8$ 中为中心元，所以两个关系交换子分别是 $[r^2,s]=1$ 与 $[r,1]=1$。$r,s$ 都出现于生成元的像，故同态满射。经过 $T$ 后四个像为 $(r^2,sr^2,r,1)$；对原四个像同时以 $r$ 共轭，利用 $rsr^{-1}=sr^{-2}=sr^2$，得到同一四元组。两个同态在全部生成元上相等，所以在整个曲面群上相等。$r$ 的准确阶保证 $r^2\ne1$。

**命题。** 对每个整数 $n$，有 $\phi T^n=\operatorname{Ad}_{r^n}\phi$。其标记稳定指数集合为 $2\mathbb Z$，其共轭类稳定指数集合为全部 $\mathbb Z$。

**证明。** $T$ 固定 $a_2$，而 $\phi(a_2)=r$，可将一步共轭公式对正负幂归纳。也可直接计算 $\phi(T^n b_1)=sr^{2n}$。标记相等恰在 $r^{2n}=1$ 时成立。

**命题。** $\ker\phi$ 被 $T$ 保持，但不是 $\Pi_2$ 的特征子群。

**证明。** 共轭类稳定保证 $T$ 及其逆都保持核。考虑交换两个把手的自同构 $J:a_1\leftrightarrow a_2,\ b_1\leftrightarrow b_2$。它保持曲面关系，因为 $[a_2,b_2][a_1,b_1]$ 是原关系的共轭，并且 $J^2=1$。现在 $a_1^2\in\ker\phi$，而 $\phi(J(a_1^2))=\phi(a_2^2)=r^2\ne1$，所以该核不被 $J$ 保持。

## 24. 同一机制的无挠和任意模数版本

**定义。** 对 $R=\mathbb Z$ 或 $R=\mathbb Z/m$，令 $H(R)$ 的元素是三元组 $(x,y,z)\in R^3$，乘法为

$$(x,y,z)(x',y',z')=(x+x',y+y',z+z'+xy').$$

其单位元为 $(0,0,0)$，逆元为 $(-x,-y,-z+xy)$。记 $X=(1,0,0)$、$Y=(0,1,0)$、$Z=(0,0,1)$，于是 $[X,Y]=Z$，且 $Z$ 为中心元。

**定理。** 对所有 $g\ge2$，赋值

$$(a_1,b_1,a_2,b_2)\longmapsto(Z,Y,X,1)$$

并将其余生成元映为单位元，定义满射 $\phi_R:\Pi_g\twoheadrightarrow H(R)$。对每个整数 $n$，

$$\boxed{\phi_R T^n=\operatorname{Ad}_{X^n}\phi_R.}$$

当 $R=\mathbb Z$ 时 $\phi_R(a_1)\ne1$，且 $H(\mathbb Z)$ 无挠；当 $R=\mathbb Z/m$ 且 $m\ge2$ 时，$\phi_R(a_1)$ 的阶恰好为 $m$。

**证明。** 两个关系交换子为 $[Z,Y]=[X,1]=1$。任意三元组可写为 $X^xY^yZ^{z-xy}$，使用整数代表给出模数情形的同一满射结论。共轭公式 $XYX^{-1}=YZ$ 与其他三个像被 $X$ 固定共同给出结论。整数情形，若 $(x,y,z)^k=1$ 且 $k\ne0$，前两坐标给出 $x=y=0$，第三坐标再给出 $z=0$，故群无挠。$Z$ 的阶由其第三坐标决定。

**推论。** 在 $H(\mathbb Z)$ 中，非零扭转次数均改变标记表示，但不改变其共轭类。模 $m$ 时，标记表示的准确周期为 $m$，共轭类周期为 $1$。因此仅增加目标群无挠的假设，仍不能将共轭类稳定改成曲线像平凡。

**证明。** 应用第 22 节的标记判据与本节共同共轭公式。

## 25. 保留中心化子的准确修复

**定义。** 对任意 $\phi:\Pi_g\to F$，令

$$S=\langle\phi(a_1),\phi(a_2),\phi(b_2),\ldots,\phi(a_g),\phi(b_g)\rangle\le F.$$

记 $C_F(S)=\{z\in F:zs=sz\text{ 对全部 }s\in S\}$，$Z(F)$ 为 $F$ 的中心。

**定理。** 对每个整数 $n$，有

$$\boxed{\phi T^n\sim\phi\quad\Longleftrightarrow\quad
\exists z\in C_F(S),\ zBz^{-1}=BA^n.}$$

等价地，右边可写为 $\exists z\in C_F(S),\ B^{-1}zBz^{-1}=A^n$。

**证明。** 若存在整个表示的共同共轭元，它必须固定每个未改变的生成元像，因此属于 $C_F(S)$。在唯一改变的 $b_1$ 处得到显示方程。反之，中心化条件给出所有未改变生成元上的同态相等，显示方程给出 $b_1$ 处的相等，生成性质给出全群的相等。

**推论。** 若 $C_F(S)\subseteq Z(F)$，则

$$\phi T^n\sim\phi\quad\Longleftrightarrow\quad A^n=1.$$

特别地，当固定生成元的像生成整个 $F$ 时，该条件成立。

**证明。** 中心共轭元不能改变 $B$，所以必要性化为 $BA^n=B$。充分性取 $z=1$。当 $S=F$ 时 $C_F(S)=Z(F)$。

## 26. 全部有限表示的特征商恢复准确指数

**定义。** 固定有限群 $F$，令 $e=\exp(F)$，即使所有 $z\in F$ 都满足 $z^e=1$ 的最小正整数。定义

$$E_F:\Pi_g\longrightarrow F^{\operatorname{Hom}(\Pi_g,F)},\qquad E_F(x)(\rho)=\rho(x),$$

并令 $Q_F=\operatorname{im}E_F$，$q_F:\Pi_g\twoheadrightarrow Q_F$ 为像限制。允许非满射的表示作为评价坐标。

**定理。** $Q_F$ 有限，$\ker q_F$ 在全部自同态下保持不变。$T$ 诱导的 $\overline T\in\operatorname{Aut}(Q_F)$ 对全部整数 $n$ 满足

$$\boxed{\overline T^{\,n}\text{ 为内自同构}
\quad\Longleftrightarrow\quad
\overline T^{\,n}=1
\quad\Longleftrightarrow\quad e\mid n.}$$

**证明。** 同态由有限多个生成元像唯一决定，所以表示集合有限；预复合保持该集合，给出核的不变性。如果 $e\mid n$，则每个表示都满足 $\rho(a_1)^n=1$，因此 $T^n$ 对全部生成元的评价均不变。

反之，假设诱导的 $n$ 次作用为内自同构。对每个 $z\in F$，取表示 $\rho_z(a_1)=z$、$\rho_z(b_1)=1$，并令其余像为单位元。每个关系交换子均平凡，故该表示存在。将假设的内共轭等式在此坐标及元素 $b_1$ 上读取，得到 $z^n=1$。因为这对全部 $z$ 成立，各元素阶均整除 $n$，所以其最小公倍数 $e$ 整除 $n$。负幂使用逆映射得到同一结论。

**命题。** 在 $F=D_8$ 时，上述特征商中的外自同构阶为 $4$，尽管第 23 节的那个满射表示的共轭类已经在一步后返回。

**证明。** $D_8$ 的指数为 $4$。具体地，另一满射表示 $(a_1,b_1,a_2,b_2)\mapsto(r,1,s,1)$ 在 $b_1$ 处看到 $r^n$，单位元的共轭不能消除这个读数。第 23 节只处理一个表示，未断言所有表示同时返回。

**推论。** 取 $F=\mathbb Z/m$ 时，$Q_F$ 可识别为模 $m$ 的一阶同调商，非分离扭转在其上的准确阶为 $m$。

**证明。** 所有交换目标同态经过阿贝尔化 $\Pi_g^{\mathrm{ab}}\cong\mathbb Z^{2g}$；各坐标模 $m$ 的读出共同核为 $m\mathbb Z^{2g}$。有限循环群的指数为 $m$，再用定理。这里的结论针对非分离扭转，不改变前述分离扭转或第二导出词所需的非交换观察深度。

## 27. 固定特征覆盖上的一阶同调提升

**定义。** 设 $\pi$ 为有限生成群，$N\le\pi$ 为有限指数特征子群，$S=\pi/N$ 为中心平凡的有限群。设 $\Lambda\le\operatorname{Out}(\pi)$ 在 $S$ 上的诱导外作用平凡。对素数 $\ell$，定义

$$N_\ell=[N,N]N^\ell,\qquad V_\ell=N/N_\ell,\qquad Q_\ell=\pi/N_\ell.$$

$N^\ell$ 表示由全部 $\ell$ 次幂生成的子群。$N_\ell$ 在 $\pi$ 中特征，$V_\ell$ 是有限维 $\mathbb F_\ell$ 向量空间，且有实际扩张

$$1\longrightarrow V_\ell\longrightarrow Q_\ell\longrightarrow S\longrightarrow1.$$

$S$ 在 $V_\ell$ 上的甲板作用记为 $\lambda$：取 $s$ 的任意提升 $x\in\pi$，令 $\lambda(s)[v]=[xvx^{-1}]$。改变提升只引入 $N$ 的内作用，在其阿贝尔化上为恒等，所以该作用良定义。

**定理。** 对 $\gamma\in\Lambda$，任选代表 $\eta\in\operatorname{Aut}(\pi)$，记 $t_\eta$ 为它在 $V_\ell$ 上的作用，$s_\eta\in S$ 为满足 $\eta|_S=\operatorname{Ad}_{s_\eta}$ 的唯一元素。则

$$\boxed{\Psi_\ell(\gamma)=\lambda(s_\eta)^{-1}t_\eta}$$

与代表无关，并定义同态

$$\Psi_\ell:\Lambda\longrightarrow\operatorname{Aut}_{\mathbb F_\ell[S]}(V_\ell).$$

**证明。** 中心平凡性给出 $s_\eta$ 的唯一性。对 $s\in S$，有 $t_\eta\lambda(s)t_\eta^{-1}=\lambda(s_\eta s s_\eta^{-1})$，所以经修正后的作用与 $\lambda(S)$ 交换。若将 $\eta$ 换为 $\operatorname{Ad}_x\eta$，则 $t_\eta$ 左乘 $\lambda(\bar x)$，$s_\eta$ 左乘 $\bar x$，两项修正相消。对两个代表 $\eta,\zeta$，有 $s_{\eta\zeta}=s_\eta s_\zeta$；将 $t_\eta=\lambda(s_\eta)\Psi_\ell(\gamma)$ 代入，再用修正作用与甲板作用交换，即得乘法保持性。

**命题。** 若 $\pi$ 来自闭可定向亏格 $g\ge2$ 的曲面，且 $\Lambda$ 保持曲面定向，则

$$\dim_{\mathbb F_\ell}V_\ell=2+2(g-1)|S|,$$

且 $\Psi_\ell(\Lambda)$ 保持覆盖曲面的一阶同调交叉形式。

**证明。** 对应的连通覆盖度数为 $|S|$。欧拉示性数的覆盖公式给出覆盖亏格 $1+(g-1)|S|$。其一阶整数同调无挠且秩为亏格的两倍，模 $\ell$ 后得到维数。代表的提升与甲板变换都保持定向，因而都保持交叉形式，其复合也保持该形式。

## 28. 修正同调作用的核与一阶上同调

**定义。** 记 $a_\ell:\Lambda\to\operatorname{Out}(Q_\ell)$ 为实际外作用，$C_\ell=\ker a_\ell$，$K_\ell=\ker\Psi_\ell$。以加法记 $V_\ell$，令

$$Z^1(S,V_\ell)=\{d:S\to V_\ell:d(st)=d(s)+s\cdot d(t)\},$$

$$B^1(S,V_\ell)=\{s\mapsto b-s\cdot b:b\in V_\ell\},\qquad
H^1(S,V_\ell)=Z^1(S,V_\ell)/B^1(S,V_\ell).$$

**定理。** 有 $C_\ell\subseteq K_\ell$，且存在单射群同态

$$\boxed{K_\ell/C_\ell\hookrightarrow H^1(S,V_\ell).}$$

特别地，$K_\ell/C_\ell$ 是有限初等交换 $\ell$ 群。若 $\ell\nmid|S|$，则 $C_\ell=K_\ell$。

**证明。** 若代表在 $Q_\ell$ 上是由 $x$ 给出的内自同构，它在 $V_\ell$ 上的作用就是 $\lambda(\bar x)$，因此修正作用为恒等。

对 $\gamma\in K_\ell$，将其诱导自同构再复合以 $s_\eta$ 的一个提升的逆作内共轭，得到同时固定 $V_\ell$ 中每个元素、并在 $S$ 上为恒等的自同构 $\beta$。若 $y\in Q_\ell$ 提升 $s\in S$，令 $d_\beta(s)=\beta(y)y^{-1}\in V_\ell$。改变 $y$ 为同一陪集内的元素不改变该值；乘积公式给出余循环关系。反过来，任一余循环定义自同构 $y\mapsto d(\bar y)y$，其逆对应 $-d$。这一步不要求扩张分裂。

改变归一化提升只使余循环增加 $b-s\cdot b$。两个归一化代表的复合对应余循环相加，故得到 $K_\ell\to H^1(S,V_\ell)$ 的同态。如果归一化后的作用是内自同构，其共轭元在 $S$ 上必须为中心元，因 $Z(S)=1$，该共轭元属于 $V_\ell$；其余循环恰是余边界。反向同样成立，所以核准确为 $C_\ell$。

当 $\ell\nmid|S|$ 时，对余循环 $d$ 取 $b=|S|^{-1}\sum_{t\in S}d(t)$。由 $d(st)=d(s)+s\cdot d(t)$ 对 $t$ 求和并重排，得到 $d(s)=b-s\cdot b$。故 $H^1(S,V_\ell)=0$。

**定理。** 设 $f:\Lambda\twoheadrightarrow F$ 满射到非交换有限单群。则对每个素数 $\ell$，包括整除 $|S|$ 的素数，都有

$$\boxed{f\text{ 经 }a_\ell(\Lambda)\text{ 因子化}
\quad\Longleftrightarrow\quad
f\text{ 经 }\Psi_\ell(\Lambda)\text{ 因子化}.}$$

**证明。** 左侧等价于 $f(C_\ell)=1$。在此条件下，$f(K_\ell)$ 是 $F$ 的正规 $\ell$ 子群，因为它是 $K_\ell/C_\ell$ 的同态像。非交换单群不具有非平凡正规 $\ell$ 子群，故 $f(K_\ell)=1$，得到右侧。反向使用 $C_\ell\subseteq K_\ell$。同一证明适用于任意没有非平凡正规 $\ell$ 子群的有限目标 $F$。

**命题。** 当素数整除基群的阶时，不能对任意这样的扩张直接删去上同调误差。

**证明。** 在扩张 $1\to C_2\to S_3\times C_2\to S_3\to1$ 中，映射 $(s,v)\mapsto(s,v+\varepsilon(s))$，其中 $\varepsilon:S_3\to C_2$ 为符号同态，是同时固定核与商的自同构。它不为内自同构，因为每个内自同构均保持第二坐标不变。这里 $Z(S_3)=1$，但 $H^1(S_3,C_2)\ne0$。这只是一般扩张的反例，不声称它是某个给定曲面覆盖的同调扩张。

## 29. 相对 Frattini 核的素数幂结构

**引理。** 设 $P$ 为有限 $\ell$ 群，$\Phi(P)$ 为其 Frattini 子群，则

$$\Phi(P)=[P,P]P^\ell,$$

且 $\operatorname{Aut}(P)\to\operatorname{Aut}(P/\Phi(P))$ 的核是有限 $\ell$ 群。

**证明。** 有限 $\ell$ 群的每个极大真子群正规且指数为 $\ell$，故都包含 $[P,P]P^\ell$；反向在初等交换商 $P/[P,P]P^\ell$ 中，用不含指定非零向量的超平面分离该向量，拉回后得到极大子群。因此等式成立。取 $P/\Phi(P)$ 的一个有序基，并考虑它的全部有序提升。每个提升都生成 $P$，否则这些提升生成的真子群包含于某极大子群，与其在 Frattini 商上生成矛盾。若基长为 $d$，提升集合大小为 $|\Phi(P)|^d$。作用核在该集合上自由作用，因为固定一组生成元的自同构就是恒等。故核的阶整除这个 $\ell$ 次幂。

**定理。** 设 $Q$ 为有限群，$P\triangleleft Q$ 为有限 $\ell$ 子群。令 $\mathcal B$ 为所有保持 $P$ 并在 $Q/\Phi(P)$ 上诱导恒等的自同构所成的群。则 $\mathcal B$ 是 $\ell$ 群。因此，任意保持 $P$ 的外自同构子群到 $\operatorname{Out}(Q/\Phi(P))$ 的映射，其核也是 $\ell$ 群。

**证明。** 限制到 $P$ 后，$\mathcal B$ 的像属于上一引理中的 $\ell$ 群。限制映射的核由同时逐点固定 $P$、且模 $\Phi(P)$ 为恒等的自同构组成。对其中的 $\beta$，缺陷 $d(x)=\beta(x)x^{-1}$ 属于 $\Phi(P)$。因为 $\beta$ 固定 $P$，对 $xpx^{-1}$ 比较得到 $d(x)\in Z(P)$。该缺陷对 $P$ 的陪集不变，并给出

$$d:Q/P\longrightarrow Z(P)\cap\Phi(P)$$

的余循环。自同构复合对应余循环相加，且缺陷映射单射，所以限制核为一个有限交换 $\ell$ 群。$\mathcal B$ 是两个 $\ell$ 群的扩张，故亦为 $\ell$ 群。

若一个保持 $P$ 的外自同构在 $Q/\Phi(P)$ 上为内自同构，将其代表复合一个提升的内自同构之逆，即可得到 $\mathcal B$ 中的代表。因此外作用核是 $\mathcal B$ 的像的子群，仍为 $\ell$ 群。这里仅使用保持 $P$ 的自同构，不要求 $P$ 对 $Q$ 的所有自同构都特征。

## 30. 同一覆盖上全部有限素数幂提升的因子化能力

**定义。** 设 $\pi$ 有限生成，$N\le\pi$ 为有限指数特征子群，$\Lambda\le\operatorname{Out}(\pi)$。这一节不要求 $\pi/N$ 中心平凡，也不要求其外作用平凡。固定素数 $\ell$，令 $N_\ell=[N,N]N^\ell$。设 $K$ 为 $\pi$ 的特征子群、$K\subseteq N_\ell$，且 $N/K$ 为有限 $\ell$ 群。记 $Q=\pi/K$，$Q_\ell=\pi/N_\ell$，并令 $A_Q,A_\ell$ 为同一个 $\Lambda$ 在两者上的实际外作用像。

**定理。** 自然映射 $A_Q\twoheadrightarrow A_\ell$ 的核为有限 $\ell$ 群。对任意到非交换有限单群的满射 $f:\Lambda\twoheadrightarrow F$，

$$\boxed{f\text{ 经 }A_Q\text{ 因子化}
\quad\Longleftrightarrow\quad f\text{ 经 }A_\ell\text{ 因子化}.}$$

**证明。** 对 $P=N/K$，上一节的公式给出 $\Phi(P)=N_\ell/K$，故 $Q/\Phi(P)=Q_\ell$。实际作用都保持 $P$，并且外作用映射由同一批 $\Lambda$ 元素诱导，故像间的映射满射。其核的 $\ell$ 群性质由上一节得到。若 $f=\theta a_Q$，该核经 $\theta$ 的像是 $F$ 的正规 $\ell$ 子群，因而平凡，$\theta$ 继续下降到 $A_\ell$。反向直接复合。

**推论。** 若只假设 $K$ 为 $\pi$ 的特征子群、$K\subseteq N$、$N/K$ 是有限 $\ell$ 群，而不要求 $K\subseteq N_\ell$，那么只要 $f$ 经该商的外作用因子化，它也经 $A_\ell$ 因子化。因此，对固定的 $N,\ell,f$，存在某个有限 $\ell$ 群提升达到因子化，当且仅当首次同调提升 $Q_\ell$ 已达到因子化。

**证明。** 用 $K\cap N_\ell$ 代替 $K$。$N/(K\cap N_\ell)$ 嵌入 $(N/K)\times(N/N_\ell)$，所以仍为有限 $\ell$ 群。这个更细的特征商映到原商，故继承已有的因子化。应用定理。反向直接选择 $K=N_\ell$。

**命题。** 上述结论比较的是指定目标的因子化能力，不断言两层外作用核相同。

**证明。** $C_8$ 的取逆自同构在 $C_8/\Phi(C_8)=C_2$ 上为恒等，在 $C_8$ 上却非恒等。交换群没有非平凡内自同构，故两层外核不同。其区别为 $2$ 群信息，正是非交换有限单群目标无法作为正规像保留的部分。

## 31. 同一中心平凡基商上的有限多素数组合

**引理。** 若 $B\le A_1\times\cdots\times A_t$ 对每侧满射，且 $\theta:B\twoheadrightarrow F$ 满射到非交换单群，则 $\theta$ 经至少一个坐标投影 $B\to A_i$ 因子化。

**证明。** 两因素时，两个坐标投影的核彼此交换。它们在 $F$ 中的像都正规，所以各为 $1$ 或 $F$；不可能同时为 $F$，否则 $F$ 交换。因此至少一个坐标核被 $\theta$ 消去。有限多个因素时，将前 $t-1$ 个坐标的联合像视为一个因素，归纳即可。

**定理。** 保留第 27 节的中心平凡、外作用平凡基商 $S=\pi/N$，固定满射 $f:\Lambda\twoheadrightarrow F$ 到非交换有限单群。令 $K_1,\ldots,K_t$ 为 $\pi$ 的有限指数特征子群，各 $K_i\subseteq N$，且 $N/K_i$ 分别为素数幂群，允许素数重复。令 $K=\bigcap_i K_i$。如果 $f$ 经 $\pi/K$ 的实际外作用像因子化，那么对其中至少一个素数 $\ell$，$f$ 已经经第 27 节的单个 $\Psi_\ell$ 因子化。

**证明。** 合并相同素数的核，再将每个核与相应的 $N_\ell$ 取交。这只使观察更细，仍保持相应的素数幂性质。于是可假设素数两两不同且 $K_i\subseteq N_{\ell_i}$。不同素数幂群的直积中，每个逐坐标满射子群等于全直积：其阶被每个因素阶整除，也整除这些互素阶的乘积。因此

$$P=N/K\cong\prod_i N/K_i,\qquad
\Phi(P)=\prod_i\Phi(N/K_i).$$

从 $\pi/K$ 到 $\pi/(\bigcap_iN_{\ell_i})$ 的外作用像之核可解。证明与第 29 节相同：限制到各特征 Sylow 子群的 Frattini 核是相应的素数幂群，限制核又嵌入以 $Z(P)\cap\Phi(P)$ 为系数的交换余循环群。所以给定的 $f$ 下降到联合首次同调商。

联合首次同调商的核为 $\prod_iV_{\ell_i}$，中心平凡基商仍为 $S$。第 28 节的归一化余循环论证在这个有限交换系数群上同样成立：从实际外作用像到联合修正作用 $\operatorname{im}(\Psi_{\ell_1},\ldots,\Psi_{\ell_t})$ 的核为交换群的子群。非交换单群目标再次消去这个正规可解核。最后应用本节引理，$f$ 经某个单独的 $\Psi_{\ell_i}$ 因子化。

**推论。** 对这个固定 $N$ 和目标 $f$，若每个素数的一次修正同调作用都不能实现 $f$，则任意有限多个覆盖核内的素数幂提升联合后也不能实现 $f$。若某个 $\Psi_\ell$ 实现 $f$，单个 $Q_\ell$ 就已经足够。

**证明。** 必要性来自定理，充分性来自第 28 节。此结论不限制更换 $N$ 后的可能性，也不包括任意非素数幂扩张核。

## 32. 实际曲线轨道的有限矩阵验收

**定理。** 在第 27 节的条件下，令 $\Lambda$ 作用于 $X$，$\alpha\in X$，$H=\operatorname{Stab}_\Lambda(\alpha)$。固定满射 $f:\Lambda\twoheadrightarrow F$ 到非交换有限单群，且 $f(H)<F$，记 $\Gamma=\ker f$。对每个素数 $\ell$，令 $L_\ell=\Psi_\ell(\Lambda)$，$B_\ell=\operatorname{im}(f,\Psi_\ell)\le F\times L_\ell$。则

$$\boxed{C_\ell\alpha\subseteq\Gamma\alpha
\quad\Longleftrightarrow\quad
B_\ell\cap(F\times\{1\})=\{(1,1)\}
\quad\Longleftrightarrow\quad |B_\ell|=|L_\ell|.}$$

**证明。** 第 18 节将轨道条件化为同一个 $f$ 经过实际外作用的因子化；第 28 节将后者化为经过修正同调作用的因子化。$B_\ell\to L_\ell$ 满射，其核就是显示的交，有限性给出阶数等价。条件失败时单性给出 $B_\ell=F\times L_\ell$，而非一个未指定的中间情形。

**构造。** 对实际闭曲面有限覆盖，选择标准生成元 $x_1,\ldots,x_{2g}$ 及关系词 $r$。令 $q_0:\pi\to S$ 为覆盖商，在 $\mathbb F_\ell$ 上构造胞腔链复形

$$\mathbb F_\ell[S]\xrightarrow{\partial_2}
\mathbb F_\ell[S]^{2g}\xrightarrow{\partial_1}\mathbb F_\ell[S].$$

顶点为 $v\in S$，边 $(v,j)$ 从 $v$ 到 $v q_0(x_j)$，二维胞腔边界按从 $v$ 开始提升关系词 $r$ 计算。因此 $V_\ell=\ker\partial_1/\operatorname{im}\partial_2$。若代表 $\eta$ 在 $S$ 上为 $\operatorname{Ad}_{s_\eta}$，其修正链映射将顶点 $v$ 送到 $v s_\eta^{-1}$，将边 $(v,j)$ 送到从 $v s_\eta^{-1}$ 出发的词 $\eta(x_j)$ 的提升路径。

**命题。** 该链映射在同调上诱导的正是 $\Psi_\ell$，且与左甲板作用交换。若给定同一有限生成集 $\gamma_1,\ldots,\gamma_k$ 的实际源自同构词和实际 $f(\gamma_i)$，则 $B_\ell$ 由配对矩阵数据 $(f(\gamma_i),\Psi_\ell(\gamma_i))$ 生成。

**证明。** 新路径的终点为

$$v s_\eta^{-1}q_0(\eta(x_j))=v q_0(x_j)s_\eta^{-1},$$

与端点的修正映射一致。关系词被源自同构保持，所以边界映到边界。该提升是原映射提升再复合甲板变换 $s_\eta^{-1}$，故在同调上为定义中的修正作用；顶点和路径的公式直接给出与左甲板作用交换。生成元像决定联合像，得到最后的配对生成结论。

**命题。** 上述有限验收不从覆盖的存在、同调维数或单独的像大小推出一个满足条件的覆盖。对于第 17 节的固定 $(f,\Gamma,\alpha)$，要通过这一族解决其轨道问题，仍须找到一个中心平凡、外作用平凡的特征基商 $S$ 及素数 $\ell$，使显示的交确实平凡；或采用不在本族内的其他特征商。

**证明。** 上述等价式右侧要求同一个 $f$ 与同一个实际同调作用之间存在因子化，而所述存在性和大小数据均未提供该关系。第 30–31 节只消去固定基商上的多余提升选择，没有给出更换基商后的统一存在定理。对一般有限指数 $\Gamma$，其正规核商也未必为非交换单群，故不能不加说明地使用这里的单性步骤。

## 33. 通用模二同调覆盖的全部符号分块

**定义。** 固定闭可定向曲面 $\Sigma_g$，$g\ge3$，令 $\pi=\pi_1(\Sigma_g)$、$M=\operatorname{Mod}^{+}(\Sigma_g)$，并定义

$$N_2=[\pi,\pi]\pi^2=\ker(\pi\to H_1(\Sigma_g;\mathbb F_2)),\qquad S=\pi/N_2\cong(\mathbb Z/2)^{2g}.$$

这里 $N_2$ 在 $\pi$ 中特征。对奇素数 $\ell$，令 $V=H_1(N_2;\mathbb F_\ell)$、$Q=\pi/[N_2,N_2]N_2^\ell$，并记实际外作用 $a:M\to\operatorname{Out}(Q)$。设 $\widehat S=\operatorname{Hom}(S,\{\pm1\})$，$X=\widehat S\setminus\{1\}$，$r=|X|=4^g-1$。对 $\chi\in\widehat S$，记 $W_\chi$ 为甲板作用的 $\chi$ 特征空间。

**命题。** 有正交辛分解

$$V=\bigoplus_{\chi\in\widehat S}W_\chi,\qquad
\dim W_1=2g,\qquad \dim W_\chi=2g-2\ (\chi\ne1).$$

因而 $\dim V=2+(2g-2)4^g$。每个非平凡分块均可识别为对应连通二重覆盖的反不变同调。

**证明。** $|S|$ 在 $\mathbb F_\ell$ 中可逆，且全部字符值已在该域内，所以投影 $e_\chi=|S|^{-1}\sum_{s\in S}\chi(s)s$ 给出分解。不同字符的配对为零，因为甲板变换保持交叉形式；各自逆字符等于自身，所以各分块上的形式非退化。覆盖胞腔链群分别为 $\mathbb F_\ell[S]$、$\mathbb F_\ell[S]^{2g}$、$\mathbb F_\ell[S]$；零阶和二阶同调都是平凡表示。半单性使链复形的表示类恒等式成为

$$V\cong\mathbb F_\ell^2\oplus\mathbb F_\ell[S]^{2g-2}.$$

取各特征空间即得维数。向 $\ker\chi$ 对应的中间二重覆盖转移时，覆盖度为 $2^{2g-1}$，可逆的平均化识别其反不变空间与 $W_\chi$。

**定义。** 令 $U=M[2]$ 为模二同调作用的核。$U$ 固定所有字符；其在 $W_\chi$ 上的作用因提升选择相差 $\pm I$，所以定义良好的射影辛表示为

$$p_\chi:U\to D_\ell:=\operatorname{PSp}_{2g-2}(\mathbb F_\ell).$$

该表示经 $a(U)$ 因子化，因为 $Q$ 的内自同构在 $V$ 上是甲板作用，在每个符号分块上只是 $\pm I$。这里没有使用第 27 节的中心平凡基商假设；当前的 $S$ 是交换群，采用射影作用消除提升歧义。

## 34. 真实分离扭转的分块支撑、秩和外阶

**定理。** 设本质分离简单闭曲线 $\alpha$ 将 $\Sigma_g$ 分成亏格 $h$ 与 $g-h$ 两侧，$1\le h<g$。若字符 $\chi\ne1$ 在其中一侧为平凡，则 $p_\chi(T_\alpha)=1$；若在两侧均非平凡，则一个标准提升在 $W_\chi$ 上是非平凡秩一幺幂变换，其阶恰为 $\ell$。

对通用模二覆盖上由全部提升曲线的正 Dehn 扭转之积给出的标准提升 $\widetilde T_\alpha$，有

$$\boxed{\operatorname{rank}(\widetilde T_{\alpha,*}-I)=(4^h-1)(4^{g-h}-1),\qquad
(\widetilde T_{\alpha,*}-I)^2=0.}$$

并且 $a(T_\alpha)$ 在 $\operatorname{Out}(Q)$ 中的阶恰为 $\ell$。

**证明。** 在对应的二重覆盖中，$\alpha$ 有两个度数一的提升。如果字符在一侧平凡，这一侧提升为两份，两条提升曲线分别分离，所以同调上的扭转均平凡。如果字符在两侧非平凡，两侧的提升均连通且各有两个边界分量。连接图是两顶点两条边，因此每条提升曲线都非分离，两者的同调类互为相反数。取其中一个本原类 $v$，标准提升作用为 $x\mapsto x+2\langle x,v\rangle v$，且 $v$ 位于反不变部分。奇特征下系数与转移产生的二次幂因子均可逆，故限制秩为一且非零。分离扭转在平凡字符块上为恒等。

两侧非平凡字符的数目是 $(4^h-1)(4^{g-h}-1)$，得到总秩。所有提升曲线两两不交，相应秩一增量的两两乘积为零，所以总增量平方为零。在 $V$ 上其 $\ell$ 次幂为恒等，在 $S$ 上也为恒等。一个同时固定扩张核 $V$ 及商 $S$ 的自同构由 $Z^1(S,V)$ 给出；由于 $\ell\nmid|S|$，平均化使每个余循环成为余边界，所以该自同构在 $Q$ 上由 $V$ 中的元素实现内共轭。这证明外阶整除 $\ell$。至少一个活跃块给出非平凡 $\ell$ 阶射影变换，故外阶恰为 $\ell$。秩公式针对所指定的标准提升；任意其他提升可以多出甲板符号，未把其秩混同。

**实例。** 当 $g=3$、$h=1$ 时，覆盖度为 $64$，覆盖亏格为 $129$，$V$ 的维数为 $258$。它有一个六维平凡块、六十三个四维非平凡块；分离扭转在其中四十五个块上非平凡，标准提升的增量秩为 $45$。

## 35. Johnson 核上的全部 Prym 分块彼此独立

**定义。** 记 $\mathcal I_g$ 为 Torelli 群、$\mathcal K_g=\mathcal J_2$ 为 Johnson 核。它们正规于 $M$，且 $\mathcal K_g\subseteq\mathcal I_g\subseteq U$。使用有限辛群的经典性质：当 $g\ge3$ 且 $\ell$ 为奇素数时，$D_\ell$ 是非交换单群；标准辛初等变换生成相应辛群。

**引理。** 对每个 $\chi\in X$，$p_\chi(U)=D_\ell$，且 $p_\chi(\mathcal K_g)=D_\ell$。

**证明。** 选择几何标记，使 $\chi$ 只在最后一个把手上非平凡。其余亏格 $g-1$ 的单边界子曲面在二重覆盖中有两份；成对同调差给出 $W_\chi$ 的辛基，交叉形式为标准形式的非零二倍。该子曲面上简单曲线的扭转平方属于 $U$，在反不变部分给出参数为 $2$ 的辛转移。取幂得到任意模 $\ell$ 参数，标准曲线所给出的这些初等变换生成整个辛群。因此射影像满射。因为 $\mathcal K_g$ 正规，其像正规于 $D_\ell$；选择一个使 $\chi$ 在两侧非平凡的分离曲线，上一节给出一个非单位像，而该扭转属于 $\mathcal K_g$。单性强制其像为整个 $D_\ell$。

**引理。** 不同 $\chi,\psi\in X$ 在 $\mathcal K_g$ 上的表示核不同。

**证明。** 用模二交叉形式把字符识别为不同的非零向量 $x,y\in H_1(\Sigma_g;\mathbb F_2)$。存在辛二平面 $W$，使 $x\in W$ 而 $y$ 在 $W$ 和 $W^\perp$ 上的投影都非零。具体地，取 $z$ 使 $\langle x,z\rangle=1$。若 $\langle x,y\rangle=0$，再要求 $\langle y,z\rangle=1$，两个独立线性条件有解。若 $\langle x,y\rangle=1$，在该仿射超平面中避开 $y,x+y$ 即可。令 $W=\langle x,z\rangle$，就满足上述要求。模二辛基可提升为整数辛基，并由曲面映射类实现，因此 $W$ 可取为亏格一子曲面的一阶模二同调。

令 $\alpha$ 为其边界。字符 $\chi$ 在补侧平凡，字符 $\psi$ 在两侧均非平凡。所以 $p_\chi(T_\alpha)=1$ 而 $p_\psi(T_\alpha)\ne1$。同一个真实分离扭转区分两个核。

**定理。** 联合映射满射：

$$\boxed{(p_\chi)_{\chi\in X}:\mathcal K_g\twoheadrightarrow D_\ell^{\,4^g-1}.}$$

**证明。** 各坐标满射且核互不相同。应用第 21 节的非交换单群次直积论证：若新增坐标与前面坐标的联合像不是整个直积，则它经前面某一个单群因素的自同构因子化，于是两个原满射核相同，矛盾。该步骤证明联合像，不以各坐标单独满射代替独立性。

## 36. 一个完全指定的合同商与一族正向轨道解

**定义。** 全映射类群在 $X$ 上通过 $G_2=\operatorname{Sp}_{2g}(\mathbb F_2)$ 置换字符。为各 $W_\chi$ 选择辛基，将不同分块之间的辛同构射影化，得到块置换表示

$$\mathcal R_\ell:M\longrightarrow D_\ell^X\rtimes G_2,$$

其中 $G_2$ 按其在非零字符上的自然作用置换直积因素。更换覆盖提升只增加各块的标量 $\pm I$，故不改变此表示。基选择只共轭目标表示。

**定理。** $\mathcal R_\ell$ 满射，且经 $a(M)$ 因子化。因此

$$\boxed{M\twoheadrightarrow D_\ell^{\,4^g-1}\rtimes\operatorname{Sp}_{2g}(\mathbb F_2)}$$

是来自实际特征曲面商 $Q$ 的合同商。

**证明。** 第 35 节表明 $\mathcal K_g$ 的像已经包含全部基群 $D_\ell^X$。模二辛表示满射，给出全部置换商 $G_2$。含有整个基群并满射到商的子群必为整个半直积。若一个映射类在 $Q$ 上以内自同构作用，它在 $S$ 上为恒等，因为 $S$ 交换；在各字符块上为甲板符号，所以 $\mathcal R_\ell$ 的像为恒等。因而 $\ker a\subseteq\ker\mathcal R_\ell$，得到所需因子化及合同性。

**定义。** 固定 $\chi\in X$，记 $M_\chi$ 为其稳定子，$p_\chi$ 在此群上同样良定义。令

$$\Gamma_{\chi,\ell}=\ker(p_\chi:M_\chi\to D_\ell),\qquad
\Delta_\ell=\ker\mathcal R_\ell.$$

**定理。** 这些是 $M$ 的有限指数子群，且

$$[M:\Gamma_{\chi,\ell}]=(4^g-1)|D_\ell|,\qquad
[M:\Delta_\ell]=|D_\ell|^{4^g-1}|\operatorname{Sp}_{2g}(\mathbb F_2)|.$$

此外，$\Delta_\ell$ 是 $\Gamma_{\chi,\ell}$ 在 $M$ 中的正规核，包含主合同核 $\ker a$，而且对每条本质简单闭曲线 $\alpha$，都有

$$\boxed{\Delta_\ell\alpha\subseteq\Gamma_{\chi,\ell}\alpha.}$$

**证明。** $G_2$ 在 $X$ 上传递，故 $[M:M_\chi]=4^g-1$；$p_\chi$ 已在其子群 $\mathcal K_g$ 上满射，得到第一个指数。第二个指数来自半直积满射。目标中对应 $\Gamma_{\chi,\ell}$ 的子群要求置换固定 $\chi$，且该坐标为单位元。若一个元素属于这个子群的全部共轭，则其置换固定所有字符，故置换为恒等；再逐字符检查得到全部坐标为单位元。因而其正规核平凡，拉回即为 $\Delta_\ell$。最后 $\Delta_\ell\subseteq\Gamma_{\chi,\ell}$ 直接给出轨道包含。

**命题。** $\Gamma_{\chi,\ell}$ 不包含 Torelli 群，因此上述输入族不能仅由底曲面的一阶同调稳定条件描述。

**证明。** 第 34 节给出一个属于 $\mathcal K_g$ 的分离扭转，其 $p_\chi$ 像非平凡。它属于 Torelli 群却不属于 $\Gamma_{\chi,\ell}$。上述结论只为显示的子群族及其上群构造轨道控制，不涵盖任意给定的有限指数子群。

## 37. 全局有限单群目标仍准确下降到底曲面同调

**引理。** 设 $L\triangleleft M$ 满足 $L\subseteq M[2]\cap M[\ell]$，令

$$R_L=L\cap\bigcap_{\chi\in X}\ker p_\chi.$$

则 $a(R_L)$ 是 $a(M)$ 的正规初等交换二群。

**证明。** 字符被全映射类群置换，所以 $R_L$ 正规。取其元素的任意覆盖提升。它固定 $S$，在平凡字符同调块上为恒等；在每个非平凡辛块上为标量 $\pm I$，因为其射影辛作用平凡。因此其平方在 $V$ 与 $S$ 上均为恒等。由于 $\ell\nmid|S|$，前述余循环平均化表明该平方在 $Q$ 上是内自同构。故 $a(R_L)$ 中每个元素的阶整除二，整个群为初等交换二群。

**定理。** 对任意满射 $f:M\twoheadrightarrow F$ 到非交换有限单群，以下等价：

$$\boxed{f\text{ 经 }a(M)\text{ 因子化}
\quad\Longleftrightarrow\quad
f\text{ 经 }M\to\operatorname{Sp}_{2g}(\mathbb Z/(2\ell))\text{ 因子化}.}$$

这里要求同一个源同态 $f$ 因子化，而非仅比较目标群的同构类型。

**证明。** 先假设 $f=\theta a$。$f(\mathcal K_g)$ 正规于 $F$，所以为 $1$ 或 $F$。取上一引理中的 $L=\mathcal K_g$。其射影核像是正规二群，被 $\theta$ 消去。若 $f(\mathcal K_g)=F$，第 35 节因而给出一个满射 $D_\ell^X\to F$。非交换单群目标只允许一个直积因素映为整个 $F$，其余因素映为 $1$：各因素的像正规且两两交换。但是全 $M$ 传递置换这些因素，且 $f$ 的核正规，所以无法只保留一个因素。这与 $|X|>1$ 矛盾。因此 $f(\mathcal K_g)=1$；$\mathcal I_g/\mathcal K_g$ 交换还给出 $f(\mathcal I_g)=1$。

为得到准确模数，令 $L=M[2\ell]$。对任意 $x\in L$，第 35 节给出 $k\in\mathcal K_g$，使 $p_\chi(x)=p_\chi(k)$ 对全部 $\chi$ 成立。于是 $xk^{-1}\in R_L$。上一引理及单性给出 $f(R_L)=1$，而 $f(k)=1$，故 $f(x)=1$。所以 $f$ 经模 $2\ell$ 辛表示因子化。

反向计算实际商的阿贝尔化。$N_2$ 在 $\pi^{\mathrm{ab}}\cong\mathbb Z^{2g}$ 中的像为 $2\mathbb Z^{2g}$，$[N_2,N_2]N_2^\ell$ 的像为 $2\ell\mathbb Z^{2g}$，因此

$$Q^{\mathrm{ab}}\cong(\mathbb Z/(2\ell))^{2g}.$$

在 $Q$ 上为内自同构的元素在此阿贝尔化上必为恒等，故模 $2\ell$ 辛表示经过 $a(M)$，完成反向因子化。该证明没有把第 36 节的大半直积像错误地当作一个新的全局单群商。

## 38. 同一模二基覆盖上全部素数幂提升的剩余范围

**定理。** 固定一个满射 $f:M\twoheadrightarrow F$ 到非交换有限单群，并假设 $f(\mathcal I_g)=F$。令 $K_1,\ldots,K_t$ 为 $\pi$ 的特征子群，各 $K_i\subseteq N_2$，且 $N_2/K_i$ 为有限素数幂群。对联合特征商 $q:\pi\to\pi/\bigcap_iK_i$，$f$ 不能经实际外作用 $a_q(M)$ 因子化。

**证明。** 单个奇素数情形由第 30 节下降到第 37 节，后者只允许底曲面同调因子化，与 $f(\mathcal I_g)=F$ 矛盾。素数二时，首次提升 $\pi/[N_2,N_2]N_2^2$ 本身是有限二群，其 Frattini 商为 $\pi/N_2$；相对 Frattini 核为二群，因而其非交换有限单群目标也下降到模二底同调。

联合情形需要处理共同内共轭，不能直接等同各层外核的交。先合并同素数的核；再与各自首次同调核取交，只使观察更细。记剩余素数两两不同、$P_i=N_2/K_i$。它们阶数互素，$N_2$ 的逐坐标满射联合像就是 $\prod_iP_i$。因此联合曲面商是各 $Q_i=\pi/K_i$ 在共同交换商 $S$ 上的完整纤维积。

考虑从联合外作用像到各坐标外作用像联合的映射。若一个自同构在每个坐标上为内自同构，可用一组共轭元 $(z_i)\in\prod_iQ_i$ 表示。因为 $S$ 交换，任何这样的元组都保持纤维积。由纤维积中的元组给出的作用已经是联合内共轭。全部元组模纤维积的商为 $S^{t-1}$，所以该外作用误差核是初等交换二群的商的子群。非交换单群目标消去这项正规误差，继续经过各坐标外作用的联合像因子化。第 31 节的次直积引理使它再经过至少一个坐标，归结为已排除的单素数情形。

**推论。** 取第 16–17 节的同一个 $f$、$\Gamma=\ker f$ 和分离曲线 $\alpha$。对于本节全部单个及有限联合提升，均有

$$\boxed{\ker(a_q)\alpha\not\subseteq\Gamma\alpha.}$$

**证明。** $f(\operatorname{Stab}(\alpha))<F$，所以第 18 节把所需轨道包含等价为同一个 $f$ 的因子化，与定理矛盾。这些商允许非幂零目标，但都在指定的模二覆盖核内作素数幂提升。结论没有排除其他基覆盖或一般扩张核，也不反驳不限制观察族的轨道合同猜想。

## 39. 没有分块置换障碍的非交换基覆盖

**定理。** 保留第 27 节的中心平凡、外作用平凡基商 $S=\pi/N$，并令 $\pi$ 来自闭亏格 $g\ge2$ 曲面。设 $\ell\nmid|S|$，取有限分裂域 $k/\mathbb F_\ell$。对于每个不可约 $k[S]$ 模 $U_\chi$，令 $d_\chi=\dim_kU_\chi$，$M_\chi=\operatorname{Hom}_{k[S]}(U_\chi,V_\ell\otimes k)$。则

$$V_\ell\otimes k\cong\bigoplus_\chi U_\chi\otimes_kM_\chi,\qquad
\dim_kM_\chi=(2g-2)d_\chi+2\mathbf1_{\chi=1}.$$

修正作用 $\Psi_\ell$ 保持每个同型分块，并给出 $\psi_\chi:\Lambda\to\operatorname{GL}(M_\chi)$。对同一个非交换有限单群满射 $f:\Lambda\twoheadrightarrow F$，

$$\boxed{f\text{ 经 }\Psi_\ell(\Lambda)\text{ 因子化}
\quad\Longleftrightarrow\quad
f\text{ 经某个 }\psi_\chi(\Lambda)\text{ 因子化}.}$$

**证明。** 半单群代数和覆盖链复形给出 $V_\ell\otimes k\cong k^2\oplus k[S]^{2g-2}$。正则表示中 $U_\chi$ 的重数为 $d_\chi$，从而得到显示维数。修正作用与 $S$ 交换，所以在同型块上为 $I\otimes\psi_\chi$，不发生由外作用引起的不可约类型置换。所有块作用联合起来忠实记录 $\Psi_\ell$ 的像，域扩张不改变其核。应用第 31 节的有限次直积引理，得到准确的单块因子化条件。反向直接投影到该块。

**命题。** 若 $\Lambda=M$ 且 $f(\mathcal I_g)=F$，平凡字符块不能实现 $f$。任何成功块必须为非平凡 $S$ 类型，并满足同源联合像条件

$$\operatorname{im}(f,\psi_\chi)\cap(F\times\{1\})=\{(1,1)\}.$$

**证明。** 平凡甲板类型的同调由底曲面同调转移得到，Torelli 群在其上为恒等。其余条件由第 18 节的因子化判据得到。上述分解只缩小固定候选的检验对象；它不构造满足条件的 $N,\ell,\chi$。半单分解必须保留 $\ell\nmid|S|$；不能把有限李型群在其定义特征中的自然表示无条件代入这一跨特征分解。

## 40. 正多扭转的实际同调矩阵与图循环格

**定义。** 设 $Y$ 为闭、连通、可定向曲面，亏格为 $G$，$c_e$ 是有限族两两不交的本质简单闭曲线。每条曲线作为一条独立分支计数，允许不同分支同位。令 $\mathcal D$ 为沿全部 $c_e$ 切开后的对偶多重图：顶点为补集分支，边为切割曲线，允许环边与重边。该图连通。记其顶点、边数为 $v,e$，循环秩为 $b=e-v+1$。取各边的方向和一棵生成树，将基本整数循环作为列组成矩阵 $Z\in M_{e\times b}(\mathbb Z)$。置

$$Q_{\mathcal D}=Z^{\mathsf T}Z.$$

令 $W=\prod_e T_{c_e}$，所有扭转均为同一正向且指数为 $1$。约定交叉配对与正向扭转满足 $T_c(x)=x+\langle x,[c]\rangle[c]$。记 $A=W_*\in\operatorname{Aut}(H_1(Y;\mathbb Z))$，$U=A-I$。

**定理。** 曲线类生成一个秩为 $b$ 的本原迷向子格 $L\subset H_1(Y;\mathbb Z)$。存在整数辛基，使 $U$ 唯一可能非零的块为 $Q_{\mathcal D}$，从 $b$ 个对偶基向量映向 $L$。特别地，

$$U^2=0,\qquad \operatorname{rank}_{\mathbb Q}U=b,\qquad
U(x)=\sum_e\langle x,[c_e]\rangle[c_e].$$

**证明。** 给图定向，令 $B:\mathbb Z^e\to\mathbb Z^v$ 为整数关联矩阵。每个补集分支的定向边界给出一项曲线类关系，因此 $\operatorname{im}B^{\mathsf T}$ 位于映射 $\mathbb Z^e\to H_1(Y;\mathbb Z)$ 的核。

对每个非树边，取其对应的切割曲线作为候选基向量。树上从该边一端到另一端的路径与该边构成基本循环，可在各连通补集分支内接起穿越路径，得到与该非树曲线交叉数为 $1$、与其他非树曲线交叉数为 $0$ 的同调类。这证明候选曲线类线性无关，并给出其生成子格的整数左逆，故该子格本原。树的顶点边界关系将其余曲线类唯一写为这些基向量的整数线性组合。关系恰为 $\operatorname{im}B^{\mathsf T}$，系数矩阵正是 $Z$ 的各行。曲线互不相交，所以 $L$ 迷向，且可把该本原迷向基扩充为整数辛基；各补集分支内部的同调给出剩余的固定方向。

单次 Dehn 扭转的同调公式及曲线类之间交叉数为零，给出 $U$ 的求和式及 $U^2=0$。在刚才构造的对偶基上，矩阵元为 $\sum_eZ_{ei}Z_{ej}$，即 $Z^{\mathsf T}Z$。$Z$ 的非树边行组成单位矩阵，因此列满秩；实数上的正定性给出 $\operatorname{rank}_{\mathbb Q}U=b$。这一步没有把任意特征下的秩等同于有理数秩。

## 41. 图临界群、实际返回商与所有模数的周期

**定义。** 令图临界群为

$$\mathcal K(\mathcal D)=\operatorname{Div}^0(\mathcal D)/\operatorname{im}(BB^{\mathsf T}),$$

其中 $\operatorname{Div}^0(\mathcal D)$ 为顶点整数系数和为零的格。当 $b>0$ 时，记 $Q_{\mathcal D}$ 的正 Smith 不变量为 $s_1\mid\cdots\mid s_b$，保留其中等于 $1$ 的项。

**定理。** 有

$$\operatorname{coker}Q_{\mathcal D}\cong\mathcal K(\mathcal D).$$

因此，对任意非零整数 $n$，实际整数返回商满足

$$\boxed{H_1(Y;\mathbb Z)/(A^n-I)H_1(Y;\mathbb Z)
\cong\mathbb Z^{2G-b}\oplus\bigoplus_{i=1}^b\mathbb Z/(|n|s_i).}$$

$b=0$ 时直接为 $\mathbb Z^{2G}$。$n=0$ 时也直接为 $\mathbb Z^{2G}$，不把它纳入非零时间的有限挠部表达式。

**证明。** 图连通意味着 $\operatorname{im}B=\operatorname{Div}^0(\mathcal D)$。记循环格 $Z_1=\ker B$、割格 $B^1=\operatorname{im}B^{\mathsf T}$。循环格本原，故它的任意整数线性泛函可扩张到 $\mathbb Z^e$。标准点积因而给出满射 $\mathbb Z^e\to Z_1^*$。该映射的核恰为割格：若整数边向量与全部基本循环垂直，沿生成树积分产生整数顶点势，其在非树边上的差由循环垂直性保证，所以该边向量等于 $B^{\mathsf T}$ 作用于这个势。

于是 $\mathbb Z^e/B^1\cong Z_1^*$，而 $Z_1$ 到其对偶的嵌入由 $Q_{\mathcal D}$ 表示。另一方面，通过 $B$ 得到

$$\mathbb Z^e/(Z_1+B^1)\cong\operatorname{Div}^0(\mathcal D)/\operatorname{im}(BB^{\mathsf T}).$$

这给出第一项。第 40 节的同调块和 $U^2=0$ 给出 $A^n-I=nU$，包括负整数 $n$。对非零块取 Smith 形即得实际返回商。

**推论。** 对任意素数 $\ell$，

$$\boxed{\operatorname{rank}_{\mathbb F_\ell}(A-I)
=b-\dim_{\mathbb F_\ell}\mathcal K(\mathcal D)[\ell]
=\#\{i:\ell\nmid s_i\}.}$$

对任意正整数 $m$，$A$ 在 $H_1(Y;\mathbb Z/m)$ 上的准确阶为

$$\boxed{\operatorname{ord}(A\bmod m)=m/\gcd(m,s_1)\quad(b>0).}$$

$b=0$ 时阶为 $1$。循环矩阵满秩在模素数后可能失效；只有当 $\ell$ 整除全部 $s_i$，即整除 $s_1$ 时，整个同调作用才为恒等。

**证明。** Smith 形在模 $\ell$ 后将秩问题化为各对角项是否为零；临界群的 $\ell$ 挠子群维数就是被 $\ell$ 整除的项数。$A^n=I+nU$，故模 $m$ 恒等恰当且仅当 $m\mid ns_i$ 对所有 $i$ 成立。因 $s_1$ 整除其余项，条件等价于 $m\mid ns_1$，最小正解如式。

**推论。** 若 $M_W$ 是实际多扭转 $W$ 的三维映射环面，则

$$\operatorname{Tor}H_1(M_W;\mathbb Z)\cong\mathcal K(\mathcal D).$$

**证明。** 映射环面的同调精确序列给出 $0\to\operatorname{coker}(A-I)\to H_1(M_W;\mathbb Z)\to\mathbb Z\to0$。最后一项自由，故序列分裂。取挠部并用定理。

## 42. 真正的有限曲面覆盖与对偶陪集图

**定义。** 设 $q_0:\pi_1(\Sigma_g)\twoheadrightarrow S$ 给出连通正则有限无分歧覆盖 $Y\to\Sigma_g$。令 $\alpha$ 为本质分离简单闭曲线，两侧子曲面群的像为 $A_0,B_0\le S$，边界循环群像为 $C_0=\langle q_0(\alpha)\rangle$，记 $d=|C_0|$。对偶图有顶点集 $S/A_0\sqcup S/B_0$，边集 $S/C_0$，边 $sC_0$ 连接 $sA_0$ 与 $sB_0$。

**定理。** 上述图正是沿 $\alpha$ 的全部提升切开 $Y$ 后的对偶图，且

$$b=\frac{|S|}{d}-\frac{|S|}{|A_0|}-\frac{|S|}{|B_0|}+1.$$

$T_\alpha^d$ 有一个在提升后的补集上为恒等的提升 $W$，其在每条提升曲线上恰作一次正扭转。因此，第 40–41 节作用于这个真实提升。

**证明。** 补集分支由两侧子曲面群的陪集标记，边界提升由边界循环群的陪集标记，包含关系给出端点。$A_0,B_0$ 生成 $S$，故图连通。每条提升边界到 $\alpha$ 的度均为 $d$，圆环坐标中的一次底层旋转提升为 $1/d$ 次旋转；底层取 $d$ 次扭转后，提升在每个圆环上为一次扭转，边界上恒等，可以与补集的恒等映射拼合。数顶点和边给出公式。

**推论。** 在第 27 节的中心平凡、外作用平凡假设下，若 $T_\alpha\in\Lambda$，则

$$\Psi_\ell(T_\alpha)^d=W_*\bmod\ell.$$

令 $\epsilon_\ell=1$ 当 $b=0$ 或 $\ell\mid s_1$，其余情形令 $\epsilon_\ell=\ell$。则上式右侧的准确阶为 $\epsilon_\ell$。

**证明。** 选基点在圆环外。$T_\alpha^d$ 在基商 $S$ 上逐点恒等；对应的内共轭元的 $d$ 次幂在 $Z(S)=1$ 中，因此第 27 节的修正在这个幂次上消失。基点提升固定的曲面映射正是前述 $W$。模素数的阶由第 41 节得到。

**例。** 亏格二曲面到 $C_2$ 的满射可取 $a_1,a_2$ 均映到非平凡元，$b_1,b_2$ 映到单位元。中间分离曲线的两侧均映满 $C_2$，边界映为单位元。对偶图是两个顶点之间的两条重边，$Q_{\mathcal D}=(2)$。两个提升曲线的同调类均非零，但它们的一次正多扭转在模 $2$ 同调上为恒等。这个覆盖是正则覆盖；此处不主张其核对整个映射类群特征。

## 43. 典范特征同调覆盖的全参数秩公式

**定义。** 固定素数 $p$、$g\ge2$，令

$$N_p=\ker(\pi_1(\Sigma_g)\to H_1(\Sigma_g;\mathbb F_p)).$$

对应覆盖的度为 $D=p^{2g}$，亏格为 $\widetilde g=1+D(g-1)$。取一条将曲面分为亏格 $h$ 与 $g-h$ 两侧的本质分离曲线，$1\le h<g$。设 $a=p^{2h}$、$b=p^{2(g-h)}$。

**定理。** 沿该曲线全部提升切开的对偶图为完全二部图 $K_{a,b}$，其正多扭转的循环格矩阵可取

$$Q=(I_{a-1}+J_{a-1})\otimes(I_{b-1}+J_{b-1}),$$

其中 $J$ 为全 $1$ 矩阵。对每个素数 $\ell$，

$$\boxed{\operatorname{rank}_{\mathbb F_\ell}(W_*-I)
=(a-1-\mathbf1_{\ell\mid a})(b-1-\mathbf1_{\ell\mid b}).}$$

因此，$\ell=p$ 时秩为 $(a-2)(b-2)$，$\ell\ne p$ 时秩为 $(a-1)(b-1)$。在每个正模数 $m$ 上，$W_*$ 的准确阶均为 $m$。

**证明。** 基商分解为两侧同调子空间的直和，阶分别为 $a,b$。边界为交换子积，像平凡。陪集图的每个左顶点与每个右顶点之间恰有一条边，故得到 $K_{a,b}$。选以一个左顶点及一个右顶点为中心的双星生成树。每个非树边对应的基本循环是一个四边形，它们的内积为 $(\delta_{ii'}+1)(\delta_{jj'}+1)$，给出 Kronecker 乘积表达式。

对 $r=a-1$，$I_r+J_r$ 的核方程迫使各坐标相等；设公共坐标为 $c$，则剩余条件为 $ac=0$。所以它在特征 $\ell$ 下的秩为 $a-1-\mathbf1_{\ell\mid a}$。对另一因素同理，Kronecker 乘积的秩为秩的乘积。因 $a,b\ge4$，矩阵中存在值为 $1$ 的非对角元，其全部矩阵元的最大公因数为 $1$，即 $s_1=1$。第 41 节给出所有模数的准确阶。

**例。** $g=2,p=2,h=1$ 时，覆盖度为 $16$，同调维数为 $34$，图循环秩为 $9$；扭转的模 $2$ 秩为 $4$，其他素数的秩为 $9$。$g=3,p=2,h=1$ 时，覆盖度为 $64$，同调维数为 $258$，相应两种秩为 $28$ 与 $45$。秩下降不等于整个作用消失。

## 44. 同一个有限特征商中分离扭转的准确外阶

**定义。** 保留 $N_p$，对正整数 $m$ 定义

$$L_{p,m}=[N_p,N_p]N_p^m,\qquad Q_{p,m}=\pi_1(\Sigma_g)/L_{p,m}.$$

这是实际有限特征商，并有

$$|Q_{p,m}|=p^{2g}m^{\,2+2(g-1)p^{2g}}.$$

**引理。** 对前述特征覆盖，任意非单位甲板变换 $s\in H_1(\Sigma_g;\mathbb F_p)$ 在 $H_1(Y;\mathbb F_p)$ 上满足

$$\operatorname{rank}(s_*-I)=\frac{2D(g-1)(p-1)}p\ge D.$$

**证明。** $s$ 生成一个自由作用的阶 $p$ 子群。其商曲面亏格为 $k=1+D(g-1)/p$。在商曲面上选适配此循环覆盖的标准基，使其覆盖同态仅把第一生成元映为 $s$，其余生成元映为单位元。存在这种基，因为一个非零模 $p$ 同调余向量可由整数辛变换移到该形式。

令 $R=\mathbb F_p[C_p]$。覆盖的胞腔边界可写为 $\partial_1=(s-1,0,\ldots,0)$，$\partial_2=(0,s-1,0,\ldots,0)^{\mathsf T}$，差一个无关紧要的定向符号。因此其同调 $R$-模为

$$\operatorname{ann}_R(s-1)\oplus R/(s-1)R\oplus R^{2k-2}.$$

前两项各是一维平凡模；在每个正则模上，$s-1$ 的秩为 $p-1$。代入 $k$ 即得公式。所有非单位甲板变换均有阶 $p$，故同一计算适用。

**定理。** 对每条本质分离简单闭曲线 $\alpha$，其 Dehn 扭转在 $\operatorname{Out}(Q_{p,m})$ 中的阶恰好为 $m$。

**证明。** 先取适配曲线的标准基，边界词 $h_\alpha$ 属于 $N_p$。$T_\alpha^m$ 对一侧生成元以 $h_\alpha^m$ 共轭，在 $Q_{p,m}$ 中这已经是单位元，所以其作用逐点为恒等。

反向，若 $T_\alpha^n$ 在 $Q_{p,m}$ 上由 $z$ 实现内共轭，其在 $V_m=N_p/L_{p,m}$ 上的作用必为甲板作用 $\lambda(\bar z)$，其中 $\bar z\in S=H_1(\Sigma_g;\mathbb F_p)$。第 43 节给出同一个 $T_\alpha^n$ 在 $V_m$ 上的准确阶为 $m/\gcd(m,n)$。

若 $p\nmid m$，甲板作用的阶整除 $p$，而该同调作用的阶整除 $m$；相等只能给出恒等，所以 $m\mid n$。若 $p\mid m$，可进一步约化到 $V_p$。非单位甲板作用的秩至少为 $D$，而 $T_\alpha^n-I=n(W_*-I)$ 的秩至多为图循环秩 $(a-1)(b-1)<ab=D$。因此 $\bar z=1$。此时 $z\in V_m$，在交换群 $V_m$ 上的内作用为恒等，再由准确同调阶得到 $m\mid n$。

任意曲线由适配基得到相同结论，且 $L_{p,m}$ 特征，故换标记不影响外阶。$m=1$ 时商为底层同调商，分离扭转为恒等，与公式一致。有限性及阶数表达式来自特征覆盖亏格公式和其无挠一阶整数同调。

## 45. 对指定有限单群因子化的素数筛选

**定义。** 保留第 27–32 节的基商及作用假设，并固定满射 $f:\Lambda\twoheadrightarrow F$ 到非交换有限单群。对一条 $T_\beta\in\Lambda$ 的本质分离曲线，令 $t_\beta=\operatorname{ord}f(T_\beta)$、$d_\beta=\operatorname{ord}q_0(\beta)$。从其实际陪集图计算 $b_\beta$ 及循环格首个 Smith 不变量 $s_{1,\beta}$；$b_\beta=0$ 时单独处理。令 $e_{\beta,\ell}=1$，若 $b_\beta=0$ 或 $\ell\mid s_{1,\beta}$，否则令 $e_{\beta,\ell}=\ell$。

**定理。** 若 $f$ 经 $\Psi_\ell$ 的实际像因子化，则对每条这样的 $\beta$，

$$\boxed{t_\beta\mid d_\beta e_{\beta,\ell}.}$$

若此整除条件对某条 $\beta$ 失败，则 $f(C_\ell)=F$。对任意固定简单曲线 $\alpha_0$ 满足 $f(\operatorname{Stab}(\alpha_0))<F$，该候选 $Q_\ell$ 均不能满足 $C_\ell\alpha_0\subseteq(\ker f)\alpha_0$。

**证明。** 第 42 节给出 $\Psi_\ell(T_\beta)^{d_\beta}$ 的准确阶为 $e_{\beta,\ell}$。因子化保持幂关系，故 $f(T_\beta)^{d_\beta e_{\beta,\ell}}=1$。若失败，则 $T_\beta^{d_\beta e_{\beta,\ell}}\in K_\ell=\ker\Psi_\ell$，但其 $f$ 像非单位。$K_\ell$ 正规及 $F$ 单，强制 $f(K_\ell)=F$。若 $f(C_\ell)=1$，则 $f(K_\ell)$ 是第 28 节的交换 $\ell$ 群 $K_\ell/C_\ell$ 的像，矛盾。单性遂给出 $f(C_\ell)=F$；稳定子像为真子群立即排除所需轨道包含。

**推论。** 写 $r_\beta=t_\beta/\gcd(t_\beta,d_\beta)$。如果 $r_\beta>1$，一个可能成功的素数必须满足 $r_\beta=\ell$，且该素数处的图循环格秩非零。因此：若某个 $r_\beta$ 为合数，或 $r_\beta$ 为素数却使相应秩为零，则在这个固定基商上没有任何素数的首次同调层能够实现 $f$。若两条曲线强制两个不同的素数，同样没有可用素数。第 31 节进一步排除固定基商上任意有限多素数幂提升的联合补救。

**证明。** $t_\beta\mid d_\beta e_{\beta,\ell}$ 等价于 $r_\beta\mid e_{\beta,\ell}$；后者仅为 $1$ 或素数 $\ell$。逐项得到排除结论，再应用固定基商的多素数因子化定理。

**命题。** 满足以上所有单个扭转的整除测试，仍不推出 $f$ 经 $\Psi_\ell$ 因子化。第 44 节的准确外阶也不证明 Klukowski 的一般曲线轨道包含。

**证明。** 整除测试仅检查一族循环子群上的幂关系，没有证明第 32 节要求的联合像交 $\operatorname{im}(f,\Psi_\ell)\cap(F\times\{1\})$ 平凡。特别地，当 $m$ 为 $p$ 的幂时，第 44 节的 $Q_{p,m}$ 本身为有限 $p$ 群；它虽准确检测所有分离扭转的规定幂，却仍受第 17 节针对固定真实曲线和固定有限指数子群的全部幂零商障碍。正向的局部检测与全局因子化是不同结论。

## 46. 单次分离扭转的映射环面与真实切割环面

**定义。** 固定闭、连通、可定向曲面 $\Sigma_g$，$g\ge2$。令 $\alpha$ 为本质分离简单闭曲线，将曲面分成亏格 $h$ 与 $g-h$ 的单边界子曲面，其中 $1\le h<g$。对非零整数 $k$，定义

$$M_{g,h,k}=(\Sigma_g\times[0,1])/((x,1)\sim(T_\alpha^k(x),0)).$$

选择支撑于 $\alpha$ 的环形邻域内的扭转代表，以及邻域外的固定基点。这确定纤维基本群 $\pi=\pi_1(\Sigma_g)$ 与时间生成元 $t$，从而有表示

$$\Pi_{g,h,k}=\pi_1(M_{g,h,k})\cong\pi\rtimes_{T_{\alpha,*}^k}\mathbb Z.$$

以下指定有限覆盖时保留这一纤维及时间标记。改变标记不能在没有证明的情况下被视为保持同一个覆盖。

**命题。** $M_{g,h,k}$ 是闭可定向三维流形。沿 $\alpha$ 的悬挂环面切开后，两个块分别为

$$\Sigma_{h,1}\times S^1,\qquad \Sigma_{g-h,1}\times S^1.$$

切割环面的基本群 $\mathbb Z^2$ 注入整个流形的基本群。两侧 Seifert 圆纤维在共同环面上的无向交数恰为 $|k|$。当 $k\ne0$ 时，这个环面是两块之间的 JSJ 环面。

**证明。** 扭转在曲线两侧离开环形邻域后为恒等。将环形邻域在映射环面中分配给两边，可把每边平凡化为相应单边界曲面与圆的乘积。穿过环形邻域时，时间方向一周累计 $k$ 次边界方向的平移。选择边界方向与圆纤维方向的符号后，按“圆纤维、曲面边界”的顺序记录基，粘合矩阵可写为

$$G_k=\begin{pmatrix}1&0\\k&-1\end{pmatrix}.$$

其行列式为 $-1$，两侧圆纤维的斜率交数为 $|k|$。不同方向约定会改变符号或矩阵的坐标表达，不改变这个绝对交数。单边界曲面的边界元在其自由基本群中无限阶，因此边界环面群向每个乘积块群的映射单射。并合积的正规形定理继而给出向整个群的单射。

每个块的底曲面欧拉示性数为负，且其乘积 Seifert 纤维由基本群的无限循环中心确定。底曲面上的内部切割仍处于同一个 Seifert 块。两侧边界上的纤维斜率不平行，故不能跨该环面延续为一个 Seifert 纤维结构。利用不可压缩环面分解的唯一性，得到显示的两个 JSJ 块。

**命题。** 在这个指定的单扭转族中，无定向同胚类型由

$$\bigl(g,\{h,g-h\},|k|\bigr)$$

准确决定。

**证明。** 同胚保持 JSJ 分解及各块的 Seifert 纤维，允许交换两块和反转纤维方向。各块群除以其中心后分别为秩 $2h$ 与 $2(g-h)$ 的自由群，故无序亏格对保持；纤维斜率的绝对交数 $|k|$ 也保持。反之，同一无序亏格对的分离曲线由曲面同胚相互对应，相同扭转次数的映射环面由此同胚。时间方向反转给出 $M_{T^k}\cong M_{T^{-k}}$，完成无定向情形。这里没有将这个结论提升为任意三维流形或任意多扭转的分类。

**命题。** 这些流形不是 $S^3$。其中的切割环面也不可能作为不可压缩环面存在于 $S^3$。

**证明。** 映射环面的投影到 $S^1$ 诱导基本群到 $\mathbb Z$ 的满射，所以其基本群非平凡。$S^3$ 单连通，既不具有这一满射，也不能容纳向其基本群单射的 $\mathbb Z^2$。本族因此处于几何化的带本质环面部分，并不满足三维庞加莱定理的单连通前提。

## 47. 所有纯时间循环覆盖的一阶同调盲区

**定义。** 对正整数 $n$，令 $M_{g,h,k}^{(n)}$ 为纤维化 $M_{g,h,k}\to S^1$ 沿 $S^1\xrightarrow{z\mapsto z^n}S^1$ 拉回的覆盖。它同胚于 $M_{g,h,nk}$。

**定理。** 对所有 $n\ge1$、$k\ne0$、$1\le h<g$，

$$\boxed{H_1(M_{g,h,k}^{(n)};\mathbb Z)\cong\mathbb Z^{2g+1}.}$$

相应的同调 monodromy 始终为恒等，特征多项式始终为 $(x-1)^{2g}$。

**证明。** 分离曲线的同调类为零，Dehn 扭转的同调转移公式给出 $T_{\alpha,*}=I$。映射环面的 Wang 正合列在一次同调处给出

$$0\longrightarrow\operatorname{coker}(T_{\alpha,*}^{nk}-I)
\longrightarrow H_1(M_{g,h,nk};\mathbb Z)
\longrightarrow\mathbb Z\longrightarrow0.$$

右端自由，扩张分裂；左端为 $\mathbb Z^{2g}$，故得结论。

**推论。** 固定 $g,h$，全部时间循环覆盖的一阶整数同调群序列，不能区分无穷多个两两不同胚的 $M_{g,h,k}$。

**证明。** 取全部正整数 $k$。第 46 节的 JSJ 斜率交数区分它们，而本节给出完全相同的群序列。这里所比较的是各层抽象一阶同调群及其纤维同调 monodromy，没有声称所有带任意附加结构的覆盖不变量均相同。

## 48. 一个指定横向覆盖的完整整数同调

**定义。** 固定素数 $p$，令

$$N_p=\ker(\pi\to H_1(\Sigma_g;\mathbb F_p)),\qquad D=p^{2g},\qquad G=1+D(g-1).$$

因为 $T_\alpha$ 在模 $p$ 同调上为恒等，赋值 $\pi\to\pi/N_p$、$t\mapsto0$ 定义满射 $\Pi_{g,h,k}\to(\mathbb Z/p)^{2g}$。令 $\widetilde M_{g,h,k,p}$ 为其核对应的 $D$ 重覆盖。它是亏格 $G$ 的曲面覆盖上、固定所选基点提升的 monodromy 的映射环面。

按大小排列

$$a=p^{2\min(h,g-h)},\qquad b=p^{2\max(h,g-h)},\qquad
\beta=(a-1)(b-1),\quad c=(a-2)(b-2),\quad R=2G+1-\beta.$$

有 $ab=D$、$a\mid b$、$a,b\ge4$。记 $q=|k|$。

**引理。** 沿 $\alpha$ 的全部提升切开该曲面覆盖，对偶图为 $K_{a,b}$。在矩形基本循环基下，循环配对矩阵为

$$Q=(I_{a-1}+J_{a-1})\otimes(I_{b-1}+J_{b-1}),$$

其中 $J_j$ 为 $j\times j$ 全一矩阵。

**证明。** 将底曲面模 $p$ 同调分成两侧直和 $A\oplus B$，阶分别为 $p^{2h}$ 与 $p^{2(g-h)}$。曲线 $\alpha$ 映为零，所以提升边由全部 $A\oplus B$ 元素标记，顶点分别由两类陪集标记。每对异侧顶点之间恰有一条边，得到完全二部图。用一固定顶点连接对侧全部顶点，再由一个固定对侧顶点连接余下顶点，组成生成树。每条非树边给出一个四边形基本循环。两个矩形循环的内积是相应两个坐标的 $(\delta_{ii'}+1)(\delta_{jj'}+1)$，即显示的 Kronecker 配对。

**引理。** $I_{a-1}+J_{a-1}$ 与 $\operatorname{diag}(1,\ldots,1,a)$ 在整数左右可逆基变换下等价；前者有 $a-2$ 个单位 Smith 因子。因此 $Q$ 的 Smith 对角为

$$1^{[c]},\qquad a^{[b-2]},\qquad b^{[a-2]},\qquad ab,$$

上标方括号表示重数。

**证明。** 以 $x_1,\ldots,x_{a-1}$ 表示该矩阵的余核生成元，关系为 $x_i+\sum_jx_j=0$。相减得到所有 $x_i$ 相等，剩余关系为 $a x_1=0$。映射 $x_i\mapsto1\pmod a$ 证明没有额外关系。矩阵非奇异且余核为循环群 $\mathbb Z/a$，故 Smith 形式如述。对两个因子各作整数可逆左右变换，取 Kronecker 积仍为整数可逆变换，得到其对角因子的全部两两乘积。因为 $a\mid b$，排列后已经构成整除链。

**定理。** 对全部上述参数，实际覆盖映射环面满足

$$\boxed{
H_1(\widetilde M_{g,h,k,p};\mathbb Z)
\cong\mathbb Z^R
\oplus(\mathbb Z/q)^c
\oplus(\mathbb Z/(qa))^{b-2}
\oplus(\mathbb Z/(qb))^{a-2}
\oplus\mathbb Z/(qab).
}$$

约定 $\mathbb Z/1$ 是平凡群。因此其挠子群的指数和阶分别为

$$\boxed{\exp\operatorname{Tor}H_1=qD,\qquad
|\operatorname{Tor}H_1|=q^\beta a^{b-1}b^{a-1}.}$$

**证明。** 单次 $T_\alpha$ 的所选提升是全部提升曲线上的一次正多扭转 $W$。在覆盖曲面的整数同调中，第 40 节证明 $W_*-I$ 的唯一非零块为 $Q$，并且 $(W_*-I)^2=0$。因此对每个正负整数 $k$，$W_*^k-I=k(W_*-I)$。其非零 Smith 因子恰为上一引理各因子乘以 $q$，其余 $2G-\beta$ 个同调方向自由。Wang 正合列再加一个自由时间方向，即得完整群分解。最后一个因子是前面全部因子的倍数，给出指数；全部因子相乘给出阶。

**命题。** 这里 $N_p$ 是纤维群的特征子群，指定的三维覆盖核在 $\Pi_{g,h,k}$ 中正规；没有仅由此推出它在整个三维群中为特征子群。

**证明。** $T_\alpha$ 保持 $N_p$，因此所写到甲板群的满射存在，核正规。覆盖的定义还使用了时间元的像为零；在改变时间元或纤维化后，需要另外比较得到的核。特征性不能从纤维群的性质直接转移到整个半直积。

## 49. 由同调秩和挠指数恢复三维粘合参数

**定理。** 给定原流形的 $H_1$、覆盖素数 $p$ 和指定覆盖的 $H_1$，可以在第 46 节的单扭转族中恢复无定向同胚类型。实际上只需要原同调秩、覆盖同调秩和覆盖挠子群指数这三个整数。

**证明。** 原同调秩为 $2g+1$，先得到 $g$，再得到 $D=p^{2g}$ 和 $G=1+D(g-1)$。若覆盖同调秩为 $R$、其挠指数为 $E$，第 48 节给出

$$\boxed{|k|=E/D,\qquad \beta=2G+1-R,\qquad a+b=D+1-\beta.}$$

$ab=D$，故 $a,b$ 是多项式

$$X^2-(D+1-\beta)X+D$$

的两个正整数根。它们为 $p$ 的偶数次幂，因此准确恢复无序对 $\{h,g-h\}$。平方判别式和整数幂检验完成解码，无需浮点对数。第 46 节将这些参数识别为本族的无定向同胚类型。

**实例。** 对 $g=2$、$p=2$，有 $D=16$、$G=17$、$a=b=4$。对于任意非零 $k$，$q=|k|$，

$$H_1(\widetilde M;\mathbb Z)
\cong\mathbb Z^{26}\oplus(\mathbb Z/q)^4
\oplus(\mathbb Z/(4q))^4\oplus\mathbb Z/(16q).$$

原流形的全部时间循环覆盖一律具有 $\mathbb Z^5$ 的一阶同调，而这个十六重横向覆盖的挠指数为 $16|k|$。

**命题。** 该恢复不区分 $k$ 与 $-k$，且不构成对任意输入三维流形的识别算法。

**证明。** 群分解只含 $|k|$，与时间反转给出的无定向同胚一致。解码定理以流形属于所述族、且覆盖为所指定覆盖为前提；一般同调数据满足某些整数等式不能替代这两个几何前提。$k=0$ 时流形是 $\Sigma_g\times S^1$，覆盖同调为 $\mathbb Z^{2G+1}$，切割亏格 $h$ 不再是此流形的参数，故另列而不代入非零公式。

## 50. 有界扭转次数只需一次有限系数观察

**定义。** 固定 $g\ge2$、素数 $p$ 和整数 $H\ge1$。选素数 $q_0>\max(H,p)$，令

$$L=q_0 p^{2g}H!.$$

考虑满足 $1\le|k|\le H$ 的第 46 节流形。仍取第 48 节的指定横向覆盖。

**定理。** 单个有限交换群

$$\boxed{H_1(\widetilde M_{g,h,k,p};\mathbb Z/L)}$$

在此有界族中确定 $\{h,g-h\}$ 和 $|k|$。它可以由原三维群的一个实际有限商及其指定甲板投影读取。

**证明。** 因 $|k|\mid H!$，第 48 节每个挠因子均整除 $p^{2g}H!$，并与 $q_0$ 互素。普遍系数定理在一次同调给出

$$H_1(\widetilde M;\mathbb Z/L)\cong(\mathbb Z/L)^R\oplus T,$$

其中 $T$ 恰为原整数同调的挠子群。其 $q_0$ 初等部分的维数为 $R$。由于 $T$ 的每个不变量因子均严格小于 $L$ 且整除 $L$，整个有限群的 Smith 分解末尾恰有 $R$ 个 $L$，剥去这 $R$ 项就恢复 $T$。于是恢复 $R,E$，应用第 49 节。

具体地，记 $K\triangleleft\Pi_{g,h,k}$ 为横向覆盖核，令 $J=[K,K]K^L$。$J$ 在 $K$ 中特征，故在 $\Pi_{g,h,k}$ 中正规，得到有限扩张

$$1\longrightarrow H_1(\widetilde M;\mathbb Z/L)
\longrightarrow\Pi_{g,h,k}/J
\longrightarrow(\mathbb Z/p)^{2g}\longrightarrow1.$$

将商连同最后的指定投影保留，就能读出所需的有限交换核。其大小满足显式上界

$$\boxed{|\Pi_{g,h,k}/J|\le p^{2g}L^{\,3+2p^{2g}(g-1)}.}$$

这是因为整数覆盖同调的自由秩加上列出的挠因子个数为 $2G+1=3+2p^{2g}(g-1)$，每项模 $L$ 的大小至多为 $L$。

**命题。** 该上界是一个存在且可计算的有限观察预算，不给出最小商、最佳覆盖次数或多项式时间复杂度，也不把这个三维商当成曲面群的主合同商。

**证明。** 构造使用 $H!$，其目的仅在于同时容纳全部允许的挠阶。正规子群 $J$ 属于整个三维群，而 Klukowski 轨道条件使用的是纤维曲面群的有限特征商及映射类群的诱导外作用，二者的群、核和作用数据不同。

## 51. 局部粘合恢复与全局轨道控制的接口边界

**命题。** 在保留曲面纤维和其映射类标记的条件下，分离曲线扭转的共轭与所构造三维粘合相容：若 $\gamma\in\operatorname{Mod}^{+}(\Sigma_g)$，则

$$\gamma T_\alpha^k\gamma^{-1}=T_{\gamma(\alpha)}^k,$$

且由 $\gamma\times\operatorname{id}$ 诱导对应映射环面之间的纤维保持同胚。这个事实本身不提供任意有限指数子群的曲线轨道控制。

**证明。** 扭转支撑环形邻域在定向保持同胚下变为像曲线的环形邻域，正向和次数保持，所以得到第一式；该式保证乘积映射在端点粘合后良定义。对有限指数 $\Gamma$ 与曲线稳定子 $H_\alpha$，所需结论仍为存在曲面特征商的主合同核 $C$ 满足 $C\subseteq\Gamma H_\alpha$。本节构造只确定一类已指定映射环面的切割亏格及单个整数斜率，不约束 $C$ 中所有元素的曲线轨道，故不能代替该包含。

**命题。** 把一条曲线的幂参数恢复定理逐条应用到若干曲线，并不能在没有附加证明的情况下推出其扭转乘积或稳定子陪集的识别。

**证明。** 一般曲线之间可以相交，此时扭转未必交换；同调像中各单独元素的阶既不确定混合关系，也不确定它们在源群所给关系下生成的配对子群。特别地，给定 $f:\Lambda\to F$ 和候选外作用 $a_q$，目标因子化仍取决于同源联合像 $\operatorname{im}(f,a_q)$ 的核，而非逐元素的阶数列表。因此，对多条粘合曲线的推广需要保留曲线的相交与稳定子作用，以及各环面粘合在同一个整体基本群中的关系。

## 52. 因果档案、周期相位与共同几何标记

**命题。** 设事件集 E 带严格因果关系及整数时间 t，且 e≺f 蕴含 t(e)<t(f)。若观察 q 合并某对可比较事件，即 e≺f 且 q(e)=q(f)，则在 q(E) 上不存在同时满足反自反性和因果保持性的关系 R，其中因果保持性指 e≺f 蕴含 R(q(e),q(f))。

**证明。** 所述事件对将给出 R(q(e),q(e))，与反自反性矛盾。故周期相位可以作为读数，却不能在合并这类事件后原样保留严格因果关系。整数时间模 M 的读数若把相差 M 的可比较事件合并，就有此障碍。保留整数提升或绕行次数可以避免这项特定合并，但并不单独确定空间度量或传播速度。

**定义。** 一个几何探测任务的数据包括同一个曲面的同调格、交叉形式、未知作用和全部允许探针。更换辛基时，这些对象必须同时输运。若只保存未知作用的单独共轭类，而给探针任意独立选代表，则通常没有保留原任务的共同标记。

**命题。** 设 A,P_1,...,P_j 为同一有限自由模上的可逆作用。对任意可逆 C，

$$\operatorname{tr}((CP_1C^{-1})\cdots(CP_jC^{-1})(CAC^{-1}))
=\operatorname{tr}(P_1\cdots P_jA).$$

因此混合迹是共同配置的坐标不变量；这不使它成为 A 的单独共轭类的函数。

**证明。** 连乘中的相邻 C^{-1}C 消去，剩下整体共轭，迹保持不变。后一差别由下文的实际混合迹公式给出：相对交叉位置进入读数，不能独立删除。

## 53. 平方零辛形变的被动谱盲区

**定义。** 设 R 为交换环，G≥r≥1。令 H=R^{2G}，取基 a_1,...,a_G,b_1,...,b_G，交叉形式满足 ⟨b_i,a_j⟩=δ_ij、⟨a_i,b_j⟩=-δ_ij，其余基配对为零。对对称矩阵 Q∈M_r(R)，定义 U_Q(a_i)=0，并令

$$U_Q(b_j)=\sum_{i=1}^{r}Q_{ij}a_i\quad(j\le r),\qquad
U_Q(b_j)=0\quad(j>r),\qquad A_Q=I+U_Q.$$

**命题。** A_Q 保持交叉形式，U_Q²=0，且对每个整数 n，

$$A_Q^n=I+nU_Q,\qquad
\operatorname{tr}(A_Q^n)=2G,\qquad
\det(xI-A_Q^n)=(x-1)^{2G}.$$

这里整数经标准映射进入 R。

**证明。** 交叉形式保持性在基向量上化为 Q_{ij}=Q_{ji}。U_Q 的像包含于其核中的 a-子模，所以平方为零；正负幂公式分别由乘法和逆矩阵 I-U_Q 得到。该基中的 A_Q^n 为对角线全一的上三角矩阵，故迹和特征多项式如式。

**推论。** 即使给出全部整数时刻的这些谱读数，也不能区分任意两个 Q。对于整数曲面上的正多扭转，第 40 节所给的适配辛基使它属于此类，因而此盲区适用于真实多扭转的被动同调谱。结论仅涉及这些谱读数，不断言全部周期点、全部余核或全部覆盖不变量都相同。

**证明。** 读数与 Q 无关。真实曲面的应用消费第 40 节的几何到同调块的识别，不能仅凭一个同形矩阵声称构造了曲面。

## 54. 一次探针的二次读数与特征二障碍

**定义。** 对 z∈H，令 φ_z(x)=⟨x,z⟩，定义辛转移 P_z=I+zφ_z。因 ⟨z,z⟩=0，它的逆为 I-zφ_z。每次实验都从同一个未知 A_Q 重新开始；探针向量和施加顺序事先指定。观测仅为最终矩阵的迹。记 ν(z)∈R^r 为 z 的前 r 个 b-坐标，并定义基线扣除读数

$$D_z(Q)=\operatorname{tr}(P_zA_Q)-\operatorname{tr}(P_z).$$

**定理。** 对任意交换环 R 和任意 z，有

$$\boxed{D_z(Q)=-\nu(z)^{\mathsf T}Q\nu(z).}$$

**证明。** 展开 P_zA_Q。U_Q 的迹为零，而秩一算子 zφ_zU_Q 的迹为 φ_z(U_Qz)=⟨U_Qz,z⟩。按约定交叉符号，它等于显示的负二次型。

**定理。** 若 R 是特征为二的域，两个对称矩阵的全部单探针读数相同，当且仅当其对角项逐项相同。若 r≥2，则一次探针不能恢复一般 Q。若 2 在 R 中可逆，则用 z=b_i 和 z=b_i+b_j 即可恢复 Q。

**证明。** 特征二下，对称矩阵的非对角贡献成对相消，故 νᵀQν=Σ_i Q_{ii}ν_i²。反向取 z=b_i 得到各对角项。r≥2 时，只有 Q_{12}=Q_{21}=1 非零的矩阵与零矩阵具有相同的全部一次读数。2 可逆时，由

$$D_{b_i+b_j}-D_{b_i}-D_{b_j}=-2Q_{ij}$$

恢复非对角项。该除法不能无条件输运到偶数模数。

## 55. 两次固定探针在任意交换环上的准确恢复

**定义。** 对 i<j≤r，取 z_i=b_i、w_{ij}=b_j+a_i，定义

$$D_i=\operatorname{tr}(P_{b_i}A_Q)-\operatorname{tr}(P_{b_i}),$$

$$D_{ij}=\operatorname{tr}(P_{b_i}P_{b_j+a_i}A_Q)
-\operatorname{tr}(P_{b_i}P_{b_j+a_i}).$$

右端先作用 A_Q，再按矩阵乘法顺序施加两个固定探针。不同读数属于从同一未知作用重置的独立实验，不把多条实验分支当成一条未重置轨迹。

**定理。** 无需除以任何整数，对每个交换环 R 均有

$$\boxed{D_i=-Q_{ii},\qquad D_{ij}=-Q_{ii}-Q_{jj}+Q_{ij},}$$

$$\boxed{Q_{ii}=-D_i,\qquad Q_{ij}=D_{ij}-D_i-D_j\quad(i<j).}$$

**证明。** 展开两个秩一更新：

$$P_zP_w=I+z\phi_z+w\phi_w+z\langle w,z\rangle\phi_w.$$

乘 U_Q 后取迹，得到

$$-\nu(z)^TQ\nu(z)-\nu(w)^TQ\nu(w)
+\langle w,z\rangle\langle U_Qz,w\rangle.$$

在指定 z=b_i、w=b_j+a_i 下，后面两个配对分别为 -1 和 -Q_{ji}，而 ν(z)、ν(w) 分别为第 i、j 个标准向量。代入并用对称性即得。恢复式只是相加减，所以对整数、任意有限域及复合模数同时成立。

**推论。** 在特征二、r≥2 的对称块任务中，允许任意辛转移探针时，准确恢复所需的最小最大探针深度恰为二：深度一只确定对角，深度二确定全部矩阵。这里深度是每次实验中的探针个数，不是实验总次数。

**证明。** 下界来自第 54 节的完整单探针等价类，上界来自本节有限探针族。

**命题。** 在整数曲面的适配辛基下，本节探针可由真实简单闭曲线的 Dehn 扭转实现。它们是覆盖曲面上的探针，不一定从底曲面映射类提升而来。

**证明。** b_i 和 b_j+a_i 都是本原整数同调向量；可用标准曲线和带和实现，也可先扩张为整数辛基，再用曲面辛表示的满射性实现。单次 Dehn 扭转的同调公式正是 P_z。此论证固定同一覆盖及同一标记，没有证明这些探针与甲板作用相容或可下降到底曲面。

## 56. 观察类数、实验数量与带噪声整数恢复

**定理。** 设 R=F_q。全部 r×r 对称矩阵有 q^{r(r+1)/2} 个。在特征二、r≥2 时，无探针的被动谱把它们合为一类，全部一次探针给出 q^r 类，全部两次探针给出 q^{r(r+1)/2} 个单点类。任意用固定个数的 F_q 值读数准确恢复矩阵的协议，至少需要 r(r+1)/2 个读数；第 55 节达到这个数量。

**证明。** 独立矩阵元的数目为 r(r+1)/2。三种类数分别由第 53、54、55 节得到。s 个 F_q 读数最多具有 q^s 个可能序列；恢复要求不同矩阵给不同序列，故 s≥r(r+1)/2。本节探针族恰有 r 个对角读数及 r(r-1)/2 个非对角读数。即使固定长度协议按已有读数自适应选探针，其叶子数上界仍是 q^s；未给停止时间或连续精度带来免费信息。

**推论。** 任何保存此完整恢复任务答案的固定宽度二进制标签，至少需要 ⌈(r(r+1)/2)log₂q⌉ 位。这个信息下界不计算构造探针、计算迹、切换基、重置或验证结果的时间费用。

**证明。** 标签必须区分全部矩阵，按标签总数计数。

**命题。** 在实数任务中，若每个已扣除基线的读数误差绝对值至多为 ε，按第 55 节解码后，对角误差至多 ε，非对角误差至多 3ε。若真矩阵为整数矩阵且 ε<1/6，逐项最近整数舍入准确恢复 Q。

**证明。** 恢复公式中对角只使用一个带符号读数，非对角使用三个，三角不等式给误差界。严格小于 1/2 的误差保证最近整数唯一。这里误差界直接加在已扣除基线的迹上；若基线也有误差，必须另行并入，不能把形式迹计算自动解释成物理测量。

## 57. 十六重曲面覆盖上的符号恢复

**定义。** 取第 48 节 g=2、p=2、h=1 的实际曲面覆盖，覆盖亏格为 G=17。单次分离扭转的提升在适配辛基上具有 r=9 的对称块

$$Q_0=(I_3+J_3)\otimes(I_3+J_3).$$

对整数 k，未知同调作用为 A_k=I+kU_{Q_0}。用矩形循环标记，取 i=(1,1)、j=(2,2)，则 (Q_0)_{ii}=(Q_0)_{jj}=4、(Q_0)_{ij}=1。

**定理。** 对全部整数 k，第 55 节的三个基线扣除读数分别为

$$D_i=-4k,\qquad D_j=-4k,\qquad D_{ij}=-7k,$$

所以

$$\boxed{k=D_{ij}-D_i-D_j.}$$

该等式在任意模数 m 上也准确恢复 k mod m。原始迹分别为 34-4k、34-4k、33-7k。

**证明。** 代入已经由实际覆盖识别的 Q=kQ_0。单探针的迹基线是 2G=34；两探针基线为 2G-⟨b_i,b_j+a_i⟩²=33。矩阵元与其余坐标无关，得到显示数值。

**推论。** 在模二同调上，A_1 非平凡，但每一个单探针迹都与 A_0 相同；指定的双探针可将二者区分。保留整数读数时，可以相对于固定方向和探针区分 k 与 -k；这不成为无标记、无定向三维流形的不变量。

**证明。** Q_0 的对角项均为四，模二为零；其指定非对角项为一，所以块非零。第 54–55 节给出全部单探针失效和双探针成功。符号恢复使用同一个带方向辛标记；第 49 节的无定向映射环面同调只恢复 |k|，两项结论的任务不同。

## 58. 完成探针语言之后仍须满足的外作用条件

**定理。** 设 a:Λ→A 为一个固定的有限观察同态，P_1,...,P_s 是在 A 的同一指定表示中预先固定的探针。凡只从 a(x)、这些固定探针及其有限乘积、迹或其他确定后处理得到的联合读数 O(x)，均满足 ker(a)⊆ker(O)，其中 ker(O) 指等读数关系。若同一个满射 f:Λ→F 满足

$$\operatorname{im}(f,a)=F\times a(\Lambda),$$

则还满足

$$\operatorname{im}(f,O)=F\times O(\Lambda).$$

**证明。** 全部操作都从同一 a(x) 开始，相等输入逐步给相等读数。对任意 O(x_0) 和任意 y∈F，直积假设给出 x 使 a(x)=a(x_0)、f(x)=y，因此 O(x)=O(x_0)。

**命题。** 第 55 节修复的是从有标记同调矩阵到被动谱读数所造成的信息丢失。它不证明任意曲面映射类由该同调矩阵确定，也不自动构造 Klukowski 轨道条件所需的有限特征商。

**证明。** 已构造的探针使 Q 到迹画像的映射单射，所以其在这个矩阵族上的核被恢复。源映射类到该矩阵的核没有因此改变。若探针只在覆盖曲面上存在、未下降到底曲面，则它也不是原底曲面作用中已经允许的操作。若在外自同构商中存在提升或共同共轭歧义，还须证明整组配置的读数在该商上良定义；独立选择代表不提供此证明。对有限指数 Γ 及真实曲线 α，最终仍须找到实际特征商的主核 C 满足 C⊆ΓStab(α)，或在先前单群情形通过同源联合像检验。被动谱的两步恢复没有替代这一包含。
## 59. 四个实例的命题化

**命题 59.1。** 本命题给出 §34 中以「实例」陈述的断言的命题形式与证明；该断言以本命题为准。设 $\ell$ 为奇素数，§33 的通用模二同调覆盖取 $g=3$，$V=H_1(N_2;\mathbb F_\ell)$，并取将底曲面分成亏格 $h=1$ 与 $g-h=2$ 两侧的本质分离曲线。则覆盖度为 $64$，覆盖亏格为 $129$，$V$ 的维数为 $258$；$V$ 分成一个六维平凡块和六十三个四维非平凡块；分离扭转在四十五个非平凡块上非平凡，标准提升的增量秩为 $45$。

**证明。** §33 的甲板群为 $(\mathbb Z/2)^{2g}$，故覆盖度为
$$|S|=2^{2g}=2^6=64.$$
无分歧覆盖的 Riemann--Hurwitz 公式给出覆盖亏格
$$\widetilde g=1+|S|(g-1)=1+64\cdot2=129.$$
§33 的分块公式给出
$$\dim V=2+(2g-2)4^g=2+4\cdot4^3=2+4\cdot64=258.$$
平凡字符的分块维数为 $2g=6$；字符总数为 $4^g=4^3=64$，所以非平凡字符有 $64-1=63$ 个，每个分块维数为 $2g-2=4$。§34 的活跃字符正是在两侧均非平凡的字符，数目为
$$\bigl(4^h-1\bigr)\bigl(4^{g-h}-1\bigr)=(4^1-1)(4^2-1)=3\cdot15=45.$$
每个活跃块上的标准提升增量秩为一，平凡块及其余非平凡块的增量为零，故总增量秩为 $45\cdot1=45$。证毕。

**命题 59.2。** 本命题给出 §42 中以「例」陈述的断言的命题形式与证明；该断言以本命题为准。令 $q_0:\pi_1(\Sigma_2)\twoheadrightarrow C_2=\{1,s\}$ 满足
$$q_0(a_1)=q_0(a_2)=s,\qquad q_0(b_1)=q_0(b_2)=1,$$
并令 $\alpha$ 为分隔两个把手的曲线。则两侧子曲面群均映满 $C_2$，$q_0(\alpha)=1$，对偶多重图是两个顶点之间的两条重边，$Q_{\mathcal D}=(2)$；两个提升曲线的同调类均非零，而它们的一次正多扭转在模 $2$ 同调上为恒等。该覆盖为正则覆盖；本命题不声称其核对整个映射类群特征。

**证明。** $C_2$ 为交换群，故每个交换子映为单位元，曲面关系保持，且 $q_0$ 满射。第一侧的像含 $q_0(a_1)=s$，第二侧的像含 $q_0(a_2)=s$，所以两侧像均为 $C_2$。分离曲线是第一把手交换子的边界，故 $q_0(\alpha)=q_0([a_1,b_1])=1$。在 §42 的记号中
$$|S|=2,\quad |A_0|=|B_0|=2,\quad |C_0|=1,\quad d=1.$$
因此顶点数为 $|S/A_0|+|S/B_0|=1+1=2$，边数为 $|S/C_0|=2$，图循环秩为 $2-2+1=1$。将两条边同向定向，取沿第一条边正向、第二条边反向的基本循环，循环矩阵为 $Z=(1,-1)^{\mathsf T}$，从而 §40 的配对矩阵为
$$Q_{\mathcal D}=Z^{\mathsf T}Z=(1)^2+(-1)^2=(2).$$
两条边在该基本循环中的系数分别为 $1$ 与 $-1$，故 §40 将两个曲线类写成同一本原非零类的正负，其整数及模 $2$ 同调类均非零。由 §42 的 $d=1$，两条提升曲线上的一次正扭转之积正是所指定的提升。§40 给出的同调增量在唯一循环块上就是 $(2)$，其模 $2$ 约化为零，所以一次正多扭转满足 $W_*=I$ 于 $H_1(Y;\mathbb F_2)$。$\ker q_0$ 在 $\pi_1(\Sigma_2)$ 中正规，故覆盖正则；这些计算没有给出它在整个映射类群下的特征性。证毕。

**命题 59.3。** 本命题给出 §43 中以「例」陈述的断言的命题形式与证明；该断言以本命题为准。对典范特征同调覆盖及分离曲线，分别有：当 $(g,p,h)=(2,2,1)$ 时，覆盖度为 $16$，同调维数为 $34$，对偶图循环秩为 $9$，扭转的模 $2$ 秩为 $4$，而对每个素数 $\ell\ne2$ 的秩为 $9$；当 $(g,p,h)=(3,2,1)$ 时，覆盖度为 $64$，同调维数为 $258$，模 $2$ 秩为 $28$，而对每个素数 $\ell\ne2$ 的秩为 $45$。这些秩均为正，故秩下降不等于整个作用消失。

**证明。** §43 给出
$$D=p^{2g},\qquad \widetilde g=1+D(g-1),\qquad \dim_{\mathbb F_\ell}H_1(Y;\mathbb F_\ell)=2\widetilde g,$$
并令 $a=p^{2h}$、$b=p^{2(g-h)}$。当 $(g,p,h)=(2,2,1)$ 时，
$$D=2^4=16,\quad \widetilde g=1+16(2-1)=17,\quad \dim_{\mathbb F_\ell}H_1(Y;\mathbb F_\ell)=2\cdot17=34,$$
$$a=b=2^2=4,\quad \operatorname{rank}_{\mathbb Z}H_1(\mathcal D;\mathbb Z)= (a-1)(b-1)=3\cdot3=9.$$
§43 的秩公式给出
$$\operatorname{rank}_{\mathbb F_2}(W_*-I)=(a-2)(b-2)=2\cdot2=4,$$
而对 $\ell\ne2$ 有
$$\operatorname{rank}_{\mathbb F_\ell}(W_*-I)=(a-1)(b-1)=9.$$
当 $(g,p,h)=(3,2,1)$ 时，
$$D=2^6=64,\quad \widetilde g=1+64(3-1)=129,\quad \dim_{\mathbb F_\ell}H_1(Y;\mathbb F_\ell)=2\cdot129=258,$$
$$a=2^2=4,\quad b=2^4=16,\quad \operatorname{rank}_{\mathbb Z}H_1(\mathcal D;\mathbb Z)=3\cdot15=45,$$
$$\operatorname{rank}_{\mathbb F_2}(W_*-I)=(4-2)(16-2)=2\cdot14=28,$$
$$\operatorname{rank}_{\mathbb F_\ell}(W_*-I)=(4-1)(16-1)=3\cdot15=45\quad(\ell\ne2).$$
上述模 $2$ 秩分别为 $4$ 与 $28$，均不为零，故相应作用没有消失。证毕。

**命题 59.4。** 本命题给出 §49 中以「实例」陈述的断言的命题形式与证明；该断言以本命题为准。对 §48 中 $g=2$、$p=2$ 的指定横向覆盖，令 $k\in\mathbb Z\setminus\{0\}$、$q=|k|$。则 $D=16$、$G=17$、$a=b=4$，并且
$$H_1(\widetilde M;\mathbb Z)\cong\mathbb Z^{26}\oplus(\mathbb Z/q)^4\oplus(\mathbb Z/(4q))^4\oplus\mathbb Z/(16q).$$
原流形的全部时间循环覆盖的一阶同调均为 $\mathbb Z^5$，而这个十六重横向覆盖的挠子群指数为 $16|k|$。

**证明。** $1\le h<g=2$ 强制 $h=1$，故 §48 的参数在这里为
$$D=2^{2g}=2^4=16,\qquad G=1+D(g-1)=1+16=17,$$
$$a=2^{2\min(1,1)}=4,\qquad b=2^{2\max(1,1)}=4,$$
$$\beta=(a-1)(b-1)=3\cdot3=9,\qquad c=(a-2)(b-2)=2\cdot2=4,$$
$$R=2G+1-\beta=2\cdot17+1-9=26.$$
将 §48 的同调分解逐项代入 $q=|k|$ 得
$$\mathbb Z^R=\mathbb Z^{26},\quad (\mathbb Z/q)^c=(\mathbb Z/q)^4,$$
$$ (\mathbb Z/(qa))^{b-2}=(\mathbb Z/(4q))^2,\quad (\mathbb Z/(qb))^{a-2}=(\mathbb Z/(4q))^2,$$
$$\mathbb Z/(qab)=\mathbb Z/(16q),$$
合并两个 $4q$ 项即得所示群分解。§48 的挠指数公式给出
$$\exp\operatorname{Tor}H_1=qD=q\cdot16=16|k|.$$
另一方面，§47 对 $g=2$ 的任意时间循环覆盖给出 $\mathbb Z^{2g+1}=\mathbb Z^5$。证毕。
