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
