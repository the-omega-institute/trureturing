# AURIC：中央响应平方与径向一致续卷

**约定（卷名、编号与记号）。** 本续卷沿用[前卷《中央响应平方与径向一致》](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)的记号。未另标来源的0–122节及其声明、公式编号均指前卷；123–129节及其声明、公式编号均指本续卷。

“静态卷”指[《任意维静态量子重构》](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)，“谱混合卷”指[《谱混合响应与直接窗口的边界》](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md)，“OmegaQ024”指[《ΩQ-024：正向增益、内生标尺与共同锚》](OMEGAQ_024_POSITIVE_GAIN_INTRINSIC_SCALE_AND_COMMON_ANCHOR.md)。

## 123. 同一原三轴与两个互补输出问题

**定义 123.1（完整前件、原输入与有限投影）。** 保持100.1与106.1的同一原候选：原 $(E,C,u,N,\mathcal P,S,D)$、完整A1–A3、准确锥、全部原P2和完整原PB；原 $E$ 可以不完备，旧 $D:E^2\to E$ 是同一总映射。只沿16.1–16.2已付的忠实、含单位、等距且准确保锥JC包含记原元素，令 $\mathcal A=C^*(X)$。不要求 $X=\mathcal A_{\rm sa}$，不预付旧关系的可加、连续、可测、商下降或完成延拓。固定实际原 $h,e$，$h^2=e^2=u$、$h\circ e=0$，以及同一旧值 $j=D(h,e)$。局部循环表取100.1，记

$$
\begin{gathered}
V_a=\{z\in E:a\circ z=0\},\qquad Gz=D(h,z)\quad(z\in V_h),\\
L_a z=a\circ z,\quad U_a=2L_a^2-I,\quad T=[L_j,L_e],\\
\Pi=\tfrac12(I-U_eU_j)=P_{+,-}+P_{-,+}\quad\hbox{在 }V_h\hbox{ 上},\\
z_B=\Pi z\in A_1\oplus A_2,\qquad
z_A=(I-\Pi)z\in A_0\oplus C_{+,+}.
\end{gathered}
\tag{123.1}
$$

$X=0$ 时以下关系全为零。$U_a z=aza$ 是原有限Jordan表达式；三份 $U_h,U_e,U_j$ 对易，均保持 $E$。$\Pi$ 保持原 $V_h$，保留100.1的全部四份分量。这里的 $C_{+,+}$ 仍位于 $V_h$，不是三轴全部交换的分量。32–36及81.5已付，对每个原 $z\in V_h$ 和实 $t$，

$$
G(tz)=tGz,\qquad Gz\in V_h,\qquad
(Gz)^2=z^2,\quad z\circ Gz=0,\quad G^2z=-z.
\tag{123.2}
$$

这些单输入与自身圆的关系不预付跨输入可加性。77.1–77.2在原标量平方片 $\operatorname{span}_{\mathbb R}\{h,e,j\}$ 的仿射窗给出，令 $n=u+h$，

$$
D(h,p+\alpha n)=q\quad(\alpha\in\mathbb R),
\qquad (p,q)=(e,j)\ \hbox{或}\ (j,-e).
\tag{123.3}
$$

这只调用已经识别的局部四维窗，不是一般单位平移。辅助环境乘法、Hilbert向量、投影与指数只用于证明；不把它们作为旧 $D$ 的输入或实际准备。

**定义 123.2（同一正读取的二表预算）。** 对任意数学正实读取 $\phi$，置

$$
B_\phi(v,w)=\phi(v^2)\phi(w^2)-\phi(v\circ w)^2.
\tag{123.4}
$$

16.2所用的原准确锥论证使环境数学态可以读取每张原P2，故 $|\phi D(v,w)|\le\sqrt{B_\phi(v,w)}$。每次比较始终使用同一个 $\phi$；不将 $|\phi D|^2$ 换成 $\phi(D^2)$。完整原PB在Jordan乘法已经识别后，准确写为

$$
\begin{gathered}
\nu=D(a,b)-a\circ c,\qquad\omega=a\circ b+D(a,c),\\
D(b+\nu,c+\omega)-D(b-\nu,c-\omega)
=-2b\circ\nu-2c\circ\omega.
\end{gathered}
\tag{123.5}
$$

这是静态卷22.3的两份平方等式经原评价分离的元素式，未展开任何未知响应的和。

## 124. 任意原横向输入的共享单位预算

**定理 124.1（两个实际锚的跨输入预算）。** 在123.1下，固定任意原 $z\in V_h$，记 $g=Gz$。对123.3的任一实际 $(p,q)$、每个实 $t$ 及同一数学正读取 $\phi$，令

$$
v_+=p+q-t(z+g),\qquad v_-=p-q+t(z-g).
$$

则

$$
\boxed{2|\phi(q+tz)|\le
\sqrt{B_\phi(n,v_+)}+\sqrt{B_\phi(n,v_-)}.}
\tag{124.1}
$$

其中 $v_\pm\in V_h$，所以每份根号内准确为 $2\phi(n)\phi(v_\pm^2)-\phi(v_\pm)^2$。

证明。对每个实 $\alpha,t$，只取实际原三元组

$$
(a,b,c)=(h,p+\alpha n,tz).
\tag{124.2}
$$

由123.2–123.3，内值准确为 $q,tg$，$h\circ b=\alpha n$、$h\circ c=0$。两份PB位移和完整外层输入是

$$
\begin{aligned}
\nu&=q,&\omega&=\alpha n+tg,\\
R_+&=p+q+\alpha n,&S_+&=t(z+g)+\alpha n,\\
R_-&=p-q+\alpha n,&S_-&=t(z-g)-\alpha n.
\end{aligned}
\tag{124.3}
$$

这些标签全部在原 $E$。由于 $p\circ q=z\circ g=0$ 以及 $n\circ q=q,n\circ z=z$，同一次PB给

$$
D(R_+,S_+)-D(R_-,S_-)=-2\alpha(q+tz).
\tag{124.4}
$$

对这两个实际旧值分别使用同一 $\phi$ 的原P2，再用标量三角不等式，得到

$$
2|\alpha|\,|\phi(q+tz)|
\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{124.5}
$$

这里只需展开已知实双线性型 $\phi(v\circ w)$。一般地，对已知自伴 $a,b,n$ 和 $s\in\{1,-1\}$，

$$
B_\phi(a+\alpha n,b+s\alpha n)
=B_\phi(a,b)+2\alpha C_s+\alpha^2 B_\phi(n,b-sa),
\tag{124.6}
$$

其中有限实数

$$
C_s=s\phi(a^2)\phi(n\circ b)+\phi(n\circ a)\phi(b^2)
-\phi(a\circ b)\{\phi(n\circ b)+s\phi(n\circ a)\}.
$$

直接相乘时三次、四次项各自抵消。正侧取 $a=p+q,b=t(z+g),s=1$，负侧取 $a=p-q,b=t(z-g),s=-1$；二次系数分别为 $B_\phi(n,v_+)$ 与 $B_\phi(n,v_-)$。把(124.5)除以 $|\alpha|$，在这两个显式标量二次式中令 $|\alpha|\to\infty$，即得(124.1)，包括零二次系数的退化情形。$n^2=2n$ 及 $n\circ v=v$ 给所述简式。

这里未知外层旧值已被逐份P2上界消去，极限只作用于已知标量式。每个有限 $\alpha$ 的实际输入仍在原域；没有假设旧 $D$ 的任何连续性，也没有增添联合复正表。∎

## 125. 两个锚的饱和读取识别全部原输出的投影

**定理 125.1（全原横向输入的交叉投影）。** 在123.1下，每个原 $z\in V_h$ 均满足

$$
\boxed{\Pi Gz=T\Pi z.}
\tag{125.1}
$$

允许 $z$ 同时含100.1的全部四份分量，平方不必中央、标量、可逆或具有有限谱。

证明。在 $\mathcal A$ 的忠实含单位Hilbert表示中读取固定原元素，内积第一槽共轭线性。以下省略表示符号；$K=je$ 是辅助环境元，满足

$$
K^*=-K,\quad K^2=-I,\quad Kh=hK,\quad Ke=-eK,\quad Kj=-jK.
\tag{125.2}
$$

它与原全词接口的 $K$ 区分。固定 $\sigma\in\{1,-1\}$，取任意单位向量

$$
\xi\in H_\sigma=\{\xi:h\xi=-\xi,\ K\xi=i\sigma\xi\},\qquad \eta=j\xi.
\tag{125.3}
$$

空子空间无需取向量。$\eta$ 为单位向量，且 $h\eta=\eta$、$K\eta=-i\sigma\eta$、$e\xi=i\sigma\eta$。对 $\delta>0$ 取数学向量态 $\phi_\delta$，向量为 $(\xi+\delta\eta)/\sqrt{1+\delta^2}$。对每个固定自伴 $v\in V_h$，反交换关系准确给

$$
\begin{aligned}
\phi_\delta(v)&=\frac{2\delta\operatorname{Re}\langle\eta,v\xi\rangle}{1+\delta^2},&
\phi_\delta(n)&=\frac{2\delta^2}{1+\delta^2},\\
\phi_\delta(v^2)&=
\frac{\|v\xi\|^2+\delta^2\|v\eta\|^2}{1+\delta^2}.&&
\end{aligned}
\tag{125.4}
$$

定义已知向量空间上的实正交投影 $P_\eta w=w-\operatorname{Re}\langle\eta,w\rangle\eta$。将(125.4)代入124.1的 $(p,q)=(e,j)$，约去 $2\delta/(1+\delta^2)$ 后，两个根号准确变成

$$
\sqrt{\|P_\eta(v_\pm\xi)\|^2+\delta^2\|v_\pm\eta\|^2}.
$$

于是令 $\delta\downarrow0$，只在这些固定已知向量范数中取极限，得到对全部实 $t$ 的

$$
2|\operatorname{Re}\langle\eta,(j+tz)\xi\rangle|
\le\|P_\eta(v_+\xi)\|+\|P_\eta(v_-\xi)\|.
\tag{125.5}
$$

令 $a=\langle\eta,z\xi\rangle,b=\langle\eta,g\xi\rangle$。在 $t=0$，两个未投影向量分别为 $(1+i\sigma)\eta,(-1+i\sigma)\eta$，投影后均为 $i\sigma\eta$。故(125.5)在零点饱和为 $2=1+1$，两份范数均在非零向量处可微。左侧导数为 $2\operatorname{Re}a$，右侧导数为

$$
\begin{aligned}
&\operatorname{Re}\langle i\sigma\eta,-P_\eta((z+g)\xi)\rangle
+\operatorname{Re}\langle i\sigma\eta,P_\eta((z-g)\xi)\rangle\\
&\hspace{3em}=-2\sigma\operatorname{Im}b.
\end{aligned}
$$

因不等式对零点两侧的 $t$ 都成立，饱和处导数必须相等，即

$$
\operatorname{Re}a=-\sigma\operatorname{Im}b.
\tag{125.6}
$$

现在使用124.1的另一份实际锚 $(p,q)=(j,-e)$。仍有 $qp=K$，而 $\eta'=q\xi=-i\sigma\eta$；(125.4)–(125.6)逐式适用。此时 $a'=i\sigma a,b'=i\sigma b$，故 $\operatorname{Re}b=\sigma\operatorname{Im}a$。联合两份实等式得到

$$
b=-i\sigma a,\qquad
\langle j\xi,(g+i\sigma z)\xi\rangle=0.
\tag{125.7}
$$

这里没有对旧 $D$ 求导；$g=Gz$ 从始至终固定。所有微分只涉及 $t$ 的显式仿射向量及非零处的普通范数。

令 $Q_\sigma$ 为 $H_\sigma$ 的Hilbert投影，$R_\sigma=jQ_\sigma j$。$j$ 将 $H_\sigma$ 等距映到 $h=1,K=-i\sigma$ 的共同子空间。式(125.7)对 $H_\sigma$ 中全部向量成立，普通复极化因而给

$$
Q_\sigma j(g+i\sigma z)Q_\sigma=0,
\qquad R_\sigma gQ_\sigma=-i\sigma R_\sigma zQ_\sigma.
\tag{125.8}
$$

具体地，对任意两个向量分别代入其和及其中一个乘 $i$ 的和，即消去两个有序非对角项；这里极化的是固定有界算子的复二次式，不是未知响应或未给的联合正性。

为把压缩读数接回原投影，取辅助自伴对称元 $O=ihK$。其共轭恰为原有限Jordan自同构

$$
\mathcal F=U_hU_eU_j,\qquad \mathcal F(v)=OvO,\qquad
\mathcal F|_{V_h}=-U_eU_j,\qquad
\Pi=\tfrac12(I+\mathcal F)|_{V_h}.
\tag{125.9}
$$

不要求 $\mathcal F=I$。$O$ 在 $H_\sigma$ 及 $R_\sigma H$ 上的符号同为 $\sigma$，在另一个 $h=1$ 子空间上符号相反。故对 $v\in V_h$，

$$
(\Pi v)Q_\sigma=R_\sigma vQ_\sigma.
\tag{125.10}
$$

另一方面，102.2的已知代数式给 $Tw=Kw$ 对所有 $w\in A_1\oplus A_2$ 成立；$K$ 在 $R_\sigma H$ 上为 $-i\sigma$。因此(125.8)–(125.10)说明 $\Pi g$ 与 $T\Pi z$ 在每个 $H_\sigma$ 上相同。这两份空间之和是整个 $h=-1$ 子空间。两个待比较算子均自伴并与 $h$ 反交换，所以另一非对角块由伴随确定，也相同。忠实性给原元素等式(125.1)。$Q_\sigma,R_\sigma,O$ 都只承担数学读取，未成为任何旧调用的输入。∎

## 126. 保留两份余量的平方与交叉和识别

**推论 126.1（原余量预算与跨分量可加）。** 在123.1下，对每个原 $z\in V_h$，

$$
\boxed{r_z:=Gz-Tz_B\in A_0\oplus C_{+,+},\qquad r_z^2=z_A^2.}
\tag{126.1}
$$

特别，对全部原 $x\in A_1,y\in A_2$，

$$
\boxed{G(x+y)=T(x+y)=Gx+Gy.}
\tag{126.2}
$$

证明。125.1给 $\Pi r_z=0$，所以两份保留扇区正是所述直和。125.9的 $\mathcal F$ 是原Jordan自同构，分别在 $z_B,Tz_B$ 上取正号，在 $z_A,r_z$ 上取负号。对已付 $(Gz)^2=z^2$ 施加 $(I+\mathcal F)/2$，混合项消去，得到

$$
(Tz_B)^2+r_z^2=z_B^2+z_A^2.
$$

102.2只用于已知 $T$，给 $(Tz_B)^2=z_B^2$，故得126.1。若 $z=x+y\in A_1\oplus A_2$，则 $z_A=0$，自伴平方零迫使 $r_z=0$。$T$ 为已知实线性算子，101.1已分别识别 $Gx=Tx,Gy=Ty$，即得126.2。不要求两个原平方成比例或原交叠为零。

这没有由相同平方推出两个一般响应相同。对一般 $z$，$r_z=G(z_A)$ 仍不由126.1得出；$A_0$ 与 $C_{+,+}$ 均保留。∎

## 127. 八份原分量共同供应全局中央 Gram

**定理 127.1（整个共同反交换空间的全局中心）。** 在123.1下，令

$$
E_\sigma=\{x\in E:U_ax=\sigma_a x\ (a=h,e,j)\},
\quad \sigma\in\{1,-1\}^3,\qquad
M=E_{---}=A_0,\quad B=E_{+++}.
\tag{127.1}
$$

对全部原 $v,w\in M$，

$$
\boxed{v\circ w\in E\cap Z(X)\cap Z(\mathcal A).}
\tag{127.2}
$$

特别，$w^2$ 对整个 $\mathcal A=C^*(X)$ 中的元素交换，不只是对三轴与 $w$ 生成的诊断子代数交换。本证明不使用125.1。

证明。对每个三符号 $\sigma$，有限原投影

$$
\mathcal P_\sigma=\tfrac18(I+\sigma_hU_h)(I+\sigma_eU_e)(I+\sigma_jU_j)
\tag{127.3}
$$

给 $E=\bigoplus_\sigma E_\sigma$。每个 $U_a$ 为Jordan自同构，故Jordan乘积逐位相乘符号。$U_ax=x$ 等价于 $ax=xa$，$U_ax=-x$ 等价于 $ax=-xa$。这些只在已付环境中解释；没有在全部 $E$ 上令 $U_hU_eU_j=I$。

固定原 $w\in M$。102.1直接给 $w\circ x=0$ 对 $x\in E_{-+-},E_{--+}$；再对实际循环三元组 $(e,j,h)$ 应用同一102.1，补得 $x\in E_{+--}$。循环有效性由同一旧表 $D(e,j)=h,D(j,h)=e$ 支付，不是重新选择取向。因此 $w$ 与恰有一个正号的三份扇区均Jordan正交。

若原 $x$ 位于恰有两个正号的扇区，$t=w\circ x$ 位于恰有一个正号的扇区，所以上段给 $w\circ t=0$，即 $L_w^2x=0$。这里可直接使用成熟的C*范数论证：在环境复空间上，已知有界线性算子 $L_w$ 满足

$$
e^{isL_w}x=e^{isw/2}xe^{isw/2}=x+isL_wx\qquad(s\in\mathbb R).
\tag{127.4}
$$

第一式由左右乘法对易，第二式由 $L_w^2x=0$ 的指数级数。两侧酉乘保持范数，故 $|s|\|L_wx\|\le2\|x\|$ 对全部有限实 $s$ 成立，迫使 $L_wx=0$。因此 $w$ 与上述两类合计六份扇区的元素都反交换。指数只在固定环境中证明这个核恒等式，未对旧 $D$ 取极限，也不供应实际时间演化。

若原 $x\in B$，因 $x$ 与 $e$ 交换，$ex=e\circ x\in E$，且其三符号为 $(-,+,-)$。上段已知 $w\circ(ex)=0$，而 $ew=-we$，所以

$$
0=w\circ(ex)=\tfrac12e(xw-wx).
\tag{127.5}
$$

由 $e^2=u$，得 $[x,w]=0$。这一论证作用于全部原 $B$，没有将其认作标量。

最后，若原 $v\in M$，则 $w\circ v\in B$，刚证的交换性给

$$
[w^2,v]=2[w,w\circ v]=0.
\tag{127.6}
$$

对原 $x\in B$，由 $[w,x]=0$ 得 $[w^2,x]=0$；对其余六份扇区，由 $wx=-xw$ 同样得 $[w^2,x]=0$。这逐一覆盖全部八份原扇区，故 $w^2$ 与全部原 $E$ 交换。已知环境乘法的连续性将此交换性传到 $X=\overline E$，继而传到其生成的 $\mathcal A$。又 $w^2\in E$，所以它在 $E\cap Z(\mathcal A)$ 中；环境交换性直接给Jordan算子交换性，故亦在 $Z(X)$ 中。

对原 $v+w\in M$ 使用同一结论，再对已知Jordan平方作实极化，

$$
v\circ w=\tfrac12\{(v+w)^2-v^2-w^2\}\in E\cap Z(X)\cap Z(\mathcal A),
$$

即得127.2。这里极化的只是原已知Jordan乘法，未极化未知响应。∎

## 128. 原输出闭合之后的跨窗口线性消费者

**推论 128.1（整个原共同反交换空间的同一线性行）。** 对127.1的整个原 $M$，令 $F_a w=D(a,w)$，$a\in\{h,e,j\}$。则每个 $F_a:M\to M$ 实线性，且对任意原 $v,w\in M$，

$$
F_av\circ F_aw=v\circ w,\qquad
v\circ F_aw+F_av\circ w=0,\qquad F_a^2=-I_M.
\tag{128.1}
$$

证明。先逐项保留106.2已付的实际输出闭合，才使用线性消费者。对任一实际循环 $(a,b,c)=(h,e,j),(e,j,h),(j,h,e)$ 及原 $w\in M$，97.1给

$$
D(a,w+b)=F_aw+c,\qquad D(a,w+c)=F_aw-b.
\tag{128.2}
$$

两份实际标签的平方保持，加上 $w\circ b=w\circ c=0$，分别给 $c\circ F_aw=0,b\circ F_aw=0$；原行已有 $a\circ F_aw=0$。故三个 $F_a$ 都把全部原 $M$ 送回 $M$，正是106.2，不将闭合算作新的供应结论。

127.2现在给29.1所要求的全局条件 $v\circ w\in Z(X)$。对每根实际 $a$，以 $W=M\subset V_a$ 应用该已发表推论，得到实线性行 $J_a=2D(a/2,\cdot)$ 与全部混合Gram式。35.1在全实强度上识别 $J_a=D(a,\cdot)=F_a$；上段闭合使29.1的负平方结论也在 $M$ 上成立，即128.1。其中央字符和商态只用于读取原标签的像；旧 $D$ 的一般商下降并不是其前件。

具体地，这个消费者对任意有限原族 $v_1,\ldots,v_m\in M$ 和实数 $t_i$ 给

$$
D\left(a,\sum_{i=1}^m t_iv_i\right)=\sum_{i=1}^m t_iD(a,v_i).
\tag{128.3}
$$

各 $v_i$ 可来自不同108.1的 $W(w)$，平方和混合Gram可有任意多个独立中央坐标。共同强度或单个 $W(w)$ 的前件不再需要。没有由此声称中心模线性。

107.1–107.2的逐点复合表现在可作为整个 $M$ 上实线性算子的等式使用：记 $I=F_h,J=F_e,K_M=F_j$，则 $IJ=K_M,JK_M=I,K_MI=J$，反向乘积取负，且三个平方均为 $-I_M$。这份四元数表、106.2的闭合、108.1的单方向共同强度窗与109.1的八维不可约读取消费均直接复用，不重新计作生产者。新增供应是127.2的全局中央Gram及其使29.1适用于整个原 $M$ 的连接。∎

## 129. 原前件对应、几何与完整来源边界

**定义 129.1（两条供应及成熟中间工具的范围）。** 124.1–126.1的承重关系是：任意原 $z$ 与两个已知仿射三轴锚各作一次实际PB，同一读取的两张P2先给124.1；饱和向量读取的双侧一次变化再锁住复非对角压缩，最后由原共轭接回同一个旧输出的交叉投影。127.1的承重关系独立于它：102.1的实际正交关系与全部八份原共轭扇区一起，迫使共同反交换方向的平方属于全局中心，随后才接128.1的既有行消费者。两者均为 $\texttt{repo-derived}$ 综合，不宣称历史原创或文献穷尽。

原前件与使用位置的对应为：静态卷22.1–22.3给同一R-free候选及完整PB；前卷16.1–16.2给原准确锥、全部数学正读取与较弱JC包含；32–36、81.5给123.2；62、77.1–77.2给实际三轴循环及123.3。100.1给原有限投影，101.1只识别两份单独扇区，102.2只用于已知 $T$ 的平方；任意和的旧值由125.1–126.1另行支付。127.1只消费102.1的原正交，且先证明对整个 $E$ 的交换性；不把谱混合卷10–16的诊断中心当作 $Z(X)$。128.1按106.2、127.2、29.1、35.1的次序调用，107–109保持原消费者身份。

实Gram行列式展开、Hilbert向量态、固定复二次式的极化、范数在非零向量处的一次变化、C*范数与自伴平方零均为成熟中间工具。JC中的Jordan算子交换与环境交换的对应见 van de Wetering，[*Commutativity in Jordan Operator Algebras*](https://arxiv.org/html/1912.01903v1)，Proposition 3.2；127.1实际使用的是环境交换蕴涵Jordan算子交换的直接方向。没有把这个成熟对应另立为新分类。

Cabello–Peralta，[*Weak-2-local symmetric maps on C*-algebras*](https://arxiv.org/html/1510.00915v1)，Lemma 2.4与Theorem 2.5处理完整复C*域的weak-2-local symmetric映射，其同时实现的线性比较器不是本候选前件；125.1只对固定已知算子作普通复极化，不使用该局部线性定理。Alfsen–Shultz，[*Orientation in Operator Algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，Theorem 1的全局线性动力对应仍按前卷30.1的前件边界保留，所述原局部行并不供应它。OmegaQ024的共同锚联合PSD与Schur余项也没有加入124.1；其两份P2始终是实际外层对、同一个正读取的预算。

**定义 129.2（尚未支付的数学桥与七项实际消费者）。** 126.2给静态卷89.1的 $\delta_h(x,y)=0$ 对全部原 $x\in A_1,y\in A_2$；128.3给 $\delta_a(v,w)=0$ 对全部原 $v,w\in A_0$ 及 $a=h,e,j$。对一般 $z\in V_h$，126.1仍未识别 $r_z=G(z_A)$，也未支付剩余两份扇区之间以及它们与交叉分量之间的全部拼接。不同首标签、一般非正交输入、没有有用原单位平方正交轴的域、全部原 $a,b,c$ 的缺陷中心性与同一旧 $D$ 的全域实双线性均未由此取得。没有给出违反一般结论的完整全P2/PB反模型，也不从这些结论推出 $A_0=0$ 或删除 $C_{+,+}$。

静态卷89.2–89.3仍是条件消费者：另付全原 $\mathsf C_{\rm add}$ 后，静态卷32.2才给同一旧 $D$ 的实双线性及全部有限复Gram，静态卷23.1、静态卷33.2才接同一个 $a\star b=a\circ b-iD(a,b)$ 的结合性与原R。全局JC包含、局部四元数作用和数学压缩不能替代这个供应步骤。有限数学三轴不限制原空间或物理空间维数，也不保证实际能取得这些轴。

完整保持98.2与110.3的原来源：唯一原 $\Omega$、原 $E/D$、native、全词同一K/J/q、parent/ready、中心经典与不等维块、全部实际准备及零／不等／次归一质量；正质量Born只在实际完整菜单归一。Hilbert表示、叠加与可取得原标签保留原范围。CP仍需整台实际箭头、实际相关联合及递归同源参考；完整仪器连环境全部成功／失败／记录／后口输出，Kraus、TP、更新、Lüders及实际忠实交换共同生成的张量各守原前件。全部合法顺序／自适应／并行历史、每个仍合法未来、细记录与真正分组遗忘、停止／拒绝／销毁、同数两侧及逆向真实返回均保留。CountRead无穷、正常性、指定前对偶、原域上的流、物理钟、Hamiltonian生成元定义域、能量、作用量和共同正 $\hbar$ 仍须实际来源。本节只供应所述两条原响应关系，不宣告完整量子起源目标成立。

## 追加锚（本行以下为增补区）
