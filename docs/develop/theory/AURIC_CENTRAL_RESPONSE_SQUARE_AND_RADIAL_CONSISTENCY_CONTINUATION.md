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

## 130. 原三轴应用的完整前件与两条供应

**定义 130.1（原域、实际三轴与引用范围）。** 本续卷130–136节仍取123.1的同一原 $(E,C,u,N,\mathcal P,S,D)$，其中 $E$ 是含单位实 Archimedean 序单位空间；正实线性评价族 $\mathcal P$ 分离元素并准确决定 $C$。保留全部原质量，包括零、不等与次归一质量。完整A1是全部有向Hermitian二表正性；A2是原相加三表及其排列的实部半正定与 $(1,-1,-1)$ 的零二次值；A3是 $S(u,u)=u$，以及同一个固定有理 $0<\theta\le1$ 上的 $0\le v\le\theta u\Rightarrow S(v,v)\le v$。全部原P2和完整原PB均取定义123.2及式(123.4)–(123.5)，对全部原输入成立。

沿前卷16.1–16.2的同一忠实、含单位、等距且准确保锥JC包含记原元素，有

$$
S(a,b)=a\circ b=\frac{ab+ba}{2},\qquad
E\subset X\subset\mathcal A_{\rm sa},\qquad
\overline E=X,\quad\mathcal A=C^*(X),\quad
C=E\cap\mathcal A_+,\quad N=\|\cdot\||_E.
\tag{130.1}
$$

原 $E$ 是这些已识别Jordan运算的原定义域，可以不完备；不要求 $X=\mathcal A_{\rm sa}$。$D:E^2\to E$ 始终是同一原总映射，不预付一般可加、连续、可测、商下降或完成延拓。以下未标“前卷”的130–136节编号均指本续卷；前卷0–122及本续卷123–129的定义与引用保持各自原范围。

固定123.1的实际原 $h,e$ 及同一旧输出 $j=D(h,e)$，故

$$
h^2=e^2=j^2=u,\qquad
h\circ e=h\circ j=e\circ j=0,\qquad
D(e,j)=h,\quad D(j,h)=e.
\tag{130.2}
$$

仍记 $V_a=\{z\in E:a\circ z=0\}$、$L_a z=a\circ z$、$U_a=2L_a^2-I$、$T=[L_j,L_e]$，并记 $Gz=D(h,z)$ 对原 $z\in V_h$。对三个实际首标签另记 $F_a w=D(a,w)$，只在所用原 $w\in V_a$ 上调用。前卷100.1及本续卷127.1的原有限分量为

$$
\begin{gathered}
E_\sigma=\{x\in E:U_ax=\sigma_a x\ (a=h,e,j)\},\qquad
E=\bigoplus_{\sigma\in\{1,-1\}^3}E_\sigma,\\
A_1=E_{-+-},\quad A_2=E_{--+},\quad
M=A_0=E_{---},\quad C_{+,+}=E_{-++},\\
V_h=A_1\oplus A_2\oplus M\oplus C_{+,+},\qquad
\Pi=\tfrac12(I-U_eU_j)|_{V_h}.
\end{gathered}
\tag{130.3}
$$

三个 $U_a$ 是保持原 $E$ 的对易Jordan自同构。每个分量投影均是式(127.3)的有限原Jordan表达式。环境解释是 $U_ax=axa$，正号等价于 $ax=xa$，负号等价于 $ax=-xa$。这里尚不假设三份共轭的乘积为恒等。

**定义 130.2（所消费的已发表关系）。** 对全部原 $z\in V_h$，125.1及126.1供应

$$
\begin{gathered}
\Pi Gz=T\Pi z,\qquad
r_z:=Gz-T\Pi z\in M\oplus C_{+,+},\\
r_z^2=((I-\Pi)z)^2.
\end{gathered}
\tag{130.4}
$$

只消费127.1的平方结论

$$
w^2\in E\cap Z(X)\cap Z(\mathcal A)\qquad(w\in M).
\tag{130.5}
$$

该中心是整个 $X$ 及其生成的 $\mathcal A$ 的中心。它不是某个有限生成诊断代数的中心；以下不需要128.1的全 $M$ 线性结论。前卷32–36及式(123.2)给原行的实齐次、自身正交、平方保持与负平方。前卷106.2、107.1–107.2给 $F_a(M)\subset M$ 及实际三轴复合表；前卷97.1给原标量平方方向上的加法。前卷54.1、56.1只在其首标签严格收缩且平方全局中央、相应原横向输入的Gram全局中央时使用。没有对125.1增加循环变体。

## 131. 共享投影排除原双交换横向分量

**定理 131.1（整个原 $C_{+,+}$ 为零）。** 在130.1的原背景下，$C_{+,+}=\{0\}$。

证明。任取原 $c\in C_{+,+}$，使用同一实际输入 $z=e+c\in V_h$。因 $e\in A_1$，有 $\Pi z=e$、$Te=j$，故(130.4)给

$$
G(e+c)=j+s,\qquad s=m+d\in M\oplus C_{+,+},\qquad s^2=c^2.
\tag{131.1}
$$

原平方保持 $(Gz)^2=z^2$ 因而准确给

$$
j\circ s=e\circ c.
\tag{131.2}
$$

$j\circ m=0$，故左侧是 $j\circ d$。它的 $U_e$ 符号为负，因为 $U_ej=-j$、$U_ed=d$；右侧的 $U_e$ 符号为正。对(131.2)施加保持原域的 $(I+U_e)/2$，得到 $e\circ c=0$。又 $U_ec=c$ 意味着 $ec=ce$，所以 $e\circ c=ec$，在环境中左乘 $e$ 并用 $e^2=u$ 得 $c=0$。环境乘法只用于证明这个原元素为零，没有成为新的旧响应输入。∎

## 132. 全局中央平方与实际三轴复合排除共同反交换方向

**定理 132.1（整个原 $M$ 为零）。** 在同一原背景下，$M=A_0=E_{---}=\{0\}$。不要求其中元素的平方为标量、可逆或有限谱。

证明。任取原 $w_0\in M$。选择正实数 $k$ 使 $w=kw_0$ 满足 $\|w\|<1$，记

$$
R=w^2,\qquad p=F_hw,\qquad r=F_jw.
\tag{132.1}
$$

由(130.5)，$R\in E\cap Z(X)\cap Z(\mathcal A)$。前卷106.2、107.1、原平方保持及自身正交给

$$
p,r\in M,\qquad p^2=r^2=R,\qquad
w\circ r=0,\qquad F_er=p,\qquad F_eh=-j.
\tag{132.2}
$$

特别 $\|r\|=\|w\|$。取正实数 $t$ 满足 $t(1+\|w\|)<1$，定义真正原标签

$$
a=t(h+r),\qquad b=e+w.
\tag{132.3}
$$

它们满足

$$
\begin{gathered}
\|a\|<1,\qquad a^2=t^2(u+R)\in Z(X)\cap Z(\mathcal A),\\
e,w\in V_a,\qquad e^2=u,\quad w^2=R,\quad e\circ w=0,\\
a\circ b=0,\qquad b^2=u+R.
\end{gathered}
\tag{132.4}
$$

这里 $r\circ e=h\circ w=h\circ r=0$ 来自原共同反交换空间，$r\circ w=0$ 来自原自身响应，故两份横向条件逐项成立。于是前卷56.1用于严格收缩的实际首标签 $a$ 及原 $e,w$，确实给

$$
D(a,b)=D(a,e)+D(a,w).
\tag{132.5}
$$

先计算第一项。首标签 $e$ 是原单位平方轴，$r,h\in V_e$，且 $r\circ h=0$。前卷97.1沿原标量平方方向 $h$ 及前卷35.1的原行实齐次给

$$
D(a,e)=-D(e,t(h+r))
=-t(F_eh+F_er)=t(j-p).
\tag{132.6}
$$

第一步是原反对称性；没有使用一般第一槽齐次。

再计算第二项。实际首标签 $w$ 已严格收缩，平方 $R$ 全局中央。原 $h,r\in V_w$ 的Gram是 $u,R,0$，所以前卷56.1与54.1在准确原域上给

$$
D(w,a)=t\{D(w,h)+D(w,r)\}.
\tag{132.7}
$$

原反对称性给 $D(w,h)=-p$ 及 $D(w,j)=-r$。对同一个实际首标签 $w$、原横向标签 $j$，前卷54.1的带权负平方给

$$
D(w,-r)=D(w,D(w,j))=-R\circ j.
$$

原第二槽奇性因而给 $D(w,r)=R\circ j$。再用原反对称性，(132.7)成为

$$
D(a,w)=t(p-R\circ j).
\tag{132.8}
$$

把两份已识别的同一旧值代回(132.5)，得到

$$
D(a,b)=t(u-R)j.
\tag{132.9}
$$

右侧环境乘积等于原Jordan表达式 $t(j-R\circ j)$。另一方面，$a\circ b=0$，故前卷16.3的原正交面积式与(132.4)给

$$
D(a,b)^2=a^2b^2=t^2(u+R)^2.
\tag{132.10}
$$

对(132.9)平方，$R$ 与 $j$ 交换且 $j^2=u$，同一个左侧又等于 $t^2(u-R)^2$。相减得 $4t^2R=0$。由于 $t>0$，有 $R=0$，自伴平方零给 $w=0$，再由 $k>0$ 得 $w_0=0$。

所有缩放均为原实线性域内的实数缩放。未知响应的缩放只在已经支付的单位平方行或严格收缩中央平方行的第二槽中调用。没有除以 $R$，没有归一化谱纤维，也没有用前卷109.1的局部诊断中心替换(130.5)。零元素和零强度不被删除。∎

## 133. 同一实际横向行的全部输入识别

**定理 133.1（全原 $V_h$ 上的同一 $D=T$）。** 在130.1下，对每个原 $z\in V_h$，

$$
\boxed{D(h,z)=Tz,\qquad V_h=A_1\oplus A_2.}
\tag{133.1}
$$

此原限制实线性、保持 $V_h$，并对全部原 $y,z\in V_h$ 满足

$$
\begin{gathered}
(Ty)^2=y^2,\qquad T^2y=-y,\qquad \|Ty\|=\|y\|,\\
Ty\circ Tz=y\circ z,\qquad
y\circ Tz+Ty\circ z=0.
\end{gathered}
\tag{133.2}
$$

证明。131.1、132.1使 $\Pi=I$ 在整个原 $V_h$ 上成立，(130.4)因而给同一实际输出(133.1)。$T=[L_j,L_e]$ 原本就是保持 $E$ 的已知实线性Jordan表达式，前卷101.1还给 $T(A_1)\subset A_2$、$T(A_2)\subset A_1$。

仅为环境计算记 $K_0=je$。前卷102.2给

$$
K_0^*=-K_0,\qquad K_0^2=-u,\qquad
Tz=\tfrac12(K_0z-zK_0)=K_0z\quad(z\in V_h),
\tag{133.3}
$$

因为原 $V_h=A_1\oplus A_2$ 的全部元素都与 $K_0$ 反交换。于是 $(Ty)(Tz)=yz$、$T^2y=-y$，而左乘酉元 $K_0$ 保范数。取Jordan对称部得到Gram等式；展开并消去 $yK_0=-K_0y$、$zK_0=-K_0z$ 的对应项，得到斜关系。这些计算识别的是(133.1)已经支付的实际旧输出，未由已知 $T$ 的性质反向假定未知 $G$ 的性质。∎

**推论 133.2（固定实际首轴的全部横向缺陷）。** 对任意有限原族 $z_i\in V_h$ 及实数 $s_i$，

$$
D\left(h,\sum_i s_i z_i\right)=\sum_i s_iD(h,z_i).
\tag{133.4}
$$

因此静态卷89.1的原加性缺陷 $\delta_h(y,z)=D(h,y+z)-D(h,y)-D(h,z)$ 对全部原 $y,z\in V_h$ 为零。

证明。只在原有限和中使用(133.1)与已知 $T$ 的实线性。前卷35.1还保证旧记号 $J_hz=2D(h/2,z)$ 在这个定义域上就是同一 $D(h,z)$。因而前卷114–115中的固定参考行 $J$ 也对应这里的实际输出。平方、Gram和交叠不受标量、中央、可逆或有限谱限制；这里没有把 $D$ 延拓到完成，也没有得到静态卷89.2的全原 $\mathsf C_{\rm add}$。∎

## 134. 从横向消失到整个原域的三重共轭

**定理 134.1（所有原分量的偶性与辅助中央取向）。** 在130.1下，

$$
\boxed{\mathcal F:=U_hU_eU_j=I_E.}
\tag{134.1}
$$

环境元 $Q=i h e j\in\mathcal A$ 满足

$$
\boxed{Q^*=Q,\qquad Q^2=u,\qquad Q\in Z(\mathcal A).}
\tag{134.2}
$$

不要求 $Q\in E$、$Q\in X$ 或 $Q$ 为标量。对全部原 $z\in V_h$，同一旧值准确为

$$
\boxed{D(h,z)=Tz=iQhz.}
\tag{134.3}
$$

证明。使用(130.3)的全部八份原有限投影。$\mathcal F$ 在 $E_\sigma$ 上的符号是 $\sigma_h\sigma_e\sigma_j$。131.1已经消去 $E_{-++}$，132.1已经消去 $E_{---}$。尚须处理 $h$-交换的两份负偶性空间，不能从 $V_h$ 上的结论直接略过它们。

若原 $x\in E_{++-}$，则 $x$ 与 $h,e$ 交换、与 $j$ 反交换。原元素 $c=e\circ x=ex\in E$ 的三符号是 $(-,+,+)$，故 $c\in C_{+,+}=0$。因 $e^2=u$ 且 $ex=xe$，$e\circ c=x$，所以 $x=0$。若原 $x\in E_{+-+}$，同样取原 $c=j\circ x=jx$，其三符号也是 $(-,+,+)$，且 $j\circ c=x$，故 $x=0$。这两份桥都只使用有限原Jordan运算，没有向原域加入 $ex$ 或 $jx$ 以外的新乘法标签：它们在各自交换条件下本来就是原Jordan乘积。

全部原分量的对应为：

| 原三符号 $(\sigma_h,\sigma_e,\sigma_j)$ | $\mathcal F$ 符号 | 原域上的结论 |
| --- | --- | --- |
| $(+,+,+)$ | $+$ | 保留，$\mathcal F x=x$ |
| $(+,+,-)$ | $-$ | $e\circ x\in E_{-++}=0$，且 $x=e\circ(e\circ x)=0$ |
| $(+,-,+)$ | $-$ | $j\circ x\in E_{-++}=0$，且 $x=j\circ(j\circ x)=0$ |
| $(+,-,-)$ | $+$ | 保留，$\mathcal F x=x$ |
| $(-,+,+)$ | $-$ | 131.1给零 |
| $(-,+,-)$ | $+$ | 原 $A_1$，保留 |
| $(-,-,+)$ | $+$ | 原 $A_2$，保留 |
| $(-,-,-)$ | $-$ | 132.1给零 |

故所有 $\mathcal F$-负分量为零，证明(134.1)对整个原 $E$ 成立。

三个轴两两反交换且平方为 $u$，直接给 $(hej)^*=-hej$、$(hej)^2=-u$，所以 $Q$ 自伴且平方为 $u$。三重共轭在环境中的准确次序是

$$
\mathcal F(x)=hej\,x\,jeh=QxQ.
\tag{134.4}
$$

由(134.1)，$QxQ=x$ 对每个原 $x\in E$ 成立；右乘 $Q$ 给 $Qx=xQ$。环境乘法连续性将此交换性传到 $X=\overline E$，再传到 $\mathcal A=C^*(X)$，得到整个环境的中央性。该步骤不延拓旧 $D$。

最后，$je=iQh$，故(133.3)给(134.3)，符号与原 $D(h,e)=j$ 一致。$Q$ 只是辅助环境中的中央自伴对称元，可在不同中央部分有不同符号，未选择统一标量取向。$K_0=je$ 与 $Q$ 均不指原native／全词接口的 $K,q,J$。∎

## 135. 原运输多项式的双交换子与完整标量平方差消费者

**定理 135.1（全部原横向对的准确缺陷式）。** 对任意原 $y,z\in V_h$，定义同一实际输出及原Jordan多项式

$$
\begin{gathered}
j_y=D(h,y),\qquad G_0=y^2=j_y^2,\\
\mathcal U_a(v)=2a\circ(a\circ v)-a^2\circ v,\\
\Delta_y(z)=\mathcal U_y(\mathcal U_{j_y}(z))+G_0^2\circ z\in E,
\qquad \Xi_y(z)=\Delta_y(z)\circ z\in E.
\end{gathered}
\tag{135.1}
$$

辅助环境元 $F_y=iyj_y$、$H_y=hF_y$ 满足

$$
F_y=QhG_0,\qquad H_y=QG_0,
\qquad [H_y,z]=Q[G_0,z].
\tag{135.2}
$$

对这些全部原输入，有准确环境表达

$$
\boxed{\Delta_y(z)=\frac12[G_0,[G_0,z]].}
\tag{135.3}
$$

不要求 $G_0$ 全局中央，也不要求任何平方可逆或具有有限谱。双交换子右侧沿(135.3)等于原域内的多项式，未被添加为新的响应输入。

证明。由(134.3)，$j_y=iQhy$；$hy=-yh$ 且 $Q$ 中央，所以

$$
F_y=iy(iQhy)=Qhy^2=QhG_0,\qquad H_y=QG_0.
$$

$G_0$ 与 $h$ 交换，故 $F_y,H_y$ 自伴，且 $F_y^2=G_0^2$。中央性给(135.2)的交换子式。成熟的JC二次表示恒等式是 $\mathcal U_a(v)=ava$；只将它用在已有原Jordan表达式上。由 $yj_y=-j_yy$，

$$
\mathcal U_y(\mathcal U_{j_y}(z))
=yj_yzj_yy=F_yzF_y
=QhG_0zQhG_0=-G_0zG_0.
\tag{135.4}
$$

最后一步只用 $Q^2=u$、$Q$ 中央、$hG_0=G_0h$ 及 $hz=-zh$，没有令 $G_0$ 与 $z$ 交换。因而

$$
\Delta_y(z)=-G_0zG_0+\tfrac12(G_0^2z+zG_0^2)
=\tfrac12[G_0,[G_0,z]],
$$

即得(135.3)。$\Delta_y(z)$ 与 $\Xi_y(z)$ 属于原 $E$，由(135.1)的有限Jordan表达式保证。这里没有断言任意 $y,z$ 的 $\Xi_y(z)$ 都非负；前卷114.2的正性只在其标量平方差定义域使用。∎

**推论 135.2（整个合格原分支的零缺陷与同一输出运输）。** 若上述原 $y,z$ 满足 $y^2-z^2=\delta u$，其中 $\delta\in\mathbb R$，则

$$
\boxed{\Delta_y(z)=\Xi_y(z)=0.}
\tag{135.5}
$$

令 $j_z=D(h,z)$。前卷115.1–115.2对这些全部原对适用，准确给

$$
\begin{gathered}
j_y\circ j_z=y\circ z,\qquad
y\circ j_z+j_y\circ z=0,\\
\boxed{\mathcal U_y(\mathcal U_{j_y}(j_z))+G_0^2\circ j_z=0.}
\end{gathered}
\tag{135.6}
$$

零、奇异、非可逆和非有限谱强度均保留。

证明。$G_0=z^2+\delta u$ 使 $[G_0,z]=0$，(135.3)直接给 $\Delta_y(z)=0$，其原Jordan乘积给 $\Xi_y(z)=0$。也可在前卷114.2的准确原域中，用(135.2)读取

$$
2\Xi_y(z)=[H_y,z]^*[H_y,z]
=[G_0,z]^*[G_0,z]=0.
\tag{135.7}
$$

原对应是前卷114.1的 $J=J_h=D(h,\cdot)$、$j=j_y$、$k=j_z$、$G=G_0$，由推论133.2及前卷35.1支付，未改换旧输出。因此零缺陷是前卷115.1的已推出前件，(135.6)是该既有消费者的直接结论，其证明不必重作。两份混合式还与式(133.2)的全 $V_h$ Gram／斜关系相符。作为输出运输的同域核对，$j_z=iQhz\in V_h$ 且

$$
[G_0,j_z]=iQh[G_0,z]=0;
$$

再将(135.3)用于这个原 $j_z$，也得到(135.6)最后一式。整个论证没有除以 $G_0$ 或 $z^2$，没有添加原根、逆或谱投影。若 $X=0$，上述原元素与关系全为零，无需选态。∎

## 136. 原供应对应、几何与完整来源的未决边界

**定义 136.1（关系的用途与数学归属）。** 131–135是 $\texttt{repo-derived}$ 的综合应用。承重关系是原投影余量与全局中央平方共同排除整个剩余横向空间，原有限Jordan映射再排除全部负偶性分量，最后同一实际行把原运输缺陷化成强度的双交换子。准确依赖与消费者为：

| 来源或结论 | 所承担的原义务 |
| --- | --- |
| 本续卷123.1、125.1、126.1 | 保留完整原背景，并识别 $D(h,e+c)$ 的实际投影与余量平方，供131.1消去 $C_{+,+}$ |
| 本续卷127.1的平方结论 | 给任意原 $w\in M$ 的全局中央 $w^2$，供132.1两次应用前卷56.1；不使用128.1或循环版125.1 |
| 前卷106.2、107.1–107.2、97.1、54.1、56.1及式(16.3) | 在准确原定义域识别式(132.3)的同一旧值，再以其原面积平方排除 $M$；严格收缩由实缩放支付 |
| 131.1、132.1、前卷101.1及102.2 | 在整个原 $V_h$ 识别 $D(h,\cdot)=T$，得到全部混合Gram与斜关系，推进前卷110、116保留的原行缺口及静态卷89.1的横向缺陷 |
| 原有限八分量投影及134.1 | 对全部原 $E$ 给 $U_hU_eU_j=I$，由此证明辅助 $Q$ 在整个 $\mathcal A$ 中中央 |
| 134.3、135.3及原 $y^2-z^2=\delta u$ | 给前卷114–115整个合格原分支的 $\Delta=\Xi=0$ 与同一实际输出运输，支付前卷116.2在此native分支上的零缺陷前件 |

前卷107的三轴复合仍由它已经展开的实际PB外层对供应：循环 $(a,b,c)$ 与原 $w$ 对应 $(c,F_aw)$、$(b,w)$，另一份对应 $(c,w)$、$(b,-F_aw)$，两份右端均为零。这里消费该已发表原值身份，不把四元数表重新作为独立生产者，也不以全域线性替换那些实际调用。

成熟中间工具是实线性投影、JC自伴平方零、单位共轭、范数连续性及固定环境乘法的交换子计算。van de Wetering，[*Commutativity in Jordan Operator Algebras*](https://arxiv.org/html/1912.01903v1)，Proposition 3.2及其式(2)给JC算子交换与环境交换的对应及 $[L_a,L_b]x=[[a,b],x]/4$；该文的二次表示约定给 $\mathcal U_a(v)=ava$。这里只将这些成熟恒等式作为原响应应用的中间工具，不另立通用分类，也不主张历史优先权或文献穷尽。

几何上，整个原 $V_h$ 现在由同一个实线性 $T$ 配对，$T^2=-I$，且准确保持原Jordan Gram。辅助中央对称元 $Q$ 记录该实际三轴的取向；它不被要求是原可取得标签或统一标量。强度 $y^2$ 对第二标签的交换关系控制135.3的运输缺陷，标量平方差使这种交换直接成立。三轴、横向复结构与中央取向均不限定整个原域或物理空间为三维；平方和交叠仍允许非中央、奇异与连续谱。

**定义 136.2（一般原响应与全部实际来源保持）。** 这些结论以存在式(130.2)的实际原单位平方正交对及其同一旧响应为条件。没有这种原轴的域仍属于完整目标，未由本应用覆盖。对一般原首标签、一般非正交输入，以及 $h$-交换分量与横向分量相加后的同一旧响应，尚未由这里取得全域加法或一般单位／中央平移。$Q$ 的全局中央性及 $\mathcal F=I_E$ 是已付环境中的结构结论，不是全部旧 $D(a,b)$ 的环境交换子表示。

静态卷89.2–89.3仍是全原 $\mathsf C_{\rm add}$ 的条件消费者；式(133.4)只供应其固定实际 $h$ 的横向子类。静态卷90–93所需的、对全部原 $a,b,c$ 统一的单个有限加性缺陷上界，未由原P2/PB或本应用生产，也不作本应用前提。一般旧 $D$ 的实双线性、完整原P3及全部有限复Gram、原R和同一 $a\star b=a\circ b-iD(a,b)$ 的结合性仍各守原供应条件；没有给出违背这些一般结论的忠实全P2／全PB反模型。前卷110.2与116.2、本续卷129.2的未决描述在131–135明确覆盖的同一native分支上由这些推导推进，其余原范围保留。

完整保持唯一原 $\Omega$、原 $E/D$、native、全词同一 $q,K,J$、parent/ready、中心经典与不等维块、全部实际准备及零／不等／次归一质量。Born只在正质量的实际完整菜单上归一；Hilbert表示、叠加及所有可取得原标签仍守原来源范围。CP需要同一整台实际箭头、真正相关联合及递归同源参考；完整仪器连环境全部成功／失败／记录／后口输出，Kraus、TP、更新、Lüders及实际忠实交换共同生成的张量仍需各自原前件。

全部合法顺序／自适应／并行历史、每个仍合法未来、细记录与真正分组遗忘、停止／拒绝／销毁、同数两侧及逆向真实返回均保留。CountRead无穷、正常性、指定前对偶、原域上的流、物理钟、Hamiltonian生成元定义域、能量、作用量及共同正 $\hbar$ 均未由辅助共轭或中央取向生产。原菜单返回障碍及其它来源条件不因原多项式运输关系而消失；这些条件与本节前件共同保持完整量子起源目标的原范围。

## 追加锚（本行以下为增补区）

## 137. 固定实际框架对任意原第二输入的奇块识别

**定义 137.1（同一原资料、固定框架与残差）。** 保持123.1、130.1的同一原
$(E,C,u,N,\mathcal P,S,D)$、准确锥、全部A1–A3、全部原P2和完整原PB。原
$E$仍可不完备，$D:E^2\to E$仍是同一个总映射；不加入可加、连续、可测、
单位平移、商下降、完成延拓、任意原轴存在或物理来源前件。固定一个实际
三轴

$$
h^2=e^2=u,\qquad h\circ e=0,\qquad j=D(h,e),
$$

并沿用134.2的辅助元 $Q=ihej\in Z(\mathcal A)$、$Q^*=Q$、$Q^2=u$。在整个
原 $E$ 上定义有限Jordan算子

$$
\widetilde T_h=[L_j,L_e],\qquad
P_h^-:=\tfrac12(I-U_h),\qquad
d_x:=D(h,x),\quad k_x:=h\circ x,\quad z_x:=P_h^-x,
$$

以及

$$
r_h(x):=d_x-\widetilde T_hx .
\tag{137.1}
$$

在 $V_h$ 上，$\widetilde T_h$ 就是100.1和133.1的 $T$；由
$je=iQh$ 及成熟的JC交换子恒等式，它在环境中也可写为

$$
\widetilde T_hx=\frac {i}{2}Q[h,x],
\tag{137.2}
$$

故它杀掉 $U_h=+1$ 的分量，并在 $V_h$ 上等于 $iQhx$。77.2在同一标量平方
片 $\operatorname{span}_{\mathbb R}\{u,h,e,j\}$ 中给出两个实际仿射锚的
放大形式：对任意实 $s,\alpha$，

$$
D(h,sp+\alpha(u+h))=sq,
\qquad (p,q)=(e,j)\ \text{或}\ (j,-e).
\tag{137.3}
$$

这里使用的是已付的标量平方片双线性，而不是一般的单位平移；式(137.3)不
把未知 $D$ 在一般 $E$ 上拆开。

**定理 137.2（R1：固定实际首轴的任意原输入投影）。** 在137.1的条件下，
对每个原 $x\in E$，

$$
\boxed{P_h^-D(h,x)=\widetilde T_hx},
\qquad
\boxed{U_hr_h(x)=r_h(x)} .
\tag{137.4}
$$

换言之，同一个实际旧值的 $h$-奇块由固定三轴完全确定；未确定的部分只能是
$h$-交换残差。若 $x\in V_h$，则133.1已经给 $r_h(x)=0$。

证明。固定 $x$，简写 $d=d_x,k=k_x,z=z_x,n=u+h$。对137.3的任一 $(p,q)$，
在完整原PB中取实际三元组

$$
(a,b,c)=(h,sp+\alpha n,x).
$$

其两个位移为 $\nu=sq-k$、$\omega=d+\alpha n$，所以两个外层原标签为

$$
\begin{aligned}
R_+&=s(p+q)+\alpha n-k,&S_+&=x+d+\alpha n,\\
R_-&=s(p-q)+\alpha n+k,&S_-&=x-d-\alpha n.
\end{aligned}
\tag{137.5}
$$

这四个标签均在原 $E$。利用 $p\circ q=0$、$n\circ q=q$、
$n\circ k-k-x=-z$，PB的右侧逐项化简为

$$
D(R_+,S_+)-D(R_-,S_-)
=-2\alpha(sq+z)+2s\,p\circ k-2x\circ d .
\tag{137.6}
$$

对两个外层旧值分别使用同一个数学正实读取 $\phi$ 的P2，并使用123.2的
$B_\phi$，再只对显式标量 $\alpha$ 取两侧的二次式主项，得到对所有实 $s$

$$
\begin{aligned}
2|\phi(sq+z)|\le{}&
\sqrt{B_\phi\bigl(n,x+k+d-s(p+q)\bigr)}\\
&+\sqrt{B_\phi\bigl(n,x+k-d+s(p-q)\bigr)}.
\end{aligned}
\tag{137.7}
$$

这一步没有对 $D$ 的值取极限：$d$ 固定在原域中，极限只作用于已知的
正实标量多项式系数。特别地，P2始终是两张原二表的同一读取预算。

现在在忠实含单位表示 $\mathcal A\subset B(H)$ 中工作。令

$$
H_\sigma=\{\xi:h\xi=-\xi,\ Q\xi=-\sigma\xi\},
\qquad \sigma\in\{1,-1\},
$$

并取非零 $\xi\in H_\sigma$、$\eta=j\xi$。若 $\phi_\delta$ 是向量
$(\xi+\delta\eta)/(1+\delta^2)^{1/2}$ 的正读取，则对每个固定自伴 $v$ 有精确式

$$
B_{\phi_\delta}(n,v)=
\frac{4\delta^2}{(1+\delta^2)^2}
\left(\|v\xi+\delta v\eta\|^2-
\bigl(\operatorname{Re}\langle\eta,v\xi\rangle
 +\delta\operatorname{Re}\langle\eta,v\eta\rangle\bigr)^2\right).
\tag{137.8}
$$

记 $P_\eta w=w-\operatorname{Re}\langle\eta,w\rangle\eta$。在137.7中先固定
$s$，约去 $2\delta/(1+\delta^2)$，令 $\delta\downarrow0$，得到

$$
\begin{aligned}
2\left|\operatorname{Re}\langle\eta,(sq+z)\xi\rangle\right|
\le{}&\left\|P_\eta\bigl((x+k+d-s(p+q))\xi\bigr)\right\|\\
&+\left\|P_\eta\bigl((x+k-d+s(p-q))\xi\bigr)\right\| .
\end{aligned}
\tag{137.9}
$$

先取 $(p,q)=(e,j)$。由 $e\xi=i\sigma\eta$、$j\xi=\eta$，两边在
$s\to+\infty$ 与 $s\to-\infty$ 的一次项均由固定向量范数给出；绝对值的两侧导数相夹，得到

$$
\begin{aligned}
w_+&:=P_\eta((x+k+d)\xi),&w_-&:=P_\eta((x+k-d)\xi),\\
P_\eta((e+j)\xi)&=i\sigma\eta,&P_\eta((e-j)\xi)&=i\sigma\eta,\\
\left.\frac{d}{ds}\right|_{+\infty}
\bigl(\|w_+-s i\sigma\eta\|+\|w_-+s i\sigma\eta\|\bigr)
&=\operatorname{Re}\langle-i\sigma\eta,w_+\rangle
 +\operatorname{Re}\langle i\sigma\eta,w_-\rangle
=-2\sigma\operatorname{Im}D_0 .
\end{aligned}
\tag{137.10a}
$$

$s\to+\infty$ 给出一个导数方向的界，而 $s\to-\infty$ 给出反向界；两侧
主斜率相同，故显示的一次系数必须相等。

$$
\operatorname{Re}A=-\sigma\operatorname{Im}D_0,
\qquad
A:=\langle\eta,z\xi\rangle,\quad D_0:=\langle\eta,d\xi\rangle .
\tag{137.10}
$$

同一计算使用第二锚 $(p,q)=(j,-e)$，其 $q\xi=-i\sigma\eta$，给出

$$
\operatorname{Re}D_0=\sigma\operatorname{Im}A.
\tag{137.11}
$$

故

$$
\langle j\xi,(d+i\sigma z)\xi\rangle=0
\qquad(\xi\in H_\sigma).
\tag{137.12}
$$

这里的顺序是先取显式 $\alpha$ 主项，再取固定向量态的 $\delta$ 极限，最后
取显式 $s$ 的两条尾部；没有缩放未知旧响应或给它添加连续性。

对137.12作普通复极化。由于 $Q$ 在整个 $\mathcal A$ 中中央，$d,z$ 没有
相反 $Q$ 扇区之间的块；而 $j$ 将 $H_\sigma$ 等距映到相应的 $h=+1$
扇区。若 $\mathsf p_\sigma$ 是 $H_\sigma$ 的投影，137.12等价于

$$
\mathsf p_\sigma j(d+i\sigma z)\mathsf p_\sigma=0.
\tag{137.13}
$$

用 $K_0=je=iQh$ 将其改写，就是
$P_h^-d\,\mathsf p_\sigma=\widetilde T_hz\,\mathsf p_\sigma$。两个
$\sigma$ 扇区的直和是整个 $h=-1$ 子空间；自伴性给出反向块，忠实性遂得
$P_h^-d=\widetilde T_hz=\widetilde T_hx$，最后一个等号由137.2及
$U_h$-偶分量上的消失性成立。于是137.4成立。空扇区和 $E=0$ 的情形均为
真空等式，不需选择向量。∎

## 138. R2：原生横向域中的交换子残差

**定理 138.1（R2：同一旧残差的原生共同交换子包含）。** 若 $x\in V_e$，置
$y=D(e,x)$。则 $y\in V_e$、$y^2=x^2$、$D(e,y)=-x$，并且

$$
\boxed{r_h(x)\in E\cap\{h,e,j\}'} .
\tag{138.1}
$$

因而对任意 $b,c\in V_e$，固定首轴的加性缺陷

$$
\delta_h(b,c):=D(h,b+c)-D(h,b)-D(h,c)
$$

满足

$$
\boxed{\delta_h(b,c)\in E\cap\{h,e,j\}'} .
\tag{138.2}
$$

证明。公共横向行133.1对实际框架 $(e,h,-j)$ 给出 $y\in V_e$ 及
$D(e,y)=-x$。在原PB中取

$$
(a,b,c)=\left(e,\frac{h-j}{2},\frac{x+y}{2}\right).
$$

其两份外层准确为 $(-j,y)$ 与 $(h,x)$；两份内平方相同且交叠为零，
故完整PB的右侧为零，得到

$$
D(-j,y)=D(h,x)=d_x.
\tag{138.3}
$$

对实际框架 $(-j,e,h)$ 使用137.4，并复用已付的三轴四元数表，得到

$$
P_j^-d_x=\widetilde T_{-j}y=\widetilde T_hx.
\tag{138.4}
$$

137.4本身给 $P_h^-d_x=\widetilde T_hx$。故 $r_h(x)$ 同时与 $h,j$
普通交换；又 $Q$ 中央且 $e=-iQhj$，它也与 $e$ 交换，证明138.1。由于
$\widetilde T_h$ 是已知线性Jordan算子，

$$
\delta_h(b,c)=r_h(b+c)-r_h(b)-r_h(c),
$$

所以138.2成立。这里没有把 $D(h,b+c)$ 拆成两项；PB只识别了同一个旧值
$D(-j,y)$。∎

## 139. R3：标量平方输入与两个实际演员的支撑律

**推论 139.1（R3：全标量平方第二输入）。** 若原 $x$ 满足

$$
x^2=\lambda u,\qquad \lambda\ge0,
$$

则

$$
\boxed{D(h,x)=\widetilde T_hx,\qquad r_h(x)=0.}
\tag{139.1}
$$

零输入、$\lambda=0$、非零输入与 $h$ 有非零交叠的情形全部包含在内。

证明。因 $h^2-x^2=(1-\lambda)u$，前卷18.1给
$h\circ D(h,x)=0$。于是 $d_x=P_h^-d_x$，137.4立即给139.1。没有除以
$x^2$，也没有选取谱根或补入原域外的标签。∎

**定理 139.2（两个实际框架的支撑敏感取向律）。** 设 $h$ 与 $a$ 是同一
环境中实际存在的两个单位平方演员，各自带有本文意义下的实际正交框架，并
记其中央取向为 $Q_h,Q_a$。则

$$
D(h,a)=\frac i2Q_h[h,a],\qquad
D(a,h)=-\frac i2Q_a[h,a],
$$

从原反对称性得到

$$
\boxed{(Q_h-Q_a)[h,a]=0},
\qquad
\boxed{\frac{u-Q_hQ_a}{2}\,[h,a]=0}.
\tag{139.2}
$$

第二式是中央支撑投影的说法；它不把 $[h,a]$ 可逆化，也不要求两个中央取向
在整个环境中相同。

证明。139.1分别应用于框架 $h$ 和 $a$，再用137.2的环境交换子表达式与
$D(a,h)=-D(h,a)$，即得两式。两中央自伴对合相乘仍为中央对合；将第一式
左乘 $Q_h$ 得第二式。∎

若 $f$ 是实际存在且与 $h$ 正交的伴轴，133–134已经支付其同一 $h$ 行所
继承的 $Q$ 相等关系。138.1在另一个实际框架上只能作用于该框架所给出的
$V_f$（及其明确的伴轴横向域）；只有当一个输入同时属于两份规定域时，
相应残差才可写成两个共同交换子的交。这里没有制造新的伴轴，也没有把有限
交提升为 $Z(X)$。

## 140. 供应对应、混合接缝与未支付的静态消费者

**定义 140.1（新增关系的归属与消费者）。** 137–139是
$\texttt{repo-derived}$ 的固定实际框架应用。137.2的成熟中间恒等式使用
van de Wetering，*Commutativity in Jordan Operator Algebras*，Proposition 3.2
及式(2)的JC算子交换子与环境交换对应；文献只供应该环境恒等式，不识别
未知原 $D$。本应用的实际来源如下：

| 新关系 | 直接使用的已付来源 | 新增的准确范围 |
| --- | --- | --- |
| 137.4 | 123.1–123.2、123.4、123.5、125.1、133.1–134.3、77.2 | 对一个实际 $h,e,j$，任意原 $x\in E$ 的同一旧输出奇块被识别为 $\widetilde T_hx$ |
| 138.1–138.2 | 133.1 的实际 $(e,h,-j)$ 行、完整PB及137.4 | $V_e$ 上的同一残差及其固定首轴缺陷落入实际三轴共同交换子 |
| 139.1 | 前卷18.1与137.4 | 全部 $x^2\in\mathbb R_{ge0}u$ 的第二输入零残差 |
| 139.2 | 两份已实际存在的框架、139.1及原反对称 | 两个实际演员交叠交换子的中央支撑律 |

137–139没有重新生产全局 $Q$ 中央性、全部 $V_h$ 的横向行或同一伴轴的
$Q$ 相等；这些由133–134直接供应。数学正读取、Hilbert向量、投影和显式
标量极限只用于验证同一原调用，不成为新的实际准备或新的 $D$ 输入。

**定义 140.2（精确的混合接缝缺口）。** 对任意原 $c,z$ 满足

$$
U_hc=c,\qquad z\in V_h,
$$

仍需证明

$$
\boxed{r_h(c+z)=r_h(c)},
\quad\text{即}\quad
\boxed{D(h,c+z)=D(h,c)+\widetilde T_hz}.
\tag{140.1}
$$

137.4只给 $r_h(c+z)$ 与 $h$ 交换；138.1只有在 $c+z\in V_e$ 时才给三轴
共同交换子，139.1只覆盖标量平方输入。一般 $c+z$ 的 $h$-交换部分与横向
部分之间仍没有一份实际PB/P2预算能消去未知的混合响应。特别不能把
$D(h,c)$ 当作零，也不能把 $D(h,c+z)$ 拆成两项。这个缺口保留了任意首
标签、无实际三轴的原域和全域旧 $D$ 的完整量词。

静态卷89.2–89.3要求对全部原 $a,b,c$，

$$
\delta_a(b,c)\in E\cap Z(X),
\quad\text{等价地}\quad
[L_{\delta_a(b,c)},L_x]y=0\quad(\forall x,y\in E).
$$

138.2只有 $E\cap\{h,e,j\}'$，这是一个由实际三轴决定的共同交换子，
一般严格大于全局中心。比如在标准全背景 $M_2(\mathbb C)\otimes
M_2(\mathbb C)$ 中取 $h=\sigma_z\otimes I$、$e=\sigma_x\otimes I$、
$j=-\sigma_y\otimes I$，其原生共同交换子含 $I\otimes\sigma_z$，而该元
不与 $I\otimes\sigma_x$ 交换；这个例子只排除“共同交换子即全局中心”的
偷换，不是否定标准响应中的零残差。因而138.2不能直接消费静态卷89。

静态卷94–98的条件消费者要求统一缺陷包络

$$
A(R)=\sup_{\|a\|,\|b\|,\|c\|\le R}\|\delta_a(b,c)\|=o(R).
$$

137–139没有给出这个全输入一致增长；逐份P2至多提供二次量级的
$A(R)\le4R^2$ 型上界，不能替换 $o(R)$。同样，原多项式卷36–40在标量
端点多项式域中已经支付全部无迹输入及共同符号，但其混合中心接头

$$
D(fu+A,gu+B)=D(A,B)
\tag{140.2}
$$

仍是该卷39.2的未决等式；139.1不能把这个域局部结论倒推为一般原域的
混合拼接。

完整保持唯一原 $\Omega$、原 $E/D$、native、全词同一 $q,K,J$、
parent/ready、中心经典与不等维块、全部实际准备及零／不等／次归一质量。
Born仍只在正质量的实际完整菜单上归一；Hilbert表示和中央取向不产生实际
准备。CP仍需同一整台实际箭头、真正相关联合及递归同源参考；完整仪器的
环境、成功／失败、记录、后口输出，Kraus、TP、更新、Lüders及实际忠实
交换共同生成的张量仍各守原前件。全部合法顺序、自适应、并行历史、每个
合法未来、真正分组遗忘、停止／拒绝／销毁、同数两侧和逆向真实返回仍在
量词内；CountRead、正常性、指定前对偶、原域流、物理钟、Hamiltonian
定义域、能量、作用量及共同正 $\hbar$ 均未由137–139生产。
## 追加锚（本行以下为增补区）
