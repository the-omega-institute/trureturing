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

## 137. 同一原三轴的有限系数域

**定义 137.1（原背景、系数与完成层）。** 完整保持130.1的同一原 $(E,C,u,N,\mathcal P,S,D)$、A1–A3、准确锥、全部原P2及完整原PB，并消费133.1–134.1。仍有 $E\subset X\subset\mathcal A_{\rm sa}$、$\overline E=X$、$\mathcal A=C^*(X)$；原 $E$ 可以不完备，$X$ 不要求等于 $\mathcal A_{\rm sa}$。固定同一实际原有向三轴

$$
s_1=h,\quad s_2=e,\quad s_3=j=D(h,e),\qquad
s_r^2=u,\quad s_r\circ s_t=0\ (r\ne t),
\tag{137.1}
$$

以及134.1的 $U_hU_eU_j=I_E$、$Q=i h e j\in Z(\mathcal A)$、$Q^*=Q$、$Q^2=u$。本节以后的方括号只指给定环境 $\mathcal A$ 的交换子，不是旧 $D$ 的定义。置

$$
\mathcal B_0=E_{+++}
=\{c\in E:[c,h]=[c,e]=[c,j]=0\},\qquad
Y=\overline{\mathcal B_0}^{\,X}.
\tag{137.2}
$$

$\mathcal B_0$ 的元素只与三根轴交换，彼此不要求交换，也不要求属于整个原域的中心。$s_rc$ 在下文表示原Jordan乘积 $s_r\circ c$；证明两者交换后，才在环境中写成普通乘积。$E=0$ 时取 $u=h=e=j=Q=0$，全部系数域、复化、完成与矩阵代数均为零；所有等式仍成立，无须非零态。非零矩阵单位的解释只用于 $E\ne0$。

**定理 137.2（整个原域的唯一有限四系数）。** 令

$$
\begin{aligned}
P_0&=\tfrac14(I+U_h+U_e+U_j),&
P_1&=\tfrac14(I+U_h-U_e-U_j),\\
P_2&=\tfrac14(I-U_h+U_e-U_j),&
P_3&=\tfrac14(I-U_h-U_e+U_j),\\
\kappa_0(a)&=P_0a,&
\kappa_r(a)&=s_r\circ P_ra\quad(1\le r\le3).
\end{aligned}
\tag{137.3}
$$

这里 $P_2$ 是有限投影的编号，不指原二表正性。每个原 $a\in E$ 唯一地写成

$$
\boxed{a=c_0+h c_1+e c_2+j c_3,\qquad c_r=\kappa_r(a)\in\mathcal B_0.}
\tag{137.4}
$$

$\mathcal B_0$ 是含单位实Jordan域，$P_r$ 与 $\kappa_r$ 都是保持原 $E$ 的有限实Jordan表达式，范数至多为一。完成层准确为

$$
Y=P_0X=X_{+++},\qquad
X=Y\oplus hY\oplus eY\oplus jY.
\tag{137.5}
$$

证明。零代数时各式直接成立，以下设 $E\ne0$。134.1给 $U_j=U_hU_e$。三个共轭对合对易，故(137.3)是四个角色投影，和为 $I$、两两乘积为零，像依次为 $E_{+++},E_{+--},E_{-+-},E_{--+}$。$P_0E=\mathcal B_0$；它的Jordan闭合来自三个 $U$ 都是原Jordan自同构。

若 $x\in P_rE$、$r>0$，则 $x$ 与 $s_r$ 交换。原 $c=s_r\circ x=s_rx$ 与三轴均交换：自身轴的符号为正，另两轴各从 $s_r$ 和 $x$ 得到一个负号。因此 $c\in\mathcal B_0$，且 $s_r\circ c=x$。反向，$c\in\mathcal B_0$ 时 $s_r\circ c\in P_rE$。对 $a=\sum_rP_ra$ 逐项使用这两个逆映射，得到(137.4)及唯一性。

每个 $U$ 是环境单位共轭，故为等距算子；$P_r$ 的四项平均给范数界一。$\|L_{s_r}\|\le\|s_r\|=1$，所以 $\|\kappa_r\|\le1$。这些有界投影与逆映射延至 $X$。$P_0E$ 在闭空间 $P_0X$ 中稠密，故 $Y=P_0X$，继而得到(137.5)。所有原输入只用了有限和及原Jordan运算，没有原根、原逆元或无限原分解。∎

## 138. 跨轴二元关系强迫内部有向闭合

**定义 138.1（内部系数有向差）。** 对原 $c,d\in\mathcal B_0$，定义有限原表达式

$$
\beta(c,d)=-j\circ\bigl((h\circ c)\circ(e\circ d)\bigr).
\tag{138.1}
$$

取 $\varepsilon_{123}=1$ 的三指标交替符号。对(137.4)中的原 $a=\sum_{r=0}^3s_rc_r$、$b=\sum_{r=0}^3s_rd_r$，此处仅以 $s_0c_0=c_0$ 作为记号，置

$$
\begin{aligned}
\gamma_0(a,b)&=\beta(c_0,d_0)+\sum_{r=1}^3\beta(c_r,d_r),\\
\gamma_k(a,b)&=\beta(c_0,d_k)+\beta(c_k,d_0)
+\sum_{r,t=1}^3\varepsilon_{rtk}(c_r\circ d_t),\\
B_\star(a,b)&=\gamma_0(a,b)+\sum_{k=1}^3s_k\circ\gamma_k(a,b).
\end{aligned}
\tag{138.2}
$$

$B_\star$ 是待由下述定理支付闭合与性质的规范候选；该符号不重命名旧 $D$。

**定理 138.2（非交换系数闭合及全部原二元乘积）。** 对全部原 $c,d\in\mathcal B_0$，

$$
\boxed{\beta(c,d)\in\mathcal B_0,\qquad
\beta(c,d)=\tfrac{iQ}{2}[c,d],\qquad
(h\circ c)\circ(e\circ d)=-j\circ\beta(c,d).}
\tag{138.3}
$$

因此(138.2)给保持整个原域的实交替双线性映射，并满足

$$
\boxed{B_\star:E^2\longrightarrow E,\qquad
B_\star(a,b)=\tfrac{iQ}{2}[a,b],\qquad
N(B_\star(a,b))\le N(a)N(b).}
\tag{138.4}
$$

原Jordan乘积也由同一系数准确决定：

$$
\begin{aligned}
a\circ b&=\eta_0+\sum_{k=1}^3s_k\circ\eta_k,\\
\eta_0&=c_0\circ d_0+\sum_{r=1}^3c_r\circ d_r,\\
\eta_k&=c_0\circ d_k+c_k\circ d_0
-\sum_{r,t=1}^3\varepsilon_{rtk}\beta(c_r,d_t).
\end{aligned}
\tag{138.5}
$$

这些公式仅由原 $S$ 及同一有向三轴决定，因而不依赖所选忠实JC实现；不以一般旧 $D$ 的任何双线性为前件。

证明。$hc\in E_{+--}$、$ed\in E_{-+-}$。因为每个 $U$ 保Jordan乘积，原 $y=(hc)\circ(ed)$ 位于 $E_{--+}$，故原 $-j\circ y$ 位于 $\mathcal B_0$。先由这个有限式支付返回原系数域，再在环境中计算：$c,d$ 与轴交换而 $eh=-he$，所以

$$
y=\tfrac12he(cd-dc),\qquad
he=-iQj,\qquad
-j\circ y=\tfrac{iQ}{2}[c,d].
\tag{138.6}
$$

对 $E_{--+}$ 施加两次 $L_j$ 为恒等，得到(138.3)的最后一式。右侧 $iQ[c,d]/2$ 自伴；这里未先假设任何环境交换子属于原域，也未将 $\beta(c,d)$ 认作旧 $D(c,d)$。

现在(138.2)的每个 $\gamma_k$ 已在 $\mathcal B_0$ 中，所以 $B_\star(a,b)\in E$。环境中三轴满足

$$
s_rs_t=-iQ\sum_k\varepsilon_{rtk}s_k\quad(r\ne t).
\tag{138.7}
$$

展开 $[a,b]$：零轴与自身轴项分别给 $[c_0,d_0]$、$[c_r,d_r]$；零轴与第 $k$ 轴项给 $s_k([c_0,d_k]+[c_k,d_0])$；异轴项为

$$
[s_rc_r,s_td_t]=2s_rs_t(c_r\circ d_t)\quad(r\ne t).
\tag{138.8}
$$

乘 $iQ/2$ 并用 $Q^2=u$，正好得到(138.2)。交替性由交换子身份给出，实双线性也已由原有限公式给出。$Q$ 为中央自伴酉元，$\|[a,b]\|\le2\|a\|\|b\|$，得到范数界。对Jordan乘积作相同展开，同轴项给 $c_r\circ d_r$，异轴项给

$$
(s_rc_r)\circ(s_td_t)
=\tfrac12s_rs_t[c_r,d_t]
=-\sum_k\varepsilon_{rtk}s_k\beta(c_r,d_t),
\tag{138.9}
$$

这证明(138.5)。全部中间输出都已在原域中。

任意保持单位、Jordan乘积及这三根标记轴的Jordan映射，都保持 $U,P,\kappa,\beta,\gamma$ 的有限表达式，所以也保持 $B_\star$。这正是相对于同一标记有向三轴的规范性，不声称所有轴选择已经给旧 $D$ 完成全域拼接。

反向检查时，若某对原系数的有向差不能返回 $\mathcal B_0$，则同一原二元关系 $y=(h\circ c)\circ(e\circ d)\in E_{--+}$ 与 $-j\circ y\in\mathcal B_0$ 不可能同时保留。若某对原 $a,b$ 的 $iQ[a,b]/2$ 不能返回 $E$，(138.2)的有限原重构将与这个环境身份矛盾。被击中的正是原跨轴Jordan闭合关系；这项反事实没有识别未知旧值 $D(a,b)$。∎

## 139. 保持原完成自伴部的结合复化

**定义 139.1（候选复乘法与原系数星代数）。** 在原复向量空间 $E_{\mathbb C}=E\oplus iE$ 上取 $`(a+ib)^*=a-ib`$，以

$$
a\star b=a\circ b-iB_\star(a,b)\qquad(a,b\in E)
\tag{139.1}
$$

作复双线性延拓。取 $\mathfrak b=\mathcal B_0\oplus i\mathcal B_0$，其同一乘法在实系数上为

$$
c\star d=c\circ d-i\beta(c,d).
\tag{139.2}
$$

记所得 $E_{\mathbb C}$ 的C*完成为 $\mathcal C$，$\mathfrak b$ 的C*完成为 $\mathcal B$；它们的存在、范数及所指的具体闭包由下一定理给出。$\mathcal C$、$\mathcal B$ 分别区别于原JC环境 $\mathcal A$ 与原锥 $C$。

**定理 139.2（内部有限闭合接到准确的完成层）。** 式(139.1)使 $E_{\mathbb C}$ 成为含单位pre-C*代数，$\mathfrak b$ 是其含单位星子代数。对 $z=a+ib$，其C*范数由原域内部给出：

$$
\boxed{\|a+ib\|_\star^2
=N\bigl(a^2+b^2+2B_\star(a,b)\bigr).}
\tag{139.3}
$$

它在自伴原域上就是 $N$。作为原环境中的复向量空间，两个完成准确为

$$
\begin{gathered}
\mathcal C=X+iX,\qquad \mathcal C_{\rm sa}=X,\qquad
\mathcal C_+=X\cap\mathcal A_+,\qquad C=E\cap\mathcal C_+,\\
\mathcal B=Y+iY\subset\mathcal C,\qquad
\mathcal B_{\rm sa}=Y,\qquad \mathfrak b_{\rm sa}=\mathcal B_0.
\end{gathered}
\tag{139.4}
$$

证明。仅在证明所用的原环境中定义

$$
z_+=\tfrac12(u+Q),\qquad z_-=\tfrac12(u-Q).
\tag{139.5}
$$

它们是 $\mathcal A$ 的中央正交投影，和为 $u$；不要求属于 $E,X$ 或 $\mathcal C$。由(138.4)，对原复化中的 $x,y$ 有

$$
x\star y=z_+xy+z_-yx.
\tag{139.6}
$$

在整个原环境向量空间上采用(139.6)，得到与

$$
z_+\mathcal A\ \oplus\ (z_-\mathcal A)^{\rm op}
\tag{139.7}
$$

相同的C*代数结构：第二部分只反转乘法次序，范数和伴随保持原样。中央正交性给结合律；两部分的C*范数均为原范数，直和范数仍为 $\mathcal A$ 的原范数。因此无需把 $z_\pm$ 作为原输入，就可使用这个辅助环境证明 $\star$ 结合且保星。

这一步是成熟的中央相反乘法构造。Najafi–Moslehian，[*Deformation of involution and multiplication in a C*-algebra*](https://arxiv.org/pdf/1304.8091)，Lemma 2.1及其证明给 $x\mathbin{\diamond}y=p x v y+(1-p)y v x$、$x^\#=v^*x^*v^*$；其中央投影 $p$ 取 $z_+$，酉参数 $v$ 取这里的单位 $u$，便是(139.6)–(139.7)。引用中的酉参数不是原三轴之一。这项成熟结果只承担辅助环境的C*性质，不承担原输出闭合或旧 $D$ 识别。

138.2已独立支付 $B_\star(E,E)\subset E$，故 $E_{\mathbb C}$ 在这个辅助环境中是含单位星子代数；(138.3)同样使 $\mathfrak b$ 星闭合。$E_{\mathbb C}$ 的范数闭包恰为 $X+iX$：一方面 $E$ 在 $X$ 稠密，另一方面实部、虚部连续且 $X$ 闭，所以 $X+iX$ 闭。同理 $\overline{\mathfrak b}=Y+iY$。这证明两个完成及其自伴部的身份。

相反C*代数与原代数具有相同的自伴正锥，中央直和也保持这个一级正锥；闭C*子代数继承环境正锥。因此 $\mathcal C_+=X\cap\mathcal A_+$，再用130.1得到原锥身份。直接在原复化中计算

$$
z^*\star z=a^2+b^2+2B_\star(a,b)\in E\cap\mathcal C_+=C.
\tag{139.8}
$$

C*恒等式给(139.3)，也表明此范数由原 $S,N$ 和标记三轴决定。非零原 $z$ 的 $z^*\star z$ 不为零，因为辅助环境的C*范数忠实；故这不是半范数。全程没有对旧 $D$ 取极限。原 $\mathfrak b,E_{\mathbb C}$ 不因此根闭合、逆闭合或完备；连续函数演算仅可在已构造的C*完成中使用。∎

## 140. 整个原域的准确二阶系数矩阵

**定理 140.1（原稠密域与完成层的同一矩阵坐标）。** 存在保单位、保星的C*同构 $\Phi:\mathcal C\to M_2(\mathcal B)$，限制为原星代数同构 $E_{\mathbb C}\to M_2(\mathfrak b)$ 及原Jordan、范数、一级序同构

$$
\boxed{E\ \cong\ H_2(\mathfrak b):=M_2(\mathfrak b)_{\rm sa}.}
\tag{140.1}
$$

对(137.4)的全部原 $a$，具体为

$$
\boxed{\Phi(a)=
\begin{pmatrix}
c_0+c_1&c_2+i c_3\\
c_2-i c_3&c_0-c_1
\end{pmatrix}.}
\tag{140.2}
$$

矩阵内系数用 $\mathfrak b$ 或 $\mathcal B$ 的 $\star$ 相乘；不将它们改成交换标量。准确保持的是

$$
\begin{gathered}
\Phi(u)=I_2,
\quad \Phi(h)=\sigma_z,\quad\Phi(e)=\sigma_x,
\quad\Phi(j)=-\sigma_y,\\
\Phi(a\circ b)=\tfrac12\bigl(\Phi(a)\Phi(b)+\Phi(b)\Phi(a)\bigr),\\
\Phi(B_\star(a,b))=\tfrac i2[\Phi(a),\Phi(b)],\\
N(a)=\|\Phi(a)\|,\qquad
\Phi(C)=H_2(\mathfrak b)\cap M_2(\mathcal B)_+.
\end{gathered}
\tag{140.3}
$$

证明。原轴在新乘法下满足 $h\star e=-ij$、$e\star j=-ih$、$j\star h=-ie$。在原复化中置

$$
f_{11}=\tfrac12(u+h),\quad f_{22}=\tfrac12(u-h),\quad
f_{12}=\tfrac12(e-ij),\quad f_{21}=\tfrac12(e+ij).
\tag{140.4}
$$

代入这些轴关系，得到

$$
f_{rs}^*=f_{sr},\qquad
f_{rs}\star f_{tv}=\delta_{st}f_{rv},\qquad
f_{11}+f_{22}=u.
\tag{140.5}
$$

这只是使用成熟矩阵单位的具体中间步骤。先准确识别系数与角：$\mathcal B$ 正是 $\mathcal C$ 内三轴的共同 $\star$-交换子代数。确实，(139.6)给 $[x,s_r]_\star=Q[x,s_r]$，$Q$ 在辅助环境中可逆；实虚部再用(137.5)得到共同交换域恰为 $Y+iY$。因此 $\mathcal B$ 与全部 $f_{rs}$ 交换。

系数到角的映射及其逆为

$$
\begin{aligned}
\iota:\mathcal B&\longrightarrow f_{11}\star\mathcal C\star f_{11},
&\iota(b)&=b\star f_{11},\\
\iota^{-1}(t)&=t+f_{21}\star t\star f_{12}.
\end{aligned}
\tag{140.6}
$$

对角内 $t$，右侧与四个矩阵单位交换，所以属于 $\mathcal B$；其乘 $f_{11}$ 正好返回 $t$。反向由(140.5)及 $b$ 与矩阵单位交换得到 $\iota^{-1}(\iota(b))=b$。两式保乘法与伴随，单位 $u$ 对应角单位 $f_{11}$。相同论证在原 $\mathfrak b$ 与 $f_{11}\star E_{\mathbb C}\star f_{11}$ 上成立。这一步不能把对角嵌入的系数直接当作角内元素而省略。

现在应用成熟的完整矩阵单位识别：Blackadar，[*Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*](https://www.bruceblackadar.com/Mathematics/Cycr.pdf)，II.9.4.3，给含单位C*代数中 $\sum_rf_{rr}=u$ 时的同构 $x\mapsto(f_{1r}\star x\star f_{s1})_{r,s}$，其值域是角代数上的二阶矩阵。再逐项施加(140.6)，得到

$$
\Phi(x)_{rs}=\iota^{-1}(f_{1r}\star x\star f_{s1}).
\tag{140.7}
$$

原域限制没有额外闭合要求：对任意 $(b_{rs})\in M_2(\mathfrak b)$，逆像是有限和 $\sum_{r,s}f_{r1}\star\iota(b_{rs})\star f_{1s}\in E_{\mathbb C}$。这同时证明原域限制的满射，而非只证明它稠密。把 $h,e,j$ 及共同交换系数代入(140.7)，正好得到(140.2)。完成层由同一公式给C*同构，因此自动等距并准确保正锥。

若矩阵在 $M_2(\mathfrak b)$ 中自伴，两个对角元属于 $\mathcal B_0$，上非对角元唯一为 $c_2+ic_3$、$c_2,c_3\in\mathcal B_0$；两个对角元的半和与半差给 $c_0,c_1$。所以其逆像准确属于原 $E$。这证明(140.1)，而不是只找出一个Pauli子窗。结合(139.4)得到(140.3)。$f_{11},f_{22}$ 是原Jordan投影，$f_{12},f_{21}$ 是原复化元素；这不赋予任何一个元素实际仪器、准备或可取得程序的身份。∎

## 141. 有限原词与候选三标签的直接消费者

**推论 141.1（同一原域的有限可逆性与候选全表）。** 对任意有限原 $a_1,\ldots,a_n\in E$，原环境的正反词对称和属于原域：

$$
\tfrac12(a_1\cdots a_n+a_n\cdots a_1)\in E.
\tag{141.1}
$$

候选 $B_\star$ 在全部原输入上满足

$$
\begin{aligned}
(a\circ b)\circ c-B_\star(B_\star(a,b),c)
&=a\circ(b\circ c)-B_\star(a,B_\star(b,c)),\\
B_\star(a,b\circ c)
&=B_\star(a,b)\circ c+b\circ B_\star(a,c),\\
\sum_{\rm cyc}B_\star(a,B_\star(b,c))&=0.
\end{aligned}
\tag{141.2}
$$

对每个原正评价 $\alpha$ 和任意有限原族，候选表准确为

$$
g^\star_\alpha(a,b)=\alpha(a\circ b)-i\alpha(B_\star(a,b)),\qquad
[g^\star_\alpha(a_r,a_s)]_{r,s=1}^n\succeq0.
\tag{141.3}
$$

因而也给候选三标签正性；这里全部响应名都是 $B_\star$，没有把候选R或候选正表记作旧 $D$ 的新支付。

证明。有限 $\star$-词 $w=a_1\star\cdots\star a_n$ 属于 $E_{\mathbb C}$，在证明环境中等于

$$
w=z_+a_1\cdots a_n+z_-a_n\cdots a_1.
\tag{141.4}
$$

于是 $`(w+w^*)/2`$ 正好等于(141.1)，并属于 $E_{\mathbb C}$ 的自伴部 $E$。这也使完成 $X$ 成为给定环境中的可逆JC代数；原 $E$ 只称具有该有限词性质的Jordan域，不要求完备，也不借一般可逆JC的分类逆命题。

对已构造的结合乘法取实部，得到(141.2)第一行；它就是将静态卷(23.1)中的响应全部换成 $B_\star$。结合代数交换子的导子律与Jacobi恒等式给另外两行。这些成熟后果的实际用途是：有限中间值已经由138.2返回同一原域，故这些身份确实是原域上的候选身份。

正评价满足 $|\alpha(a)|\le\alpha(u)N(a)$，所以唯一连续延至 $X$。若 $x\in X_+$，用 $a_m\in E$ 逼近 $x$，再加趋零的正实倍单位即可取原正逼近，故该延拓保持正性。复线性延拓为 $\widehat\alpha:\mathcal C\to\mathbb C$ 后，(139.4)使它正且保持质量 $\widehat\alpha(u)=\alpha(u)$。对 $W=\sum_r\lambda_ra_r\in E_{\mathbb C}$，有

$$
\sum_{r,s}\overline{\lambda_r}\lambda_sg^\star_\alpha(a_r,a_s)
=\widehat\alpha(W^*\star W)\ge0,
\qquad W^*\star W\in C.
\tag{141.5}
$$

零质量时原正评价为零，整表为零；没有归一。正泛函、有限Gram和交换子后果是成熟C*工具，这里的增量在于它们可消费整个原稠密域的内部有限闭合。它们不证明未知旧表 $[\alpha(a_r\circ a_s)-i\alpha(D(a_r,a_s))]$ 的三标签或更长正性。∎

## 142. 同一个旧总映射的精确矩阵运输

**定理 142.1（原P2、PB与未识别旧值的同域改坐标）。** 令 $\phi=\Phi|_E:E\to H_2(\mathfrak b)$。定义

$$
\begin{gathered}
\widetilde D(A,B)=\phi\bigl(D(\phi^{-1}A,\phi^{-1}B)\bigr),\qquad
\widetilde\alpha=\alpha\circ\phi^{-1},\\
A\circ_m B=\tfrac12(AB+BA),\qquad
\widetilde C=H_2(\mathfrak b)\cap M_2(\mathcal B)_+.
\end{gathered}
\tag{142.1}
$$

则 $\widetilde D$ 是定义在全部原矩阵域 $H_2(\mathfrak b)^2$ 上、值仍在该域中的同一个旧总映射的精确运输。全部原评价、质量、范数、A1–A3、原P2与完整原PB同时运输。其中原二表为

$$
\left[
\widetilde\alpha(A_r\circ_m A_s)
-i\widetilde\alpha(\widetilde D(A_r,A_s))
\right]_{r,s=1}^2\succeq0,
\tag{142.2}
$$

完整PB为：对全部 $A,B,T\in H_2(\mathfrak b)$，置

$$
\nu=\widetilde D(A,B)-A\circ_m T,\qquad
\omega=A\circ_m B+\widetilde D(A,T),
\tag{142.3}
$$

则

$$
\widetilde D(B+\nu,T+\omega)-\widetilde D(B-\nu,T-\omega)
=-2B\circ_m\nu-2T\circ_m\omega.
\tag{142.4}
$$

只在已经支付的三条原横向单位行上认回候选：

$$
\begin{gathered}
D(s_r,z)=B_\star(s_r,z)\quad(z\in V_{s_r},\ r=1,2,3),\\
\widetilde D(\phi(s_r),Z)=\tfrac i2[\phi(s_r),Z]
\quad(\phi(s_r)\circ_m Z=0).
\end{gathered}
\tag{142.5}
$$

证明。140.1给 $\phi$ 对原域的实线性双射、Jordan同构、等距与准确一级保锥，故(142.1)只改变每个原输入和输出的坐标。评价分离、准确锥和所有质量随双射保持。将原两标签代入(142.2)，每个复数项逐项等于原二表；A1–A3中的所有相加、零值、单位和同一个有理小窗口同样逐项保持。把原(123.5)整体施加 $\phi$，得到(142.3)–(142.4)。这里没有展开任何未知旧响应的和，也没有把 $\widetilde D$ 延到 $M_2(\mathcal B)_{\rm sa}$。

对 $r=1$，134.3与 $[h,z]=2hz$ 给(142.5)。将130.2的循环三元组 $(e,j,h)$、$(j,h,e)$ 分别代入已经完整成立的133.1–134.1，得到另两条横向行；循环置换的 $i s_1s_2s_3$ 仍是同一个 $Q$。再用(140.3)得到矩阵式。这里只消费这三条完整定理，不另假定125.1的循环中间结论。∎

**定义 142.2（下一原消费者与未证等式）。** 在同一原域定义

$$
\rho(a,b)=D(a,b)-B_\star(a,b)\in E,
\qquad
\widetilde\rho(A,B)=\widetilde D(A,B)-\tfrac i2[A,B].
\tag{142.6}
$$

由精确坐标运输有 $\widetilde\rho(\phi(a),\phi(b))=\phi(\rho(a,b))$，所以全原 $\rho=0$ 与全原矩阵域上 $\widetilde D(A,B)=i[A,B]/2$ 完全是同一个待证命题。定义残差不证明它为零，也不给残差双线性或连续性。例如，对原 $a=c_0+h c_1+z$、$z\in V_h$，(142.5)仍不能把未知 $D(h,a)$ 拆成三项；完整单位行、一般单位或中央平移、第一槽一般齐次、一般可加、商下降、未知输入连续性、函数演算输入及完成延拓均未由此取得。

前卷77.1–78.1已认回标量系数四维窗的同一旧乘法，直接复用其原范围，不作为此处新结论。对全域旧 $D$，静态卷32.2、23.1、33.2的P3、双线性、原R及同一旧结合乘法消费者仍取各自完整前件。141.1的候选有限Gram与候选R不替它们支付任何旧表前件；这里也没有构造满足全部原P2/PB而 $\rho\ne0$ 的反模型。新的真实消费者是将同一个旧问题及其全部原二元、三元关系准确放到 $H_2(\mathfrak b)$ 上，不是另选辅助响应替换原目标。

## 143. 原环境、矩阵序与三轴分支的准确范围

**定义 143.1（三层对象与一级序）。** 原系数星代数 $\mathfrak b$ 可以无限维、非交换、不完备；$\mathcal B$ 是它的数学C*完成。$\mathcal A=C^*(X)$ 用原JC环境的乘法生成，$\mathcal C=X+iX$ 用由三轴确定的 $\star$ 相乘。它们不得默认相等。$\Phi:\mathcal C\to M_2(\mathcal B)$ 作为C*同构完全等距且完全保正；但从 $\mathcal C$ 到原 $\mathcal A$ 的相同向量包含，只在自伴部保证140.3的原范数和一级正锥，未保证原环境继承的全部矩阵序或CP。

原环境也可用成熟矩阵单位识别为二阶矩阵，但其系数与乘法不同：置 $\mathcal R=\{r\in\mathcal A:[r,h]=[r,e]=0\}$，其矩阵单位为

$$
t_{11}=\tfrac12(u+h),\quad t_{22}=\tfrac12(u-h),\quad
t_{12}=\tfrac12(e-iQj),\quad t_{21}=\tfrac12(e+iQj).
\tag{143.1}
$$

在原环境乘法下代入轴关系即得完整矩阵单位，且 $\mathcal R$ 是其共同交换域；系数到角仍需(140.6)同形的识别。因此 Blackadar II.9.4.3给 $\mathcal A\cong M_2(\mathcal R)$。这里的 $t_{12},t_{21}$ 未必属于 $E_{\mathbb C}$，$\mathcal R$ 的原乘法不能替代 $\mathcal B$ 的 $\star$，所以这个成熟环境分解不承担140.1的原域结论。

**命题 143.2（原环境可严格大于保持原自伴部的新完成）。** 存在满足137.1背景的原域，使 $Q,z_\pm$ 不属于 $\mathcal C$，且相同向量包含 $\mathcal C\subset\mathcal A$ 不保持矩阵正性。

证明。只为显示这些边界，取

$$
E=X=\{(x,x^{\mathsf T}):x\in M_2(\mathbb C)_{\rm sa}\}
\subset M_2(\mathbb C)\oplus M_2(\mathbb C),
\tag{143.2}
$$

单位、Jordan乘法、范数、锥和全部正评价均从第一坐标运输，旧响应取同一图上的标准响应

$$
D\bigl((x,x^{\mathsf T}),(y,y^{\mathsf T})\bigr)
=\bigl(i[x,y]/2,(i[x,y]/2)^{\mathsf T}\bigr).
\tag{143.3}
$$

它是标准二阶C*模型的原Jordan、旧响应同构，故全部原P2/PB成立；标准模型的这些关系直接复用前卷29.2所引任意C*乘法身份。取 $h=(\sigma_z,\sigma_z)$、$e=(\sigma_x,\sigma_x)$、$j=(-\sigma_y,\sigma_y)$。直接相乘得到

$$
Q=(I,-I),\quad z_+=(I,0),\quad z_-=(0,I),\qquad
\mathcal A=C^*(X)=M_2(\mathbb C)\oplus M_2(\mathbb C).
\tag{143.4}
$$

最后一个身份也可直接看出：$Q$ 属于生成代数，两个中央投影分别切出整个两份全矩阵。另一方面，

$$
\mathcal C=X+iX=\{(z,z^{\mathsf T}):z\in M_2(\mathbb C)\}
\tag{143.5}
$$

按(139.6)相乘，等于一份 $M_2(\mathbb C)$；它不含(143.4)的三个取向元素。第一坐标到原环境的向量包含是 $z\mapsto(z,z^{\mathsf T})$。其第二腿转置在一级上保正，但在二阶矩阵上，正元 $\sum_{r,s=1}^2E_{rs}\otimes E_{rs}=|\Omega\rangle\langle\Omega|$、$\Omega=e_1\otimes e_1+e_2\otimes e_2$，被送到翻转算子 $\sum_{r,s}E_{rs}\otimes E_{sr}$。它在 $e_1\otimes e_2-e_2\otimes e_1$ 上的本征值为 $-1$，故不保正。这是成熟转置现象在所构造两层环境上的应用，不把该例另立为新的标准矩阵理论，也不把数学矩阵正元当作实际相关准备。∎

**定义 143.3（完成闭合与全局轴的条件范围）。** 前卷29.2的原自伴多项式模型直接给 $\mathfrak b$ 不要求根闭合或逆闭合的实例：取常值Pauli三轴，其系数原域仍是相应多项式星代数；原域没有一般谱根。原 $1+t^2$ 在完成中可逆，但其逆不在原多项式域：若 $(1+t^2)p(t)=1$ 在区间成立，则为多项式恒等式，比较最高次系数即矛盾。数学完成中的平方根、逆元、谱投影与极限不自动成为原 $E$ 的可调用输入。$Q,z_\pm$ 尤其不取得原标签、仪器或实际中央分支身份。

二阶表示没有把整个原域压成四个实数；四个系数本身可无限维且彼此不交换。因此除非再有相应交换与标量前件，不能把它称作普通Bloch球，也不表示物理三空间。若这个三轴分支的 $\mathcal C$ 恰为有限维，则 $\mathcal B$ 的有限维C*分块使其简单复块为 $M_{2n_r}(\mathbb C)$，$n_r$ 可不同。故全单位三轴本来就不兼容该分支中的非零一维经典块或奇数满矩阵块。完整原目标仍包括没有这份全单位三轴的无轴、经典、奇数矩阵及其它域；这些域不能因本分支的坐标定理而被删除。不同块、不同轴和一般原响应的识别仍各取实际前件。

## 144. 原关系的增量与更短几何

**定义 144.1（承重对应与数学归属）。** 137–142的综合归为 $\texttt{repo-derived}$：消费同一原三轴已迫的四偶扇区，再由(138.1)把跨轴二元Jordan关系转成内部系数有向差，供整个原域的有限候选闭合，继而精确给原稠密矩阵域及保持 $X$ 的定向C*完成。矩阵单位、相反代数、C*完成、正泛函及有限Gram是成熟中间工具，承重处分别采用139.2及140.1所引的准确文献条件；不调用通常需要更高秩前件的Jordan协调化分类，也不以普遍C*包络的自伴部替换原 $X$。不宣称历史原创或文献穷尽。

前卷18.1的面积、77.1–78.1的标量四维窗、29.2的指定 $M_2(B)$ 多项式模型、本续卷131–134的消失与原横向行均是已有供应。它们不等于从当前整个原域推出 $E_{\mathbb C}=M_2(\mathfrak b)$ 的内部闭合链。静态卷14.1、23.1、32.2、33.2的同一旧乘法后端仍各有原R、P3或旧双线性前件，也未被倒用来构造本候选。

二元关系所保留的不只是各系数自己的对称乘积：把 $c,d$ 分别放到 $h,e$ 两条轴上，轴的反交换使其系数先后差在原Jordan乘积中显露；第三轴 $j$ 再把这份差读回 $\mathcal B_0$。这是有限三向提升，不是在物理空间添加方向，也不是把原三标签正性无条件支付给旧 $D$。式(138.3)、(138.5)说明内部定义不能任意互相独立：改动系数有向差而保留原混合Jordan二元关系，会直接破坏这些等式。141.3的三标签与全部有限表只属于这个已构造候选。

几何简化准确地是 $E=H_2(\mathfrak b)$、$X=M_2(\mathcal B)_{\rm sa}$ 的坐标描述，连同142.1对同一个旧 $D$ 的运输。没有把候选响应当成旧响应，没有证明完整A1–A3/P2/PB的独立信息减少，也没有给全局最少公理数。原候选与原完成判据保持；下一份实际数学缺口仍是142.2的全原旧值识别。

## 145. 七项原量子消费者的完整条件接口

**定义 145.1（复Hilbert载体、可观测量与叠加）。** 139–140给原Jordan域的保单位、原范数和一级原锥的复C*几何，故可用成熟忠实Hilbert表示表示 $\mathcal C\cong M_2(\mathcal B)$。要把该结合表示认作同一原响应的共同乘法，仍须全域 $D=B_\star$，或另已支付静态卷32.2、23.1所需的旧双线性、P3及完整PB等原入口。唯一原 $\Omega$、具名且可取得的原标签、跨评价配对、native、全词同一 $q,K,J$、parent/ready、合法控制及实际相干叠加准备，完整取静态卷8.3–8.4、14.2、25.1与三标签卷8.2–8.5、80.1的来源合同；数学表示不产生全 $B(H)$ 满射或任意控制。

**定义 145.2（正评价、效果、质量与Born）。** 141.1保质量延拓每份原正评价，140.3保原效果区间 $E\cap[0,u]$。只在同一个实际完整菜单及 $m_\alpha=\alpha(u)>0$ 时使用 $p_\alpha(e)=\alpha(e)/m_\alpha$；零、不等、次归一质量、原 $q$、中心经典混合、不等维块与静默部分按原范围保留。数学所有态和效果不等于实际准备或菜单齐备。静态卷25.1第二行所保留的原准备、事件接受归属、共同根、抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度尺度、P9分支及独立 $W_e$、完整菜单、固定支持全质量与全部原中间切口，均不由矩阵坐标生成；一般无限维系数域没有被改成有限密度矩阵表。

**定义 145.3（native、真正相关联合与张量）。** $M_2(\mathcal B)$ 是同一单域的数学因子描述，不制造实际二元参考或复合。全词同一 $K/J$、交叉零和生成分离仍需原来源；张量接线仍需同一个实际非零联合、忠实同向交换的两腿、联合生成、所需重数，以及全部相关输入、中心对、经典和不等维块。其量词准确沿静态卷25.1第三行、53.1及单位桥95.2、116.1；分别可达的两腿、相同边缘或一个数学张量表示不替代共同实现。系数非交换也不自动给它物理子系统身份。

**定义 145.4（CP与整台递归同源参考）。** 原未归一回溯 $\alpha_A(\beta_rb)=\alpha_B^r(b)$、typed前接及合法后口、全未来自然性、反变合法复合、typed分区和箭头商下降均取原合同。要使用原CP接口，实际箭头须连环境及全部成功、失败、细记录、后口输出，系统腿与二元参考腿须共同真支持且忠实同向交换；三实际投影与各自支持内补、全部相关正输入上的intertwining及夹界、每个有限递归深度与累计支持的准确运输均保留。静态卷25.1第四行及原整台参考消费者的这些前件不由静态 $M_2(\mathcal B)$ 或141.3候选Gram支付；143.2也排除了把一级原序保持直接升级为原环境CP的推断。支持内补仍不是环境补。

**定义 145.5（完整仪器、Kraus、更新、TP与Lüders）。** 原Jordan二次夹心仍是有限表达式 $\mathcal U_a(b)=2a\circ(a\circ b)-a^2\circ b$；在候选结合乘法中它等于 $a\star b\star a$。这只给数学入口。静态卷25.1第五行所需的全部原输入运输、完整typed输出菜单、环境、成功失败、细记录、接受端、真正分组遗忘、AC、精确 $N_u$、X/Xs、平方根词及其原接受条件全部保留。TP需要完整单位分区，Lüders需要同一完整输出的像内射线校准；仅正质量分支归一，零分支和合法未来不删除。有限密度、迹和算子Kraus公式只在原有限全矩阵域或已供应所需正规表示与指定前对偶并确实适用的域消费。数学完成里的根不供应原平方根词或接受端。

**定义 145.6（全部历史、未来、遗忘与真实返回）。** 原合法顺序、自适应、并行历史，每个仍合法未来，环境与全部细记录、真正分组遗忘、停止、拒绝、销毁、泄漏、同数两侧及逆向真实返回，均保留静态卷8.4、25.1第六行和单位桥原消费者的全部量词。CountRead绑定读后同一原完整活动输入及全未来返回；负提升两条活路的分别控制与相干聚合、具名分析词到实际菜单均须原生构造。原 $B$ 的精确正生成与另名 $B_{\rm cl}$ 的闭正生成不混同，这两个来源条件也不是此处系数代数 $\mathcal B$。可数可加、非离散记录、无限历史、正常性和指定前对偶不由范数完成产生；相同矩阵而不同原程序、原读取顺序、原 $q$-零集和AC方向仍保持。

**定义 145.7（动力、物理钟与共同尺度）。** 候选 $B_\star$ 可给数学有界内导子，但若要使用旧响应公式 $\dot b=2D(H,b)/\hbar$，仍须认回同一个旧 $D$ 并供应原流保持原域、实际相位和门序列、可逆一参数群、物理钟、所需强连续酉实现与生成元定义域、Hamiltonian的能量解释、作用量及共同正 $\hbar$。静态卷25.1第七行中的原 $\sigma,t_0$、共同仪器、固定 $d$、固定域、resolvent与 $3s+r\le1$ 预算均守原量词。矩阵单位、$Q$、谱、数学指数及完成不产生这些物理来源；一般无界生成元不被有界候选导子替代。

## 146. 四系数几何与旧关系的完整白话

**定义 146.1（有限坐标、内部闭合与原缺口的白话含义）。** 三根已经由同一原响应选定的轴，给每个原对象盖上三个正反记号。134.1只允许四种偶记号，因此每个原对象都能有限、唯一地拆成四份。第一份本来就与三轴交换；把另外三份各乘回相应轴，它们也都成为与三轴交换的系数。这里的“系数”不是四个实数：它们可以各有无限多自由度，并且彼此不交换。

关键在于，原来的对称二元关系没有丢掉系数的先后差。把一份系数放到 $h$ 轴上，另一份放到 $e$ 轴上，再作原Jordan组合；轴自身的反交换会把系数的先后差留下来。第三轴 $j$ 把它读回原系数域。这一步给出的是有限原公式，所以不需要先向原域加入根、逆、谱切片或极限。它把四个分量接成了整个带系数二阶复矩阵域；只说“像一个三维球”会漏掉系数自身的非交换关系。

由此，每个原对象和全部原对称二元关系都在一张准确矩阵坐标表里。补上数学极限以后得到真正的二阶矩阵C*代数，但原对象仍准确占原来的稠密矩阵域。原JC环境可以同时容纳正反取向，新的乘法按同一有向三轴协调这两部分；环境的取向投影甚至可以不在新完成里，更不是原可调用标签。保持一级正锥也不等于保持原环境所有矩阵层的正性，更不等于实际复合或CP已经存在。

这张几何表强迫了一份规范候选有向关系，却没有替换旧 $D$。三条已经认回的横向单位行确实与候选一致；一般带交换分量、带单位分量或任意两输入的旧值仍要用原P2/PB继续认回。现在可以把同一个旧总映射连同原评价、P2及PB完整搬到同一个原矩阵域上继续研究，而不能用候选正表或候选换括号式代付旧表。若候选不能内部闭合，原跨轴Jordan关系就会直接矛盾；若旧 $D$ 还没有被认回，矩阵图景的简洁也不会使这个缺口自行消失。

这里缩短的是整个Jordan域的几何描述，没有减少已经声明的独立原公理数，没有把数学三轴说成物理三空间，也没有删掉完整目标中无轴、经典、奇数矩阵等其它原域。Born的实际菜单、整台仪器、真正相关联合和参考、全部历史未来与真实返回、物理时钟、能量及共同尺度，都仍要来自同一个原世界；数学完成和坐标不能替世界供应它们。

## 追加锚（本行以下为增补区）

## 147. 任意原混合输入与同一旧输出的两个投影

**定义 147.1（完整原前件与固定行）。** 本节及以下各节完整保持130.1、137.1的同一原 $(E,C,u,N,\mathcal P,S,D)$、A1–A3、准确锥、全部原P2及完整原PB。仍有同一忠实含单位JC包含

$$
E\subset X\subset\mathcal A_{\rm sa},\qquad
\overline E=X,\qquad\mathcal A=C^*(X).
\tag{147.1}
$$

原 $E$ 可以不完备，不要求 $X=\mathcal A_{\rm sa}$；旧 $D:E^2\to E$ 不预付一般齐次、可加、连续、商下降、输入函数演算或完成延拓。固定同一实际原 $h,e,j=D(h,e)$，消费133.1–134.1的全部原横向行、三轴循环及辅助中央取向

$$
\begin{gathered}
h^2=e^2=j^2=u,\qquad h\circ e=h\circ j=e\circ j=0,\\
Q=i h e j\in Z(\mathcal A),\qquad Q^*=Q,\quad Q^2=u,\\
T=[L_j,L_e],\qquad D(h,v)=Tv=iQhv\quad(v\in V_h),
\qquad T^2v=-v.
\end{gathered}
\tag{147.2}
$$

这里 $L_a z=a\circ z$、$V_h=\{v\in E:h\circ v=0\}$。$Q$ 不要求属于 $E$ 或 $X$。令

$$
\begin{gathered}
U_h=2L_h^2-I,\qquad
P_{\rm tr}=\tfrac12(I-U_h),\qquad
P_{\rm com}=\tfrac12(I+U_h),\\
\operatorname{Com}_h=\{c\in E:hc=ch\}=P_{\rm com}E.
\end{gathered}
\tag{147.3}
$$

这些都是保持原域的有限Jordan表达式。对每个任意原 $x\in E$，以下始终固定

$$
\begin{gathered}
c=P_{\rm com}x,\qquad v=P_{\rm tr}x,\qquad
x=c+v,\quad hc=ch,\quad hv=-vh,\\
k=h\circ x=h\circ c=hc\in E,\qquad
g=D(h,x)\in E,\qquad n=u+h.
\end{gathered}
\tag{147.4}
$$

特别没有假定 $g\in V_h$；$g$ 的两个 $h$-交换对角块全程保留。环境乘法、Hilbert向量和谱压缩只供证明，不增加旧 $D$ 的可调用输入。零原域的全部等式为零，以下非零向量读取仅用于非零表示空间。

**定义 147.2（两份实际锚与同一读取）。** 只取两种已存在的实际原锚

$$
(p,q)=(e,j)\quad\hbox{或}\quad(p,q)=(j,-e).
\tag{147.5}
$$

前卷77.1在同一标量四维窗中准确给出，对所有实 $t,\alpha$，

$$
D(h,tp+\alpha n)=tq,\qquad
h\circ(tp+\alpha n)=\alpha n,\qquad p\circ q=0.
\tag{147.6}
$$

这里只使用已经认回的原窗，不向一般 $x$ 加单位后拆分未知旧值。对同一个数学正实读取 $\phi$，沿用123.2

$$
B_\phi(a,b)=\phi(a^2)\phi(b^2)-\phi(a\circ b)^2,
\qquad |\phi D(a,b)|\le\sqrt{B_\phi(a,b)}.
\tag{147.7}
$$

由16.2及123.2的准确锥接口，环境数学向量态可以如此读取每张原P2；它不必是实际准备。每次两张P2共用同一 $\phi$，不把 $|\phi D|^2$ 换成 $\phi(D^2)$。

## 148. 任意混合旧值的实际配平与完整 Gram 预算

**定理 148.1（保留全部输出块的共享预算）。** 对147.4的任意固定原 $x,g$、147.5的任一实际锚、每个实 $t$ 及同一个数学正读取 $\phi$，令

$$
W_+=x+k+g-t(p+q),\qquad
W_-=x+k-g+t(p-q).
\tag{148.1}
$$

则

$$
\boxed{2|\phi(tq+v)|\le
\sqrt{B_\phi(n,W_+)}+\sqrt{B_\phi(n,W_-)}.}
\tag{148.2}
$$

$W_\pm$ 可以含任意 $h$-交换分量，不预付它们横向。

证明。对全部有限实 $t,\alpha$，只调用同一个原PB三元组

$$
(a,b,z)=(h,tp+\alpha n,x).
\tag{148.3}
$$

两份内层原响应由(147.4)、(147.6)准确为 $tq,g$；相应位移及两份完整外层原输入为

$$
\begin{aligned}
\nu&=tq-k,&\omega&=\alpha n+g,\\
R_+&=t(p+q)-k+\alpha n,&S_+&=x+g+\alpha n,\\
R_-&=t(p-q)+k+\alpha n,&S_-&=x-g-\alpha n.
\end{aligned}
\tag{148.4}
$$

每个标签都在原 $E$。由于 $n\circ q=q$，且

$$
n\circ k=c+hc,\qquad n\circ x=c+hc+v,
\qquad n\circ k-n\circ x=-v,
\tag{148.5}
$$

原PB的右端完整展开为

$$
\begin{aligned}
D(R_+,S_+)-D(R_-,S_-)
&=-2(tp+\alpha n)\circ(tq-k)-2x\circ(\alpha n+g)\\
&=2t\,p\circ k-2x\circ g-2\alpha(tq+v).
\end{aligned}
\tag{148.6}
$$

$2t\,p\circ k$ 与 $-2x\circ g$ 都保留；任何一般交换性或输出横向性都未用来删项。对两个未知完整外值分别施加同一个 $\phi$ 的原P2，再作标量三角不等式，得到

$$
\left|\phi(2t\,p\circ k-2x\circ g)-2\alpha\phi(tq+v)\right|
\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{148.7}
$$

为准确处理大 $\alpha$，对任意固定原自伴 $A,B,n$ 和 $s\in\{1,-1\}$，已知实Jordan乘法的双线性给

$$
\begin{aligned}
B_\phi(A+\alpha n,B+s\alpha n)
&=B_\phi(A,B)+2\alpha C_s(A,B;n)
+\alpha^2B_\phi(n,B-sA),\\
C_s(A,B;n)
&=s\phi(A^2)\phi(n\circ B)+\phi(n\circ A)\phi(B^2)\\
&\quad-\phi(A\circ B)\{\phi(n\circ B)+s\phi(n\circ A)\}.
\end{aligned}
\tag{148.8}
$$

确实，三份已知读取分别展开为

$$
\begin{aligned}
\phi((A+\alpha n)^2)&=\phi(A^2)+2\alpha\phi(n\circ A)+\alpha^2\phi(n^2),\\
\phi((B+s\alpha n)^2)&=\phi(B^2)+2s\alpha\phi(n\circ B)+\alpha^2\phi(n^2),\\
\phi((A+\alpha n)\circ(B+s\alpha n))
&=\phi(A\circ B)+\alpha\{\phi(n\circ B)+s\phi(n\circ A)\}
+s\alpha^2\phi(n^2).
\end{aligned}
\tag{148.9}
$$

在前两式乘积减第三式平方中，四次、三次项各自相消；二次项为

$$
\phi(n^2)\phi((B-sA)^2)-\phi(n\circ(B-sA))^2,
$$

即(148.8)所写的Gram行列式。正外层取 $A=t(p+q)-k,B=x+g,s=1$；负外层取 $A=t(p-q)+k,B=x-g,s=-1$，故二次系数准确是 $B_\phi(n,W_+)$ 与 $B_\phi(n,W_-)$。

把(148.7)除以 $|\alpha|$，只在这些显式标量二次式中令 $|\alpha|\to\infty$，得到(148.2)。二次系数为零时，除后的相应根号仍趋于零，未丢退化情形。两份未知外值在每个有限 $\alpha$ 已由原P2逐份上界，不存在 $D$ 的输入极限或未知输出连续性前件。∎

## 149. 不假定横向的向量态预算

**定理 149.1（全部对角块保留时的精确向量恒等式）。** 在 $\mathcal A$ 的忠实含单位Hilbert表示中，内积第一槽共轭线性。固定 $\sigma\in\{1,-1\}$，取任意单位向量

$$
\xi\in H_{\sigma,-}:=\{\xi:Q\xi=\sigma\xi,\ h\xi=-\xi\},
\qquad \eta=q\xi,
\tag{149.1}
$$

其中 $(p,q)$ 是147.5的任一锚；空空间无需取向量。对 $\delta>0$，令 $\phi_\delta$ 为单位向量 $(\xi+\delta\eta)/\sqrt{1+\delta^2}$ 的数学向量态，并令

$$
\mathfrak p_\eta w=w-\operatorname{Re}\langle\eta,w\rangle\eta.
\tag{149.2}
$$

它是底层实Hilbert空间中去掉实方向 $\eta$ 的正交投影。对每个任意固定自伴 $W\in E$，无须 $W\in V_h$，均有

$$
\boxed{B_{\phi_\delta}(n,W)
=\frac{4\delta^2}{(1+\delta^2)^2}
\left\|\mathfrak p_\eta(W\xi+\delta W\eta)\right\|^2.}
\tag{149.3}
$$

因此148.2推出，对全部实 $t$，

$$
\boxed{
2\left|t+\operatorname{Re}\langle\eta,v\xi\rangle\right|
\le
\left\|\mathfrak p_\eta((v+g)\xi)-t p\xi\right\|
+\left\|\mathfrak p_\eta((v-g)\xi)+t p\xi\right\|.}
\tag{149.4}
$$

证明。两份锚都满足 $qp=je=iQh$，所以

$$
\|\eta\|=1,\qquad h\eta=\eta,\quad Q\eta=\sigma\eta,
\qquad p\xi=-i\sigma\eta.
\tag{149.5}
$$

这里 $Q$ 中央，故 $p,q$ 和所有固定原元素都保持其两个谱子空间。$h$ 自伴使 $\xi\perp\eta$；又 $n\xi=0,n\eta=2\eta,n^2=2n$。直接读取固定 $W$ 得

$$
\begin{aligned}
\phi_\delta(n^2)&=\frac{4\delta^2}{1+\delta^2},\\
\phi_\delta(W^2)&=\frac{\|W\xi+\delta W\eta\|^2}{1+\delta^2},\\
\phi_\delta(n\circ W)
&=\frac{2\delta}{1+\delta^2}
\operatorname{Re}\langle\eta,W\xi+\delta W\eta\rangle.
\end{aligned}
\tag{149.6}
$$

最后一式使用 $W=W^*$，故 $\langle\eta,W\eta\rangle$ 为实数。代入Gram行列式，正好是去掉一个实正交分量后的范数平方，得到(149.3)。这些公式没有删除 $W$ 的任何对角作用。

$tq+v\in V_h$，其两份对角读取为零，所以

$$
\phi_\delta(tq+v)=\frac{2\delta}{1+\delta^2}
\left(t+\operatorname{Re}\langle\eta,v\xi\rangle\right).
\tag{149.7}
$$

将(149.3)分别用于148.2的完整 $W_+,W_-$，将(149.7)用于左侧，约去共同正因子 $2\delta/(1+\delta^2)$，得

$$
2\left|t+\operatorname{Re}\langle\eta,v\xi\rangle\right|
\le\sum_{s\in\{+,-\}}
\left\|\mathfrak p_\eta(W_s\xi+\delta W_s\eta)\right\|.
\tag{149.8}
$$

现在只对固定向量范数令 $\delta\downarrow0$。由 $x+k=nc+v$、$c$ 与 $h$ 交换及 $n\xi=0$，有 $(x+k)\xi=v\xi$。又 $q\xi=\eta$、$p\xi=-i\sigma\eta$，所以

$$
\mathfrak p_\eta(q\xi)=0,\qquad
\mathfrak p_\eta(p\xi)=p\xi.
\tag{149.9}
$$

两份极限向量准确是(149.4)右侧。$g$ 自始至终是固定的完整旧值；其 $h$-交换分量仍在 $(v\pm g)\xi$ 中。全部极限只读取已固定元素，不曾令 $D$ 的输入收敛。∎

## 150. 正反大锚及两锚复极化锁住同一非对角块

**定理 150.1（任意原混合输入的横向旧输出）。** 对147.1背景下每个原 $x\in E$，同一个旧总映射满足

$$
\boxed{P_{\rm tr}D(h,x)=T P_{\rm tr}x=iQh P_{\rm tr}x.}
\tag{150.1}
$$

不要求 $x$ 的平方、任一系数平方或混合Gram为标量、中央、可逆或有限谱。

证明。固定149.1的 $\sigma,\xi$ 及任一实际锚。记实数和固定向量

$$
a=\operatorname{Re}\langle\eta,v\xi\rangle,\qquad
w=p\xi,\qquad z_\pm=\mathfrak p_\eta((v\pm g)\xi),\qquad
b=\operatorname{Re}\langle w,g\xi\rangle.
\tag{150.2}
$$

$\|w\|=1$ 且 $\operatorname{Re}\langle\eta,w\rangle=0$。成熟的Hilbert范数一次项对任意固定向量 $z$ 给

$$
\|rw+z\|-r
=\frac{2r\operatorname{Re}\langle w,z\rangle+\|z\|^2}
{\|rw+z\|+r}
\longrightarrow\operatorname{Re}\langle w,z\rangle
\quad(r\to+\infty).
\tag{150.3}
$$

分母除以 $r$ 后趋于二，因为 $|\|rw+z\|-r|\le\|z\|$。这里仅对显式固定向量范数使用平方差恒等式。

在(149.4)取 $t=r\to+\infty$，两份右侧范数减去 $2r$ 的极限为

$$
-\operatorname{Re}\langle w,z_+\rangle
+\operatorname{Re}\langle w,z_-\rangle=-2b;
$$

左侧减去 $2r$ 的极限为 $2a$，故 $a\le-b$。再取 $t=-r\to-\infty$，两份右侧范数减去 $2r$ 的极限为 $2b$，左侧为 $-2a$，故 $a\ge-b$。两端一起迫使

$$
\operatorname{Re}\langle\eta,v\xi\rangle
=-\operatorname{Re}\langle p\xi,g\xi\rangle.
\tag{150.4}
$$

在这些等式中，$\operatorname{Re}\langle w,\mathfrak p_\eta z\rangle
=\operatorname{Re}\langle w,z\rangle$，所以没有将未知 $g$ 换成横向投影再求预算。由(149.5)及内积约定，(150.4)等价于

$$
\operatorname{Im}\langle\eta,g\xi\rangle
=\sigma\operatorname{Re}\langle\eta,v\xi\rangle.
\tag{150.5}
$$

先取 $(p,q)=(e,j)$，写

$$
A_\xi=\langle j\xi,v\xi\rangle,\qquad
B_\xi=\langle j\xi,g\xi\rangle.
$$

第一锚给 $\operatorname{Im}B_\xi=\sigma\operatorname{Re}A_\xi$。第二锚 $(p,q)=(j,-e)$ 给 $\eta'=-e\xi=i\sigma j\xi$，因此

$$
A'_\xi=-i\sigma A_\xi,\qquad B'_\xi=-i\sigma B_\xi.
$$

将它们代入第二份(150.5)，得到

$$
-\sigma\operatorname{Re}B_\xi=\operatorname{Im}A_\xi.
$$

联合两份实等式，准确为

$$
\boxed{B_\xi=i\sigma A_\xi,\qquad
\langle j\xi,(g-i\sigma v)\xi\rangle=0.}
\tag{150.6}
$$

两种实际锚各自使用148.3–148.7的一次PB及同一读取的两张P2，不假定它们的未知外层输出相等。

为将全部二次读取接回完整压缩，令 $E_\sigma=(I+\sigma Q)/2$、$P_\pm=(I\pm h)/2$，只在数学表示中使用这些投影；它们不成为原输入。$E_\sigma$ 与所有原元素交换。令

$$
M_\sigma=E_\sigma P_-\,j(g-i\sigma v)\,P_-E_\sigma.
\tag{150.7}
$$

(150.6)对 $H_{\sigma,-}$ 中每个单位向量成立，再以固定算子的二次齐次性推广到全部向量。普通复极化不需要 $M_\sigma$ 自伴：若 $q_M(\zeta)=\langle\zeta,M_\sigma\zeta\rangle$，则对任意 $\zeta,\omega\in H_{\sigma,-}$，

$$
\begin{aligned}
4\langle\zeta,M_\sigma\omega\rangle
&=q_M(\zeta+\omega)-q_M(\zeta-\omega)\\
&\quad-iq_M(\zeta+i\omega)+iq_M(\zeta-i\omega)=0.
\end{aligned}
\tag{150.8}
$$

所以 $M_\sigma=0$。$j$ 将 $H_{\sigma,-}$ 酉地送到 $H_{\sigma,+}=E_\sigma P_+H$，且 $j^2=I$；左乘 $j$ 即给

$$
E_\sigma P_+gP_-E_\sigma
=i\sigma E_\sigma P_+vP_-E_\sigma.
\tag{150.9}
$$

$g,v$ 自伴，故伴随确定反向块：

$$
E_\sigma P_-gP_+E_\sigma
=-i\sigma E_\sigma P_-vP_+E_\sigma.
\tag{150.10}
$$

这里的反号正是 $i\sigma hv$ 在反向块上的反号；没有声称完整 $g=i\sigma v$。$Q$ 中央排除不同 $\sigma$ 谱空间之间的任何原元素块。又

$$
P_{\rm tr}g=\tfrac12(g-hgh)=P_+gP_-+P_-gP_+,
$$

故(150.9)–(150.10)在两份 $Q$ 谱空间上共同给 $P_{\rm tr}g=iQhv$。空谱空间无须读取；若某份 $h$ 负空间为空，$j$ 的酉对应使其正空间也为空。忠实性把这个环境等式认回原元素，最后用147.2的已有原 $Tv=iQhv$ 得(150.1)。全部未知旧值只在有限原标签上出现，未使用任何 $D$ 的可加性或输入连续性。∎

## 151. 横向身份的有限原参数反事实

**推论 151.1（每个失败见证都有有限实际预算矛盾）。** 若150.1对某个固定原 $x$ 失败，则存在147.5的一种实际锚、有限实 $t,\alpha$、正实 $\delta$ 及149.1的一份向量态，使同一个原PB的(148.6)与该态下两份原P2不能同时成立。这是逐失败见证的有限检出，不是一份预先固定的有限参数表覆盖无限原域。

证明。若横向算子差非零，由 $Q$ 中央、自伴性及两个非对角块互为伴随，某份 $E_\sigma P_+(g-i\sigma v)P_-E_\sigma$ 非零。$j$ 的酉对应及复极化(150.8)遂给一个单位 $\xi$，使(150.6)失败。第一、第二实际锚的两份实等式不可能同时成立，故至少一种锚在(150.2)有

$$
\varepsilon:=a+b\ne0.
\tag{151.1}
$$

设 $F(t)$ 是(149.4)右侧减左侧。由(150.3)，

$$
\lim_{r\to+\infty}F(r)=-2\varepsilon,
\qquad \lim_{r\to+\infty}F(-r)=2\varepsilon.
\tag{151.2}
$$

$\varepsilon>0$ 时取一个有限大正 $t$，$\varepsilon<0$ 时取一个有限大负 $t$，使相应 $F(t)<0$。现在固定这个 $t$；(149.8)右侧是固定向量的连续范数，因此存在有限正 $\delta$，使(149.8)仍严格失败。等价地，该固定 $\phi_\delta$ 的(148.2)严格失败。最后固定 $t,\delta,\xi$：由(148.8)及(148.7)左侧的显式仿射式，除以 $|\alpha|$ 后的差趋向这份严格负差，所以某个有限大 $|\alpha|$ 已使(148.7)失败。

(148.7)只由该同一个原PB和同一态的两张原P2推出。故这个有限原三元组及两份完整原外层就是矛盾见证，不需要真的把无穷大或零极限当成原标签。参数可依赖 $x$、其同一旧值和失败压缩，没有给出统一的有限测试清单或资源上界。∎

## 152. 任意实纵向轴偏移的原值与两层原消费者

**定理 152.1（任意原横向输入加实轴偏移）。** 对全部实 $\lambda$ 及任意原 $v\in V_h$，同一个旧响应满足

$$
\boxed{D(h,\lambda h+v)=Tv=iQhv.}
\tag{152.1}
$$

$v^2$ 可非中央、奇异、非可逆或具有连续谱，$N(v)$ 不受小窗口限制。

证明。置原 $x=\lambda h+v$，固定同一个旧 $g=D(h,x)$。有 $h\circ x=\lambda u$。精确消费前卷18.1的标量交叠入口：它已经给出 $h\circ g=0$，故 $P_{\rm tr}g=g$。本卷150.1于是给

$$
g=P_{\rm tr}g=T P_{\rm tr}(\lambda h+v)=Tv.
\tag{152.2}
$$

这里用的是18.1已经证明的正交结论，不从相同面积平方擅自选择取向，也不重新证明或重计18.1的面积关系。其已有面积结论在这个分支正是 $g^2=v^2$，与133.2的 $(Tv)^2=v^2$ 相符；识别完整原值所新增的步骤是150.1。$\lambda=0$ 复用已有横向行，$v=0$ 复用同轴零值，这两种特例不另计增量。证明不对 $v^2$ 作原根、逆元、谱切片或归一。∎

**推论 152.2（同一旧行的两层有限嵌套）。** 对上述每个原 $(\lambda,v)$，两次原调用准确为

$$
\begin{array}{c|c|c}
\text{原层次}&\text{完整原输入}&\text{同一旧输出}\\ \hline
\text{内层}&(h,\lambda h+v)&Tv\in E\cap V_h\\
\text{外层}&(h,D(h,\lambda h+v))=(h,Tv)&-v
\end{array}
\tag{152.3}
$$

即

$$
\boxed{D(h,D(h,\lambda h+v))=-v.}
\tag{152.4}
$$

证明。内层由152.1识别为同一原 $Tv$，133.1保证它仍在原 $V_h$。外层再对这份实际旧输出使用133.1，得到 $D(h,Tv)=T(Tv)=-v$。全部内外标签均在原域，不把候选 $B_\star$ 的复合表冒充旧响应，也不把这个数学嵌套解释成实际仪器的逆向返回程序。∎

## 153. 同一原矩阵表的非对角块与精确剩余量

**定义 153.1（保留的原残差）。** 对每个原 $x=c+v$ 定义

$$
\rho_h(x)=P_{\rm com}D(h,x)\in E,\qquad
h\rho_h(x)=\rho_h(x)h.
\tag{153.1}
$$

150.1给准确分解

$$
\boxed{D(h,c+v)=Tv+\rho_h(c+v).}
\tag{153.2}
$$

这个定义不声称 $\rho_h(c+v)$ 与 $v$ 无关，也不声称它等于 $D(h,c)$。

**定理 153.2（与整个原系数几何的真实连接）。** 使用140.1及142.1的同一原矩阵坐标，令

$$
H=\phi(h)=\begin{pmatrix}u&0\\0&-u\end{pmatrix},\qquad
A=\phi(x)=\begin{pmatrix}a&b\\b^*&d\end{pmatrix}
\in H_2(\mathfrak b),
\tag{153.3}
$$

其中 $a,d\in\mathcal B_0$、$b\in\mathfrak b$；这里矩阵中的 $u$ 是系数代数的单位。则同一个旧 $\widetilde D$ 准确满足

$$
\boxed{\widetilde D(H,A)=
\begin{pmatrix}
r_+(A)&ib\\-ib^*&r_-(A)
\end{pmatrix},\qquad r_\pm(A)\in\mathcal B_0.}
\tag{153.4}
$$

同一个旧输出的全部非对角块已识别；两个对角块仍是原问题的剩余量。特别对全部 $\lambda\in\mathbb R,b\in\mathfrak b$，

$$
\widetilde D\left(H,\begin{pmatrix}\lambda u&b\\b^*&-\lambda u\end{pmatrix}\right)
=\begin{pmatrix}0&ib\\-ib^*&0\end{pmatrix}.
\tag{153.5}
$$

证明。$P_{\rm com}x$ 对应 $A$ 的对角部分，$P_{\rm tr}x$ 对应非对角部分。138.2的候选有准确身份

$$
B_\star(h,x)=\tfrac{iQ}{2}[h,x]=iQhv=Tv.
\tag{153.6}
$$

因此本次150.1不是用它定义旧值，而是另外证明旧值与这份候选的差只在交换块中：142.2的同一全域残差限制到这条原行时，确有

$$
\rho(h,x)=D(h,x)-B_\star(h,x)=\rho_h(x).
\tag{153.7}
$$

由140.3，

$$
\phi(Tv)=\tfrac i2[H,A]
=\begin{pmatrix}0&ib\\-ib^*&0\end{pmatrix}.
\tag{153.8}
$$

将(153.2)整体施加 $\phi$，剩余原自伴交换块 $\phi(\rho_h(x))$ 恰为两份自伴系数 $r_\pm(A)$，即(153.4)。这里从未对不要求属于 $E$ 的辅助 $Q$ 施加 $\phi$。$a=\lambda u,d=-\lambda u$ 时，152.1消去同一剩余块，得到(153.5)。矩阵系数可以非交换且不完备，$b$ 是任意原系数复化元素，不是标量窗的替代记号。∎

**定义 153.3（准确未证边界）。** 在本次固定实际三轴分支，一般目标仍包含

$$
\rho_h(c+v)=0\quad(c\in\operatorname{Com}_h,\ v\in V_h).
\tag{153.9}
$$

150.1仅把这份缺口定位到同一旧输出的 $h$-交换块。$v=0$ 时它只给 $[D(h,c),h]=0$，不证明一般 $D(h,c)=0$；特别对任意 $c\in\mathcal B_0$ 的完整零行仍未支付。$\rho_h(c+v)=D(h,c)$ 亦未支付，不能先设它与 $v$ 无关再消去它。152.1只消去 $c=\lambda h$ 的分支；不能把它与此前另已支付的单位偏移分支合用，擅自得到任意 $\mu u+\lambda h+v$ 的完整原值，也不能推出一般单位或中央平移。

全部原第二输入上的完整单位平方行、一般首标签、无这份实际原正交三轴的域、一般第一槽齐次、全域分别可加及实双线性、全部旧P3与有限旧复Gram、旧R和同一旧结合乘法，仍各有未付桥。一般商下降、输入函数演算、未知输入连续性及旧响应的原完成运输也未由此得到。141.1的候选正表、候选R和139.2的候选完成保持其候选身份，不代付这些旧表条件。没有给出满足完整全部原P2/PB而违反上述一般结论的反模型，故不宣称这些条件独立或完整目标不可能。

## 154. 承重来源、二元后果与几何简化的范围

**定义 154.1（原关系对应与复用边界）。** 148–153的增量归为 $\texttt{repo-derived}$ 综合：任意原混合 $x$ 的同一旧输出，先由实际PB及两份原P2识别全部横向块，再以既有正交消费者识别实纵向轴偏移分支，最后给同一行的两层旧值。其承重关系准确为：

| 来源 | 本次承担的义务 |
| --- | --- |
| 130.1、137.1及123.2 | 同一个旧总映射、完整原A1–A3/P2/PB、原准确锥和同一读取；不预付混合旧输出横向 |
| 前卷77.1 | 两份实际锚的全部有限内值 $D(h,tp+\alpha n)=tq$，使148.4的外层完整可列 |
| 133.1–134.1 | 原横向 $T$、负平方及整个环境中的中央 $Q$；不重计 $M,C_{+,+}$ 消失或横向行 |
| 148.6–148.9 | 一份实际PB与同态两张P2的完整Gram预算，保留一般 $k$、$g$ 及全部常数项 |
| 149.3、150.3及150.8 | 任意自伴旧输出的向量预算、正反大锚一次项与两锚复极化，认回同一个非对角块 |
| 前卷18.1及150.1 | 已有正交加本次投影身份，供152.1识别任意原 $v$ 与实 $\lambda h$ 混合的完整旧值 |
| 133.1及152.1 | 152.3两次实际原调用，外层消费内层已经认回的旧输出 |
| 138.2、140.1及142.1 | 将新身份准确接到同一 $H_2(\mathfrak b)$ 原域和旧 $\widetilde D$；剩余只在该行的对角块 |

124–125已对横向输入使用共享预算及饱和读取，133–134已识别全部原横向行；本次不将这些特例改称新结论。前卷18.1的面积与正交、77.1–78.1的标量四维窗均直接复用；152.1的 $v$ 不必落在任何标量平方片中。静态卷55.1–56.1认回所有混合旧值的入口还要求有限完成及全部固定演员行的可加性，不能用该条件结论代付本次任意不完备原域中的剩余块。以上对应不宣称全仓检索穷尽。

148.8的实Gram展开、149.3的Hilbert范数恒等式、150.3的范数一次项和150.8的固定算子复极化都是成熟中间工具，已在承重证明中给出具体等式。它们不证明一般非线性旧表的局部到整体定理，也不供应额外联合正表。van de Wetering，[*Commutativity in Jordan Operator Algebras*](https://arxiv.org/html/1912.01903v1)，Proposition 3.2及式(2)的JC对应保持136.1的使用范围；Alfsen–Shultz，[*Orientation in Operator Algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，Theorem 1的全域线性动力对应前件仍未供应。Cabello–Peralta，[*Weak-2-local symmetric maps on C*-algebras*](https://arxiv.org/abs/1510.00915)，Theorem 2.5所需完整复C*域及逐对、逐泛函共同复线性保星插值器也不是本候选的前件。这里沿129.1、136.1已有引文保留这些适用边界，不宣称新的外部文献穷尽或全球原创。

137–140的更简洁几何是整个原Jordan域的有限四系数与 $H_2(\mathfrak b)$，不是普通三维Bloch球。本次增加的是同一个旧响应缺陷的定位：对固定 $h$ 的全部原混合输入，几何中的非对角块已无自由余量；未知仍在同一个旧输出的两份对角块。138.3的内部系数闭合若失败，会直接破坏原跨轴Jordan二元关系；150.1的旧输出投影若失败，则由151.1破坏一份实际原PB和同态两张P2。二者的反事实对象不同，不能用候选闭合替代旧响应身份。完整原公理仍逐项使用，未减少所声明的独立公理数，也未证明最少公理数或独立性。

## 155. 新支付对七项原量子消费者的准确接口

**定义 155.1（同一原来源与七项条件保持）。** 145.1–145.7的七项定义逐项完整保持。本次新增支付只有150.1的固定行横向块、152.1的受限混合完整原值及152.3的两层原调用，不把它们升级为全部量子来源。相应接口为：

1. **复Hilbert、可观测量与叠加。** 145.1已有的数学 $\mathcal C\cong M_2(\mathcal B)$ 表示保持；新值确实属于同一个旧行，却没有供应全域 $D=B_\star$、旧双线性、旧P3、原R及全域共同乘法。唯一原 $\Omega$、原 $E/S/D$、native、全词同一 $q,K,J$、parent/ready、具名可取得标签、合法控制及实际相干叠加准备不由辅助压缩生成，也不宣称所有 $B(H)$ 均可取得。
2. **态、效果、质量与Born。** 145.2中的同一原正评价、原效果、全部实际完整菜单及接受条件保持；仅对正质量归一，零、不等、次归一质量、中心经典混合、不等维与静默部分完整保留。证明中的数学向量态不增加实际准备，原质量没有被 $\delta$ 或谱压缩重定标。
3. **native、真相关联合与张量。** 145.3中的同一个实际非零共同来源、忠实同向交换的两腿、共同生成分离、所需重数及全部相关输入仍须原实现。相同边缘、辅助 $Q$ 的谱部分和系数矩阵分解均不提供真相关联合；完整目标中无轴、经典及奇数矩阵等原域继续保留。
4. **CP与整台递归同源参考。** 145.4中的原回溯、typed前接后接、所有仍合法未来、原箭头商下降、系统与参考共同真支持、支持内补、全部相关正输入及每个所需有限递归深度不变。整台实际箭头连同环境、全部成功／失败／细记录／port／post-port输出都在原量词内；单行非对角识别不支付这些运输或联合正性，也不把143.2的一级序边界升级为CP。
5. **完整仪器、Kraus、TP、更新与Lüders。** 145.5所需全部原输入运输、完整typed菜单和单位分区、AC及原接受端、射线校准、真正分组遗忘及全部输出保持。更新仅在正输出质量归一；Kraus、密度与迹类公式仍限于准确合格的有限全矩阵域，或另已供应正常表示、指定前对偶及所需收敛的域。152.3的旧响应输出不提供原平方根词或实际仪器。
6. **全部历史、未来、真遗忘、双向真实返回与CountRead。** 145.6的全部合法顺序／自适应／并行历史、每个仍合法未来、全部细记录、停止／拒绝／销毁、泄漏、同数两侧及逆向真实返回保持。152.4是数学两层响应，不能认作实际返回程序。CountRead仍绑定读后同一原完整活动输入和全未来；无限／非离散记录、可数可加、正常性及指定前对偶不由本次范数读取或原域有限嵌套产生。
7. **动力、物理钟、能量与共同尺度。** 145.7的同一旧全域乘法、保持不完备原域的流、实际相位与门序列、可逆一参数群、物理钟、强连续酉实现及生成元定义域、Hamiltonian能量解释、作用量与共同正 $\hbar$ 仍各取原来源和预算。$\alpha,t,\delta$ 是有限见证的数学参数，其极限仅比较固定标量或向量，不供应物理时间、控制成本或钟能量的共同尺度。

因此同源要求仍覆盖唯一原世界、原评价与质量、全部实际菜单、整台输出及环境记录、真正相关联合与递归参考、全部历史未来及真遗忘双向返回。辅助 $Q$、向量态、矩阵坐标和两层数学响应不替换任何一个原接口。

## 156. 任意混合旧输出与剩余对角块的完整白话

**定义 156.1（同一原值、两次实际配平与几何位置的白话含义）。** 固定已经存在的原轴 $h$ 后，每个原输入都能有限地拆成两份：一份与 $h$ 交换，记作 $c$；另一份与 $h$ 反交换，记作 $v$。旧结果已经知道单独送入 $v$ 时，同一原响应会把它转成 $Tv$。新问题是，把任意交换部分 $c$ 加进去以后，那张旧表究竟还输出什么。这里不先说输出横向，也不把新构造的标准表当成答案；同一份完整旧输出一直记作 $g$。

已知的三轴小窗提供两种确实可调用的锚。把锚沿同一已知原方向放大，再加一个有限倍的 $u+h$，每种锚都只需把它和原 $x$ 放进一次完整正反配平。两份内层旧值已知，其中一份就是固定的 $g$；两份外层虽然未知，却各有同一个正读取的原二表预算。展开的只是已知Jordan乘法，绝不把未知响应拆成加法。大投影倍数的三次、四次项相消，留下两份完整Gram预算；交换输入和输出的对角块在这一步都保留。

随后用一个几乎落在 $h$ 负空间的数学向量读取，并在正空间掺入一点由实际锚确定的向量。它不是新准备，只是准确锥允许的证明读取。对任意自伴旧输出，Gram行列式都恰好是一份去掉实方向后的向量范数平方，所以不需要先假定 $g$ 横向。交换输入 $c$ 在选定负向量上的已知组合消去，未知 $g$ 的对角作用仍在范数里。

让已知锚分别沿正端和负端变大，固定向量范数的两份一次项必须同时满足预算。与锚正交的固定对角向量不能改变这份一次项，因此两端共同固定一个真实非对角读数。换另一种实际锚，就补齐它的另一个复相位分量；再比较同一空间中向量的和与相位和，所有非对角块都被确定。结论是：不论原交换输入 $c$ 是什么，同一旧输出的横向部分始终就是 $Tv$。若有一处不符，先取有限大的正锚或负锚，再取有限小的掺入量和有限大的投影倍数，就已经破坏同一次原配平与两张原二表；并不需要把无穷标签送进旧表，也没有一张固定有限参数清单覆盖全部原输入。

这仍没有删掉输出中与 $h$ 交换的那一块。它准确叫作 $\rho_h(c+v)$，是同一旧输出的一部分，可以依赖整个输入。现在还不能说它就是单独输入 $c$ 的响应，更不能直接说一般为零。四系数矩阵几何因此确实让问题短了一截：整条固定旧行的非对角块已认回，剩下的是同一张表的两个对角块；不是另画一张更漂亮的候选表替代原表，也不是少用了原公理。

若交换输入恰好只是任意实倍 $\lambda h$，情况进一步闭合：原交叠 $h\circ(\lambda h+v)$ 是标量单位，既有18.1已经保证完整输出横向。本次又确定了它的全部横向部分，所以真正得到原值 $D(h,\lambda h+v)=Tv$。这里的 $v$ 可以有非中央、奇异或连续谱平方，不需属于有限标量窗。把这份已经认回、仍在原域的输出再送入同一行，第二次原响应就是 $-v$。它是两个真实原标签调用的数学身份，不是实际机器已经能逆向返回的证明，也不能和另一种单位偏移未经证明地叠加使用。

完整目标还包括一般交换块零值、完整单位平方行、其它首标签和没有这些实际三轴的原域，以及同一旧表的全域双线性、原R与完成运输。三轴和带系数二阶矩阵没有把物理空间规定为三维。实际准备、全部菜单和原质量、整台仪器与环境记录、真相关联合和递归同源参考、全部历史未来、真遗忘和双向真实返回、完整计数、物理钟、能量及共同正尺度，仍必须来自同一个原世界，不能由这份几何或数学嵌套凭空供应。

## 追加锚（本行以下为增补区）

## 157. 原生横向域中的三轴共同交换残差

**定义 157.1（同一原资料与已识别的投影）。** 本节及158–160完整保持
130.1、137.1及147.1的同一原 $(E,C,u,N,\mathcal P,S,D)$、准确锥、
全部A1–A3、全部原P2及完整原PB。固定同一实际原三轴
$h^2=e^2=u$、$h\circ e=0$、$j=D(h,e)$，沿用134.1的辅助中央自伴对合
$Q=ihej$、147.3的有限原投影和153.1的同一旧输出残差 $\rho_h$。记

$$
\begin{gathered}
\widehat T_h=[L_j,L_e],\qquad
P_a^-=\tfrac12(I-U_a),\qquad U_a=2L_a^2-I\quad(a=h,e,j),\\
\widehat T_hx=\tfrac i2Q[h,x]=T P_{\rm tr}x,\qquad
\rho_h(x)=D(h,x)-\widehat T_hx\in\operatorname{Com}_h
\quad(x\in E).
\end{gathered}
\tag{157.1}
$$

环境恒等式沿用153.6及136.1的JC交换子对应；最后一式直接消费150.1和
153.1–153.2，不另证明任意原输入的奇块识别。原 $E$ 仍可不完备，旧
$D:E^2\to E$ 仍是原总映射，不添加一般齐次、可加、连续、可测、单位或中央
平移、商下降、完成延拓、任意原轴存在或物理来源前件。方括号仍只指原
环境交换子，$\widehat T_h$ 和138.2的 $B_\star$ 均不重定义旧 $D$。

**定理 157.2（R2：同一旧残差的原生共同交换子包含）。** 对每个原
$x\in V_e$，置 $y=D(e,x)$。则 $y\in V_e$、$y^2=x^2$、
$D(e,y)=-x$，并且

$$
\boxed{\rho_h(x)\in E\cap\{h,e,j\}'=\mathcal B_0.}
\tag{157.2}
$$

因而对任意原 $b,c\in V_e$，固定首轴的加性缺陷

$$
\delta_h(b,c):=D(h,b+c)-D(h,b)-D(h,c)
$$

满足

$$
\boxed{\delta_h(b,c)\in E\cap\{h,e,j\}'=\mathcal B_0.}
\tag{157.3}
$$

输入平方不要求标量、中央、可逆或有限谱。

证明。133.1对实际框架 $(e,h,-j)$ 给出
$y=iQex\in V_e$、$y^2=x^2$ 及 $D(e,y)=-x$。在原PB中取

$$
(a,b,c)=\left(e,\frac{h-j}{2},\frac{x+y}{2}\right).
$$

133.1还给 $x\circ y=0$。两份内层位移准确为
$\nu=-(h+j)/2$、$\omega=(y-x)/2$，故
$b\circ\nu=-(h^2-j^2)/4=0$、
$c\circ\omega=(y^2-x^2)/4=0$。两份外层准确为 $(-j,y)$ 与 $(h,x)$，
完整PB的右侧遂为零，得到

$$
D(-j,y)=D(h,x)=:d_x.
\tag{157.4}
$$

对实际框架 $(-j,e,h)$ 使用150.1，记
$\widehat T_{-j}=[L_h,L_e]$。此框架的中央取向仍为 $Q$，所以

$$
P_j^-d_x=\widehat T_{-j}y=\widehat T_hx.
\tag{157.5}
$$

其中 $\widehat T_{-j}y=\tfrac{iQ}{2}[-j,y]$；代入 $y=iQex$，
再用 $ex=-xe$、$je=iQh$、$ej=-iQh$，即得最后一个等号。
150.1本身给 $P_h^-d_x=\widehat T_hx$，而 $\widehat T_hx$ 同时属于
$h,j$ 的奇块，故 $\rho_h(x)$ 与 $h,j$ 普通交换。又 $Q$ 中央且
$e=-iQhj$，它也与 $e$ 交换，证明157.2。由于 $\widehat T_h$ 是已知
线性Jordan算子，

$$
\delta_h(b,c)=\rho_h(b+c)-\rho_h(b)-\rho_h(c),
$$

所以157.3成立。这里没有把 $D(h,b+c)$ 拆成两项；PB只识别了同一个旧值
$D(-j,y)$。∎

## 158. 标量平方第二输入的完整原值

**推论 158.1（R3：全标量平方第二输入）。** 在157.1的原背景下，若原
$x$ 满足

$$
x^2=\lambda u,\qquad\lambda\ge0,
$$

则

$$
\boxed{D(h,x)=\widehat T_hx,\qquad\rho_h(x)=0.}
\tag{158.1}
$$

零输入、$\lambda=0$、非零输入与 $h$ 有非零交叠的情形全部包含在内。

证明。因 $h^2-x^2=(1-\lambda)u$，前卷18.1给
$h\circ D(h,x)=0$。于是 $D(h,x)=P_{\rm tr}D(h,x)$，150.1立即给158.1。
没有除以 $x^2$，也没有选取谱根或补入原域外的标签。∎

## 159. 两个实际框架的支撑敏感取向律

**定理 159.1（两个实际演员的交叠交换子支撑）。** 在同一原背景与环境中，
设 $h,a\in E$ 是两个实际单位平方演员，各自带有实际原正交框架
$(h,e,j)$ 与 $(a,f,k)$，其中 $j=D(h,e)$、$k=D(a,f)$。
记两份134.1所给的辅助中央自伴对合为
$Q_h=ihej$、$Q_a=iafk$。则

$$
D(h,a)=\frac i2Q_h[h,a],\qquad
D(a,h)=-\frac i2Q_a[h,a],
$$

并且

$$
\boxed{(Q_h-Q_a)[h,a]=0},\qquad
\boxed{\frac{u-Q_hQ_a}{2}\,[h,a]=0}.
\tag{159.1}
$$

第二式是中央支撑投影的说法；它不把 $[h,a]$ 可逆化，也不要求两个中央
取向在整个环境中相同。

证明。158.1分别应用于框架 $h$ 和 $a$，再用157.1的环境表达式与
原反对称性 $D(a,h)=-D(h,a)$，得到第一份框中等式。两中央自伴对合
相乘仍为中央对合；将该等式左乘 $Q_h$，再除以二，得到第二式。∎

若 $f$ 是实际存在且与 $h$ 正交的伴轴，133–134已经给其同一 $h$ 行所
继承的 $Q$ 相等关系。157.2在另一个实际框架上只能作用于该框架所给出的
$V_f$（及其明确的伴轴横向域）；只有当一个输入同时属于两份规定域时，
相应残差才可写成两个共同交换子的交。这里没有制造新的伴轴，也没有把
有限交提升为 $Z(X)$。

## 160. 残差约束的来源与完整原消费者边界

**定义 160.1（关系的归属与准确消费者）。** 157–159是
$\texttt{repo-derived}$ 的固定实际框架应用，不宣称历史原创或文献穷尽。
承重来源与适用范围为：

| 关系 | 直接使用的来源 | 准确范围 |
| --- | --- | --- |
| 157.1 | 150.1、153.1–153.2、153.6及133–134 | 复用任意原输入的奇块识别及同一 $\rho_h$，不另立重复证明 |
| 157.2–157.3 | 133.1的实际 $(e,h,-j)$ 行、完整原PB及两份150.1 | $V_e$ 上的同一残差及固定首轴缺陷落入实际三轴共同交换子 |
| 158.1 | 前卷18.1与150.1 | 全部 $x^2\in\mathbb R_{\ge0}u$ 的第二输入零残差 |
| 159.1 | 两份实际原框架、158.1及原反对称性 | 两个实际演员交叠交换子的中央支撑律 |

157.1的成熟环境中间恒等式准确沿用136.1、154.1所引
van de Wetering，*Commutativity in Jordan Operator Algebras*，
Proposition 3.2及式(2)的JC对应；文献只供应该环境恒等式，不识别未知原
$D$。137–146的整个系数矩阵几何、133–134的全部 $V_h$ 横向行与全局
$Q$ 中央性，以及同一伴轴的 $Q$ 相等均直接复用。152.1的实纵向轴偏移
分支也保持其原范围。158.1使用标量平方差入口，未把152.1与单位偏移
未经证明地拼接；一般非标量平方输入仍不由158.1处理。

**定义 160.2（混合接缝及中央性与增长缺口）。** 对任意原 $c,z$ 满足

$$
U_hc=c,\qquad z\in V_h,
$$

仍需证明

$$
\boxed{\rho_h(c+z)=\rho_h(c)},\quad\text{即}\quad
\boxed{D(h,c+z)=D(h,c)+\widehat T_hz}.
\tag{160.1}
$$

153.9的全行零残差目标也完整保持。150.1只给 $\rho_h(c+z)$ 与 $h$
交换；157.2只有在 $c+z\in V_e$ 时才给三轴共同交换子，158.1只消去
标量平方输入。一般 $c+z$ 的 $h$-交换部分与横向部分之间仍未由这些关系
取得消去未知混合响应的实际PB/P2预算。特别不能把一般 $D(h,c)$ 当作零，
也不能先把 $D(h,c+z)$ 拆成两项。一般 $h$-交换原输入的完整零行仍未支付。
这个缺口保留任意首标签、无实际三轴的原域和全域旧 $D$ 的完整量词。

静态卷89.2–89.3要求对全部原 $a,b,c$，

$$
\delta_a(b,c)\in E\cap Z(X),\quad\text{等价地}\quad
[L_{\delta_a(b,c)},L_x]y=0\quad(\forall x,y\in E).
$$

157.3只有 $\mathcal B_0=E\cap\{h,e,j\}'$。137.1已经保留该系数域非交换
的可能性，它不自动成为全局中心。共同交换子严格较大的例子是标准
$M_2(\mathbb C)\otimes M_2(\mathbb C)$ 背景中的
$h=\sigma_z\otimes I$、$e=\sigma_x\otimes I$、$j=-\sigma_y\otimes I$：
$I\otimes\sigma_z$ 与三轴交换，却不与 $I\otimes\sigma_x$ 交换。
这仅排除“共同交换子即全局中心”的推断，不是否定标准响应中的零残差。
因而157.3不能直接消费静态卷89，也未给任意混合输入残差间的自交换。

静态卷94–98的条件消费者要求统一缺陷包络

$$
A(R)=\sup_{\|a\|,\|b\|,\|c\|\le R}\|\delta_a(b,c)\|=o(R).
$$

157–159没有给这个全输入一致增长；逐份P2至多提供二次量级的
$A(R)\le4R^2$ 型上界，不能替换 $o(R)$。原多项式卷51.2已在其指定
标量端点二阶矩阵多项式原域中识别全部混合旧值。因此该卷原式(39.2)的
混合中心接头

$$
D(fu+A,gu+B)=D(A,B)
\tag{160.2}
$$

在该指定域已由57.1支付，49.1的全部锚幅度也由该式识别。
该识别使用指定标量端点和同一实际输出的有限多项式性，
不能倒推为任意原域的混合拼接，也不把157.2的共同交换子变成全局中心。
158.1同样不能补这份一般桥。

对上述一般原域目标，没有构造满足完整原P2/PB却违反它们的反模型，
也不宣称其独立或不可能。指定多项式分支已取得该卷57.1的旧双线性、
原P3、有限旧复Gram、原R及同一旧结合乘法；在这里保留的任意原域中，
这些全域旧表与原完成运输仍各有未付桥。候选 $B_\star$ 不替代旧 $D$。

**定义 160.3（完整原来源与物理范围）。** 145.1–145.7及155.1的全部来源
接口逐项完整保持。唯一原 $\Omega$、原 $E/D$、一般无原子及不完备域、
native、全词同一 $q,K,J$、parent/ready、中心经典与不等维块、全部实际
准备及零／不等／次归一质量均保留。Born只在正质量的实际完整菜单上归一；
Hilbert表示、数学正读取、向量态、辅助中央取向和系数矩阵均不产生实际
准备、菜单或原域外可调用标签。

CP仍需同一整台实际箭头、真正相关联合及递归同源参考；完整仪器的环境、
成功／失败、细记录、port及post-port输出，Kraus、TP、更新、Lüders与
实际忠实同向交换且共同生成的张量仍各守原前件。全部合法顺序、自适应、
并行历史、每个仍合法未来、真正分组遗忘、停止／拒绝／销毁、泄漏、
同数两侧及逆向真实返回全部在原量词内。CountRead与无穷／非离散记录、
可数可加、正常性、指定前对偶、保持原域的流、物理钟、Hamiltonian
生成元定义域、能量、作用量及共同正 $\hbar$ 均未由157–159生产。
局部旧值身份、数学完成或辅助支撑投影不供应这些实际来源。

## 追加锚（本行以下为增补区）

## 161. 两种实偏移的同一原响应与完整前件

**定义 161.1（原候选、实际三轴与结论域）。** 本节及以下各节完整采用130.1、137.1、147.1的同一原 $(E,C,u,N,\mathcal P,S,D)$。$E$ 是实Archimedean序单位空间，$\mathcal P$ 的正实线性评价分离元素并准确决定 $C$；每份质量 $m_\alpha=\alpha(u)$ 保留原值，包括零、不等和次归一质量。A1保留所有原标签的两条有向Hermitian二表正性；A2保留实际相加三表 $(a+b,a,b)$ 及其排列在整个实三空间的实部半正定性和 $(1,-1,-1)$ 的零二次值；A3保留 $S(u,u)=u$ 及同一固定有理 $0<\vartheta_0\le1$ 上的 $0\le z\le\vartheta_0u\Rightarrow S(z,z)\le z$。全部原P2和完整原PB仍对全部原输入成立。

沿前卷16.1–16.2的同一忠实、含单位、等距且准确保锥JC包含，写

$$
\begin{gathered}
E\subset X\subset\mathcal A_{\rm sa},\qquad
\overline E=X,\qquad\mathcal A=C^*(X),\\
S(a,b)=a\circ b=(ab+ba)/2,\qquad
C=E\cap\mathcal A_+,\quad N=\|\cdot\||_E.
\end{gathered}
\tag{161.1}
$$

原 $E$ 可以不完备，$X$ 不必为 $\mathcal A_{\rm sa}$；$D:E^2\to E$ 始终是同一旧总映射。不预付一般齐次、可加、连续、可测、商下降、输入函数演算或完成延拓。固定实际原 $h,e,j=D(h,e)$，直接消费133.1–134.1与147.2–147.3：

$$
\begin{gathered}
h^2=e^2=j^2=u,\quad h\circ e=h\circ j=e\circ j=0,\\
Q=ihej\in Z(\mathcal A),\quad Q^*=Q,\quad Q^2=u,\\
V_h=\{v\in E:hv=-vh\},\quad
T=[L_j,L_e],\quad D(h,v)=Tv=iQhv,\quad T^2v=-v,\\
U_h=2L_h^2-I,\quad
P_{\rm tr}=(I-U_h)/2,\quad P_{\rm com}=(I+U_h)/2,\\
\operatorname{Com}_h=P_{\rm com}E=\{c\in E:hc=ch\}.
\end{gathered}
\tag{161.2}
$$

$L_a z=a\circ z$。$T$、两份投影及 $h\circ x$ 都是保持原 $E$ 的有限Jordan表达式。辅助 $Q$ 不要求属于 $E$ 或 $X$；证明中的结合乘法、Hilbert向量及读取代数不扩大原输入域。零原对象的所有等式均为零。

本组定理的完整原值域是

$$
D(Rh,\mu u+\lambda h+v),\qquad
D(su+rh,w),\qquad
R,\mu,\lambda,s,r\in\mathbb R,\quad v,w\in V_h.
\tag{161.3}
$$

第二式的第二输入严格为横向；这两个受限域不被合成为 $D(su+rh,\mu u+\lambda h+v)$ 的一般公式。原七项来源合同保持145.1–145.7、155.1及下文171的全部量词。

**定义 161.2（实际锚、原预算与同轴零行）。** 置 $n=u+h$，只用两种实际锚 $(p,q)=(e,j),(j,-e)$。前卷76.1–77.1在同一实际三轴的四维标量窗内准确给

$$
D(su+rh,tp+\alpha n)=rtq
\qquad(s,r,t,\alpha\in\mathbb R).
\tag{161.4}
$$

这里 $su+rh$ 和 $\alpha u+\alpha h+tp$ 都属于该四维窗；所用叉积是 $h\times p=q$。同时直接复用前卷16.2的全单位行、零输入零值、反对称性及同轴仿射零行，特别是

$$
D(su,y)=0\quad(y\in E),\qquad
D(au+bh,cu+dh)=0\quad(a,b,c,d\in\mathbb R).
\tag{161.5}
$$

这些是已识别的原值，未由一般输入线性性推得。对同一个数学正读取 $\phi$，完整P2与PB的元素式为

$$
\begin{gathered}
B_\phi(a,b)=\phi(a^2)\phi(b^2)-\phi(a\circ b)^2,\qquad
|\phi D(a,b)|^2\le B_\phi(a,b),\\
\nu=D(a,b)-a\circ z,\quad\omega=a\circ b+D(a,z),\\
D(b+\nu,z+\omega)-D(b-\nu,z-\omega)
=-2b\circ\nu-2z\circ\omega.
\end{gathered}
\tag{161.6}
$$

前卷16.2和本卷123.2的准确锥接口允许环境数学态读取每张原P2；证明不把它们列为实际准备，也不将 $|\phi D|^2$ 换成 $\phi(D^2)$。

## 162. 仿射首标签的完整外层与共享 Gram

**引理 162.1（不删除交换块的仿射预算）。** 固定任意原 $x\in E$ 及实 $s,r$，记

$$
\begin{gathered}
a=su+rh,\quad g=D(a,x),\quad
v=P_{\rm tr}x,\quad k=h\circ x,\quad\theta=s+r,\\
Z=(1+s\theta)x+r\theta k,\\
W_+=Z+g-rtp-r\theta tq,\qquad
W_-=Z-g+rtp-r\theta tq.
\end{gathered}
\tag{162.1}
$$

对161.2的任一锚、每个有限实 $t$ 及同一个数学正读取 $\phi$，有

$$
\boxed{2|r|\,|\phi(tq+v)|
\le\sqrt{B_\phi(n,W_+)}+\sqrt{B_\phi(n,W_-)}.}
\tag{162.2}
$$

$Z,g,W_\pm$ 的全部交换块均保留。

证明。对每个有限实 $t,\alpha$，在原PB中准确取 $(a,b,z)=(su+rh,tp+\alpha n,x)$。由(161.4)，内值为 $rtq,g$。两份位移和完整外层输入准确为

$$
\begin{aligned}
\nu&=rtq-sx-rk,&\omega&=stp+\theta\alpha n+g,\\
R_+&=t(p+rq)-sx-rk+\alpha n,&
S_+&=x+g+stp+\theta\alpha n,\\
R_-&=t(p-rq)+sx+rk+\alpha n,&
S_-&=x-g-stp-\theta\alpha n.
\end{aligned}
\tag{162.3}
$$

所有标签仍在原 $E$。若 $c=P_{\rm com}x$，则 $k=hc$，$n\circ x=c+hc+v$、$n\circ k=c+hc$；另有 $p\circ q=0,n\circ q=q$。因此完整PB的右端是

$$
\begin{aligned}
-2(tp+\alpha n)\circ(rtq-sx-rk)
-2x\circ(stp+\theta\alpha n+g)
=2rt\,p\circ k-2x\circ g-2\alpha r(tq+v).
\end{aligned}
\tag{162.4}
$$

其中 $2st\,p\circ x$ 与 $-2st\,x\circ p$ 相消；含 $\alpha$ 的其余项为 $-2\alpha r\{tq+n\circ x-n\circ k\}$。没有删除任何未知旧值。两份外层分别用同一个 $\phi$ 的原P2，给

$$
\left|\phi(2rt\,p\circ k-2x\circ g)-2\alpha r\phi(tq+v)\right|
\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{162.5}
$$

为处理任意实斜率，包括 $\theta=0$，对固定自伴 $A,B,n$、任意实 $\vartheta$ 作实Gram展开：

$$
\begin{aligned}
B_\phi(A+\alpha n,B+\vartheta\alpha n)
&=B_\phi(A,B)+2\alpha C_\vartheta
+\alpha^2B_\phi(n,B-\vartheta A),\\
C_\vartheta
&=\vartheta\phi(A^2)\phi(n\circ B)+\phi(n\circ A)\phi(B^2)\\
&\quad-\phi(A\circ B)\{\phi(n\circ B)+\vartheta\phi(n\circ A)\}.
\end{aligned}
\tag{162.6}
$$

确实，两份平方读取的系数依次为 $(\phi(A^2),2\phi(n\circ A),\phi(n^2))$ 和 $(\phi(B^2),2\vartheta\phi(n\circ B),\vartheta^2\phi(n^2))$；交叠读取的系数是 $(\phi(A\circ B),\phi(n\circ B)+\vartheta\phi(n\circ A),\vartheta\phi(n^2))$。相乘再减平方，三、四次项各自抵消，二次项恰为所写的Gram式。

正外层取 $A=t(p+rq)-sx-rk,B=x+g+stp,\vartheta=\theta$，所以 $B-\vartheta A=W_+$；负外层取 $A=t(p-rq)+sx+rk,B=x-g-stp,\vartheta=-\theta$，所以 $B-\vartheta A=W_-$。将(162.5)除以 $|\alpha|$，只在这两个显式标量二次式中令 $|\alpha|\to\infty$，得到(162.2)。二次系数为零的根号除后也趋于零，故包括全部退化情形。这不是旧 $D$ 的输入极限。∎

## 163. 正负强度均适用的仿射首标签投影

**定理 163.1（任意原第二输入的横向块）。** 在161.1下，对全部实 $s,r$ 及任意原 $x\in E$，同一个旧响应满足

$$
\boxed{P_{\rm tr}D(su+rh,x)=rT P_{\rm tr}x.}
\tag{163.1}
$$

$r=0$ 包含原单位行，不要求旧输出横向。

证明。$r=0$ 时直接用(161.5)，两边为零。设 $r\ne0$，保持162.1的同一固定 $x,g,v,Z$。在忠实含单位Hilbert表示中取内积第一槽共轭线性。对任一 $\sigma\in\{1,-1\}$，取任意单位向量 $Q\xi=\sigma\xi,h\xi=-\xi$，置 $\eta=q\xi$。149.1–149.5给

$$
\|\eta\|=1,\quad h\eta=\eta,\quad
p\xi=-i\sigma\eta,\quad
\mathfrak p_\eta z=z-\operatorname{Re}\langle\eta,z\rangle\eta.
\tag{163.2}
$$

用向量 $(\xi+\delta\eta)/\sqrt{1+\delta^2}$ 的态 $\phi_\delta$。准确复用149.3对任意固定自伴 $W$ 的恒等式

$$
B_{\phi_\delta}(n,W)
=\frac{4\delta^2}{(1+\delta^2)^2}
\|\mathfrak p_\eta(W\xi+\delta W\eta)\|^2.
\tag{163.3}
$$

另一方面，$tq+v$ 横向，故其读取为 $2\delta\{t+\operatorname{Re}\langle\eta,v\xi\rangle\}/(1+\delta^2)$。将它和(163.3)代入(162.2)，约去共同正因子，再只对固定向量范数令 $\delta\downarrow0$。由于 $\mathfrak p_\eta(q\xi)=0$、$\mathfrak p_\eta(p\xi)=p\xi$，得到

$$
\begin{aligned}
2|r|\left|t+\operatorname{Re}\langle\eta,v\xi\rangle\right|
\le{}&\|\mathfrak p_\eta((Z+g)\xi)-rtp\xi\|\\
&+\|\mathfrak p_\eta((Z-g)\xi)+rtp\xi\|.
\end{aligned}
\tag{163.4}
$$

这里一般没有 $Z\xi=v\xi$，也不需要它；共同 $Z$ 只在下一步两份一次项中相消。

记 $w=p\xi$、$z_\pm=\mathfrak p_\eta((Z\pm g)\xi)$，以及实数

$$
A_\xi=\operatorname{Re}\langle\eta,v\xi\rangle,\quad
B_\xi=\operatorname{Re}\langle w,g\xi\rangle,\quad
\epsilon=\operatorname{sgn}(r).
\tag{163.5}
$$

$w$ 为单位向量，且 $\operatorname{Re}\langle\eta,w\rangle=0$。150.3的范数一次项给：在(163.4)取 $t=L\to+\infty$，右侧减 $2|r|L$ 的极限是

$$
-\epsilon\operatorname{Re}\langle w,z_+\rangle
+\epsilon\operatorname{Re}\langle w,z_-\rangle=-2\epsilon B_\xi,
$$

左侧相应极限是 $2|r|A_\xi$。取 $t=-L\to-\infty$，两侧相应极限分别为 $2\epsilon B_\xi$ 与 $-2|r|A_\xi$。共同 $Z$ 在这两个差式里准确相消。两端一起给

$$
|r|A_\xi=-\epsilon B_\xi,\qquad
r\operatorname{Re}\langle\eta,v\xi\rangle
=-\operatorname{Re}\langle p\xi,g\xi\rangle.
\tag{163.6}
$$

这一步明确包括 $r<0$。由(163.2)，等价于

$$
\operatorname{Im}\langle\eta,g\xi\rangle
=r\sigma\operatorname{Re}\langle\eta,v\xi\rangle.
\tag{163.7}
$$

先取 $(p,q)=(e,j)$，令 $A=\langle j\xi,v\xi\rangle,B=\langle j\xi,g\xi\rangle$。再取 $(p,q)=(j,-e)$，此时 $\eta'=-e\xi=i\sigma j\xi$，相应二次读取是 $A'=-i\sigma A,B'=-i\sigma B$。两份(163.7)分别给 $\operatorname{Im}B=r\sigma\operatorname{Re}A$ 和 $-\sigma\operatorname{Re}B=r\operatorname{Im}A$，故

$$
B=ir\sigma A,\qquad
\langle j\xi,(g-ir\sigma v)\xi\rangle=0.
\tag{163.8}
$$

令 $F_\sigma=(I+\sigma Q)/2$、$P_\pm=(I\pm h)/2$，只用于数学表示。对固定算子 $F_\sigma P_-j(g-ir\sigma v)P_-F_\sigma$ 使用150.8的普通复极化，由(163.8)对全部向量成立，遂得该算子为零。$j$ 将 $F_\sigma P_-H$ 酉地送到 $F_\sigma P_+H$，于是

$$
F_\sigma P_+gP_-F_\sigma
=ir\sigma F_\sigma P_+vP_-F_\sigma.
\tag{163.9}
$$

反向块由自伴性为其伴随，准确带相反的 $i$ 号。$Q$ 中央排除跨 $\sigma$ 块；因此两份谱空间共同给 $P_{\rm tr}g=irQhv=rTv$。空谱块无须选择向量，某份负空间为空时 $j$ 的酉对应也使其正空间为空。忠实性返回原元素，得到(163.1)。所有极限都只作用于固定旧值的显式标量或向量式。∎

## 追加锚（本行以下为增补区）

## 164. 同一份原 PB 给残余的真实反交换关系

**定理 164.1（外层投影的实际消费）。** 对任意实 $\mu,\lambda$ 和原 $v\in V_h$，固定

$$
\begin{gathered}
c=\mu u+\lambda h,\quad x=c+v,\quad
k=hc=\lambda u+\mu h,\\
g=D(h,x)=Tv+\rho,\qquad
\rho=P_{\rm com}g\in E,\quad h\rho=\rho h.
\end{gathered}
\tag{164.1}
$$

这里的分解由150.1给出。则同一实际旧输出的残余满足

$$
\boxed{v\circ\rho=0.}
\tag{164.2}
$$

证明。$\mu=0$ 时，前卷18.1对 $h\circ x=\lambda u$ 给 $h\circ g=0$，即152.1的完整旧值 $g=Tv$，故 $\rho=0$。以下取 $\mu\ne0$，只用 $D(h,k)=0$ 的同轴原零值。在完整原PB中取 $(a,b,z)=(h,x,k)$，则

$$
\begin{aligned}
\nu&=g-c,&\omega&=k,\\
(b+\nu,z+\omega)&=(v+g,2k),&
(b-\nu,z-\omega)&=(2c+v-g,0).
\end{aligned}
\tag{164.3}
$$

负外层第二标签确实为原零标签，其旧值由P2为零。$k^2=c^2$、$x\circ c=c^2+\mu v$，故PB及反对称性准确给

$$
\begin{aligned}
D(v+g,2k)&=-2x\circ(g-c)-2k^2
=-2x\circ g+2\mu v,\\
\boxed{D(2k,v+g)=2x\circ g-2\mu v.}
\end{aligned}
\tag{164.4}
$$

此时 $v+g$ 尚含 $\rho$，未被当成横向输入。对同一个左侧旧值用163.1，参数一一对应为

$$
s=2\lambda,\qquad r=2\mu,\qquad y=v+g.
$$

于是

$$
P_{\rm tr}D(2k,v+g)
=2\mu T P_{\rm tr}(v+g)
=2\mu T(v+Tv)=2\mu(Tv-v).
\tag{164.5}
$$

另一方面，展开的只是已知Jordan乘法。由 $h\circ Tv=0$、$v\circ Tv=0$，有

$$
x\circ g=\mu Tv+c\circ\rho+v\circ\rho.
\tag{164.6}
$$

$c\circ\rho$ 与 $h$ 交换，$v\circ\rho$ 与 $h$ 反交换，因而(164.4)右端的横向投影是 $2\mu(Tv-v)+2v\circ\rho$。与(164.5)比较便得(164.2)。这条关系来自两份完整旧外值的PB，随后确由新投影公式消费；没有定义外层候选值来替换它。∎

## 165. 含实际残余的相对中心与全部不可约读取

**引理 165.1（固定元素的P2排零）。** 在161.1的同一环境与实际 $h,Q$ 下，设固定原 $v,\rho$ 满足

$$
h^2=u,\quad hv=-vh,\quad h\rho=\rho h,\quad v\rho=-\rho v,
\tag{165.1}
$$

且固定元素 $g=Tv+\rho=iQhv+\rho$ 对原输入 $(h,x)$、$x=\mu u+\lambda h+v$ 满足全部环境数学态读取的原P2。则 $\rho=0$。这里 $\mu,\lambda$ 为任意实数，包括零；不假设 $v^2$ 全局中央、标量、可逆或有限谱。

证明。零代数无须选态。其余情形定义

$$
w=h\rho,\qquad\mathcal K=C^*(u,Q,h,v,\rho)\subset\mathcal A.
\tag{165.2}
$$

$w$ 自伴。由(165.1)，

$$
wv=h\rho v=-hv\rho=vh\rho=vw.
$$

它也与 $h,\rho,Q$ 交换，所以 $w\in Z(\mathcal K)$。另有 $hv^2=v^2h$、$\rho v^2=v^2\rho$，而 $v^2$ 与 $v,Q$ 交换，故

$$
\boxed{h\rho,\ v^2\in Z(\mathcal K).}
\tag{165.3}
$$

这里的中心只属于含这份实际 $\rho$ 的 $\mathcal K$，未提升到整个 $\mathcal A$ 的中心；把 $\rho$ 明列为生成元，正是为了不预付旧 $D$ 的任何输出闭合。

取 $\mathcal K$ 的任意非零不可约表示 $\pi$。由Schur引理，写

$$
\pi(Q)=\sigma I,\quad\pi(v^2)=b^2I,\quad
\pi(h\rho)=mI,\qquad
\sigma\in\{1,-1\},\ b\ge0,\ m\in\mathbb R.
\tag{165.4}
$$

令 $H=\pi(h),V=\pi(v)$，则

$$
H^2=I,\quad HV=-VH,\quad V^2=b^2I,\quad
\pi(\rho)=mH.
\tag{165.5}
$$

若 $b=0$，自伴性给 $V=0$。像代数只由 $H$ 与标量生成，是交换的；不可约性使它为一维，$H=\pm I$。于是 $\pi(x)=\mu I+\lambda H$ 亦为标量。其唯一态拉回 $\mathcal K$ 并延拓到 $\mathcal A$，原 $(h,x)$ 的Gram为零，P2给 $m^2=0$，所以 $m=0$。这个分支也覆盖 $v=0$、$\mu=0$、$\lambda=0$ 的全部交会端点。

设 $b>0$，只在表示中定义

$$
E_0=V/b,\qquad J_0=i\sigma HE_0.
\tag{165.6}
$$

$H,E_0,J_0$ 为两两反交换、自伴且平方为 $I$ 的三轴。为确认读取是真正的二阶像，令 $P_\pm=(I\pm H)/2$。$E_0$ 酉地交换两份非零的 $P_\pm$ 空间；以此识别两份空间后，$H$ 是 $\operatorname{diag}(I,-I)$，$E_0$ 是两个非对角单位。故它们生成的像准确为 $M_2(\mathbb C)\otimes I_{\mathcal L}$。不可约性使重数空间 $\mathcal L$ 为一维，否则其上任一非平凡投影都在交换子中。因此当前像确为不可约 $M_2(\mathbb C)$，并且

$$
\pi(x)=\mu I+\lambda H+bE_0,\qquad
\pi(g)=bJ_0+mH.
\tag{165.7}
$$

对每个单位实Bloch向量 $(n_x,n_y,n_z)$，二阶密度 $\tfrac12(I+n_xE_0+n_yJ_0+n_zH)$ 为正且迹一，其态分别读取三轴为 $n_x,n_y,n_z$。将此态拉回 $\mathcal K$，再由共同单位C*子代数的态延拓取得 $\mathcal A$ 上的态。该态所读的仍是同一份原 $h,x,g$，包括它们的原平方和原Jordan乘积。

具体地，

$$
\begin{aligned}
\pi(x^2)&=(\mu^2+\lambda^2+b^2)I+2\mu\lambda H+2\mu bE_0,\\
\pi(h\circ x)&=\lambda I+\mu H.
\end{aligned}
\tag{165.8}
$$

所以原P2准确成为

$$
\boxed{(bn_y+mn_z)^2
\le b^2+2\mu b n_x+\mu^2(1-n_z^2)
=(b+\mu n_x)^2+\mu^2n_y^2.}
\tag{165.9}
$$

最后一个等号使用 $n_x^2+n_y^2+n_z^2=1$。$\lambda$ 消失来自(165.8)的显式Gram相消，不是对未知响应使用剪切或平移不变性。

若 $0<b<|\mu|$，取

$$
n_x=-b/\mu,\qquad n_y=0,\qquad
n_z=\sqrt{1-b^2/\mu^2}>0.
\tag{165.10}
$$

右侧为零，故 $m=0$，包括 $\mu$ 的两种符号。

若 $b=|\mu|>0$，对 $0<z<1$ 取

$$
n_x=-\operatorname{sgn}(\mu)\sqrt{1-z^2},\quad n_y=0,\quad n_z=z.
$$

(165.9)给

$$
m^2z^2\le b^2(1-\sqrt{1-z^2})^2,\qquad
|m|\le\frac{bz}{1+\sqrt{1-z^2}}.
\tag{165.11}
$$

只令固定标量表达式的 $z\downarrow0$，得到 $m=0$；没有把端点态或极限输入送入旧 $D$。

若 $b>|\mu|$，置 $q_0=\sqrt{1-\mu^2/b^2}>0$。反设 $m\ne0$，对 $0<z<q_0$ 取

$$
n_x=-\mu/b,\quad
n_y=\operatorname{sgn}(m)\sqrt{q_0^2-z^2},\quad n_z=z.
$$

从(165.9)减去 $b^2n_y^2$，准确得到

$$
2b|m|\sqrt{q_0^2-z^2}\,z+m^2z^2
\le(b^2-\mu^2)z^2.
\tag{165.12}
$$

除以正 $z$，令 $z\downarrow0$，左侧趋于 $2b|m|q_0>0$，右侧趋于零，矛盾。$\mu=0,b>0$ 也在这个分支，$q_0=1$；没有遗漏零偏移。至此全部不可约表示都有 $m=0$，即 $\pi(\rho)=0$。不可约表示分离C*元素，故 $\rho=0$。∎

证明所用成熟接口的准确出处为Blackadar，[*Operator Algebras*](https://www.bruceblackadar.com/Mathematics/Cycr.pdf)，II.6.1.8（不可约表示的交换子为 $\mathbb CI$）、II.6.3.1（子代数／算子系统的态延拓）、II.6.3.3与II.6.3.5（纯态取范数及态分离），以及II.6.4.9（不可约表示取范数，因而分离元素）。前卷18、72–73已有同类局部C*读取背景；(165.6)–(165.12)在此给出当前固定元素所需的完整计算。这些文献只提供读取工具，不提供新的旧响应身份。全程没有定义商上的 $D$，也没有把 $\pi(D(a,b))$ 写成某个新响应作用在 $\pi(a),\pi(b)$ 上。

## 166. 同时单位偏移、轴偏移与任意实首槽强度

**定理 166.1（同一原轴行的完整受限混合值）。** 在161.1下，对全部实 $R,\mu,\lambda$ 及任意原 $v\in V_h$，

$$
\boxed{D(Rh,\mu u+\lambda h+v)=RTv.}
\tag{166.1}
$$

两种实偏移可同时非零；$v$ 的平方允许非中央、非可逆、奇异或连续谱，范数不受小窗口限制。

证明。先取 $R=1$。150.1给164.1的分解；164.1消费实际 $\mathrm{PB}(h,x,k)$ 得 $v\circ\rho=0$。165.1对这份固定旧输出使用原P2，得到 $\rho=0$，故 $D(h,x)=Tv$。$\mu=0$ 的已付152.1及 $v=0$ 的同轴零行也与此一致。

$R=0$ 时原P2与评价分离给 $D(0,x)=0$。现设 $R\ne0$，固定同一实际旧值

$$
g=D(Rh,x)=RTv+\rho,\qquad\rho=P_{\rm com}g,
\tag{166.2}
$$

其中分解用163.1的 $s=0,r=R$，不是假设第一槽齐次。若 $\mu=0$，$(Rh)\circ x=R\lambda u$；前卷18.1给 $(Rh)\circ g=0$。由于 $R\ne0$ 且 $h\circ g=h\rho$、$h^2=u$，便有 $\rho=0$。

若 $\mu\ne0$，仍令 $c=\mu u+\lambda h,k=hc$，只在原PB中取 $(a,b,z)=(Rh,x,Rk)$。同轴零行给 $D(Rh,Rk)=0$；完整位移与外层为

$$
\begin{aligned}
\nu&=g-R^2c,&\omega&=Rk,\\
(b+\nu,z+\omega)&=((1-R^2)c+v+g,2Rk),\\
(b-\nu,z-\omega)&=((1+R^2)c+v-g,0).
\end{aligned}
\tag{166.3}
$$

负外层为零。用 $x\circ c=c^2+\mu v$、$k^2=c^2$，再用反对称性，准确得到

$$
\boxed{D(2Rk,(1-R^2)c+v+g)=2x\circ g-2R^2\mu v.}
\tag{166.4}
$$

左侧用163.1，完整参数为 $s=2R\lambda,r=2R\mu,y=(1-R^2)c+v+g$，横向投影是

$$
2R\mu T(v+RTv)=2R\mu Tv-2R^2\mu v.
\tag{166.5}
$$

右侧因 $x\circ g=R\mu Tv+c\circ\rho+v\circ\rho$，横向投影是(166.5)加 $2v\circ\rho$，故仍得 $v\circ\rho=0$。这一步包含负 $R$ 及 $R^2=1$ 的端点，不以第二标签预先横向为条件。

最后，对全部数学态的原P2有

$$
|\phi(g/R)|^2\le B_\phi(h,x),\qquad
B_\phi(Rh,x)=R^2B_\phi(h,x).
\tag{166.6}
$$

这里除的是固定元素和显式Gram，不是改写 $D(Rh,x)/R$ 为 $D(h,x)$。对 $g/R=Tv+\rho/R$ 用165.1，得到 $\rho/R=0$。所有分支共同证明(166.1)。∎

## 167. 已识别外值、仿射横向整行与两层旧调用

**推论 167.1（同一PB外值的完整识别）。** 对164.1的实际输入，(164.4)的外值完整为

$$
\boxed{D(2\lambda u+2\mu h,v+Tv)=2\mu(Tv-v).}
\tag{167.1}
$$

更一般地，(166.4)的同一个实际外值是

$$
D\bigl(2R\lambda u+2R\mu h,(1-R^2)(\mu u+\lambda h)+v+RTv\bigr)
=2R\mu Tv-2R^2\mu v.
\tag{167.2}
$$

证明。分别将166.1已识别的同一内值 $g=Tv$、$g=RTv$ 代回(164.4)、(166.4)。$x\circ Tv=\mu Tv$，所以得到所写完整值。即使(167.2)的第二标签带交换部分，识别依据也只是该次实际PB的精确标签；它不被扩张到任意混合第二输入。$R=0$ 时两边均零。∎

**定理 167.2（仿射首标签的原横向整行）。** 对全部实 $s,r$ 和任意原 $w\in V_h$，

$$
\boxed{D(su+rh,w)=rTw.}
\tag{167.3}
$$

证明。取原元素 $v=(w-Tw)/2\in V_h$，由 $T^2=-I$，有 $v+Tv=w$、$Tv-v=Tw$。在(167.1)准确置 $\lambda=s/2,\mu=r/2$，得到(167.3)。$r=0$ 与原单位行一致，$w=0$ 与零输入零值一致，$s=0$ 与166.1的 $\mu=\lambda=0$ 分支一致。这是同一外值已经认回后的消费者，不从163.1的投影值直接删掉未知交换块。∎

**推论 167.3（实际两层原响应）。** 对166.1的每个实际原输入，任意实 $s,r,R$ 都有

$$
\begin{gathered}
D(Rh,\mu u+\lambda h+v)=RTv\in E\cap V_h,\\
D\bigl(su+rh,D(Rh,\mu u+\lambda h+v)\bigr)=-rR v.
\end{gathered}
\tag{167.4}
$$

特别

$$
\boxed{D(h,D(h,\mu u+\lambda h+v))=-v,\qquad
D(Rh,D(Rh,\mu u+\lambda h+v))=-R^2v.}
\tag{167.5}
$$

证明。内层由166.1识别为同一个原 $RTv$，外层对这份原横向元素用167.2，得到 $rT(RTv)=-rRv$。$T$ 的实线性来自其有限Jordan表达式，并非旧 $D$ 的全域线性前件。零值、负强度和全部偏移端点均包含在等式中。内外标签确实都在不完备原 $E$，但这些数学调用不供应物理准备、可控逆过程或实际双向返回。∎

## 168. 原系数矩阵中的两份对角残余真正为零

**推论 168.1（任意原非交换横向系数的旧矩阵值）。** 使用140.1、142.1、153.2的同一原坐标与旧 $\widetilde D$。对任意原 $z\in\mathfrak b$ 及实 $R,\mu,\lambda$，有

$$
\boxed{
\widetilde D\!\left(
RH,\begin{pmatrix}(\mu+\lambda)u&z\\z^*&(\mu-\lambda)u\end{pmatrix}
\right)
=R\begin{pmatrix}0&iz\\-iz^*&0\end{pmatrix}.}
\tag{168.1}
$$

证明。令 $v$ 为该矩阵的原非对角部分之逆像，它属于原 $V_h$。140.1的同一坐标把 $\mu u+\lambda h+v$ 送到所写矩阵；153.8把 $Tv$ 送到右侧的 $R=1$ 矩阵。对166.1整体施加该坐标即得结论。这里的 $u$ 为系数单位，$H=\operatorname{diag}(u,-u)$；$z$ 可以是原不完备且非交换的系数域元素，不要求标量或有限谱。∎

因此153.4的 $r_+(A),r_-(A)$ 在 $a=(\mu+\lambda)u,d=(\mu-\lambda)u$ 这个实际域上都为零。所排除的是同一个旧输出的残差，不是候选 $B_\star$ 的残差；166.1也准确给 $D(Rh,x)=B_\star(Rh,x)$，因为 $B_\star(Rh,x)=iRQhv$。这种一致性只在陈述的输入域成立。

## 追加锚（本行以下为增补区）

## 169. 非零缺陷必有有限原预算见证

**推论 169.1（仿射投影的有限反事实）。** 若163.1对某个固定原 $x,s,r$ 失败，则存在有限原标签及有限份原PB/P2构成矛盾见证；不需要对旧 $D$ 取输入极限，也没有统一有限测试表的结论。

证明。$r=0$ 的失败直接违反原单位行。$r\ne0$ 时，由 $Q$ 的中央性、伴随块与150.8的复极化，某份单位 $\xi$ 和两种实际锚之一必使(163.6)失败。沿用163.5，记

$$
\varepsilon=|r|A_\xi+\operatorname{sgn}(r)B_\xi\ne0.
\tag{169.1}
$$

令 $F(t)$ 为(163.4)右侧减左侧。163.6之前的两个显式范数极限准确给

$$
\lim_{L\to+\infty}F(L)=-2\varepsilon,\qquad
\lim_{L\to+\infty}F(-L)=2\varepsilon.
\tag{169.2}
$$

据 $\varepsilon$ 的符号，先选一个有限正或负 $t$，使 $F(t)<0$。固定该 $t$，163.3的固定向量范数在 $\delta=0$ 连续，故选有限正 $\delta$ 后162.2仍严格失败。再固定这份向量态，162.6给除以 $|\alpha|$ 后的显式极限，所以存在有限大 $|\alpha|$ 使162.5严格失败。最后这份不等式只来自同一次PB和同一读取的两张原P2；其162.3完整外层都在原 $E$。参数依赖具体失败输出，不提供统一资源上界。∎

**推论 169.2（相对中心排零的有限反事实）。** 在165.1的反交换条件已经成立后，若固定 $\rho\ne0$，存在一个数学态对同一原 $(h,x,g)$ 的P2严格给出矛盾。每个见证的Bloch参数均可取有限值。

证明。不可约表示分离给一份 $\pi(\rho)=mH\ne0$，故 $m\ne0$。$b=0$ 时是165.5之后的一维零预算。$0<b<|\mu|$ 时，直接用(165.10)的零预算且 $mn_z\ne0$。

$b=|\mu|>0$ 时，选任一 $0<z<\min(1,|m|/b)$；(165.11)右侧严格小于 $bz<|m|$，即为有限反例。$b>|\mu|$ 时，置 $q_0=\sqrt{1-\mu^2/b^2}$，选

$$
0<z<\min\left(\frac{q_0}{2},\frac{b|m|q_0}{b^2-\mu^2}\right).
\tag{169.3}
$$

则(165.12)除以 $z$ 后的左侧大于 $b|m|q_0$，右侧小于这个数，严格矛盾。$\mu=0$ 仍在该分支。将相应态拉回并延拓，便是原输入及同一原输出的P2见证；$R\ne0$ 时166.6乘回 $R^2>0$ 仍为原 $(Rh,x,g)$ 的严格矛盾。没有把 $V/b$、谱根、无限参数或新态当作旧 $D$ 的输入或物理准备。∎

## 170. 原关系对应、较短几何与一般对角目标的三处缺口

**定义 170.1（承重接口与实际增量）。** 161–169的条件结论归为 $\texttt{repo-derived}$ 综合，不作历史优先权或全仓／全球文献穷尽主张。各个实质接口的供应及真实消费者为：

| 供应 | 准确支付 | 真实消费者 |
| --- | --- | --- |
| 前卷16.1–16.2，本卷130.1、137.1 | 同一弱JC包含、准确锥、原域有限Jordan运算及原单位／零行 | 所有原标签的合法性及环境态读取原P2 |
| 前卷76.1–77.1 | $D(su+rh,tp+\alpha n)=rtq$ 的完整有限四维锚值 | 162.3的一次PB，其未知目标 $g$ 保持固定 |
| 133.1–134.1，149.3、150.3、150.8 | 已有横向 $T$、全局中央 $Q$、任意输出的Gram、范数一次项和复极化 | 163.1对任意第二输入的仿射首标签投影 |
| 163.1与实际 $\mathrm{PB}(h,x,hc)$ | 对同一个 $D(2k,v+g)$ 的投影，给 $v\circ\rho=0$ | 含实际 $\rho$ 的读取代数之相对中心165.3 |
| 全部原P2及Blackadar的读取接口 | 全部不可约读取中的165.9与三个幅度分支 | 同一实际残余为零，得到166.1 |
| 163.1与实际 $\mathrm{PB}(Rh,x,Rhc)$ | 不假设首槽齐次而识别全部实 $R$ | 166.1及其零值、负值和端点 |
| 完整166.1及同一次原PB | 167.1–167.2的完整旧外值 | $v=(w-Tw)/2$ 接回167.3的原横向整行 |
| 166.1、167.3及原 $T^2=-I$ | 内层输出仍是原横向元素 | 167.4–167.5的实际两层原响应 |
| 140.1、142.1与166.1 | 同一原矩阵坐标保留输入和旧输出 | 168.1的两个实际旧对角块为零 |

前卷18.1的标量交叠正交、77.1的完整标量窗、本卷133.1的横向行及152.1的单轴偏移均直接复用；成熟实Gram、Hilbert范数、固定算子极化、态延拓与不可约表示分离不计作新增理论。新的连接是163.1允许读取仍含实际残余的外层，164.1使残余与 $v$ 反交换，165.1再让原P2排除这份残余。它没有新增数学正性公理或输出闭合公理。

[《原多项式零响应与Cayley域边界》51–58节](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)已在标量端点Hermitian多项式原域识别全部混合旧值，包括任意两个标量多项式偏置。其51.2通过同一多项式第三标签在两处取得不同约束，再以实际输出的多项式恒等原理连接；零端值对由真实单位接回。这与此处共有“先读实际外层，再回代同一PB”的方法关系，但对象和桥梁不同：该域的无迹部分在标量端点消失，不供应此处实际单位三轴；此处任意原横向输入可带非交换系数，不输入有限多项式性。这里建立的是含实际残余代数的相对中心，然后用全部不可约表示分离；不以两处点值或多项式恒等原理代替该分离，也不重复证明51.2。

几何缩短可精确表为：四系数域仍是同一个 $H_2(\mathfrak b)$；横向块由 $Tv$ 固定以后，在实对角输入域 $c=\mu u+\lambda h$ 上，原先未识别的交换输出分量也被排除。局部二阶Bloch球只在165.3已经证明、并且选定一个不可约读取后出现，不把整个非交换系数空间说成一个普通三维球。简化的是这个实际域上少了一份待解的响应分量，完整原A1–A3、准确锥、P2及PB仍保留；没有减少独立公理数，也没有证明公理独立性、最小公理数或完整量子起源。

**定义 170.2（一般交换部分的具体未付接口）。** 对一般原 $c\in\operatorname{Com}_h$，目标仍为 $\rho_h(c+v)=0$。当前网络有三处明确缺口：

1. 原内值 $D(h,hc)=0$ 只在 $c=\mu u+\lambda h$ 由同轴零行供应。一般 $hc$ 不在该实二维轴片，不能先设它为零来删除PB位移。
2. 即使另行证明这个内值为零，PB给出的外层首标签 $2hc$ 一般不属于 $\mathbb Ru+\mathbb Rh$；163.1没有读取它的接口。因此(164.5)不能照搬。
3. 即使以后建立相应联合反交换关系，最后的P2化简165.8–165.9仍使用 $c=\mu u+\lambda h$ 的两个实系数。一般 $c$ 的算子系数与 $v,\rho$ 可不交换，既没有所写标量Gram，也没有已证的同一不可约二阶像；不能把输入边缘或点压缩的相同数值冒充平方和乘积的共同读取。

所以一般 $D(h,c)=0$、$\rho_h(c+v)$ 与 $v$ 无关、一般交换或中央平移、全域分别可加及实双线性仍未证明。旧全域R、P3、全部有限旧复Gram、同一旧结合乘法、商下降、输入函数演算、输入连续性与完成延拓也未由这些受限行得到；无这份实际三轴、无轴、经典及奇数矩阵等原分支不由本证明覆盖。多项式卷的指定域完整结论各守其前件，不能据此把这些一般缺口改称已解。定理167.2的整行公式(167.3)只允许纯横向第二输入，定理166.1与定理167.2不授权任意两个混合输入的公式。这里没有满足完整P2/PB的反模型，故不作独立性或不可能性结论。

## 171. 七项量子消费者的全部原来源条件

**定义 171.1（复Hilbert、可观测量与叠加的来源）。** 完整保持145.1、155.1第1项与静态卷25.1第1行。139–140的 $\mathcal C\cong M_2(\mathcal B)$ 和成熟忠实Hilbert表示仍只给数学载体；166.1、167.3认回的是同一旧 $D$ 的指定原值域。若要把全域表示认作同一原响应的共同乘法，仍须全域 $D=B_\star$，或准确支付静态卷32.2、23.1所需旧双线性、P3和PB等入口。唯一原 $\Omega$、原 $E/S/D$、跨评价配对、具名且可取得的原标签、native、全部原词同一 $q,K,J$、parent/ready、合法控制及实际相干叠加准备，继续由静态卷8.3–8.4、14.2、25.1和三标签卷8.2–8.5、80.1承担。辅助 $Q$、数学纯态与矩阵坐标不制造准备，也不推出全 $B(H)$ 的像、原完备性或任意算子可取得／控制。

**定义 171.2（原态、效果、质量与完整Born菜单）。** 完整保持145.2、155.1第2项及静态卷25.1第2行。原评价、准确效果区间 $E\cap[0,u]$、原事件和接受归属必须属于同一个实际来源；只对实际完整菜单且 $m_\alpha=\alpha(u)>0$ 使用

$$
p_\alpha(e)=\alpha(e)/m_\alpha.
\tag{171.1}
$$

全部零、不等、次归一质量、原 $q$、中心权及中心经典混合、经典不等维块和静默部分均保留；零质量不作除法。原准备、共同根、抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度尺度、P9分支及独立 $W_e$、全部实际完整菜单、固定支持全质量和全部原中间切口，逐项仍取原合同。数学全部态、效果、二阶密度与165.9的Bloch读取不等于实际准备或菜单齐备，不改变原质量；一般无限维系数域也不被改成有限密度矩阵表。

**定义 171.3（native、真相关联合与张量）。** 完整保持145.3、155.1第3项、静态卷25.1第3行、53.1及单位桥95.2、116.1。全词同一 $K/J$、原交叉零和共同生成分离均须原来源。张量消费者仍要求同一个实际非零共同联合来源、旧局部乘法、满足原消费者局部全矩阵条件的忠实同向交换两腿、共同实现、联合生成与分离、所需重数、全部真正相关输入及全部中心对、经典和不等维块。系统与参考不能分别挑选后冒充一份共同生成；相同边缘、分别可达、数学张量表示或辅助 $Q$ 的两份谱空间都不能代替实际相关联合。$M_2(\mathcal B)$ 是单域数学因子描述，系数非交换本身不赋予物理子系统或真实参考身份；完整目标的无轴等其它原域保留。

**定义 171.4（typed CP与整台递归同源参考）。** 完整保持145.4、155.1第4项及静态卷25.1第4行。原未归一回溯

$$
\alpha_A(\beta_r b)=\alpha_B^r(b)
\tag{171.2}
$$

及每个合法typed前接／后接、反变合法复合、typed分区、全未来自然性和原箭头商下降，均取原合同。CP来自原过程比较或整台实际箭头的递归实际同源二元参考；整台箭头包括系统、整个环境、全部成功／失败／细记录／port／post-port输出，每个输出的所有仍合法未来都在量词内。系统腿与参考腿须共同真支持且忠实同向交换；三实际投影与各自支持内补、共同真实支持上的准确运输、全部相关正输入上的intertwining与夹界、每个所需有限递归深度和累计支持的完整实际链全部保留。支持内补不等于环境补。167.4的两个数学原调用不供应这些箭头、参考、联合运输或CP；143.2的一级序边界也未被升级。

**定义 171.5（整台仪器、Kraus、TP、更新与Lüders）。** 完整保持145.5、155.1第5项及静态卷25.1第5行。原二次Jordan夹心 $\mathcal U_a(b)=2a\circ(a\circ b)-a^2\circ b$ 只是数学接口。全部原输入运输、完整typed输出菜单、整台环境、全部成功／失败／细记录／port／post-port输出及各自所有仍合法未来、原接受端、真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词及其接受条件，全部须由原实现保留。TP需要完整单位分区；Lüders另需同一个完整输出的像内射线校准。更新只对正输出质量归一，零分支不删除。有限密度、迹类及算子Kraus公式仅在准确合格的原有限全矩阵域，或另已供应所需正规物理表示、指定前对偶与所需收敛并确实适用的域使用；一般正规子代数只给自身前对偶态及CP对偶。辅助 $V/b$、数学完成中的平方根、二阶态与旧响应识别不供应原平方根词、实际仪器或接受端。

**定义 171.6（全历史、全未来、真遗忘、真实双向返回与CountRead）。** 完整保持145.6、155.1第6项、静态卷8.4、25.1第6行及单位桥的全部原量词：所有合法顺序／自适应／并行历史、每个输出的每个仍合法未来、整个环境、全部细记录与泄漏、停止／拒绝／销毁、真正分组遗忘、同数两侧真实返回和同数逆向真实返回均不得删除。CountRead仍绑定读后同一原完整活动输入及其全未来返回；负提升两条活路的分别控制与相干聚合、具名分析词到原实际完整菜单和接受端的接线仍须原生构造。原 $B$ 的精确正生成与另名 $B_{\rm cl}$ 的闭正生成不混同，两者也不是系数代数 $\mathcal B$。无限历史、无限／非离散记录、可数可加、正常性及指定前对偶各取其原扩展来源。相同矩阵但不同原程序、实际读取顺序、原 $q$-零集与AC方向均保留。167.5的 $-v$ 是同一旧表的两层数学值，不是实际准备、活动ready接头、可取得逆程序或物理双向返回。

**定义 171.7（动力、物理钟、能量与共同正尺度）。** 完整保持145.7、155.1第7项及静态卷25.1第7行。若要使用旧响应动力 $\dot b=2D(H,b)/\hbar$，仍须同一旧全域乘法、保持可能不完备原域的流、实际相位及门序列、同一可逆一参数群、原物理钟、所需强连续酉实现、生成元定义域、Hamiltonian的能量解释、共同作用量、共同正 $\hbar$ 与共同仪器。原 $\sigma,t_0$、固定 $d$、固定域、resolvent与 $3s+r\le1$ 预算仍取该原合同的参数及量词，不与本组仿射标签参数混同。候选数学有界内导子不替代一般无界生成元。$\alpha,t,\delta,z$ 在证明中只选择有限数学读取，$R,s,r,\mu,\lambda$ 只给原实标签；它们不供应物理时间、控制成本、钟能量尺度或跨装置共同 $\hbar$。辅助 $Q$、数学指数、坐标和完成均不产生这些来源。

七项合同因此仍覆盖唯一原世界、全部原质量与完整菜单、真实相关联合和递归参考、整台仪器及环境记录、所有合法历史未来、真遗忘和真实双向返回、完整计数及物理钟和共同尺度。本文的数学条件结论不将这些来源前件视作已经实现。

## 172. 同一份旧残余消去的完整白话

**定义 172.1（实际接线、较短几何与适用边界的直观含义）。** 固定同一个原世界中确实存在的三根轴和同一张旧响应表。每个输入相对 $h$ 都有沿轴交换的部分和横向部分。已经认识的横向部分会被原响应转四分之一圈，写成 $Tv$；问题是加上单位偏移和轴偏移以后，同一份旧输出会不会偷偷多出两块对角残余。不能把分别已知的两种偏移公式直接拼起来，也不能另画一张标准表代替原表。这里用原三轴的四维小窗作两个真实锚：即使首标签同时带单位和轴分量，两个锚仍能在完整配平和同一读取的两张二表预算里，锁住任意第二输入所对应输出的横向块。共同的交换项没有提前删掉，它只在正反大锚的两份一次读数中抵消。随后把目标输出本身放进一次真实配平；这次配平的一条外层第二标签恰为零，另一条外层的首标签恰为刚刚能读取的实仿射轴。读回这份外层，就迫使目标残余与原横向输入反交换。此时才有资格缩小证明用的读取代数：它明确含有那一份实际残余，残余乘回轴和横向平方都在这个代数的中心里。在每个不可约读取中，它们成为两个实幅度，问题便落到真正的二阶矩阵几何。若残余幅度非零，有的幅度区间直接遇到零预算，有的在饱和方向旁稍微转动就超预算，临界等号和零横向块也各有明确见证；每次矛盾都能用有限参数找到。因此那两块原残余确实为零，任意原横向输入同时加上任意实单位偏移、实轴偏移，送进原 $Rh$ 行，输出准确是 $RTv$。再把已认回的旧值代回同一次配平，还能认回带单位偏置首标签对所有纯横向输入的整行；把内层真实输出再送进原 $h$ 行，第二次值就是 $-v$。这对原域不完备、横向平方不中央或带连续谱的情况同样适用，因为证明没有要求把谱根、商元素或极限标签送进旧表。更大的难点仍是一般非标量交换输入：它的内值、外层首标签和最后的共同预算都还缺桥，不能由这些受限公式拼成任意两混合输入的全域公式。几何上少掉的是已陈述域内的一份未知响应分量，原公理及七项实际来源条件一项也没有少；数学态、二阶坐标和两层负号没有替原世界造出准备、整台仪器、真正联合、全未来返回、物理钟或共同作用量。

161–172均为带完整前件的纸面定义、条件定理及证明，不冒领Lean kernel核验、摄入、冻结、独立评审结论或实际量子来源的完成。

## 追加锚（本行以下为增补区）

## 173. 全交换类与混合原值的共同前件

**定义 173.1（同一原域、实际框架与固定旧值）。** 完整保持130.1、137.1、
147.1和157.1的同一原 $(E,C,u,N,\mathcal P,S,D)$、A1–A3、准确锥、
全部原正P2和完整原PB。原 $E$ 可以不完备、无限维、不可分且有非交换系数；
旧 $D:E^2\to E$ 始终是同一个总映射。只沿已付的忠实含单位JC包含
$E\subset X\subset\mathcal A_{\rm sa}$ 计算已知乘法，$\overline E=X$，
不要求 $X=\mathcal A_{\rm sa}$。固定实际原框架 $h,e,j=D(h,e)$，
$h^2=e^2=j^2=u$，三轴两两Jordan正交；134.1的辅助
$Q=ihej$ 中央、自伴且 $Q^2=u$。不增加别的实际轴。

本节以下以 $\mathcal U_a=2L_a^2-L_{a^2}$ 表示一般Jordan二次表示，
避免与147.3只对单位平方轴写的 $U_h=2L_h^2-I$ 混淆。
在原JC环境中 $\mathcal U_a(y)=aya$。对每个原 $x$ 固定

$$
\begin{gathered}
P_h^\pm=\tfrac12(I\pm U_h),\qquad
c=P_h^+x,\quad z=P_h^-x,\quad x=c+z,\\
t=[L_j,L_e]z=iQhz,\qquad d=D(h,x),\qquad r=d-t,\qquad
k=h\circ x=h\circ c=hc.
\end{gathered}
\tag{173.1}
$$

133.1与150.1供应

$$
[h,c]=[h,r]=0,\quad hz=-zh,\quad ht=-th,\quad
D(h,z)=t,\quad t^2=z^2,\quad z\circ t=0,\quad k^2=c^2.
\tag{173.2}
$$

$c,z,t,d,r,k$ 都是原有限Jordan表达式或真正的旧输出；环境式中的
$Q$ 本身不取得原标签身份。尤其 $r=\rho_h(x)$ 是153.1的同一残差。
不先给旧 $D$ 可加、一般齐次、连续、可测、商下降或完成延拓。

**定义 173.2（同一读取与原配平）。** 对任意数学正实泛函 $\phi$，沿用123.2

$$
\begin{gathered}
B_\phi(a,b)=\phi(a^2)\phi(b^2)-\phi(a\circ b)^2,\qquad
|\phi D(a,b)|^2\le B_\phi(a,b),\\
\nu=D(a,b)-a\circ q,\qquad \omega=a\circ b+D(a,q),\\
D(b+\nu,q+\omega)-D(b-\nu,q-\omega)
=-2b\circ\nu-2q\circ\omega.
\end{gathered}
\tag{173.3}
$$

每对输出比较共用同一个 $\phi$。准确锥接口使环境态、正延拓及正二次
读取可以如此读原表；它们不是实际准备。P2的左侧是输出均值的平方，
不是 $\phi(D(a,b)^2)$。取比例输入直接得

$$
D(a,\lambda a)=D(a,0)=0\qquad(a\in E,\ \lambda\in\mathbb R).
\tag{173.4}
$$

下一定理只需150.1的较小部分

$$
[h,c]=0\quad\Longrightarrow\quad[h,D(h,c)]=0.
\tag{173.5}
$$

它不另假设标量行，也不假设 $[c,D(h,c)]=0$。所有完成、谱、支撑、根和
逆元仅用于已知乘法及数学读取，从不作为新的 $D$ 输入。

## 174. 原交换第二输入的整个零行

**定理 174.1（全部原 $h$-交换类）。** 在173.1的原背景下，对每个原
$c\in E$，

$$
\boxed{[h,c]=0\quad\Longrightarrow\quad D(h,c)=0.}
\tag{174.1}
$$

结论包含不定号、非中央平方、无限谱及不完备原域。关于这条旧行的额外
响应信息只用173.5；证明是[原多项式卷](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)
4.2的定点角局部化，不将角压缩误当成全域Jordan同态。

证明。固定原 $c$ 与 $d_0=D(h,c)$，二者都与 $h$ 交换。零代数直接成立。
对 $\epsilon=\pm1$ 置

$$
p=\frac{u+\epsilon h}{2},\qquad
\kappa(v)=\mathcal U_p(v)=pvp,\qquad
Y=\mathcal U_pX,\quad E_p=\mathcal U_pE,\qquad
B=\kappa(c),\quad H=\kappa(d_0).
\tag{174.2}
$$

$p=0$ 的角直接贡献零。其余 $Y$ 是单位为 $p$ 的JB代数，$E_p$ 是
$Y$ 中范数稠密的原Jordan子代数。$p$ 和 $\mathcal U_p$ 本身是有限原
Jordan表达式，所以 $E_p\subset E$，没有添加标签。

先限定压缩的乘法用途。$\kappa$ 对全部 $X$ 正，但一般不保乘法。若
$v$ 与 $h$ 交换，它在 $p,u-p$ 两块间没有交叉项，故对任意 $w\in X$

$$
\kappa(v^2)=\kappa(v)^2,\qquad
\kappa(v\circ w)=\kappa(v)\circ\kappa(w).
\tag{174.3}
$$

第二式只要求因子 $v$ 为偶；$w$ 不必为偶。因此当原表的两个输入都偶时，
$\beta\kappa$ 对它的P2给

$$
|\beta\kappa D(v,w)|^2
\le\beta(\kappa(v)^2)\beta(\kappa(w)^2)
   -\beta(\kappa(v)\circ\kappa(w))^2
\tag{174.4}
$$

对每个 $Y$ 上正 $\beta$ 成立。若这样的第二输入 $\kappa(w)=0$，两份
输入平方规则使右侧为零；正泛函分离才给 $\kappa D(v,w)=0$。
没有关于非偶输入或一般输出的局部性断言。

先在证明内部支付有符号平方零行。实际上，只要此角的 $B$ 半定，便有
$H=0$。反设 $H\ne0$，在 $C^*(p,H)\subset p\mathcal A p$ 选择
$H$ 的非零谱值 $\tau$ 的字符，正延拓为角环境态，限制到 $Y$ 记作
$\beta$。它满足

$$
\beta(H)=\tau\ne0,\qquad
\beta((H-\tau p)^2)=0.
\tag{174.5}
$$

取真正原比例第三标签 $q_0=\tau h/2$，173.4给 $D(h,q_0)=0$。
PB $(h,c,q_0)$ 的两份完整外层及其角像为

$$
\begin{array}{c|c|c|c}
R_+&S_+&\kappa R_+&\kappa S_+\\ \hline
c+d_0-\tau u/2&\tau h/2+hc&B+H-\tau p/2&\epsilon(B+\tau p/2)
\end{array}
$$

及

$$
\begin{array}{c|c|c|c}
R_-&S_-&\kappa R_-&\kappa S_-\\ \hline
c-d_0+\tau u/2&\tau h/2-hc&B-H+\tau p/2&-\epsilon(B-\tau p/2).
\end{array}
\tag{174.6}
$$

由174.5，在半内积 $\beta(v\circ w)$ 中两组角输入分别成比例，故两张
实际P2的输出读取都为零。PB右侧准确是 $-2c\circ d_0$，因为
$h\circ(h\circ c)=c$；其角像为 $-2B\circ H$。
Schwarz和174.5给 $\beta(B\circ H)=\tau\beta(B)$，所以 $\beta(B)=0$。
若 $B$ 为正或负，谱序不等式
$0\le B^2\le\|B\|(\pm B)$ 给 $\beta(B^2)=0$。
原 $(h,c)$ 表的174.4于是给 $\tau^2\le0$，矛盾。

这个论证对每个原偶输入及每个非零角都成立。因此若原偶 $q$ 在两角中
分别半定，$D(h,q)=0$。特别对每个原偶 $v$ 和每个符号 $\eta=\pm1$，

$$
D(h,\eta v^2)=0.
\tag{174.7}
$$

两角可取不同符号，零角及半定元素的零支撑也已包含。这里只用了比例零值，
没有把两个偏移零值相减来拆未知 $D$。

现在消去一般 $B$ 的符号抵消。固定 $Y$ 的纯态 $\beta$，先设
$\beta(H)\ne0$。在 $M=Y^{**}$ 中取其最小支撑投影 $f$，
$\beta(f)=1$ 且 $\mathcal U_f(v)=\beta(v)f$。这些是原多项式卷4.2所用的
成熟支撑工具：Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，
Theorem4.4.3，以及Hamhalter，[*Pure states on Jordan algebras*](https://dml.cz/bitstream/handle/10338.dmlcz/133911/MathBohem_126-2001-1_7.pdf)，
§1，页82–83。$f$ 可以只在数学双对偶中存在；不要求原域有最小投影。
令

$$
K=\frac{\epsilon H}{2},\qquad \alpha=\beta(K)\ne0,
\qquad C_0=\frac{\mathcal U_K(f)}{\alpha}.
\tag{174.8}
$$

$\mathcal U_K$ 保正，故 $C_0$ 按 $\alpha$ 的符号半定。
将 $K=\alpha f+v+w$ 作Peirce $1,1/2,0$ 分解；同书Lemma2.6.3给

$$
\mathcal U_K(f)=\alpha^2 f+\alpha v+(v^2)_0,
\qquad C_0-K=(v^2)_0/\alpha-w\in M_0(f),
\qquad\beta((C_0-K)^2)=0.
\tag{174.9}
$$

同书Lemma4.1.9的有界集乘法联合强连续性和Theorem4.5.12的Kaplansky
密度，先在 $Y$ 中给 $|C_0|^{1/2}$ 的有界强逼近，再用 $E_p$ 在 $Y$ 中
的范数稠密性，给实际原 $v_i\in E_p$。可以取一致范数有界的网，使
$v_i\to|C_0|^{1/2}$ 强收敛。令

$$
q_i=\operatorname{sgn}(\alpha)v_i^2\in E_p\subset E,
\qquad \delta_i=2q_i-\epsilon H,
\qquad \eta_i=\beta(\delta_i^2)^{1/2}\longrightarrow0.
\tag{174.10}
$$

$q_i$ 一致有界并强趋于 $C_0$，最后一式由174.9得到。
网而非序列保留不可分情形。每个 $q_i$ 都是实际偶有符号平方，故174.7
已经给全原值 $D(h,q_i)=0$；没有对双对偶标签调用 $D$。

对每个 $i$ 真正使用PB $(h,c,q_i)$，保留两份实际外层

$$
\begin{aligned}
R_+^{(i)}&=c+d_0-h\circ q_i,& S_+^{(i)}&=q_i+hc,\\
R_-^{(i)}&=c-d_0+h\circ q_i,& S_-^{(i)}&=q_i-hc.
\end{aligned}
\tag{174.11}
$$

它们都偶，角像满足

$$
\kappa S_+^{(i)}-\epsilon\kappa R_+^{(i)}
=\kappa S_-^{(i)}+\epsilon\kappa R_-^{(i)}=\delta_i.
\tag{174.12}
$$

给第二向量加第一向量的实倍数不改Gram行列式。两张实际P2因此各给

$$
|\beta\kappa D(R_\pm^{(i)},S_\pm^{(i)})|
\le\beta((\kappa R_\pm^{(i)})^2)^{1/2}\eta_i
\le M_0\eta_i,
\tag{174.13}
$$

其中 $M_0<\infty$ 由固定 $B,H$ 及 $\sup_i\|q_i\|<\infty$ 给出。
PB右侧角像却始终固定为

$$
-2B\circ(H-\epsilon q_i)-2q_i\circ(\epsilon B)
=-2B\circ H.
\tag{174.14}
$$

故 $|\beta(B\circ H)|\le M_0\eta_i$，得到 $\beta(B\circ H)=0$。
这是用每份实际表估计一个固定元素；若固定读取非零，一个足够准确的
$q_i$ 就已矛盾，不是取 $D$ 的输入或输出极限。

还须处理纯态的零读取。如果 $\beta(H)=\beta(H^2)=0$，Schwarz直接给
$\beta(B\circ H)=0$。若 $\beta(H)=0$ 而 $\beta(H^2)>0$，取足够小非零实
$s$，使 $p+sH$ 正且在 $Y$ 中可逆。其二次表示是正锥自同构，所以

$$
\beta_s(y)=\frac{\beta(\mathcal U_{p+sH}y)}
 {\beta((p+sH)^2)}
\tag{174.15}
$$

仍是纯态。单生成演算给

$$
\beta_s(H)=\frac{2s\beta(H^2)+s^2\beta(H^3)}
 {1+s^2\beta(H^2)}\ne0
\tag{174.16}
$$

对充分小的非零 $s$ 成立。已经证明的情形使 $\beta_s(B\circ H)=0$；
$\mathcal U_{p+sH}=I+2sL_H+s^2\mathcal U_H$ 给 $\beta_s\to\beta$ 范数收敛。
故零读取情形同样成立。这里的逆元和纯态变形仅作用于已知 $Y$，
不向原域补根、补逆或补准备。纯态分离 $Y$，于是

$$
B\circ H=0,\qquad BH=-HB.
\tag{174.17}
$$

还不能由反交换直接断言 $H=0$。取第二份固定实际调用PB $(c,h,\epsilon c)$。
173.4给 $D(c,\epsilon c)=0$，反对称性给 $D(c,h)=-d_0$。
其完整正负外层是

$$
\begin{aligned}
a&=h-d_0-\epsilon c^2,&b&=\epsilon c+hc,\\
a_-&=h+d_0+\epsilon c^2,&b_-&=\epsilon c-hc.
\end{aligned}
\tag{174.18}
$$

四个输入都偶，$\kappa(b_-)=0$；174.4使 $\kappa D(a_-,b_-)=0$。
PB右侧为 $2h\circ d_0$，故两张固定原表准确给

$$
\begin{array}{c|c|c}
\text{第一输入角像}&\text{第二输入角像}&\text{同一旧输出角像}\\ \hline
\epsilon p&B&H\\
A:=\epsilon(p-B^2)-H&2\epsilon B&2\epsilon H.
\end{array}
\tag{174.19}
$$

这只是固定实际表的三个角像，不是在角上定义响应。

由174.17，$B^2$ 与 $H$ 交换。对交换C*代数
$C^*(p,B^2,H)\subset p\mathcal A p$ 的任一字符，写
$B^2\mapsto v\ge0,H\mapsto\tau$。若 $\tau=0$，所需谱关系已成立。
若 $\tau\ne0$，正延拓给一个GNS循环单位向量 $\xi$，满足
$B^2\xi=v\xi,H\xi=\tau\xi$。第一张表给 $|\tau|\le\sqrt v$，故 $v>0$。
反交换使 $\xi$ 与 $B\xi/\sqrt v$ 正交，二者张成的子空间对 $B,H$ 不变；
在这份二维空间上

$$
B=\sqrt v\,\sigma_x,\qquad H=\tau\sigma_z,\qquad
A=\epsilon(1-v)I-\tau\sigma_z.
\tag{174.20}
$$

对实单位向量 $(\cos\theta,\sin\theta)$ 读第二张固定表，置
$\gamma=\cos2\theta$。旧输出均值为 $2\epsilon\tau\gamma$，两输入作用向量
的面积绝对值为 $2\sqrt v\,|\epsilon(1-v)\gamma-\tau|$，所以

$$
|\tau\gamma|\le\sqrt v\,|\epsilon(1-v)\gamma-\tau|
\quad(-1\le\gamma\le1),\qquad |\tau|\le\sqrt v.
\tag{174.21}
$$

若 $v\ne1$，记 $a_0=\epsilon(1-v)\ne0$。
当 $0<|\tau|\le|a_0|$ 时取 $\gamma=\tau/a_0$，右侧零而左侧非零。
当 $|\tau|>|a_0|$ 时取 $\gamma=\operatorname{sgn}(a_0\tau)$，得
$|\tau|\le\sqrt v(|\tau|-|a_0|)$。$v<1$ 时立即矛盾；$v>1$ 时推出

$$
|\tau|\ge\frac{\sqrt v(v-1)}{\sqrt v-1}
=\sqrt v(\sqrt v+1)>\sqrt v,
$$

仍违反第一张表。因此非零 $\tau$ 只能在 $v=1$。字符分离，包括
$v=0,\tau=0$ 的退化情形，给

$$
(B^2-p)H=0.
\tag{174.22}
$$

最后消去 $v=1$ 上的残余。取真正原输出和标签

$$
k_0=D(b,a),\qquad g=b\circ a.
$$

174.19与反对称性给 $\kappa(k_0)=-2\epsilon H$，已知乘法给

$$
G:=\kappa(g)=2(B-B^3),\qquad GH=HG=0,\qquad A\circ H=-H^2.
\tag{174.23}
$$

这里用174.17和174.22；$g,a,b$ 都偶，但 $k_0$ 不要求偶。
实际PB $(b,a,0)$ 的两份外层完整保留为

$$
D(a+k_0,g)-D(a-k_0,-g)=-2a\circ k_0.
\tag{174.24}
$$

对任意 $Y$ 上正 $\rho$，使用正读取
$\phi=\rho\circ\mathcal U_H\circ\kappa|_E$。因为 $g$ 偶，174.3使两个
实际第二平方对角均为

$$
\phi(g^2)=\rho(HG^2H)=0.
$$

因此P2消去两份实际输出的 $\phi$ 读取，完全不需要压缩
$(a\pm k_0)^2$。右侧的混合项则由 $a$ 偶这一因子单独保证
$\kappa(a\circ k_0)=A\circ\kappa(k_0)$，即使 $k_0$ 不偶仍合法。
174.24遂给

$$
0=4\epsilon\rho\bigl(\mathcal U_H(A\circ H)\bigr)
=-4\epsilon\rho(H^4).
\tag{174.25}
$$

正泛函分离得 $H^4=0$，C*范数恒等式给 $H=0$。两角都如此，
$d_0$ 偶又给 $d_0=\kappa_+(d_0)+\kappa_-(d_0)=0$，定理得证。
从头至尾只有原有限标签及实际旧输出进入 $D$，没有完成响应、商响应、
输出局部性或 $D$ 连续性。∎

## 175. 一个实际第三标签的混合扇区预算

**推论 175.1（全部归一扇区读取）。** 对173.1的任意原 $x$，取任一非零
$p=(u+\epsilon h)/2$，以及 $Y=\mathcal U_pX$ 的任意归一态 $\beta$，
令 $\phi=\beta\circ\mathcal U_p|_E$。则

$$
\boxed{
2|\phi(c\circ r)|\le\sqrt{2\phi(z^2)}
\left[\sqrt{\phi((c+r/2)^2)}+
      \sqrt{\phi((c-r/2)^2)}\right].}
\tag{175.1}
$$

证明。原标签 $q=(h\circ r)/2=hr/2$ 与 $h$ 交换，所以174.1给
$D(h,q)=0$。实际PB $(h,x,q)$ 的两份完整外层是

$$
\begin{aligned}
R_+&=x+d-r/2=c+r/2+z+t,&S_+&=h(c+r/2),\\
R_-&=x-d+r/2=c-r/2+z-t,&S_-&=-h(c-r/2).
\end{aligned}
\tag{175.2}
$$

没有删除任何旧外层输出。置 $C_\pm=c\pm r/2$，$Z=\phi(z^2)$，
$V_\pm=\phi(C_\pm^2)$。扇区读取消去每个奇元素，并使偶、奇作用向量
正交。又 $(z\pm t)^2=2z^2$，故这些实际输入的准确读数为

$$
\begin{array}{c|c|c|c}
&\phi(R_\pm^2)&\phi(S_\pm^2)&\phi(R_\pm\circ S_\pm)\\ \hline
+&V_++2Z&V_+&\epsilon V_+\\
-&V_-+2Z&V_-&-\epsilon V_-.
\end{array}
\tag{175.3}
$$

因此 $B_\phi(R_\pm,S_\pm)=2ZV_\pm$，不是零预算。
PB右侧在原域准确为

$$
-2x\circ d+x\circ r-(hr)\circ(hc)
=-2x\circ d+z\circ r.
\tag{175.4}
$$

最后一步只用 $h$ 与 $c,r$ 交换。扇区读取中
$\phi(x\circ d)=\phi(c\circ r)$，因为 $c\circ t,z\circ r$ 奇且
$z\circ t=0$；$\phi(z\circ r)=0$。用同一 $\phi$ 对两份P2及175.4作
三角不等式，便得175.1。没有第二次纯态插值或未知响应极限。∎

**定义 175.2（同一固定首轴的实际加性缺陷）。** 174.1和133.1使

$$
r=D(h,c+z)-D(h,c)-D(h,z)=\delta_h(c,z).
\tag{175.5}
$$

这只是同一实际首轴及它的偶奇分解上的准确身份，不是把一般
$D(h,b+c)$ 拆开。175.1保留正 $z^2$ 预算，未使 $c\circ r$ 或 $r$ 为零，
也未给静态卷89所需全部原首标签、全部原三元组的缺陷中心性。

## 176. 不依赖交换零行的普遍湮灭与强制界

**定理 176.1（同一旧混合输出的支撑桥）。** 只用173.1–173.3，不用174.1，
对每个原 $x$ 及每个数学正实读取 $\phi$ 有

$$
|\phi(hr)|^2\le\phi(c^2)\,[\phi(u)+\phi(d^2)].
\tag{176.1}
$$

并且在同一原范数下

$$
\boxed{\|r\|^4\le(1+\|d\|^2)\|\mathcal U_r(c^2)\|
                  \le(1+\|x\|^2)\|\mathcal U_r(c^2)\|,}
\tag{176.2}
$$

$$
\boxed{\mathcal U_r(c^2)=0\ \Longleftrightarrow\ cr=0
                         \ \Longleftrightarrow\ r=0.}
\tag{176.3}
$$

$cr$ 只是在忠实环境中的乘积，$\mathcal U_r(c^2)$ 则是原有限Jordan
表达式，不要求 $cr$ 或任何根、逆成为新的 $D$ 输入。

证明。实际PB $(x,h,0)$ 的内值是 $D(x,h)=-d$、$D(x,0)=0$，故两份
完整外层准确为

$$
D(h-d,k)-D(h+d,-k)=2h\circ d=2hr.
\tag{176.4}
$$

其中 $h\circ t=0$，$k^2=c^2$。保留同一 $\phi$ 的两个准确行列式

$$
\Delta_-=B_\phi(h-d,k),\qquad
\Delta_+=B_\phi(h+d,-k).
$$

两份P2给 $2|\phi(hr)|\le\sqrt{\Delta_-}+\sqrt{\Delta_+}$。
只丢掉非负的交叉均值平方，再用
$(\sqrt A+\sqrt B)^2\le2(A+B)$，得到

$$
\begin{aligned}
4|\phi(hr)|^2
&\le2\phi(c^2)\,[\phi((h-d)^2)+\phi((h+d)^2)]\\
&=4\phi(c^2)\,[\phi(u)+\phi(d^2)],
\end{aligned}
\tag{176.5}
$$

即176.1。这里的 $d^2$ 来自实际输入 $h-d,h+d$ 的平方对角，
没有把 $|\phi(d)|^2$ 偷换成 $\phi(d^2)$。

对任意环境归一态 $\rho$，取数学正读取
$\phi=\rho\circ\mathcal U_r|_E$。二次表示保正，所以它可以读取全部原表；
其质量 $\rho(r^2)$ 可以为零，无须除以该质量。$h,r$ 交换给

$$
\begin{aligned}
\phi(hr)&=\rho(hr^3),&\phi(c^2)&=\rho(rc^2r),\\
\phi(u)+\phi(d^2)&=\rho(r^2+rd^2r)
& &\le(1+\|d\|^2)\|r\|^2.
\end{aligned}
\tag{176.6}
$$

$hr^3$ 自伴且 $\|hr^3\|=\|r\|^3$。环境态范数化这个固定自伴元素；
对176.1取态的上确界得

$$
\|r\|^6\le(1+\|d\|^2)\|r\|^2\|rc^2r\|.
\tag{176.7}
$$

$r=0$ 时176.2–176.3直接成立；$r\ne0$ 时才约去 $\|r\|^2$。
原 $(h,x)$ 的P2及态范数化给 $\|d\|\le\|h\|\|x\|=\|x\|$，
得到176.2第二界。最后

$$
\mathcal U_r(c^2)=rc^2r=(cr)^*(cr)\ge0,
\tag{176.8}
$$

故它为零等价于 $cr=0$；176.2再给 $r=0$，反向直接成立。∎

**推论 176.2（向横向子空间的固定行控制）。** 同一原值满足

$$
\|r\|\le\sqrt{1+\|d\|^2}\,\|c\|
\le\sqrt{1+\|x\|^2}\,\|c\|.
\tag{176.9}
$$

证明。176.2与 $\|rc^2r\|\le\|r\|^2\|c\|^2$ 给出结果，
仍只在 $r\ne0$ 时约去 $\|r\|^2$；零情形直接成立。∎

176.9是在有界 $x$ 集上随 $c\to0$ 的固定行余量控制。它没有比较任意
两个混合输入的旧值，不能升级为一般 $D$ 输入连续性、单位平移、
全域加性缺陷的统一次线性增长或实际准备稳定性。在140.1的原矩阵坐标中，
$c=\operatorname{diag}(a,f)$、$r=\operatorname{diag}(r_+,r_-)$ 时，
$\mathcal U_r(c^2)=\operatorname{diag}(r_+a^2r_+,r_-f^2r_-)$；
两份非交换系数均保留，没有取标量迹后丢掉平方。

## 177. 两次相关原调用的条件正交自举

**定理 177.1（交换分解中的充分生产条件）。** 在173.1下，若同一固定原
$x=c+z$ 还满足

$$
[c,z]=0,\qquad c\circ r=0,
\tag{177.1}
$$

则 $r=0$。174.1已经供应所需 $D(h,h\circ c)=0$；177.1中的两项不是
这里已经生产出的关系，尤其第一项不从一般偶奇分解推出。

证明。实际PB $(h,x,hc)$ 使用旧内值 $d$ 和已付零值
$D(h,hc)=0$。其两份完整外层为

$$
(a,b)=(z+d,2hc),\qquad (a_-,b_-)=(2c+z-d,0).
\tag{177.2}
$$

负外层的实际第二标签为零，173.4消去它，所以同一个实际原输出为

$$
K:=D(a,b)=-2x\circ d+2z\circ c.
\tag{177.3}
$$

置 $w=z+t$、$M=z\circ r$。由177.1，$c$ 与 $z,t,w$ 交换，
$c$ 与 $r$ 反交换，$c^2$ 与 $r$ 交换。于是 $a=r+w,b=2hc$ 的
实际重叠 $a\circ b=0$，且

$$
K=2c(z-t)-2M.
\tag{177.4}
$$

现在才对这份实际 $(a,b,K)$ 消费前卷18.1：零重叠是其标量入口，故

$$
b\circ K=0,\qquad K^2=a^2b^2.
\tag{177.5}
$$

没有重新证明面积定理，也没有把它应用于一般非零重叠。

$cM=-Mc$，$hM=-Mh$，所以 $hc$ 与 $M$ 交换。177.4的第一项与
$hc$ Jordan正交，因此

$$
b\circ K=-4hcM=0,\qquad cM=Mc=0.
\tag{177.6}
$$

$(z-t)^2=2z^2$，而 $c$ 与 $z-t$ 交换；177.6使177.4平方的两个混合项
都为零，得

$$
K^2=8c^2z^2+4M^2.
\tag{177.7}
$$

另一方面，$t\circ r=iQhM$，所以

$$
\begin{aligned}
a^2b^2
&=4c^2\,[r^2+2z^2+2M+2iQhM]\\
&=8c^2z^2+4c^2r^2.
\end{aligned}
\tag{177.8}
$$

这里 $c^2$ 与 $a$ 交换，且 $c^2M=0$，故所写乘法和消去均合法。
177.5给 $M^2=c^2r^2$。再乘 $c^2$ 得

$$
c^4r^2=0=(c^2r)^*(c^2r).
\tag{177.9}
$$

$c^2r=0$，因而 $(cr)^*(cr)=rc^2r=0$，即 $cr=0$。
176.3强迫 $r=0$。也有 $M^2=0$，但不需要倒置 $c$ 或约去它的支撑。
零 $c$、零 $z$、非可逆或无限谱的情形全由这些恒等式包含。∎

**定义 177.2（一般原重叠与下一联合接口）。** 没有177.1时，同一个实际
177.2–177.3仍成立，但其重叠准确是

$$
F:=a\circ b=2h(c\circ r)+h[c,z+t].
\tag{177.10}
$$

这是环境乘法的直接展开：$r\circ(2hc)=2h(c\circ r)$，
$(z+t)\circ(2hc)=h[c,z+t]$。第一项为 $h$-偶，第二项为 $h$-奇；
二者不能互相抵消。又

$$
[c,z+t]=(u+iQh)[c,z],\qquad
(u+iQh)^{-1}=(u-iQh)/2
\tag{177.11}
$$

只是在已知环境中的恒等式，不许可向 $D$ 输入该逆元。因此准确地

$$
F=0\quad\Longleftrightarrow\quad
c\circ r=0\ \hbox{且}\ [c,z]=0.
\tag{177.12}
$$

在已限定 $[c,z]=0$ 的子类，177.1和反向恒等式给
$r=0\Longleftrightarrow c\circ r=0\Longleftrightarrow F=0$。
一般 $r=0$ 并不要求 $[c,z]=0$，故不能把177.12写成全域零残差判据。

保留同一个实际 $K$，进一步PB $(a,b,0)$ 和PB $(b,a,0)$ 分别给

$$
\begin{aligned}
D(b+K,F)-D(b-K,-F)&=-2b\circ K,\\
D(a-K,F)-D(a+K,-F)&=2a\circ K.
\end{aligned}
\tag{177.13}
$$

这些只是下一原生产路线的调用接口。譬如同一正读取的P2直接给

$$
|\phi(b\circ K)|^2\le\phi(F^2)\,[\phi(b^2)+\phi(K^2)],
\tag{177.14}
$$

其中 $K^2$ 来自真实输入 $b\pm K$ 的平方。它不是新的独立生产结果，
也没有消去 $F^2$。一般目标仍是由这些共同出现的实际旧值生产
$\mathcal U_r(c^2)=0$，或一份足以与176.2合用的严格收缩，或下节所接的
余量自交换；不能只增加一个未消去的正预算就宣布完成。

## 178. 全态二表仍需两次相关配平的有限诊断

**命题 178.1（一个局部旧值候选的准确排除）。** 在允许的有限特例
$E=H_4(\mathbb C)=H_2(M_2(\mathbb C))$ 中，令 $X,Y,Z$ 为标准Pauli矩阵，
$I=I_2$，取标准实际框架

$$
h=Z\otimes I,\qquad e=X\otimes I,\qquad j=-Y\otimes I,\qquad Q=I_4.
$$

固定普通实数 $s,v>0$ 且 $s+v\le1$，取实际标签及一个待检验的单表输出

$$
\begin{gathered}
c=I\otimes Z,\qquad z=sX\otimes I,\qquad x=c+z,\\
t=-sY\otimes I,\qquad r=vI\otimes Y,\qquad d=t+r.
\end{gathered}
\tag{178.1}
$$

这份指定 $(h,x,d)$ 表满足每个正读取的P2，且
$[h,r]=0,[c,z]=0,c\circ r=0,r\ne0$；175.1的所有扇区预算亦成立。
但若同时保留已付的 $D(h,hc)=0$ 及零输入值，两次相关PB
$(h,x,hc)$、$(z+d,2hc,0)$ 不可能都成立。
这是一份局部表信息的诊断，不是完整PB的总映射反模型。

证明。第一输入平方是 $I_4$。记

$$
P=Z\otimes Z=h\circ x,\qquad
T=Y\otimes I,\qquad V=X\otimes Z,\qquad J=Y\otimes Y.
$$

直接乘法给

$$
x^2=(1+s^2)I_4+2sV,\qquad d=(-s+vJ)T.
\tag{178.2}
$$

$J$ 与 $P,T,V,d$ 交换；$P,T,V$ 两两反交换且平方均为 $I_4$。
在任一非零 $J$-谱扇区 $\eta=\pm1$，对任意态置
$p_0=\phi(P),q_0=\phi(T),w_0=\phi(V)$。因为
$(aP+bT+cV)^2=(a^2+b^2+c^2)I_4$，态范数界给

$$
p_0^2+q_0^2+w_0^2\le1.
\tag{178.3}
$$

$|-s+\eta v|\le s+v\le1$，故

$$
p_0^2+(-s+\eta v)^2q_0^2
\le1-w_0^2
\le1+s^2+2sw_0,
\tag{178.4}
$$

最后一差恰为 $(w_0+s)^2$。这正是这份原二表的行列式不等式
$|\phi(d)|^2+\phi(h\circ x)^2\le\phi(h^2)\phi(x^2)$。
表的全部元素都与 $J$ 交换，任意态在它们上的读取为两个扇区态读取的
凸组合。数值Hermitian半正定二表的凸性因此给所有态的P2；
一般正泛函按质量缩放，零质量直接为零。这里未使用输出第二矩。
$c\circ r=0$ 使175.1左侧为零，右侧非负，所以该预算不排除本表。
另外 $[r,x]=2ivI\otimes X\ne0$。

若第一份实际PB成立，177.2–177.3强迫同一个原输出

$$
\begin{gathered}
a=z+d=s(X-Y)\otimes I+vI\otimes Y,\qquad b=2Z\otimes Z,\\
K=D(a,b)=2s\bigl[(X+Y)\otimes Z-vX\otimes Y\bigr].
\end{gathered}
\tag{178.5}
$$

Pauli乘法 $XY=iZ,YZ=iX,ZX=iY$ 直接给

$$
a\circ b=0,\qquad b\circ K=-4svY\otimes X\ne0.
\tag{178.6}
$$

第二份真正PB $(a,b,0)$ 的两份完整外层因而是

$$
D(b+K,0)-D(b-K,0)=-2b\circ K=8svY\otimes X.
\tag{178.7}
$$

P2使左侧两个输出都为零，右侧非零，矛盾。这两次调用须消费同一个
178.5的 $K$，不能分别挑选独立可达的输出预算。
因此178.1证明的是较弱局部数据不足，并被具名的相关PB排除；
没有给出违反重构而满足完整全部PB的候选总映射。∎

## 179. 既有标量铅笔对余量自交换的直接应用

**推论 179.1（同一原表的自交换充分接口）。** 在173.1下，对每个原 $x$，
静态卷引理5.7直接给

$$
\boxed{[r,x]=0\quad\Longleftrightarrow\quad r=0.}
\tag{179.1}
$$

这是一份已有逐对标量铅笔结果的参数应用，不是新的谱定理，
也没有生产一般 $[r,x]=0$。

证明。反向直接成立。正向利用已付的 $[r,h]=0$；在已知环境的含单位
C*子代数

$$
\mathcal A_0=C^*(u,h,x,r,Q)
\tag{179.2}
$$

中，$r,Q$ 都中央。任取其非零不可约表示 $\pi$，存在实
$\lambda$ 和 $\epsilon\in\{1,-1\}$ 使
$\pi(r)=\lambda I,\pi(Q)=\epsilon I$。令

$$
p=\pi(h),\qquad q=\pi(x),\qquad
\delta=\epsilon\pi(d)=\frac i2[p,q]+\epsilon\lambda I.
\tag{179.3}
$$

每个 $\pi(\mathcal A_0)$ 的态先拉回 $\mathcal A_0$，再正延拓到
$\mathcal A$；其限制读取的正是同一实际 $(h,x,d)$ 原P2。
所以它的二表对角准确为 $p^2,q^2$、实非对角为 $p\circ q$。
若 $\epsilon=-1$，将数值Hermitian二表复共轭只反转虚非对角符号，
仍半正定。因此所有这些态对179.3的 $\delta$ 都满足静态卷5.7的准确前件。
该引理以 $(p,q,\tau)=(\pi(h),\pi(x),\epsilon\lambda)$ 给
$\epsilon\lambda=0$。不可约表示分离 $\mathcal A_0$，故 $r=0$。

这里只对同一实际原表作表示读取，没有定义表示像上的 $D$，
没有假设 $D(\epsilon h,x)=\epsilon D(h,x)$。
静态卷5.7的有界自伴算子、全态二表及实标量余项前件已逐项对应，
其谱边界子证明不在这里重证。∎

## 180. 已付纯像小标签机制与两种迁移边界

**定义 180.1（完整多项式域与全部实际纯像的不同范围）。** 原多项式卷
51–58已经在其指定的标量端点矩阵多项式原域中识别全部旧值，包含标量
背景下的混合桥。该指定域的原式39.2已付，不再作为未解问题。
该卷59–64进一步给另一份无需多项式输出传播的已付连接。

准确地，保持该卷59.1的同一原 $E,D$ 及有限维满Jordan商
$\pi:X\to Y$，取非零自旋角 $J=Y_2(p)=\mathbb Rp\oplus H$ 和实际
$T=\{a\in E:\pi a\in J\}$。对全部实际原代表 $a,b\in T$，只要
$\pi a=x_0,\pi b=y_0\in H$ 都纯，59.2给

$$
\pi D(a,b)=B(x_0,y_0).
\tag{180.1}
$$

$B$ 是该卷已经构造的交替实双线性面积映射，
$B_y(v)=B(v,y)$，$B_y^2=-\|y\|^2I+y\otimes y$。
这里没有未付的纯像幅度或实际代表纤维。
它不包含任意标量背景的混合纤维。

该连接的承重调用不能误记为多项式唯一延拓。对非零正交纯像
$x_0,y_0$，固定原未知输出像 $d_0=\pi D(a,b)$；旧纯像正交消费者已给
$d_0\perp x_0,y_0$。选择一个普通有限实数 $\tau>0$，使

$$
\tau\|y_0\|\sqrt{1+\|x_0\|^2}<1,\qquad q_0=\tau b\in T.
\tag{180.2}
$$

只缩小这个实际第三标签。已有小窗口识别
$\pi D(a,q_0)=\tau B(x_0,y_0)$，并非假设未知 $D$ 的缩放律。
同一次原PB的两份外层像是

$$
R_\pm=y_0\pm d_0,\qquad
S_\pm=\tau y_0\pm\tau B(x_0,y_0),\qquad
\|S_\pm\|<1.
\tag{180.3}
$$

两份原外层同时进入已付短Gram方向窗口，故都能识别为同一个 $B$；
PB再由 $B_y^2$ 认回大行 $d_0$。零像由零平方预算处理，非正交纯像由
实际常数SO$(2)$旋转处理。该卷60–61已证明这些步骤，180.2–180.3只是
这里的原调用对应，不另计新结果。既不需要向未知输出传播多项式恒等，
也不需要另假设全域输入连续或齐次。

在该卷62.1明确选择的连续原域

$$
\begin{gathered}
E=\{a\in C([0,1],H_2(\mathbb C)):a(0)\in\mathbb RI_2\},\\
E_0=\{A\in E:\operatorname{tr}A(s)=0\ (s\in[0,1])\}.
\end{gathered}
\tag{180.4}
$$

中，62.2–62.3已经认回每个实际纯像及全部全局无迹输入的共同符号
交换子；同一连续锚输出把符号固定在 $(0,1]$。63.1的连续标量权重首先
在纯输入限制上成立。该卷65–71进一步识别严格定号首像与横向纯第二像
的全部实际代表，不要求全局原单位轴；这条受限点桥保持其准确范围。

该卷72.1–72.2、77.1在180.4的同一个连续原域和同一旧总映射上，现已
识别全部原输入，包括不定号、非横向及两槽任意连续标量偏置。原式63.2
和69.2的完整桥因而已付：

$$
\begin{gathered}
D(fu+A,gu+B)=D(A,B)
=\varepsilon_0\frac{\mathrm i}{2}[A,B],\\
f,g\in C([0,1],\mathbb R),\qquad A,B\in E_0.
\end{gathered}
\tag{180.5}
$$

准确的来源对应是该卷73–76的同一点实际配平，不是把65.2的定号横向
前件删除后直接套用。73的两份实际仿射／同轴第三标签先消去一般横向
比较输出的标量部分。74选一个足够大但有限的实际单位标签，使两份
外层第二像均严格定号；在外层输出纯性尚未建立时，只对这两份实际
外层同时使用原P2的52.2点约束，再与同一次PB联合取得定号张成对的
纯性与正交性。75用两次这样的真实大单位配平覆盖任意原混合输入，
没有以尚未证明的输出纯性作为该步骤的前提。

76随后选择同一个实际仿射第三标签，使正侧外层的两份点像同时纯。
这时才用62.2认回正侧旧值；负侧无需变纯，它的输出已保持75.3所证的
纯性与两输入方向正交。同一次PB和这两份相关约束固定原输出的共同
面积幅度。零点标量像、共线像、零向量及零偏置按该卷的原零像、共线
零值与分支处理。这里不假设输入正则性、旧 $D$ 缩放、局部性、平移、
混合商下降或跨点唯一延拓；实际原标签和两份旧外值始终一起保留。

由该卷72.2的全对公式，77.1在整个180.4的原 $E$ 上已经给出实双线性、
Jacobi、任意连续标量权重 $D(fa,gb)=fgD(a,b)$ 及全部混合点纤维一致性。
静态卷32.2、23.1的准确前件于是已满足，故原P3、全部有限原复Gram、
字面原R及同一个 $S-\mathrm iD$ 的结合性均在该指定域支付。
其复化准确为
$E+\mathrm iE=\{F\in C([0,1],M_2(\mathbb C)):F(0)\in\mathbb CI_2\}$；
固定坐标中 $\varepsilon_0=1$ 为通常乘法，$\varepsilon_0=-1$ 为反乘法。
这些均直接复用该卷72–79，不计作本节或174.1的新增结论。

点标量零行本身仍不是180.5的证明；该桥由以上实际网络另行支付。
180.4本来就是另一原域，不是完成旧多项式 $D$ 后冒充原响应。
该域的全局无迹标签在标量端点消失，不提供173.1的实际原单位三轴；
也没有把该域、纯像或其有限自旋商替换一般非交换系数原域。
全部原A1–A3、准确锥、P2、完整PB和独立公理数保持，数学点读取和
标签选择不生产任何实际物理来源。

**命题 180.2（正标量化不保持原平方）。** 在标准完整模型
$E=H_2(M_2(\mathbb C))$、$D(A,B)=i[A,B]/2$ 中，存在保单位正映射
$\Psi:E\to H_2(\mathbb C)$ 和实际原 $A,B$，使

$$
\Psi(A)=\Psi(B)=0,\qquad
\Psi(D(A,B))\ne0,\qquad\Psi(A^2)\ne\Psi(A)^2.
\tag{180.6}
$$

证明。取系数向量态 $\chi$ 满足 $\chi(Z)=1,\chi(X)=\chi(Y)=0$，
令 $\Psi=\operatorname{id}_2\otimes\chi$，
$A=I\otimes X,B=Z\otimes Y$。则

$$
D(A,B)=-Z\otimes Z,\quad
\Psi D(A,B)=-Z,\quad \Psi(A^2)=I,\quad\Psi(A)^2=0.
\tag{180.7}
$$

$\Psi$ 甚至完全正，但不是Jordan同态。标准模型满足原全部静态条件和
全部PB，准确复用静态卷35.1–35.2的 $\kappa=1$。
所以不能把任意正系数读取当作有限Jordan商，不能以读取后的输入平方
替换真实平方对角，更不能据其零像给一般旧响应商下降。此模型的 $D$
本来就是目标交换子，命题反驳的是迁移规则，不是重构。∎

**命题 180.3（实际连续输出没有自动区间唯一性）。** 有满足全部原静态
条件和完整PB、带同一实际框架的连续系数原域，其中一份实际旧输出
在非空开区间为零，却在另一点非零。

证明。明确选择 $E=C([0,1],H_2(\mathbb C))$、通常Jordan乘法及同一
总映射 $D(a,b)=i[a,b]/2$，仍由静态卷35.1–35.2消费完整模型。
取实际常轴 $h=Z,e=X,j=-Y$，以及实际连续原标签
$f(s)=\max(0,s-1/2)$、$a=Z,b=fX$。则

$$
D(a,b)=-fY.
\tag{180.8}
$$

这份固定输出在 $(0,1/2)$ 为零，在 $s=1$ 非零。它是原连续域中的
真实输出，不是随输入取极限造出的新值。因此一般连续输出不能承接
原多项式卷52–55的区间恒等传播。该反例不触及式(180.2)–(180.3)的实际
小第三标签机制；那一机制已经不依赖区间唯一性，也不反驳重构，
因为此模型已经有标准 $D$。∎

把180.1移到一般原域，仍须逐项供应保所需Jordan乘法及平方对角的
分离读取、真正可调用的第三标签、两份外层同时进入已识别窗口的条件，
以及能消去同一旧输出缺陷的辅助关系。正泛函读取本身不能供应这些条件。
若选择旧的跨读取多项式路线，另须证明同一固定输出的唯一传播律；
180.3排除了仅以连续性代替该律。若选择新小标签路线，则须验证
式(180.3)的外层仍是可识别纯像及其面积算子平方律；一般非交换系数不免费
满足标量自旋几何。两条方法边界均不证明一般生产不可能。

## 181. 承重归属、原生产接口与完整量子来源

**定义 181.1（新增综合与成熟中间工具）。** 174.1的整个交换类局部化、
176.1的同一旧输出湮灭强制界及177.1的条件相关自举归为
$\texttt{repo-derived}$ 纸面综合；175.1是174.1的直接混合消费者，
178.1给该生产路线的局部二表诊断。179.1只是已有静态卷5.7的参数应用，
180.1–180.5只接回原多项式卷51–79的各自已付范围，不另计为新刚性。
这些结果不主张历史原创、文献穷尽、独立公理数已经减少或内核认证。

原多项式卷4.2是174.1所局部化的成熟仓内机制，不是可直接套在
$\kappa$ 上的全域同态定理。174.3明确给每次平方、混合乘法的使用范围；
最后174.24只需 $g$ 的偶性消去第二平方，只需 $a$ 的偶性处理
$a\circ k_0$，不假设 $k_0$ 偶。174.8–174.16的支撑、Peirce规则、
双对偶、Kaplansky密度及强乘法连续性，按原多项式卷4.2所列的
Hanche-Olsen–Størmer和Hamhalter原条件复用。二次表示保正亦见
van de Wetering，[*Commutativity in Jordan Operator Algebras*](https://arxiv.org/html/1912.01903v1)，
Proposition2.21；其JC公式 $\mathcal U_a(b)=aba$ 及本文已付忠实包含
说明176.6的正读取。正Hahn–Banach延拓、GNS、交换C*字符分离、
不可约表示分离和有限Pauli代数是成熟中间工具，不各立为新结果。
177.5直接复用前卷18.1，179.3直接复用静态卷5.7；不把这些既有定理
改名为新的面积或谱结果。数学引用只供应所列工具，不供应未知原响应
的可加性或任何实际物理源。

**定义 181.2（一般原生产仍须达到的关系）。** 174.1使153.9在整个
$c\in\operatorname{Com}_h,z=0$ 分支付清，并使160.1准确成为

$$
D(h,c+z)=D(h,z),\qquad\text{即 }r=\delta_h(c,z)=0.
\tag{181.1}
$$

所有原 $c,z$、非交换系数、一般无限谱和不完备域仍在该目标内。
176.3给全域充分且必要的原支撑条件
$\mathcal U_r(c^2)=0$；179.1给另一等价充分接口 $[r,x]=0$。
177.1只在 $[c,z]=0$ 时把 $c\circ r=0$ 变成充分生产条件，
177.10明确保留一般非交换重叠。这里没有生产这些一般零关系，
没有构造满足全部P2/PB却否定它们的完整反模型。

与既有161–172的接线须逐项区分。166.1已付任意原横向 $v$、任意实
$R,\mu,\lambda$ 的 $D(Rh,\mu u+\lambda h+v)=RTv$；167.2的式167.3已付
$D(su+rh,w)=rTw$ 的原横向整行。这些公式允许非标量、非可逆及无限谱
$v^2$，是本节直接复用的既有结果，不是174.1重新生产的仿射结论。
它们的两种受限输入域仍不合并为任意两混合输入的公式。

170.2所列第一处一般内值缺口现由174.1支付：对每个原偶 $c$，
$hc=h\circ c$ 仍原且与 $h$ 交换，故 $D(h,hc)=0$。因此177.2的实际
$\mathrm{PB}(h,c+z,hc)$ 及其剩余外值177.3，已经在全部原偶 $c$
上合法，不再把这个内零值列为一般未付前件。174.1也直接支付一般
$D(h,c)=0$，但未支付在混合输入中删除 $c$ 的181.1。

170.2的另外两处缺口仍在：外层首标签 $2hc$ 一般不属于
$\mathbb Ru+\mathbb Rh$，163.1的仿射投影接口不能读取该一般算子系数
首标签，因而164.5的横向投影比较不能照搬。即使另获相应联合反交换
关系，165.8–165.9的全态标量Gram仍使用 $c=\mu u+\lambda h$；一般
$c$ 与 $z,r$ 可不交换，既未得到同一不可约二阶像，也没有该共同平方
和乘积的标量读取。176.2的支撑界不生产自己的湮灭子，179.1的余量
自交换只是充分接口；177.13–177.14保留相关旧外层及正预算，不消去
一般非零重叠。不能用更多正下界、任意正标量化或分别可达的预算填上
这两处生产缺口。

余量落入三轴共同交换子的157.2–157.3保持其原生指定域，
不升级为全局中心。静态卷89仍需全部原首标签和全部原三元组的
加性缺陷中心性；94–98仍需全输入统一 $A(R)=o(R)$，176.9不是这个
增长条件。除这里及180.4指定域已经识别的原值外，一般首标签、一般
无实际原正交框架的域、一般原 $D$ 的双线性、旧P3、全部有限旧复Gram、
旧R、同一旧结合乘法及原完成运输仍各守准确未付接口。
候选 $B_\star$、辅助C*完成和已知乘法不代替旧 $D$。

原多项式指定域的全部值和一般有限自旋商的全部实际纯像，已各在
180.1的准确范围支付；180.4指定连续标量端点域的全部原对及180.5、
全域实双线性、连续权重、混合点纤维、P3、全部有限复Gram、原R和
同一个通常／相反结合乘法，也已由原多项式卷72.2、77.1支付。
这些不再列为未解，亦不将其归功于本节；一般原JB／算子系数的混合
旧值识别和完整物理来源仍未付，原独立公理数不变。

**定义 181.3（全部原物理接口与几何含义）。** 145.1–145.7、155.1及
160.3的来源合同逐项完整保持，175.5或任何局部交付均不替代完整目标。
唯一原 $\Omega$、同一原 $E/D$、原门序列与读出、native、全词同一
$q,K,J$、parent/ready、原中心及经典／不等维／静默块、一般无原子和
无限维分支全部保持。实际准备、全部零／不等／次归一质量及同一个
实际完整菜单保持原量词；Born只在该菜单严格正质量时归一，零质量不
归一。数学正读取、支撑态、GNS向量和角压缩不生产实际准备或完整菜单。

整台typed仪器及其环境、全部成功／失败／细记录／port／post-port输出，
原接受端、真正分组遗忘、更新、Kraus、TP、Lüders和CP各守原前件。
真正相关联合、共同实现、忠实同向交换的腿、共同生成及重数、全部相关
输入和递归同源参考不由单域矩阵几何制造。全部合法顺序、自适应、并行
历史，每份输出的每个合法未来，停止／拒绝／销毁／泄漏、同数两侧及
真实双向返回均在完整原量词内。CountRead的无限与非离散记录、可数
可加、正常性及指定前对偶没有由范数完成支付。

保持原域的流、实际相位与门序列、物理钟、强连续实现、一般无界生成元
及其域、Hamiltonian能量解释、作用量和共同正 $\hbar$ 仍须同源供应。
有限三轴和偶奇角是关系几何，不是把一般原世界缩成有限维量子系统，
也不是物理三维空间的证明。174.1的几何作用是排除整片交换方向上的
旧响应；176.3说明混合余量若非零，必须在原交换输入平方上留下非零
正支撑；177.10说明该支撑生产还须控制同一混合输入的非交换联系。
这些条件关系推进原问题，却不把数学兼容性或公理前提重述当作
完整量子物理起源。

## 追加锚（本行以下为增补区）

## 182. 原系数反射给出的第二份实际框架

**定义 182.1（完整原候选与反射分支）。** 完整采用173.1–173.2的同一原
$(E,C,u,N,\mathcal P,S,D)$、A1–A3、准确锥、全部原P2和完整原PB。
具体地，A1保留所有原标签的两条有向Hermitian二表正性；A2保留实际
相加三表 $(a+b,a,b)$ 及其排列在整个实三空间上的实部半正定性及
$(1,-1,-1)$ 的零二次值；A3保留 $S(u,u)=u$ 和同一固定有理
$0<\vartheta_0\le1$ 上的 $0\le y\le\vartheta_0u\Rightarrow S(y,y)\le y$。
原正评价分离元素并准确决定原锥，全部零、不等和次归一质量保留。
沿前卷16.1–16.2的同一忠实、含单位、等距且准确保锥JC包含，仍写

$$
E\subset X\subset\mathcal A_{\rm sa},\qquad
\overline E=X,\quad\mathcal A=C^*(X),\quad
S(a,b)=a\circ b=(ab+ba)/2.
\tag{182.1}
$$

$E$ 可以不完备、无限维、不可分，$X$ 不必填满 $\mathcal A_{\rm sa}$。
旧 $D:E^2\to E$ 不预付一般可加、齐次、连续、可测、协变、商下降或
完成延拓。固定同一实际原 $h,e,j=D(h,e)$，消费133.1–134.1的
$h^2=e^2=j^2=u$、两两Jordan正交，以及辅助中央自伴对合
$Q=ihej\in Z(\mathcal A)$；不要求 $Q\in E$。

另给一份明确的充分分支资料：原 $s\in E$ 满足

$$
s^2=u,\qquad [s,h]=[s,e]=0.
\tag{182.2}
$$

这是对同一原域内已有标签的条件，不由A1–A3或PB推断其存在。取任意
$\lambda,\nu\in\mathbb R$、$\nu\ne0$ 及原 $z\in E$、$hz=-zh$，固定

$$
\begin{gathered}
c=\lambda h+\nu s,\quad x=c+z,\quad
t=D(h,z)=iQhz,\quad d=D(h,x)=t+r,\quad
[h,r]=0,\quad k=h\circ x=hc=\lambda u+\nu hs.
\end{gathered}
\tag{182.3}
$$

这里 $[h,r]=0$ 来自150.1；$r$ 始终是这份旧输出的同一余量，而不是
另选的候选输出。174.1已给 $D(h,c)=D(h,k)=0$，但不先把混合响应
拆开。对 $a=h,s$，记原有限Jordan算子

$$
U_a y=2a\circ(a\circ y)-y=aya,\qquad
P_a^\pm=(I\pm U_a)/2,\qquad y_{\rm e}=P_s^+y,\quad y_{\rm o}=P_s^-y.
\tag{182.4}
$$

特别 $z_{\rm e},z_{\rm o},r_{\rm e},r_{\rm o},t_{\rm e},t_{\rm o}$ 都是原
标签。$U_h,U_s$ 对易；括号只表示已知环境交换子，不定义新的响应。
所有结合乘法、表示和数学态仅用于证明，不把原域外的根、逆元、谱符号
或归一化元素送进 $D$。

**引理 182.2（新轴的实际旧值与同一取向）。** 在182.1下，令
$H=h\circ s=hs$。则 $H\in E$、$H^2=u$、$H\circ e=0$，且真正的旧值为

$$
J:=D(H,e)=s\circ j=sj,\qquad iHeJ=Q.
\tag{182.5}
$$

因此 $(H,e,J)$ 是与原框架同取向的实际原框架；对每个原 $y\in E$，
163.1在这个框架上的准确特化是

$$
\boxed{P_H^-D(2\lambda u+2\nu H,y)
       =2\nu iQH P_H^-y.}
\tag{182.6}
$$

这只识别所示实际输出的一个投影。

证明。由 $[s,h]=[s,e]=0$ 及中央 $Q$，已知恒等式 $j=iQhe$ 给
$[s,j]=0$。因此 $H=h\circ s$、$sj=s\circ j$ 都是原Jordan表达式；
$H^2=h^2s^2=u$，而 $eH=-He$。先使用实际交换框架 $(e,h,-j)$：
原反对称性给 $D(e,h)=-j$，其取向为 $ie h(-j)=Q$。
133.1–134.1在此框架上对原 $H\in V_e$ 给

$$
D(e,H)=iQeH=-s j.
\tag{182.7}
$$

再次用原反对称性才得到 $J=D(H,e)=sj$。于是 $J^2=u$，且 $J$ 与
$H,e$ 两两反交换；$s$ 与 $h,e,j$ 交换还给
$iHeJ=i h s e s j=ihej=Q$。这逐项支付163.1所需的实际框架前件。
将其首槽参数取为 $2\lambda,2\nu$、第二标签取为同一 $y$，得到182.6。
未使用 $D$ 的第一槽齐次、换轴协变或乘法相容律。∎

## 183. 同一个相关外层生产余量的第二种偶性

**定理 183.1（原反射系数的混合余量关系）。** 在182.1的全部条件下，
同一原 $r=D(h,\lambda h+\nu s+z)-D(h,z)$ 满足

$$
\boxed{[s,r]=0,\qquad [c,r]=0,\qquad P_s^+z\circ r=0.}
\tag{183.1}
$$

不要求 $[s,z]=0$、$[c,z]=0$、$c\circ r=0$、$[r,x]=0$ 或任何支撑湮灭
关系作为前件。

证明。只新增选择原三元组 $\mathrm{PB}(h,x,k)$。174.1给
$D(h,k)=0$；173.3的两份位移是 $d-c$ 和 $k$，所以两份实际外层完整为

$$
(a,b)=(z+d,2k),\qquad
(a_-,b_-)=(2c+z-d,0).
\tag{183.2}
$$

负外层的旧值由原零输入P2为零。使用原 $k^2=c^2$，PB准确给177.3
已列出的同一旧输出及其反向值

$$
\begin{aligned}
K:=D(a,b)&=-2x\circ(d-c)-2k^2=-2x\circ d+2z\circ c,\\
D(b,a)&=2x\circ d-2z\circ c.
\end{aligned}
\tag{183.3}
$$

177.2–177.3的这两项身份并不使用177.1的额外假设，此处不把其零重叠
结论借入。特别 $b=2k=2\lambda u+2\nu H$，182.6正好能读这份实际
$D(b,a)=-K$，没有更换任何一个端点。

置原 $M=z\circ r$，$M_{\rm e}=P_s^+M$。由 $s$ 与 $h,Q$ 交换，
$t_{\rm e}=iQhz_{\rm e}$、$t_{\rm o}=iQhz_{\rm o}$。只展开已知Jordan
乘法，并用 $h\circ t=z\circ t=0$，得到

$$
\begin{aligned}
c\circ t&=\nu s t_{\rm e},&
c\circ r&=\lambda hr+\nu s r_{\rm e},&
z\circ c&=\nu s z_{\rm e},\\
D(b,a)&=2\nu s(t_{\rm e}-z_{\rm e})
       +2\lambda hr+2\nu s r_{\rm e}+2M.
\end{aligned}
\tag{183.4}
$$

这里与 $s$ 或 $h$ 交换的乘积本来就是原Jordan乘积；未展开未知
$D(h,c+z)$。同一 $M$ 为 $h$-奇，因为 $z$ 为 $h$-奇、$r$ 为 $h$-偶。
又 $U_H=U_hU_s$，故 $z_{\rm e},t_{\rm e},r_{\rm o}$ 为 $H$-奇，
$z_{\rm o},t_{\rm o},r_{\rm e}$ 为 $H$-偶，并且 $P_H^-M=M_{\rm e}$。
于是从实际输入和183.4分别得到

$$
\begin{aligned}
P_H^-a&=z_{\rm e}+t_{\rm e}+r_{\rm o},\\
P_H^-D(b,a)&=2\nu s(t_{\rm e}-z_{\rm e})
                    +2\lambda hr_{\rm o}+2M_{\rm e}.
\end{aligned}
\tag{183.5}
$$

另一方面，对同一个旧输出用182.6，且
$iQh t_{\rm e}=-z_{\rm e}$，得到

$$
P_H^-D(b,a)
=2\nu s(t_{\rm e}-z_{\rm e})+2\nu iQhsr_{\rm o}.
\tag{183.6}
$$

两种读取比较后准确是

$$
\nu iQhsr_{\rm o}=\lambda hr_{\rm o}+M_{\rm e}.
\tag{183.7}
$$

两项含 $r_{\rm o}$ 的元素为 $h$-偶，$M_{\rm e}$ 为 $h$-奇。原有限
$h$-偶奇投影因此分别给

$$
M_{\rm e}=0,\qquad (\nu iQs-\lambda u)r_{\rm o}=0.
\tag{183.8}
$$

后式只在已知环境中左乘 $-\nu iQs-\lambda u$。由于 $Q,s$ 交换且
$(iQs)^2=-u$，得

$$
(\nu^2+\lambda^2)r_{\rm o}=0.
\tag{183.9}
$$

$\nu\ne0$，所以 $r_{\rm o}=0$，即 $[s,r]=0$。连同 $[h,r]=0$，这给
$[c,r]=0$。最后 $r$ 为 $s$-偶，故
$M_{\rm e}=P_s^+(z\circ r)=z_{\rm e}\circ r$，由183.8得到183.1。
这个消元没有使用谱逆或谱符号；183.7若保留非零 $r_{\rm o}$ 或
$M_{\rm e}$，便会同时违反同一旧外值的两份投影身份。∎

## 184. 不跨反射扇区的全部原横向输入

**定理 184.1（同一实际混合值的受限识别）。** 在182.1下，若还满足
$[s,z]=0$，则同一旧余量为零，准确地

$$
\boxed{D(h,\lambda h+\nu s+z)=D(h,z)=iQhz.}
\tag{184.1}
$$

原 $z^2$ 可非中央、奇异、不可逆或有无限谱；不要求全原域具有有限商
分离族。

证明。183.1此时给 $z\circ r=0$，即 $zr=-rz$。零代数直接成立。
其余情形只为数学读取定义含同一实际余量的共同C*子代数

$$
\mathcal K_0=C^*(u,Q,s,h,z,r)\subset\mathcal A.
\tag{184.2}
$$

$Q,s,z^2,hr$ 全部属于 $Z(\mathcal K_0)$。确切地，$s$ 与所有生成元
交换，$z^2$ 与 $h,r,z,Q,s$ 交换，而
$(hr)z=h(-zr)=zhr$，$hr$ 也与其余生成元交换。$hr$ 自伴，$z^2$ 正。
这只是在含该 $r$ 的读取代数中取中心，不把它们宣称为全局中央元。

对任意非零不可约表示 $\pi$，由Schur读取写

$$
\begin{gathered}
\pi(s)=\epsilon I,\quad\pi(Q)=\eta I,\quad
\pi(z^2)=b^2I,\quad\pi(hr)=mI,\\
\epsilon,\eta\in\{1,-1\},\quad b\ge0,\quad m\in\mathbb R,\\
A=\pi(h),\quad V=\pi(z),\quad
A^2=I,\quad AV=-VA,\quad V^2=b^2I,\quad\pi(r)=mA.
\end{gathered}
\tag{184.3}
$$

至此才有同一实际原输入、输出的联合像

$$
\begin{gathered}
\mu=\nu\epsilon,\qquad
\pi(x)=\mu I+\lambda A+V,\qquad
\pi(d)=i\eta AV+mA,\\
\pi(x^2)=(\mu^2+\lambda^2+b^2)I+2\mu\lambda A+2\mu V,\qquad
\pi(h\circ x)=\lambda I+\mu A.
\end{gathered}
\tag{184.4}
$$

特别前两项不是把原 $c$ 预先替换为标量；$\lambda A$ 仍在原输入的像中。
$\pi$ 保留真实平方、Jordan乘积及该同一输出。任一 $\pi(\mathcal K_0)$
上的态拉回 $\mathcal K_0$，再由含共同单位C*子代数的正性延拓
取得 $\mathcal A$ 上的正归一态，不要求该态正常。这个正性延拓正是165.1
所用Blackadar II.6.3.1。准确锥接口123.2、173.2允许它读取原
$(h,x,d)$ 的同一P2；没有定义 $\pi(E)$、压缩角或商上的响应。

若 $b=0$，自伴性给 $V=0$，像代数只由单个对合 $A$ 和标量生成，
不可约性使其一维。原 $h,x$ 的这份联合标量读取有零Gram行列式，
所以P2强迫 $m^2=0$。

若 $b>0$，仅在表示中置 $E_0=V/b$、$J_0=i\eta AE_0$。184.3表明
像代数正好由 $A,E_0$ 和标量生成；$\pi(r)=mA$ 没有增加生成元。
165.6–165.7的成熟两轴表示论证于是逐项适用：$E_0$ 酉地互换 $A$ 的两个
特征空间，它们生成 $M_2(\mathbb C)\otimes I$，不可约性消去重数。
对每个单位Bloch向量 $(n_x,n_y,n_z)$ 的态，用184.4读取真实原P2，得

$$
\begin{aligned}
(bn_y+mn_z)^2
&\le b^2+2\mu b n_x+\mu^2(1-n_z^2)\\
&=(b+\mu n_x)^2+\mu^2n_y^2.
\end{aligned}
\tag{184.5}
$$

左侧是 $|\phi(d)|^2$，不是 $\phi(d^2)$；$\lambda$ 的消失严格来自
184.4的真实Gram相消。现在直接消费165.9–165.12的固定算子排零机制，
参数对应为其 $\sigma=\eta$、横向幅度 $b$、偏移 $\mu=\nu\epsilon$、
余量幅度 $m$。165.10、165.11、165.12分别处理
$0<b<|\mu|$、$b=|\mu|>0$、$b>|\mu|$，由全部184.5强迫 $m=0$；
零横向分支已单列。因此没有将已有标量排零另立为新定理。
所用态只读这份固定原输入和固定原输出，有限见证或固定标量估计不要求
$D$ 的输入、输出连续性。

所有不可约表示都有 $\pi(r)=0$。由165.1所引Blackadar II.6.4.9的
不可约表示分离，$r=0$，再用133.1即得184.1。正延拓只供应证明读取，
不供应正常物理表示、实际准备或商下降。∎

## 185. 承重连接、已有范围与未付关系

**定义 185.1（准确来源与新增消费者）。** 182.2–184.1是
$\texttt{repo-derived}$ 的原元素承重综合，不主张历史优先权。
新连接是让同一反射系数产生另一份实际框架，使已付仿射投影真正读取
177.3的同一相关旧外值，再将新生产的关系接回已有排零机制。
其来源对应为：

| 原来源 | 此处消费者与参数对应 | 保留的范围 |
| --- | --- | --- |
| 前卷16.1–16.2、本卷123.2、173.1–173.2 | 182.1的原域、反对称性、正读取与完整PB | $E$ 只在 $X$ 中稠密，不填满环境、不延拓旧 $D$ |
| 133.1–134.1及实际交换框架 $(e,h,-j)$ | 182.7给真正的 $D(e,H)$，182.5给 $D(H,e)$ 及同一 $Q$ | 先确认原输入和旧值，不用未知换轴协变 |
| 150.1、173.2 | 182.3的同一 $r$ 为 $h$-偶，$t=iQhz$ | 未预付其 $s$-偶性或与 $z$ 的关系 |
| 174.1 | 183.2所需原内值 $D(h,k)=0$ | 全交换零行已付，不在此重证 |
| 177.2–177.3 | 183.2–183.3的两个真实外层与同一 $K$ | 不借入177.1的 $c\circ r=0$ 或零重叠前件 |
| 163.1，实际框架 $(H,e,J)$ | 182.6、183.6；首槽参数 $2\lambda,2\nu$，第二输入 $a=z+d$ | 只给 $H$-奇投影，不替换完整外值 |
| 165.2–165.12 | 184.2–184.5共同读取后取 $\mu=\nu\epsilon$、$\sigma=\eta$ | 真实平方与乘积先接通，再复用固定标量排零 |

新增选择的PB三元组只有 $(h,x,h\circ x)$；它的正外层及反向值由
同一旧 $K$ 关联，负外层由真实零标签排零。这是相对已付163.1、174.1
的调用说明，不把这些既有定理的证明成本说成一次PB。

**定义 185.2（新识别的准确子域及其边界）。** 183.1在全部182.2分支
生产 $[s,r]=0$ 及 $z_{\rm e}\circ r=0$；184.1只在另外给定
$[s,z]=0$ 时识别完整旧值。具体边界为：

1. 当 $\lambda=0$ 且 $[s,z]=0$，$c=\nu s$ 满足
   $[c,z]=0$、$c^2=\nu^2u$、$[c,e]=0$。这是181.1交换分解方向的一个
   充分子类；并未预付177.1的 $c\circ r=0$、176.3的
   $\mathcal U_r(c^2)=0$ 或179.1的 $[r,x]=0$。
2. 当 $\lambda\ne0$ 且 $[s,z]=0$，仍有184.1，但
   $[c,z]=\lambda[h,z]=2\lambda hz$ 可以非零。因此证明并不把所有
   输入限制到177.1的交换分解上。$s$ 可在三轴共同交换子中而不全局
   中央；$c$ 不必属于 $\mathbb Ru+\mathbb Rh$。
3. $\nu=0$ 或 $s=\pm u$ 的完整旧值已由166.1支付，不计为新增范围。
   $z=0$ 已由174.1支付。一般 $z^2$ 则不要求中央、可逆或有限谱。
4. 没有 $[s,z]=0$ 时，只得 $P_s^+z\circ r=0$；还没有
   $P_s^-z\circ r=0$。183.1本身不生产这条分支上的 $r=0$、
   $[r,x]=0$、$\mathcal U_r(c^2)=0$ 或 $c\circ r=0$。
5. 任意 $c\in\operatorname{Com}_h$ 不一定具有182.2–182.3的形式。
   一般 $2hc$ 不能未经证明就当成某个实际单位平方轴的实仿射标签；
   域外谱符号、平方根、逆元或归一化都不供应那根原轴和实际伴轴值。
   一般181.1完整保留，也没有完整P2/PB反模型或全域不可能性结论。

[静态卷](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)
50–51的原投影角闭合与限制已付，但不包含一般
$D(U_pa,U_pb)=U_pD(a,b)$。本证明没有分别算出 $s$ 的两角旧值再相加；
183.3始终是一份跨全部原域的相关外值。
[原多项式卷](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)
80–88已付全部实际混合二阶有限商角、块内共同取向及其秩一小连接行；
182–184不重证这些结果，也不要求有限商或有限商族分离原域。
该卷72.2、77.1的完整连续标量端点域、180.4–180.5列出的旧双线性、
原P3、有限复Gram、原R与通常／相反乘法继续守其已付范围，不再列为
该域缺口。一般原系数域、任意首标签、无实际框架的原域、全局旧双线性、
原P3、全部有限旧复Gram、原R、同一旧结合乘法及原完成运输，仍各守
181.2的准确未付接口。局部旧值识别不减少独立原公理数。

**定义 185.3（成熟先例的数学用途）。** 有限Jordan二次表示及JC环境
恒等式复用van de Wetering，[*Commutativity in Jordan Operator Algebras*](https://arxiv.org/html/1912.01903v1)，
Proposition 2.21、Proposition 3.2及式(2)。它们解释已知乘法的二次表示
保正及交换子对应，不给未知 $D$ 的任何正则性。共同读取所用成熟接口
为Blackadar，[*Operator Algebras*](https://www.bruceblackadar.com/Mathematics/Cycr.pdf)，
II.6.1.8（不可约交换子为 $\mathbb CI$）、II.6.3.1（正的态延拓）、
II.6.3.3、II.6.3.5（纯态取范数及态分离）、II.6.4.9（不可约表示
取范数并分离）。这些文献工具和165的标量排零仅是承重证明的中间
输入，不各立为新增结果。

Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，
PNAS 95，6596–6601，DOI [10.1073/pnas.95.12.6596](https://doi.org/10.1073/pnas.95.12.6596)，
Dynamical Correspondences及Theorem 1的动力对应已是到斜序导子的线性
映射。Baez，[*Getting to the Bottom of Noether's Theorem*](https://arxiv.org/html/2006.14741v5)，
动力对应定义及Theorem 12亦明确保留这一线性前件和相容方程。
这些成熟重构定理不供应182.1中未知原 $D$ 的线性性，因而不能替代
183.7的同一外值比较。这里的新增身份归于上述原接口的综合，不作
一般Jordan／Lie–Jordan重构或历史原创性主张。

## 186. 七项原量子来源合同的准确消费者

**定义 186.1（复Hilbert、可观测量与相干叠加）。** 完整保持145.1–145.7、
155.1、160.3、171.1–171.7、181.3及原多项式卷87.1的全部原合同，
下列七项是182–184的消费者对应，不取代或缩减任何一项。
184.1只认回同一原 $h$ 行在182.2及 $[s,z]=0$ 分支的旧值；
139–140的数学Hilbert载体与系数矩阵几何仍需一般旧响应识别才能成为
同一旧全域共同乘法。唯一原 $\Omega$、原 $E/S/D$、跨评价配对、
具名可取得标签、native、全词同一 $q,K,J$、parent/ready、合法控制及
实际相干叠加准备，仍完整取171.1及其静态卷8.3–8.4、14.2、25.1和
三标签卷8.2–8.5、80.1的原来源。辅助新轴、正读取和Bloch几何不
产生全 $B(H)$ 的可取得像、原完备性或实际准备；无轴及一般原域保留。

**定义 186.2（原态、效果、质量与Born）。** 184.5只是同一原P2的数学
态读取。Born仍绑定171.2、145.2及其静态卷25.1第2行的同一原评价、
原事件、准确效果区间、全部实际完整菜单和接受归属；只对该菜单的
严格正总质量归一。零、不等、次归一质量、原 $q$、中心权、中心经典
混合、经典不等维块和静默部分完整保留。共同根、抽签、mark、
$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度、P9及独立
$W_e$、全部原中间切口和固定支持全质量仍须原来源。数学正延拓不
证明实际准备或菜单齐备，不将一般无限维态替换成有限密度矩阵。

**定义 186.3（native、真正相关联合与张量）。** 183.3的同一个数学
输出不替代171.3、145.3、静态卷25.1第3行、53.1及单位桥95.2、116.1
要求的同一个实际非零相关联合。原全词 $K/J$、交叉零、共同生成与
分离、满足局部全矩阵前件的忠实同向交换两腿、共同实现、所需重数、
全部真正相关输入、中央对、经典及不等维块和递归同源参考均保留。
分别可达、相同边缘、同一数学商或相同取向不供应共同来源；
$s$ 与三轴交换不自动赋予它一个物理子系统的身份。

**定义 186.4（typed CP、Kraus接线与整台参考）。** 完整保持171.4、
145.4及静态卷25.1第4行：原未归一回溯、每个合法typed前接／后接、
反变合法复合、typed分区、全未来自然性和原箭头商下降仍须原合同。
CP所需同源参考覆盖整台实际箭头，包括系统、整个环境、全部成功／
失败／细记录／port／post-port输出及每份输出的每个合法未来。
系统腿与参考腿须共同真支持且忠实同向交换；三实际投影、各自支持内
补、共同真实支持上的准确运输、全部相关正输入的intertwining与
夹界、每个所需有限递归深度和累计支持完整链均保留。支持内补不改成
环境补；184.2的读取子代数与正的态延拓均不产生实际箭头、参考或CP。

**定义 186.5（仪器、TP、更新与Lüders）。** 完整保持171.5、145.5及
静态卷25.1第5行的全部原输入运输、完整typed菜单、整台环境和上述
所有输出及其未来、原接受端、真正分组遗忘、AC、精确 $N_u$、X/Xs、
原平方根词及其接受条件。TP需要完整单位分区；Lüders另需同一个完整
输出的像内射线校准。只对正输出质量归一，零分支保留。密度、迹类和
算子Kraus公式只在准确合格的有限全矩阵原域，或另已供应所需正常
物理表示、指定前对偶与所需收敛且确实适用的域消费。184.4的同一平方
保持不制造原平方根词、完整仪器或接受端。

**定义 186.6（全部历史、全未来、真实返回与CountRead）。** 完整保持
171.6、145.6、静态卷8.4、25.1第6行及单位桥原消费者的全部量词：
所有合法顺序／自适应／并行历史、每份输出每个合法未来、整个环境、
全部细记录与泄漏、停止／拒绝／销毁、真正分组遗忘、同数两侧真实
返回和同数逆向真实返回。CountRead仍绑定读后同一原完整活动输入及
全未来返回；负提升两条活路的分别控制与相干聚合、具名分析词到原
完整菜单及接受端的接线须原生构造。原 $B$ 的精确正生成与另名
$B_{\rm cl}$ 的闭正生成不混同。无限历史、无限／非离散记录、可数
可加、正常性和指定前对偶保留各自原来源。程序、实际读取次序、原
$q$-零集和AC方向不由矩阵相同而等同；两种有限偶奇及一次PB提升不
供应真实双向返回或无限记录的可加性。

**定义 186.7（动力、物理钟、能量与共同尺度）。** 完整保持171.7、
145.7及静态卷25.1第7行：同一旧全域乘法、保持可能不完备原域的流、
实际相位和门序列、可逆一参数群、原物理钟、所需强连续酉实现、
生成元定义域、Hamiltonian的能量解释、共同作用量、共同正 $\hbar$
和共同仪器仍须同源供应。原 $\sigma,t_0,d$、固定域、resolvent与
$3s+r\le1$ 保持其合同含义，不与182.2的反射标签或183.9的余量混淆。
$\lambda,\nu$ 和数学态参数不供应物理时间、控制成本或钟能量；数学
有界候选导子不替代一般无界生成元。184.1的受限旧值不能直接升级成
全域旧响应动力或完整量子物理来源。

## 187. 两种二元偶奇与有限第三标签的完整直观含义

**定义 187.1（原关系、减少的自由度与剩余来源）。** 完整候选仍从同一
原世界的两标签有向正二表出发，同时保留原相加三角的实正性、单位
小窗口和每个原三标签的正反配平；没有先规定未知响应可以相加、连续
或穿过数学商。实际三轴是这份关系中已经存在的有限骨架，系数仍可
无限维、彼此不交换，原标签域也可不完备。固定 $h$ 后，每个输入有
与它交换的部分 $c$ 和反交换的横向部分 $z$；横向旧值已知是 $t$，
完整旧值还可能带一份与 $h$ 交换的余量 $r$。这里再给一面确实属于原
域的两面反射 $s$，要求它与实际 $h,e$ 交换，并把交换系数限制成
$c=\lambda h+\nu s$。相对 $h$ 和相对 $s$ 是两种不同的二元偶奇；
它们共同给四种符号，却没有把整个世界压成四个实数。把 $h$ 沿反射
翻向，得到的 $H=hs$ 确实还是原单位轴，且先用旧横向行认出它的真正
伴轴响应 $J=sj$，才能说新旧框架有同一取向。随后只把同一个实际
第三标签 $k=h\circ x$ 加入原PB：负外层准确碰到零标签，正外层的反向
首标签准确落在新轴的已知仿射行上。因此两种读法必须回答同一份旧
外值；再按原 $h$ 偶奇拆开，就迫使余量不能跨越 $s$ 的两个扇区，并
迫使它与 $z$ 留在同一扇区的部分反交换。若 $z$ 本来就不跨这两个
扇区，这个关系覆盖整个 $z$；把同一余量一起放进读取代数后，每个
不可约读取才真正成为已经认识的二阶几何，原二表正性便排除所有非零
余量。这说明在所写的完整受限域里，加入这份算子系数偏置不改变原
$h$ 响应；既不是先拼接两个零行，也不是另画一张标准响应表。若 $z$
跨扇区，仍缺它另一部分与余量的联系；一般 $c$ 也未必给出这样的原
反射轴，不能用域外谱符号代替。有限三轴、二阶读取和两种偶奇只描述
关系几何，不证明物理空间三维。这里减少的是受限域中旧输出可另选的
自由度，原公理数及全部七项实际来源条件没有减少：同一个原世界的
准备、零及不等质量、实际完整菜单与Born接受、真正相关联合、整台
仪器和环境记录、递归参考、全部合法历史未来、真遗忘及真实双向返回、
无限计数、保持原域的动力、物理钟、能量和共同正尺度，仍各须原合同
中的实际来源，不能由数学态、取向、矩阵坐标或完成替世界供应。

## 追加锚（本行以下为增补区）

## 188. 仿射首标签与同一反射框架的完整前件

**定义 188.1（完整原候选与实际轴）。** 完整保持161.1、173.1–173.2、182.1的同一原 $E,C,u,N,\mathcal P,S,D$。A1是全部原有向Hermitian二表正性；A2是原相加三表及其排列的实部正性和 $(1,-1,-1)$ 零二次值；A3是原单位平方及同一固定有理小窗口。准确锥、全部正评价与零、不等、次归一质量不变。仍为含单位稠密实Jordan包含 $E\subset X\subset\mathcal A_{\rm sa}$、$\mathcal A=C^*(X)$，$S=\circ$；$X$ 不必填满环境，原域可以不完备、不可分。同一个未知总映射只另取全部原P2和完整PB：

$$
\begin{gathered}
|\phi D(a,b)|^2\le\phi(a^2)\phi(b^2)-\phi(a\circ b)^2,\\
v=D(a,b)-a\circ c,\qquad w=a\circ b+D(a,c),\\
D(b+v,c+w)-D(b-v,c-w)=-2b\circ v-2c\circ w.
\end{gathered}
\tag{188.1}
$$

不预付旧 $D$ 的一般可加、齐次、连续、可测、单位平移、协变、商下降或完成延拓。实际原框架仍为 $h,e,j=D(h,e)$、$h^2=e^2=j^2=u$、两两Jordan正交，$Q=ihej$ 是既有辅助中央自伴对合，$T_hz=iQhz$ 在原 $h$-奇域由有限Jordan式给出。163.1已经识别

$$
P_h^-D(\alpha u+\beta h,y)=\beta T_hP_h^-y,\qquad
U_hy=hyh,\quad P_h^\pm=(I\pm U_h)/2.
\tag{188.2}
$$

以下先识别这条原仿射行的交换零值，再将其用于182.1的第二实际框架。不把188.2的投影等式当成完整旧值。

## 189. 两角读取中的仿射交换零行

**定理 189.1（整个原仿射首槽的交换零行）。** 在188.1下，对任意实 $\alpha,\beta$ 及原 $y\in E$，

$$
\boxed{[h,y]=0\quad\Longrightarrow\quad D(\alpha u+\beta h,y)=0.}
\tag{189.1}
$$

证明。置 $a=\alpha u+\beta h$、$g=D(a,y)$。188.2给 $g$ 为 $h$-偶。对每个 $\epsilon=\pm1$，取实际 $p=(u+\epsilon h)/2$，记

$$
\kappa(v)=pvp=\mathcal U_pv,\quad
Y=\mathcal U_pX,\quad E_p=\mathcal U_pE,\quad
\mu=\alpha+\epsilon\beta,\quad B=\kappa(y),\quad G=\kappa(g).
\tag{189.2}
$$

零角直接贡献零。其余 $Y$ 是单位为 $p$ 的JB代数，$E_p\subset E$ 在其中范数稠密。$\kappa$ 在全原锥上正，但只在下面准确范围内保持乘法：若 $v$ 为 $h$-偶，则对任意自伴 $w$，

$$
\kappa(v^2)=(\kappa v)^2,\qquad
\kappa(v\circ w)=\kappa v\circ\kappa w.
\tag{189.3}
$$

这是174.3的既有块乘法。任意 $Y$ 上正 $\rho$ 的拉回 $\rho\kappa|_E$ 都能读取188.1。因而对两个实际偶输入，其P2准确成为像的P2；若其中一个偶输入角像为零，则该张表的旧输出角像为零。这里不对一般非偶的零角像输入作此断言。

若 $\mu=0$，原 $(a,y)$ 的首平方角像为零，故 $G=0$。以下 $\mu\ne0$。证明复用原多项式卷4.2的标量像排零机制；下面逐项支付其对角压缩的用途，不把 $\kappa$ 当作全域同态。

先固定任意原偶 $v$，记 $B_v=\kappa(v)$、$g_v=D(a,v)$、$G_v=\kappa(g_v)$。188.2使 $g_v$ 仍偶。若 $B_v$ 半定而 $G_v\ne0$，在 $C^*(p,G_v)$ 选择非零谱值 $Z$ 的支撑态，正延拓到角环境并限制为 $Y$ 上态 $\rho$，满足

$$
\rho(G_v)=Z\ne0,\qquad \rho((G_v-Zp)^2)=0.
\tag{189.4}
$$

取实际比例第三标签 $q_0=ta$，$t=Z/(1+\mu^2)$。原比例零行给 $D(a,q_0)=0$。PB $(a,v,q_0)$ 的完整两外层及角像为

$$
\begin{array}{c|c|c|c}
R_\pm&S_\pm&\kappa R_\pm&\kappa S_\pm\\\hline
v\pm g_v\mp ta^2&ta\pm a\circ v&
B_v\pm G_v\mp t\mu^2p&t\mu p\pm\mu B_v.
\end{array}
\tag{189.5}
$$

四个实际输入均偶，故189.3允许像Gram计算，且
$\kappa S_+-\mu\kappa R_+=\kappa S_-+\mu\kappa R_-=\mu(Zp-G_v)$。
189.4使两份预算为零；PB右端角像准确为 $-2B_v\circ G_v$。Schwarz给 $Z\rho(B_v)=0$。由 $B_v$ 半定及 $0\le B_v^2\le\|B_v\|(\pm B_v)$，得 $\rho(B_v^2)=0$；原 $(a,v)$ 的P2却给 $Z^2\le0$，矛盾。因此

$$
v\text{ 为原偶元},\quad\kappa(v)\text{ 半定}
\quad\Longrightarrow\quad \kappa D(a,v)=0.
\tag{189.6}
$$

## 190. 固定旧输出的角内反交换关系

证明189.1（续）。回到同一固定 $y,g,B,G$。对满足 $\rho(G)\ne0$ 的 $Y$ 纯态 $\rho$，在 $Y^{**}$ 取其最小支撑 $f$，置

$$
K=\frac{\mu G}{1+\mu^2},\qquad
\tau=\rho(K)\ne0,\qquad C_0=\mathcal U_K(f)/\tau.
\tag{190.1}
$$

原多项式卷4.8–4.9与174.8–174.10使用的同一JB支撑和Peirce计算给：$C_0$ 按 $\tau$ 符号半定，$\rho((C_0-K)^2)=0$；有界Kaplansky逼近及 $E_p$ 的范数稠密性供应实际 $v_i\in E_p$，使

$$
q_i=\operatorname{sgn}(\tau)v_i^2\in E_p,\quad
\sup_i\|q_i\|<\infty,\quad
\eta_i:=\rho\left(((1+\mu^2)q_i-\mu G)^2\right)^{1/2}\longrightarrow0.
\tag{190.2}
$$

网保留不可分情形；$f,C_0$ 及其根未输入旧 $D$。每个 $q_i$ 是实际偶的有符号平方，189.6给当前角的 $\kappa D(a,q_i)=0$。另一个角因 $q_i$ 像为零，由偶输入P2给输出角像零。188.2又使 $D(a,q_i)$ 偶，两角合起来才给真正原值 $D(a,q_i)=0$。

因此PB $(a,y,q_i)$ 的实际外层完整为

$$
R_\pm^{(i)}=y\pm g\mp a\circ q_i,\qquad
S_\pm^{(i)}=q_i\pm a\circ y.
\tag{190.3}
$$

它们均偶，像满足
$\kappa S_+^{(i)}-\mu\kappa R_+^{(i)}
=\kappa S_-^{(i)}+\mu\kappa R_-^{(i)}=(1+\mu^2)q_i-\mu G$。
分别用两张实际P2及已知实Gram剪切，得到

$$
|\rho\kappa D(R_\pm^{(i)},S_\pm^{(i)})|
\le\rho((\kappa R_\pm^{(i)})^2)^{1/2}\eta_i
\le M_0\eta_i.
\tag{190.4}
$$

$M_0<\infty$ 只依赖固定 $B,G,\mu$ 及190.2的一致界。PB右端角像始终为
$-2B\circ(G-\mu q_i)-2q_i\circ\mu B=-2B\circ G$。
故 $|\rho(B\circ G)|\le M_0\eta_i$，迫使这份固定读取为零。

若纯态 $\rho(G)=\rho(G^2)=0$，Schwarz直接给同一零值；若 $\rho(G)=0$ 而 $\rho(G^2)>0$，取充分小非零实 $t$，以正锥自同构 $\mathcal U_{p+tG}$ 归一地变形纯态。它读 $G$ 为

$$
\rho_t(G)=\frac{2t\rho(G^2)+t^2\rho(G^3)}{1+t^2\rho(G^2)}\ne0,
\qquad \rho_t\longrightarrow\rho\text{ 范数收敛}.
\tag{190.5}
$$

已证分支使 $\rho_t(B\circ G)=0$，所以原零读取亦为零。纯态分离 $Y$，得

$$
B\circ G=0,\qquad BG=-GB\quad\text{在角环境中成立}.
\tag{190.6}
$$

支撑、Peirce逼近及纯态变形均准确复用原多项式卷4.8–4.15和174.8–174.17；新增输入接线是每次原仿射行的实际输出确实偶。极限只估计固定 $B\circ G$，未对未知响应取输入或输出极限。

## 191. 两张固定原表与最后一份非偶输出

证明189.1（续）。准确调用PB $(y,a,\mu y)$，原反对称性和比例零值给 $D(y,a)=-g$、$D(y,\mu y)=0$。两份完整外层为

$$
\begin{aligned}
a_0&=a-g-\mu y^2,&b_0&=\mu y+a\circ y,\\
a_-&=a+g+\mu y^2,&b_-&=\mu y-a\circ y.
\end{aligned}
\tag{191.1}
$$

四输入均偶，$\kappa b_-=0$，故P2给负外值角像零。PB右端角像为 $2\mu G$；同一原域中的两张固定表具有

$$
\begin{array}{c|c|c}
\text{第一输入角像}&\text{第二输入角像}&\text{实际旧输出角像}\\\hline
\mu p&B&G\\
A_0:=\mu(p-B^2)-G&2\mu B&2\mu G.
\end{array}
\tag{191.2}
$$

不在角上定义新响应。190.6使 $B^2$ 与 $G$ 交换。对 $C^*(p,B^2,G)$ 的字符写 $B^2\mapsto v\ge0,G\mapsto\zeta$。若 $\zeta\ne0$，第一张P2给 $|\zeta|\le|\mu|\sqrt v$，从而 $v>0$；字符态的GNS向量与 $B$ 作用后归一的向量组成同一个二维不变空间。在其中 $B=\sqrt v\,\sigma_x$、$G=\zeta\sigma_z$。第二张表的全部实单位向量读取给

$$
|\zeta\gamma|\le\sqrt v\,|\mu(1-v)\gamma-\zeta|
\quad(-1\le\gamma\le1),\qquad |\zeta|\le|\mu|\sqrt v.
\tag{191.3}
$$

这是原多项式卷4.17的同一成熟二表计算，参数为角单位 $p$、$\mu,B,G$。若 $v\ne1$，令 $a_*=\mu(1-v)\ne0$：当 $0<|\zeta|\le|a_*|$，取 $\gamma=\zeta/a_*$ 得矛盾；当 $|\zeta|>|a_*|$，取 $\gamma=\operatorname{sgn}(a_*\zeta)$，得 $|\zeta|\le\sqrt v(|\zeta|-|a_*|)$。$v<1$ 时不可能，$v>1$ 时却要求 $|\zeta|\ge|\mu|\sqrt v(\sqrt v+1)$，仍违反第一张表。因此字符分离给

$$
(B^2-p)G=0.
\tag{191.4}
$$

还须排除 $v=1$ 的残余。取真正原标签 $k_0=D(b_0,a_0)$、$g_0=b_0\circ a_0$。191.2与已知乘法给

$$
\kappa k_0=-2\mu G,\quad
G_0:=\kappa g_0=2\mu^2(B-B^3),\quad
G_0G=GG_0=0,\quad A_0\circ G=-G^2.
\tag{191.5}
$$

$k_0$ 不必偶；$a_0,b_0,g_0$ 确实偶。实际PB $(b_0,a_0,0)$ 的完整外层是 $(a_0+k_0,g_0)$、$(a_0-k_0,-g_0)$，右端为 $-2a_0\circ k_0$。对任意角正 $\rho$，正读取 $\phi=\rho\mathcal U_G\kappa|_E$ 的两个第二平方对角均为

$$
\phi(g_0^2)=\rho(\mathcal U_G(G_0^2))=0.
\tag{191.6}
$$

P2遂消去两份外值的 $\phi$ 读数，不需压缩第一输入的平方。右端只因 $a_0$ 偶便可用189.3，即使 $k_0$ 非偶仍有

$$
0=-2\phi(a_0\circ k_0)
=4\mu\rho(\mathcal U_G(A_0\circ G))
=-4\mu\rho(G^4).
\tag{191.7}
$$

$\mu\ne0$、正泛函分离及C*范数恒等式给 $G=0$。两角分别成立，原 $g$ 又偶，所以两份对角压缩合起来给 $g=0$，完成189.1。零角、$\alpha\pm\beta=0$、负系数和零输入均已包含。∎

证明没有宣称 $\kappa$ 为全域同态，也没有宣称一般两个偶输入的旧输出偶。只有仿射首槽的偶输出由188.2供应；最后不具此性质的 $k_0$ 只出现在已经逐项合法的两个读取中。

## 192. 任意实首槽强度下的同一反射余量

**定理 192.1（同一原余量的双偶性）。** 保持182.1的完整原候选及实际 $h,e,j,s$ 条件。本节另取任意实 $R,\lambda,\nu$ 及原 $h$-奇 $z\in E$，置

$$
\begin{gathered}
c=\lambda h+\nu s,\quad x=c+z,\quad k=h\circ x=\lambda u+\nu H,\quad H=hs,\\
t=D(h,z)=iQhz,\quad g=D(Rh,x)=Rt+r.
\end{gathered}
\tag{192.1}
$$

则同一原余量满足

$$
\boxed{[h,r]=[s,r]=[c,r]=0,\qquad P_s^+z\circ r=0.}
\tag{192.2}
$$

这里不要求 $z$ 为 $s$-偶或 $s$-奇；$g=Rt+r$ 是由163.1识别奇投影后的定义，不是第一槽齐次假设。

证明。$R=0$ 时原零输入P2给 $g=r=0$。$\nu=0$ 时166.1给 $g=Rt$，同样成立。以下 $R\nu\ne0$。163.1首先给 $r$ 为 $h$-偶。182.2供应第二实际框架 $(H,e,J)$ 及同一 $Q$。189.1在原 $h$ 框架上给实际 $D(Rh,Rk)=0$，因为 $Rk$ 与 $h$ 交换。准确调用PB $(Rh,x,Rk)$：位移是 $g-R^2c,Rk$，两份完整外层为

$$
\bigl((1-R^2)c+z+g,2Rk\bigr),\qquad
\bigl((1+R^2)c+z-g,0\bigr).
\tag{192.3}
$$

负外层第二标签实际为零。由 $k^2=c^2$、$x\circ c=c^2+z\circ c$，原PB与反对称性准确给

$$
D\bigl(2Rk,(1-R^2)c+z+g\bigr)
=2x\circ g-2R^2z\circ c.
\tag{192.4}
$$

用182.4的原有限投影写 $z_{\rm e},z_{\rm o},t_{\rm e},t_{\rm o},r_{\rm e},r_{\rm o}$，并令 $M=z\circ r$、$M_{\rm e}=P_s^+M$。$c$ 为 $H$-偶，$U_H=U_hU_s$，故192.4的实际第二输入的 $H$-奇部分是 $z_{\rm e}+Rt_{\rm e}+r_{\rm o}$。163.1在第二实际框架上，首槽取 $2Rk=2R\lambda u+2R\nu H$，得到同一左值的投影

$$
P_H^-D\bigl(2Rk,(1-R^2)c+z+g\bigr)
=2R\nu s(t_{\rm e}-Rz_{\rm e})+2R\nu iQhsr_{\rm o}.
\tag{192.5}
$$

这里只用 $iQht_{\rm e}=-z_{\rm e}$，未把未知 $D$ 展开。另一方面，在192.4右端只展开已知Jordan乘法。$z\circ t=h\circ t=0$，且

$$
\begin{gathered}
c\circ t=\nu s t_{\rm e},\qquad
c\circ r=\lambda hr+\nu s r_{\rm e},\qquad
z\circ c=\nu s z_{\rm e},\\
P_H^-M=M_{\rm e}.
\end{gathered}
\tag{192.6}
$$

于是该右端的 $H$-奇部分准确为

$$
2R\nu s t_{\rm e}-2R^2\nu s z_{\rm e}
+2\lambda hr_{\rm o}+2M_{\rm e}.
\tag{192.7}
$$

比较192.5、192.7，得

$$
R\nu iQhsr_{\rm o}=\lambda hr_{\rm o}+M_{\rm e}.
\tag{192.8}
$$

含 $r_{\rm o}$ 的两项为 $h$-偶，$M_{\rm e}$ 为 $h$-奇。因此分别投影，再仅在环境代数中左乘 $h$，得到

$$
M_{\rm e}=0,\qquad (R\nu iQs-\lambda u)r_{\rm o}=0.
\tag{192.9}
$$

后式左乘 $-R\nu iQs-\lambda u$，利用 $(iQs)^2=-u$，便有 $((R\nu)^2+\lambda^2)r_{\rm o}=0$。因 $R\nu\ne0$，得 $r_{\rm o}=0$，即 $[s,r]=0$。再结合 $[h,r]=0$ 得 $[c,r]=0$；$r$ 现为 $s$-偶，使 $M_{\rm e}=z_{\rm e}\circ r=0$。没有把环境逆元送进原 $D$，负 $R,\nu$ 及 $R^2=1$ 均已包含。∎

**定理 192.2（跨反射扇区的原值及强度比例）。** 在192.1下，若还满足 $sz=-zs$，则

$$
\boxed{D(Rh,\lambda h+\nu s+z)=R\,iQhz
      =R\,D(h,\lambda h+\nu s+z).}
\tag{192.10}
$$

对全部实 $R,\lambda,\nu$ 及任意幅度的原 $z$ 成立，不要求 $z^2$ 中央或可逆。

证明。$R=0$ 已由零输入P2支付。取 $R\ne0$，用192.1的同一 $g=Rt+r$。$z,t$ 同时为 $h$-奇、$s$-奇，故为 $H$-偶；$h,r$ 也与 $H$ 交换。因此 $g,Rh-g,Rh+g$ 均为 $H$-偶。实际PB $(x,Rh,0)$ 的内值是 $-g,0$，位移为 $-g,Rk$，故完整地

$$
D(Rh-g,Rk)-D(Rh+g,-Rk)=2Rh\circ g.
\tag{192.11}
$$

$Rk=R\lambda u+R\nu H$。189.1在真正的 $H$ 框架上，分别对实际 $(Rk,Rh-g)$、$(-Rk,Rh+g)$ 给零；原反对称性消去192.11的两份实际外值。由于 $h\circ t=0$，右端为 $2Rhr$，所以 $r=0$。对 $R=1$ 的同一结论给192.10的第二个等号。这是在原限定域上证明的第一槽比例，并未将任何齐次规律赋给一般未知 $D$。∎

## 193. 非中央奇异平方的非空实例

**定义 193.1（标准六阶模型的准确参数）。** 取 $E=H_6(\mathbb C)$、$u=I_6$、标准锥及范数、全部正评价，$S=\circ$、$D_*(a,b)=i[a,b]/2$。P2和完整PB直接复用原多项式卷6.6–6.7的结合乘法计算，不另计标准模型的新意。用标准Pauli矩阵及三阶矩阵单位，置

$$
\begin{gathered}
h=\sigma_z\otimes I_3,\quad e=\sigma_x\otimes I_3,\quad
j=-\sigma_y\otimes I_3,\quad Q=I_6,\\
S_0=\operatorname{diag}(1,-1,1),\quad K_0=E_{12}+E_{21},\quad
s=I_2\otimes S_0,\quad z=\gamma\sigma_x\otimes K_0,\quad\gamma\ne0.
\end{gathered}
\tag{193.1}
$$

它们满足全部实际框架前件，$hz=-zh$、$sz=-zs$，且 $z^2=\gamma^2I_2\otimes\operatorname{diag}(1,1,0)$ 奇异并非全矩阵中心元。对任意实 $R,\lambda,\nu$，同一标准值为

$$
D_*(Rh,\lambda h+\nu s+z)=-R\gamma\sigma_y\otimes K_0=R iQhz.
\tag{193.2}
$$

当 $\nu\ne0$ 时，非零 $z$ 不满足184.1的 $[s,z]=0$，所以192.2确有该已付偶分支之外的实际输入。此例只检验定义域非空和符号，不把标准表替换进一般未知 $D$。

## 194. 新连接、完整候选与量子消费者的范围

**定义 194.1（准确来源与未付混合）。** 承重综合归为 $\texttt{repo-derived}$。189.1把163.1的实际偶输出接到原多项式卷4.2、174.1已用的角内排零机制；192.1用同一原PB把183.1的余量关系扩至任意实首槽强度；192.2再用新零行读取另一份实际PB，识别反射奇分支并证明该原限定行的强度比例。谱支撑、纯态变形、Peirce逼近、二维固定表和正读取均是原来源的成熟中间工具，不各自取得新内容名义。

具体复用163.1、150.1、166.1、182.2、183.1；原多项式卷4.5–4.20供应189–191所列准确参数计算，174.3供应只需一个因子偶的压缩乘法。支撑和逼近的出处保持174.1所引Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，Lemma2.6.3、Lemma4.1.9、Theorem4.4.3、Theorem4.5.12，以及Hamhalter，[*Pure states on Jordan algebras*](https://dml.cz/bitstream/handle/10338.dmlcz/133911/MathBohem_126-2001-1_7.pdf)，§1；C*读取和态延拓保持185.3的Blackadar接口。没有文献穷尽、历史优先权或外部开放问题解决的声称。

完整候选仍是188.1的原A1–A3/P2及全部PB，独立公理数未减少。184.1在首强度一识别原 $s$-偶分支，192.2在全部实首强度识别原 $s$-奇分支；未知 $D$ 仍不可据此在任意 $z=z_{\rm e}+z_{\rm o}$ 上拆和。一般交换系数 $c$ 也未必为 $\lambda h+\nu s$，无实际框架的原域仍保留。一般旧双线性、全有限旧复Gram、原R、完整旧乘法、原完成运输及完整量子重构未由此支付。有限商的已付二阶角和秩一小连接行仍取原多项式卷80–88，不把新框架存在性代入一般商。原多项式卷102–108在秩三Euclidean丛的截面域上，由分离的完整二阶评价商生产连续取向及同旧表静态消费者；当前一般JC域未给出该项分离纤维前件，不把那一特殊域的全表识别移来替代本节证明。

**定义 194.2（七项同源消费者逐项保持）。** 完整保持186.1–186.7及其全部上游量词，下表只标识本组定理的供应和仍须的原接口：

| 原消费者 | 新增供应及仍存接口 |
| --- | --- |
| 复Hilbert、可观测量与相干叠加 | 只识别所写原行；同一全域旧乘法、唯一 $\Omega$、native、全词 $q,K,J$、parent/ready、可取得标签、合法控制及实际准备仍须原来源。 |
| 态、效果、质量与Born | 原事件、准确效果区间、全部实际完整菜单及接受归属不变；仅对该菜单正总质量归一，零、不等、次归一质量、中心权、经典不等维及静默块保留，数学正读取不增加准备。 |
| 真正相关联合与张量 | 同一实际非零相关联合、忠实同向交换局部腿、共同生成分离、重数、所有相关输入、中央对及递归同源参考仍须原合同；$s$ 与框架交换不供应物理子系统。 |
| typed CP、Kraus接线与整台参考 | 原回溯、typed前后接及合法复合、全未来自然性、分区和箭头商下降保留；系统、整个环境、全部成功失败细记录及port/post-port输出与每个合法未来、三实际投影及各支持内补、共同真实支持和每个有限递归深度的准确运输仍须原生供应。 |
| 仪器、TP、更新与Lüders | 原完整菜单、整台环境及所有输出未来、真正分组遗忘、接受端、AC、精确 $N_u$、X/Xs、平方根词及接受条件不变；TP需完整单位分区，Lüders需同一完整输出的像内射线校准；只归一正输出，零分支保留，正常物理表示、前对偶和收敛另付。 |
| 历史、全未来、返回与CountRead | 全部合法顺序、自适应、并行历史及每个仍合法未来、整个环境细记录泄漏、停止拒绝销毁、真遗忘、同数两侧及逆向真实返回保留；读后同一原完整活动输入、负提升两活路分别控制与相干聚合、原完整菜单接线、精确 $B$ 与闭正生成 $B_{\rm cl}$、无限非离散记录的可数可加、正常性和指定前对偶仍须原来源。 |
| 动力、物理钟、能量与共同尺度 | 同一旧全域乘法、保持不完备原域的流、真实相位与门序列、可逆一参数群、物理钟、所需强连续酉实现、生成元域、Hamiltonian能量、共同作用量、共同正 $\hbar$ 和共同仪器保持；原固定域、resolvent和预算不被数学轴、参数或读取替换。 |

## 195. 同一比较的第二把尺与完整白话

**定义 195.1（两份原接法消去同一余量）。** 仍用原来的两两有向正表、相加三角、单位小窗和全部三者正反配平。先固定一根实际轴：横向输出已经认出，轴加上任意单位偏置后，对交换输入的输出虽只知为偶，却能被两扇原角窗口分别读回。每个窗口里首输入只剩一个实数；保留原配平的完整标签，已有标量排零机制便排除两角残余，所以这整条交换零行确实成立。现在给原轴任意实强度，让同一原横向输入跨过一面实际反射的两侧。第一份配平对同一实际输出的两种投影迫使未知余量相对原轴和反射都不变；这一步也容许横向输入混有两种反射奇偶。若横向输入纯跨反射，两次变号又使它和已知横向响应相对第二根实际轴不变。交换原演员位置、让第三标签取零，第二份配平的两张外表便都是第二根轴上的已知交换零行；同一次配平却要求它们的差读出原余量乘第一根轴及原强度。非零强度下余量只能为零，零强度本来就由正性给零。因此在这类原输入上，比较强度放大多少，旧响应也只能放大多少；比例成为结论，没有另加齐次公理。若横向输入同时混有两种反射奇偶，目前只得余量约束，仍不能把两个纯分支直接相加。这里的互易和等价接法相容不要求实际测量先后可交换；实际准备、菜单、联合、整台仪器、全未来返回、计数及物理时间尺度仍守194.2的原合同。

188–195为纸面定义、条件定理与证明，不冒领Lean kernel核验、摄入、冻结或完整量子重构。

## 追加锚（本行以下为增补区）

## 196. 同一原候选与一份交叉关系的准确目标

**定义 196.1（原条件和固定输出）。** 完整保持188.1、182.1的同一原 $E,C,u,N,\mathcal P,S,D$、A1–A3、准确锥、全部原正评价及零、不等、次归一质量、全部P2与完整PB。仍为含单位稠密实Jordan包含 $E\subset X\subset\mathcal A_{\rm sa}$、$\mathcal A=C^*(X)$，$X$ 不必填满环境，原域可以不完备、无限维、不可分。准确使用

$$
\begin{gathered}
|\phi D(a,b)|^2\le\phi(a^2)\phi(b^2)-\phi(a\circ b)^2,\\
v=D(a,b)-a\circ c_0,\quad w=a\circ b+D(a,c_0),\\
D(b+v,c_0+w)-D(b-v,c_0-w)=-2b\circ v-2c_0\circ w.
\end{gathered}
\tag{196.1}
$$

A1保留全部原有向Hermitian二表；A2保留全部实际相加三表及排列的实部正性和指定零向量；A3保留原单位平方及同一固定有理小窗口。旧 $D$ 不预付可加、齐次、连续、可测、单位平移、协变、商下降或完成延拓。实际 $h,e,j=D(h,e),s$、辅助中央自伴对合 $Q=ihej$ 和第二实际框架 $(H,e,J)$ 全取182.1–182.2。任取实 $R,\lambda,\nu$ 及原 $h$-奇 $z$，固定192.1的

$$
\begin{gathered}
c=\lambda h+\nu s,\quad x=c+z,\quad t=iQhz,\\
g_R=D(Rh,x)=Rt+r_R,\quad
z_{\rm e}=P_s^+z,\quad z_{\rm o}=P_s^-z.
\end{gathered}
\tag{196.2}
$$

192.1已经给 $[h,r_R]=[s,r_R]=[c,r_R]=0$ 及 $z_{\rm e}\circ r_R=0$。本节不假定 $z$ 只有一种反射奇偶；新增目标是证明另一项 $z_{\rm o}\circ r_R=0$ 一旦从原关系生产出来，就已足够排除整个余量，不再另留一份正性排零义务。

## 197. 共同轴余量的全复平面铅笔界

**定理 197.1（固定二表的锐平方缺口）。** 设 $\mathcal B$ 为含单位复C*代数，$h,x,r$ 自伴，$h^2=u$，$Q$ 为中央自伴对合。定义

$$
\begin{gathered}
c=(x+hxh)/2,\quad z=(x-hxh)/2,\quad
k=h\circ x,\quad t=iQ[h,x]/2,\quad g=t+r,\\
[h,r]=[c,r]=0,\qquad z\circ r=0.
\end{gathered}
\tag{197.1}
$$

若某个实 $\varepsilon\ge0$ 使每个数学态 $\phi$ 满足

$$
\phi(g)^2+\phi(k)^2\le\phi(x^2)+\varepsilon,
\tag{197.2}
$$

则 $\|r\|^2\le\varepsilon$。特别是准确P2的 $\varepsilon=0$ 迫使 $r=0$。这里的平方是读数的平方；没有将其换成 $\phi(g^2)$，也未假定 $[r,x]=0$。

证明。零代数直接成立。其余取共同含单位子代数
$\mathcal L=C^*(u,Q,h,c,z,r)$。由197.1，$hr$ 自伴且与每个生成元交换：对 $z$ 有 $(hr)z=h(-zr)=zhr$，对 $c,h,r,Q$ 则直接交换。因此 $hr\in Z(\mathcal L)$。不要求 $z^2$ 或 $c$ 中央，也不将 $hr$ 宣称为整个环境的中心元。

任取非零不可约表示 $\pi$，Schur引理给

$$
A=\pi(h),\quad X=\pi(x),\quad
\pi(Q)=\eta I,\quad \pi(hr)=mI,\quad
\pi(r)=mA,\quad \eta\in\{1,-1\},\ m\in\mathbb R.
\tag{197.3}
$$

每个像代数的态拉回 $\mathcal L$，再正延拓到 $\mathcal B$，所以同一197.2对实际联合像
$K=A\circ X$、$G=i\eta[A,X]/2+mA$ 成立。全部这些态准确分离正锥。对任意实 $p,q$ 及每个像态 $\psi$，有

$$
\begin{aligned}
&\psi(X^2)+(p^2+q^2)-2p\psi(K)-2q\psi(G)+\varepsilon\\
&=(p-\psi(K))^2+(q-\psi(G))^2
+\psi(X^2)+\varepsilon-\psi(K)^2-\psi(G)^2\ge0.
\end{aligned}
$$

因此得到算子不等式

$$
X^2+(p^2+q^2)I-2pK-2qG+\varepsilon I\ge0.
\tag{197.4}
$$

只在这个辅助像代数中置

$$
\zeta=p-i\eta q,\qquad B=AX-i\eta mA=A(X-i\eta mI).
\tag{197.5}
$$

$A$ 自伴且 $A^2=I$，直接乘法给完整恒等式

$$
\begin{aligned}
(B-\zeta I)^*(B-\zeta I)-m^2I
&=(X-i\eta mI-\zeta A)^*(X-i\eta mI-\zeta A)-m^2I\\
&=X^2+(p^2+q^2)I-2pK-2qG.
\end{aligned}
\tag{197.6}
$$

故对整个复平面，

$$
(B-\zeta I)^*(B-\zeta I)\ge(m^2-\varepsilon)I.
\tag{197.7}
$$

若 $m^2>\varepsilon$，记 $a=(m^2-\varepsilon)^{1/2}>0$。当 $B-\zeta I$ 可逆时，197.7及C*范数恒等式给
$\|(B-\zeta I)^{-1}\|\le a^{-1}$。其预解集非空，因为 $|\zeta|>\|B\|$ 时Neumann级数给逆；它本来开。它也闭：若预解点 $\zeta_n\to\zeta_0$，取 $n$ 使 $|\zeta_n-\zeta_0|<a$，则

$$
B-\zeta_0I=(B-\zeta_nI)
\left[I-(\zeta_0-\zeta_n)(B-\zeta_nI)^{-1}\right]
\tag{197.8}
$$

的第二因子由Neumann级数可逆。复平面连通使预解集成为全平面，与非零含单位复Banach代数的谱非空性矛盾。此处只在已经可逆的点估计逆范数，未把一般有下界的算子当成满射或可逆元。

因此每个不可约表示都满足 $m^2\le\varepsilon$，即 $\|\pi(r)\|^2\le\varepsilon$。不可约表示取范数并分离 $\mathcal L$，得 $\|r\|^2\le\varepsilon$。全程没有取未知响应的极限，辅助逆元和复参数也未成为原 $D$ 的输入。∎

常数一不可改小：在 $H_2(\mathbb C)$ 中取 $h=\sigma_z$、$Q=I$、$x=\alpha h$、$r=mh$，则 $t=0,k=\alpha I$，全部态的最大左侧超额准确为 $m^2=\|r\|^2$。这是197.1所述固定二表界的锐性实例；$m\ne0$ 时它不满足准确P2，不是完整原候选的反模型。

## 198. 一份反射交叉关系已等价于完整余量排零

**定理 198.1（同一原混合值的单项判据）。** 在196.1的全部原条件下，对每个实际196.2，无须假定 $z$ 为纯反射扇区，准确有

$$
\boxed{
D(Rh,\lambda h+\nu s+z)=R iQhz
\quad\Longleftrightarrow\quad z_{\rm o}\circ r_R=0.
}
\tag{198.1}
$$

右侧是待由原关系生产的结论，不是新增给完整候选的公理；本定理没有证明它一般成立。

证明。正向由 $r_R=0$ 直接成立。反向先处理 $R=0$：原零输入P2给 $g_R=r_R=0$。取 $R\ne0$，只归一这份固定输出为

$$
\widehat g=g_R/R=t+\widehat r,\quad\widehat r=r_R/R,\quad
|\phi(\widehat g)|^2+\phi(h\circ x)^2\le\phi(x^2)
\tag{198.2}
$$

对全部数学态成立。这来自原 $(Rh,x)$ 的两个显式平方因子和 $R^2$ 的约去，不是 $D$ 的第一槽齐次。192.1给 $[h,\widehat r]=[c,\widehat r]=0$、$z_{\rm e}\circ\widehat r=0$；198.1右侧又给 $z_{\rm o}\circ\widehat r=0$。只对已知Jordan乘法相加，得 $z\circ\widehat r=0$。197.1以 $\varepsilon=0$ 应用到同一固定 $h,x,\widehat g,\widehat r,Q$，使 $\widehat r=0$，从而 $r_R=0$。$\nu=0$ 也与166.1一致；负强度只通过非零实数的固定归一出现。∎

因此混合反射问题现在只须从原全部P2/PB生产这一份交叉Jordan零值；“它为零以后正性是否足够”已由197.1回答。纯奇分支192.2继续成立；当 $z_{\rm o}=0$ 时198.1右侧自动为零，所以它也将184.1的纯偶分支扩到任意实首槽强度。不以两个纯分支相加取得混合输入的右侧，也不把它当成已经由192.1支付。

条件域包含真正混合输入：在193.1的同一标准 $H_6(\mathbb C)$ 模型中另取 $z=\sigma_x\otimes(\delta E_{11}+\gamma K_0)$、$\delta\gamma\ne0$。则 $z_{\rm e}=\delta\sigma_x\otimes E_{11}$、$z_{\rm o}=\gamma\sigma_x\otimes K_0$ 都非零，标准旧值仍给 $r_R=0$；$z^2$ 在第三系数坐标为零、在前两坐标非零，故奇异且非中央。这里仅说明限定域非空，不把标准公式代入一般未知响应。

## 199. 来源、几何与量子消费者的完整边界

**定义 199.1（新增承重与成熟工具）。** 本组归为 $\texttt{repo-derived}$。197.1的承重连接是把同一反交换余量的 $hr$ 放入共同读取代数的中心，将全部固定二表读数接到197.6的同一个复算子铅笔，再由全平面统一下界排除非零轴余量。Schur、态正延拓、不可约表示取范数与谱非空性是成熟工具；预解集开闭及Neumann级数不各立为新发现。198.1消费192.1生产的共同交换关系和已付偶项零值，准确关闭交叉零值之后的剩余排零义务。

本卷179.1和静态卷5.7处理中央的标量余项 $\tau I$；这里不可约像的余项是 $mA$，不将两者混同。184.1还用 $s,z^2$ 的相对中心性化到二维；197.1不要求它们中央，也不要求有限维或任何有限商分离族。正延拓和不可约取范数保持185.3的Blackadar，[*Operator Algebras*](https://www.bruceblackadar.com/Mathematics/Cycr.pdf)，II.6.1.8、II.6.3.1、II.6.4.9的准确用途；谱非空性、预解集和Neumann级数准确取该书II.1.3.1、II.1.3.2及II.1.4.2。这里没有文献穷尽、历史优先权或外部开放问题解决的声称。

有限三元提升仍由同一实际 $h,e,j$ 承担，197.1把它置于共同生成的C*整体，不要求整体退化成二维商，也不把数学三轴当作物理三维。几何上 $h,s$ 仍给四种原有限奇偶，$z_{\rm e}$ 只翻转 $h$，$z_{\rm o}$ 同时翻转 $h,s$。192.1已经约束前一种连线；198.1把后一种连线识别为整个余量的充分判据。若两种连线都与余量反交换，同一轴余量在每个不可约读取中只剩一个实幅度。非零幅度会迫使辅助算子在每个复点都离零保持相同正距离；197.7–197.8说明这张全平面图不能存在。复点是证明参数，不是额外原标签、物理空间坐标、钟、能量或可控制相位。

完整候选仍为196.1的A1–A3/P2及全部原PB，独立公理数未减少。没有新增“交叉项为零”公理；它的原生产仍未解。一般原双线性、任意首标签的混合识别、全部有限旧复Gram、原R、旧结合乘法及完整量子重构也未被198.1无条件支付。197.1只在所写精确交换和反交换前件下给锐界，不提供小交叉项的一般稳定性结论。

**定义 199.2（七项同源合同逐项保持）。** 完整保持194.2、186.1–186.7及其上游全部量词，不更换原世界或缩小消费者：

1. 复Hilbert、可观测量与相干叠加仍须同一原 $\Omega/\mathrm{native}$、全词 $K/J/q$、parent/ready、可取得标签、合法控制和实际准备；全域旧乘法与完成运输仍须原桥。
2. 态、效果、质量与Born仍绑定原评价、原事件、准确效果区间和实际完整菜单及接受归属；原抽签、共同根、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定强度、P9、独立 $W_e$、全部原中间切口及固定支持全质量保持。零、不等、次归一质量、中心权、经典不等维和静默块保留，只对实际菜单的正总质量归一，数学态不增加准备。
3. 真正相关联合与张量仍须同一个真实非零相关联合、忠实同向交换局部腿、共同实现、联合生成分离、重数、所有相关输入、中央对及递归同源参考；辅助读取代数和框架交换不供应这些来源。
4. typed CP、Kraus接线及参考仍须原未归一回溯、合法typed前接后接、反变复合、全未来自然性、分区和箭头商下降；覆盖系统、整个环境、全部成功／失败／细记录／port／post-port输出及每个仍合法未来。三实际投影和支持内补、共同真实支持、全部相关正输入的intertwining及夹界、每个有限递归深度及累计支持的准确运输保持。
5. 仪器、TP、更新与Lüders仍须完整typed菜单、原接受端、整台环境和所有输出未来、真正分组遗忘、AC、精确 $N_u$、X/Xs、平方根词及接受条件。TP需完整单位分区，Lüders需完整输出的像内射线校准；只归一正输出，零分支保留。正规物理表示、指定前对偶和收敛另付，不能由正性延拓取得。
6. 历史、全未来、返回与CountRead仍含全部合法顺序、自适应、并行历史、每个输出的所有合法未来、环境及细记录泄漏、停止拒绝销毁、真遗忘、同数两侧及逆向真实返回；读后同一原完整活动输入、负提升两活路分别控制和相干聚合、完整原菜单、精确 $B$ 与闭正生成 $B_{\rm cl}$ 保持。无限非离散记录的可数可加、正常性和指定前对偶仍须原来源。
7. 动力、物理钟、能量及共同尺度仍须保持可能不完备原域的流、真实相位和门序列、可逆一参数群、物理钟、所需强连续酉实现、生成元域、Hamiltonian能量、共同作用量、共同正 $\hbar$ 和共同仪器；原固定域、resolvent及预算保持。197.8的辅助预解式不替换原物理resolvent合同。

## 200. 从两个未付问题缩到一份原交叉关系的白话

**定义 200.1（完整候选与这一轮的实际简化）。** 仍是同一世界的两两有向正比较、相加三角、单位小窗和全部三者正反配平，没有另加线性或换序公理。前面的配平已把同一未知余量限制成相对两根实际轴都不变，又让它与一种横向连线反交换；另一种跨反射连线还未付。现在证明：如果那一份跨连线也由原关系认回，整份余量便不能留下。把余量与原轴一起读取，每个不可约窗口里它只剩沿原轴的一个实幅度；同一二表正性却会让这个非零幅度在整个复平面上挖出同样大的空隙，而一个有界算子的谱必定在某处挡住这种全平面空隙。因此余量必为零；若二表容许统一误差，余量的平方也不能超过它，且常数恰好是一。少掉的是“交叉关系成立之后是否还会藏余量”这一份未付证明，不是独立公理数；尚须从原配平真正生产那份交叉零值，不能把它直接当作新公理，也不能把两个纯输入响应相加。这里的等价接法相容仍保留关系的方向，实际测量先后可以有影响。复参数和数学态都只是证明工具；真实准备、完整Born菜单及零支质量、真正共同联合、整台仪器和环境全部输出、递归参考、所有历史未来与真实双向返回、无限计数、保持原域的动力、物理钟、能量和共同作用量，仍逐项守199.2的同一原合同。

196–200为纸面定义、条件定理与证明，不冒领Lean kernel核验、摄入、冻结或完整量子重构。

## 追加锚（本行以下为增补区）

## 201. 两个单位偏移使同一原输出的两角归零

**定理 201.1（实际反射分支的完整混合行）。** 完整保持196.1的同一原候选、182.1–182.2的实际 $h,e,j,s,H,Q$ 及199.2全部七项原来源合同。对任意实 $R,\lambda,\nu$ 及任意原 $h$-奇 $z$，不再限制其 $s$-奇偶，准确有

$$
\boxed{D(Rh,\lambda h+\nu s+z)=R\,iQhz
       =R\,D(h,\lambda h+\nu s+z).}
\tag{201.1}
$$

完整候选仍为原A1–A3、准确锥及全部正评价、全部P2和完整PB；不增加旧 $D$ 的可加、齐次、连续、单位平移、协变、商下降或完成延拓前提。

证明。保持同一个实际原输入和输出，置

$$
c=\lambda h+\nu s,\quad x=c+z,\quad
k=hc=\lambda u+\nu H,\quad t=iQhz,\quad
g=D(Rh,x)=Rt+r.
\tag{201.2}
$$

192.1已经给 $[h,r]=[s,r]=[c,r]=0$ 及 $z_{\rm e}\circ r=0$。$R=0$ 时原零输入P2直接给 $g=r=0$。以下 $R\ne0$，不对 $\lambda,\nu$ 或横向平方作除法。

对每个实 $\alpha$，189.1因 $[h,Rk+\alpha u]=0$ 给实际 $D(Rh,Rk+\alpha u)=0$。调用完整PB $(Rh,x,Rk+\alpha u)$，其位移为 $v=g-R^2c-R\alpha h,w=Rk$，两份外层准确为

$$
\begin{aligned}
A_\alpha&=(1-R^2)c+z+g-R\alpha h,& B_\alpha&=2Rk+\alpha u,\\
A_\alpha^-&=(1+R^2)c+z-g+R\alpha h,& B_\alpha^-&=\alpha u.
\end{aligned}
\tag{201.3}
$$

161.5的全单位零行及原反对称性给 $D(A_\alpha^-,B_\alpha^-)=0$。只展开已知Jordan乘法，利用 $x\circ h=k$、$k^2=c^2$，PB右侧为

$$
\begin{aligned}
-2x\circ v-2(Rk+\alpha u)\circ Rk
&=-2x\circ g+2R^2(x\circ c-k^2)
  +2R\alpha(x\circ h-k)\\
&=-2x\circ g+2R^2z\circ c=:K.
\end{aligned}
\tag{201.4}
$$

因此每个 $\alpha$ 的实际旧输出都是同一个 $D(A_\alpha,B_\alpha)=K$；没有假定响应的平移律，也没有分别选择可达输出。

对 $\sigma\in\{1,-1\}$，取原有限投影及实偏移

$$
p_\sigma=(u+\sigma H)/2,\quad
\alpha_\sigma=-2R(\lambda+\sigma\nu),\quad
B_{\alpha_\sigma}=2R\nu(H-\sigma u),\quad
B_{\alpha_\sigma}p_\sigma=p_\sigma B_{\alpha_\sigma}=0.
\tag{201.5}
$$

任取环境数学正泛函 $\omega$，其原正读取 $\phi_\sigma(a)=\omega(p_\sigma a p_\sigma)$ 准确满足 $\phi_\sigma(B_{\alpha_\sigma}^2)=\phi_\sigma(A_{\alpha_\sigma}\circ B_{\alpha_\sigma})=0$。对这一张实际原表，P2给 $|\phi_\sigma(K)|^2\le0$，故 $p_\sigma Kp_\sigma=0$。这允许零角及零、不等、次归一质量；既不需要压缩第一输入平方，也未在角或商上定义响应。两符号共同给

$$
P_H^+K=(K+HKH)/2=p_+Kp_++p_-Kp_-=0.
\tag{201.6}
$$

现用原有限分解 $z=z_{\rm e}+z_{\rm o}$、$t=t_{\rm e}+t_{\rm o}$。$z_{\rm e},t_{\rm e}$ 为 $H$-奇，$z_{\rm o},t_{\rm o}$ 为 $H$-偶；后两者同时与 $h,s$ 反交换，故 $c\circ z_{\rm o}=c\circ t_{\rm o}=0$。再用 $z\circ t=0$ 及192.1的共同交换关系，仅对已知乘法展开：

$$
\begin{gathered}
P_H^+(x\circ g)=cr+z_{\rm o}\circ r,\qquad
P_H^+(z\circ c)=0,\\
0=P_H^+K=-2cr-2z_{\rm o}\circ r.
\end{gathered}
\tag{201.7}
$$

$cr$ 为 $h$-偶，$z_{\rm o}\circ r$ 为 $h$-奇，分别投影得 $cr=0$ 及 $z_{\rm o}\circ r=0$。这正是198.1尚需原生产的交叉零值；消费该定理即得 $r=0$。取 $R=1$ 再得201.1第二等号，故比例是同一原行的结论。所有负参数、$\nu=0$、$\lambda=0$、纯奇、纯偶及真正混合输入均已包含，横向平方可非中央、奇异或带无限谱。∎

## 202. 新接头、完整候选与量子消费者边界

**定义 202.1（来源及准确简化）。** 本组为 $\texttt{repo-derived}$。161.5供应全单位零行；189.1供应内值；192.1供应同一余量的双偶性及偶项零值；198.1连同197.1支付交叉零值之后的谱排零。新增承重是201.3–201.7：以第三标签的单位偏移保持同一个实际旧输出，再让其两份对角读取各遇零平方预算，真正生产缺失交叉项。相对这些已付接口，至多两个偏移调用即足够；不把整个依赖证明的成本说成两次PB。有限投影压缩保正、正泛函分离及对合奇偶分解是成熟C*工具，准确沿199.1、185.3的既有来源复用，不各立为新发现，也不主张文献穷尽或历史优先权。

完整原候选与独立公理数保持196.1；201.1删去198.1在此实际反射分支上尚未支付的交叉条件，完整识别任意实强度的混合行。它不把不同纯输入的响应相加，也不将这条原行扩大到带任意额外单位偏置的混合输入、一般 $h$-交换背景、任意首标签或全域旧双线性。全部有限旧复Gram、原R、同一旧结合乘法及完成运输仍须各自原桥；完整量子重构未由这条行恒等式取得。

199.2的七项同源合同及其全部上游量词逐项原样保留：复Hilbert、可观测量与实际相干准备；原态、效果、零及非归一质量与完整Born菜单；真正相关联合与张量；typed CP、Kraus及全部有限递归参考；整台仪器、环境全部输出及更新；全部合法历史未来、泄漏、真实双向返回和CountRead；保持原域的动力、物理钟、能量、生成元域和共同正 $\hbar$。原 $\Omega/\mathrm{native}$、全词、共同根和真实支持不变；数学读取、两角与实偏移不新增物理准备、控制、参考、正常性或时间尺度。201–203均为纸面定义、定理和证明，不冒领Lean核验、摄入、冻结或物理实现认证。

## 203. 同一份比较经两种接法认回的白话

**定义 203.1（完整候选的本轮图景）。** 仍是同一世界的两两有向正比较、相加三角、单位小窗和完整正反配平。先前已认出一份混合响应的横向部分，并把余量限制为相对两根实际轴都不变，却还缺跨反射连线与余量的关系。现在只移动第三个原标签：两种选好的单位偏移让比较的两端改变，但完整配平要求读回同一份旧输出。第一种接法在一个角中没有第二输入的平方预算，第二种接法在另一个角也没有；同一输出的两个对角读数因而都得为零。把它接回原余量，两种不同奇偶的部分不能互相抵账，缺失的交叉关系便被迫成立，已有谱界随即排除余量。于是两种反射成分混在同一个输入里也能完整认回，不再留下交叉条件；减少的是已陈述分支的未付证明，独立公理数没有减少。两个角不是两个物理系统，等价接法相容也不要求实际测量先后可交换；全部七项真实量子来源仍守202.1的原合同。

## 追加锚（本行以下为增补区）
