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

## 173. 同一原轴向旧值与一个实际系数圆

**定义 173.1（完整原候选与圆的供应条件）。** 本节及以下增补完整采用
130.1、137.1、147.1及161.1的同一原 $(E,C,u,N,\mathcal P,S,D)$：
含单位实Archimedean序单位空间、分离且准确决定原锥的正实线性评价族，
全部零／不等／次归一质量，以及全部A1–A3。A1保留全部原标签的两条有向
Hermitian二表正性；A2保留实际相加三表 $(a+b,a,b)$ 及其排列在整个实
三空间的实部半正定性和 $(1,-1,-1)$ 的零二次值；A3保留
$S(u,u)=u$ 及同一固定有理 $0<\vartheta_0\le1$ 上的
$0\le z\le\vartheta_0u\Rightarrow S(z,z)\le z$。全部原P2和完整原PB
仍对全部原输入成立，其元素式准确取(161.6)。

沿前卷16.1–16.2已经支付的同一包含，仍有

$$
E\subset X\subset\mathcal A_{\rm sa},\quad
\overline E=X,\quad\mathcal A=C^*(X),\quad
C=E\cap\mathcal A_+,\quad N=\|\cdot\||_E,\quad S(a,b)=a\circ b.
\tag{173.1}
$$

$E$ 可不完备，$X$ 不必等于 $\mathcal A_{\rm sa}$。
$D:E^2\to E$ 始终是同一个原总映射；不预付其一般齐次、可加、连续、可测、
中央平移、商下降、输入函数演算或完成延拓。固定实际原三轴
$h,e,j=D(h,e)$，直接复用133.1–134.1及157.1–157.2，记

$$
\begin{gathered}
h^2=e^2=j^2=u,\quad he=-eh,\quad hj=-jh,\quad ej=-je,\\
Q=ihej\in Z(\mathcal A),\quad Q^*=Q,\quad Q^2=u,\\
\mathcal B_0=E\cap\{h,e,j\}',\qquad
\widehat T_hx=\tfrac i2Q[h,x].
\end{gathered}
\tag{173.2}
$$

137.2给 $\mathcal B_0$ 是含单位原Jordan域，其内部允许非交换。
对固定原 $b\in\mathcal B_0$，只研究同一份

$$
x=h\circ b=hb\in E,\qquad g=D(h,hb)\in E.
\tag{173.3}
$$

称一对实际原 $f,s\in\mathcal B_0$ 为此 $b$ 的一个系数圆，若

$$
[f,s]=[f,b]=[s,b]=0,\qquad f^2+s^2=u.
\tag{173.4}
$$

这是条件供应，不是对所有不完备原域添加根或逆元公理。
额外的生成条件是 $b\in C^*(u,f,s)\subset\mathcal A$；这里的闭代数
只在环境中定义，不是送入旧 $D$ 的新输入域。所有交换子均为同一环境交换子。

## 174. 一次倾斜与原轴反射分别锁住两个系数

**定理 174.1（一个原圆的同一残差交换律）。** 在173.1下，若(173.4)
由一对实际原标签供应，则同一个 $g=D(h,hb)$ 满足

$$
\boxed{g\in\mathcal B_0,\qquad[g,f]=[g,s]=0.}
\tag{174.1}
$$

不要求 $b,f,s$ 有限谱，不要求 $\mathcal B_0$ 整体交换或 $E$ 完备。

证明。$x=hb$ 与 $h$ 交换，与原 $e$ 反交换，故 $x\in V_e$ 且
$\widehat T_hx=0$。157.2对原框架先给
$g=\rho_h(x)\in\mathcal B_0$。

只构造一根实际倾斜轴及其实际旧伴轴：

$$
e'=e\circ f+j\circ s=ef+js\in E,\qquad
j'=D(h,e').
\tag{174.2}
$$

每个所写普通乘积都因系数与相应轴交换而等于原Jordan乘积。
由(173.4)及两轴反交换，$he'=-e'h$、$(e')^2=u$。
因此133.1–134.1的原 $V_h$ 整行直接识别这个完整旧值：

$$
\begin{aligned}
j'&=iQhe'=jf-es\in E,\\
(j')^2&=u,\qquad e'j'=-j'e'=ej,\\
Q'&=ihe'j'=ihej=Q.
\end{aligned}
\tag{174.3}
$$

第一行只对已知环境表达式展开，没有把 $D(h,ef+js)$ 拆成两次调用。
第二行的交叉项由 $fs=sf$ 抵消。于是 $(h,e',j')$ 确实是同一原候选中的
实际有向单位框架，其中央取向为同一个 $Q$。

由于 $b$ 交换 $f,s$，$x=hb$ 与 $e'$ 反交换，所以 $x\in V_{e'}$。
新框架的完整残差准确为

$$
\begin{gathered}
\widehat T'_hx=\tfrac i2Q'[h,x]=0,\\
\rho'_h(x)=D(h,x)-\widehat T'_hx=D(h,hb)=g.
\end{gathered}
\tag{174.4}
$$

157.2因而可以在这个新实际框架上使用，给 $[g,e']=[g,j']=0$。
这里两次157.2作用在同一原 $x$、同一首标签 $h$ 和同一旧输出 $g$ 上，
并非两个未证明相等的响应。

由 $g$ 与原 $e,j$ 交换，$[g,e']=0$ 准确成为

$$
A+B=0,\qquad A=e[g,f],\quad B=j[g,s].
\tag{174.5}
$$

在环境中用原 $e$ 共轭。$g,f,s$ 全与原 $e$ 交换，而 $eje=-j$，故

$$
eAe=A,\qquad eBe=-B,\qquad A-B=0.
\tag{174.6}
$$

两式相加、相减得 $A=B=0$。左乘 $e$、$j$，分别得到
$[g,f]=[g,s]=0$。这份偶／奇拆分使用原坐标反射；单个和式确能在这份
已证反射关系下分别识别两项。$A,B$ 只是证明中的环境元素，不是旧 $D$ 的标签。∎

## 175. 交换读取代数的零预算消去同一原值

**定理 175.1（单圆生成条件下的原轴向零行）。** 在174.1的条件下，若另有
$b\in C^*(u,f,s)$，则

$$
\boxed{D(h,hb)=0.}
\tag{175.1}
$$

此结论不要求 $E$ 完备，也不假设旧输出预先属于输入生成的小代数。

证明。固定 $g$ 的环境交换子满足
$\|[g,a]-[g,a']\|\le2\|g\|\|a-a'\|$。
由174.1，$g$ 交换 $u,f,s$，故交换其生成的整个C*代数，特别 $[g,b]=0$。
这只用固定元素的环境乘法连续性，与 $D$ 的输入连续性无关。
因此明确含有同一实际旧输出的代数

$$
\mathcal K=C^*(u,h,b,g)\subset\mathcal A
\tag{175.2}
$$

是交换的。零代数分支各值为零；其余情形任取 $\mathcal K$ 的字符 $\chi$。
字符是态，由共同单位子代数的态延拓取到 $\mathcal A$ 上的态 $\phi$，
其限制为 $\chi$。所需成熟事实是Blackadar，
[*Operator Algebras*](https://www.bruceblackadar.com/Mathematics/Cycr.pdf)，
II.2.2.2、II.2.2.4及II.6.3.1；分离也可与II.6.3.5的态分离对照。
这里是正的态延拓，不要求或推出von Neumann意义的正常性。

前卷16.2及123.2的准确锥接口允许这份 $\phi$ 读取原P2。全部读取对象
$h,hb,g,h^2,(hb)^2,h\circ(hb)$ 均是实际原元素；其环境等式为

$$
h^2=u,\qquad(hb)^2=b^2,\qquad h\circ(hb)=b.
\tag{175.3}
$$

$\chi$ 的乘法性于是使同一张原P2准确给

$$
\begin{aligned}
|\chi(g)|^2=|\phi D(h,hb)|^2
&\le\phi(h^2)\phi((hb)^2)-\phi(h\circ(hb))^2\\
&=\chi(b^2)-\chi(b)^2=0.
\end{aligned}
\tag{175.4}
$$

交换C*代数的Gelfand表示分离元素，所以 $g=0$。没有定义字符或商上的新
$D$，没有把 $\chi(D(h,hb))$ 改写成某张标量响应表，也没有将数学态当作
实际准备。原 $E$ 的完备性在这一步完全未用。∎

**推论 175.2（同一旧值的反事实）。** 在173.1及实际圆(173.4)的背景下，
若174.1的某个系数交换式失败，
则(174.5)与其原 $e$ 共轭式不可能同时成立，违反157.2给出的实际框架约束。
若生成条件成立而 $g\ne0$，则有一份延拓态使原 $(h,hb)$ 的P2严格失败。

证明。第一项由(174.6)的两份线性等式直接得到。第二项用Gelfand分离选
$\chi(g)\ne0$，其态延拓使(175.4)的左侧严格正而右侧恰为零。所比较的
始终是同一个实际旧残差，不是新定义的候选值。∎

## 176. 原平方根帽、完整原域与有理圆消费者

**推论 176.1（一个实际平方根帽足够）。** 在173.1下固定原 $b\in\mathcal B_0$。
若存在实 $\tau\ne0$ 及实际原 $f\in\mathcal B_0$ 满足

$$
[f,b]=0,\qquad f^2=u-\tau^2b^2,
\tag{176.1}
$$

则 $D(h,hb)=0$。不要求此 $f$ 为正根，也不要求任何其它原标签有根。

证明。取实际原 $s=\tau b$。这使(173.4)成立，而且
$b=\tau^{-1}s\in C^*(u,f,s)$，所以175.1适用。
$f,s,e',j',hb$ 都属于原 $E$。环境中存在一个根，若未证明它属于原 $E$，
不能充当(176.1)的供应。∎

**推论 176.2（完整原JB域的全部系数轴向零值）。** 若173.1的原域本身
完备，即 $E=X$，则对每个原 $b\in\mathcal B_0$，

$$
\boxed{D(h,hb)=0.}
\tag{176.2}
$$

这包括 $b$ 的连续谱及非交换的整个系数域，不要求 $X=\mathcal A_{\rm sa}$。

证明。$b=0$ 时用原零行，亦可用158.1。设 $b\ne0$，选实 $\tau$ 使
$0<|\tau|\|b\|<1$。在环境的单生成含单位C*代数内取

$$
f=(u-\tau^2b^2)^{1/2}.
\tag{176.3}
$$

Blackadar II.2.3.1的连续函数演算和实多项式一致逼近说明：存在实多项式
$p_n$，在 $[-\|b\|,\|b\|]$ 一致逼近
$\lambda\mapsto\sqrt{1-\tau^2\lambda^2}$，且
$p_n(b)\to f$ 于环境范数。每个 $p_n(b)$ 都是由原 $u,b$ 的有限Jordan幂
构成的元素，属于 $\mathcal B_0$；这是单生成幂结合性，亦见原多项式卷3.1
所引van de Wetering的Corollaries 2.9–2.10。
$E=X$ 在同一环境范数下闭合，故 $f\in E$；与三轴交换的条件也在此范数下
闭合，所以 $f\in\mathcal B_0$，并且 $[f,b]=0$。
因此(176.1)确有实际原标签供应，176.1给结论。

极限只用来证明一个环境函数演算元素本来属于完整原域。随后175.1调用的是
原 $D(h,hb)$ 与实际倾斜框架；没有取 $D$ 的输入极限，没有假设其连续性，
也没有扩张到 $\mathcal A_{\rm sa}$。每次只用一个 $b$ 的交换单生成代数，
不要求两份任意系数交换。∎

**推论 176.3（已有原逆元时的有理圆）。** 在可不完备的173.1原域中，若
对某实 $\tau\ne0$，环境逆元

$$
r=(u+\tau^2b^2)^{-1}
\tag{176.4}
$$

本来属于原 $\mathcal B_0$，则 $D(h,hb)=0$。

证明。$r$ 在环境中交换 $b$。取

$$
f=(u-\tau^2b^2)r,\qquad s=2\tau br.
\tag{176.5}
$$

这些乘积因相应因子交换而是原Jordan乘积，所以 $f,s\in\mathcal B_0$。
它们彼此及与 $b$ 交换，并有

$$
\begin{aligned}
f^2+s^2&=((u-\tau^2b^2)^2+4\tau^2b^2)r^2=u,\\
u+f&=2r\ge\frac{2}{1+\tau^2\|b\|^2}u>0,\\
b&=\tau^{-1}s(u+f)^{-1}\in C^*(u,f,s).
\end{aligned}
\tag{176.6}
$$

最后的逆元由严格正下界及环境连续函数演算属于 $C^*(u,f,s)$；它只证明
生成条件，不作为旧 $D$ 的标签。175.1遂适用。
若 $E=X$，同样的实多项式逼近也使(176.4)属于原域；在一般不完备域中
则须保留这里的实际原逆元条件。∎

## 177. 不完备矩阵多项式域的精确圆供应边界

**命题 177.1（非恒定自伴多项式不供应这种圆）。** 在
$M_2(\mathbb C[\xi])\subset C([-1,1],M_2(\mathbb C))$ 中取逐点伴随，令

$$
b(\xi)=\sigma_x+\xi\sigma_z,\qquad -1\le\xi\le1,
\tag{177.1}
$$

其中 $\sigma_x,\sigma_z$ 为标准两根Pauli自伴轴。任意自伴矩阵多项式
$f,s$ 若满足 $f^2+s^2=I_2$，则二者均为常矩阵。若还各自交换每点的
$b(\xi)$，则 $f,s$ 均为实标量常矩阵，因而

$$
b\notin C^*(I_2,f,s).
\tag{177.2}
$$

特别，对任意实 $\tau\ne0$，此原系数域不含交换 $b$ 且满足
$f^2=I_2-\tau^2b^2$ 的自伴多项式，也不含
$(I_2+\tau^2b^2)^{-1}$。

证明。自伴性使 $f(\xi)=\sum_{k=0}^dF_k\xi^k$、
$s(\xi)=\sum_{k=0}^dS_k\xi^k$ 的系数均为自伴矩阵；缺少的高次项补零。
若共同最高次数 $d>0$，圆恒等式在整个区间成立，故各矩阵项的多项式系数
恒等。其 $\xi^{2d}$ 系数准确为

$$
F_d^2+S_d^2=0.
\tag{177.3}
$$

对每个向量 $z\in\mathbb C^2$，这给
$\|F_dz\|^2+\|S_dz\|^2=0$，从而 $F_d=S_d=0$，与最高次数相矛盾。
所以 $f,s$ 都是常矩阵；这一步甚至不需要 $fs=sf$。
常矩阵 $F$ 交换所有 $b(\xi)$，则由常数项和一次项分别得
$[F,\sigma_x]=[F,\sigma_z]=0$。前一个轴使 $F$ 在其本征基中对角，
另一个轴的两个非对角项使对角值相等，故 $F$ 是标量；自伴时标量为实。
因此它们生成的环境C*代数只有标量常函数，而 $b$ 非恒定，得到(177.2)。

若上述 $f$ 存在，取 $s=\tau b$ 就有含非恒定 $s$ 的多项式圆，与首项
矛盾。另有 $b(\xi)^2=(1+\xi^2)I_2$，所以环境逆元为

$$
(I_2+\tau^2b(\xi)^2)^{-1}
=\frac{1}{1+\tau^2+\tau^2\xi^2}I_2.
\tag{177.4}
$$

若它是矩阵多项式，则其对角项为多项式 $p$ 且
$(1+\tau^2+\tau^2\xi^2)p(\xi)=1$；最高次数不可能相等。
故该逆元也不属于原多项式域。∎

**定义 177.2（供应边界的准确范围）。** 这份系数域可放在外层原Jordan域
$H_2(M_2(\mathbb C[\xi]))$，取标准外层Pauli单位框架，系数放在外层单位
上；其共同交换系数正是上述自伴矩阵多项式。命题177.1只限制这种精确
原圆、原平方根帽与原有理逆元的供应。它没有给这份域指定任何违反轴向零行
且满足完整原P2/PB的旧 $D$，故不是完整候选的反模型，亦不否定其它原标签
或其它证明路线能消去同一旧残差。范数稠密与有限Jordan闭合本身不把
(176.3)或(176.4)的环境元素变为原标签。

## 178. 原关系的准确增量与较短几何

**定义 178.1（承重对应、已有结果与消费者）。** 174–177的新增连接归为
$\texttt{repo-derived}$ 综合，不作历史优先权或文献穷尽主张。
成熟C*工具只承担新原值证明中的中间步骤，不被另列为新理论：

| 原供应或成熟步骤 | 在本证明中的准确作用 | 实际消费者 |
| --- | --- | --- |
| 137.2的原有限系数域 | $hb,ef,js,jf,es$ 在相应交换条件下是原Jordan标签 | 同一原 $(h,hb)$ 和实际倾斜轴 |
| 133.1–134.1的已识别横向整行 | 完整旧 $j'=D(h,e')=jf-es$ 及 $Q'=Q$ | 在新实际框架合法使用157.2 |
| 两份157.2及原 $e$ 共轭 | 同一 $g$ 与原框架、倾斜轴交换，偶／奇分开两个系数交换子 | 174.1，不需要连续角族或导数 |
| Blackadar II.2.2.2、II.2.2.4、II.6.3.1及全部原P2 | 含实际 $g$ 的交换读取代数、字符态延拓和严格零Gram | 175.1消去同一原值；态分离另见II.6.3.5 |
| 单生成原Jordan多项式及Blackadar II.2.3.1 | 在原域完备时确认一个平方根确实属于原 $E$ | 176.2；不对旧 $D$ 作极限 |
| 实际原逆元及严格正下界 | 有限原有理圆与环境中的生成恒等式 | 176.3；最后的环境逆不送入 $D$ |

158.1的全部标量平方输入零残差也保持：若 $b^2=\lambda u$，则
$(hb)^2=\lambda u$，直接复用158.1即可，不需再供应一个圆。
前卷39.2已经把交换且均有限谱的原对归给
[原多项式零响应卷定理3.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)：
它们是同一个实际原生成元的两个实多项式，旧响应为零。
这里不另立有限谱零行。若当前 $(h,hb)$ 本来有这样的共同原多项式生成元，
也直接使用该既有定理。174–176处理的是一般条件圆供应下的同一未知 $g$，
不把共同原多项式生成性作为前件；尤其176.2不对连续谱的 $b$ 强加有限谱。

原多项式卷51.2、57.1的指定标量端点多项式域已经识别全混合旧值。
其72.2在62.1的完整连续标量端点原域
$E=X=\{a\in C([0,1],H_2(\mathbb C)):a(0)\in\mathbb RI_2\}$
上也已用同一 $\varepsilon_0\in\{1,-1\}$ 识别全部原对的旧值
$D(a,b)=\varepsilon_0\mathrm i[a,b]/2$，包括两槽的任意连续标量部分。
其77.1由此支付该域的中央连续标量背景消去、全域旧实双线性、P3、
全部有限复Gram、原R (77.2)及同一结合复乘法 (77.3)；65.2、69.1的
定号横向族包含在这一完整结果中，该连续分支的混合桥已经支付。

该准确连续域的纯原标签在零端点消失，没有全局单位平方；因端点为实
标量，原单位平方标签也不能在此组成反交换两轴。此处173.1则从实际
$h^2=e^2=u$、$he=-eh$ 的原三轴出发，允许一般且非交换的
$\mathcal B_0$、不完备的 $E$ 及 $X\ne\mathcal A_{\rm sa}$。
点像归一不供应这样的实际单位框架。因此72.2是指定连续域的完整旧值
识别，174–176是一般实际标架下的条件轴向零行；两者的原域前件不同，
均不代付一般JB域或一般非交换系数混合旧值的完整识别。

几何上，固定的一份旧轴向残差先被原三轴锁在系数方向内；只倾斜一根实际
单位轴，再用原轴反射分开偶项和奇项，便让这份残差交换两个圆坐标。
生成条件把这种交换传到原 $b$；最后在明确含残差的交换读取代数里，原P2
的面积预算恰为零。这里缩短的是证明所需的几何：一个圆、一份原坐标反射、
一张同源零Gram。没有连续旋转族、导数或任意原函数演算前件；没有把非交换
系数域压成普通三维物理空间，也没有减少独立原公理数。

## 179. 系数轴向零值以后仍保留的一般旧响应目标

**定义 179.1（准确支付与未付桥）。** 本节的双零消费者使用下文独立证明的
182.1：在全部原 $\operatorname{Com}_h=E\cap\{h\}'$ 上，
$D(h,c)=0\Longleftrightarrow D(h,hc)=0$。因此175.1的原圆及生成条件、
176.1的原平方根帽、176.3的原逆元各自支付同一原 $b\in\mathcal B_0$ 的
$D(h,hb)=D(h,b)=0$；176.2在完整原域中对全部原 $b\in\mathcal B_0$
支付这两个零值，准确接线见182.2。它们是不同的原调用；只运输零值，
不将任意非零值等同。以下未付目标均指当前一般实际单位标架分支；178.1所列指定连续域的
全混合识别及静态消费者已经支付。用137.2的同一有限四系数，任意原
$h$-交换标签写为

$$
c=c_0+hc_1,\qquad c_0,c_1\in\mathcal B_0.
\tag{179.1}
$$

即使在完整原域中已经分别知道 $D(h,c_0)=D(h,hc_1)=0$，也不能先把
$D(h,c)$ 拆开。在不完备域中，无相应圆供应的系数零行仍未由175–176支付；
在包括完整原域的一般背景中，全部 $D(h,c)=0$ 及任意原 $v\in V_h$ 的

$$
\rho_h(c+v)=0,\qquad
D(h,c+v)=D(h,c)+Tv
\tag{179.2}
$$

仍是未付目标；第二式的混合接缝不能由第一槽固定、横向行线性直接得到。
166.1的实 $\mu u+\lambda h+v$ 与167.2的仿射首标签横向整行仍守其原范围。

170.2的三个缺口相应保留而有明确局部支付：
对 $c\in\mathcal B_0$，所述圆供应或原完备性已支付内值 $D(h,hc)=0$
及对应的 $D(h,c)=0$；
对一般(179.1)，$hc=hc_0+c_1$ 仍不能按未知 $D$ 的加法拆分，
所以一般内值 $D(h,hc)$ 尚未识别；182.1只证明这两个零值条件等价，
不独自提供其中任何一个。纯交换输入 $c$ 的条件零值接线已由182.1完成，
不再依赖把首标签 $2hc$ 认作实仿射轴。
但一般混合输入 $c+v$ 所生的外层首标签 $2hc$ 仍是算子系数标签，
不在163.1可读取的实仿射轴片内。最后，一般 $c,v,\rho_h(c+v)$
可带不交换的系数，165.8–165.9的共同标量Gram和不可约二阶像仍没有供应；
分别的边缘读取、分别可达或不同实现中的最优值不能替代同一份平方与乘积。

一般不完备原域另保留圆供应缺口：174.1若有实际圆就成立，175.1若再有
生成条件就成立；177.1说明仅有矩阵多项式原运算不能保证这些输入存在。
它既未证明所有不完备域缺圆，也未证明有圆是轴向零值的必要条件，更未给
完整P2/PB的反模型。不得把方法供应边界改写成原命题不可能或独立的结论。

完整保留的数学目标仍是同一旧全域 $D=B_\star$，或准确供应原消费者所需的
旧分别可加、实双线性、R、P3和全部有限旧复Gram，再认回同一旧结合乘法。
一般中央平移、原输入函数演算、输入连续性、商下降与完成运输不由当前
轴向零值自动产生。任意两混合输入、任意首标签、无实际三轴／无轴、经典
及其它原域均继续在原目标中。全量子重构所需的实际来源也不由这些条件
原值身份生成。

## 180. 轴向原值到七项量子消费者的完整条件对应

**定义 180.1（共同载体与叠加）。** 本节逐项完整保持145.1–145.7、
171.1–171.7及其所引静态卷25.1七行的所有原量词，不以当前定理缩小其中
任一条件。对应145.1／171.1，174–176及182只消去实际三轴分支的指定旧值，
并在全部原 $\operatorname{Com}_h$ 运输条件零值；
139–140的数学Hilbert载体、可观测量和矩阵坐标仍须全域旧乘法桥才能成为
同一原响应的共同表示。唯一原 $\Omega$、原 $E/S/D$、跨评价配对、具名且
可取得的原标签、native、全部原词同一 $q,K,J$、parent/ready、合法控制及
实际相干叠加准备全部保留。不推出全 $B(H)$ 满射、任意算子可控制或原域
完备；176.2的原完备性是该消费者的明确条件。

**定义 180.2（原态、效果与全部Born菜单）。** 对应145.2／171.2，原评价、
效果、事件与接受归属仍来自同一实际来源。全部实际准备、共同根、抽签、mark、
$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度尺度、P9及独立
$W_e$、全部实际完整菜单、固定支持全质量及全部原中间切口保持。所有零／
不等／次归一质量、中心经典混合、经典不等维块与静默部分保持。
仅对实际完整菜单且 $m_\alpha>0$ 才用 $p_\alpha(e)=\alpha(e)/m_\alpha$；
零质量不除。字符作为态的正延拓只是数学正读取，不是新的实际准备，
也不供应菜单齐备或改变原 $q$。这里“态泛函”不附加正常性条件。

**定义 180.3（native与真正相关联合张量）。** 对应145.3／171.3，
全部词的同一 $K/J$、原交叉零和共同生成分离保持。仍需同一个实际非零
共同联合、旧局部乘法、满足原局部全矩阵条件的忠实同向交换两腿、共同
实现、联合生成与分离、所需重数、全部真正相关输入、全部中心对、经典与
不等维块。系统和参考分别可达、相同边缘或数学张量表示均不代付共同生成。
系数域非交换不使它自动成为物理子系统；原域外的系数谱点也不是实际参考。

**定义 180.4（typed整台箭头与递归同源参考）。** 对应145.4／171.4，
全部typed整台（WHOLE）箭头、原未归一回溯
$\alpha_A(\beta_rb)=\alpha_B^r(b)$、合法前接／后接、反变合法复合、typed
分区、全未来自然性和原箭头商下降保持。CP仍要求整台实际箭头的递归
同源二元参考或原过程比较：系统、整个环境、全部成功／失败／细记录／
port／post-port输出及每个输出的所有仍合法未来，均不可删除。
共同真支持、忠实同向交换、三实际投影及各自支持内补、共同真实支持上的
准确运输、全部相关正输入上的intertwining与夹界、每个所需有限递归深度
及累计支持的完整实际链仍为前件。支持内补不是环境补；一级原序和175.4
的零预算均不供应整台CP或实际参考。

**定义 180.5（完整仪器与全部输出）。** 对应145.5／171.5，原Jordan夹心
只是数学接口。Kraus、TP、更新及Lüders仍保留全部原输入运输、完整typed
整台仪器及输出菜单、整个环境、全部成功／失败／细记录／port／post-port
输出和各自所有仍合法未来、接受端、真正分组遗忘、AC、精确 $N_u$、X/Xs、
原平方根词及其原接受条件。TP需要完整单位分区，Lüders另需同一个完整
输出的像内射线校准；更新只在正输出质量归一，零分支不删。有限密度、迹类、
算子Kraus式仅在原合同规定的合格全矩阵域，或有正规物理表示、指定前对偶
及所需收敛且确实适用的域使用。(176.3)的环境平方根及(176.4)的逆元不制造原物理
平方根词、实际仪器或接受端。

**定义 180.6（全历史、真遗忘、双向真实返回与CountRead）。** 对应
145.6／171.6，所有合法顺序／自适应／并行历史、每个输出的每个仍合法未来、
整个环境、全部细记录与泄漏、停止／拒绝／销毁、真正分组遗忘、同数两侧
及同数逆向的实际返回全部保持。CountRead仍绑定读后同一原完整活动输入
及全未来返回；负提升两条活路的分别控制与相干聚合、具名分析词到原实际
完整菜单和接受端的接线仍须原生构造。原 $B$ 的精确正生成与另名
$B_{\rm cl}$ 的闭正生成不混同，也不等于系数代数。所有无限历史、无限／
非离散记录、可数可加、正常性与指定前对偶，各取原扩展来源；相同矩阵而
不同原程序、实际读取顺序、原 $q$-零集及AC方向均保持。一次数学轴反射
不是物理控制、真正遗忘或同数两侧真实逆返回。

**定义 180.7（物理动力、钟与共同正作用量）。** 对应145.7／171.7，
$\dot b=2D(H,b)/\hbar$ 仍需同一旧全域乘法、保持可能不完备原域的流、
实际相位及门序列、同一可逆一参数群、真实物理钟、所需强连续酉实现、
Hamiltonian生成元定义域与能量解释、共同作用量、共同正 $\hbar$ 和共同
仪器。原 $\sigma,t_0$、固定 $d$、固定域、resolvent及 $3s+r\le1$ 预算的
全部原参数与量词保持；不与本节的圆参数 $\tau$ 混同。
一般无界生成元不由数学有界候选导子替代。字符、根、逆元、矩阵坐标、
辅助 $Q$ 和数学完成均不供应物理钟、能量或共同正作用量尺度。

## 181. 一个原圆、一面原镜子与两份有限配平的完整白话

**定义 181.1（同一残差、反事实与未完目标的直观含义）。** 想象原世界里
已经有三根互相垂直的单位轴，但每根轴上的“刻度”可以是一整块会互相不交换
的算子材料，而不是一个实数。现在拿一份原系数 $b$ 放在 $h$ 轴上，得到
确实可送入旧表的 $hb$；问题始终是原表对 $(h,hb)$ 的那一个答案 $g$，
它会不会沿系数方向偷偷留下余量。已有三轴关系先把这份余量锁进与三轴
都交换的格子。若原域里确实有一对彼此相容的圆坐标 $f,s$，平方和正好是
单位，而且它们都与这份 $b$ 相容，就能把 $e$ 轴与 $j$ 轴按这两个坐标
倾斜成一根新的单位轴。新轴不是画在完成空间里的替身：它由有限原运算
拼成，其伴轴也由已经认识的原横向整行算出，仍是原表的实际旧答案。
同一个 $hb$ 对新轴仍是横向，于是同一份 $g$ 必须与这根倾斜轴交换。
这个要求表面上只是两份交换误差的和为零，似乎容许一份顶住另一份；
但原 $e$ 轴像一面已经在手里的镜子，一照以后，一份误差保持原样，另一份
翻号。照前照后必须同时成立，所以两份误差只能各自为零；不必再画第二个
圆，也不必让轴连续转动后求导。如果这一个圆的两个坐标在环境中已经能
认出原 $b$，那么余量也必须与 $b$ 交换。此时把 $h,b$ 和那份实际余量
一同放进一个交换读取盒子，每个字符都是该盒子的一种数学读法，可以正地
延拓到整个环境，合法读取原表同一张二表预算。字符把平方和乘积读成同一份
标量乘法，$(h,hb)$ 的面积预算恰为零；任何非零余量总有一份字符读得出来，
就会在零预算上留下正数，直接矛盾。因此这份旧余量为零。原域不完备并不
妨碍这最后一步，真正需要留意的是圆能不能在原域内找到：一个原平方根帽
或一个原有理逆元就够；原域若本来完备，单个 $b$ 的多项式逼近会把帽子
供应出来，哪怕 $b$ 有连续谱、其它系数彼此不交换。原域若只是矩阵多项式，
最高次的两个自伴平方却不容相消，精确圆只能是常量；环境里画得出的帽子
和逆元未必是原标签。这说明当前方法的输入供应仍有边界，不说明原零值
命题是假，更没有构造完整公理的反模型。还可以把一个零答案传回另一次原调用，
但要另做182.1的有限配平，不能直接把两张旧表格当成同一格。对任意与 $h$
交换的原 $c$，若原表对 $(h,hc)$ 已答零，就拿 $(h,c,hc)$ 与
$(h,hc,c)$ 这两个实际三角分别配平；同一个外层答案在两份等式中翻号，
其余余量却同号，因此 $c$ 与未知旧答案 $g=D(h,c)$ 的Jordan交叠
只能为零。这时它们还可能反交换，不能立即宣告乘积为零；把实际原对
$(g,2hc)$ 送进已付的正交面积式，才得到乘积的C*范数为零。于是 $h,c,g$
真的可以放进同一个交换读取盒子，含实际 $g$ 的原P2再次只剩零预算，
迫使这另一次旧答案也为零。乘 $h$ 两次回到原标签，所以反向零值运输也成立。
因此圆、帽子、逆元各自供应的 $b$ 都有 $D(h,hb)=D(h,b)=0$；原域完备时，
整个原系数域都有这两个零值。两个任意非零答案仍未被等同，两份各自给零响应的
输入也不能凭空拆开一般 $c_0+hc_1$ 的旧表；再加横向 $v$ 的混合答案、
算子系数首标签的外层读取和共同非交换预算仍须接通。几何确实缩短到同一个
实际圆、一面原镜子、两个有限原PB三角和零面积读取，原A1–A3、准确锥、全部P2/PB
及七项量子来源条件却一项没有少。镜子和字符没有替原世界造出叠加准备、
完整Born菜单、真正联合及递归参考、整台仪器、所有历史未来与真实返回，
更没有造出物理钟、能量或共同作用量；这些仍属于完整原量子目标。

## 182. 全部原交换标签的两次 PB 条件零值运输

**定理 182.1（同一原轴的零值等价）。** 完整采用173.1的原候选及实际
单位框架，置 $\operatorname{Com}_h=\{c\in E:[h,c]=0\}$。对每个实际原
$c\in\operatorname{Com}_h$，有

$$
\boxed{D(h,c)=0\quad\Longleftrightarrow\quad D(h,hc)=0.}
\tag{182.1}
$$

这里 $hc=h\circ c\in E$，$h(hc)=c$，所以这是原域内的条件零值运输。
不要求 $c\in\mathcal B_0$，不要求原圆、根、逆元、有限谱或 $E$ 完备，
也不要求 $X=\mathcal A_{\rm sa}$。此式不主张任意非零的两份旧值相等。

证明。先设 $k=D(h,hc)=0$，保留同一未知实际旧输出 $g=D(h,c)\in E$。
150.1直接用于原 $x=c$ 给

$$
P_{\rm tr}c=0,\qquad P_{\rm tr}g=0,\qquad [h,g]=0.
\tag{182.2}
$$

最后一步是 $P_{\rm tr}g=(g-hgh)/2=0$ 与 $h^2=u$ 的环境恒等式；
也可在163.1取 $s=0,r=1$ 得到。该已付投影定理适用于任意第二输入，
不消费本定理的零值、单圆结论或未知的 $D$ 可加性。

准确用(161.6)的 $(a,b,z)$ 记三输入。第一份原 $\mathrm{PB}(h,c,hc)$ 的
两份内值是 $g,k=0$，位移和全部外层标签为

$$
\begin{gathered}
\nu=g-c,\qquad\omega=hc,\\
(b+\nu,z+\omega)=(g,2hc),\qquad
(b-\nu,z-\omega)=(2c-g,0).
\end{gathered}
\tag{182.3}
$$

用原零输入零值及 $(hc)^2=c^2$，这份PB准确成为

$$
\begin{aligned}
D(g,2hc)
&=-2c\circ(g-c)-2(hc)\circ(hc)\\
&=-2c\circ g.
\end{aligned}
\tag{182.4}
$$

第二份原 $\mathrm{PB}(h,hc,c)$ 的两份内值是 $k=0,g$，准确为

$$
\begin{gathered}
\nu=-hc,\qquad\omega=c+g,\\
(b+\nu,z+\omega)=(0,2c+g),\qquad
(b-\nu,z-\omega)=(2hc,-g).
\end{gathered}
\tag{182.5}
$$

左侧只用前卷16.2所复用的原零行、第二槽奇性及反对称性，依次成为
$0-D(2hc,-g)=D(2hc,g)=-D(g,2hc)$。右侧准确是
$-2(hc)\circ(-hc)-2c\circ(c+g)=-2c\circ g$。两份PB一起给

$$
D(g,2hc)=-2c\circ g,\qquad
-D(g,2hc)=-2c\circ g,\qquad
c\circ g=0,\quad D(g,2hc)=0.
\tag{182.6}
$$

这里没有把 $D(g,2hc)$ 中的二提到调用外，也没有展开任何未知旧值的和。
两份PB的原三标签 $h,c,hc$，以及全部外层标签
$g,2hc,2c-g,0,2c+g,-g$，均属于原 $E$：$hc=h\circ c$、$g$ 是
实际旧输出，其余只用原实向量运算。

由(182.2)、$hc=ch$ 及 $cg+gc=0$，有

$$
g\circ(2hc)=ghc+hcg=h(gc+cg)=0.
\tag{182.7}
$$

现在才把前卷16.2的原正交面积式(16.3)用于实际原对 $(g,2hc)$，得到

$$
0=D(g,2hc)^2=g^2(2hc)^2=4g^2c^2.
\tag{182.8}
$$

反交换关系另给 $gc^2=c^2g$，故

$$
(cg)^*(cg)=gc^2g=c^2g^2=0,\qquad
\|cg\|^2=0,\qquad cg=gc=0.
\tag{182.9}
$$

用的是环境C*恒等式与范数正定性；反交换本身并不推出零乘积。
此时，明确含实际旧输出的
$\mathcal K=C^*(u,h,c,g)\subset\mathcal A$ 已是交换C*代数。
零代数时结论直接成立；其余情形对任意字符 $\chi$，按175.1所引
Blackadar II.2.2.2及II.6.3.1正地延拓到 $\mathcal A$ 上的态 $\phi$。
前卷16.2及本卷123.2的准确锥接口使这份态合法读取原 $\mathrm{P2}(h,c)$。
全部读取对象 $h,c,g,h^2,c^2,h\circ c=hc$ 均是实际原元素，且属于
$\mathcal K$。同一个实际 $g$ 因而满足

$$
\begin{aligned}
|\chi(g)|^2=|\phi D(h,c)|^2
&\le\phi(h^2)\phi(c^2)-\phi(h\circ c)^2\\
&=\chi(c^2)-\chi(hc)^2\\
&=\chi(c)^2\bigl(1-\chi(h)^2\bigr)=0.
\end{aligned}
\tag{182.10}
$$

最后用 $\chi(h)^2=\chi(u)=1$。Blackadar II.2.2.4的Gelfand分离给 $g=0$。
此处不要求态正常，不定义商上或字符上的新响应，不把输入代数上的字符
直接套在尚未属于它的旧输出上；正延拓和分离全程包含同一实际 $g$。

这证明 $D(h,hc)=0\Rightarrow D(h,c)=0$。若反过来已知 $D(h,c)=0$，
取实际原 $d=hc\in\operatorname{Com}_h$；$hd=c$，故刚证的蕴含用于 $d$
给 $D(h,hd)=0\Rightarrow D(h,d)=0$，即另一方向。原域的完备性与
$D$ 的一般齐次、可加、连续及输入函数演算均未参与。∎

**推论 182.2（单圆、原帽、原逆元与完备原域的双零消费者）。** 在173.1下，
固定实际原 $b\in\mathcal B_0$。若有173.4的实际系数圆并满足
$b\in C^*(u,f,s)$，或有176.1的实际原平方根帽，或176.3的实际原逆元，
则

$$
\boxed{D(h,hb)=D(h,b)=0.}
\tag{182.11}
$$

若原域本身完备 $E=X$，此式对全部实际原 $b\in\mathcal B_0$ 成立，包括
连续谱及非交换系数域，仍不要求 $X=\mathcal A_{\rm sa}$。

证明。各分支分别直接消费175.1、176.1、176.3及176.2的同一原
$D(h,hb)=0$；$b\in\operatorname{Com}_h$，所以182.1给另一个零值。
不重新构造根、逆元或圆，不把 $D(h,hb)$ 与 $D(h,b)$ 预先认作相等。
158.1的标量平方分支、既有有限谱／共同原多项式零行及178.1所列指定
连续标量端点域的完整识别都直接复用，不计作新的零行证明。∎

**定义 182.3（新增关系的准确范围）。** 182.1的 $\texttt{repo-derived}$
连接是两份完整原PB把条件零值转成实际外层 $(g,2hc)$ 的零值和正交，
再消费已付面积及C*范数正定性，最后用包含实际旧输出的原P2消去 $g$。
它不重复133–134的横向行、157.2的共同交换子或158.1的标量平方零行；
成熟C*工具只是中间步骤，不作历史优先权或文献穷尽主张。
单圆与原镜面照旧，另接两个有限原PB三角和零面积，不新增原公理或正则性。
179.1的一般 $c_0+hc_1$ 不能拆分，一般 $c+v$ 的混合残余仍未消去；
182.1也不自行供应所缺的原圆、原根、原逆元或物理来源。
原A1–A3、准确锥、全部P2/PB、一般旧全域乘法目标及180.1–180.7的七项
完整量子来源条件均保持原量词。

## 追加锚（本行以下为增补区）
