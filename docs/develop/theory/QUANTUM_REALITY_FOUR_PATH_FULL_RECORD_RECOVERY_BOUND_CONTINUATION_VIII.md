# Four-path full-record recovery: central negative-floor continuation VIII

This volume continues [Continuation VII](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_VII.md). It retains Definition 57.1's complete endpoint domain, fixed labels, one shared feedback, ordinary transpose, nonnegative roots and full attained triangle. Section 75 is a conditional paper deduction using Corollary 56.2--56.3 and the clean energy bounds in (57.9); it does not claim Lean-kernel verification or a physical realization.

## 75. 低端中央残差的第四段闭合

**定理 75.1（低端中央残差的第四段全三角域地板）。** 保持定义 57.1 的负号行、固定标签、同一反馈、普通转置、非负根支及完整三角域。对

$$
q\in\left[\frac3{25},\frac{61}{500}\right]
\quad\text{及全部 }(X,Y)\in\mathcal T_x
$$

都有

$$
\boxed{G_-(q,X,Y)>\frac{23}{50}.}
\tag{75.1}
$$

**证明。** 在 Corollary 56.3 的辅助有序坐标中置

$$
p=1-q,\qquad L=\frac{19}{16}+\frac q2,
\qquad a=L^2,\qquad u=X+Y.
$$

交换 $X,Y$ 只用于上界证明；由 $h^2-s^2=c^2-h^2=h/2>0$，交换弱增 $R,C$，再由 Lemma 46.2 的原始重构桥接回固定标签结论。当前区间给出

$$
\frac8{25}<\sqrt{pq}<\frac{33}{100},
\qquad \frac{31}{20}<a<\frac{39}{25},
\qquad \frac a2\le u\le2.
\tag{75.2}
$$

取 $z=13/10$，并令

$$
\alpha=p+\frac{13}{10}\sqrt{pq},
\qquad
\beta=q+\frac{10}{13}\sqrt{pq}.
$$

正有理比较给出

$$
\alpha<\frac{131}{100},\qquad
\beta<\frac{19}{50},\qquad
\alpha+\beta<\frac{17}{10},\qquad
\beta>\frac{119}{325}.
\tag{75.3}
$$

事实上 $q(1-q)\le(61/500)(439/500)=26779/250000<(33/100)^2$，而 $q\ge3/25$ 给出 $p\le22/25$。因此
$\alpha<22/25+(13/10)(33/100)<131/100$，第二式由
$q\le61/500$ 和 the same root bound 得到，第三式由
$\alpha+\beta=1+(269/130)\sqrt{pq}$ 得到；最后一个下界由 $q\ge3/25$、$\sqrt{pq}>8/25$ 得到。

沿用

$$
sh<\frac{271}{1000},\qquad
k^2:=(h-s)^2<\frac{27}{256},\qquad
S:=c^2+h^2<\frac{677}{500},\qquad
c^2h^2<\frac{427}{1000}.
\tag{75.4}
$$

令

$$
B=(2-u)^2,\qquad D=a(2u-a),\qquad
W=\frac{BD}{u^2},\qquad T=\min\{B,D\},
$$

并在 $u\le1$ 时将 $T$ 解释为 Corollary 56.2 的椭圆支撑量 $W/\kappa$。于是 Corollary 56.3 给出

$$
\Gamma_-^2\le\mathcal H(u):=
\alpha\left(sh\,a+\frac{k^2u}{2}\right)
+\beta S\left(1-\frac u2\right)
+\sqrt{\frac{(\alpha+\beta)^2T}{32}
             +\frac{427}{1000}\beta^2W}.
\tag{75.5}
$$

记非根部分为

$$
N(u)=\alpha\left(sh\,a+\frac{k^2u}{2}\right)
     +\beta S\left(1-\frac u2\right).
$$

由 $S>1$ 及

$$
\alpha k^2<\frac{131}{100}\frac{27}{256}
<\frac{119}{325}<\beta S,
\tag{75.6}
$$

$N(u)$ 随 $u$ 严格递减。

因为 $31/20<a<39/25$，有 $a/2<4/5$。沿用七段支撑界

$$
\begin{array}{c|c|c}
u\text{ 的区间}&T&W\\
\hline
[a/2,4/5]&1/4&1/4\\
[4/5,9/10]&2/3&2/3\\
[9/10,1]&3/4&3/4\\
[1,11/10]&91/100&4/5\\
[11/10,6/5]&9/10&7/10\\
[6/5,13/10]&13/20&3/5\\
[13/10,2]&1/2&1/2
\end{array}
\tag{75.7}
$$

这些界仍由 $W$ 在 $u\le1$ 时随 $u$ 增、随 $a$ 减的性质，$u\ge1$ 时的内部临界值 $W(u_*)\le a/2<39/50$，以及端点的 $W\le B$ 得到；$[1,11/10]$ 的 $T<91/100$ 仍由 $u=21/20$ 分割得到。

将 (75.2)--(75.7) 作正有理代入，七段的非根上界、根式平方上界及根式上界为

$$
\begin{array}{c|c|c|c}
u\text{ 的区间}&N\text{ 的上界}&\text{根式平方上界}&\text{根式上界}\\
\hline
[a/2,4/5]&295309787/320000000&1519713/40000000&1/5\\
[4/5,9/10]&36711729/40000000&506571/5000000&319/1000\\
[9/10,1]&57591229/64000000&4559139/40000000&169/500\\
[1,11/10]&5638689/6400000&26302283/200000000&363/1000\\
[11/10,6/5]&55182551/64000000&12444241/100000000&353/1000\\
[6/5,13/10]&13494553/16000000&19139681/200000000&31/100\\
[13/10,2]&52773873/64000000&1519713/20000000&69/250
\end{array}
\tag{75.8}
$$

例如第一行在 $u=a/2$ 处使用 $a<39/25$、$a>31/20$，得到

$$
\frac{131}{100}\frac{39}{25}
\left(\frac{271}{1000}+\frac{27}{1024}\right)
+\frac{19}{50}\frac{677}{500}\left(1-\frac{31}{80}\right)
=\frac{295309787}{320000000}.
$$

其余各行由 $N$ 的严格递减性取左端点。根式平方是
$(\alpha+\beta)^2T/32+(427/1000)\beta^2W$ 的直接代入；逐项平方比较给出最后一列。于是七行的 $\mathcal H$ 上界分别小于

$$
\frac{359309787}{320000000},\quad
\frac{49471729}{40000000},\quad
\frac{395832137}{320000000},\quad
\frac{198905221}{160000000},\quad
\frac{388588747}{320000000},\quad
\frac{92201763}{80000000},\quad
\frac{351905357}{320000000}.
$$

每一个都严格小于

$$
\frac{12487}{10000}
<\frac{E(q)-23/50}{4}.
$$

最后一个严格能量界来自 (57.9)、$e=2(h+s)$、$d=2(h+c)$ 以及 $q\ge3/25$。结合 (75.5) 得 $4\Gamma_-^2<E(q)-23/50$，故 (75.1) 成立。全部椭圆退化端点和三角域边界按 Corollary 56.3 的连续性约定包含。\hfill$\square$

## 76. 本批来源与边界

**文献表态。** 本批为 `repo-derived` 的有限正有理推导，直接复用 Continuation IV 的 Corollary 56.2--56.3、Definition 57.1、(57.8)--(57.9) 及 Lemma 46.2；没有把这些引用宣称为外部文献的新结论。

**本批不主张的。** Section 75 没有处理 $(61/500,1/2)$，没有修复 Continuation IV 的 Section 58 源文本，也没有形式化为 Lean、证明物理实现或结算 #27057 的全域开放问题。

## 追加锚（本行以下为增补区）

## 77. 低端中央残差的第五段闭合

**定理 77.1（低端中央残差的第五段全三角域地板）。** 保持定义 57.1 的负号行、固定标签、同一反馈、普通转置、非负根支及完整三角域。对

$$
q\in\left[\frac{61}{500},\frac{63}{500}\right]
\quad\text{及全部 }(X,Y)\in\mathcal T_x
$$

都有

$$
\boxed{G_-(q,X,Y)>\frac{23}{50}.}
\tag{77.1}
$$

**证明。** 本节的推导复用 Continuation IV 的 Theorem 56.2、Corollary 56.3、Definition 57.1 及 (57.8)--(57.9)，以及 Continuation II 的 Lemma 46.2。在 Corollary 56.3 的辅助有序坐标中仍置

$$
p=1-q,\qquad L=\frac{19}{16}+\frac q2,
\qquad a=L^2,\qquad u=X+Y.
$$

交换 $X,Y$ 只用于上界证明；由
$h^2-s^2=c^2-h^2=h/2>0$，交换弱增 $R,C$，再由 Lemma 46.2 的原始重构桥接回固定标签结论。当前区间给出

$$
\frac{327}{1000}<\sqrt{pq}<\frac{83}{250},
\qquad
\frac{31}{20}<a<\frac{7819}{5000},
\qquad
\frac a2\le u\le2.
\tag{77.2}
$$

取 $z=13/10$，并令

$$
\alpha=p+\frac{13}{10}\sqrt{pq},
\qquad
\beta=q+\frac{10}{13}\sqrt{pq}.
$$

正有理比较给出

$$
\alpha<\frac{131}{100},\qquad
\beta<\frac{383}{1000},\qquad
\alpha+\beta<\frac{17}{10},\qquad
\beta>\frac{607}{1625}.
\tag{77.3}
$$

事实上，$p\le439/500$，而
$$
\frac{61}{500}\frac{439}{500}>
\left(\frac{327}{1000}\right)^2,\qquad
\frac{63}{500}\frac{437}{500}<
\left(\frac{83}{250}\right)^2.
$$
于是根式范围成立；并且
$$
\frac{439}{500}+\frac{13}{10}\frac{83}{250}
=\frac{1637}{1250}<\frac{131}{100},
$$
$$
\frac{63}{500}+\frac{10}{13}\frac{83}{250}
=\frac{2479}{6500}<\frac{383}{1000},
$$
$$
1+\frac{269}{130}\frac{83}{250}
=\frac{54827}{32500}<\frac{17}{10},
$$
而
$$
\frac{61}{500}+\frac{10}{13}\frac{327}{1000}
=\frac{607}{1625}.
$$
同理，
$$
\left(\frac{19}{16}+\frac{61}{1000}\right)^2>\frac{31}{20},
\qquad
\left(\frac{19}{16}+\frac{63}{1000}\right)^2
=\frac{6255001}{4000000}<\frac{7819}{5000}.
$$

沿用

$$
sh<\frac{271}{1000},\qquad
k^2:=(h-s)^2<\frac{27}{256},\qquad
S:=c^2+h^2<\frac{677}{500},\qquad
c^2h^2<\frac{427}{1000}.
\tag{77.4}
$$

令

$$
B=(2-u)^2,\qquad D=a(2u-a),\qquad
W=\frac{BD}{u^2},\qquad T=\min\{B,D\},
$$

并在 $u\le1$ 时将 $T$ 解释为 Theorem 56.2 的椭圆支撑量 $W/\kappa$。于是 Corollary 56.3 给出

$$
\Gamma_-^2\le\mathcal H(u):=
\alpha\left(sh\,a+\frac{k^2u}{2}\right)
+\beta S\left(1-\frac u2\right)
+\sqrt{\frac{(\alpha+\beta)^2T}{32}
             +\frac{427}{1000}\beta^2W}.
\tag{77.5}
$$

由 $S>1$ 及

$$
\alpha k^2<
\frac{131}{100}\frac{27}{256}
<\frac{607}{1625}<\beta S,
\tag{77.6}
$$

$N(u):=\alpha(sh\,a+k^2u/2)+\beta S(1-u/2)$ 随 $u$ 严格递减。

同一导数和端点计算在
$31/20<a<7819/5000$ 下仍给出

$$
\begin{array}{c|c|c}
u\text{ 的区间}&T&W\\
\hline
[a/2,4/5]&1/4&1/4\\
[4/5,9/10]&2/3&2/3\\
[9/10,1]&3/4&3/4\\
[1,11/10]&91/100&4/5\\
[11/10,6/5]&9/10&7/10\\
[6/5,13/10]&13/20&3/5\\
[13/10,2]&1/2&1/2
\end{array}
\tag{77.7}
$$

具体地，$a/2<391/500<4/5$，且

$$
W_u=\frac{2a(u-2)(u^2+2u-2a)}{u^3},\qquad
W_a=\frac{2(2-u)^2(u-a)}{u^2}.
$$

因此 $u\le1$ 时 $W$ 随 $u$ 增、随 $a$ 减，前三段的上界依次为
$279/1600<1/4$、$3751/6480<2/3$、$279/400<3/4$；此时
$\kappa\ge1$，故 $T\le W$。
$u\ge1$ 时的内部临界点满足 $u_*=\sqrt{1+2a}-1>1$，并有

$$
W(u_*)=\frac a2\frac{(2-u_*)^3}{u_*}
\le\frac a2<\frac{391}{500}<\frac45.
$$

在 $[1,21/20]$ 上，$T\le D<341/400$；在 $[21/20,11/10]$
上，$T\le B\le361/400$，两者均小于 $91/100$。
因 $a<7819/5000<341/200$，有 $u_*<11/10$，故后续各段中 $W$
随 $u$ 减。在 $u=11/10$ 和 $u=6/5$ 处，$W$ 随 $a$ 减，分别给出
$W<32643/48400<7/10$ 和 $W<527/900<3/5$。
其余 $T,W$ 界由 $T\le B$、$W\le B$ 得出。因此 (77.7)
覆盖全部 $u\in[a/2,2]$，并包含椭圆退化端点。

将 (77.2)--(77.7) 作正有理代入，七段的非根上界、根式平方上界及根式上界为

$$
\begin{array}{c|c|c|c}
u\text{ 的区间}&N\text{ 的上界}&\text{根式平方上界}&\text{根式上界}\\
\hline
[a/2,4/5]&927/1000&152948703/4000000000&1/5\\
[4/5,9/10]&461/500&50982901/500000000&8/25\\
[9/10,1]&903/1000&458846109/4000000000&17/50\\
[1,11/10]&221/250&661466687/5000000000&73/200\\
[11/10,6/5]&173/200&1251265921/10000000000&9/25\\
[6/5,13/10]&423/500&240712117/2500000000&8/25\\
[13/10,2]&827/1000&152948703/2000000000&7/25
\end{array}
\tag{77.8}
$$

每个根式平方分数严格小于相应根式上界的平方；由 $N$ 的严格递减性，
首行在 $u=a/2$ 处使用 $a<7819/5000$、$a>31/20$，
其余各行取左端点并作同一正有理代入。因而七段的 $\mathcal H$ 上界分别小于

$$
\frac{1127}{1000},\quad
\frac{621}{500},\quad
\frac{1243}{1000},\quad
\frac{1249}{1000},\quad
\frac{49}{40},\quad
\frac{583}{500},\quad
\frac{1107}{1000}.
$$

它们都严格小于

$$
\frac{250329}{200000}
<\frac{E(q)-23/50}{4}.
$$

最后一个严格能量界来自 (57.9)、$e=2(h+s)$、$d=2(h+c)$ 以及
$q\ge61/500$。结合 (77.5) 得
$4\Gamma_-^2<E(q)-23/50$，故 (77.1) 成立。
全部椭圆退化端点和三角域边界按 Corollary 56.3 的连续性约定包含。
\hfill$\square$

## 78. 全三角域地板的剩余参数域

**定义 78.1（覆盖域与剩余域）。** 将 Definition 57.1 的参数限制为 $[1/25,3/5]$，将定理 77.1 与此前全三角域地板合并后的覆盖域记为

$$
\mathcal Q_{\mathrm{covered}}
=\left[\frac1{25},\frac{63}{500}\right]
\cup\left[\frac12,\frac35\right].
$$

其在该参数域内的补集为

$$
\mathcal Q_{\mathrm{residual}}
=\left(\frac{63}{500},\frac12\right).
$$

剩余域表示这些地板证明尚未覆盖的参数，不断言其中存在违反地板的不等式实例。定理 77.1 的几何含义是：在同一反馈约束下的完整可达三角域中，把全部合法二元坐标按 $X+Y$ 分为七段；每一段的相干增益上界都小于同一个能量阈值，所以该闭参数区间中没有能越过地板的合法点。

## 追加锚（本行以下为增补区）

## 79. 椭圆外包的不可消除间隙与回接曲率

**定义 79.1（精确参数的椭圆支撑包络）。** 采用 Continuation II Definition 46.1、Lemma 46.2 与 Continuation IV Theorem 56.2、Corollary 56.3、Definition 57.1 的负号行。固定

$$
h=\frac1{\sqrt2},\quad s=\sqrt{\frac{1-h}{2}},\quad
c=\sqrt{\frac{1+h}{2}},\quad p=1-q,\quad
L=\frac{19}{16}+\frac q2,\quad a=L^2.
$$

本节取 $q\in[0,1]$、$x=L-1$，原始域为

$$
\mathcal T_x=\{(X,Y)\in[0,1]^2:\sqrt X+\sqrt Y\ge L\}.
$$

其 $R,C,F$ 均保留 Lemma 46.2 的同一整体反馈关系。在该域的辅助有序坐标中，令 $u=X+Y$、$t=Y-X\ge0$；本节的椭圆障碍与曲率回接均限制在 $u\ge1$，等价地

$$
u\in[\max\{1,a/2\},2].
$$

置

$$
B=(2-u)^2,\quad D=a(2u-a),\quad W=\frac{BD}{u^2}.
$$

当 $u\ge1$ 时，置 $M=\min\{B,D\}$、$N=\max\{B,D\}$、$T=M$。
对每个 $z>0$，定义

$$
\alpha=p+z\sqrt{pq},\qquad
\beta=q+\frac{\sqrt{pq}}z,
$$

$$
\begin{aligned}
\mathcal H(q,u,z)={}&
\alpha\left(sh\,a+\frac{(h-s)^2u}{2}\right)
+\beta(c^2+h^2)\left(1-\frac u2\right)\\
&+\sqrt{\frac{(\alpha+\beta)^2T}{32}+\beta^2c^2h^2W}.
\end{aligned}
$$

写 $e=2(h+s)$、$d=2(h+c)$、$E(q)=e^2p+d^2q$，并记目标支撑阈值为

$$
\Theta(q)=\frac{E(q)-23/50}{4}.
$$

这里 $\mathcal H$ 使用精确的 $h,s,c$，没有以有理上界替代它们。

**定理 79.2（标量重加权不能消除外包间隙）。** 在定义 79.1 下，即使允许 $z$ 任意依赖于 $(q,u)$，仍有

$$
\boxed{\mathcal H\left(\frac14,\frac{11}{10},z\right)
>\Theta\left(\frac14\right)+\frac1{100}
\qquad(z>0).}
\tag{79.1}
$$

因而，只使用 $\Gamma_-^2\le\mathcal H$ 并调节 $z$，不能在全部中央参数上证明 $\Gamma_-^2<\Theta(q)$。
这个障碍属于外包方法，不断言原始 $G_-$ 违反 $23/50$ 地板。

在 $u\ge1$ 的全部同源可达点上，若 $r=t^2$，则原始关系还满足

$$
\boxed{
4F^2=\frac{N(M-r)}{u^2}
-\frac{(u^2-N)r(M-r)}{u^2(u^2-r)}.}
\tag{79.2}
$$

特别地，得到保留四次项的上包络

$$
\boxed{
4F^2\le\frac{N(M-r)}{u^2}
-\frac{u^2-N}{u^4}r(M-r).}
\tag{79.3}
$$

**证明。** 先证 (79.1)。固定 $q=1/4$、$u=11/10$，则

$$
a=\frac{441}{256},\qquad
B=T=M=\frac{81}{100},\qquad
D=N=\frac{269451}{327680},\qquad
W=\frac{21825531}{39649280}.
$$

取椭圆中的辅助点

$$
t_0=\frac35,\qquad \widehat F=\frac{69}{250}.
$$

它严格满足外包条件，因为

$$
1-\frac{t_0^2}{T}-\frac{4\widehat F^2}{W}
=\frac{15278051}{7578309375}>0.
\tag{79.4}
$$

定义该辅助点上的两个正数

$$
\widehat R^2=sh\,a+\frac{(h-s)^2u}{2}+\frac{ht_0}{4},
$$

$$
\widehat C^2=(c^2+h^2)\left(1-\frac u2\right)
+\frac{ht_0}{4}+2ch\widehat F.
$$

对 (79.4) 使用二维 Cauchy--Schwarz，不论 $z>0$ 如何选取都有

$$
\frac{h(\alpha+\beta)t_0}{4}+2\beta ch\widehat F
\le\sqrt{\frac{(\alpha+\beta)^2T}{32}+\beta^2c^2h^2W}.
$$

故

$$
\mathcal H\ge\alpha\widehat R^2+\beta\widehat C^2
\ge\left(\frac{\sqrt3}{2}\widehat R+\frac12\widehat C\right)^2.
\tag{79.5}
$$

第二步使用 $z\widehat R^2+\widehat C^2/z\ge2\widehat R\widehat C$，所以它对全部正 $z$ 同时成立。
由 (57.8) 的正有理包络，直接得到

$$
\begin{aligned}
\widehat R^2&>
\frac{3826}{10000}\frac{7071}{10000}\frac{441}{256}
+\left(\frac{7071-3827}{10000}\right)^2\frac{11}{20}
+\frac{7071}{10000}\frac3{20}\\
&=\frac{40319089387}{64000000000}>
\left(\frac{793}{1000}\right)^2,
\end{aligned}
$$

$$
\begin{aligned}
\widehat C^2&>
\left[\left(\frac{4619}{5000}\right)^2+
\left(\frac{7071}{10000}\right)^2\right]\frac9{20}
+\frac{7071}{10000}\frac3{20}
+2\frac{4619}{5000}\frac{7071}{10000}\frac{69}{250}\\
&=\frac{53783522973}{50000000000}>
\left(\frac{1037}{1000}\right)^2.
\end{aligned}
$$

又有 $\sqrt3/2>433/500$，因而 (79.5) 给出

$$
\mathcal H>
\left(\frac{433}{500}\frac{793}{1000}+\frac{1037}{2000}\right)^2
=\frac{363149659161}{250000000000}.
\tag{79.6}
$$

另一方面，同一 (57.8) 的上界给出

$$
\Theta\left(\frac14\right)
<\frac34\left(\frac{7072+3827}{10000}\right)^2
+\frac14\left(\frac{7072}{10000}+\frac{231}{250}\right)^2
-\frac{23}{200}
=\frac{576445947}{400000000}.
$$

两个有理界之差为

$$
\frac{363149659161}{250000000000}
-\frac{576445947}{400000000}
=\frac{1435471143}{125000000000}>\frac1{100},
$$

故 (79.1) 对每个 $z>0$ 成立，且对 $z$ 取下确界后仍保留至少 $1/100$ 的间隙。

辅助点并非原关系的一个实现。在同一 $u,t_0$ 上，实际
$X=(u-t_0)/2=1/4$、$Y=(u+t_0)/2=17/20$ 都属于 $[0,1]$，且
$\sqrt X+\sqrt Y>1/2+9/10=7/5>21/16=L$，所以该坐标点确在原始三角域。
但 (56.6) 固定其实际值为

$$
F^2=\frac{(B-t_0^2)(D-t_0^2)}{4(u^2-t_0^2)}
=\frac{6816879}{111411200}
<\widehat F^2,
$$

而且

$$
\widehat F^2-F^2=\frac{1043737857}{69632000000}>0.
\tag{79.7}
$$

因此 (79.4) 中的合法外包点不能在保持该 $u,t_0$ 时同时满足原始 $F$ 定义。

最后证明 (79.2)--(79.3)。对 $u\ge1$ 的原始可达点，
$0\le r\le M<u^2$，而

$$
u^2-B=4(u-1)\ge0,\qquad u^2-D=(u-a)^2\ge0.
$$

故 $N\le u^2$。将 (56.6) 写为

$$
4F^2=\frac{(M-r)(N-r)}{u^2-r}
$$

并与 $N(M-r)/u^2$ 通分相减，即得 (79.2)。因 $u^2-r\le u^2$、
$(u^2-N)r(M-r)\ge0$，从 (79.2) 得 (79.3)。这里 $M<u^2$ 也包含退化边界：
若 $u=1$，则 $a=L^2>1$ 给出 $D<u^2$；若 $u>1$，则 $B<u^2$。
即使 $M=0$，也只有 $r=0$，(79.2)--(79.3) 两边仍为零。

这说明椭圆的轮廓多包进了一块原关系没有的区域。标量 $z$ 只重新分配两个分支的权重，不能恢复被外包丢掉的弯曲约束；(79.2) 把这块多余区域精确写成一个非负缺陷项，(79.3) 则以四次关系保留其一部分。\hfill$\square$

## 80. 精确固定和纤维的严格凹性与中央内部最大点

与 [Continuation III](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_III.md) 的既有结论相比：Theorem 51.3 已给出每条开竖直纤维在完整闭纤维上的唯一内部最大点，不依赖 $D_\sigma$ 的符号；Lemma 53.3 给出 $X+Y<L^2$ 的指定开凸域上 $F$ 的严格联合凹性；Theorem 53.4 已在 $D_\sigma(x,q)<0$ 的假设下给出固定人口参数的全三角域有序长度最大点唯一性。本节的新增范围是完整闭固定和纤维的结构，以及中央区间每条非退化固定和纤维的内部最大点，不另将上述条件全局唯一性计作新结论。

**定义 80.1（原负分支与精确固定和纤维）。** 沿用 Continuation II 的 Definition 46.1、Lemma 46.2 与 Continuation IV 的 Theorem 56.2、Corollary 56.3、Definition 57.1，在原距离 $\xi=13/4$ 处置

$$
h=\frac1{\sqrt2},\qquad s=\sqrt{\frac{1-h}{2}},\qquad
c=\sqrt{\frac{1+h}{2}},\qquad e=2(h+s),\quad d=2(h+c),
$$

$$
q\in[0,1],\quad p=1-q,\quad x=\frac3{16}+\frac q2,\quad
L=1+x=\frac{19}{16}+\frac q2,\quad a=L^2,
\qquad
\mathcal T_x=\{(X,Y)\in[0,1]^2:\sqrt X+\sqrt Y\ge L\}.
\tag{80.1}
$$

负分支的固定配对为 $J=(3,4)$、$K_{\rm pair}=(1,2)$。对一个整体反馈 $U=\operatorname{diag}(v)U_-$，令 $|v_j|=1$、$|\sum_jv_j|=2L$，并令 $X=|v_3+v_4|^2/4$、$Y=|v_1+v_2|^2/4$。在整个 $\mathcal T_x$ 上定义

$$
\begin{aligned}
Z&=\frac{a-X-Y}{2\sqrt{XY}},&
F&=\sqrt{(1-X)(1-Y)(1-Z^2)},\\
R^2&=s^2X+h^2Y+sh(a-X-Y),&
C^2&=c^2(1-X)+h^2(1-Y)+2chF,\\
\Gamma_-&=\sqrt p\,R+\sqrt q\,C,&
G_-(q,X,Y)&=e^2p+d^2q-4\Gamma_-^2.
\end{aligned}
\tag{80.2}
$$

根号均取非负值。由 Lemma 46.2，$X,Y\ge x^2>0$、$|Z|\le1$，每点的 $R,C$ 可由同一个整体反馈同时取得。用原证书基 $T=(b_+\ b_-)$ 及 $\beta=(e^{i\phi}\sqrt q,\sqrt p)^{\mathsf T}$，选择对齐相位 $\phi$，效应为 $E=(T\beta\beta^\dagger T^\dagger)^{\mathsf T}$；外层转置是普通转置。原距离由 (46.8) 为 $4(1-x)+2q=13/4$，该处的两符号预算保证它是真实联合距离。四个反馈条目仅共用一个任意整体相位。交换 $(X,Y)$ 只用于比较两个可达点，固定配对标记始终保留。

对有序点 $X\le Y$ 置

$$
u=X+Y,\quad t=Y-X,\quad K=u^2,\quad
B=(2-u)^2,\quad D=a(2u-a),\quad M=\min(B,D),\quad N=\max(B,D).
\tag{80.3}
$$

这里 $a$ 专指 $L^2$，$K$ 专指标量 $u^2$。定义纤维表达式

$$
\begin{aligned}
f(r)&=\frac{(B-r)(D-r)}{K-r},&
F(t)&=\frac12\sqrt{f(t^2)},\\
R(t)^2&=sh\,a+\frac{(h-s)^2u}{2}+\frac{ht}{4},&
C(t)^2&=(c^2+h^2)\left(1-\frac u2\right)+\frac{ht}{4}+2chF(t),\\
g_{q,u}(t)&=\sqrt p\,R(t)+\sqrt q\,C(t).
\end{aligned}
\tag{80.4}
$$

**定理 80.2（完整纤维、严格凹性与唯一最大点）。** 设 $q\in[1/25,3/5]$。整个有序三角域与

$$
\frac a2\le u\le2,\qquad 0\le t\le\sqrt M
\tag{80.5}
$$

一一对应，逆映射为 $X=(u-t)/2$、$Y=(u+t)/2$；在此域内恒有 $M<K$，且 (80.4) 恰为 (80.2) 的限制。交换任意逆序点使 $R,C$ 同时严格增大，故最大化 $\Gamma_-$ 可精确归约到 (80.5)。

若 $a/2<u<2$，则 $M>0$，$F$ 与 $g_{q,u}$ 在整个闭纤维上严格凹，$g_{q,u}$ 有唯一最大点 $t_*(q,u)\in(0,\sqrt M]$。若存在内部驻点，它就是唯一最大点，并且是下式在 $(0,\sqrt M)$ 中的唯一根；否则最大点为右端点：

$$
-8cF'(t)=1+\sqrt{\frac pq}\frac{C(t)}{R(t)},
\qquad F'(t)=\frac{t f'(t^2)}{4F(t)}.
\tag{80.6}
$$

在 $u=a/2$ 或 $u=2$ 时，纤维均为单点 $t_*=0$，以 (80.4) 的连续值定义目标，不使用驻点方程。

证明。由 $\sqrt X+\sqrt Y\ge L$ 得 $2u\ge a$，盒约束给出 $u\le2$、$t\le2-u$。又因 $|\sqrt X-\sqrt Y|\le1<L$，两个三角不等式合为 $|a-u|\le2\sqrt{XY}$，故 $t^2\le a(2u-a)=D$。反之，(80.5) 给出同一平方不等式；一旦 $t<u$，逆映射即满足盒约束及 $a\le u+2\sqrt{XY}$，从而属于 $\mathcal T_x$。所需的 $t<u$ 和全部分母的正性来自：$a>1$，故当 $u\le1$ 时

$$
K-D=(u-a)^2>0;
\qquad\text{当 }u>1\text{ 时}\qquad K-B=4(u-1)>0.
$$

因此恒有 $M<K$。$M=0$ 恰在两个所述端点发生。代入逆映射，并用 $h^2-s^2=c^2-h^2=h/2$，得到 (80.4)；其中 $4F(t)^2=f(t^2)$ 正是 (56.6)，两恢复量的展开也与 Corollary 56.3 一致。若 $X>Y$，交换后 $R^2,C^2$ 各增加 $h(X-Y)/2>0$，而 $F,u$ 保持不变。Lemma 46.2 保证比较后的点仍有同一整体反馈的联合实现。

以下固定非退化 $u$。令 $k=(K-B)(K-D)=4(u-1)(u-a)^2$。多项式除法与求导给出

$$
f(r)=B+D-K-r+\frac{k}{K-r},\qquad
f'(r)=-1+\frac{k}{(K-r)^2},\qquad
f''(r)=\frac{2k}{(K-r)^3}.
\tag{80.7}
$$

当 $u\le1$ 时，$k\le0$，于是 $f'<0$、$f''\le0$，并有

$$
\frac{d^2}{dt^2}f(t^2)=2f'(t^2)+4t^2f''(t^2)<0.
$$

$f(t^2)$ 在闭纤维上非负，在右端点以前为正；非负平方根的凹性与严格递增性使 $F$ 严格凹，包含右端点。

当 $u\ge1$ 时，$B\le K$，且 $D=K-(u-a)^2\le K$，故 $0<M\le N\le K$。对 $J\in\{M,N\}$ 置

$$
v_J(t)=\frac{J-t^2}{\sqrt{K-t^2}},\qquad
v_J''(t)=-\frac{K(K-t^2)+(K-J)(K+2t^2)}{(K-t^2)^{5/2}}<0.
\tag{80.8}
$$

于是 $F=\tfrac12\sqrt{v_Mv_N}$。所用几何平均凹性可直接由 Cauchy–Schwarz 写成：对非负 $A_i,B_i$ 与 $0<\lambda<1$，

$$
\lambda\sqrt{A_1B_1}+(1-\lambda)\sqrt{A_2B_2}
\le\sqrt{(\lambda A_1+(1-\lambda)A_2)
             (\lambda B_1+(1-\lambda)B_2)}.
\tag{80.9}
$$

对任意两个不同的纤维点，$v_M,v_N$ 的两个加权平均均为正。由 (80.8)，它们在内插点的值都严格大于各自加权平均；几何平均在正象限逐坐标严格递增，再用 (80.9)，得到 $F$ 的严格凹性。这一论证也包含 $M=N$ 与右端点的零值。

非退化纤维上 $R>0$，且 $C^2\ge(c^2+h^2)(1-u/2)>0$。$R$ 是正仿射函数的平方根，满足 $R''=-h^2/(64R^3)<0$；$C^2$ 凹，故 $C$ 凹。因此 $p,q>0$ 时 $g_{q,u}$ 严格凹，并在开纤维内光滑。$F'(0)=0$，所以

$$
g_{q,u}'(0)=\frac h8\left(\frac{\sqrt p}{R(0)}+
                                  \frac{\sqrt q}{C(0)}\right)>0.
$$

紧性给出最大点，严格凹性给出唯一性，正的左端导数排除 $t=0$。在内部直接求导为

$$
g_{q,u}'(t)=\frac{h\sqrt q}{8C(t)}
\left(1+\sqrt{\frac pq}\frac{C(t)}{R(t)}+8cF'(t)\right).
\tag{80.10}
$$

严格凹性使 $g_{q,u}'$ 严格递减，因而其内部零点至多一个；若无零点，最大点只能是右端点。这证明 (80.6) 及分类。该论证使用 $g_{q,u}'$ 的单调性，不要求把 (80.6) 移项后的残差另证为单调。$\square$

**推论 80.3（中央区间的最大点恒在内部）。** 对每个 $q\in[1/8,1/2]$ 及每个 $a/2<u<2$，均有

$$
0<t_*(q,u)<\sqrt M,
$$

且 $t_*(q,u)$ 是 (80.6) 的唯一内部根。把两个退化纤维的 $t_*=0$ 一并纳入，定义

$$
H(q,u)=e^2(1-q)+d^2q-4g_{q,u}(t_*(q,u))^2.
\tag{80.11}
$$

则对每个这样的 $q$，精确地有

$$
\min_{(X,Y)\in\mathcal T_x}G_-(q,X,Y)
=\min_{a(q)/2\le u\le2}H(q,u).
\tag{80.12}
$$

证明。若 $M<N$，则 $f(M)=0$ 且

$$
f'(M)=-\frac{N-M}{K-M}<0,
$$

故 $F'(t)\to-\infty$ 当 $t\uparrow\sqrt M$。由于非退化纤维的 $R,C$ 在右端点均有限且为正，(80.10) 给出 $g_{q,u}'(t)\to-\infty$，排除右端点。

若 $M=N$，由 $B=D$ 解得 $u=1+(L-1)^2$；另一根 $1+(L+1)^2>2$。令 $b=L-1$，则 $1/4\le b\le7/16$，并有

$$
t_{\max}=\sqrt M=1-b^2,\quad K-M=4b^2,\quad
F(t)=\frac{M-t^2}{2\sqrt{K-t^2}},\quad
|F'(t_{\max}^-)|=\frac{1-b^2}{2b}\ge\frac{207}{224}>\frac56.
\tag{80.13}
$$

最后一个下界使用 $(1-b^2)/(2b)$ 严格递减。由 (57.8)，$c>9/10$、$h>7/10$、$s>3/8$，而 $a\ge25/16$，所以在该端点

$$
R^2\ge sh\,a>\frac{105}{256}>\frac9{25},\qquad R>\frac35.
$$

这里 $u>1$、$t_{\max}<1$、$h<1$、$c^2+h^2<3/2$、$F(t_{\max})=0$，故

$$
C^2=(c^2+h^2)\left(1-\frac u2\right)+\frac{ht_{\max}}4
<\frac34+\frac14=1.
$$

又 $\sqrt{p/q}\le\sqrt7<3$，从而

$$
\sqrt{\frac pq}\frac CR<5,\qquad
8c|F'(t_{\max}^-)|>6>1+\sqrt{\frac pq}\frac CR.
\tag{80.14}
$$

由 (80.10)，该有限左导数也严格为负。结合 $g_{q,u}'(0)>0$、连续性与定理 80.2，得到唯一内部根及最大点。最后，固定 $q,u$ 时最小化 $G_-$ 等价于最大化非负 $g_{q,u}$；完整纤维对应、交换比较及整体实现给出 (80.12)，其最小值由原闭三角域的紧性取得。$\square$

用白话说，固定人口参数 $q$ 和两对长度平方之和 $u$ 后，剩下的精确可达曲线只有一个最高点；在中央区间的每条非退化曲线上，这个点都由同一个驻点方程的唯一内部根确定。由本卷 §78 的覆盖，中央地板的剩余参数域恰为 $q\in(63/500,1/2)$；仍须对该区间的所有 $q$ 及全部 $a(q)/2\le u\le2$ 证明 $H(q,u)>23/50$，包括两条退化端点纤维。唯一根消去了每条曲线上的竞争极大点，外层 $u,q$ 的统一估计仍是待证义务。

## 81. 保留精确同源纤维的全域共同切平面证书

**定义 81.1（原负分支、限制域与共同锚）。** 沿用定义 80.1、Continuation II 的 Definition 46.1、Lemma 46.2 及 Continuation IV 的 Definition 57.1，固定

$$
\begin{gathered}
q\in[1/8,1/2],\quad p=1-q,\quad
h=1/\sqrt2,\quad s=\sqrt{(1-h)/2},\quad c=\sqrt{(1+h)/2},\\
L=19/16+q/2,\quad a=L^2\in[25/16,529/256],\quad
j=(h-s)^2,\quad S=c^2+h^2,\quad b=h/4.
\end{gathered}
\tag{81.1}
$$

这里 $a$ 只表示 $L^2$，$b$ 只表示 $h/4$；原负行的系数另写为 $(a_{\rm row},b_{\rm row},\ell,m)=(s,h,c,h)$。原完整三角域仍为 $\mathcal T_x=\{(X,Y)\in[0,1]^2:\sqrt X+\sqrt Y\ge L\}$，其中 $x=L-1$。固定标签 $J=(3,4)$、$K_{\rm pair}=(1,2)$，$X,Y$ 分别是这两对和模平方的四分之一。Lemma 46.2 在每个点用一个整体反馈 $U=\operatorname{diag}(w)U_-$、$|w_i|=1$、$|\sum_iw_i|=2L$ 同时实现定义 80.1 的 $R,C$；对齐效应为

$$
E=(T\beta_\phi\beta_\phi^\dagger T^\dagger)^{\mathsf T},\qquad
\beta_\phi=(e^{i\phi}\sqrt q,\sqrt p)^{\mathsf T},\qquad T=(b_+\ b_-).
$$

外层是普通转置；原距离为 $4(1-x)+2q=13/4$。交换只比较两个可达点，不重标记原坐标；有序坐标为 $u=X+Y$、$t=Y-X\ge0$。在定理 80.2 的完整有序域上写

$$
\begin{aligned}
\Omega_a&=\{(u,t):t\ge0,\ u+t\le2,\ u\ge a/2+t^2/(2a)\},
&\mathcal S_a&=\Omega_a\cap\{u\le a\},\\
K&=u^2,&B&=(2-u)^2,&D&=a(2u-a),\\
F^2&=\frac{(B-t^2)(D-t^2)}{4(K-t^2)},\\
R^2&=sh\,a+ju/2+bt,
&C^2&=S(1-u/2)+bt+2chF,\\
g(u,t)&=\sqrt p\,R+\sqrt q\,C,
&V(q)&=\max_{(X,Y)\in\mathcal T_x}\Gamma_-(q,X,Y).
\end{aligned}
\tag{81.2}
$$

根号均非负。对 $0<\lambda<1$ 及一个共同锚 $(v,\tau)\in\operatorname{int}\mathcal S_a$，置 $\alpha=p/\lambda$、$\beta=q/(1-\lambda)$，并写 $F_0=F(v,\tau)$、$F_{u0}=F_u(v,\tau)$、$F_{t0}=F_t(v,\tau)$。所用导数有显式表达式

$$
\frac{F_u}{F}=\frac{u-2}{B-t^2}+\frac{a}{D-t^2}-\frac{u}{K-t^2},\qquad
\frac{F_t}{F}=-\frac{t}{B-t^2}-\frac{t}{D-t^2}+\frac{t}{K-t^2}.
\tag{81.3}
$$

定义仿射系数、支撑函数及证书

$$
\begin{aligned}
P_0&=\alpha sh\,a+\beta S+2\beta ch(F_0-vF_{u0}-\tau F_{t0}),\\
P_u&=(\alpha j-\beta S)/2+2\beta chF_{u0},\\
P_t&=b(\alpha+\beta)+2\beta chF_{t0},\\
\sigma_a(m,n)&=\max_{(u,t)\in\mathcal S_a}(mu+nt),\\
\mathcal U(q;\lambda,v,\tau)&=P_0+\sigma_a(P_u,P_t).
\end{aligned}
\tag{81.4}
$$

**定理 81.2（显式全域支撑与精确取得的共同切平面族）。** 对定义 81.1 的每个 $q$，$\mathcal S_a$ 是有非空二维内部的紧凸集，且

$$
V(q)=\max_{\mathcal S_a}g;
\qquad\text{每个最大点均在 }\operatorname{int}\mathcal S_a.
\tag{81.5}
$$

令

$$
t_c=2\sqrt a-a,\quad u_c=2+a-2\sqrt a,\quad
u_+=\min(a,2),\quad t_+=\max(0,2-a),\quad
\operatorname{clip}(z,0,T)=\min\{T,\max(0,z)\}.
$$

对任意实数 $m,n$，(81.4) 中唯一剩余的仿射最大化有闭式

$$
\sigma_a(m,n)=
\begin{cases}
\displaystyle \frac{ma}{2}+\frac{m\widehat t^2}{2a}+n\widehat t,
&m<0,\quad \widehat t=\operatorname{clip}(-an/m,0,t_c),\\[2mm]
\max\{mu_+,\ mu_++nt_+,\ mu_c+nt_c\},&m\ge0.
\end{cases}
\tag{81.6}
$$

每个合法共同锚给出原完整三角域上的上界 $V(q)^2\le\mathcal U(q;\lambda,v,\tau)$，并且两项最小值都在所示开参数域内取得：

$$
\boxed{
V(q)^2
=\min_{0<\lambda<1}\ \max_{\mathcal S_a}(\alpha R^2+\beta C^2)
=\min_{\substack{0<\lambda<1\\(v,\tau)\in\operatorname{int}\mathcal S_a}}
\mathcal U(q;\lambda,v,\tau).
}
\tag{81.7}
$$

特别地，置

$$
\Theta(q)=(h+s)^2(1-q)+(h+c)^2q-\frac{23}{200}.
$$

结合定义 78.1 的已覆盖参数，完整中央地板
$\min_{\mathcal T_x}G_-(q,X,Y)>23/50$ 对所有 $q\in[1/8,1/2]$ 成立，当且仅当

$$
\forall q\in(63/500,1/2)\quad
\exists\,\lambda\in(0,1),\ (v,\tau)\in\operatorname{int}\mathcal S_{a(q)}:
\quad \mathcal U(q;\lambda,v,\tau)<\Theta(q).
\tag{81.8}
$$

证明。定理 80.2 给出 $\Omega_a$ 与完整有序三角域的一一对应及 $K-t^2>0$；其交换比较把原最大值精确归约到 $\Omega_a$。先独立证明可限制到 $u\le a$。若有序点满足 $u>a$，保留 $Y$，置 $\widetilde X=a-Y$。由于 $a>1$、$Y\le1$，有 $0<\widetilde X<X\le Y\le1$，且 $\widetilde X+Y=a$、$(\sqrt{\widetilde X}+\sqrt Y)^2=a+2\sqrt{\widetilde XY}>a$，故新点可行且 $\widetilde Z=0$。由各非负因子得

$$
\begin{aligned}
\widetilde F^2&=(1-\widetilde X)(1-Y)
\ge(1-X)(1-Y)(1-Z^2)=F^2,\\
\widetilde R^2-R^2&=s(h-s)(u-a)>0,\\
\widetilde C^2-C^2&=c^2(u-a)+2ch(\widetilde F-F)>0.
\end{aligned}
\tag{81.9}
$$

因此这些点不能最大化。$\mathcal S_a$ 由抛物线上方与三个闭半平面相交而成，故紧且凸。取 $a/2<u_0<\min(a,2)$，再取充分小的 $t_0>0$，可使全部不等式严格；这使用 $1<a<4$，也证明二维内部非空。

在 $\operatorname{int}\mathcal S_a$ 上，逆变换给出 $0<X<Y<1$、$X+Y<a$ 及 $\sqrt X+\sqrt Y>L$。Continuation III 的 Lemma 53.3 因而给出这里的 $F$ 凹性。$F$ 在闭集 $\mathcal S_a$ 连续：原三角域有 $X,Y\ge x^2>0$，且 $|Z|\le1$。固定内部点 $z_0$，对任意 $z\in\mathcal S_a$，点 $(1-\varepsilon)z+\varepsilon z_0$ 在内部；对两个这样的点用凹不等式，再令 $\varepsilon\downarrow0$，把凹性延到整个闭集，包括 $t=0$ 及全部边界。因此 $R^2$ 仿射，$C^2$ 凹。此论证只在 $u\le a$ 上延拓，没有断言 $F$ 在整个 $\Omega_a$ 联合凹。

紧性给出最大点。推论 80.3 保证每条 $a/2<u<2$ 的非退化纤维最大点满足 $0<t<\sqrt{\min(B,D)}$，从而排除该纤维的所有边界。对退化纤维 $u=a/2,t=0$，取 $t=\varepsilon$、$u=a/2+\varepsilon^2/(2a)$。此时 $D=t^2$、$F=0$；对充分小的 $\varepsilon>0$ 仍满足盒约束且 $u<a$，并有

$$
\Delta R^2=\frac{j\varepsilon^2}{4a}+\frac{h\varepsilon}{4}>0,\qquad
\Delta C^2=-\frac{S\varepsilon^2}{4a}+\frac{h\varepsilon}{4}>0
\quad(\varepsilon<ah/S).
\tag{81.10}
$$

另一退化纤维 $u=2,t=0$ 的点 $(X,Y)=(1,1)$ 也不能最大化：取 $(1-\varepsilon,1)$，因 $L<2$ 而对充分小的 $\varepsilon>0$ 可行，$R^2$ 增加 $s(h-s)\varepsilon$，$C^2$ 从零增加到 $c^2\varepsilon$。最后，若 $u=a<2$ 是最大点，纤维内部性给出 $X,Y<1$、$Z=0$、$F>0$，且原三角不等式严格。在此点

$$
F_X=-\frac{F}{2(1-X)}<0,\qquad
\partial_X R^2=-s(h-s)<0,\qquad
\partial_X C^2=-c^2+2chF_X<0.
\tag{81.11}
$$

保留 $Y$ 并稍减 $X$ 仍可行，且同时增大 $R,C$，矛盾。$a=2$ 时该边界已由 $u=2$ 排除；$a>2$ 时域内没有 $u=a$。这证明 (81.5)。每个最大点的 $R,C,F$ 均正，所有 (81.3) 中的因子、分母均正，$g$ 光滑且梯度为零。

下面计算支撑函数。由抛物线与 $u=2-t$ 的交点以及 $a>1$，恰有

$$
\mathcal S_a=
\left\{(u,t):0\le t\le t_c,\quad
\frac a2+\frac{t^2}{2a}\le u\le\min(a,2-t)\right\}.
\tag{81.12}
$$

若 $m<0$，最优 $u$ 是下端点，剩下的严格凹二次式在 $[0,t_c]$ 的最大点就是 (81.6) 的 $\widehat t$。若 $m\ge0$，可取上端点；所得函数分段仿射，只须比较 $(u_+,0)$、$(u_+,t_+)$、$(u_c,t_c)$。当 $a\ge2$ 时前两点重合；当 $a<2$ 时它们是水平上边的两个端点。这个论证包含 $m=0$ 及 $n$ 的任意符号，证明 (81.6)。

对任意 $\lambda\in(0,1)$，在同一点的两恢复量满足 Cauchy–Schwarz 不等式

$$
g^2=(\sqrt\lambda\sqrt\alpha R+\sqrt{1-\lambda}\sqrt\beta C)^2
\le\alpha R^2+\beta C^2=:Q_\lambda.
\tag{81.13}
$$

$Q_\lambda$ 在 $\mathcal S_a$ 凹。取实际最大点 $z_*=(u_*,t_*)$，写 $R_*=R(z_*)$、$C_*=C(z_*)$，并令

$$
\lambda_*=
\frac{\sqrt p\,R_*}{V(q)}\in(0,1).
\tag{81.14}
$$

在该点 (81.13) 取等号，且

$$
Q_{\lambda_*}(z_*)=V(q)^2,\qquad
\nabla Q_{\lambda_*}(z_*)=2V(q)\nabla g(z_*)=0.
\tag{81.15}
$$

凹性遂给出 $\max_{\mathcal S_a}Q_{\lambda_*}=V(q)^2$；另一方面 (81.13) 在 $z_*$ 对任意 $\lambda$ 给出反向界 $\max Q_\lambda\ge V(q)^2$。这直接证明 (81.7) 的第一项等式与取得性，无须另加极小极大交换假设。

对任意共同锚，由闭域凹性有

$$
F(u,t)\le F_0+F_{u0}(u-v)+F_{t0}(t-\tau).
\tag{81.16}
$$

代入 $Q_\lambda$ 得 $Q_\lambda(u,t)\le P_0+P_uu+P_tt$，最大化并用 (81.6)，即得 $V(q)^2\le\mathcal U$。取同一个实际最大点作为锚 $(v,\tau)=z_*$，再取 (81.14) 的 $\lambda_*$，则 (81.15) 给出 $P_u=P_t=0$，而锚处切线取等号给出 $P_0=V(q)^2$。所以 $\sigma_a(0,0)=0$，(81.7) 的第二项最小值也在合法内部参数处取得。其精确性不要求选择一个固定的纤维椭圆。

最后，由定义 57.1 或 (80.2)，

$$
\min_{\mathcal T_x}G_-(q,X,Y)
=4(h+s)^2p+4(h+c)^2q-4V(q)^2.
\tag{81.17}
$$

因此该值严格大于 $23/50$ 当且仅当 $V(q)^2<\Theta(q)$。一方向用 $V^2\le\mathcal U$，另一方向用 (81.7) 的取得性，再结合定义 78.1 对 $[1/8,63/500]\cup\{1/2\}$ 的覆盖，恰得 (81.8)。

本条的 `repo-derived` 内容是精确限制域的闭式支撑函数与原同源目标的取得型共同切平面表示。完整三角域与联合实现复用 II46.1--46.2，纤维恒等式复用 IV(56.6)，内部纤维最大点复用推论 80.3，联合凹性只按 III53.3 的 $X+Y<a$ 条件使用。凹函数切线不等式是标准结果，参见 Boyd--Vandenberghe，[*Convex Optimization*](https://web.stanford.edu/~boyd/cvxbook/)，§3.1.3；Cauchy–Schwarz 仅作证明中的中间步骤。III53.4 已有的 $D_\sigma<0$ 全域有序长度唯一性不作为本条新增结论；这里也没有人口最小点或相位代表的唯一性结论。$\square$

用白话说，原完整三角域的最高值确实等于这族显式共同切平面上界中的一个最小值，所以这一族没有固定椭圆松弛留下的结构损失。还须在每个 $q\in(63/500,1/2)$ 上给出合法的共同参数，并证明同一个严格不等式 $\mathcal U<\Theta$；也可以用若干显式参数选择覆盖该区间。上述取得性只保证最优证书存在，不能把未知真实最大点当作已经算出的严格上界，因而中央 $23/50$ 地板仍待这一统一严格符号证书。

## 82. 椭圆障碍、闭纤维与共同支撑证书的来源及边界

**定义 82.1（来源与结论范围）。** §§79–81 的 `repo-derived` 范围是本仓特定同源目标的椭圆间隙与曲率缺陷、完整闭固定和纤维分析，以及精确限制域支撑函数和取得型共同切平面表示。其原始域、固定标签与同一整体反馈的联合重构复用 Continuation II Definition 46.1、Lemma 46.2，精确纤维恒等式复用 Continuation IV (56.6)，限制域上的联合凹性复用 Continuation III Lemma 53.3。III Theorem 51.3 的竖直纤维结论与 Theorem 53.4 在行列式假设下的全局唯一性保留原适用范围。Cauchy–Schwarz、几何平均凹性和凹函数支撑平面仅为推导中的标准供应结果；支撑平面的来源见 §81 所引 Boyd–Vandenberghe §3.1.3。本仓综合推导不构成文献原创首发声明。

这些结论是在所列定义与继承前提下的纸面数学推导，未作 Lean kernel 核验，也不主张物理取得。精确取得式 (81.7) 不提供未知最优锚的显式位置，更不单凭其存在性给出严格统一地板；剩余义务正是 (81.8) 在整个 $(63/500,1/2)$ 上的严格符号证书，或等价的 (80.12) 全纤维严格界。

几何上，§79 的椭圆把真实曲线之外的点也包了进来，调权无法删去这块多余区域；§80 沿每条真实固定和曲线找到唯一顶点；§81 则在保留同源曲率的凸域上用共同切平面支撑整个目标。存在一张恰好接触最高点的切平面，并不说明它已经低于目标阈值；最后这段高度差仍须在全部剩余人口参数上严格证明。

## 追加锚（本行以下为增补区）

## 83. 原负分支最大点的符号与坐标定位

**定义 83.1（原有序域与多项式因子）。** 沿用 [Continuation II](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md) Definition 46.1、Lemma 46.2，[Continuation IV](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_IV.md) Definition 57.1 及本卷定义 80.1、81.1 的负号行、固定标签、一个共同反馈、普通转置和全部非负根支；完整三角域仍为 $\mathcal T_x$。以下的 $a=L^2$、$Z=u^2-t^2$、$U,W,T,J$ 均为局部标量，不分别表示原行系数、迹余弦、整体反馈、证书基或固定配对。

置

$$
q_0=\frac{63}{500},\quad q_1=\frac12,\quad
h=\frac1{\sqrt2},\quad s=\sqrt{\frac{1-h}{2}},\quad
c=\sqrt{\frac{1+h}{2}},\quad p=1-q,
$$

$$
L=\frac{19}{16}+\frac q2,\quad a=L^2,\quad
j=(h-s)^2,\quad S=c^2+h^2,\quad H=S+j,\quad
\Delta=(h+c)^2-(h+s)^2.
$$

常数恒等式为

$$
S=1+\frac h2,\quad j=1-\frac h2-2sh,\quad
H=2-2sh,\quad \Delta=h+2s.
\tag{83.1}
$$

最后一式可由正数恒等式 $c-s=2hs$ 得到。令

$$
\Theta=(h+s)^2+q\Delta-\frac{23}{200}
=1-\frac h2+2sh+q(h+2s)-\frac{23}{200}.
$$

原有序域及限制域为

$$
\Omega_a=\{(u,t):t\ge0,\ u+t\le2,\ 2au-a^2-t^2\ge0\},
\qquad \mathcal S_a=\Omega_a\cap\{u\le a\}.
$$

在 $\operatorname{int}\mathcal S_a$ 中定义下列具体多项式因子；本节的 $Z$ 是分母因子，不是原文的迹余弦：

$$
\begin{aligned}
\delta&=a-u,& Z&=u^2-t^2,\\
A&=(2-u)^2-t^2,& E&=a(2u-a)-t^2,\\
J&=Z^2-4(u-1)\delta^2,\\
Q&=\delta A(au-t^2)-(2-u)EZ,\\
r&=sh\,a+\frac{ju}{2}+\frac{ht}{4},&
z&=S\left(1-\frac u2\right)+\frac{ht}{4}.
\end{aligned}
\tag{83.2}
$$

于是 $R^2=r$、$C^2=z+2chF$，且

$$
F=\frac12\sqrt{\frac{AE}{Z}},\qquad
g=\sqrt p\,R+\sqrt q\,C.
\tag{83.3}
$$

在此域中 $\delta,Z,A,E,F,r,C$ 均严格为正。定义

$$
U=hQ+2jtJ,\qquad W=2StJ-hQ,\qquad T=pU+qW.
\tag{83.4}
$$

**定理 83.2（最大点的代数定位）。**

对每个 $q\in[q_0,q_1]$，原完整三角域上 $g$ 的每个最大点都满足

$$
F_u>0,\qquad Q>0,\qquad u<\frac43.
\tag{83.5}
$$

更精确地，

$$
\begin{cases}
3u<a+2,&a\le2,\\
u^2+2u<2a,&a\ge2.
\end{cases}
\tag{83.6}
$$

在这样的最大点，令 $w=\sqrt{p/q}\,C/R$，则

$$
0<w<\frac{35}{4},\quad U>0,\quad W>0,\quad
F=\frac{cU}{HZ^2},\quad w=\frac WU.
\tag{83.7}
$$

这里 (83.6) 的两项在 $a=2$ 同时成立。

**证明。**

由 VIII (81.5)，最大点在 $\operatorname{int}\mathcal S_a$，故可使用全部光滑导数，且 $a/2<u<a$、$0<t<2-u$、$t^2<a(2u-a)$。本参数段有

$$
\frac{25}{16}\le a\le\frac{529}{256},\quad
\sqrt{p/q}\le\sqrt7<3.
$$

由 IV (57.8) 及 VIII (77.4)，可复用

$$
h>\frac7{10},\ s>\frac38,\ h<\frac34,\ c<1,
\qquad j<\frac{27}{256},\quad S>1.
$$

所以

$$
R^2\ge sh\,a>\frac{105}{256}>\frac9{25},\qquad R>\frac35.
$$

原同源关系给出

$$
C\le c\sqrt{1-X}+h\sqrt{1-Y}\le c+h<\frac74,
$$

因此 $w<3(7/4)/(3/5)=35/4$。

对 (83.3) 直接求导，得

$$
F_u=\frac{Q}{4FZ^2},\qquad
F_t=-\frac{tJ}{4FZ^2}.
\tag{83.8}
$$

这里 $J>0$：若 $u<1$ 则定义即给出；若 $u\ge1$，用
$K=u^2$、$B=(2-u)^2$、$D=a(2u-a)$、$\rho=t^2<\min(B,D)$，有

$$
Z=K-\rho>\max(K-B,K-D),\qquad
4(u-1)\delta^2=(K-B)(K-D)\ge0,
$$

故仍有 $J>0$。

两条一阶方程恰为

$$
jw-S+4chF_u=0,\qquad
\frac h4(w+1)+2chF_t=0.
\tag{83.9}
$$

由于

$$
jw<\frac{945}{1024}<1<S,
$$

第一式推出 $F_u>0$，再由 (83.8) 得 $Q>0$。把 (83.8) 代入 (83.9)，不平方地解这两个线性关系，得到

$$
c(hQ+2jtJ)=HFZ^2,\qquad
w+1=\frac{2ctJ}{FZ^2}.
$$

这正给出 (83.7)，其中 $U,W$ 的正号继承自 $F,w>0$。

下面将 $Q>0$ 转为可直接筛除的参数条件。除 (83.2) 外，$Q$ 还有如下具体分解：

$$
Q=(a-2)Z^2+2\delta(a+2-3u)Z-4u(u-1)\delta^2.
\tag{83.10}
$$

若 $a\le2$ 而 $3u\ge a+2$，则 $u>1$，(83.10) 前两项非正，最后一项严格为负，矛盾。因此第一项 (83.6) 成立。

若 $a\ge2$，把 $Q$ 看成 $\rho=t^2$ 的二次多项式：

$$
\begin{aligned}
Q(\rho)={}&a u(u-2)(u^2+2u-2a)\\
&-2\bigl((a+1)u^2-(4a+2)u+a(a+2)\bigr)\rho
+(a-2)\rho^2.
\end{aligned}
\tag{83.11}
$$

假设 $u\ge u_*:=\sqrt{1+2a}-1$。由 $a\ge2$、$L\le23/16$，

$$
u_*\ge\sqrt5-1>\frac65>
\frac{305}{256}\ge1+(L-1)^2.
$$

$B=D$ 的较小根是 $1+(L-1)^2$，较大根为 $a+2+2L>2$；故在此假设下 $D>B$，且 $0<\rho<B$。又

$$
Q(0)=a u(u-2)(u^2+2u-2a)\le0,
$$

$$
Q(B)=-(2-u)(D-B)(u^2-B)<0.
$$

(83.11) 关于 $\rho$ 凸，因为 $a-2\ge0$。它在 $0<\rho<B$ 不大于两端值的线性内插，因而严格为负，仍矛盾。因此 $u<u_*$，即第二项 (83.6)。

第一项 (83.6) 直接给出 $u<4/3$；在第二项中，
$2a\le529/128<40/9=(4/3)^2+2(4/3)$，亦得同一严格上界。来源与范围：本条的 `repo-derived` 内容是 (83.5)--(83.7) 的具体符号、坐标与比值定位；最大点内部性复用 (81.5)，一般驻点关系参见 [Continuation III](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_III.md) Proposition 51.4，特别是 (51.25)，常数包络复用 [Continuation IV](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_IV.md) (57.8) 与本卷 (77.4)。$\square$

## 84. 原地板失败与带符号临界系统的双向桥

**定义 84.1（固定正支的多项式系统）。**

定义如下四个具体多项式，全部以 (83.1)--(83.4) 的因式形式给出，不含未指定导数、结果式或待选锚：

$$
\boxed{P_1=2(1+h)U^2-H^2Z^3AE,}
\tag{84.1}
$$

$$
\boxed{P_2=2qrW^2-2pzU^2-pHhAEZU,}
\tag{84.2}
$$

$$
\boxed{
P_3=T\bigl(2rW(W-U)+2pLsh\,UW-pLHh\delta AZU\bigr)
       -2p\Delta U^2W,
}
\tag{84.3}
$$

$$
\boxed{P_4=rT^2-p\Theta U^2.}
\tag{84.4}
$$

由于 $L$ 仿射、$a=L^2$，这些是 $q,u,t$ 上系数在固定实代数数域 $\mathbb Q(h,s)$ 中的多项式。若要求只用有理系数，可把常数支一并写成

$$
8s^4-8s^2+1=0,\quad \frac38<s<\frac25,\quad h=1-2s^2;
\tag{84.5}
$$

该区间固定原来的正根，不能改取其他共轭根。

令 $\mathscr C$ 为以下严格符号域：

$$
\begin{gathered}
q_0<q<q_1,\qquad \frac a2<u<a,\qquad u<\frac43,\\
0<t<2-u,\qquad E>0,\qquad Q>0,\qquad U>0,\\
3U<2W,\qquad 4W<35U,\\
(a\le2\Longrightarrow 3u<a+2),\qquad
(a\ge2\Longrightarrow u^2+2u<2a).
\end{gathered}
\tag{84.6}
$$

在该域上 $p,q,Z,A,E,J,H,U,W,T,r,z$ 都严格为正。

**定理 84.2（原失败与带符号临界系统有解等价）。** 记

$$
B_-(q)=\min_{(X,Y)\in\mathcal T_x}G_-(q,X,Y).
$$

以下两项等价：

1. 存在残余参数 $q\in(q_0,q_1)$，原完整三角域的负地板失败，即 $B_-(q)\le23/50$。
2. 存在 $(q,u,t)\in\mathscr C$ 满足

$$
\boxed{P_1=P_2=P_3=0,\qquad P_4\ge0.}
\tag{84.7}
$$

其中任一满足 (84.7) 的精确根均直接给出原域合法点

$$
X=\frac{u-t}{2},\qquad Y=\frac{u+t}{2},\qquad
G_-(q,X,Y)-\frac{23}{50}=-\frac{4P_4}{pU^2}\le0.
\tag{84.8}
$$

不要求先证明该根唯一或是全局最优，才能使用这个反例方向。

**证明。**

先证原失败必给出 (84.7)，包括额外的 $q$ 驻点和 $w>3/2$ 条件。

由于 $a(q)$ 连续，联合集合 $\{(q,u,t):q\in[q_0,q_1],\ (u,t)\in\Omega_{a(q)}\}$ 闭且有界，故紧；定理 80.2 的完整纤维对应保证 $Z>0$，所以 $g$ 在这个联合闭域上连续。在该联合紧集上最小化

$$
m(q,u,t)=\Theta(q)-g(q,u,t)^2.
$$

由 (81.17) 的最小值桥，若存在原失败，所取最小值不大于零。定义 78.1 的覆盖在 $q=q_0,q_1$ 均给出原地板严格成立，故最小点的 $q$ 严格处于两端之间。在固定该 $q$ 时，它最大化 $g$；VIII (81.5) 与定理 83.2 因而给出几何内部性和 (83.5)--(83.7)。所有定义域不等式在该点严格，故保持 $u,t$ 不变也能局部改变 $q$；于是

$$
\partial_q(g^2)=\Theta'(q)=\Delta.
\tag{84.9}
$$

这里不需要假设人口值函数可微，也不需要最大点唯一。

本点的 $w$ 还满足 $w>3/2$。为证明它，先在整个当前有序域给出两个精确上界。由 IV (57.8)，

$$
sh<\frac{2707}{10000},\qquad Lsh<\frac{39}{100}.
\tag{84.10}
$$

事实上 $3827\cdot7072=27064544<27070000$，且
$23\cdot2707=62261<62400$。利用 $t\le2-u$、$j/2-h/4<0$、$u\ge a/2$，有

$$
\begin{aligned}
r&\le sh\,a+\frac h2+\left(\frac j2-\frac h4\right)u\\
&\le\frac h2+\frac a4(1-h+2sh)\\
&<\frac{7072}{20000}+\frac{529}{1024}\frac{8343}{10000}
=\frac{8034311}{10240000}<\frac{157}{200}.
\end{aligned}
\tag{84.11}
$$

最后一步可直接比较同分母的 $8034311<8038400$。

保持 $u,t$ 不变时，$a'=L$ 且 $F_a=-\delta F/E$，故精确地

$$
\partial_q(g^2)
=(p+qw)\left(\frac{r(w-1)}p+Lsh-
                    \frac{2Lch\delta F}{wE}\right).
\tag{84.12}
$$

若 $w\le3/2$，则 $p\ge1/2$，$0<p+qw\le5/4$。由 (84.10)--(84.12)，括号内小于 $157/200+39/100=47/40$，所以

$$
\partial_q(g^2)<\frac{47}{32}<\frac{147}{100}
<\frac{14723}{10000}<\Delta,
$$

与 (84.9) 矛盾。最右严格界是 IV (57.8) 的
$h+2s>7071/10000+2(3826/10000)$。因而

$$
\frac32<w<\frac{35}{4}.
\tag{84.13}
$$

结合 $w=W/U$，即得到 (84.6) 的两条严格比值筛网。

现在逐项消去根号，并保留其合法支。由 (83.7) 和 $4F^2Z=AE$，

$$
4c^2U^2=H^2Z^3AE,
$$

即 $P_1=0$，这里 $4c^2=2(1+h)$。同一等式还给出

$$
2chF=\frac{HhAEZ}{2U},\qquad
C^2=z+\frac{HhAEZ}{2U}.
\tag{84.14}
$$

$w^2=pC^2/(qr)$ 结合 $w=W/U$、(84.14)，恰给出 $P_2=0$。

在 $P_1=0$ 的正支上，(84.12) 中的最后一项可无平方地改写为

$$
\frac{2ch\delta F}{wE}
=\frac{Hh\delta AZ}{2W}.
\tag{84.15}
$$

将 (84.15)、$w=W/U$ 代入 (84.9)、(84.12)，只乘严格正的分母 $2pU^2W$，即得 $P_3=0$。

最后，由正根和比值等式，

$$
g^2=\frac{rT^2}{pU^2},\qquad
m=-\frac{P_4}{pU^2}.
\tag{84.16}
$$

所选最小点 $m\le0$，故 $P_4\ge0$。必要性得证。

反向，设 (84.6)--(84.7) 成立。它们给出一个原限制域内部点，特别是 $Z,A,E>0$。$P_1=0$ 与 $U>0$ 固定正根：

$$
\frac12\sqrt{AE/Z}=\frac{cU}{HZ^2}>0.
$$

因此没有把平方后的负 $F$ 支混入。$P_2=0$、(84.14)、$U,W>0$ 又固定

$$
\frac WU=\sqrt{\frac pq}\frac CR>0,
$$

没有把人口或恢复量的负根混入。于是 (84.16) 确实是原目标值。逐点恒等式 (80.2)，亦即 Continuation IV (57.3) 的负行，结合 (84.16) 给出 (84.8)。VIII Theorem 80.2 把 $(u,t)$ 送回原完整三角域；II Lemma 46.2 在该点联合实现 $R,C$，并沿用固定配对及普通转置效应。因此所得是原合法实例，绝非放松域的反例。反例方向甚至只需 $P_1=P_2=0$ 与 $P_4\ge0$；加入 $P_3=0$ 不损失失败的存在性，是因为必要方向可选取整个闭参数带上的最小点。来源与范围：本条的 `repo-derived` 内容是 (84.1)--(84.7) 中保留正号的具体多项式系统、整个闭参数带最坏失败点的 (84.13)，以及与原失败存在性的双向桥；一般驻点原则、既有内部性和标准代数消元只作证明步骤。原点的联合实现与普通转置效应复用 [Continuation II](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md) Definition 46.1、Lemma 46.2，逐点目标恒等式复用 (80.2)/[Continuation IV](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_IV.md) (57.3)，最小值桥复用 (81.17)。$\square$

## 85. 带符号系统的剩余严格判据

**定义 85.1（原残余地板的严格符号判据）。** 固定定义 83.1 的常数正支；若将常数也作为变量，则加上 (84.5) 的代数等式与指定开区间。原残余域的统一严格地板等价于

$$
\forall(q,u,t)\in\mathscr C:\quad
P_1=P_2=P_3=0\ \Longrightarrow\ P_4<0.
$$

由定理 84.2，另一方向的精确合法反例是该符号域中满足 $P_1=P_2=P_3=0$、$P_4\ge0$ 的一个精确根。上述蕴含尚未证明，也尚未给出这样的精确根，因此原残余区间的严格地板仍未解决。

(83.5)--(83.7) 对每个固定 $q\in[q_0,q_1]$ 的最大点成立；更窄窗口 (84.13) 仅用于必要方向所选的整个闭 $q$ 带上的最坏失败点，不断言每个固定 $q$ 的最大点均满足其下界。任意满足定理 84.2 全部条件的精确根都由 (84.8) 恢复为原合法反馈与对齐效应，不需要先取得最优性或唯一性。一般驻点原则、原边界内部性及证书取得性均为所引前置；本节不作外部文献首发或物理实现的主张。

## 追加锚（本行以下为增补区）
