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

**证明。** 在 Corollary 56.3 的辅助有序坐标中仍置

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

并在 $u\le1$ 时将 $T$ 解释为 Corollary 56.2 的椭圆支撑量 $W/\kappa$。于是 Corollary 56.3 给出

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

具体地，$a/2<391/500<4/5$，$W$ 在 $u\le1$ 时随 $u$ 增、随 $a$ 减；
$u\ge1$ 时的内部临界值满足 $W(u_*)\le a/2<391/500<4/5$，
其余端点分别由 $W\le B$ 和同一 $u=21/20$ 分割控制。因此 (77.7)
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

## 78. 本批来源与边界

**文献表态。** 本批为 repo-derived 的有限正有理推导，直接复用 Continuation IV 的 Corollary 56.2--56.3、Definition 57.1、(57.8)--(57.9) 及 Lemma 46.2；没有把这些引用宣称为外部文献的新结论。

**本批不主张的。** Section 77 没有处理 $(63/500,1/2)$，没有修复 Continuation IV 的 Section 58 源文本，也没有形式化为 Lean、证明物理实现或结算 #27057 的全域开放问题。

## 追加锚（本行以下为增补区）
