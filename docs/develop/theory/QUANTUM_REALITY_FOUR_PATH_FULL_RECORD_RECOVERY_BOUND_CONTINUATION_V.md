# Four-path full-record recovery: central negative-floor continuation V

This volume continues [Continuation IV](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_IV.md), retaining its Section 57 definitions, source conventions, exact attained triangle, fixed labels, one shared feedback, ordinary transpose and nonnegative root branches. Sections 65--68 below are the next exact full-triangle certificates for the same negative-floor comparison. They remain conditional paper deductions and do not claim a physical realization or settle the full endpoint comparison.

## 65. 高端入口的 $z=3/2$ 椭圆地板

**定理 65.1（高端入口的全三角域地板）。** 保持定义 57.1 的负号行、固定标签、同一反馈、普通转置、非负根支及完整三角域。对
\[
 q\in\left[\frac{27}{50},\frac{109}{200}\right]
 \quad\text{及全部 }(X,Y)\in\mathcal T_x
\]
都有
\[
 \boxed{G_-(q,X,Y)>\frac{23}{50}.}
 \tag{65.1}
\]

*证明。* 仍在 Corollary 56.3 的辅助有序坐标中置
\[
 p=1-q,\qquad L=\frac{19}{16}+\frac q2,\qquad a=L^2,\qquad u=X+Y.
\]
排序交换只用于该上界证明；由 $h^2-s^2=c^2-h^2=h/2>0$，交换弱增 $R,C$，再由原始重构桥接回固定标签结论。此区间给出
\[
 \frac{53}{25}<a\le\frac{5329}{2500},\qquad
 u\ge\frac a2>\frac{53}{50}>1.
 \tag{65.2}
\]
取 $z=3/2$，于是
\[
 \alpha=p+\frac32\sqrt{pq},\qquad
 \beta=q+\frac23\sqrt{pq}.
\]
因为 $p\le23/50$、$q>1/2$ 且 $\sqrt{pq}<1/2$，有
\[
 \alpha<\frac{121}{100},\qquad
 \beta<\frac{527}{600},\qquad
 \alpha+\beta<\frac{25}{12}.
 \tag{65.3}
\]
使用既有包络
\[
 sh<\frac{271}{1000},\quad
 k^2:=(h-s)^2<\frac{26569}{250000},\quad
 S:=c^2+h^2<\frac{677}{500},\quad
 c^2h^2<\frac{427}{1000},
 \tag{65.4}
\]
并写 $B=(2-u)^2$、$D=a(2u-a)$、$W=BD/u^2$、$T=\min\{B,D\}$。Corollary 56.3 给出
\[
 \Gamma_-^2\le\mathcal H(u):=
 \alpha\left(sh\,a+\frac{k^2u}{2}\right)
 +\beta S\left(1-\frac u2\right)
 +\sqrt{\frac{625}{4608}T+\frac{427}{1000}\beta^2W}.
 \tag{65.5}
\]

对 $a/2\le u\le11/10$，有 $a>u$，并由正性与单调性直接得到
\[
 D<\frac7{25},\qquad \frac D{u^2}<\frac14,\qquad B<1,\qquad
 W<\frac14,\qquad T<\frac7{25}.
\]
同时
\[
 sh\,a+\frac{k^2u}{2}<\frac{641}{1000},\qquad
 S\left(1-\frac u2\right)<\frac{131}{200},
\]
故非根部分小于
\[
 \frac{641}{1000}\frac{121}{100}
 +\frac{131}{200}\frac{527}{600}<\frac{1352}{1000}.
\]
根式平方严格小于
\[
 \frac{625}{4608}\frac7{25}
 +\frac{427}{1000}\frac{1}{4}\left(\frac{527}{600}\right)^2
 =\frac{19253087}{160000000}<\left(\frac7{20}\right)^2.
\]
所以 $\mathcal H(u)<1.702$。

对 $11/10\le u\le6/5$，同理
\[
 D<\frac{69}{100},\qquad \frac D{u^2}<\frac12,\qquad
 W<\frac12,\qquad T<\frac{69}{100},
\]
以及
\[
 sh\,a+\frac{k^2u}{2}<\frac{647}{1000},\qquad
 S\left(1-\frac u2\right)<\frac{61}{100}.
\]
非根部分小于
\[
 \frac{647}{1000}\frac{121}{100}
 +\frac{61}{100}\frac{527}{600}<\frac{132}{100},
\]
根式平方严格小于
\[
 \frac{625}{4608}\frac{69}{100}
 +\frac{427}{1000}\frac{1}{2}\left(\frac{527}{600}\right)^2
 =\frac{371946191}{1440000000}<\left(\frac{51}{100}\right)^2.
\]
故 $\mathcal H(u)<1.830$。

最后对 $6/5\le u\le2$，有 $B\le16/25$，且
\[
 D=u^2-(u-a)^2\le u^2,\qquad W=\frac{BD}{u^2}\le B,\qquad T\le B.
\]
从而 $W,T\le16/25$。又有
\[
 sh\,a+\frac{k^2u}{2}<\frac{69}{100},\qquad
 S\left(1-\frac u2\right)\le\frac{677}{1250},
\]
非根部分小于
\[
 \frac{69}{100}\frac{121}{100}
 +\frac{677}{1250}\frac{527}{600}<\frac{1312}{1000},
\]
而根式平方严格小于
\[
 \frac{625}{4608}\frac{16}{25}
 +\frac{427}{1000}\frac{16}{25}\left(\frac{527}{600}\right)^2
 =\frac{6975767}{23437500}<\left(\frac{11}{20}\right)^2.
\]
故 $\mathcal H(u)<1.862$。

最后，由 (55.3)--(55.4) 的正有理平方比较，
\[
 (h+s)^2>\frac{1187}{1000},\qquad
 (h+c)^2>\frac{5319}{2000},
\]
从而
\[
 E(q)=e^2p+d^2q
 >\frac{1187}{250}+\frac{589}{100}q
 \ge\frac{39643}{5000}.
\]
因此
\[
 \frac{E(q)-23/50}{4}>\frac{37343}{20000},\qquad
 1.702<\frac{37343}{20000},\quad
 1.830<\frac{37343}{20000},\quad
 1.862<\frac{37343}{20000}.
\]
结合 (65.5) 得 $4\Gamma_-^2<E(q)-23/50$，故 (65.1) 成立。椭圆退化端点和全部三角域边界由 Corollary 56.3 的连续性约定包含。\hfill$\square$

**定义 65.2（中央残差的当前边界）。** 定理 61.1--65.1 合并后，完整原始三角域上已严格排除
\[
 q\in\left[\frac1{25},\frac1{10}\right]
 \cup\left[\frac{27}{50},\frac35\right].
\]
因此 #27057 的剩余未决区间缩小为
\[
 \left(\frac1{10},\frac{27}{50}\right).
\]
端点 $q=1/10$ 与 $q=27/50$ 均属于已证明区间；未决边界不是反例，也没有改变原注册事件的全称量词。

## 66. 中央入口的四段椭圆地板

**定理 66.1（中央入口的全三角域地板）。** 保持定义 57.1 的负号行、固定标签、同一反馈、普通转置、非负根支及完整三角域。对
\[
 q\in\left[\frac{53}{100},\frac{107}{200}\right]
 \quad\text{及全部 }(X,Y)\in\mathcal T_x
\]
都有
\[
 \boxed{G_-(q,X,Y)>\frac{23}{50}.}
 \tag{66.1}
\]

*证明。* 在 Corollary 56.3 的辅助有序坐标中置
\[
 p=1-q,\qquad L=\frac{19}{16}+\frac q2,\qquad
 a=L^2,\qquad u=X+Y.
\]
交换 $X,Y$ 只用于上界证明；由
$h^2-s^2=c^2-h^2=h/2>0$，交换弱增 $R,C$，再由原始重构桥接回固定标签结论。当前区间给出
\[
 \frac{21}{10}<a<\frac{53}{25},\qquad
 \frac a2\le u\le2.
 \tag{66.2}
\]
取 $z=3/2$，于是
\[
 \alpha=p+\frac32\sqrt{pq},\qquad
 \beta=q+\frac23\sqrt{pq}.
\]
由 $q\in[53/100,107/200]$、$\sqrt{pq}<1/2$ 及直接平方比较，
\[
 \alpha<\frac{61}{50},\qquad
 \beta<\frac78,\qquad
 \alpha+\beta<\frac{25}{12}.
 \tag{66.3}
\]
使用既有正有理包络
\[
 sh<\frac{271}{1000},\qquad
 k^2:=(h-s)^2<\frac{27}{256},\qquad
 S:=c^2+h^2<\frac{677}{500},\qquad
 c^2h^2<\frac{427}{1000}.
 \tag{66.4}
\]
记
\[
 B=(2-u)^2,\qquad D=a(2u-a),\qquad
 W=\frac{BD}{u^2},\qquad T=\min\{B,D\}.
\]
Corollary 56.3 给出
\[
 \Gamma_-^2\le\mathcal H(u):=
 \alpha\left(sh\,a+\frac{k^2u}{2}\right)
 +\beta S\left(1-\frac u2\right)
 +\sqrt{\frac{625}{4608}T+\frac{427}{1000}\beta^2W}.
 \tag{66.5}
\]

四段 $u$ 区间的有理包络如下：
\[
\begin{array}{c|c|c}
 u\text{ 的区间}&T&W\\
 \hline
 [a/2,23/20]&21/50&168/529\\
 [23/20,6/5]&63/100&867/2000\\
 [6/5,13/10]&16/25&2/5\\
 [13/10,2]&49/100&49/100
\end{array}
 \tag{66.6}
\]
表中前两行的 $T,W$ 为严格上界，后两行允许非严格上界。其理由是：在 $u<a$ 时，
 $D/u^2$ 随 $u$ 增而增、随 $a$ 增而减（故 $a$ 越小上界越大）；在 $u\ge a$ 时直接使用
$D/u^2=1-(u-a)^2/u^2\le1$。分别在各段端点代入
$a\in(21/10,53/25)$，并用 $B=(2-u)^2$，得到表中的上界；这也覆盖 $T=0$ 或 $W=0$ 的椭圆退化端点。

由 (66.3)--(66.4) 直接作正有理交叉相乘，四段根式平方分别严格小于
\[
 \frac{32662259}{203136000},\qquad
 \frac{29077741}{128000000},\qquad
 \frac{313307}{1440000},\qquad
 \frac{203987}{900000},
 \tag{66.7}
\]
且四个数都严格小于 $1/4$。对非根部分，先注意
\[
 \alpha k^2<\frac{1647}{12800}<\frac{53}{100}<\beta S,
 \tag{66.8a}
\]
其中 $S>1$ 且 $\beta\ge q\ge53/100$；故
$\alpha(sh\,a+k^2u/2)+\beta S(1-u/2)$ 随 $u$ 严格递减，因为
\[
 \alpha k^2-\beta S
 <\frac{61}{50}\frac{27}{256}-\frac{53}{100}<0.
 \tag{66.8b}
\]
前两段均有 $u\ge a/2$，所以统一得到
\[
 \alpha\left(sh\,a+\frac{k^2u}{2}\right)
 +\beta S\left(1-\frac u2\right)<\frac43,
 \tag{66.8}
\]
后两段得到
\[
 \alpha\left(sh\,a+\frac{k^2u}{2}\right)
 +\beta S\left(1-\frac u2\right)<\frac{13}{10}.
 \tag{66.9}
\]
具体地，前两段均可在 $u=a/2$ 处取上界，再分别对正项使用
$a<53/25$ 与 $a>21/10$，得到
\[
 N(u)\le N(a/2)
 <\frac{61}{50}\frac{53}{25}
   \left(\frac{271}{1000}+\frac{27}{1024}\right)
  +\frac78\frac{677}{500}\frac{19}{40}
 =\frac{213098679}{160000000}<\frac43.
 \tag{66.8c}
\]
第三、第四段分别使用 $u\ge6/5,13/10$，代入 (66.3)--(66.4) 得到逐段上界
\[
 \frac{50080701}{40000000},\quad
 \frac{49769951}{40000000},
 \tag{66.8d}
\]
分别严格小于 $13/10,13/10$，从而得到 (66.8)--(66.9)。
由 (66.7)--(66.9)，四段统一满足
\[
 \mathcal H(u)<\frac{11}{6}.
 \tag{66.10}
\]

另一方面，(57.9) 及 $e=2(h+s)$、$d=2(h+c)$ 给出
\[
 e^2>\frac{1187}{250},\qquad d^2>\frac{5319}{500},\qquad
 E(q)=e^2p+d^2q>
 \frac{1187}{250}+\frac{589}{100}q
 \ge\frac{78697}{10000}.
 \tag{66.11}
\]
因此
\[
 \frac{E(q)-23/50}{4}>\frac{74097}{40000}>\frac{11}{6}.
 \tag{66.12}
\]
结合 (66.5)、(66.10)--(66.12) 得
\[
 4\Gamma_-^2<E(q)-\frac{23}{50},
\]
从而 $G_-(q,X,Y)>23/50$。四段覆盖 (66.2) 的全部 $u$，椭圆退化端点和三角域边界由 Corollary 56.3 的连续性约定包含。\hfill$\square$

**定义 66.2（中央残差的当前边界）。** 定理 61.1--66.1 合并后，完整原始三角域上已严格排除
\[
 q\in\left[\frac1{25},\frac1{10}\right]
 \cup\left[\frac{53}{100},\frac{107}{200}\right]
 \cup\left[\frac{27}{50},\frac35\right].
\]
因此 #27057 的剩余未决区间缩小为
\[
 \left(\frac1{10},\frac{53}{100}\right)
 \cup\left(\frac{107}{200},\frac{27}{50}\right).
\]
各个已证明区间的端点均属于已证明区间；未决边界不是反例，也没有改变原注册事件的全称量词。

## 67. 窄中央残差的闭合

**定理 67.1（窄中央残差的全三角域地板）。** 保持定义 57.1 的负号行、固定标签、同一反馈、普通转置、非负根支及完整三角域。对
\[
 q\in\left[\frac{107}{200},\frac{27}{50}\right]
 \quad\text{及全部 }(X,Y)\in\mathcal T_x
\]
都有
\[
 \boxed{G_-(q,X,Y)>\frac{23}{50}.}
 \tag{67.1}
\]

*证明。* 仍在 Corollary 56.3 的辅助有序坐标中置
\[
 p=1-q,qquad L=\frac{19}{16}+\frac q2,qquad
 a=L^2,qquad u=X+Y.
\]
排序交换只用于上界证明；由
$h^2-s^2=c^2-h^2=h/2>0$，交换弱增 $R,C$，再由 Lemma 46.2 的原始重构桥接回固定标签结论。当前区间给出
\[
 \frac{21}{10}<a<\frac{17}{8},\qquad
 \frac a2\le u\le2.
 \tag{67.2}
\]
取 $z=3/2$，于是
\[
 \alpha=p+\frac32\sqrt{pq},\qquad
 \beta=q+\frac23\sqrt{pq}.
\]
由 $p\le93/200$、$q\ge107/200$ 及 $\sqrt{pq}<1/2$，
\[
 \alpha<\frac{243}{200},\qquad
 \beta<\frac78,qquad
 \alpha+\beta<\frac{25}{12}.
 \tag{67.3}
\]
使用
\[
 sh<\frac{271}{1000},\qquad
 k^2:=(h-s)^2<\frac{27}{256},\qquad
 S:=c^2+h^2<\frac{677}{500},\qquad
 c^2h^2<\frac{427}{1000}.
 \tag{67.4}
\]
记
\[
 B=(2-u)^2,qquad D=a(2u-a),\qquad
 W=\frac{BD}{u^2},\qquad T=\min\{B,D\}.
\]
Corollary 56.3 给出
\[
 \Gamma_-^2\le\mathcal H(u):=
 \alpha\left(sh\,a+\frac{k^2u}{2}\right)
 +\beta S\left(1-\frac u2\right)
 +\sqrt{\frac{625}{4608}T+\frac{427}{1000}\beta^2W}.
 \tag{67.5}
\]

由于 $a>21/10$，四段
\[
 [a/2,23/20],\qquad[23/20,6/5],\qquad
 [6/5,13/10],\qquad[13/10,2]
 \tag{67.6}
\]
上的 $T,W$ 上界仍分别为
\[
 \left(\frac{21}{50},\frac{168}{529}\right),\quad
 \left(\frac{63}{100},\frac{867}{2000}\right),\quad
 \left(\frac{16}{25},\frac25\right),\quad
 \left(\frac{49}{100},\frac{49}{100}\right).
 \tag{67.7}
\]
这是因为在 $u<a$ 时 $D/u^2$ 随 $u$ 增而增、随 $a$ 增而减，且各段的最大值取在 $a=21/10$ 的极限；$u\ge a$ 时使用 $D/u^2\le1$。椭圆退化端点按 Corollary 56.3 的连续性约定处理。

由 (67.3)--(67.4) 及 (67.7)，四段根式平方仍严格小于
\[
 \frac{32662259}{203136000},\qquad
 \frac{29077741}{128000000},\qquad
 \frac{313307}{1440000},\qquad
 \frac{203987}{900000},
 \tag{67.8}
\]
故均小于 $1/4$。对非根部分令
\[
 N(u)=\alpha\left(sh\,a+\frac{k^2u}{2}\right)
      +\beta S\left(1-\frac u2\right).
\]
因为 $S>1$、$\beta\ge q\ge107/200$ 且
\[
 \alpha k^2<\frac{243}{200}\frac{27}{256}<\frac{107}{200}<\beta S,
 \tag{67.9}
\]
$N$ 随 $u$ 严格递减。前两段均有 $u\ge a/2$，所以
\[
 N(u)\le N(a/2)
 <\frac{243}{200}\frac{17}{8}
   \left(\frac{271}{1000}+\frac{27}{1024}\right)
  +\frac78\frac{677}{500}\frac{19}{40}
 =\frac{272490733}{204800000}<\frac43.
 \tag{67.10}
\]
第三、第四段分别使用 $u\ge6/5,13/10$，并代入 (67.3)--(67.4)，得到
\[
 N(u)<\frac{8003039}{6400000}<\frac{13}{10},qquad
 N(u)<\frac{7951969}{6400000}<\frac{13}{10}.
 \tag{67.11}
\]
由 (67.8)、(67.10)--(67.11)，四段统一满足
\[
 \mathcal H(u)<\frac{11}{6}.
 \tag{67.12}
\]

最后，(57.9) 及 $e=2(h+s)$、$d=2(h+c)$ 给出
\[
 E(q)=e^2p+d^2q>
 \frac{1187}{250}+\frac{589}{100}q
 \ge\frac{157983}{20000}.
 \tag{67.13}
\]
因而
\[
 \frac{E(q)-23/50}{4}>\frac{148783}{80000}
 >\frac{11}{6}.
 \tag{67.14}
\]
结合 (67.5)、(67.12)--(67.14) 得
\[
 4\Gamma_-^2<E(q)-\frac{23}{50},
\]
故 (67.1) 成立。四段覆盖 (67.2) 的全部 $u$，并包含全部三角域边界。
\hfill$\square$

**定义 67.2（中央残差的当前边界）。** 定理 61.1--67.1 合并后，完整原始三角域上已严格排除
\[
 q\in\left[\frac1{25},\frac1{10}\right]
 \cup\left[\frac{53}{100},\frac35\right].
\]
因此 #27057 的剩余未决区间缩小为
\[
 \left(\frac1{10},\frac{53}{100}\right).
\]
端点 $q=1/10$ 与 $q=53/100$ 均属于已证明区间；未决区间不是反例，也没有改变原注册事件的全称量词。

## 追加锚（本行以下为增补区）

## 68. 宽中央残差的下端闭合

**定理 68.1（下端中央残差的全三角域地板）。** 保持定义 57.1 的负号行、固定标签、同一反馈、普通转置、非负根支及完整三角域。对
\[
 q\in\left[\frac12,\frac{51}{100}\right]
 \quad\text{及全部 }(X,Y)\in\mathcal T_x
\]
都有
\[
 \boxed{G_-(q,X,Y)>\frac{23}{50}.}
 \tag{68.1}
\]

*证明。* 在 Corollary 56.3 的辅助有序坐标中置
\[
 p=1-q,\qquad L=\frac{19}{16}+\frac q2,qquad
 a=L^2,qquad u=X+Y.
\]
排序交换只用于上界证明；由
$h^2-s^2=c^2-h^2=h/2>0$，交换弱增 $R,C$，再由 Lemma 46.2 的原始重构桥接回固定标签结论。当前区间给出
\[
 \frac{529}{256}\le a\le\left(\frac{577}{400}\right)^2,qquad
 \frac a2\le u\le2.
 \tag{68.2}
\]
取 $z=3/2$，于是
\[
 \alpha=p+\frac32\sqrt{pq},\qquad
 \beta=q+\frac23\sqrt{pq}.
\]
这里 $\sqrt{pq}\le1/2$，故端点 $q=1/2$ 也被包含，并且
\[
 \alpha\le\frac54,\qquad
 \beta<\frac{17}{20},\qquad
 \alpha+\beta\le\frac{25}{12}.
 \tag{68.3}
\]
使用
\[
 sh<\frac{271}{1000},\qquad
 k^2:=(h-s)^2<\frac{27}{256},\qquad
 S:=c^2+h^2<\frac{677}{500},\qquad
 c^2h^2<\frac{427}{1000}.
 \tag{68.4}
\]
记
\[
 B=(2-u)^2,qquad D=a(2u-a),\qquad
 W=\frac{BD}{u^2},\qquad T=\min\{B,D\}.
\]
Corollary 56.3 给出
\[
 \Gamma_-^2\le\mathcal H(u):=
 \alpha\left(sh\,a+\frac{k^2u}{2}\right)
 +\beta S\left(1-\frac u2\right)
 +\sqrt{\frac{625}{4608}T+\frac{427}{1000}\beta^2W}.
 \tag{68.5}
\]

由于 $a\ge529/256>2$，按 $u$ 分四段
\[
 [a/2,23/20],\qquad[23/20,6/5],\qquad
 [6/5,13/10],\qquad[13/10,2]
 \tag{68.6}
\]
可取以下 $T,W$ 上界：
\[
 \left(\frac12,\frac38\right),\quad
 \left(\frac7{10},\frac{289}{800}\right),\quad
 \left(\frac{16}{25},\frac{32}{75}\right),\quad
 \left(\frac{49}{100},\frac{49}{100}\right).
 \tag{68.7}
\]
前两行的两个分量均为严格上界，第三行的 $W$ 为严格上界，最后一行允许非严格上界。其理由仍是 $u<a$ 时 $D/u^2$ 随 $u$ 增而增、随 $a$ 增而减，在各段端点取 $a=529/256$ 的极限，再结合 $B=(2-u)^2$；$u\ge a$ 时使用 $D/u^2\le1$。退化椭圆端点由 Corollary 56.3 的连续性约定包含。

由 (68.3)--(68.4) 及 (68.7)，四段根式平方分别严格小于
\[
 \frac{2642503}{14400000},\qquad
 \frac{594408703}{2880000000},\qquad
 \frac{4914797}{22500000},\qquad
 \frac{313386017}{1440000000}.
 \tag{68.8}
\]
前两者严格小于 $(7/15)^2$，后两者严格小于 $1/4$。令
\[
 N(u)=\alpha\left(sh\,a+\frac{k^2u}{2}\right)
      +\beta S\left(1-\frac u2\right).
\]
因 $S>1$、$\beta\ge q\ge1/2$ 且
\[
 \alpha k^2\le\frac54\frac{27}{256}<\frac12<\beta S,
 \tag{68.9}
\]
$N$ 随 $u$ 严格递减。前两段均有 $u\ge a/2$，所以
\[
 N(u)\le N(a/2)
 =\alpha a\left(sh+\frac{k^2}{4}\right)
   +\beta S\left(1-\frac a4\right)
 <\frac54\left(\frac{577}{400}\right)^2
   \left(\frac{271}{1000}+\frac{27}{1024}\right)
  +\frac{17}{20}\frac{677}{500}
   \left(1-\frac{529}{1024}\right)
 =\frac{21787404527}{16384000000}<\frac43.
 \tag{68.10}
\]
第三、第四段分别使用 $u\ge6/5,13/10$，得到
\[
 N(u)<\frac{159274839}{128000000}<\frac{13}{10},qquad
 N(u)<\frac{158659079}{128000000}<\frac{13}{10}.
 \tag{68.11}
\]
由 (68.8)、(68.10)--(68.11)，四段统一满足
\[
 \mathcal H(u)<\frac95.
 \tag{68.12}
\]

最后，(57.9) 及 $e=2(h+s)$、$d=2(h+c)$ 给出
\[
 E(q)=e^2p+d^2q>
 \frac{1187}{250}+\frac{589}{100}q
 \ge\frac{7693}{1000}.
 \tag{68.13}
\]
因此
\[
 \frac{E(q)-23/50}{4}>\frac{7233}{4000}
 >\frac95.
 \tag{68.14}
\]
结合 (68.5)、(68.12)--(68.14) 得
\[
 4\Gamma_-^2<E(q)-\frac{23}{50},
\]
故 (68.1) 成立。四段覆盖 (68.2) 的全部 $u$，并包含全部三角域边界。\hfill$\square$

**定义 68.2（中央残差的当前边界）。** 定理 61.1--68.1 合并后，完整原始三角域上已严格排除
\[
 q\in\left[\frac1{25},\frac1{10}\right]
 \cup\left[\frac12,\frac{51}{100}\right]
 \cup\left[\frac{53}{100},\frac35\right].
\]
因此 #27057 的剩余未决区间缩小为
\[
 \left(\frac1{10},\frac12\right)
 \cup\left(\frac{51}{100},\frac{53}{100}\right).
\]
各个已证明区间的端点均属于已证明区间；未决区间不是反例，也没有改变原注册事件的全称量词。

## 追加锚（本行以下为增补区）
