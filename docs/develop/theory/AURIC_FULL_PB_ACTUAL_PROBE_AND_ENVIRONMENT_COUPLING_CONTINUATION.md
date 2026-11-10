# AURIC 全部探针与环境耦合的固定输出延续

本卷只在既有《AURIC FULL PB POLYNOMIAL TRANSPORT AND REAL ROOT RIGIDITY》的固定输出接口上增加一条精确的环境耦合应用。承载来源仍是该卷在提交 `0fd6b8d8b80330b90beecbc012c9b7eb9a57f765` 的原文，正文身份仍为 `AURIC_FULL_PB_POLYNOMIAL_TRANSPORT_AND_REAL_ROOT_RIGIDITY.md`；本卷不改写原卷的任何字节。普通有限维完整 $\mathsf H_A(D)$ 下的分类，包括 $M_3(\mathbb C)$，已经由原卷 §22.1 所复用的 AH42.4 等结果支付。本卷的增量仅是：对一个显式环境耦合族，不携带总映射 $D$ 或任何外层响应值，较弱的固定输出 P2 已足以消去残量；这里不新增完整 H、$M_3$ 或原整行分类，也不提出完整量子候选或完整总响应反模型。

## 1. 固定接口与问题边界

设 $A$ 是含幺复 $C^*$-代数，$P$ 是实际投影，$C=PAP$。取非零正交投影 $p,q\le P$，令

$$
S=p+q,\qquad c=p+2q,\qquad
K_\sigma(u,v)=\frac{\sigma i}{2}[u,v],\qquad \sigma\in\{1,-1\}.
$$

给定任意 $t=t^*$ 及

$$
s=s_p+s_q,\qquad s_p=s_p^*\in pAp,\qquad s_q=s_q^*\in qAq,\qquad
g=K_\sigma(c,t)+s.
$$

对正泛函 $\phi$ 写

$$
B_\phi(U,V)=\phi(U^2)\phi(V^2)-\phi(U\circ V)^2,
\qquad U=U^*,\ V=V^*.
$$

这里及下文的 $\phi\ge0$ 遍取同一 $A$ 上全部数学正泛函，不要求归一、忠实或相对于某个表示正常；零、不等及次归一质量均保留。数学读取不增加原物理评价标签，零质量和零 Gram 读数均不作除法。

固定输出二表是

$$
\phi(g)^2\le B_\phi(c,t)\qquad(\phi\ge0).
\tag{1.1}
$$

对每个 $x=x^*\in C$，令

$$
\begin{gathered}
h=K_\sigma(c,x),\qquad r=c\circ x,\qquad k=c\circ t,\\
R_+=x+h-k,\qquad R_-=x-h+k,\\
V_+=t+r+g,\qquad V_-=t-r-g,\\
L=-2x\circ(h-k)-2t\circ(r+g).
\end{gathered}
$$

全部实际探针预算为

$$
|\phi(L)|\le
\sqrt{B_\phi(R_+,V_+)}+\sqrt{B_\phi(R_-,V_-)}
\qquad(\phi\ge0, x\in C_{\rm sa}).
\tag{1.2}
$$

本卷给出一个允许真实角外环境连线的显式子类：在该子类中只用 (1.1) 就得到 $s=0$。此时 (1.2) 的充分性完全由同一已知 $C^*$-代数上的标准全局比较映射 $K_\sigma$ 支付，具体如下。承载原卷在上述固定提交的定义 0.1、5.1 已引用静态重构卷定义 35.1、定理 35.2 的标准模型 PB；取 $\mathcal A_0=A$、$\kappa=\sigma=\pm1$，式 (35.2) 的 PB 缺陷为零，对每个实际 $c,x,t\in A_{\rm sa}$ 均成立。一旦 $g=K_\sigma(c,t)$，本节的 $h,r,k,R_\pm,V_\pm,L$ 就准确成为该标准模型同一次 PB 的标签，因而

$$
L=K_\sigma(R_+,V_+)-K_\sigma(R_-,V_-).
$$

对任意自伴 $U,V$ 和全部 $\phi\ge0$，通常正 Gram／Cauchy–Schwarz 给 $|\phi(UV)|^2\le\phi(U^2)\phi(V^2)$，而 $|\phi(UV)|^2=\phi(U\circ V)^2+\phi(K_\sigma(U,V))^2$，故 $|\phi(K_\sigma(U,V))|\le\sqrt{B_\phi(U,V)}$。对上式两项取三角不等式即得 (1.2)，对全部 $x\in A_{\rm sa}$ 成立，尤其覆盖实际 $C_{\rm sa}$；同一 Gram 计算也给标准输出的 (1.1)。这里没有识别未知 $D$ 的外值，也没有构造实际未知总 $D$。任意 $A,t$ 下的固定输出／全部探针充分性仍是 OPEN。

承载原文在固定提交上的字节 SHA-256 为 12879459b2e413632516b20d928d27d0b3b8619ee2e1f89830b7d7ef7664da96。

## 2. P2 的标量二表与正算子铅笔

下列引理 2.1 和 3.1 是定理 4.1 消费的成熟初等工具及其证明，不作为新的独立抽象数学成果。正 Hermitian 二表、标量参数正算子铅笔、零 Gram／比例输入读取和正泛函分离的归属见 §5。

**引理 2.1（正铅笔等价式）。** 条件 (1.1) 等价于对每个 $z=x+iy\in\mathbb C$ 都有

$$
F_z:=t^2-2x(c\circ t)+|z|^2c^2+2y g\ \ge 0.
\tag{2.1}
$$

代入 $g=K_\sigma(c,t)+s$，再置

$$
X_{x,y}=t-(x+i\sigma y)c,
$$

可得精确分解

$$
F_{x+iy}=X_{x,y}^*X_{x,y}+2ys.
\tag{2.2}
$$

**证明。** 对每个正泛函，(1.1) 正好是 Hermitian 二阶矩阵

$$
\begin{pmatrix}
\phi(c^2)&\phi(c\circ t)-i\phi(g)\\
\phi(c\circ t)+i\phi(g)&\phi(t^2)
\end{pmatrix}
$$

的行列式非负。将列向量 $(-z,1)$ 代入，得到 $\phi(F_z)\ge0$。反向地，$\phi(F_z)\ge0$ 对全部 $z$ 给出第二分量非零的全部二次型；第二分量为零时由 $\phi(c^2)\ge0$ 支付，故该标量矩阵半正定。正泛函分离自伴正锥，遂得到 (2.1) 与 (1.1) 的等价性。直接展开 $X_{x,y}^*X_{x,y}$，其交叉项为 $-2x(c\circ t)+i\sigma y[c,t]$，而 $2yK_\sigma(c,t)=i\sigma y[c,t]$，即得 (2.2)。这里仅对全部标量 $z$ 检验 $F_z$，未声称对应的二阶算子矩阵为正，也没有二正性结论。∎

## 3. 实广义特征向量消去残量

**引理 3.1（实广义特征纤维上的残量消失）。** 在任意忠实表示 $\pi:A\hookrightarrow B(\mathcal H)$ 中，若 $\xi\in\mathcal H$ 和 $\lambda\in\mathbb R$ 满足

$$
(\pi(t)-\lambda\pi(c))\xi=0,
\tag{3.1}
$$

则

$$
\langle\pi(s)\xi,\xi\rangle=0.
\tag{3.2}
$$

若 $E_\lambda=\ker(\pi(t)-\lambda\pi(c))$，则 $\pi(s)$ 在 $E_\lambda$ 上的压缩为零。

**证明。** 对 (2.2) 取 $x=\lambda$，把同一个 $\xi$ 代入任意 $y\in\mathbb R$。由 (3.1)，

$$
X_{\lambda,y}\xi=-i\sigma y\,\pi(c)\xi,
$$

故正性给

$$
y^2\|\pi(c)\xi\|^2+2y\langle\pi(s)\xi,\xi\rangle\ge0
\qquad(y\in\mathbb R).
\tag{3.3}
$$

令 $y\downarrow0$ 与 $y\uparrow0$，线性项必须为零，得到 (3.2)。同一 $E_\lambda$ 中的任意复线性组合仍满足 (3.1)，因此对 $\xi+\eta$ 和 $\xi+i\eta$ 使用 (3.2) 的复极化，得
$\langle\pi(s)\xi,\eta\rangle=0$。∎

在定理 4.1 的实际秩一 $p,q$ 中，所消费的准确读取是 $\xi_p=(1,0,-\overline v/d)^T$ 与 $\xi_q=(0,1,-\overline w/d)^T$：它们分别满足 $p\xi_p=e_1,q\xi_p=0$ 和 $p\xi_q=0,q\xi_q=e_2$，所以 (3.2) 分别读出 $\rho=0$ 与 $\eta=0$。一般算子块的联合读取张成／忠实性桥尚未证明，准确义务见 §5。这里没有把未知 $D$ 压缩或下降到商代数，也不使用其可加性、齐次性或连续性。

## 4. 带真实环境连线的精确 $M_3$ 家族

**定理 4.1（环境耦合族的固定输出刚性）。** 取

$$
A=M_3(\mathbb C),\qquad P=S=e_{11}+e_{22},\qquad
p=e_{11},\quad q=e_{22},\quad C=PAP\cong M_2(\mathbb C),\quad
c=\operatorname{diag}(1,2,0).
$$

任取 $a,b,d\in\mathbb R$，其中 $d\ne0$，以及 $v,w,\zeta\in\mathbb C$，满足精确的实际条目关系 $\zeta d=v\overline w$，并令

$$
t=
\begin{pmatrix}
a&\zeta&v\\
\overline\zeta&b&w\\
\overline v&\overline w&d
\end{pmatrix},
\qquad
s=\rho e_{11}+\eta e_{22},
\qquad
g=K_\sigma(c,t)+s.
\tag{4.1}
$$

其中 $\rho,\eta\in\mathbb R$ 正好穷尽这两个秩一角的自伴残量。对两种取向 $\sigma\in\{1,-1\}$，若 (1.1) 对所有正泛函成立，则 $\rho=\eta=0$。因此 $g=K_\sigma(c,t)$，由 §1 的标准比较证明，(1.2) 对全部实际 $x\in C_{\rm sa}$ 成立；同时要求这些预算不改变结论。

这里

$$
ptp=a p,\qquad qtq=b q,
$$

所以两个对角输入可以任意取值，包括零；同时

$$
(1-P)tP=(1-S)tS=
\begin{pmatrix}0&0&0\\0&0&0\\\overline v&\overline w&0\end{pmatrix}.
$$

该实际真角 $C\cong M_2(\mathbb C)$ 到 $1-P=e_{33}$ 环境的连线非零，当且仅当 $(v,w)\ne(0,0)$；当 $v,w$ 均非零时，两个旧角都连到同一个环境。实际模型中的整个 $C$ 可作为已分类角；下列固定输出证明本身无需任何未知 $D$。

**证明。** 在同一个实际 $t$ 上置

$$
\xi_p=\begin{pmatrix}1\\0\\-\overline v/d\end{pmatrix},
\qquad
\xi_q=\begin{pmatrix}0\\1\\-\overline w/d\end{pmatrix}.
$$

关系 $\zeta d=v\overline w$ 及其共轭给出精确乘法

$$
\begin{aligned}
t\xi_p&=\begin{pmatrix}a-|v|^2/d\\0\\0\end{pmatrix}
       =\left(a-\frac{|v|^2}{d}\right)c\xi_p,\\
t\xi_q&=\begin{pmatrix}0\\b-|w|^2/d\\0\end{pmatrix}
       =\frac{b-|w|^2/d}{2}\,c\xi_q.
\end{aligned}
\tag{4.2}
$$

因为 $a,b,d$ 为实数，二者分别是 (3.1) 的实广义特征向量，参数为
$\lambda_p=a-|v|^2/d$ 和 $\lambda_q=(b-|w|^2/d)/2$。由引理 3.1，

$$
0=\langle s\xi_p,\xi_p\rangle=\rho,
\qquad
0=\langle s\xi_q,\xi_q\rangle=\eta.
$$

故 $s=0$，再由 (4.1) 得 $g=K_\sigma(c,t)$。∎

定理 4.1 不要求 $v,w$ 非零；一个或两个为零时，同一证明不变。$d\ne0$ 只用于写出精确的数学向量，不取 $v,w$ 的逆，不归一化 $\phi$，也没有对未知 $D$ 取无穷小极限。$a,b$ 完全任意，故不要求 $ptp$、$qtq$ 为零，也不要求它们非零。该证明只使用真实 $M_3$ 乘法与全部正泛函的 P2 读数。

这条实际条目关系可由成熟的 Schur 补消元直接看出。令 $r=1-S=e_{33}$，则 $rtr=dr$ 在实际一维环境角 $rAr$ 内可逆，逆元为 $d^{-1}r$，该角单位为 $r$。在 $p,q$ 坐标下，数学 Schur 补准确为

$$
StS-Str(rtr)^{-1}rtS
\longleftrightarrow
\begin{pmatrix}
a-|v|^2/d&\zeta-v\overline w/d\\
\overline\zeta-w\overline v/d&b-|w|^2/d
\end{pmatrix}.
\tag{4.3}
$$

它为对角矩阵当且仅当 $\zeta d=v\overline w$。这是同一个实际 $t$ 的条目间关系，只是已知矩阵消元；没有压缩未知响应，也没有引入物理 Schur 仪器。这一关系是输入族限制，不是新的 $D$ 公理，也不重定义完整目标。

例如取 $v=u,w=d,\zeta=u$，其中 $u,d\in\mathbb R$、$ud\ne0$，便得到

$$
t=\begin{pmatrix}a&u&u\\u&b&d\\u&d&d\end{pmatrix}.
$$

这只是定理 4.1 已覆盖的实参数子情形，不另立推论或重复证明。

## 5. 参数对应、已付内容与未决范围

定理 4.1 的 $p,q$ 正是固定输出接口中的两个实际非零正交投影，$P=S$ 是真角单位；第三坐标是 $1-P=1-S$ 的真实角外环境。向量 $\xi_p$、$\xi_q$ 是忠实表示中检验正算子铅笔的数学向量，不生产准备、菜单或响应输出。因而 (4.2) 只支付固定 P2 所蕴含的代数关系。

该显式家族保留任意 $a,b\in\mathbb R$，包括零，并允许二者同时非零；$v,w$ 可为任意复数，包括零，$d\in\mathbb R\setminus\{0\}$，且仅要求 $\zeta d=v\overline w$。真正角外连线的准确判据是 $(v,w)\ne(0,0)$，不能对全部允许成员声称两个环境边均非零。$\rho,\eta$ 为标量是因为实际 $p,q$ 秩一，不是对一般算子块的额外简化公理。普通有限维完整 H／$M_3$ 分类及其原行消费者已经支付；本卷唯一新增的纸面应用是这个具体耦合族、上述参数对应及其不依赖 $D$ 或外值的固定 P2 充分性。原卷定理 41.2 的零对角、无 $S$-补块连线结果照原范围复用。

$d=0$、非对角 Schur 补及一般算子值块均未由定理 4.1 处理。一般算子块还缺一条明确的张成／忠实性桥。对所有 $\lambda\in\mathbb R$、$\xi\in E_\lambda$，考虑成对块读取

$$
(r_p,r_q)\longmapsto
\langle\pi(r_p)\pi(p)\xi,\pi(p)\xi\rangle+
\langle\pi(r_q)\pi(q)\xi,\pi(q)\xi\rangle,
\qquad (r_p,r_q)\in(pAp)_{\rm sa}\oplus(qAq)_{\rm sa}.
$$

要从引理 3.1 推出一般 $s_p=s_q=0$，须证明这些联合块读取的实线性张成分离上述实际算子块空间，即全部读取为零蕴含 $r_p=r_q=0$。一般 $c,t$ 是否供应该分离性是 **UNPROVED**；本卷只在 (4.2) 的两个具体纤维上完成其秩一计算。任意 $A,t$ 的固定输出／全部探针目标仍为 OPEN，没有得到一般原混合整行或完整 $\mathsf H_A(D)$ 反模型。

成熟工具的归属沿承载原卷固定提交的定义 10.1、§36.3、§41.5：Peirce 块与角乘法术语见 Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，§2.6.2、Lemma 2.6.3；正泛函、正性、Gram／Cauchy–Schwarz、分离及表示背景见原卷所引 Gelfand–Naimark、Segal，亦见 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)。正 Hermitian 二表与标量参数正算子铅笔的互写、零 Gram／比例输入读取、复极化、正泛函分离以及 Schur 补矩阵消元均为成熟工具，引理 2.1、3.1 只保留为被消费的辅助证明；(4.3) 只展示该消元在实际条目上的矩阵。这些来源不被归为本卷特定 $M_3$ 家族的作者；本卷没有历史原创、文献穷尽或检索覆盖主张。

## 6. 完整原问题与七项物理合同的精确身份

本节物理来源谓词中的 $S$ 始终是原 Jordan 响应 $S(a,b)=a\circ b$，不是 §§1–5 中的投影 $S=p+q$。本卷的物理来源谓词逐字取承载原卷上述固定提交中定义 47.1 的递归全文合取，沿用其同一身份；下式的 $\mathrm{new}$ 仅是别名，不是新的物理谓词：

$$
\mathcal C_{47}^{\mathrm{new}}(\Omega;S,D)
:=\mathcal C_{47}^{\mathrm{pin}}(\Omega;S,D)
\quad\text{（定义 47.1 的同一对象、同一量词、同一递归上游）。}
\tag{6.1}
$$

式 (6.1) 将定义 47.1 全文及每份递归上游逐句、逐公式、逐量词、逐层固定版本同时纳入，保留其中所有对象和量词。特别完整纳入 AH64.3 第1–7项、SF 定义 105.1 第1–7项及式 (105.1)–(105.7)、SF96.1 和各项全部递归上游，以及 PB153.2 与其全部固定上游；各直接读取身份和内层钉版均严格沿定义 47.1，不由本卷别名压平。以下七项说明与该全文共同保留，不作为缩短合同。

其中固定根、全部静默与其他静态分支、原域 $E=A_{\rm sa}$、原评价族及其零／不等／次归一／非正常质量均不改变。原完整 $\mathsf H_A(D)$ 仍对所有原输入、两种次序、A1/P2、A2 的所有三表与排列、A3 小窗，以及每个实际三元组和全部嵌套调用的 PB 同时量化；PB 仍是

$$
v=D(c,x)-c\circ y,\qquad w=c\circ x+D(c,y),\qquad
D(x+v,y+w)-D(x-v,y-w)=-2x\circ v-2y\circ w.
\tag{6.2}
$$

式 (6.1) 保留原卷的七项物理合同，具体为：

1. **复 Hilbert、可观测量与实际相干叠加。** 已分类角中的复乘法、有限旧复 Gram 与数学 GNS 只能在原同一 $\Omega/\mathrm{native}$、具名标签、共同全词、parent/ready、合法控制与实际相干准备的全部前件下消费；数学向量不生产实际准备或可取得像。
2. **原态、效果、Born、全菜单与质量。** Born 概率只在同一原事件绑定、完整菜单、接受归属和严格正实际质量下归一；零、不等、次归一、静默、非正常支与所有固定支持全质量保留，零质量不作除法。
3. **真正相关联合、复合与张量。** 张量与复合只在同一实际非零有序相关联合、全词 $K/J$、交叉零、同向交换腿、共同实现、联合生成分离及所需重数同时成立时使用；相同边缘或数学同构不供应共同来源。
4. **typed CP、Kraus 与整台递归参考。** 每条实际 typed 分支的未归一上下文、全部输出及每个合法未来、质量运输、反变复合、分区、真支持、支持内补、交织夹界、精确根和累计支持运输均沿 SF 定义 105.1 及其相关式 (105.3)–(105.6) 和全部递归上游保留；完整谓词仍含第1–7项及全部式 (105.1)–(105.7)、SF96.1。正延拓不自动成为 CP，子代数不自动成为全 $B(H)$。
5. **完整仪器、TP、条件更新与 Lüders。** 完整 typed 菜单、接受端、整台环境、全部成功／失败／细记录／port／post-port 输出及未来、分组遗忘、单位分区、输出校准和 Lüders 射线前件均保留；正夹心只给代数入口，不生产可执行仪器。
6. **全部合法历史、全未来、真遗忘与真实 Return。** 所有顺序、自适应、并行、停止、拒绝、销毁、泄漏、参考副本、真遗忘、两侧与逆向 Return 均保留。CountRead 仍要求同一接受叶的完整活动输出、实际读后活动 ready、第一合法消费者以及读后同一完整活动输入对全部合法未来的真实 Return；同一算子不合并不同程序、记录或未来权限。
7. **动力、物理钟、能量与共同正作用量。** 原实际连续可逆流、实际逆、强连续酉实现、物理钟与单位、一般生成元域、Hamiltonian 解释、共同仪器及同一个正 $\hbar$ 的全部前件保留；数学指数、范数路径或辅助钟不生产真实动力学与跨装置共同作用量。

原卷边界 47.2 的实际分析器要求仍准确保留：对字面旧程序 $\tau;T_P$ 的指定接受族，在全部原准备、中间切口、参考／副本、允许的分析词和树、原坐标、完整菜单及固定支持全质量上，供应到同一原实际完整菜单与接受端的准备无关准确接受关联，保持原支持和未归一标尺。该接受关联不被加强成整仪器或全部历史恒等。CountRead 的上述同一接受完整活动输出、读后 ready、第一合法消费者及全输入／全未来 Return 也仍须实际供应。

因此 (6.1) 只是对完整来源的精确引用，不由定理 4.1 反向制造 Born、CP、复制、相干控制、CountRead 或 Return。边界仍是原完整目标：本卷只在一个允许真实真角外环境耦合的显式族中得到不依赖 $D$ 的固定 P2 充分性，一般固定输出／全部探针目标、完整物理来源和完整量子起源仍为 OPEN。

## 7. 中文直观说明

P2 的二阶矩阵可以改写成一族正算子铅笔：先把 $t$ 减去一个复数倍的 $c$，所得乘积必为正；残量 $s$ 只以 $2ys$ 的线性方式出现。若某个实数 $\lambda$ 使 $t\xi=\lambda c\xi$，那么在同一向量上把复数倍的虚部取正、取负，平方项都只有二次小量，而残量给出一阶正负相反的变化，只能为零。

在定理 4.1 中，$P=S$ 的前两维是一间真 $M_2$ 房间，第三维是房间外的环境。$v,w$ 是两间旧角连向这个共同环境的复系数；至少一个非零才有真正角外连线，两个均非零才是两间都接上环境。$d\ne0$ 让我们能在数学上精确消去环境坐标；条件 $\zeta d=v\overline w$ 正好要求消去后两间之间的交叉项为零。这不是新的响应公理，而是这批实际矩阵条目满足的关系。第一根向量只在 $p$ 和环境方向取分量，第二根只在 $q$ 和环境方向取分量；同一个 $t$ 上的两次精确乘法和引理 3.1 分别给出 $\rho=0$、$\eta=0$。某根连线为零时，对应向量的环境分量也为零，证明照样成立。$a,b$ 可任意改变，包括零，不要求两个对角输入非零。这个显式参数对应说明较弱的固定 P2 在该族已经够用；完整 H 下的有限维 $M_3$ 分类本来已经成立，不是这里的新成果。

$d=0$、消元后仍有非零交叉项以及一般算子值块的情形都未由这个家族证明解决。一般算子块仍须证明 §5 的联合读取张成确实分离两个实际块；两条秩一计算没有支付这条一般桥。即使残量在已有纤维上都读成零，也不能直接宣布整个 $pAp$、$qAq$ 中的残量为零。全部探针预算能否在一般情形补足这一步仍是 OPEN。

## 追加锚（本行以下为增补区）


## 8. 有限可逆环境的 Schur 谱分类

**§§8–12 的来源读法。** 下文 PB34、PB42、PB22 均指[《AURIC：全 PB 多项式运输与实根刚性》](AURIC_FULL_PB_POLYNOMIAL_TRANSPORT_AND_REAL_ROOT_RIGIDITY.md)在提交 `21e6dcd4cad211827c9df24646da9ff8fd2fd154` 的对应节；“运输卷 §10”指[《AURIC 区间原响应与移动投影的全域运输》](AURIC_INTERVAL_ORIGINAL_RESPONSE_AND_VARIABLE_PROJECTION_TRANSPORT.md)在同一提交的 §10。§§1–7 对提交 `0fd6b8d8b80330b90beecbc012c9b7eb9a57f765` 的引用、字节 SHA-256 及原有含义保持不变。

### 8.1 输入与结论

把前两维的真角写成 $C=\operatorname{diag}(c_1,c_2)$，其中 $c_1,c_2>0$，并允许一个有限环境块：

$$
c=\begin{pmatrix}C&0\\0&0_m\end{pmatrix},\qquad
t=\begin{pmatrix}B&V\\V^*&D\end{pmatrix},\qquad
s=\begin{pmatrix}\operatorname{diag}(s_1,s_2)&0\\0&0_m\end{pmatrix},
$$

其中 $B=B^*\in M_2(\mathbb C)$，$D=D^*\in M_m(\mathbb C)$ 可为不定或负定但必须可逆，$V\in M_{2,m}(\mathbb C)$，其中 $s_1,s_2\in\mathbb R$；$m=0$ 时所有环境块按空矩阵解释。置

$$
H=B-VD^{-1}V^*,\qquad A=C^{-1/2}HC^{-1/2},\qquad
g=K_\sigma(c,t)+s,\quad \sigma\in\{1,-1\}.
\tag{8.1}
$$

这里的 $D^{-1}$ 只出现在已知输入 $t$ 的 Schur 消元中，不是对未知总映射或物理响应作压缩。

**定理 8.1（可逆有限环境上的固定 P2 谱分类）。** 对全部正泛函的固定 P2（等价地，前述标量正算子铅笔对所有实 $x,y$ 非负）有如下互斥分类。
这里的“固定”是对给定的取向 $\sigma$；若另要求两个取向同时成立，应将相应的两个闭区间取交集。

1. 若 $A_{11}\ne A_{22}$，或 $A_{12}=0$，则固定 P2 成立当且仅当 $s=0$。
2. 若 $A_{11}=A_{22}=\alpha$ 且 $\beta:=|A_{12}|>0$，取酉矩阵 $U$ 使
  
  $$
  U^*AU=\Lambda:=\operatorname{diag}(\alpha+\beta,\alpha-\beta),\qquad
  Z=\operatorname{diag}(1,-1),\qquad
  \omega=(U^*ZU)_{12}.
  $$
  
  则 $\lvert\omega\rvert=1$，并且固定 P2 成立当且仅当存在 $\rho\in\mathbb R$ 使
  
  $$
  \operatorname{diag}(s_1,s_2)=\operatorname{diag}(c_1\rho,-c_2\rho),\qquad
  G=U^*C^{-1/2}\begin{bmatrix}I_2&-VD^{-1}\end{bmatrix},\qquad
  Q=(GG^*)^{-1}=\begin{pmatrix}q_1&h\\\overline h&q_2\end{pmatrix},
  $$
  
  $$
  R=\sqrt{q_1q_2},\qquad \Delta=R^2-|h|^2>0,\qquad J=\operatorname{Im}(\overline h\,\omega),
  $$
  
  且满足下列两个等价的锐条件：
  
  $$
  \left|h+\frac{i\sigma\rho\,\omega}{2\beta}\right|+\frac{|\rho|}{2\beta}\le R,
\tag{8.2}
  $$
  
  $$
  -\frac{\beta\Delta}{R+\sigma J}\le \rho\le
  \frac{\beta\Delta}{R-\sigma J}.
\tag{8.3}
  $$

在第二种情形中，$Q$ 由完整实际输入与原空间范数决定；准确地，

$$
GG^*=U^*C^{-1/2}(I_2+VD^{-2}V^*)C^{-1/2}U.
$$

因此完整耦合幅度及环境度量都参与，不能只从环境耦合的列空间或 $H$ 读取 $Q$。因为 $\lvert J\rvert\le\lvert h\rvert<R$，(8.3) 的两个分母严格为正；$\Delta>0$ 还说明区间包含非零内点。因而每一个平衡的非对角 Schur 输入都有一段真正的非零固定-P2 残量，而不是只有零点。端点也包括在内。第一种情形包含旧的对角 Schur 子类。

当 $m=0$、$c_1\ne c_2$ 且 $B=v\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$、$v>0$ 时，才恰好恢复 PB34.1 的两块标量族。此时直接代入

$$
\beta=\frac{v}{\sqrt{c_1c_2}},\qquad R=\frac{c_1+c_2}{2},\qquad
\Delta=c_1c_2,\qquad J=0,
$$

得到 $|\rho|\le2v\sqrt{c_1c_2}/(c_1+c_2)$。定理 8.1 本身仍允许 $c_1=c_2$ 和一般 $B$，这些输入不归为 PB34.1 的原范围。

### 8.2 广义特征向量的刚性分支

令 $u_1,u_2$ 是 $A$ 的正交归一特征向量，$Au_j=\lambda_j u_j$。相应的原空间向量为

$$
\xi_j=\begin{pmatrix}C^{-1/2}u_j\\-D^{-1}V^*C^{-1/2}u_j\end{pmatrix},\qquad
(t-\lambda_j c)\xi_j=0.
\tag{8.4}
$$

由本卷引理 3.1，$0=\xi_j^*s\xi_j=u_j^*S_0u_j$，其中

$$
S_0=C^{-1/2}\operatorname{diag}(s_1,s_2)C^{-1/2}=\operatorname{diag}(s_1/c_1,s_2/c_2).
$$

若 $\lambda_1\ne\lambda_2$，置 $a_j=|(u_j)_1|^2$。两个零对角条件是

$$
\begin{pmatrix}a_1&1-a_1\\a_2&1-a_2\end{pmatrix}\begin{pmatrix}s_1/c_1\\s_2/c_2\end{pmatrix}=0,\qquad
\det=a_1-a_2=\frac{A_{11}-A_{22}}{\lambda_1-\lambda_2}.
\tag{8.5}
$$

所以 $A_{11}\ne A_{22}$ 时两行确实可逆，严格得到 $s_1=s_2=0$；这不是“泛型”说法。若 $A_{12}=0$，坐标向量本身就是广义特征向量，分别给出 $s_1=s_2=0$。若特征值重复，则 $A$ 是标量矩阵，从而已经落入 $A_{12}=0$ 的分支。$s=0$ 时 (2.2) 直接是 $X^*X$，故反向蕴含也成立。

## 9. 平衡分支的圆与锐区间

### 9.1 Schur 行、正性与圆参数

在 $A_{11}=A_{22}=\alpha$、$\beta>0$ 时，$Z$ 与 $A-\alpha I$ 反交换。故

$$
U^*ZU=\begin{pmatrix}0&\omega\\\overline\omega&0\end{pmatrix},\qquad |\omega|=1,
\tag{9.1}
$$

而 (8.4) 的两个零对角条件给出且仅给出

$$
S_0=\rho Z,\qquad \operatorname{diag}(s_1,s_2)=\operatorname{diag}(c_1\rho,-c_2\rho).
\tag{9.2}
$$

令 $w=x+i\sigma y$，并为本节另定义重参数化铅笔

$$
\mathcal F(w):=F_{\operatorname{Re}(w)+i\sigma\operatorname{Im}(w)}
=(t-wc)^*(t-wc)+2\sigma\operatorname{Im}(w)s.
$$

参数变换 $w\mapsto\operatorname{Re}(w)+i\sigma\operatorname{Im}(w)$ 对每个 $\sigma\in\{1,-1\}$ 都是复平面的双射，所以本卷引理 2.1 的固定 P2 等价性在两个取向都完整保留。下文 $w$ 遍取全部非实数。Schur 消元给出 $X(w)=t-wc$ 可逆，且其前两行为

$$
C^{-1/2}U(\Lambda-wI)^{-1}G,\qquad
G=U^*C^{-1/2}\begin{bmatrix}I_2&-VD^{-1}\end{bmatrix}.
\tag{9.3}
$$

$G$ 满行秩二：右边的方括号含有 $I_2$，左边的两个因子可逆。因此 $Q=(GG^*)^{-1}$ 正定，$\Delta>0$。

把 $\mathcal F(w)$ 对 $X(w)^{-1}$ 作合同变换，并将 $\ker G$ 与 $G^*$ 的最小范数截面分开，得到

$$
\mathcal F(w)\ge0\quad\Longleftrightarrow\quad Q+M(w)\ge0,
\tag{9.4}
$$

其中 $M(w)$ 的对角为零，而

$$
M_{12}(w)=\sigma\rho\,\omega\,k(w),\qquad
k(w)=\frac{2\operatorname{Im}w}{(\alpha+\beta-\overline w)(\alpha-\beta-w)}.
\tag{9.5}
$$

(9.4) 的“当且仅当”是精确的：给定 $u=Gz$，$z^*z$ 的最小值是 $u^*Qu$；沿 $\ker G$ 的分量只增加范数。因此二维正性恰好是

$$
|h+\sigma\rho\,\omega\,k(w)|\le R.
\tag{9.6}
$$

直接倒数可得

$$
\frac1{k(w)}=\frac{(\operatorname{Re}w-\alpha)^2+(\operatorname{Im}w)^2-\beta^2}{2\operatorname{Im}w}-i\beta.
\tag{9.7}
$$

取 $\operatorname{Re}w=\alpha$，正的 $\operatorname{Im}w$ 使 (9.7) 的实部遍历 $\mathbb R$；所以所有非实 $w$ 的 $k(w)$ 恰好遍历

$$
\left|k-\frac{i}{2\beta}\right|=\frac1{2\beta},\qquad k\ne0.
\tag{9.8}
$$

闭包补上 $k=0$，而 $|h|<R$ 已自动满足该点。圆上的最大值给出

$$
\sup_{(9.8)}|h+\sigma\rho\omega k|
=\left|h+\frac{i\sigma\rho\omega}{2\beta}\right|+\frac{|\rho|}{2\beta},
\tag{9.9}
$$

这正是 (8.2)。当 $w$ 为实数时，$\mathcal F(w)=(t-wc)^2\ge0$，包括两个实根；这一步直接使用自伴平方，不需要逆矩阵。整个论证没有把实根处的不可逆性替换成未知响应的极限。

### 9.2 从圆 containment 到闭区间

用 $J=\operatorname{Im}(\overline h\,\omega)$ 展开 (8.2) 的平方，且保留其必要的 $R-|\rho|/(2\beta)\ge0$，得到

$$
R|\rho|-\sigma J\rho\le\beta(R^2-|h|^2)=\beta\Delta.
\tag{9.10}
$$

对 $\rho\ge0$ 和 $\rho\le0$ 分别整理，恰为 (8.3)。反向地，(9.10) 给出 $(R-|J|)|\rho|\le\beta\Delta$，因此由 $|J|\le|h|<R$，

$$
\frac{|\rho|}{2\beta}\le\frac{\Delta}{2(R-|J|)}
\le\frac{R+|h|}{2}<R.
$$

故反向平方时两边非负，没有丢失符号条件；该界同样包含 $\rho=0$ 和闭区间的两个端点。相位变换 $U\mapsto U\operatorname{diag}(e^{i\theta_1},e^{i\theta_2})$ 同时把 $h,\omega$ 乘以同一个相位，(8.2) 与 $J$ 不变；按 $\alpha+\beta,\alpha-\beta$ 的有序标记固定交换自由度。

这也给出越过区间的明确反例。若 (8.3) 失败，则圆上存在 $k$ 使 $|h+\sigma\rho\omega k|>R$；若唯一最大点是被闭包删去的 $k=0$，取其附近的非零圆点即可。由 (9.7) 取到一个非实 $w$，令 $M=M(w)$。此时 $Q+M$ 的行列式为 $q_1q_2-|h+\sigma\rho\omega k|^2<0$，取 $u$ 使 $u^*(Q+M)u<0$，再令 $z=G^*Qu$，则 $Gz=u$ 且

$$
z^*(I+G^*MG)z=u^*(Q+M)u<0.
$$

最后取原空间向量 $\xi=X(w)^{-1}z$，就有 $\xi^*\mathcal F(w)\xi<0$。因此区间外不是未检验的数值猜测，而是由一个非实铅笔点和一个具体的数学向量反向击穿 P2；反之 (9.4)–(9.9) 对所有非实点成立，再加实轴上的平方项，完成充分性。

## 10. 一个具有非零环境边的 $M_3(\mathbb C)$ 矩阵实例

取

$$
c=\operatorname{diag}(1,2,0),\qquad D=(1),\qquad V=\begin{pmatrix}1\\0\end{pmatrix},\qquad
B=\begin{pmatrix}1&\sqrt2\\\sqrt2&0\end{pmatrix},
$$

即

$$
t=\begin{pmatrix}1&\sqrt2&1\\\sqrt2&0&0\\1&0&1\end{pmatrix}.
\tag{10.1}
$$

这里 $H=\left(\begin{smallmatrix}0&\sqrt2\\\sqrt2&0\end{smallmatrix}\right)$，故

$$
A=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad
\omega=1.
$$

直接由 (9.3) 得

$$
G=\frac1{\sqrt2}\begin{pmatrix}1&1/\sqrt2&-1\\1&-1/\sqrt2&-1\end{pmatrix},\qquad
Q=\begin{pmatrix}5/4&-3/4\\-3/4&5/4\end{pmatrix}.
\tag{10.2}
$$

所以 $R=5/4$、$\Delta=1$、$J=0$，而对

$$
s=\rho\,\operatorname{diag}(1,-2,0)
$$

固定 P2 的准确范围为

$$
|\rho|\le\frac45.
\tag{10.3}
$$

这是一条真正的角—环境连线（$V\ne0$）上的非零残量区间；它不是把第三坐标删除后得到的二维玩具，也没有用任何未知总映射。它只说明该实际矩阵族的固定 P2 几何，不能升级为完整 $\mathsf H_A(D)$ 或全部 PB 的分类。

## 11. 与既有支付结果、成熟工具和完整来源的边界

定理 8.1 使用本卷引理 2.1 的标量正铅笔等价和本卷引理 3.1 的实广义特征纤维消去，并包含本卷定理 4.1 的有限 $M_3$ 对角 Schur 刚性作为子情形。$m=0$、$c_1\ne c_2$ 且 $B=v\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$、$v>0$ 的特化按 §8.1 恰好恢复 PB34.1；$c_1=c_2$ 或一般 $B$ 不属于该原定理的输入类。PB42 提供平衡零环境对角星形族的非零残量 P2 证书；运输卷 §10 对移位族在 $\lambda\ne0,\ 0<|\rho|\le\min(1/4,|\lambda|)$ 的区域给出实际非零原探针，否定该区域内从固定 P2 到全部探针预算的蕴含。星形 P2 证书与移位族的非零探针各按上述钉版来源承担自身结论。AH42.4（PB22.1）已经支付有限三维的 FULL-$\mathsf H$ 分类；这里的有限环境 Schur 推导不计作新的 FULL-$\mathsf H$ 结果。

有限维谱定理、Schur 补、正 Hermitian 二表、Gram/Cauchy–Schwarz、正泛函分离、最小范数截面、二维行列式和圆的最大模估计是成熟工具；其一般背景沿本卷 §5 和原卷 §36.3 所引 Hanche-Olsen–Størmer、Gelfand–Naimark、Segal、Blackadar 及标准有限维线性代数。把这些工具按 $C\oplus0_m$ 的实际输入、$G$ 的环境行和 (9.8) 的圆重新组织，是本仓库的 repo-derived synthesis；不作历史优先权、文献穷尽或独立外部原创声明，也不把成熟工具的来源归为本节特定族的作者。

旧的对角 Schur 情形正是 $A_{12}=0$ 的第一分支。旧 §§5、7 的非对角 Schur 缺口在定理 8.1 限定的两个标量秩一角残量、可逆有限环境和实际输入类内已经闭合，包含该类中所有非对角 Schur 补。既有已付子类以外的奇异环境 $D$、高秩算子值角残量与一般块、任意 $C^*$-代数及全部 PB 探针的一般分类仍未付。§8.1 的 $GG^*$ 公式表明，完整实际耦合幅度及原空间度量共同决定允许半径，不能只从环境列空间或 $H$ 读取。所有零、不等、次归一或非正常质量仍沿本卷引理 2.1 的正泛函等价处理，不对质量作除法。

严格的局部简化是：无穷多个复参数铅笔测试被压缩为“谱是否平衡”与一个显式圆 containment/闭区间；它没有减少完整原量子来源的任何前件。全部原准备、事件、过程、参考与副本、相关联合、零与不等质量、时钟和单位、控制与 ready/flags、完整记录、失败、停止、销毁、未来、Return、固定支持、full-menu 和中间切口仍由 §6 的同一 $\mathcal C_{47}^{\mathrm{pin}}$ 逐项承担。该固定 P2 分类不供应原分析器来源，本节不引入 CountRead、native-control 或任何类似假设；实际 analyzer、CountRead、Return supplier 以及 all-PB-probe classification 仍是分离的 OPEN 义务。数学特征向量和 GNS 也不生产物理准备、Born 菜单、CP/Kraus、复制、相干控制或共同正作用量；没有新的量子 axiom candidate 被提出。

## 12. 中文直观说明

把 $c$ 想成只在真角的两格亮起、在环境格上归零的刻度盘。$D$ 虽然可以有负方向，只要它可逆，就能在输入矩阵里做一次诚实的 Schur 消元：环境对两格的影响被完整地留在 $H=B-VD^{-1}V^*$ 和随后出现的行矩阵 $G$ 中。这里没有把未知规则、实验仪器或物理环境压缩掉；只是把同一个已知 $t$ 的线性方程解开。

若归一化后的 $A$ 有两个不同的对角读数，或者根本没有交叉项，两个广义特征方向分别把残量读成零，因而两格都不能留下余量。唯一能留下余量的几何，是两格的对角读数完全相等、但它们仍以非零交叉相连。那时残量只能一正一负地平衡，写成 $\rho Z$；这正是老的两块标量区间为什么不是错误，而是唯一可能的非刚性。

平衡以后，全部非实参数 $w$ 经重参数化铅笔 $\mathcal F(w)$ 保留两个取向的完整 P2 测试。Schur 行把它们变成 $k(w)$，而 $1/k(w)$ 在一条水平直线上移动，所以 $k(w)$ 正好遍历去掉零点的圆。$Q>0$ 是二维行空间上的正度量，并固定正数 $q_1,q_2$；在这两个对角元固定时，正性允许的复非对角元 $z$ 构成闭圆盘 $|z|\le R$。$h+\sigma\rho\omega k$ 描出一条圆（$\rho=0$ 时退化为一点），其闭包包含在该圆盘中恰好等价于“中心距离加半径”不超过 $R$。这里没有把 $Q$ 本身断言为 $k$ 平面中的椭圆。把这个几何不等式平方，就得到带方向项 $J$ 的左右两个精确端点。越过端点时，圆上有一个对应非实 $w$ 的点，并且最小范数的反解向量直接把 $\mathcal F(w)$ 读成负数。

三维实例中，第三格确实通过 $V$ 接到第一格，残量仍可在 $|\rho|\le4/5$ 的闭区间内存在。这说明真实环境耦合本身不强迫固定 P2 刚性；允许半径还取决于完整实际耦合的幅度及原空间度量。它只是一条固定输入的代数结算：要回到 Omega 的完整量子起源，仍必须找到原始准备、事件、完整仪器、共同相关联合、全历史与未来、真实 Return 和 CountRead 的逐项来源。运输卷 §10 的移位星形全部探针反例边界和完整三维 FULL-$\mathsf H$ 支付各自保持原身份，不能被这个圆或这个向量替代。

## 新增锚（本行以下为后续增补区）
## 13. 任意有限 Hermitian 环境的零模耦合分类

### 13.1 同一个固定 P2 输入与已知环境的逆

本节保留 §8 的全部数学输入，只删除已知环境块可逆这一条限制。准确地，令 $m\ge0$ 有限，

$$
C=\operatorname{diag}(c_1,c_2)>0,\qquad
c=C\oplus0_m,\qquad
t=\begin{pmatrix}B&V\\V^*&D\end{pmatrix}=t^*,\qquad
s=\operatorname{diag}(s_1,s_2)\oplus0_m,
\tag{13.1}
$$

其中 $B\in M_2(\mathbb C)$、$D\in M_m(\mathbb C)$ 均 Hermitian，$s_1,s_2\in\mathbb R$，$V$ 任意；$c_1=c_2$ 也允许。这里 $D$ 始终是已知输入 $t$ 的环境矩阵，不是未知总响应。对给定 $\sigma\in\{1,-1\}$，输出仍为 $g_\sigma=\sigma i[c,t]/2+s$。固定 P2 的完整量词是

$$
\phi(g_\sigma)^2\le
\phi(c^2)\phi(t^2)-\phi(c\circ t)^2
\qquad\bigl(\phi\ge0\text{ 遍取 }M_{2+m}(\mathbb C)\text{ 上全部正复线性泛函}\bigr).
\tag{13.2}
$$

不归一化、不删零或不等质量，不缩成真角上的泛函。沿 §9.1 的双射重参数化，§2 的既有等价式准确成为

$$
\mathcal F_\sigma(w)=(t-wc)^*(t-wc)+2\sigma\operatorname{Im}(w)s\ge0
\qquad(w\in\mathbb C).
\tag{13.3}
$$

令 $D^\dagger$ 为这个已知有限 Hermitian 矩阵的 Moore–Penrose 逆：在每个非零谱值上取倒数，在核上为零。令

$$
N=\ker D,\qquad P_N=I-D^\dagger D,\qquad
W=V|_N,\qquad N_0=\ker W\subseteq N,\qquad
N_1=N\ominus N_0,\qquad r=\operatorname{rank}W\in\{0,1,2\},
$$

$$
H=B-VD^\dagger V^*.
\tag{13.4}
$$

$D^\dagger$、$P_N$ 和 $H$ 只是同一输入的谱分解与矩阵运算；没有对未知响应取逆、作函数演算或要求其与压缩、换基、取极限交换。特别是 $H$ 只消去环境的非零谱部分，不能在 $r>0$ 时把零模连线一起忽略。

环境有实际正交分解 $\operatorname{ran}D\oplus N_1\oplus N_0$，且 $\dim N_1=r$。$c,t,s$ 在 $N_0$ 上都为零；自伴性还保证它是共同约化子空间。因此 (13.3) 正好是 $N_0^\perp$ 上的铅笔直和零，正性当且仅当缩小后的铅笔正。这里沿用原空间的正交限制和范数。通过 (13.2)–(13.3) 的原空间等价性，原来全部正泛函的域完整保留，包括在 $N_0$ 上有质量或与其有非对角密度块的泛函；这不是物理删口或未知响应的下降。

### 13.2 秩一时的原空间行与锐条件

若 $r=1$，取 $N_1$ 的单位生成元 $q$，置

$$
v=C^{-1/2}Vq,\qquad \gamma=\|v\|>0,\qquad n=v/\gamma,
\qquad e^*n=0,\quad\|e\|=1,\quad U=[e,n],
$$

$$
A=U^*C^{-1/2}HC^{-1/2}U
=\begin{pmatrix}a&b\\\overline b&d\end{pmatrix},\qquad
S_0=U^*C^{-1/2}\operatorname{diag}(s_1,s_2)C^{-1/2}U.
\tag{13.5}
$$

$a,d$ 为实数。下列两行作用在原来的 $\mathbb C^2\oplus\mathbb C^m$ 右端项上，不重新选择环境度量：

$$
L=e^*C^{-1/2}\begin{bmatrix}I_2&-VD^\dagger\end{bmatrix},\qquad
j=\gamma^{-1}\begin{bmatrix}0_{1\times2}&q^*\end{bmatrix},\qquad
G=\begin{bmatrix}L-bj\\j\end{bmatrix},
$$

$$
Q=(GG^*)^{-1}=\begin{pmatrix}q_1&h\\\overline h&q_2\end{pmatrix},\qquad
R=\sqrt{q_1q_2},\qquad \Delta=R^2-|h|^2.
\tag{13.6}
$$

$G$ 的第二行在演员两列为零，而第一行在那里为非零的 $e^*C^{-1/2}$；第二行本身非零。因此 $G$ 满行秩，$Q>0$，$q_1,q_2,\Delta>0$。两行均消去 $N_0$，所以在原空间或其正交约化空间计算 $GG^*$ 得到同一个矩阵。

当原演员坐标中的 $|n_1|^2=|n_2|^2=1/2$ 时，称这个零模连线平衡。令 $Z=\operatorname{diag}(1,-1)$，则

$$
U^*ZU=\begin{pmatrix}0&\omega\\\overline\omega&0\end{pmatrix},\qquad
\omega=(U^*ZU)_{12},\quad |\omega|=1,\qquad
J=\operatorname{Im}(\overline h\,\omega).
\tag{13.7}
$$

**定理 13.1（任意有限环境的完整固定-P2 分类）。** 对 (13.1) 的给定输入和给定取向 $\sigma$，(13.2) 有以下互斥且穷尽的分类。

1. **$r=0$：复用可逆谱分类。** 在 $N_0^\perp=\mathbb C^2\oplus\operatorname{ran}D$ 上，直接应用定理 8.1，环境为 $D_1=D|_{\operatorname{ran}D}$，允许空环境。其 Schur 矩阵是 (13.4) 的 $H$。准确说，令 $A_0=C^{-1/2}HC^{-1/2}$；若 $(A_0)_{11}\ne(A_0)_{22}$ 或 $(A_0)_{12}=0$，则当且仅当 $s=0$。否则按 §8.1 的有序谱基 $U_0$、$\beta=|(A_0)_{12}|$，以 $G_0=U_0^*C^{-1/2}[I_2,-VD^\dagger]$ 计算原来的 $Q,R,\Delta,J$，结论正是 $s=\rho\operatorname{diag}(c_1,-c_2)\oplus0_m$ 及 (8.2)–(8.3)。这是既有结果的直接应用。
2. **$r=1$：零模平衡分支。** 若 $|n_1|^2\ne|n_2|^2$，则当且仅当 $s=0$。若 $|n_1|^2=|n_2|^2=1/2$，则当且仅当 $s=\rho\operatorname{diag}(c_1,-c_2)\oplus0_m$，其中 $\rho\in\mathbb R$ 满足

   $$
   |h-i\sigma\rho\omega|+|\rho|\le R,
   \tag{13.8}
   $$

   等价地，

   $$
   -\frac{\Delta}{2(R-\sigma J)}\le\rho\le
   \frac{\Delta}{2(R+\sigma J)}.
   \tag{13.9}
   $$

3. **$r=2$：完全刚性。** 固定 P2 当且仅当 $s=0$，与 $B$、非零谱环境及其连线的具体值无关。

秩一的 (13.9) 中 $|J|\le|h|<R$，故分母严格正，两个端点均包括，区间内部包含 $0$ 的一个开邻域，特别包含非零残量。若分别对 $g_+$ 和 $g_-$ 要求两个取向，则必须取两个区间的交集。在平衡秩一分支，这个交集可进一步准确写为

$$
I_+\cap I_-=
\left[-\frac{\Delta}{2(R+|J|)},\frac{\Delta}{2(R+|J|)}\right],
\tag{13.10}
$$

因为两种符号的左端点取较大者、右端点取较小者，恰都选取分母 $R+|J|$。这没有把单个取向的非对称区间替换成对称区间。

### 13.3 非实铅笔的精确消元

以下证明新出现的 $r=1,2$ 分支；$r=0$ 只作上述复用。在 $N_0^\perp$ 的正交坐标 $\mathbb C^2\oplus\operatorname{ran}D\oplus N_1$ 上，写 $V_1=V|_{\operatorname{ran}D}$、$W_1=V|_{N_1}$，则

$$
X(w)=t-wc=
\begin{pmatrix}B-wC&V_1&W_1\\V_1^*&D_1&0\\W_1^*&0&0\end{pmatrix}.
\tag{13.11}
$$

对非实 $w$，若 $X(w)(u,y,z)^{\mathsf T}=0$，其二次型虚部给
$-\operatorname{Im}(w)u^*Cu=0$，所以 $u=0$；第二行给 $y=0$，第一行给 $W_1z=0$。$W_1$ 在 $N_1$ 单射，故 $z=0$。有限维性于是给 $X(w)$ 可逆。空的 $\operatorname{ran}D$ 块按空方程处理。

当 $r=1$，用 $q$ 作 $N_1$ 的坐标，$W_1=\gamma C^{1/2}n$。给定右端项 $\eta=(\eta_A,\eta_R,\eta_N)$，令 $\zeta=U^*C^{1/2}u$。第二、三行及第一行的 $e$ 分量依次给

$$
y=D_1^{-1}(\eta_R-V_1^*u),\qquad
\zeta_2=\eta_N/\gamma=j\eta,\qquad
(a-w)\zeta_1+b\zeta_2=L\eta.
$$

第一行剩余的 $n$ 分量唯一确定 $z$，不再限制 $\eta$。因此逆矩阵的演员部分准确为

$$
u=C^{-1/2}U T(w)G\eta,\qquad
T(w)=\operatorname{diag}((a-w)^{-1},1).
\tag{13.12}
$$

在原空间中，$L,j$ 正好就是 (13.6)，因为 $D^\dagger=D_1^{-1}\oplus0_N$；不存在把 $N_1$ 的坐标任意缩放成新度量的步骤。

### 13.4 两个零对角约束与耦合秩二的刚性

先看 $r=1$。在同一正交坐标中取

$$
\xi_a=\begin{pmatrix}
C^{-1/2}e\\-D_1^{-1}V_1^*C^{-1/2}e\\-\overline b/\gamma
\end{pmatrix}.
\tag{13.13}
$$

由 (13.5)，消去 $\operatorname{ran}D$ 后，第一行的归一化值为
$(A-aI)(1,0)^{\mathsf T}+\gamma(0,1)^{\mathsf T}(-\overline b/\gamma)=0$；另两行也为零。故 $(t-ac)\xi_a=0$。在 $N_0$ 上补零得到原空间向量。$a$ 为实数，§3 的既有实广义特征纤维引理遂给

$$
(S_0)_{11}=\xi_a^*s\xi_a=0.
\tag{13.14}
$$

为读取第二对角，令 $w=x+iy$，$y\ne0$。将 (13.3) 对 $X(w)^{-1}$ 作合同变换，利用 (13.12)，准确得到

$$
I+G^*M(w)G\ge0,\qquad
M(w)=2\sigma y\,T(w)^*S_0T(w).
\tag{13.15}
$$

对任意 $z\in\mathbb C^2$，满足 $G\eta=z$ 的最小范数向量为 $\eta_0=G^*Qz$：它确实映到 $z$，与 $\ker G$ 正交，且 $\|\eta_0\|^2=z^*Qz$。其余向量为 $\eta_0+\kappa$，$\kappa\in\ker G$，范数平方多出 $\|\kappa\|^2$。所以 (13.15) 当且仅当

$$
Q+M(w)\ge0.
\tag{13.16}
$$

由 (13.14)，$M_{11}=0$、$M_{22}=2\sigma y(S_0)_{22}$。若 $(S_0)_{22}\ne0$，选使 $\sigma y(S_0)_{22}<0$ 且 $2|y(S_0)_{22}|>q_2$ 的一个有限 $y$，就使 (13.16) 的第二对角为负。因而

$$
(S_0)_{11}=(S_0)_{22}=0.
\tag{13.17}
$$

这里没有给未知响应加入连续性或无穷小输入规则。令 $p=|n_1|^2$、$\alpha_j=s_j/c_j$；二维酉性给 $|e_1|^2=1-p$，于是 (13.17) 正好是

$$
(1-p)\alpha_1+p\alpha_2=0,\qquad
p\alpha_1+(1-p)\alpha_2=0.
\tag{13.18}
$$

其系数行列式为 $1-2p$。不平衡时 $\alpha_1=\alpha_2=0$；平衡时恰为 $\alpha_1=-\alpha_2=\rho$，且 (13.7) 给 $(S_0)_{12}=\rho\omega$。这证明了秩一分支中残量形状的必要性。

当 $r=2$，$W_1$ 是两个二维空间之间的可逆矩阵。(13.11) 的第三行对任何右端项都固定演员向量 $u=(W_1^*)^{-1}\eta_N$，完全不依赖 $w$。若 $s\ne0$，可取 $u$ 使 $u^*\operatorname{diag}(s_1,s_2)u\ne0$，并固定右端项 $\eta=(0,0,W_1^*u)$。对每个非实 $w$，$\xi(w)=X(w)^{-1}\eta$ 的演员部分就是这个 $u$。于是 (13.3) 必须给

$$
\|W_1^*u\|^2+2\sigma y\,u^*\operatorname{diag}(s_1,s_2)u\ge0
\qquad(y\in\mathbb R\setminus\{0\}).
\tag{13.19}
$$

选相反符号且足够大的有限 $y$ 即矛盾。因此 $s=0$。在秩一不平衡和秩二的各刚性分支，$s=0$ 的充分性统一由 (13.3) 的平方项直接支付。

### 13.5 同一个圆、取向与全部端点

秩一平衡时，(13.15)–(13.17) 的非对角元为

$$
M_{12}(w)=\sigma\rho\omega\,k(w),\qquad
k(w)=\frac{2\operatorname{Im}w}{a-\overline w},\qquad
\frac1{k(w)}=\frac{a-\operatorname{Re}w}{2\operatorname{Im}w}+\frac i2.
\tag{13.20}
$$

固定任何一个非零虚部，改变实部就使倒数的实部遍历实轴。因此非实 $w$ 的像准确为

$$
|k+i|=1,\qquad k\ne0.
\tag{13.21}
$$

$Q+M(w)$ 的对角元始终为严格正的 $q_1,q_2$，所以 (13.16) 恰好等价于 $|h+\sigma\rho\omega k|\le R$。在 (13.21) 的圆上取上确界，补点 $k=0$ 时的条件 $|h|<R$ 本来就成立，故

$$
\sup_{|k+i|=1,\ k\ne0}|h+\sigma\rho\omega k|
=|h-i\sigma\rho\omega|+|\rho|.
\tag{13.22}
$$

这证明 (13.8) 对全部非实点的必要与充分性。它与 §9 的圆包含机制相同，但圆的中心在这里为 $-i$，不能照抄 (8.2) 的符号或谱间距。

展开 $|h-i\sigma\rho\omega|^2=|h|^2+\rho^2+2\sigma J\rho$，且保留 $R-|\rho|\ge0$，得到

$$
R|\rho|+\sigma J\rho\le\Delta/2.
\tag{13.23}
$$

分别对 $\rho\ge0$ 和 $\rho\le0$ 整理，就是 (13.9)。反向地，(13.23) 蕴含

$$
|\rho|\le\frac{\Delta}{2(R-|J|)}
\le\frac{R+|h|}{2}<R,
$$

所以反向平方没有引入伪解。严格正分母和 $\Delta>0$ 同时证明非零内点确实存在。整个推导使用非严格不等式，故保留闭端点、$\rho=0$ 及退化二表。

若区间条件失败，(13.22) 给一个非零圆点使 $|h+\sigma\rho\omega k|>R$；即便一个上确界位置是补点，严格违反仍在附近非零圆点保持。由 (13.20) 取到非实 $w$，$Q+M(w)$ 的行列式为负。取 $z$ 使 $z^*(Q+M(w))z<0$，令 $\eta=G^*Qz$，再令 $\xi=X(w)^{-1}\eta$，则

$$
\xi^*\mathcal F_\sigma(w)\xi
=\eta^*(I+G^*M(w)G)\eta
=z^*(Q+M(w))z<0.
\tag{13.24}
$$

在 $N_0$ 上补零即为原空间中的违反读取。由 §2 的等价性，该正向量泛函不能满足固定 P2。这也给出区间外的反证机制。

对所有实 $w$，包括 $w=a$ 及任何其他实奇点，直接有 $\mathcal F_\sigma(w)=(t-wc)^2\ge0$；无需逆矩阵，更无需未知输入的极限。结合 (13.22)，完成全部复平面上的充分性，因而定理 13.1 的新分支证毕。∎

### 13.6 相位与正交环境坐标不变性

若 $q'=e^{i\chi}q$，则 $n'=e^{i\chi}n$；再令 $e'=e^{i\theta}e$，写 $T_0=\operatorname{diag}(e^{i\theta},e^{i\chi})$。直接由定义，

$$
b'=e^{i(\chi-\theta)}b,\qquad L'=e^{-i\theta}L,\qquad
j'=e^{-i\chi}j,\qquad G'=T_0^*G,\qquad Q'=T_0^*QT_0.
$$

因此 $h$ 与 $\omega$ 同乘 $e^{i(\chi-\theta)}$，$q_1,q_2,R,\Delta,J$ 均不变，(13.8)–(13.10) 也不变。平衡性只取决于 $|n_1|^2,|n_2|^2$，不依赖这些选择。

对任意环境酉换基 $E$，新坐标中 $V'=VE$、$D'=E^*DE$、$(D')^\dagger=E^*D^\dagger E$、$q'=E^*q$。此时 $H,v,\gamma,n$ 不变，$L'=L\operatorname{diag}(I_2,E)$、$j'=j\operatorname{diag}(I_2,E)$，故 $G'G'^*=GG^*$。零模耦合秩以及上述分类全部不变。这种不变性是同一个有限矩阵和原 Hilbert 范数的坐标不变性，不是未知响应的自然性公理，也不允许任意非酉环境变换后仍使用原来的 $Q$。

## 14. 秩一零模的非对称区间与已付星形的回收

### 14.1 一个带非零方向项的三维输入

取

$$
C=\operatorname{diag}(1,2),\qquad D=(0),\qquad
V=\begin{pmatrix}1\\\sqrt2\end{pmatrix},\qquad
B=\begin{pmatrix}0&i\sqrt2\\-i\sqrt2&0\end{pmatrix},\qquad
t=\begin{pmatrix}0&i\sqrt2&1\\-i\sqrt2&0&\sqrt2\\1&\sqrt2&0\end{pmatrix}.
\tag{14.1}
$$

这里 $r=1$，取 $q=1$、$e=(1,-1)^{\mathsf T}/\sqrt2$、$n=(1,1)^{\mathsf T}/\sqrt2$、$\gamma=\sqrt2$。因 $D^\dagger=0$，$H=B$，在 $U=[e,n]$ 中

$$
A=\begin{pmatrix}0&i\\-i&0\end{pmatrix},\qquad a=0,\quad b=i,\quad\omega=1,
$$

$$
G=\begin{pmatrix}1/\sqrt2&-1/2&-i/\sqrt2\\0&0&1/\sqrt2\end{pmatrix},\qquad
GG^*=\begin{pmatrix}5/4&-i/2\\i/2&1/2\end{pmatrix}.
\tag{14.2}
$$

其行列式为 $3/8$，故普通二阶逆给

$$
Q=\begin{pmatrix}4/3&4i/3\\-4i/3&10/3\end{pmatrix},\qquad
R=\frac{2\sqrt{10}}3,\quad \Delta=\frac83,\quad J=-\frac43.
\tag{14.3}
$$

对 $s=\rho\operatorname{diag}(1,-2,0)$，定理 13.1 因而给出准确充要条件

$$
\frac{2\sigma-\sqrt{10}}3\le\rho\le
\frac{2\sigma+\sqrt{10}}3.
\tag{14.4}
$$

例如左端点由 $-\Delta/[2(R-\sigma J)]=-2/(\sqrt{10}+2\sigma)=(2\sigma-\sqrt{10})/3$ 得到；右端点同理由 $2/(\sqrt{10}-2\sigma)$ 得到。分别要求两种取向时，两个不同区间的交集正是

$$
|\rho|\le\frac{\sqrt{10}-2}{3}.
\tag{14.5}
$$

这是一个固定三维输入的全正泛函 P2 结论。它展示 $b\ne0$ 通过原空间行度量产生 $J\ne0$，使单个取向的允许区间偏离对称；不构成全部 PB、完整 $\mathsf H_A(D)$ 或未知总响应的反模型。

### 14.2 已付实星形不再计作新成果

将 (14.1) 的 $B$ 改为 $\lambda C$，$\lambda\in\mathbb R$，其余 $C,D,V$ 不变，便准确得到运输卷的已付移位实星形。此时 $H=\lambda C$，而归一化的 $A=\lambda I$、$b=0$；直接在 (13.6) 中取

$$
G=\begin{pmatrix}1/\sqrt2&-1/2&0\\0&0&1/\sqrt2\end{pmatrix},\qquad
Q=\operatorname{diag}(4/3,2),\qquad h=J=0,\quad\omega=1.
$$

故 (13.8) 为 $2|\rho|\le\sqrt{8/3}$，恰好是 $\rho^2\le2/3$。这只回收[运输卷定理 11.2](https://github.com/the-omega-institute/trureturing/blob/caab4df341883a38bfc59b17ca04ad2c41af4e32/docs/develop/theory/AURIC_INTERVAL_ORIGINAL_RESPONSE_AND_VARIABLE_PROJECTION_TRANSPORT.md)在固定提交 `caab4df341883a38bfc59b17ca04ad2c41af4e32` 的全部正泛函阈值，包括所有实 $\lambda$、两种取向和端点；不把这条已付阈值或旧星形证书计作新增。该固定提交中的运输卷定理 11.4 与推论 11.6 分别提供实际非零探针的扩大排除域与必要残余包络，并未给出星形的全部探针充要分类。

## 15. 精确增益、成熟归属与完整原来源边界

本节新增的 repo-derived 综合是定理 13.1 在 $r=1,2$ 的完整推导，以及它与 $r=0$ 既有分类的共同组织：在同一个有限正秩二演员、对角标量角残量、任意有限 Hermitian 输入环境和全原空间正泛函的固定 P2 类中，去掉环境块可逆这一条数学前件，按 $\operatorname{rank}(V|_{\ker D})=0,1,2$ 完整分类。$r=0$ 的谱平衡结果直接复用定理 8.1；§14.2 的实星形阈值直接复用上述固定运输卷定理 11.2；有限三维及其他原范围内的 FULL-$\mathsf H$ 分类仍按 §11 的 AH42.4／PB22.1 等既有结果承担。§§11–12 关于奇异环境未付的原文字节保留，其缺口只在本节明确列出的有限输入类内由定理 13.1 闭合。

Moore–Penrose 逆及有限 Hermitian 谱分解、非零谱块的 Schur 消元、正 Hermitian 二表、最小范数截面与 Gram 矩阵、二维行列式和圆的最大模均是成熟工具。Moore–Penrose 逆的背景可参见 Penrose，[*A generalized inverse for matrices*](https://doi.org/10.1017/S0305004100030401)，其余背景沿 §§5、11 的既有归属；这里给出的谱定义和逐行消元已列明全部所用性质。不将通用工具重称为本仓库原创，不作历史优先权、文献穷尽或独立外部原创主张。新的组合关系是：环境核留下的约束先固定演员的若干坐标，耦合秩决定剩余实根读取与非实参数读取怎样共同消去残量，再由保持原范数的 $G$ 确定锐区间。

本节的固定运输卷引用严格为 `caab4df341883a38bfc59b17ca04ad2c41af4e32`；它不改写 §§8–12 的 `21e6dcd4cad211827c9df24646da9ff8fd2fd154` 或 §§1–7 的 `0fd6b8d8b80330b90beecbc012c9b7eb9a57f765` 引用身份。完整原目标和 §6 的同一 $\mathcal C_{47}^{\mathrm{pin}}$ 递归全文保持不变，包含定义 47.1、AH64.3 第1–7项、SF 定义 105.1 第1–7项及 (105.1)–(105.7)、SF96.1、PB153.2 和每份固定递归上游。

具体说，七项消费者仍分别需要：原复 Hilbert／实际相干准备；原事件、Born、全菜单与全部质量；同一共同实现的真正相关联合、复合与张量；typed CP／Kraus 及整台递归参考；完整仪器、TP、条件更新与 Lüders；全部合法历史、全未来、真遗忘、真实 Return 与 CountRead；实际动力、物理钟、能量与共同正作用量。所有原准备、事件、过程、参考／副本、相关联合、零／不等／次归一质量、支持、控制、ready／flags、完整细记录、失败、拒绝、停止、销毁、中间切口和全未来权限仍逐项保留。数学向量、逆矩阵与正锥读取都不生成这些实际资源。

原分析器仍须对字面旧程序 $\tau;T_P$ 的指定接受族，在全部原准备、切口、参考／副本、允许的分析词和树、原坐标、完整菜单及固定支持全质量上，实际供应准备无关的准确接受关联，保持原支持与未归一标尺。CountRead 仍须同一接受叶的完整活动输出、实际读后活动 ready、第一合法消费者以及读后同一完整活动输入对全部合法未来的真实 Return；不以接受关联替代整仪器或全部历史恒等。

[native XI 定义 1.1–1.4](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md)仍给定其原复载体、矩阵、唯一 ready 和实际程序／保留读合同；[C139 定义 65.1](AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md)仍以实际接受输出、已供应的固定返回及真实后历史上的条件地址律为前件，不能从边缘均匀反推它。OTF8 的选定有限 CP 衰减／返回结论也仍以声明的实际 CP 端口为前件，不供应这些端口的原物理来源。具有实际输入、调用、返回与 INITIAL 消费者结论的 native GP 使用其自身原始启动装置；未证它与这里原 AURIC 来源同一，不能移作供应者。

尚未支付的是一般算子值角残量、更高演员秩、一般 $C^*$-代数中的固定 P2／全部 PB 探针分类，以及完整原分析器、CountRead 和全输入／全未来 Return 的实际来源。定理 13.1 不增加未知响应的正则性、公理或操作权限，也不降低原量子问题的全域、资源与物理合同。它是纸面有限矩阵分类，不承担 Lean kernel 认证；没有由此提出完整量子候选、完整总响应或原量子起源已完成的主张。

## 16. 中文直观说明

环境块不能取逆时，应先分清两种零方向。一种既不在环境内部起作用，也完全不连向演员；它是整个输入的共同零块，正交分开后原算子正性和全部正泛函读取都原样保留。另一种虽然在环境内部为零，却仍连向演员；这条连线不能用伪逆抹掉，正是本节保留的 $W$。

如果这样的独立连线一条也没有，就回到原来的可逆环境证明：看消元后的两个谱方向是否平衡。若恰有一条，它把演员的一个坐标钉在右端项上；与它正交的坐标仍有一个实广义特征根。实根先读掉残量的一个对角项，非实铅笔的正负虚部再读掉另一个。原残量只有两格对角数值，只有零模对这两格同样用力时，两次数值读取才允许一正一负的非零余量。这就是“零模平衡”，与无零模时的“谱平衡”承担不同角色。若有两条独立连线，两个演员坐标都已固定，正负虚部立即把全部残量压成零。

平衡秩一仍留下一个真实区间。全部非实参数通过 $k(w)$ 绕一个去掉零点的圆；行矩阵 $G$ 保留同一完整输入和原空间范数，给出正度量 $Q$。把所描圆放进二维正性允许的闭圆盘，仍是“中心距离加半径”的准确条件。圆心的符号解释了两个取向各自的非对称端点；要求两种取向时才取交集。§14.1 的虚交叉项让这种偏移可见，旧实星形则是方向项为零的已付特例。

因而少掉的只是这类已知有限环境矩阵必须可逆的数学限制。没有少掉原世界的准备、真实相关、整台仪器、全部记录失败、ready、合法后继或 Return 义务，也没有从一个矩阵区间造出实际量子来源。原 Omega 的完整量子起源目标仍未完成。

## 新增锚（本行以下为后续增补区）

## 17. 全部原探针的共同六维读取支撑

**定义 17.1（已知环境决定的原空间截面）。** 在原 Hilbert 空间 $\mathcal H=\mathbb C^2\oplus\mathcal E$、$\mathcal E=\mathbb C^m$ 上，取任意有限 $m\ge0$，并令

$$
\begin{gathered}
C_A=\operatorname{diag}(1,2),\qquad
c=C_A\oplus0_m,\qquad P=I_2\oplus0_m,\\
t=\begin{pmatrix}B&V\\V^*&D_{\rm env}\end{pmatrix}=t^*,\qquad
s=\operatorname{diag}(s_1,s_2)\oplus0_m,\qquad s_1,s_2\in\mathbb R.
\end{gathered}
\tag{17.1}
$$

$B$ 和 $D_{\rm env}$ 为任意 Hermitian 矩阵，$V$ 任意；$D_{\rm env}$ 只表示已知输入的环境块。每个 $\sigma\in\{1,-1\}$ 分别给出 $g=K_\sigma(c,t)+s$。沿用本卷 (1.1)–(1.2) 的全部原算子与乘法；以下以承载卷定义 41.1 的原符号 $S_\pm=t\pm(r+g)$ 书写本卷的同一 $V_\pm$，$R_\pm=x\pm(h-k)$、$L$ 和 $B_\phi$ 均不改变。探针始终是每个实际 $x=x^*=PxP$。对 $\xi\in\mathcal H$，记原全矩阵代数上的向量泛函为 $\phi_\xi(a)=\xi^*a\xi$，其质量为 $\|\xi\|^2$。

令 $D_{\rm env}^\dagger$ 取 §13.1 的谱定义，置

$$
\begin{gathered}
\mathcal R=\operatorname{ran}D_{\rm env},\qquad
N=\ker D_{\rm env},\qquad W=V|_N,\\
N_1=N\ominus\ker W,\qquad
\mathcal W=\operatorname{ran}W,\qquad r_0=\dim\mathcal W,\qquad
Q=\text{原 }\mathbb C^2\text{ 中到 }\mathcal W^\perp\text{ 的正交投影}.
\end{gathered}
$$

以 $\Pi_{\mathcal R}$ 表示原环境内到 $\mathcal R$ 的正交投影。定义复子空间

$$
\begin{gathered}
\mathcal K=\operatorname{ran}(\Pi_{\mathcal R}V^*)
          +\operatorname{ran}(D_{\rm env}^\dagger V^*Q)
          \subseteq\mathcal R,\\
\mathcal E_0=N_1\oplus D_{\rm env}^\dagger\mathcal K,
\qquad \mathcal H_0=\mathbb C^2\oplus\mathcal E_0
\subseteq\mathcal H.
\end{gathered}
\tag{17.2}
$$

这里的直和正交，因为 $D_{\rm env}^\dagger\mathcal K\subseteq\mathcal R=N^\perp$。令 $J:\mathcal W\to N_1$ 为同一个 $W|_{N_1}$ 的逆；零空间之间的逆取唯一的零映射。对于 $\xi=(u,y)$，置

$$
\begin{gathered}
q=D_{\rm env}y,\qquad q_0=\Pi_{\mathcal K}q,\qquad d=q-q_0,\\
y_0=D_{\rm env}^\dagger q_0+
J\bigl(Vy-VD_{\rm env}^\dagger q_0\bigr),\qquad
T\xi=(u,y_0),\qquad \delta=\|d\|^2.
\end{gathered}
\tag{17.3}
$$

下述证明同时说明 $J$ 的该次实参确实属于 $\mathcal W$。所有正交投影与范数均取原空间度量。

**定理 17.2（同一截面的精确预算等价）。** 对定义 17.1 的每份环境数据 $V,D_{\rm env}$，$\mathcal H_0$ 仅由这两者决定，且 $\dim_{\mathbb C}\mathcal H_0\le6$。映射 $T$ 良定义、复线性，值域为 $\mathcal H_0$，并在 $\mathcal H_0$ 上为恒等。它同时适用于任意 $B,s_1,s_2$、每个实际 Hermitian 角探针 $x$ 和两种分别解释的取向。

准确地，对每个原空间向量 $\xi$，写 $\eta=T\xi=(u,y_0)$，则

$$
\begin{gathered}
Vy_0=Vy,\qquad D_{\rm env}y_0=q_0,\qquad
VD_{\rm env}y_0=VD_{\rm env}y,\\
d\perp\operatorname{ran}V^*,\qquad d\perp q_0,\qquad
\|D_{\rm env}y\|^2=\|D_{\rm env}y_0\|^2+\delta.
\end{gathered}
\tag{17.4}
$$

以下均为同一原算子在两份向量泛函上的恒等式，所有平方仍在原 $M_{m+2}(\mathbb C)$ 中计算：

$$
\begin{gathered}
\phi_\xi(g)=\phi_\eta(g),\qquad
\phi_\xi(c^2)=\phi_\eta(c^2),\qquad
\phi_\xi(c\circ t)=\phi_\eta(c\circ t),\\
\phi_\xi(t^2)=\phi_\eta(t^2)+\delta,\qquad
\phi_\xi(L)=\phi_\eta(L),\\
\phi_\xi(R_\pm^2)=\phi_\eta(R_\pm^2),\qquad
\phi_\xi(R_\pm\circ S_\pm)=\phi_\eta(R_\pm\circ S_\pm),\\
\phi_\xi(S_\pm^2)=\phi_\eta(S_\pm^2)+\delta.
\end{gathered}
\tag{17.5}
$$

因此，同一个 $\delta\ge0$ 给出

$$
\begin{aligned}
B_{\phi_\xi}(c,t)
 &=B_{\phi_\eta}(c,t)+\delta\,\phi_\eta(c^2),\\
B_{\phi_\xi}(R_\pm,S_\pm)
 &=B_{\phi_\eta}(R_\pm,S_\pm)+\delta\,\phi_\eta(R_\pm^2).
\end{aligned}
\tag{17.6}
$$

对于每个给定的有限质量 $\mu\ge0$，有两条分别成立的充要关系。其中 $\phi$ 遍取完整 $M_{m+2}(\mathbb C)$ 上全部正复线性泛函，不限制环境密度块：

$$
\begin{aligned}
&\bigl[\mathsf{P2}\text{ 对全部 }\phi\ge0,\ \phi(I_{m+2})=\mu\text{ 成立}\bigr]\\
&\hspace{8mm}\Longleftrightarrow
\bigl[\mathsf{P2}\text{ 对全部 }\phi_\eta,\ \eta\in\mathcal H_0,
\ \|\eta\|^2=\mu\text{ 成立}\bigr],\\[1mm]
&\bigl[\mathsf{PB}_x\text{ 对全部 }\phi\ge0,\ \phi(I_{m+2})=\mu\text{ 成立}\bigr]\\
&\hspace{8mm}\Longleftrightarrow
\bigl[\mathsf{PB}_x\text{ 对全部 }\phi_\eta,\ \eta\in\mathcal H_0,
\ \|\eta\|^2=\mu\text{ 成立}\bigr].
\end{aligned}
\tag{17.7}
$$

第二条对每个原 $x$ 单独成立，不以 P2 为附加前件。故也可以在第二条两侧同时加上全部原 $x$ 的全称量词，并与第一条合取；无需随 $x$、$\sigma$ 或 $\mu$ 改选 $\mathcal H_0$。

证明。先构造截面。$W|_{N_1}$ 单射，且其像为 $\mathcal W$，故 $J$ 存在。因为 $D_{\rm env}$ 自伴，$\mathcal E=\mathcal R\oplus N$，$D_{\rm env}^\dagger$ 在 $\mathcal R$ 上是 $D_{\rm env}$ 的逆。$d\in\mathcal R\cap\mathcal K^\perp$，而 (17.2) 的两份像给

$$
Vd=0,\qquad QVD_{\rm env}^\dagger d=0.
\tag{17.8}
$$

第一式也说明 $d\perp\operatorname{ran}V^*$。更准确地，$\mathcal R$ 内同时被 $V$ 和 $QVD_{\rm env}^\dagger$ 消去的向量恰好组成 $\mathcal R\cap\mathcal K^\perp$；故在保持这两份线性读取的所有环境像中，$q_0$ 是唯一最小范数者。这是正交分解的直接应用。写 $y=D_{\rm env}^\dagger q+n$，$n\in N$，便有

$$
Q\bigl(Vy-VD_{\rm env}^\dagger q_0\bigr)
=QVD_{\rm env}^\dagger d+QVn=0.
$$

故 (17.3) 的 $J$ 实参在 $\ker Q=\mathcal W$ 内。其定义立即给 $Vy_0=Vy$、$D_{\rm env}y_0=q_0$；再用 (17.8)，得到 (17.4)。$q_0\perp d$ 则来自正交投影。所有映射复线性，且 $y_0\in\mathcal E_0$。若 $y\in\mathcal E_0$，则 $q\in\mathcal K$、$q_0=q$，并且 $J(Vy-VD_{\rm env}^\dagger q)$ 正好回收其 $N_1$ 分量，所以 $T$ 在 $\mathcal H_0$ 上为恒等。维数满足

$$
\dim\mathcal K\le2+(2-r_0)=4-r_0,\qquad
\dim\mathcal H_0=2+r_0+\dim\mathcal K\le6.
\tag{17.9}
$$

这些式子包含 $m=0$、$D_{\rm env}=0$ 和任意零模耦合秩；空块无需另作非零性假设。

其次验证全部原读取。写 $z=\xi-\eta=(0,y-y_0)$。由 (17.4)，$V(y-y_0)=0$，从而

$$
cz=xz=hz=rz=sz=gz=kz=0,\qquad
tz=(0,d),\qquad R_\pm z=0,\qquad S_\pm z=(0,d).
\tag{17.10}
$$

这里对 $g,k$ 的读取使用同一原矩阵的准确块形状

$$
\begin{gathered}
g=\begin{pmatrix}
\frac{\sigma i}{2}[C_A,B]+\operatorname{diag}(s_1,s_2)
 &\frac{\sigma i}{2}C_AV\\
-\frac{\sigma i}{2}V^*C_A&0
\end{pmatrix},\qquad
k=\begin{pmatrix}C_A\circ B&C_AV/2\\V^*C_A/2&0\end{pmatrix}.
\end{gathered}
\tag{17.11}
$$

$g,k$ 的环境像在 $\operatorname{ran}V^*$ 内，故 $V(y-y_0)=0$ 还给 $\phi_\xi(g)=\phi_\eta(g)$。$c\eta$ 在演员空间内；$R_\pm\eta$ 的环境分量为 $\mp V^*C_Au/2$。$t\eta$ 的环境分量为 $V^*u+q_0$，$S_\pm\eta$ 的环境分量为

$$
V^*\left(I_2\mp\frac{\sigma i}{2}C_A\right)u+q_0.
\tag{17.12}
$$

因此 (17.4) 使这些环境分量与 $d$ 全部正交。对自伴 $U,V$ 使用
$\phi_\xi(U^2)=\|U\xi\|^2$ 和 $\phi_\xi(U\circ V)=\operatorname{Re}((U\xi)^*V\xi)$，结合 (17.10)，就得到 (17.5) 中除 $L$ 外的全部恒等式，包含两份平方增加同一个 $\delta$。

对 $L$，准确使用原定义给

$$
\phi_\xi(L)=-2\operatorname{Re}\bigl((x\xi)^*(h-k)\xi\bigr)
             -2\operatorname{Re}\bigl((t\xi)^*(r+g)\xi\bigr).
\tag{17.13}
$$

第一项在 $\xi,\eta$ 之间完全相同。第二项的差仅为
$-2\operatorname{Re}((0,d)^*(r+g)\eta)$，而 $(r+g)\eta$ 的环境分量为 $-\sigma iV^*C_Au/2$，故差也为零。这证明完整 (17.5)，代入原标量 $B_\phi$ 即得 (17.6)。所有恒等式对同一个 $\eta,d$ 同时成立，并未为两份符号、两个面积根或不同探针分别优化。

最后证明质量与全正泛函的等价。$\mu=0$ 时，正泛函的有限维谱分解使它只能为零，右侧向量也只能为零，两条关系均成立。以下固定 $\mu>0$。原 P2 关于正泛函的正倍数是二次齐次的，原 PB 的两边是一次齐次的；因 $\phi_{a\eta}=a^2\phi_\eta$ 对每个实 $a>0$ 成立，某条预算在 $\mathcal H_0$ 上所有质量 $\mu$ 的向量成立，就在 $\mathcal H_0$ 上所有向量成立。这里也包含零向量，并不要求 $T$ 保持范数或质量。

现在取任意原空间向量 $\xi$。P2 的左端由 (17.5) 不变，右端由 (17.6) 只增加非负量 $\delta\phi_\eta(c^2)$，所以支撑上的 P2 推出全部原向量上的 P2。同理，PB 的左端不变，每个根内量都增加非负量 $\delta\phi_\eta(R_\pm^2)$，故对固定 $x$ 的支撑预算推出同一 $x$ 在全部原向量上的预算。没有把失败的充分估计解释成预算失败；这里使用的是已证的单向单调性。

还须将全部原向量结论提升到全部原正泛函。任意 $\phi\ge0$ 在完整 $M_{m+2}(\mathbb C)$ 上有有限谱分解

$$
\phi=\sum_j\phi_{\xi_j},\qquad
\sum_j\|\xi_j\|^2=\phi(I_{m+2}).
\tag{17.14}
$$

这里的 $\xi_j$ 是完整原空间向量，没有去掉环境密度块。对于 P2，全部向量预算准确等价于每个 Hermitian 二阶矩阵

$$
M_{\phi_{\xi_j}}=
\begin{pmatrix}
\phi_{\xi_j}(c^2)&\phi_{\xi_j}(c\circ t)-i\phi_{\xi_j}(g)\\
\phi_{\xi_j}(c\circ t)+i\phi_{\xi_j}(g)&\phi_{\xi_j}(t^2)
\end{pmatrix}
$$

为正：对角元本来非负，行列式正好是 P2 的余量。这是 §2 的既有二表写法。矩阵对泛函线性，故 $M_\phi=\sum_jM_{\phi_{\xi_j}}\ge0$，其行列式给 $\phi$ 的 P2，包括零对角和退化情形。

对于 PB，直接使用[运输卷](https://github.com/the-omega-institute/trureturing/blob/caf0f3b3064a987b753b67aaa3836d6d86e73f75/docs/develop/theory/AURIC_INTERVAL_ORIGINAL_RESPONSE_AND_VARIABLE_PROJECTION_TRANSPORT.md)式 (9.28)–(9.30) 的成熟二阶正 Gram 行列式根不等式：对任意实际自伴 $U,V$，

$$
\sqrt{B_\phi(U,V)}\ge\sum_j\sqrt{B_{\phi_{\xi_j}}(U,V)}.
\tag{17.15}
$$

该工具只用二阶矩阵相加，与谱分解的项数无关。将它分别用于同一原 $R_+,S_+$ 与 $R_-,S_-$，便有

$$
\begin{aligned}
|\phi(L)|
&\le\sum_j|\phi_{\xi_j}(L)|\\
&\le\sum_j\left(\sqrt{B_{\phi_{\xi_j}}(R_+,S_+)}
                 +\sqrt{B_{\phi_{\xi_j}}(R_-,S_-)}\right)\\
&\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\end{aligned}
\tag{17.16}
$$

取 (17.14) 的总质量为给定 $\mu$，即得 (17.7) 的两个反向蕴涵；正向蕴涵只用每个 $\phi_\eta$ 本身就是质量 $\mu$ 的原全空间正复线性泛函。两条证明分别使用自己的预算，没有相互增加前件。$T$ 的定义与任何探针和取向无关，故最后的同时量词断言也成立。∎

## 18. 原平方与压缩平方的严格区别

**命题 18.1（读取支撑可以不约化原输入）。** 定理 17.2 的 $\mathcal H_0$ 不必是 $t$ 的不变子空间。令 $\Pi_0$ 为原空间到它的正交投影，$t_0=\Pi_0t|_{\mathcal H_0}$；即使对 $\eta\in\mathcal H_0$，也不总有 $\phi_\eta(t^2)=\eta^*t_0^2\eta$。

证明。取 $m=3$、$B=0$、$s=0$，并置

$$
D_{\rm env}=\operatorname{diag}(1,2,3),\qquad
V=\begin{pmatrix}1&1&1\\0&0&0\end{pmatrix},\qquad
v=(1,1,1)^{\mathsf T}.
\tag{18.1}
$$

此时 $N_1=0$、$Q=I_2$，故定义 17.1 的环境支撑准确为

$$
\mathcal E_0=\operatorname{span}_{\mathbb C}
\left\{(1,1/2,1/3)^{\mathsf T},(1,1/4,1/9)^{\mathsf T}\right\}.
\tag{18.2}
$$

若 $v$ 是这两列以系数 $a,b$ 的组合，前两坐标给 $a+b=1$、$2a+b=4$，所以 $a=3,b=-2$；第三坐标却给 $a/3+b/9=7/9\ne1$。因此 $v\notin\mathcal E_0$。取原演员向量 $\eta=(e_1,0)\in\mathcal H_0$，则 $t\eta=(0,v)\notin\mathcal H_0$，并且

$$
\phi_\eta(t^2)=\|v\|^2=3
>\|\Pi_{\mathcal E_0}v\|^2
=\eta^*t_0^2\eta.
\tag{18.3}
$$

一般的差准确是成熟的正交投影恒等式

$$
\Pi_0t^2|_{\mathcal H_0}-t_0^2
=\Pi_0t(I-\Pi_0)t|_{\mathcal H_0}\ge0.
\tag{18.4}
$$

本例使它在 $\eta$ 上严格正。因此 (17.7) 检验的是原全矩阵算子的原平方与原 Jordan 乘积，只缩小向量的读取范围。将 $t$ 换成 $t_0$ 再在小矩阵代数中作平方会改变这些预算的输入；定理 17.2 不提供这一步等价，也不能据此直接套用旧的小矩阵分类。∎

**约定 18.2（分类范围与承重归属）。** 定理 17.2 是 (17.1) 整个有限输入类的共同读取支撑结论，既未断言全部原 PB 消去每个非零 $s$，也未给任何非零 $s$ 的全 PB 证书。关于固定 P2，直接复用本卷定理 13.1：$\operatorname{rank}(V|_{\ker D_{\rm env}})=2$ 或不平衡秩一时已经有 $s=0$；余下只有平衡秩一与秩零的 Schur 平衡非零区间。秩零的阈值继续由定理 8.1 支付，不重新计为定理 17.2 的内容。

旧移位实星形的全部实参数已由上述固定提交的运输卷定理 12.3 精确分类；零移位星形和零演员对角、无角外连线类分别复用[承载卷](https://github.com/the-omega-institute/trureturing/blob/caf0f3b3064a987b753b67aaa3836d6d86e73f75/docs/develop/theory/AURIC_FULL_PB_POLYNOMIAL_TRANSPORT_AND_REAL_ROOT_RIGIDITY.md)定理 42.2、41.2。$s=0$ 的原预算充分性直接复用本卷 §1。已知有限维完整 $\mathsf H_A(D)$ 分类及[双角卷](https://github.com/the-omega-institute/trureturing/blob/caf0f3b3064a987b753b67aaa3836d6d86e73f75/docs/develop/theory/AURIC_FULL_PB_TWO_CORNER_POSITIVE_CERTIFICATE_CONTINUATION.md)定理 44.2 要求其各自更强前件，不是 (17.7) 的固定输出分类。平衡秩一和 Schur 平衡秩零中，除上述准确已付子类以外，全部原 PB 与非零残量区间的交仍待判定；定理 17.2 只把它等价地放到同一个原六维以内读取支撑上。

(17.3) 的最小范数步骤是在环境像 $q=D_{\rm env}y$ 中保持线性读取后作正交投影，不是保持 $\|y\|$ 的断言。它使用成熟的最小范数插值／representer 原理，背景见 Argyriou–Micchelli–Pontil，[*When Is There a Representer Theorem? Vector Versus Matrix Regularizers*](https://jmlr.org/papers/v10/argyriou09a.html)，JMLR 10 (2009), 2507–2529，§§1–3；这里只使用复有限维正交分解，并已在证明中建立所需性质，不调用该文关于一般正则项的刻画。Moore–Penrose 逆沿 §15 的 Penrose 引文；正 Gram、谱分解和行列式根工具沿本卷及运输卷的既有归属。这些成熟工具不单列为新增数学定理。新的 repo-derived 综合是 (17.2) 同时保留两份环境线性读取、(17.5)–(17.6) 同一非负余项对全部原探针的恒等式，以及据此得到的逐质量、逐预算全正泛函等价；不作历史优先权或文献穷尽主张。

此处只讨论已知矩阵和原数学泛函，不给未知总响应 $D$ 添加正则性、可加性、齐次性、协变性、单位平移中性、压缩或商自然性，也不增加实际准备或读取标签。运输卷 (12.29) 的一般共同实现义务 $\mathcal E_+^D=\mathcal E_-^D$、一般稳定性目标 $N_\omega(\varepsilon)^2\to0$、完整原 $\mathsf H$ 与总 $D$，以及本卷 §§6、15 的同一递归钉版实际物理来源全文均保持原范围。它们不是有限读取支撑的结论。

## 新增锚（本行以下为后续增补区）


## 19. 平衡零模族的原零探针刚性

本节与 §20 准确沿用承载卷在 `caf0f3b3064a987b753b67aaa3836d6d86e73f75` 的定义 41.1，以及本卷 (1.1)–(1.2)。记 $S_\pm=t\pm(r+g_\sigma)$，即 (1.2) 中的同一 $V_\pm$；不改变任何读取标签。始终取

$$
C=\operatorname{diag}(1,2),\quad c=C\oplus0_m,\quad P=I_2\oplus0_m,
\quad t=\begin{pmatrix}B&V\\V^*&D_{\rm env}\end{pmatrix}=t^*,
\quad g_\sigma=\frac{\sigma i}{2}[c,t]+s,
\quad\sigma\in\{1,-1\}.
\tag{19.1}
$$

$D_{\rm env}$ 是已知有限 Hermitian 环境矩阵。全部正泛函仍是完整 $M_{m+2}(\mathbb C)$ 上的全部正复线性泛函，包含零泛函与任意有限质量。对原空间向量 $\xi$，使用 $\phi_\xi(A)=\xi^*A\xi$；因此
$\phi_\xi(A^2)=\|A\xi\|^2$、$\phi_\xi(A\circ B)=\operatorname{Re}((A\xi)^*B\xi)$，所有乘积均取原完整矩阵乘法。实 Gram 的这些恒等式及正泛函背景沿 §§1、5、11 的成熟归属；本节的增量是下述特定输入的显式共同见证，不另立通用 Gram 定理。

**定理 19.1（平衡秩一族的零探针刚性与继承区间）。** 设 $m\ge1$，

$$
\begin{gathered}
v=(1,\sqrt2)^{\mathsf T},\qquad
U=\operatorname{diag}(\zeta_1,\zeta_2),\quad |\zeta_j|=1,\qquad
V=Uv\ell^*,\qquad P_{\ker D_{\rm env}}\ell\ne0,\\
B=U\begin{pmatrix}a&z\\\bar z&d\end{pmatrix}U^*,\qquad
 a,d\in\mathbb R,\quad z\in\mathbb C,\qquad
 d=3\sqrt2\operatorname{Re}z-4a,\qquad
 \delta=2a-\sqrt2\operatorname{Re}z\ne0.
\end{gathered}
\tag{19.2}
$$

对任意实对角角残量 $s=\operatorname{diag}(s_1,s_2)\oplus0_m$，固定 P2 的准确条件直接由定理 13.1 给出：

$$
\begin{gathered}
s=\rho\operatorname{diag}(1,-2)\oplus0_m,\qquad \rho\in\mathbb R,\\
\alpha=\|P_{\ker D_{\rm env}}\ell\|>0,\qquad
\gamma=\sqrt2\alpha,\qquad
\mathfrak b=\frac34\delta+\frac{i\operatorname{Im}z}{\sqrt2},\qquad
K=\sqrt{|\mathfrak b|^2+\frac34\gamma^2},\\
-\frac{\gamma^2}{2(K+\sigma\operatorname{Im}\mathfrak b)}
\le\rho\le
\frac{\gamma^2}{2(K-\sigma\operatorname{Im}\mathfrak b)}.
\end{gathered}
\tag{19.3}
$$

若要求两个取向，两个准确区间的交集为

$$
 |\rho|\le\frac{\gamma^2}{2(K+|\operatorname{Im}\mathfrak b|)}.
\tag{19.4}
$$

对每个分别固定的 $\sigma$，全部原 P2 与原 $x=0$ PB 同时成立，当且仅当 $s=0$。更具体地，对任意 $\rho\ne0$，下述同一个有限原空间向量使原零探针的两笔 Gram 预算同时为零，而其左端严格正；不要求 $\rho$ 先属于 (19.3)。

证明。先准确代入定理 13.1，不重证其分类。令

$$
q=\alpha^{-1}P_{\ker D_{\rm env}}\ell,\qquad
n=U(1,1)^{\mathsf T}/\sqrt2,\qquad
e=U(1,-1)^{\mathsf T}/\sqrt2.
\tag{19.5}
$$

$q$ 为单位向量，$D_{\rm env}q=0$、$\ell^*q=\alpha$，而
$C^{-1/2}Vq=\gamma n$，故零模耦合秩为一且平衡。归一化 Schur 矩阵中，被减去的项为
$(\ell^*D_{\rm env}^\dagger\ell)U(1,1)^{\mathsf T}(1,1)U^*$；其 $e,n$ 条目为零。因此 (13.5) 的 $b$ 准确为

$$
e^*C^{-1/2}(B-VD_{\rm env}^\dagger V^*)C^{-1/2}n
=\frac{a-d/2}{2}+\frac{i\operatorname{Im}z}{\sqrt2}
=\mathfrak b.
\tag{19.6}
$$

在 (13.6) 的同一个原行空间中，$e^*C^{-1/2}V=0$，所以

$$
L=[e^*C^{-1/2},0],\qquad j=\gamma^{-1}[0,q^*],\qquad
G=\begin{bmatrix}L-\mathfrak b j\\j\end{bmatrix},\qquad
GG^*=\begin{pmatrix}
3/4+|\mathfrak b|^2/\gamma^2&-\mathfrak b/\gamma^2\\
-\overline{\mathfrak b}/\gamma^2&1/\gamma^2
\end{pmatrix}.
\tag{19.7}
$$

其逆及定理 13.1 的标量准确为

$$
\begin{gathered}
Q=\begin{pmatrix}4/3&4\mathfrak b/3\\
4\overline{\mathfrak b}/3&\gamma^2+4|\mathfrak b|^2/3\end{pmatrix},\qquad
R=4K/3,\quad \Delta=4\gamma^2/3,\quad
\omega=e^*\operatorname{diag}(1,-1)n=1,\quad
J=-4\operatorname{Im}\mathfrak b/3.
\end{gathered}
\tag{19.8}
$$

将它们直接代入 (13.9) 和 (13.10)，得到 (19.3) 和 (19.4)，包括全部闭端点及原质量。$K>|\operatorname{Im}\mathfrak b|$，所以分母严格正；两个区间都包含非零内点。这里保留了实际耦合幅度 $\gamma$ 及取向 $\sigma$。

现在给出原零探针的向量。置

$$
u_0=(-2\sqrt2,1)^{\mathsf T},\qquad
w=4\sqrt2a-3z,\qquad y=(w/\alpha)q,\qquad
\xi=(Uu_0,y)\in\mathbb C^2\oplus\mathbb C^m.
\tag{19.9}
$$

此处的 $u_0$ 是上述列向量；$U$ 保留在原演员坐标中。$\ell^*y=w$、$D_{\rm env}y=0$。直接用原 $k=c\circ t$ 的三个块行，得到

$$
\begin{aligned}
U^*(k\xi)_{\rm actor}
&=\binom{-2\sqrt2a+3z/2+w/2}
{-3\sqrt2\bar z+2d+\sqrt2w}=\binom00,\\
(k\xi)_{\rm env}
&=\tfrac12\ell\,v^*Cu_0=0.
\end{aligned}
\tag{19.10}
$$

第二演员行使用的准确关系是
$2d+8a-3\sqrt2(z+\bar z)=0$。令 $\nu=\operatorname{Im}z$，则同一向量还满足

$$
T=\binom{\sqrt2\delta-2i\nu}{2\delta-i\sqrt2\nu},\qquad
 t\xi=(UT,-\sqrt2\ell).
\tag{19.11}
$$

由 $k\xi=0$，有 $tc\xi=-ct\xi$，故对于任意实 $\rho$，

$$
Z=\operatorname{diag}(1,-1),\qquad
 g_\sigma\xi=(U(\sigma iCT+\rho CZu_0),0_m),\qquad
 CZu_0=(-2\sqrt2,-2)^{\mathsf T}.
\tag{19.12}
$$

取实际 $x=0$，则 $h=r=0$。两对完整原标签在这一个向量上的作用分别为

$$
\begin{gathered}
R_+\xi=-k\xi=0,\qquad R_-\xi=k\xi=0,\\
S_\pm\xi=
\bigl(U[T\pm(\sigma iCT+\rho CZu_0)],-\sqrt2\ell\bigr).
\end{gathered}
\tag{19.13}
$$

因此 $B_{\phi_\xi}(R_+,S_+)=B_{\phi_\xi}(R_-,S_-)=0$。这里两个 $S$ 的环境分量仍是原来的 $-\sqrt2\ell$；零预算来自 $R_\pm\xi=0$，不是删除环境平方。另一方面，$T^*CT$ 为实数，且

$$
\operatorname{Re}(T^*CZu_0)=-8\delta,\qquad
\phi_\xi(L)=-2\operatorname{Re}((t\xi)^*g_\sigma\xi)
=16\rho\delta.
\tag{19.14}
$$

这对两种 $\sigma$ 分别成立。$\|\xi\|^2=9+|w|^2/\alpha^2>0$，所有条目均有限；故 $\rho\delta\ne0$ 时左端为 $16|\rho\delta|>0$，两笔预算之和为零。任取质量 $\mu>0$，再用 $\sqrt\mu\xi/\|\xi\|$，两笔预算仍为零，左端为 $16\mu|\rho\delta|/\|\xi\|^2$。零泛函本身满足零等式。

于是 P2 先给 (19.3) 的残量形状，而原零探针排除其中全部非零 $\rho$。$s=0$ 时的 P2 与全部实际角探针 PB 直接复用 §1 的标准零残量结果。这证明充要结论。∎

## 20. 第一角无环境连线时的实际探针

**定理 20.1（解耦第一角的有限探针排除）。** 在 (19.1) 的完整原空间中，允许任意有限 $m\ge0$，并设

$$
V^*e_1=0,\qquad a=B_{11},\qquad b=B_{12},\qquad
s=\rho\operatorname{diag}(1,-2)\oplus0_m,\qquad
 a\rho\ne0,\qquad a^2\le\tfrac52\rho^2.
\tag{20.1}
$$

对每个分别固定的 $\sigma$，以下实际有限 Hermitian 角探针和原向量 $\xi=e_1\oplus0_m$ 联合严格违反 PB：

$$
\begin{gathered}
\tau=\sqrt{\tfrac52\rho^2-a^2},\qquad
u=\rho+\operatorname{sgn}(\rho)\tau,\qquad
p_\sigma=1+\sigma i/2,\\
A_+=(u-a)p_\sigma+\tfrac32(u+a+\rho),\qquad
B_+=\tfrac32(u-a)-p_\sigma(u+a+\rho),\qquad
\eta=-A_+/B_+,\\
x=\begin{pmatrix}u&\bar\eta b\\\eta\bar b&0\end{pmatrix}\oplus0_m.
\end{gathered}
\tag{20.2}
$$

式中的 $u$ 为上述实数。该结论不要求 P2，不限制 $b,B_{22},D_{\rm env}$ 或第二演员的环境连线。

证明。$u$ 与 $\rho$ 同号，且

$$
 (u-\rho)^2+a^2-\tfrac52\rho^2=0.
\tag{20.3}
$$

若 $B_+=0$，其虚部给 $u+a+\rho=0$，再由实部得 $u=a$，从而 $\rho=-2a$。这与 $u$、$\rho$ 同号矛盾。因此 $\eta$ 定义良好，$x=x^*=PxP$ 且有限。

由 $V^*e_1=0$，下列均为完整原算子在同一 $\xi$ 上的作用，所有环境分量恰为零：

$$
\begin{gathered}
t\xi=(a,\bar b,0_m),\quad
k\xi=(a,\tfrac32\bar b,0_m),\quad
g_\sigma\xi=(\rho,\tfrac{\sigma i}{2}\bar b,0_m),\\
x\xi=(u,\eta\bar b,0_m),\quad
h\xi=(0,\tfrac{\sigma i}{2}\eta\bar b,0_m),\quad
r\xi=(u,\tfrac32\eta\bar b,0_m).
\end{gathered}
\tag{20.4}
$$

特别地，两对完整原标签为

$$
\begin{aligned}
R_+\xi&=(u-a,(p_\sigma\eta-3/2)\bar b,0_m),\\
S_+\xi&=(u+a+\rho,(p_\sigma+3\eta/2)\bar b,0_m),\\
R_-\xi&=(u+a,(\bar p_\sigma\eta+3/2)\bar b,0_m),\\
S_-\xi&=(a-u-\rho,(\bar p_\sigma-3\eta/2)\bar b,0_m).
\end{aligned}
\tag{20.5}
$$

为同时证明两笔实 Gram 为零，定义剩下的两个明确系数

$$
A_-=(u+a)\bar p_\sigma-\tfrac32(a-u-\rho),\qquad
B_-=-\tfrac32(u+a)-\bar p_\sigma(a-u-\rho).
\tag{20.6}
$$

每一对 (20.5) 的前两坐标行列式分别是
$(A_++\eta B_+)\bar b$ 与 $(A_-+\eta B_-)\bar b$。第一个由定义为零。四个系数的完整实虚部分为

$$
\begin{aligned}
2A_+&=5u+a+3\rho+\sigma i(u-a),\\
2B_+&=u-5a-2\rho-\sigma i(u+a+\rho),\\
2A_-&=5u-a+3\rho-\sigma i(u+a),\\
2B_-&=-u-5a+2\rho+\sigma i(a-u-\rho).
\end{aligned}
\tag{20.7}
$$

相乘相减，虚部相消，实部给

$$
A_+B_--A_-B_+
=-2u^2+4\rho u+3\rho^2-2a^2
=-2\bigl((u-\rho)^2+a^2-\tfrac52\rho^2\bigr)=0.
\tag{20.8}
$$

故 $A_-+\eta B_-=(A_-B_+-A_+B_-)/B_+=0$。这同时处理 $\tau=0$ 的边界，不使用严格不等号。

第一对的两个实首坐标不能同时为零，否则 $u=a,\rho=-2a$；第二对也不能同时为零，否则 $u=-a,\rho=2a$。两者均与 $u$、$\rho$ 同号矛盾。因此在每一对中，至少有一个非零实首坐标；行列式为零遂保证两个完整作用向量是实比例，而不仅是复比例。于是

$$
 B_{\phi_\xi}(R_+,S_+)=B_{\phi_\xi}(R_-,S_-)=0.
\tag{20.9}
$$

最后，不改变向量或探针，由 (20.4) 得

$$
\begin{aligned}
\operatorname{Re}((x\xi)^*(h-k)\xi)
 &=-au-\tfrac32|b|^2\operatorname{Re}\eta,\\
\operatorname{Re}((t\xi)^*(r+g_\sigma)\xi)
 &=a(u+\rho)+\tfrac32|b|^2\operatorname{Re}\eta,\\
\phi_\xi(L)&=-2a\rho.
\end{aligned}
\tag{20.10}
$$

PB 左端为 $2|a\rho|>0$，右端由 (20.9) 为零，故严格失败。$\xi$ 的质量为一；用 $\sqrt\mu\xi$ 可在任意给定有限质量 $\mu>0$ 得同一严格违反。$B_{22}$ 与环境块未出现在这些原作用列中，是 $V^*e_1=0$ 的准确结果，不是对原输入作 Schur 替换或压缩平方。∎

**命题 20.2（全正 P2 相容而被实际探针排除的同一实现）。** 取

$$
\begin{gathered}
m=1,\qquad D_{\rm env}=(1),\qquad V=(0,1)^{\mathsf T},\qquad
B=\begin{pmatrix}\rho/2&1\\1&\rho+1\end{pmatrix},\\
s=\rho\operatorname{diag}(1,-2,0),\qquad
0<|\rho|\le1/\sqrt2.
\end{gathered}
\tag{20.11}
$$

对两种分别解释的 $\sigma$，该完整 $M_3(\mathbb C)$ 实现满足全部原正泛函的固定 P2，而下述同一实现的有限原探针与原向量严格违反 PB：

$$
x_\sigma=\begin{pmatrix}5\rho/2&2+3\sigma i&0\\
2-3\sigma i&0&0\\0&0&0\end{pmatrix},\qquad
\xi=(1,0,0)^{\mathsf T}.
\tag{20.12}
$$

证明。P2 直接复用定理 8.1。其参数为

$$
H=B-VV^*=\begin{pmatrix}\rho/2&1\\1&\rho\end{pmatrix},\qquad
C^{-1/2}HC^{-1/2}
=\begin{pmatrix}\rho/2&1/\sqrt2\\1/\sqrt2&\rho/2\end{pmatrix},
\qquad \beta=1/\sqrt2.
\tag{20.13}
$$

取其有序正交谱基 $U_0$，则原度量给

$$
GG^*=U_0^*C^{-1/2}(I_2+VV^*)C^{-1/2}U_0=I_2,
\quad Q=I_2,\quad R=\Delta=1,\quad h=J=0.
\tag{20.14}
$$

故 (8.2) 准确成为 $|\rho|\le\beta=1/\sqrt2$，包含端点；这已是对原全部正复线性泛函、零泛函和任意有限质量的充要证书，不以选定向量读取替代 P2 的全称量词。

对该同一输入，$a=\rho/2$、$b=1$，定理 20.1 的 $\tau=3|\rho|/2$、$u=5\rho/2$、$\eta=2-3\sigma i$，正好得到 (20.12)。其两对完整原作用列明确为

$$
\begin{aligned}
R_+\xi&=(2\rho,2-2\sigma i,0)^{\mathsf T},&
S_+\xi&=2R_+\xi,\\
R_-\xi&=(3\rho,2-4\sigma i,0)^{\mathsf T},&
S_-\xi&=-R_-\xi.
\end{aligned}
\tag{20.15}
$$

所以两笔 Gram 预算均为零，而 (20.10) 给
$|\phi_\xi(L)|=\rho^2>0$。环境矩阵 $1$、连线 $V$、两个演员对角条目及全部原标签均保持 (20.11) 的实际值。∎

## 21. 有限排除域与未决边界

定理 19.1 的覆盖域准确是 (19.2)，其固定 P2 形状和锐区间复用 ENV13.1；新增的 repo-derived 推断是 (19.9)–(19.14) 的原零探针见证。定理 20.1 的覆盖域准确是 (20.1)，其新增推断是 (20.2)–(20.10) 的同一有限探针、向量及两笔零预算；命题 20.2 在同一实现上结合 ENV8.1 的既有 P2 证书。它们不重证 ENV8.1、ENV13.1、ENV17.2、ENV18.1、既有实星形区间、F41.2、F42.2 或标准零残量 PB，也不从六维共同读取支撑推出普通 $M_6$ 分类。有限矩阵乘法、实 Gram 与二次方程在上述证明中只作为成熟工具；不主张历史优先权或文献穷尽。

平衡秩一中不属于 (19.2) 的输入、包括该等式族中 $\delta=0$ 的情形，尚未由这里的零探针见证排除。Schur 平衡秩零中不属于 (20.1) 的非零残量也尚未由这里的探针构造排除。定理 20.1 对任意已知有限 Hermitian 环境成立，但未声称其域之外存在全部 PB 相容残量；上述有限排除域不构成整个有限类的分类，也没有给出任何全 PB 反例。

原一般混合输入的 $E_+^D=E_-^D$、$N_\omega(\varepsilon)^2\to0$、一般完整 $\mathsf H$／总响应 $D$、全部递归钉版实际物理来源，以及 §§6、15、18 的原全域和资源义务仍保持原范围。上述数学向量和探针不供应任何未知总响应的正则性、输入可加性、齐次性、协变性、单位平移中性、压缩或商自然性，也不生成原物理准备与过程。

## 新增锚（本行以下为后续增补区）

## 22. 原环境平面上的面积下界与满行秩接触

**定义 22.1（原预算差额与共同接触）。** 沿用定义 17.1 的完整有限矩阵输入、(1.1)–(1.2) 及承载卷[§41.1](https://github.com/the-omega-institute/trureturing/blob/caf0f3b3064a987b753b67aaa3836d6d86e73f75/docs/develop/theory/AURIC_FULL_PB_POLYNOMIAL_TRANSPORT_AND_REAL_ROOT_RIGIDITY.md#411-原完整问题与较弱的固定输出接口)。特别地，$C=\operatorname{diag}(1,2)$，$c=C\oplus0_m$，$P=I_2\oplus0_m$，$D_{\rm env}$ 是给定 $t$ 的任意有限 Hermitian 环境块。每个取向 $\sigma$ 分别解释，$S_\pm$ 仍为原 $t\pm(r+g_\sigma)$。对同一个实际 $x=x^*=PxP$ 和同一个正复线性泛函 $\phi$，定义

$$
\begin{gathered}
\mathcal A_\pm(x,\phi)=\sqrt{B_\phi(R_\pm,S_\pm)},\qquad
\mathcal G_\sigma(x,\phi)=|\phi(L)|-\mathcal A_+(x,\phi)-\mathcal A_-(x,\phi),\\
\mathcal Z_\sigma(x)=\{\phi\ge0:\mathcal A_+(x,\phi)=\mathcal A_-(x,\phi)=0\}.
\end{gathered}
\tag{22.1}
$$

称 $\mathcal Z_\sigma(x)$ 中的泛函为该探针的共同零预算接触。任意正泛函唯一写成 $\phi(A)=\operatorname{Tr}(\Theta A)$，$\Theta\ge0$；其支撑为 $\operatorname{ran}\Theta$，质量为 $\operatorname{Tr}\Theta$。零密度及任意有限质量均保留。

这里的 $B_\phi$ 使用未中心化的原二阶矩。对质量 $\mu>0$，中心化方差另为 $\phi(A^2)/\mu-(\phi(A)/\mu)^2$。[Tóth–Fröwis, arXiv:2109.06893v5, §§II、IV](https://arxiv.org/html/2109.06893v5) 的 Robertson–Schrödinger 与密度分解讨论，以及 [Szymański–Życzkowski, arXiv:1804.06191v2, §§2–4](https://arxiv.org/html/1804.06191v2) 的方差联合范围，均使用其各自的中心化量；这些量不替换 (22.1) 的原预算。以下只在推导内部使用成熟的实 Gram、Cauchy–Schwarz、正交投影与有限正密度谱分解；混合泛函的共同提升直接引用本卷 (17.14)–(17.15)。

**定理 22.2（全部实际探针的环境面积底界）。** 对定义 22.1 的每份输入、每个实际 $x$ 和全部原正泛函，有

$$
\boxed{\mathcal A_+(x,\phi)+\mathcal A_-(x,\phi)
\ \ge\ \tfrac12\phi\bigl(ct(1-P)tc\bigr).}
\tag{22.2}
$$

不要求 P2，亦不要求 $s=\rho\operatorname{diag}(1,-2)\oplus0_m$；定义 17.1 的任意实对角残量均允许。

证明。先取同一个原向量 $\xi=(u,y)$，置

$$
w=V^*Cu,\qquad d=V^*u+D_{\rm env}y.
\tag{22.3}
$$

由原块矩阵 (17.11)–(17.12)，两对作用向量的环境部分准确为

$$
(R_\pm\xi)_{\rm env}=\mp w/2,\qquad
(S_\pm\xi)_{\rm env}=d\mp\sigma i w/2.
\tag{22.4}
$$

$w=0$ 时 (22.2) 的向量版本只是 Gram 非负性。设 $w\ne0$，在原复 Hilbert 空间的实化中取正交单位向量

$$
e=(0,w)/\|w\|,\qquad f=(0,iw)/\|w\|,
\qquad (a,b)_{\mathbb R}=\operatorname{Re}(a^*b).
$$

任意两向量的实 Gram 面积不小于其在 $\operatorname{span}_{\mathbb R}\{e,f\}$ 上的有向面积绝对值。具体地，第一向量 $a\ne0$ 时，把第二向量写成 $b=\lambda a+b_\perp$，$\lambda\in\mathbb R$、$b_\perp\perp_{\mathbb R}a$。投影行列式中的 $\lambda a$ 消去，二维 Cauchy–Schwarz 将其绝对值控制为 $\|a\|\|b_\perp\|$，正好是原实 Gram 面积；$a=0$ 时两者均为零。这一步只投影作用向量以取得下界，没有替换原算子的平方。

用 (22.4) 计算这个有向面积，得到

$$
\begin{aligned}
\mathcal A_+(x,\phi_\xi)
&\ge\frac12\left|\operatorname{Im}(w^*d)-\frac{\sigma}{2}\|w\|^2\right|,\\
\mathcal A_-(x,\phi_\xi)
&\ge\frac12\left|\operatorname{Im}(w^*d)+\frac{\sigma}{2}\|w\|^2\right|.
\end{aligned}
\tag{22.5}
$$

两式中的 $d,w$ 来自同一个 $\xi$。实数三角不等式给两右端之和至少为 $\|w\|^2/2$，而

$$
\phi_\xi\bigl(ct(1-P)tc\bigr)=\|(1-P)tc\xi\|^2=\|V^*Cu\|^2.
\tag{22.6}
$$

这证明全部原向量的断言。

对任意 $\phi=\sum_j\phi_{\xi_j}$，直接使用 (17.15)，分别在两笔原预算中对同一谱分解求和：

$$
\mathcal A_+(x,\phi)+\mathcal A_-(x,\phi)
\ge\sum_j\bigl(\mathcal A_+(x,\phi_{\xi_j})+\mathcal A_-(x,\phi_{\xi_j})\bigr)
\ge\tfrac12\sum_j\phi_{\xi_j}\bigl(ct(1-P)tc\bigr).
$$

最后一和是 (22.2) 的右端。空谱分解处理零泛函，未除以任何质量。∎

**定理 22.3（总耦合满行秩时的共同零预算穷尽）。** 在定理 22.2 的输入中，若实际 $\operatorname{rank}V=2$，则对每个实际 $x$，

$$
\begin{aligned}
\phi_\xi\in\mathcal Z_\sigma(x)
&\ \Longleftrightarrow\ \xi=(0,y),\quad Vy=0,\\
\phi\in\mathcal Z_\sigma(x)
&\ \Longleftrightarrow\ \operatorname{ran}\Theta\subseteq0\oplus\ker V.
\end{aligned}
\tag{22.7}
$$

每个这样的正泛函均满足 $\phi(L)=0$。$\ker V$ 中的环境向量不必在 $\ker D_{\rm env}$ 中。

证明。若向量两笔预算均为零，(22.2) 给 $V^*Cu=0$。$V^*$ 单射且 $C$ 可逆，故 $u=0$。记 $z=Vy$，原作用列此时为

$$
R_\pm\xi=(\mp Cz/2,0),\qquad
S_\pm\xi=((I_2\pm\sigma iC/2)z,D_{\rm env}y).
\tag{22.8}
$$

复 Cauchy–Schwarz 给任意作用列 $a,b$ 的实 Gram 不小于 $|\operatorname{Im}(a^*b)|^2$。在 (22.8) 中，$z^*Cz$ 为实数，且

$$
\left|\operatorname{Im}\bigl((R_\pm\xi)^*S_\pm\xi\bigr)\right|
=\|Cz\|^2/4.
\tag{22.9}
$$

零预算遂强制 $z=0$。反向地，$u=0,Vy=0$ 时 $x\xi=h\xi=r\xi=k\xi=g_\sigma\xi=0$，两份 $R$ 均消去 $\xi$，而 $S_\pm\xi=(0,D_{\rm env}y)$。故两预算为零，且原 (17.13) 给 $\phi_\xi(L)=0$。

一般正密度取 (17.14) 的谱分解。若两笔总预算为零，(17.15) 及各项非负性使每个谱向量也有两笔零预算，刚证的向量结论给出支撑包含关系。若支撑包含于 $0\oplus\ker V$，则 $R_\pm$ 消去支撑，故 $\phi(R_\pm^2)=0$，两笔预算为零；向量结论相加还给 $\phi(L)=0$。∎

## 23. 总秩一平衡零模的全部共同接触

**定理 23.1（接触超平面、全部探针与正密度）。** 取 §19 的实际耦合形状，但不预设其接触超平面或 $\delta\ne0$：

$$
\begin{gathered}
V=Uv\ell^*,\quad v=(1,\sqrt2)^{\mathsf T},\quad
U=\operatorname{diag}(\zeta_1,\zeta_2),\quad |\zeta_j|=1,\\
B=UB_0U^*,\quad B_0=\begin{pmatrix}a&z\\\bar z&d\end{pmatrix},\quad
\alpha=\|P_{\ker D_{\rm env}}\ell\|>0,\quad
s=\rho\operatorname{diag}(1,-2)\oplus0_m,\\
u_0=(-2\sqrt2,1)^{\mathsf T},\quad p_0=(1,2\sqrt2)^{\mathsf T},\quad
w_0=4\sqrt2a-3z,\quad\delta=2a-\sqrt2\operatorname{Re}z.
\end{gathered}
\tag{23.1}
$$

这里 $a,d,\rho\in\mathbb R$，$z\in\mathbb C$，$D_{\rm env}$ 任意有限 Hermitian，$\sigma$ 分别固定。对任意实际 $x=x_A\oplus0_m$，向量 $\xi=(u,y)$ 的两笔原预算同时为零，当且仅当以下两种情形之一成立：

$$
u=0,\qquad \ell^*y=0;
\tag{23.2}
$$

或存在 $\lambda\in\mathbb C\setminus\{0\}$、$\beta\in\mathbb R$ 使

$$
\begin{gathered}
d+4a-3\sqrt2\operatorname{Re}z=0,\qquad
u=\lambda Uu_0,\qquad x_A=\beta Up_0p_0^*U^*,\\
\ell^*y=\lambda\bigl(w_0-2\sigma i\sqrt2\beta\bigr).
\end{gathered}
\tag{23.3}
$$

$D_{\rm env}y$ 不受额外约束。对固定 $x$，令 $\mathcal M_x$ 为如下复子空间：若超平面等式成立且 $x_A=\beta Up_0p_0^*U^*$，则

$$
\mathcal M_x=\{(\lambda Uu_0,y):\lambda\in\mathbb C,
\ \ell^*y=\lambda(w_0-2\sigma i\sqrt2\beta)\};
\tag{23.4}
$$

其余情形令 $\mathcal M_x=0\oplus\ker\ell^*$。任意正密度的准确条件与读取为

$$
\boxed{\phi\in\mathcal Z_\sigma(x)\ \Longleftrightarrow\
\operatorname{ran}\Theta\subseteq\mathcal M_x,\qquad
\phi(L)=\frac{16\rho\delta}{9}\phi(P)\quad(\phi\in\mathcal Z_\sigma(x)).}
\tag{23.5}
$$

特别地，(23.3) 的向量读取是 $\phi_\xi(L)=16\rho\delta|\lambda|^2$；(23.2) 的读取为零。这些断言不以 P2 为前件。

证明。由 (22.2)，共同零预算向量必须满足

$$
V^*Cu=\ell v^*CU^*u=0.
$$

$\ell\ne0$，而 $\ker(v^*C)=\mathbb C u_0$，所以 $u=\lambda Uu_0$。$\lambda=0$ 时，(22.8)–(22.9) 的同一计算仍适用，强制 $Vy=0$，等价于 $\ell^*y=0$；反向与零读取也由该计算给出。

以下设 $\lambda\ne0$。两份 $R_\pm\xi$ 的环境部分均为零，两份 $S_\pm\xi$ 的环境部分则同为 $V^*u+D_{\rm env}y$。它们投影到环境零模后的值是

$$
P_{\ker D_{\rm env}}(V^*u+D_{\rm env}y)
=-\sqrt2\lambda P_{\ker D_{\rm env}}\ell\ne0.
\tag{23.6}
$$

零实 Gram 的两个向量实线性相关；一向量的环境部分为零、另一向量的环境部分非零时，前一向量只能为零。故两份 $R_\pm\xi$ 都为零，相加相减得到

$$
x\xi=0,\qquad (h-k)\xi=0.
\tag{23.7}
$$

Hermitian 二阶矩阵 $U^*x_AU$ 消去 $u_0$，因而准确为 $\beta p_0p_0^*$，$\beta\in\mathbb R$。这是 $u_0^\perp=\mathbb C p_0$ 上的一维 Hermitian 作用。由 $p_0^*Cu_0=2\sqrt2$，有

$$
h\xi=-\frac{\sigma i}{2}xc\xi
=(-\sigma i\sqrt2\beta\lambda Up_0,0).
\tag{23.8}
$$

记 $K_0=C\circ B_0$。$k\xi$ 的演员部分为 $U(\lambda K_0u_0+C v\ell^*y/2)$，其中 $Cv=p_0$，环境部分为零。将 $k\xi=h\xi$ 左乘 $u_0^*U^*$，得到

$$
0=u_0^*K_0u_0=8a+2d-6\sqrt2\operatorname{Re}z.
\tag{23.9}
$$

这正是 (23.3) 的超平面。该等式下，(19.10) 的原矩阵恒等式给

$$
K_0u_0=-w_0p_0/2.
\tag{23.10}
$$

故 $k\xi=h\xi$ 的剩余标量方程准确为 (23.3) 的最后一式。反向地，(23.3)、(23.8)–(23.10) 给 $x\xi=0$、$k\xi=h\xi$，从而两份 $R$ 都消去 $\xi$，两笔预算确为零。这个反向不需要约束 $D_{\rm env}y$。由于 $\alpha>0$，(23.3) 的环境方程始终有解：令 $q_0=P_{\ker D_{\rm env}}\ell/\alpha$，可取

$$
y=\lambda(w_0-2\sigma i\sqrt2\beta)q_0/\alpha.
\tag{23.11}
$$

这也表明超平面上每个这样的探针都有非零演员接触。

为计算左端，(23.7) 给 $h\xi=-\sigma i r\xi$、$tc\xi=2h\xi-ct\xi$，所以

$$
(r+g_\sigma)\xi=\sigma i ct\xi+s\xi,\qquad
\phi_\xi(L)=-2\operatorname{Re}((t\xi)^*s\xi).
\tag{23.12}
$$

后式中 $\operatorname{Re}(\sigma i(t\xi)^*ct\xi)=0$，第一项 $x\xi$ 也为零。复用 (19.11)–(19.14) 的演员计算，记其中的演员列为 $T$，则

$$
(t\xi)_{\rm actor}=\lambda U(T-2\sigma i\sqrt2\beta v),\qquad
\operatorname{Re}(T^*CZu_0)=-8\delta,\quad Z=\operatorname{diag}(1,-1).
\tag{23.13}
$$

这些是超平面上的矩阵恒等式，不对 $\delta$ 作除法，故也适用于 $\delta=0$。$v^*CZu_0=-4\sqrt2$ 为实数，故 (23.13) 中新增的纯虚系数不改变 (23.12) 的实部，得到 $16\rho\delta|\lambda|^2$。$s\xi$ 只有演员分量，因此任意 $D_{\rm env}y$ 都未被忽略或改写。

最后，(23.2)–(23.3) 中的全部向量恰组成 (23.4) 所定义的 $\mathcal M_x$，且 $R_\pm$ 均消去这个子空间。若总密度的两笔预算为零，(17.15) 强制每个谱向量属于 $\mathcal M_x$，因而支撑包含于它；反向由 $R_\pm$ 消去支撑直接得到。谱向量写成 $(\lambda_jUu_0,y_j)$，其中纯环境情形取 $\lambda_j=0$，则

$$
\phi(P)=9\sum_j|\lambda_j|^2,\qquad
\phi(L)=16\rho\delta\sum_j|\lambda_j|^2.
$$

这就是 (23.5)，也包括零密度与任意混合质量。∎

## 24. 第一环境边为正时的两笔正预算

**定理 24.1（任意有限环境中的严格正预算排除域）。** 保持原输入 (19.1)，设

$$
B_{11}=\rho/2,\qquad B_{12}=b,\qquad
0<|\rho|\le\tfrac12,\qquad |b|\le1,\qquad
0<q:=\|V^*e_1\|\le\rho^2/16,\qquad
s=\rho\operatorname{diag}(1,-2)\oplus0_m.
\tag{24.1}
$$

不限制 $B_{22}$、第二演员环境边或 $D_{\rm env}$。对每个分别固定的 $\sigma$，取同一实际探针与单位向量

$$
x_\sigma=\begin{pmatrix}
5\rho/2&(2+3\sigma i)b\\
(2-3\sigma i)\bar b&0
\end{pmatrix}\oplus0_m,\qquad
\xi=e_1\oplus0_m.
\tag{24.2}
$$

则两笔原预算均严格为正，并且

$$
\boxed{\mathcal G_\sigma(x_\sigma,\phi_\xi)>\rho^2/16.}
\tag{24.3}
$$

该断言不要求 P2。对每个给定质量 $\mu>0$，同一探针和 $\sqrt\mu\xi$ 的预算差额严格大于 $\mu\rho^2/16$，两预算仍严格为正；零泛函满足原 PB 的零等式。

证明。探针是 (20.2) 在 $a=\rho/2$ 时的既有演员探针：$u=5\rho/2$、$\eta=2-3\sigma i$。只复用 (20.5)–(20.8) 的演员计算；环境作用列仍须取当前实际非零边。置

$$
w=V^*e_1,\qquad
 a_+=(2\rho,(2-2\sigma i)\bar b)^{\mathsf T},\qquad
 a_-=(3\rho,(2-4\sigma i)\bar b)^{\mathsf T}.
$$

原块乘法给同一个 $\xi$ 上的完整四列：

$$
\begin{array}{ll}
R_+\xi=(a_+,-w/2),&S_+\xi=(2a_+,(1-\sigma i/2)w),\\
R_-\xi=(a_-,w/2),&S_-\xi=(-a_-,(1+\sigma i/2)w).
\end{array}
\tag{24.4}
$$

特别是两份 $S$ 的环境平方均保留 $(5/4)q^2$，不适用 (20.9) 的零边断言。令

$$
A_+=\|a_+\|^2=4\rho^2+8|b|^2,\qquad
A_-=\|a_-\|^2=9\rho^2+20|b|^2.
\tag{24.5}
$$

由 (24.4) 得原平方及实配对

$$
\begin{array}{lll}
\phi_\xi(R_+^2)=A_++q^2/4,&
\phi_\xi(S_+^2)=4A_++5q^2/4,&
\phi_\xi(R_+\circ S_+)=2A_+-q^2/2,\\
\phi_\xi(R_-^2)=A_-+q^2/4,&
\phi_\xi(S_-^2)=A_-+5q^2/4,&
\phi_\xi(R_-\circ S_-)=-A_-+q^2/2.
\end{array}
\tag{24.6}
$$

相乘相减，准确得到

$$
\begin{aligned}
B_{\phi_\xi}(R_+,S_+)&=\tfrac{17}{4}A_+q^2+\tfrac1{16}q^4,\\
B_{\phi_\xi}(R_-,S_-)&=\tfrac52 A_-q^2+\tfrac1{16}q^4.
\end{aligned}
\tag{24.7}
$$

$q>0$、$\rho\ne0$ 保证两者严格正。

左端也在同一个原向量上读取。$x\xi$ 没有环境分量，故 (20.10) 的第一项演员实部不变；第二项比零边情形只多

$$
\operatorname{Re}\bigl(w^*(-\sigma i w/2)\bigr)=0.
$$

因此原定义仍给

$$
\phi_\xi(L)=-2(\rho/2)\rho=-\rho^2.
\tag{24.8}
$$

这里没有删去 $t\xi$ 或 $g_\sigma\xi$ 的环境分量。

由 (24.1)，$A_+\le9$、$A_-\le89/4$、$q\le1/64$。于是

$$
\begin{gathered}
\tfrac{17}{4}A_++q^2/16
\le153/4+1/65536<49,\\
\tfrac52 A_-+q^2/16
\le445/8+1/65536<64.
\end{gathered}
\tag{24.9}
$$

结合 (24.7)，两根之和严格小于 $7q+8q=15q\le15\rho^2/16$；(24.8) 给出 (24.3)。最后，正倍数泛函下 $B$ 为二次齐次、其根和 $\phi(L)$ 为一次齐次，故同一严格差额按 $\mu$ 缩放。∎

## 25. 总耦合秩二且全正 P2 成立的同一实现

**定理 25.1（满行秩 P2 与正预算违反同时实现）。** 取

$$
\begin{gathered}
m=2,\qquad D_{\rm env}=I_2,\qquad V=\operatorname{diag}(\varepsilon,1),\\
B=\begin{pmatrix}\rho/2&1\\1&\rho+1-2\varepsilon^2\end{pmatrix},\qquad
s=\rho\operatorname{diag}(1,-2)\oplus0_2,\\
0<|\rho|\le\tfrac12,\qquad0<\varepsilon\le\rho^2/16.
\end{gathered}
\tag{25.1}
$$

实际 $\operatorname{rank}V=2$，而 $\ker D_{\rm env}=0$，故零模耦合秩为零。对两种分别解释的 $\sigma$，同一完整 $M_4(\mathbb C)$ 输入满足全部原正泛函的固定 P2；(24.2) 取 $b=1$ 给该同一输入的实际 PB 严格违反，并有 (24.3) 的严格正差额及两笔正预算。若只保留 (25.1) 的矩阵公式并允许 $\rho\in\mathbb R$，则对每个固定 $\varepsilon>0$，此矩阵族的全正 P2 准确区间为

$$
|\rho|\le\frac{\sqrt2}{2+\varepsilon^2}.
\tag{25.2}
$$

证明。直接应用定理 8.1 的原全正泛函对应；不以选定向量检验代替它。其 Schur 矩阵和归一化矩阵是

$$
\begin{gathered}
H=B-VV^*=\begin{pmatrix}\rho/2-\varepsilon^2&1\\1&\rho-2\varepsilon^2\end{pmatrix},\\
C^{-1/2}HC^{-1/2}=\begin{pmatrix}
\rho/2-\varepsilon^2&1/\sqrt2\\
1/\sqrt2&\rho/2-\varepsilon^2
\end{pmatrix}.
\end{gathered}
\tag{25.3}
$$

故为非对角 Schur 平衡分支，$\beta=1/\sqrt2$。取有序谱基

$$
U_0=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad
\omega=(U_0^*ZU_0)_{12}=1.
$$

原环境度量准确给

$$
\begin{gathered}
GG^*=U_0^*C^{-1/2}(I_2+VV^*)C^{-1/2}U_0
=\begin{pmatrix}1+\varepsilon^2/2&\varepsilon^2/2\\
\varepsilon^2/2&1+\varepsilon^2/2\end{pmatrix},\\
Q=\frac1{1+\varepsilon^2}
\begin{pmatrix}1+\varepsilon^2/2&-\varepsilon^2/2\\
-\varepsilon^2/2&1+\varepsilon^2/2\end{pmatrix},\\
R=\frac{2+\varepsilon^2}{2(1+\varepsilon^2)},\qquad
h=-\frac{\varepsilon^2}{2(1+\varepsilon^2)},\qquad
\Delta=\frac1{1+\varepsilon^2},\qquad J=0.
\end{gathered}
\tag{25.4}
$$

代入 (8.3) 得 (25.2)，与 $\sigma$ 无关，包含端点、零泛函和任意有限质量。对 (25.1) 的参数，$\varepsilon\le1/64$，所以

$$
|\rho|(2+\varepsilon^2)\le\tfrac12(2+1/4096)<\tfrac54<\sqrt2.
$$

故这些输入均在全正 P2 区间内。

在同一个输入上，$B_{11}=\rho/2$、$b=1$、$\|V^*e_1\|=\varepsilon$，准确满足 (24.1)。直接消费定理 24.1，得实际 $x_\sigma$、同一 $\xi=e_1\oplus0_2$、两笔正预算和严格违反。任意正质量的严格违反由该定理的同一缩放给出。由于 $\varepsilon>0$，实际耦合秩二，定理 22.3 同时保证不存在左端非零的共同零预算接触；这里的违反确实使用正预算。它不是满足全部 PB 的非零残量模型。∎

## 26. 完整有限类的剩余不等式

**定义 26.1（原全称问题与剩余域）。** 固定每个 $\sigma$，令 $\mathfrak F_\sigma$ 为 (17.1) 的全部有限输入中，$s=\rho\operatorname{diag}(1,-2)\oplus0_m$、$\rho\ne0$ 且原 P2 对完整 $M_{m+2}(\mathbb C)$ 上全部正泛函成立的输入集合。$m$ 任意有限，$B,D_{\rm env}$ 任意 Hermitian，$V$ 任意；不附加关于未知总响应 $D$ 的任何假设。原有限类的非零残量全 PB 集合仍定义为

$$
\mathfrak A_\sigma=
\{(B,V,D_{\rm env},\rho)\in\mathfrak F_\sigma:
\mathcal G_\sigma(x,\phi)\le0
\text{ 对每个实际 }x=x^*=PxP\text{ 及全部 }\phi\ge0\}.
\tag{26.1}
$$

定理 8.1、13.1 已给 $\mathfrak F_\sigma$ 的完整 P2 参数条件，未给 (26.1) 的全 PB 分类。令 $\mathfrak D_{\rm old}$ 是本卷定理 19.1、20.1，以及[区间卷定理 12.3](AURIC_INTERVAL_ORIGINAL_RESPONSE_AND_VARIABLE_PROJECTION_TRANSPORT.md#123-原全部探针的参数完备结论)、承载卷[定理 41.2](https://github.com/the-omega-institute/trureturing/blob/caf0f3b3064a987b753b67aaa3836d6d86e73f75/docs/develop/theory/AURIC_FULL_PB_POLYNOMIAL_TRANSPORT_AND_REAL_ROOT_RIGIDITY.md#412-两个明确斜率的有限充分定理)、[定理 42.2](https://github.com/the-omega-institute/trureturing/blob/caf0f3b3064a987b753b67aaa3836d6d86e73f75/docs/develop/theory/AURIC_FULL_PB_POLYNOMIAL_TRANSPORT_AND_REAL_ROOT_RIGIDITY.md#422-零探针刚性及明确的有限反证读取) 各自准确排除域与 $\mathfrak F_\sigma$ 的并交；这些既有结论直接引用。令 $\mathfrak D_{\rm pos}$ 是 (24.1) 的域与 $\mathfrak F_\sigma$ 的交，定义

$$
\mathfrak R_\sigma=
\mathfrak F_\sigma\setminus(\mathfrak D_{\rm old}\cup\mathfrak D_{\rm pos}).
\tag{26.2}
$$

完整目标仍是判定 $\mathfrak A_\sigma$ 是否为空。其未决不等式准确为：对 $\mathfrak R_\sigma$ 的每份数据，判定是否存在同一个原探针和同一个原正泛函，使

$$
|\phi(L)|>
\sqrt{\phi(R_+^2)\phi(S_+^2)-\phi(R_+\circ S_+)^2}
+\sqrt{\phi(R_-^2)\phi(S_-^2)-\phi(R_-\circ S_-)^2}.
\tag{26.3}
$$

若有非零残量满足全部 PB，则须在同一份数据上对每个实际探针及全部原正泛函证明 (26.3) 的反向非严格不等式；零质量和任意有限质量同在此量词内。$\rho=0$ 的充分性直接由 §1 的标准零残量结果承担。

$\mathfrak R_\sigma$ 中明确保留：平衡零模秩一在既有排除域与 (24.1) 之外的全部输入；实际总耦合满行秩 $\operatorname{rank}V=2$ 在这些域之外的输入；零模耦合秩零、归一化 Schur 矩阵平衡且非对角的其余输入。在总秩一形状 (23.1) 中，超平面外或 $\delta=0$ 的未覆盖成员仍属于这一目标：定理 23.1 只表明它们没有左端非零的共同零预算接触，未断言 PB 成立。定理 22.3 对满行秩输入给出同样的方法边界；定理 24.1、25.1 只在其明确域中提供正预算违反。

(26.1)–(26.3) 的每个平方与乘积始终在原 $M_{m+2}(\mathbb C)$ 中计算。本卷 (17.7)、(17.15) 提供的是共同原读取与正密度提升，定理 18.1 的非约化障碍仍禁止将其改成普通 $M_6$ 的压缩平方分类。[双角卷定理 44.2](AURIC_FULL_PB_TWO_CORNER_POSITIVE_CERTIFICATE_CONTINUATION.md#44-两个完整角约束同一输出的三项正证书) 依赖完整原 $\mathsf H_A(D)$ 和两个整个角的共同符号，不能代替此固定输出目标的前件。

这里的环境面积底界、共同接触穷尽及小正边预算差额是上述原标签中的 $\texttt{repo-derived}$ 推导；实 Gram 与正交投影只作为其中的成熟中间工具。§§6、15、18、21 的完整来源身份和递归固定物理合同仍按原全文解释。一般原关系的 $E_+^D=E_-^D$、$N\omega(\varepsilon)^2\to0$、完整 $\mathsf H$／任意总响应 $D$ 及固定物理来源的共同实现仍是独立未决义务。(26.1) 不将协变、正则性、齐次、单位平移、商或压缩自然性增为前件，也不由数学向量和探针生成物理来源。

## 新增锚（本行以下为后续增补区）

## 27. 全有限类的联合探针与环境系数判据

### 27.1 原空间像与实系数矩阵

**定义 27.1（联合二次型）。** 准确沿用定义 17.1 的任意有限输入 (17.1)、本卷 (1.1)–(1.2)，以及[承载卷定义 41.1](https://github.com/the-omega-institute/trureturing/blob/caf0f3b3064a987b753b67aaa3836d6d86e73f75/docs/develop/theory/AURIC_FULL_PB_POLYNOMIAL_TRANSPORT_AND_REAL_ROOT_RIGIDITY.md#411-原完整问题与较弱的固定输出接口)的原标签。固定一个 $\sigma\in\{1,-1\}$，记

$$
C=\operatorname{diag}(1,2),\qquad S_A=\operatorname{diag}(s_1,s_2),\qquad
s=S_A\oplus0_m,\qquad g_\sigma=\frac{\sigma i}{2}[c,t]+s.
\tag{27.1}
$$

$B,D_{\rm env}$ 任意 Hermitian，$V$ 任意，$s_1,s_2$ 为任意实数；此处不假设 P2。$D_{\rm env}$ 始终只是同一个已知输入 $t$ 的环境矩阵。

直接取定义 17.1 的 $\mathcal E_0\subseteq\mathbb C^m$ 和 $\mathcal H_0=\mathbb C^2\oplus\mathcal E_0$。定理 17.2 已给出 $d:=\dim_{\mathbb C}\mathcal E_0\le4$ 及逐预算、逐质量的全正泛函等价。选定该子空间的一组复正交归一基，以等距嵌入 $F:\mathbb C^d\to\mathbb C^m$ 表示，定义实线性坐标

$$
Y(v)=F(v_1+i v_{d+1},\ldots,v_d+i v_{2d})^{\mathsf T},
\qquad v\in\mathbb R^{2d}.
\tag{27.2}
$$

$d=0$ 时 $v$ 为空、$Y=0$。对 $a\in\mathbb R^4$ 定义全部 Hermitian 演员探针的坐标

$$
X(a)=\begin{pmatrix}a_1&a_3+i a_4\\a_3-i a_4&a_2\end{pmatrix},\qquad
H_\sigma(X)=\frac{\sigma i}{2}[C,X],\qquad J_C(X)=C\circ X.
\tag{27.3}
$$

以下把原 $\mathcal H=\mathbb C^2\oplus\mathbb C^m$ 当作实 Hilbert 空间，只使用其实内积
$\langle z,w\rangle_{\mathbb R}=\operatorname{Re}(z^*w)$，范数仍为原复 Hilbert 范数。固定任意单位演员方向 $u\in\mathbb C^2$，不要求它的任一坐标非零。令

$$
n=5+2d\le13,\qquad z=(a,v,\tau)\in\mathbb R^n.
$$

定义下列从 $\mathbb R^n$ 到原 $\mathcal H$ 的实线性映射；每个像都保留其演员与环境分量：

$$
\begin{aligned}
\mathcal Xz&=(X(a)u,0),&
\mathcal H_\sigma z&=(H_\sigma(X(a))u,0),&
\mathcal Jz&=(J_C(X(a))u,0),\\
\mathcal Tz&=(\tau Bu+VY(v),\ \tau V^*u+D_{\rm env}Y(v)),\\
\mathcal Kz&=(\tau(C\circ B)u+\tfrac12 CVY(v),\ \tfrac\tau2 V^*Cu),\\
\mathcal G_sz&=(\tau(\tfrac{\sigma i}{2}[C,B]+S_A)u
                      +\tfrac{\sigma i}{2}CVY(v),\ -\tfrac{\sigma i\tau}{2}V^*Cu).
\end{aligned}
\tag{27.4}
$$

对 $\delta\in\{1,-1\}$，再置

$$
\begin{gathered}
\mathcal R_\delta=\mathcal X+\delta(\mathcal H_\sigma-\mathcal K),\qquad
\mathcal S_{\delta,s}=\mathcal T+\delta(\mathcal J+\mathcal G_s),\\
\ell_s(z)=-2\langle\mathcal Xz,(\mathcal H_\sigma-\mathcal K)z\rangle_{\mathbb R}
           -2\langle\mathcal Tz,(\mathcal J+\mathcal G_s)z\rangle_{\mathbb R}.
\end{gathered}
\tag{27.5}
$$

若 $\mathcal A,\mathcal B$ 是这类实线性映射，记
$\operatorname{Sym}(\mathcal A,\mathcal B)
=(\mathcal A^{\mathsf T}\mathcal B+\mathcal B^{\mathsf T}\mathcal A)/2$，其中转置对上述原实内积取伴随。令

$$
\mathscr L_s=-2\operatorname{Sym}(\mathcal X,\mathcal H_\sigma-\mathcal K)
              -2\operatorname{Sym}(\mathcal T,\mathcal J+\mathcal G_s),
\qquad z^{\mathsf T}\mathscr L_sz=\ell_s(z).
$$

索引 $\theta$ 只含下列变量：

$$
\theta=(u,\epsilon,\alpha_+,\alpha_-,\beta_+,\beta_-),\qquad
\|u\|=1,\quad\epsilon\in\{1,-1\},\quad
0<\alpha_+,\alpha_-<\infty,\quad\beta_+,\beta_-\in\mathbb R.
\tag{27.6}
$$

这里的 $\epsilon$ 是绝对值的两个实符号，与固定的取向 $\sigma$ 分开。对每个 $\theta$ 定义实对称系数矩阵

$$
\boxed{\quad
\mathscr Q_{\sigma,s}(\theta)=
\sum_{\delta=\pm1}\left[
\alpha_\delta\mathcal R_\delta^{\mathsf T}\mathcal R_\delta
+\alpha_\delta^{-1}
 (\mathcal S_{\delta,s}-\beta_\delta\mathcal R_\delta)^{\mathsf T}
 (\mathcal S_{\delta,s}-\beta_\delta\mathcal R_\delta)
\right]-2\epsilon\mathscr L_s .\quad}
\tag{27.7}
$$

矩阵的阶数为 $n\le13$，其条目由 (27.2)–(27.5) 的原空间实内积唯一确定。$(a,v,\tau)$ 是构造系数时的二次型变量，不属于索引 $\theta$，也不是额外的探针或读取量词。换取 $\mathcal E_0$ 的另一组复正交归一基只在 $v$ 坐标上作实正交变换，故 (27.7) 相应作合同变换；其半正定性不变，原 $B,V,D_{\rm env}$ 并未被替换。

### 27.2 全部原 PB 的充要条件与有限失败见证

**定理 27.2（联合消元的全称系数判据）。** 对定义 27.1 的每份有限输入、每个分别固定的 $\sigma$，以下两项等价：

1. 每个实际 $x=x^*=PxP$ 和完整 $M_{m+2}(\mathbb C)$ 上每个正复线性泛函 $\phi$ 都满足原 PB，即

   $$
   |\phi(L)|\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
   \tag{27.8}
   $$

2. 对 (27.6) 的每个 $\theta$ 都有 $\mathscr Q_{\sigma,s}(\theta)\succeq0$。

这里不假设 P2，不要求任何环境块、系数块或 Gram 矩阵可逆。对每个指定有限质量 $\mu>0$，第一项可以等价地只量化 $\phi(I_{m+2})=\mu$；所得条件仍是同一第二项。质量 $0$ 时正泛函只有零泛函，(27.8) 总是零等式，本身不对系数矩阵加条件。因此量化全部非负有限质量与第二项等价，并完整保留零质量。

每个 (27.7) 也有如下等价的广义 Schur 写法。按最后一个坐标分块，记

$$
\mathscr Q_{\sigma,s}(\theta)=
\begin{pmatrix}A&b\\b^{\mathsf T}&\gamma\end{pmatrix}.
$$

则该系数测试准确等价于

$$
A\succeq0,\qquad b\in\operatorname{ran}A,\qquad
\gamma-b^{\mathsf T}A^\dagger b\ge0.
\tag{27.9}
$$

$A^\dagger$ 是这个实对称矩阵的谱 Moore–Penrose 逆。不得在 $A$ 奇异时删掉中间的值域条件。

如果任何一个有限索引 $\theta$ 的系数测试失败，则在同一份不变的 $B,V,D_{\rm env},s,\sigma$ 上存在一个有限实际 Hermitian 角探针和一个原全空间向量泛函，使 (27.8) 严格失败。对每个指定 $\mu>0$ 都能在同一探针上取得质量恰为 $\mu$ 的严格失败；所用泛函的两笔预算和左端始终属于同一个实际实现。

证明。首先确认 (27.4)–(27.5) 所编码的是原算子像。$\tau=1$ 时令

$$
x=X(a)\oplus0_m,\qquad \eta=(u,Y(v))\in\mathcal H_0.
$$

原全空间块乘法直接给

$$
\begin{gathered}
\mathcal Xz=x\eta,\quad\mathcal H_\sigma z=h\eta,\quad
\mathcal Jz=r\eta,\quad\mathcal Tz=t\eta,\quad
\mathcal Kz=k\eta,\quad\mathcal G_sz=g_\sigma\eta,\\
\mathcal R_\delta z=R_\delta\eta,\qquad
\mathcal S_{\delta,s}z=S_\delta\eta,\qquad
\ell_s(z)=\phi_\eta(L).
\end{gathered}
\tag{27.10}
$$

尤其 $\mathcal T$ 中的 $D_{\rm env}Y(v)$、$\mathcal K$ 和 $\mathcal G_s$ 中的环境像全部保留。对任何原自伴 $U,W$，已有的原像恒等式给

$$
\phi_\eta(U^2)=\|U\eta\|^2,\qquad
\phi_\eta(U\circ W)=\langle U\eta,W\eta\rangle_{\mathbb R}.
\tag{27.11}
$$

这计算的是 $U,W$ 的原全空间乘积，不是它们压缩后的平方或乘积。$\mathcal H_0$ 不必约化它们，命题 18.1 的障碍仍保留。

所消费的变分恒等式是成熟的二阶实 Gram 行列式／算术几何平均关系。为包含退化情形，在这里给出全部所需代数。对同一实 Hilbert 空间中的 $U,W$，置

$$
a_0=\|U\|^2,\qquad b_0=\langle U,W\rangle_{\mathbb R},\qquad
c_0=\|W\|^2,\qquad\Delta=a_0c_0-b_0^2\ge0.
$$

则

$$
2\sqrt\Delta=
\inf_{\alpha>0,\ \beta\in\mathbb R}
\left(\alpha\|U\|^2+\alpha^{-1}\|W-\beta U\|^2\right).
\tag{27.12}
$$

确实，$a_0>0$ 时配方为

$$
\alpha a_0+\alpha^{-1}\left(
a_0(\beta-b_0/a_0)^2+\Delta/a_0\right)\ge2\sqrt\Delta.
$$

若 $\Delta>0$，取 $\beta=b_0/a_0$、$\alpha=\sqrt\Delta/a_0$ 达到等号。若 $\Delta=0$，对任意给定 $e>0$，取同一 $\beta$、$\alpha=e/a_0$ 就使该式等于 $e$。$a_0=0$ 时 $U=0$、$b_0=\Delta=0$；若 $c_0>0$，取 $\alpha=c_0/e$ 使该式等于 $e$，若 $c_0=0$ 则任意参数都给零。故所有零 Gram 情形都包括在内，而且每个正容差都由有限参数实现，无须假设下确界取到。

现在对固定的同一 $x,\eta$，将 (27.12) 分别用于 (27.10) 的两对像。每次只有两个实变分参数，所有像仍由共同的 $a,v$ 决定。于是 (27.8) 对这个 $x,\phi_\eta$ 成立，当且仅当对两个 $\epsilon$ 和全部四个变分参数有

$$
\begin{aligned}
&\sum_{\delta=\pm1}\left[
\alpha_\delta\|\mathcal R_\delta z\|^2
+\alpha_\delta^{-1}\|\mathcal S_{\delta,s}z-\beta_\delta\mathcal R_\delta z\|^2
\right]-2\epsilon\ell_s(z)\\
&\hspace{30mm}=z^{\mathsf T}\mathscr Q_{\sigma,s}(\theta)z\ge0,
\qquad z=(a,v,1).
\end{aligned}
\tag{27.13}
$$

这里取两份数值下确界之和，只是在同一固定实现上使用两次 (27.12)；不分别选择探针、向量、环境或质量，也不交换任何极小与极大。

对固定 $\theta$，(27.13) 对全部 $a,v$ 成立，当且仅当 $\mathscr Q_{\sigma,s}(\theta)\succeq0$。一个方向显然；另一个方向对任意 $\tau\ne0$ 使用齐次化恒等式

$$
z^{\mathsf T}\mathscr Q_{\sigma,s}(\theta)z
=\tau^2\,(a/\tau,v/\tau,1)^{\mathsf T}
\mathscr Q_{\sigma,s}(\theta)(a/\tau,v/\tau,1),
\tag{27.14}
$$

再由有限二次型的连续性包括 $\tau=0$。这一步同时消去全部四个真实探针坐标和全部 $2d$ 个环境读取坐标，不把它们换成彼此无关的优化变量。

还须处理读取向量的演员分量。对任意 $\eta=(w,y)\in\mathcal H_0$，若 $w\ne0$，则

$$
\eta=\|w\|\,(u,y/\|w\|),\qquad u=w/\|w\|.
$$

向量泛函按 $\|w\|^2$ 缩放，PB 两边都按这个相同因子缩放，故单位 $u$ 的测试穷尽所有此类向量，没有除以某个演员坐标。若 $w=0$，原定义直接给

$$
x\eta=h\eta=r\eta=s\eta=0,\qquad
g_\sigma\eta=(\tfrac{\sigma i}{2}CVy,0),\qquad
t\eta=(Vy,D_{\rm env}y),
$$

所以 $\phi_\eta(L)=-2\operatorname{Re}((Vy)^*(\sigma i CVy/2))=0$，PB 自动成立。这也包含零向量。轴向 $u=e_1,e_2$、空环境和全部奇异块均未被删去。

定理 17.2 的 (17.7) 已将每个原探针在 $\mathcal H_0$ 全部向量上的 PB，与原全代数全部正复线性泛函上的 PB 等价，其 (17.15)–(17.16) 支付混合密度提升；直接消费这条结论，不另加 P2。它没有删掉环境密度块。结合 (27.13)–(27.14) 和刚才的演员分量分析，得到本定理的充要关系。对任意固定 $\mu>0$，任一非零正泛函均可乘以唯一正因子而成为质量 $\mu$，PB 的根与左端都一次齐次，故质量限制不改变判据。$\mu=0$ 时正密度的非负谱值之和为零，只能是零密度，给出所述零等式。

为说明 (27.9) 在奇异处没有缺项，使用成熟的广义 Schur 判别，其来源为 Higham，[*What Is the Schur Complement of a Matrix?*](https://nhigham.com/2023/06/01/what-is-the-schur-complement-of-a-matrix/)，Generalized Schur Complement，Theorem 1。所需实对称特例也可完整验证如下。半正定性首先给 $A\succeq0$。若 $b\notin\operatorname{ran}A=(\ker A)^\perp$，可取 $k\in\ker A$ 使 $b^{\mathsf T}k\ne0$；向量 $(qk,1)$ 上的值是 $2q b^{\mathsf T}k+\gamma$，某个有限实 $q$ 即使它为负。故值域条件必要。在值域条件下，对任何 $w\in\mathbb R^{n-1}$、$\tau\in\mathbb R$ 有准确配方

$$
\begin{aligned}
w^{\mathsf T}Aw+2\tau b^{\mathsf T}w+\gamma\tau^2
&=(w+\tau A^\dagger b)^{\mathsf T}A(w+\tau A^\dagger b)\\
&\quad+(\gamma-b^{\mathsf T}A^\dagger b)\tau^2.
\end{aligned}
\tag{27.15}
$$

由谱定义 $AA^\dagger b=b$，这个恒等式成立；取 $w=-A^\dagger b,\tau=1$ 又给最后标量条件的必要性。这证明 (27.9)，包括 $A=0$。

最后从系数失败提取一个实际严格见证。令 $Q=\mathscr Q_{\sigma,s}(\theta)$，取有限实向量 $z_0=(a,v,\tau)$ 使 $z_0^{\mathsf T}Qz_0<0$。若 $\tau=0$，令 $e_n$ 为最后一个坐标向量，并记

$$
\kappa_0=-z_0^{\mathsf T}Qz_0>0,\qquad
M=2|e_n^{\mathsf T}Qz_0|+|e_n^{\mathsf T}Qe_n|,\qquad
h_0=\frac{\kappa_0}{2(\kappa_0+M)}>0.
$$

取 $z_1=z_0+h_0e_n$。因为 $h_0\le1/2$，
$z_1^{\mathsf T}Qz_1\le-\kappa_0+h_0M<-\kappa_0/2$，且其最后坐标非零。若原 $\tau\ne0$，直接取 $z_1=z_0$。将 $z_1$ 的坐标仍记为 $(a,v,\tau)$，定义一次有限的原探针与向量

$$
x=X(a/\tau)\oplus0_m,\qquad
\eta=(u,Y(v/\tau)).
\tag{27.16}
$$

(27.13)–(27.14) 及 (27.12) 的下界给

$$
\epsilon\phi_\eta(L)>
\frac12\sum_{\delta=\pm1}
\left[\alpha_\delta\|R_\delta\eta\|^2
+\alpha_\delta^{-1}\|S_\delta\eta-\beta_\delta R_\delta\eta\|^2\right]
\ge\sum_{\delta=\pm1}\sqrt{B_{\phi_\eta}(R_\delta,S_\delta)}.
\tag{27.17}
$$

因此原 PB 严格失败。$\eta$ 的演员分量为单位 $u$，所以它非零且质量有限。对每个给定 $\mu>0$ 使用同一 $x$ 和

$$
\xi_\mu=\frac{\sqrt\mu}{\|\eta\|}\eta,\qquad
\phi_{\xi_\mu}(I)=\mu,
\tag{27.18}
$$

严格差额按 $\mu/\|\eta\|^2$ 缩放。这里是一个已经取得的有限见证，不是无穷探针极限，也不要求退化 Gram 的变分下确界取到。反向地，若单位演员读取上的原 PB 有严格差额，则 (27.12) 中每笔误差小于这个差额的有限参数就使 (27.13) 严格为负；故充要关系也没有遗漏只在退化根处出现的失败。∎

### 27.3 保持同一泛函的两笔严格正预算

**定理 27.3（有限探针扰动的共同正预算见证）。** 在定理 27.2 的同一有限类中，若全部原 PB 不成立，则对每个指定有限 $\mu>0$，存在一个实际有限角探针 $x'$ 和一个质量为 $\mu$ 的原全空间向量泛函 $\phi$，使

$$
B_\phi(R_+(x'),S_+(x'))>0,\qquad
B_\phi(R_-(x'),S_-(x'))>0,
$$

且原 PB 在 $x',\phi$ 上严格失败。准确地，可以先取 (27.16)–(27.18) 的严格见证，保持其中的 $\phi$ 完全不变，只作一次有限探针扰动 $x'=x+\lambda j$，其中

$$
j=J\oplus0_m,\qquad J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\tag{27.19}
$$

$\lambda$ 可取在零的任意充分小邻域中一个实际非零实数。输入 $t$、残量、取向、两个预算的泛函及其质量均不改变。

证明。由定理 27.2，全部 PB 失败给一个系数失败及 (27.16)–(27.18) 的有限严格见证。写 $\phi=\phi_\xi$、$\xi=(w,y)$，则 $w\ne0$。在同一 $\xi$ 上，$x+\lambda j$ 的每份原作用像关于实 $\lambda$ 都是仿射的，因此

$$
p_\delta(\lambda)=B_{\phi_\xi}(R_\delta(x+\lambda j),S_\delta(x+\lambda j))
\tag{27.20}
$$

是处处非负的实多项式，次数至多四。其四次系数来自两份原像的最高次项

$$
A_\delta=((J+\delta H_\sigma(J))w,0),\qquad
C_\delta=(\delta\tfrac32Jw,0).
$$

由于 $H_\sigma(J)=\sigma i\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)/2$，直接乘法有

$$
\begin{gathered}
J_C(J)=\tfrac32J,\qquad
\|Jw\|^2=\|w\|^2,\qquad
\|H_\sigma(J)w\|^2=\tfrac14\|w\|^2,\\
\langle Jw,H_\sigma(J)w\rangle_{\mathbb R}=0,\\
\|A_\delta\|^2=\tfrac54\|w\|^2,\qquad
\|C_\delta\|^2=\tfrac94\|w\|^2,\qquad
\langle A_\delta,C_\delta\rangle_{\mathbb R}
=\delta\tfrac32\|w\|^2.
\end{gathered}
$$

故 (27.20) 的四次系数准确是

$$
\|A_\delta\|^2\|C_\delta\|^2
-\langle A_\delta,C_\delta\rangle_{\mathbb R}^2
=\frac9{16}\|w\|^4>0
\qquad(\delta=1,-1).
\tag{27.21}
$$

这是原像随探针变化的最高次系数，不是删去常数环境像后的预算替代式。两多项式均非零，各自实零点有限。原严格差额

$$
\lambda\longmapsto
|\phi_\xi(L(x+\lambda j))|-\sqrt{p_+(\lambda)}-\sqrt{p_-(\lambda)}
$$

连续，在 $0$ 为正，故在零的某个开邻域内仍严格为正。该开邻域去掉两多项式的有限零点及 $0$ 后非空；任取其中一个有限 $\lambda$，两多项式因非负且不为零而同时严格为正，原差额也仍严格为正。这样一次选择同时支付两根，泛函始终是同一个 $\phi_\xi$。此论证适用于演员轴方向、$m=0$ 及任意奇异环境；没有用渐近序列代替取得的探针。质量零只给零等式，不能成为严格见证。∎

### 27.4 固定输入上平衡残量的值域与二次依赖

**定理 27.4（平衡残量的精确值域／二次条件）。** 固定任意同一 $B,V,D_{\rm env}$ 和一个 $\sigma$，令

$$
T_A=\operatorname{diag}(1,-2),\qquad s=\rho T_A\oplus0_m,\qquad\rho\in\mathbb R.
\tag{27.22}
$$

保持定义 27.1 的 $\mathcal E_0,F$ 及索引族不变。对每个 $\theta$，其系数矩阵准确有形式

$$
\mathscr Q_{\sigma,\rho T_A}(\theta)=
\begin{pmatrix}
A&b_0+\rho b_1\\
(b_0+\rho b_1)^{\mathsf T}&\gamma_0+\rho\gamma_1+\rho^2\kappa
\end{pmatrix},
\tag{27.23}
$$

其中 $A,b_0,b_1,\gamma_0,\gamma_1,\kappa$ 均不依赖 $\rho$，并且

$$
A\succeq0,\qquad b_0\in\operatorname{ran}A,\qquad
q_0:=\gamma_0-b_0^{\mathsf T}A^\dagger b_0\ge0,\qquad
\kappa=(\alpha_+^{-1}+\alpha_-^{-1})\|T_Au\|^2>0.
\tag{27.24}
$$

定义实系数

$$
q_1=\gamma_1-2b_1^{\mathsf T}A^\dagger b_0,\qquad
q_2=\kappa-b_1^{\mathsf T}A^\dagger b_1.
\tag{27.25}
$$

则这个固定输入在残量 (27.22) 下满足全部原 PB，当且仅当对每个 $\theta$ 同时有

$$
\boxed{\qquad
\rho(I-AA^\dagger)b_1=0,\qquad
q_0+\rho q_1+\rho^2q_2\ge0.
\qquad}
\tag{27.26}
$$

对 $\rho\ne0$，第一条准确等价于 $b_1\in\operatorname{ran}A$。若某个索引不满足该值域条件，则同一固定 $B,V,D_{\rm env}$ 的全部非零 $\rho$ 都不能满足全部 PB，并分别具有定理 27.2–27.3 的有限严格正预算见证。这里不对尚未分类的 $q_1,q_2$ 赋予符号，也不据 (27.26) 断言 PB 允许的 $\rho$ 集合为区间。

证明。令 $e_n$ 仍为最后一个坐标向量，置

$$
w_u=(T_Au,0)\in\mathcal H,\qquad
\mathcal Wz=(e_n^{\mathsf T}z)w_u,\qquad
\mathcal M_\delta=\mathcal S_{\delta,0}-\beta_\delta\mathcal R_\delta.
$$

(27.4)–(27.5) 给出准确的残量依赖

$$
\begin{gathered}
\mathcal G_{\rho T_A}=\mathcal G_0+\rho\mathcal W,\qquad
\mathcal S_{\delta,\rho T_A}=\mathcal S_{\delta,0}+\delta\rho\mathcal W,\\
\mathscr L_{\rho T_A}=\mathscr L_0-2\rho\operatorname{Sym}(\mathcal T,\mathcal W).
\end{gathered}
\tag{27.27}
$$

所以 (27.7) 展开为

$$
\begin{gathered}
\mathscr Q_{\sigma,\rho T_A}
=\mathscr Q_{\sigma,0}+\rho(e_n h^{\mathsf T}+h e_n^{\mathsf T})
+\rho^2\kappa e_ne_n^{\mathsf T},\\
h=\sum_{\delta=\pm1}\delta\alpha_\delta^{-1}
     \mathcal M_\delta^{\mathsf T}w_u+2\epsilon\mathcal T^{\mathsf T}w_u,
\qquad
\kappa=\sum_{\delta=\pm1}\alpha_\delta^{-1}\|w_u\|^2.
\end{gathered}
\tag{27.28}
$$

所有转置与像仍取原空间实内积。令 $b_1$ 为 $h$ 的前 $n-1$ 个坐标、$\gamma_1=2e_n^{\mathsf T}h$，并按 (27.23) 分解 $\mathscr Q_{\sigma,0}$，即得全部系数公式。特别是残量只改变最后一行与列，前块 $A$ 无 $\rho$ 依赖；$\|T_Au\|^2=|u_1|^2+4|u_2|^2>0$ 给 $\kappa>0$。

$s=0$ 的全部原 PB 直接复用 §1 的标准零残量结果，不重新证明标准映射的因式分解。由定理 27.2，$\mathscr Q_{\sigma,0}(\theta)\succeq0$ 对全部索引成立。将既有零残量结论代入 (27.9)，便得到 (27.24) 的 $A\succeq0$、$b_0\in\operatorname{ran}A$ 和 $q_0\ge0$。

现在对 (27.23) 使用 (27.9)。其实值域条件为

$$
(I-AA^\dagger)(b_0+\rho b_1)=0.
$$

因 $b_0$ 已在值域内，这准确化成 (27.26) 的第一条。剩下的标量广义 Schur 补准确为

$$
\begin{aligned}
&\gamma_0+\rho\gamma_1+\rho^2\kappa
-(b_0+\rho b_1)^{\mathsf T}A^\dagger(b_0+\rho b_1)\\
&\hspace{25mm}=q_0+\rho q_1+\rho^2q_2,
\end{aligned}
$$

即得第二条与全部 PB 的充要关系。$\rho=0$ 时两条自动成立；任意非零 $\rho$ 时，值域失败已经使系数矩阵非正。定理 27.2–27.3 随即给出所述同一输入上的有限见证。$\kappa>0$ 只属于未消元矩阵的最后对角系数，不能替代对消元后二次系数 $q_2$ 的判断。∎

### 27.5 与固定 P2 的准确交及剩余目标

**推论 27.5（既有 P2 平衡域上的全 PB 表达式）。** 对每个分别固定的 $\sigma$，定义 26.1 的集合准确满足

$$
\begin{aligned}
\mathfrak A_\sigma
=\{(B,V,D_{\rm env},\rho)\in\mathfrak F_\sigma:\ &
\rho(I-AA^\dagger)b_1=0,\\
&q_0+\rho q_1+\rho^2q_2\ge0
\text{ 对每个 }\theta\text{ 成立}\}.
\end{aligned}
\tag{27.29}
$$

其中所有系数均为该份同一输入在定理 27.4 中的系数，不可从不同输入或不同环境度量拼接。更一般的对角标量残量问题中，P2 已在零模耦合秩二、不平衡秩一及秩零非 Schur 平衡分支迫使 $s=0$；其余只须将定理 27.4 与既有平衡分支的准确 P2 区间取交。若同时要求两个取向，则分别形成各自条件再取交，不能删除 $\sigma$ 依赖。

特别地，对任何已在 $\mathfrak F_\sigma$ 中的输入，若某个系数测试失败，定理 27.2–27.3 给出的同一实际输入在每个指定正质量上仍满足全部原 P2，却有同一个原泛函下两笔严格正预算的 PB 严格违反。

证明。固定 P2 的整个有限分类直接取定理 13.1；其中零模秩零的分类与区间直接取定理 8.1。它们已经将可能的非零对角残量准确限制为 (27.22) 及其各自区间，不是此处新增的 P2 结论。在每份被保留的同一输入上，定理 27.4 恰好等价于全部原 PB，故与定义 26.1 合取就是 (27.29)。系数失败时应用定理 27.2–27.3，只选择原探针与原泛函，既不改变输入，也不改变 P2 的任何条件或全称量词，故得到最后的同时实现断言。其余刚性分支由这些既有定理及 §1 的零残量充分性处理。两个取向的断言分别应用同一证明。∎

**约定 27.6（判据的范围与数学来源）。** (27.7)、(27.26)、(27.29) 是连续全称系数族；单位方向和四个有限变分参数仍须全部量化。它们没有成为有限清单，也不是普通 $M_6$ 或 $M_{13}$ 的算子分类、替代可观测量代数或一份已排除的新参数元组。$13$ 是共同实二次型系数矩阵的阶数上界，原算子仍属于 $M_{m+2}(\mathbb C)$，原 $m$ 任意有限，且所有像、平方、Jordan 乘积及泛函都取自该同一完整实现。

本节新增的 $\texttt{repo-derived}$ 应用关系是：在既有共同读取截面上，将两个原 PB 根的变分关系与四个实际 Hermitian 探针坐标、全部环境读取坐标联合齐次化，得到 (27.7) 的充要条件；由其失败取得同一原实现的有限见证；由 (27.21) 保持同一泛函而同时使两笔预算严格为正；并将平衡残量精确保留为 (27.26) 的值域与二次条件。定理 17.2 的截面、同时读取恒等式及全正密度提升、命题 18.1 的压缩平方障碍，以及定理 8.1、13.1 的完整 P2 分类均为直接复用。§§19–25、运输卷定理 12.3 与承载卷定理 41.2、42.2 的既有排除域保持原有范围，不重复证明或作为新增内容。

实 Gram／Cauchy–Schwarz、二阶行列式的变分写法与算术几何平均、实二次型齐次化、有限维谱分解、广义 Schur 补和 Moore–Penrose 逆均为成熟数学。(27.12)、(27.15) 只给出本节承重推导实际消费的完整辅助证明，不作为新的通用定理。广义 Schur 判别准确沿上述 Higham 的 Theorem 1；伪逆的谱定义、最小范数背景沿 §15 的 Penrose 引文，亦见 Higham，[*What Is the Pseudoinverse of a Matrix?*](https://nhigham.com/2023/07/25/what-is-the-pseudoinverse-of-a-matrix/)中 Moore–Penrose 条件及奇异值分解公式。原正泛函与 Gram 背景仍沿 §§5、11、18 的来源。本节不作历史优先权或文献穷尽主张。

对一般输入，尚未判定 (27.26) 全部值域条件与二次不等式的符号分类，也未判定 (27.29) 是否含有任何非零残量。因此原有限类的 $\mathfrak A_\sigma$ 是否为空、特别是剩余域 $\mathfrak R_\sigma$ 上是否每份输入都可取得严格正预算违反，仍为未决；这里没有给出非零残量的全部 PB 模型。已知共同零预算接触的边界继续直接由定理 22.3、23.1 承担。

本节不对未知总响应添加正则性、可加性、齐次性、协变性、单位平移中性、压缩、商或自然性前件，也不把已知 $D_{\rm env}$ 当作它。原一般混合输入、共同实现义务 $\mathcal E_+^D=\mathcal E_-^D$、稳定性目标 $N_\omega(\varepsilon)^2\to0$、完整原 $\mathsf H$／总 $D$ 以及 §§6、15、18、21 的同一递归钉版实际物理来源全文均保持原范围与未决义务。有限矩阵读取与数学探针不供应原实际准备、评价标签、完整菜单、typed 仪器、全部合法历史、CountRead 或全输入／全未来 Return，也不以较强完整 $\mathsf H$ 的分类代替固定输出接口。

## 新增锚（本行以下为后续增补区）
