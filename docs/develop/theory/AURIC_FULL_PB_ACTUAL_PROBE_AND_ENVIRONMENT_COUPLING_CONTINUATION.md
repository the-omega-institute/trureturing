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
