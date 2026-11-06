# AURIC：原共同自主性供应正活动与完整光滑密度的联合四时诊断（续卷 XII）

> 本卷是普通数学散文的参考输入，未经 Lean kernel 验证。采用 `generic-v1`；既有条目及编号只增不减，后续勘误与增补置于文末追加锚之后。本卷只将原生来源上的综合推导标为 `repo-derived`，不作全球原创或文献优先权主张。

## 1. 同一原生来源与两项结论的读法

本卷沿用 [II][II]、[III][III]、[IV][IV]、[XI][XI] 的同一个原生完整 $89$ 坐标来源族。这四个链接固定其所引正文；原卷内部的来源绑定及假设继续按原义承担。文中以 II、III、IV、XI 标明外卷的章节、条目和公式；无外卷前缀的 §2–4 编号属于本卷。

§2–3 的主要结果是原 N+A 已供应 B，随后直接消费 XI10.3–10.5 的完整 Born/R 结论；不另建 Born 或率分类。§4 保留完整光滑 $\mathscr C_{\rm nat}$ 密度的原地址九联合四时诊断，说明较弱分量约束仍未决定的联合关系。两者的前件不同：§4 的密度不被当作满足 §2 的完整 A 的模型，两个结果也不被拼成同一实际过程。

两项推导都保留同一实际 $\Omega$ 的完整目标、原坐标与资源边界；全数学输入和函数恒等式不授予实际准备或控制权限。下文分别给出完整证明、成熟工具的消费范围及仍须独立供应的实际来源桥梁。

## 2. 原共同自主性供应安全非恒模轨道的正活动

**定义 2.1（只撤去独立 B 的原数学合同）。** 固定 XI 定义 10.1 的同一个 $E,\mathcal K=\mathbb C^E,Q,H_j,U_j$、原复结构与内积。响应仍为全 $\mathbb{CP}^{88}$ 上连续、非负、归一且对全部非零复缩放不变的 $\Pi$，保留一向节点条件 N。A 严格取 [III 假设 177.2][III]：所有原活动对按中心位 $0\to1$ 定向，共用同一对 $\gamma_\pm:D\to[0,\infty)$，其中 $D=\{[a:b]:ab\ne0\}$；两率连续、有限，不依赖块范数、旁观幅度、块号、地址、调用年龄或任何其它完整隐藏过去。全部数学非零输入、全部内部数学时刻的等变性、无跨块移动、单点保持、适定因果纯跳 Markov 族及节点合法接续、同地址连续调用不重抽不复位，逐项保留。这里只不把 III177.3 的 B 列作独立假设。

**引理 2.2（原三坐标截面迫使 N+A 蕴含 B）。** 在定义 2.1 下，每条原安全非恒模局部轨道都满足

$$
\int_0^{10}(\gamma_++\gamma_-)(\ell(t))\,dt>0.
\tag{2.1}
$$

因而原 B 是 N+A 的数学推论，无须添加准备、控制、响应正性或率公式前提。

证明。记 $x=\varphi^{-1}$、$y=\sqrt x$、$c=xy>0$、$\alpha=3\pi/5$，始终使用原 $Q=\begin{pmatrix}x&c\\c&x^2\end{pmatrix}$。以下三个步骤均在同一全域响应内进行。

（一）从原单点保持取得三坐标径向响应。置

$$
u=\varnothing,\quad v=\{1\},\quad w=\{2\},\qquad
W=\operatorname{span}_{\mathbb C}\{e_u,e_v,e_w\}\subset\mathcal K .
\tag{2.2}
$$

由 III (157.2) 及 XI 定义 1.2，$W$ 在地址 $0,1,2$ 下不变；按 $(u,v,w)$ 排列，其投影限制恰为

$$
D_0=\mathcal P_0|_W=\begin{pmatrix}0&0&0\\0&1&0\\0&0&0\end{pmatrix},\quad
T=\mathcal P_1|_W=\begin{pmatrix}x&c&0\\c&x^2&0\\0&0&0\end{pmatrix},\quad
\mathcal P_2|_W=\begin{pmatrix}x&0&c\\0&0&0\\c&0&x^2\end{pmatrix}.
\tag{2.3}
$$

确切地，地址一的 $w$ 和地址二的 $v$ 各只有一个邻位占据，因此都是投影值恰为零的阻塞单点。地址零的所有分量均为单点。没有使用另一套三态矩阵。

令 $F=\Pi_w|_{W\setminus\{0\}}$。A 的单点保持及全时等变性给

$$
F(U_0(t)z)=F(U_1(t)z)=F(z)
\quad(z\in W\setminus\{0\},\ 0\le t\le10).
\tag{2.4}
$$

只去掉 $U_j(t)=e^{i\alpha t}e^{i\alpha t\mathcal P_j}$ 的共同整体相位，便得 $F$ 在 $e^{isD_0}$、$e^{isT}$ 下不变。因 $D_0,T$ 是投影，这两个群均为 $2\pi$ 周期，而 $\alpha[0,10]=[0,6\pi]$，所以不变性覆盖全部实参数，包括逆元。它是函数恒等式，不要求实际执行任意实参数或逆控制。

令 $G$ 为这两个一参数群在 $U(W)$ 中生成的闭子群。有限乘积保持 $F$，连续性使其闭包仍保持 $F$；$G$ 是紧矩阵群。以 $E_{ab}$ 表示此三坐标上的矩阵单位，直接有

$$
\begin{aligned}
K&=[iD_0,iT]=c(E_{uv}-E_{vu}),\\
L&=[iD_0,K]=-ic(E_{uv}+E_{vu}),\\
[K,L]&=-2ic^2(E_{uu}-E_{vv}).
\end{aligned}
\tag{2.5}
$$

三个矩阵张成作用在 $(u,v)$、在 $w$ 上为零的 $\mathfrak{su}(2)$。这里所用的成熟矩阵群闭包事实可直接按乘积极限核对：若相应的一参数群已在 $G$ 中，则

$$
\begin{aligned}
e^{t(X+Y)}&=\lim_{n\to\infty}(e^{tX/n}e^{tY/n})^n,\\
e^{t[X,Y]}&=\lim_{n\to\infty}
 (e^{\epsilon_nX}e^{\epsilon_nY}e^{-\epsilon_nX}e^{-\epsilon_nY})^n,
 \qquad \epsilon_n=\sqrt{t/n},\quad t\ge0 .
\end{aligned}
\tag{2.6}
$$

负 $t$ 交换 $X,Y$，实倍数通过重参数化取得。因此 (2.5) 的全部实线性组合的指数都在 $G$ 中；每个 $SU(2)$ 矩阵可酉对角化为特征值 $e^{i\theta},e^{-i\theta}$，故是一个无迹反 Hermitian 矩阵的指数。于是 $SU(2)_{\{u,v\}}\oplus1_{\{w\}}\subseteq G$。这是标准李代数生成工具在原矩阵上的使用，参见 [D’Alessandro，Theorem 1、§2 (8)–(9)][DA]；只取闭包不变性，不借其物理控制解释。

这个 $SU(2)$ 固定 $w$ 坐标本身，而非只固定它的模。对 $r^2=|a|^2+|b|^2>0$，

$$
\frac1r\begin{pmatrix}\overline a&\overline b\\-b&a\end{pmatrix}
\binom ab=\binom r0 ,
\tag{2.7}
$$

左边矩阵属于 $SU(2)$。先归一化非零输入；若 $w$ 坐标非零，先用全局射影相位把它变为非负实数，再在 $(u,v)$ 上使用 (2.7)。这同时消去了它与前两坐标的相对相位，没有额外商掉一个相对相位。故

$$
\begin{gathered}
h(s)=\Pi_w(\sqrt{1-s}\,e_u+\sqrt s\,e_w),\qquad h:[0,1]\to[0,1],\\
F(ae_u+be_v+\eta e_w)
 =h\!\left(\frac{|\eta|^2}{|a|^2+|b|^2+|\eta|^2}\right).
\end{gathered}
\tag{2.8}
$$

$h$ 连续。N 给 $h(0)=0$；在纯 $e_w$ 输入上，N 消去其它全部坐标，归一化给 $h(1)=1$。前两坐标全零或 $w$ 坐标为零的退化情形也由这些端值及射影不变性包括。$h$ 是这里新得的三坐标径向函数，不将其先认作 XI (10.2) 的旧参考响应 $g$；也没有假设 $h(s)=s$。平方模在 (2.8) 中只是给定酉作用的轨道参数。

（二）径向函数的内部严格正性。复用 XI 引理 10.2 的安全周期主方程机制，但须核对它作用于这里的 $h$。任取 $s_0\in(0,1)$，在原 $(u,w)$ 活动对上取数学输入

$$
a=\sqrt{1-s_0},\quad b=e^{i\theta}\sqrt{s_0},\quad 0<\theta<\pi,\qquad
e=x(1-s_0)+x^2s_0+2c\sqrt{s_0(1-s_0)}\cos\theta\notin\{x,x^2\}.
\tag{2.9}
$$

守恒能量 $e$ 随此区间内的 $\theta$ 严格递减，至多两个相位被排除，故确可选择。III177.5 给出能量 $x,x^2$ 恰对应经过两个局部节点的轨道，所以该地址二轨道安全。记 $(a(t),b(t))=U_2(t)(a,b)$ 的局部代表、$p(t)=|b(t)|^2$，其范数恒为一；原方程为 $b'=i\alpha(ca+(1+x^2)b)$，故 $p'=2\alpha c\operatorname{Im}(\overline a b)$，初时得

$$
p(0)=s_0,\qquad p'(0)=2\alpha c\sqrt{s_0(1-s_0)}\sin\theta>0.
\tag{2.10}
$$

N 在此两坐标输入上消去其余 $87$ 个配置，故 $Y(t)=\Pi_w(a(t)e_u+b(t)e_w)=h(p(t))$ 是 A 中该输入总质量为一的两态配置概率。由 A，

$$
Y'=r_+(t)(1-Y)-r_-(t)Y,\qquad
r_\pm(t)=\gamma_\pm([a(t):b(t)]) .
\tag{2.11}
$$

安全轨道是 $D$ 内紧集，所以两率连续有界；只需此局部有界性。由 $10\alpha=6\pi$ 及 $\mathcal P_2^2=\mathcal P_2$，共同相位和投影指数均回到一，得到 III177.5 的全向量 $U_2(10)=I$。A 的不复位接续使十个单位调用遵循同一方程；等变性遂给 $Y(10)=Y(0)$。若 $h(s_0)=0$，XI (10.5) 的积分因子公式给

$$
0=Y(10)=\int_0^{10}r_+(s)
 \exp\!\left[-\int_s^{10}(r_++r_-)(t)\,dt\right]ds .
\tag{2.12}
$$

指数严格正，被积项非负且连续，故 $r_+\equiv0$；以 $Y(0)=0$ 解余下方程得 $Y\equiv0$。这不需要 B，也不从总活动声称双向率都正。

由 (2.10) 及光滑的原矩阵演化，$p(t)$ 在零时刻的两侧覆盖 $s_0$ 的开邻域；小负时间的像由 $t=10-\varepsilon$ 的同一正向回返代表。因此 $h(s_0)=0$ 迫使 $h$ 在该邻域恒零。零集 $\{s\in(0,1):h(s)=0\}$ 既开又闭；若非空，连通性使它为整个 $(0,1)$，与连续性及 $h(1)=1$ 矛盾。对 $1-Y$ 交换 $r_+,r_-$ 重复同一论证，以 $h(0)=0$ 排除内部的一值，遂有

$$
0<h(s)<1\qquad(0<s<1).
\tag{2.13}
$$

可微的是沿原过程的 $Y$，由主方程保证；没有假设整个 $\Pi$ 或 $h$ 可微、单调、解析或对混合仿射。

（三）同一局部射线在不同块范数下排除零活动。反设某条原安全非恒模轨道 $\ell(t)$ 违反 (2.1)。总活动非负连续，积分为零迫使 $\gamma_+(\ell(t))=\gamma_-(\ell(t))=0$ 对 $0\le t\le10$ 处处成立。所有原活动块都是按中心位 $0,1$ 排列的同一个 $Q$，故可将其局部初向量归一化，写作 $(a(t),b(t))$ 在同一个 $Q$ 下的演化。令

$$
p(t)=|b(t)|^2,\quad
m=\min_{[0,10]}p(t),\quad M=\max_{[0,10]}p(t),\qquad 0<m<M<1 .
\tag{2.14}
$$

严格界分别由整个闭区间上的安全性、连续性和非恒模性给出。对每个 $0<\lambda\le1$，使用原全数学输入域内的单位向量

$$
z_\lambda=\sqrt\lambda\,a(0)e_u+\sqrt{1-\lambda}\,e_v
                    +\sqrt\lambda\,b(0)e_w .
\tag{2.15}
$$

沿原地址二，$(u,w)$ 对的向量是 $\sqrt\lambda(a(t),b(t))$，其局部射线、定向、$\alpha$ 和整个内部时钟都恰为原 $\ell(t)$；$v$ 是 (2.3) 的原阻塞单点，只获整体相位。这里不把幅度块范数 $\lambda$ 认作其未知配置概率质量。

A 用于所有地址和背景的正是同一对局部射线函数。因此改变原块、地址、旁观坐标及 $\lambda$ 后，两率仍逐时为零。无跨块移动使 $w$ 的无条件概率恒定；若该活动块初配置质量为零，亦因块保持而恒零，无须条件化或除以该质量。由等变性及 (2.8)，

$$
\Pi_w(U_2(t)z_\lambda)=h(\lambda p(t))
\quad\hbox{随 }t\hbox{ 恒定},\qquad
h(\lambda M)=h(\lambda m)\quad(0<\lambda\le1).
\tag{2.16}
$$

置 $\rho=m/M\in(0,1)$，逐次取 $\lambda=\rho^n$，得到

$$
h(M)=h(\rho M)=h(\rho^2M)=\cdots
       \longrightarrow h(0)=0 .
\tag{2.17}
$$

这与 $M\in(0,1)$ 及 (2.13) 矛盾，故每条原安全非恒模轨道都满足 B。全部 $z_\lambda$ 仅是 A 已量化的非零数学输入；当 $\lambda\downarrow0$ 只用响应连续性，既不评价零块局部射线或节点率，也不假设率在节点连续或全域有界。∎

**推论 2.3（只供应 B，直接接回原全域 Born 与 R）。** 在定义 2.1 的精确前件下，逐全部 $q\in E$、全部 $z\ne0$，

$$
\Pi_q(z)=\frac{|z_q|^2}{\|z\|^2},\qquad
\Pi_q(z)>0\Longleftrightarrow z_q\ne0,\qquad m_i(z)=t_i(z),\qquad
\Pi_q(z)=m_i(z)\Pi_q(M_i z)\quad(q\in E_i).
\tag{2.18}
$$

最后一式在 $M_i z=0$ 时右端仍按原约定置零，绝不评价 $\Pi(0)$；它特别覆盖原全部有限实际前字 $\chi_a$ 上的 R。

证明。引理 2.2 供应 B，原 N、A 均未改变，故依次直接应用 XI 引理 10.3、XI 定理 10.4、XI 推论 10.5。这包括零配置质量块、部分支撑、特征射线、未来碰节点的非节点输入和零记录投影，范围完全取自既有消费者；不重证赔率／幂函数或 Born 分类，不从 (2.8) 另建选择定理。∎

## 3. 原命题依赖的范围、关系几何与未供应接口

**命题 3.1（旧差方程依赖不等于 B 的全局独立性）。** XI 命题 11.2 关于 XI (10.9) 的依赖陈述只说明该差方程本身在未供应 B 时不能保证严格收缩；它没有给出 N+A 的全域零活动模型。定义 2.1 的完整模型类内，B 由其余条件推出，而 C、最小完整路径律仍不由 N+A 推出。

证明。引理 2.2 在使用 XI (10.9) 之前供应 B，所以完整 N+A 类中的安全非恒模轨道不发生其乘子等于一的情形；XI 命题 11.2 末句明确没有声称全局逻辑最小性。III180.2 的同一个 Born 响应及对称交通族仍满足 N+A+B 而违反 C，原参数及局部归一权重不变。因此本结论不选出最小率、完整跳时律、节点强度版本的逐点值或指定的跨程序耦合；III180–182 和 XI §45 各自保留其原附加合同。∎

**定义 3.2（来源对应与成熟工具范围）。** 本卷 §2 的承重综合为 repo-derived：原三坐标的单点不变性先给 (2.8)，共同局部率再把零活动变成 (2.16) 的缩放等式，与节点连续性矛盾。成熟工具只作为该推导的中间步骤，不申报新的群定理、主方程或最小率机制，不作全球原创或优先权主张。

| 来源 | 此处的精确使用 |
| --- | --- |
| [II100.1][II]；XI 定义 1.1–1.4 | 原 $89$ 维载体、$26+63$ 扇区、唯一 ready、原终端及十一前／七后地址；全射线数学域不授予额外实际准备。 |
| [III157.1–157.2、177.1–177.3][III]；XI 定义 10.1 | 原 $Q,H_j,U_j$、全部分量及单点、N 和未弱化的共同自主 A；(2.3) 的两个阻塞投影值均恰为零。 |
| [III177.5][III]；XI 引理 10.2 | 原全向量十调用回返、节点能量判据及安全紧轨道的积分因子／零集开闭机制；$h$ 与旧 $g$ 不先作等同。 |
| XI 引理 10.3、XI 定理 10.4、XI 推论 10.5、XI 命题 11.2；[III180.2][III] | 已有全坐标 Born/R 消费者、原零质量处理、旧证明依赖的准确范围及非最小对称交通反例。 |
| [D’Alessandro，arXiv:0904.2793v1，Theorem 1、§2 (8)–(9)][DA] | literature-attested 的紧矩阵群李代数生成框架；这里只用 (2.5)–(2.6) 的闭包事实。该文将经典秩条件归于 Jurdjevic–Sussmann；不把其控制可达性移作本原菜单的权限。 |
| [Dürr–Goldstein–Tumulka–Zanghì，quant-ph/0407116v1，§2.3 (15)][DGTZ] | literature-attested 的跳过程增益减损失主方程；积分因子与连通零集是标准初等工具。不使用其预给平方分布的最小率设计来选择未知响应。 |

**定义 3.3（局部几何与完整实际合同）。** 原二坐标射线有 $\mathbb{CP}^1\simeq S^2$ 的三实 Bloch 坐标。写 $d=x-x^2$，原 $Q=(I+n\cdot\sigma)/2$、$n=(2c,0,d)$、$|n|=1$；原局部流沿绕 $n$ 的圆运动，过两个节点的圆由能量 $x,x^2$ 辨认。本卷 §2 的推导另用嵌入原 $\mathbb{CP}^{88}$ 的三复坐标截面：闭包中的 $SU(2)$ 固定第三坐标，其余二坐标的定范数球面给相同响应，比较只余单个径向参数。旁观幅度改变该参数，却不改变同一活动对的局部射线和率；这正是零活动与节点值不相容的关系。三实 Bloch 坐标、三复坐标截面均不推出物理空间三维，也不替代完整 $89$ 坐标模型。

N、原复载体／内积／相位／相干矩阵以及 A 的全数学输入、全内部时间、完整隐藏过去自主性、过程存在和节点接续仍为分别需供应的条件。闭群、乘积极限、相位选择及全部 $z_\lambda$ 都只承担这些数学量词内的函数比较；不新增实际准备、辅助载体、任意酉、分数脉冲、负时间控制或另一实际 $\Omega$。原十调用是同一地址的十个整数调用；局部射影周期 $10/3$ 不成为可执行控制。

数学 R 不供应实际读器、字面报告 $I=b_9(Q_-)$、配置保留、纯更新、同源门事件绑定，或每个实际接缝及真实可读细档案上的同响应条件充分性。这些仍按 XI 假设 6.1、XI 定义 11.3 和 [IV195.1–195.2][IV] 各自的共同切口／实际核合同供应；参考、联合和档案关系不能由矩阵相等或密度唯一性替代。III180.2 的对称交通及 C／最小完整路径律边界保持原义。

全部 $89$ 配置、$26+63$ 扇区、唯一 ready、十一前／七后地址、两个记录切口、$1024$ 旧标签／$2048$ 形式联合标签，以及全部细结果、零、失败、拒绝、停止、告警、返回、参考、联合、更新和档案均保留。全部原合法有限顺序、自适应及并行历史各自仍须满足原义务，不截断长度、不按成功重归一。原可靠有限取得、校准／精度／失败预算、独立来源与驱动、共同实现、物理时钟／能量／$\hbar$ 尺度和复合资源仍须独立的来源桥梁。本结论删去 B 的独立数学前提，不供应实际 A，也不完成同一实际 $\Omega$ 的完整量子起源。

## 4. 完整光滑原生密度的地址九联合四时诊断

**命题 4.1（同边缘下的有限原前缀联合时间缺陷）。** 保留 III 定义 157.1 的整个 $\mathscr C_{\rm nat}$，取 III 定理 165.2 的同一个全域密度

$$
\Pi_q(z)=b_q(z)+\varepsilon c_qH(z),\qquad
H=h_{\rm sm},\quad 0<\varepsilon<1,\quad
H(z)=\frac12\prod_{s\subseteq O}\eta(u_s(z)),\qquad
u_s(z)=\frac{\kappa_s^2|a_s(z)|^2-\|v_s(z)\|^2}{\|z\|^2}.
\tag{4.1}
$$

这里 $O=\{1,3,5,7,9\}$，$a_s,v_s,\kappa_s,c_q,\eta$ 均为 III (164.3)、III (164.7)、III (164.10)、III (165.1) 的原定义。其可容许性直接复用 III 定理 165.2：全部 $89$ 个复坐标、十一组原 Hamiltonian、每个单点及二维支撑分量、每个非零复输入、全部非零复缩放和内部 $t\in[0,1]$ 的分量方程同时保留；未把密度换成有限次、径向或仅代码上的函数。

存在同一个有限正向原字 $a\in\mathsf W_{11}$，不依赖 $\varepsilon$，使
$H(\chi_a)>0$ 而 $H(K_9^k\chi_a)=0$ 对 $k=1,2,3$ 同时成立。对四个合法程序 $\mathsf R(a\,9^k,\emptyset)$（$k=0,1,2,3$），$\emptyset$ 表示空后读字，令 $J_k$ 为另供读取前条件律 III (174.1) 并按原不变配置字面报告所定义的直接联合描述 III (175.7)。对于原已读事件

$$
\mathcal E_*=\{I=0,\ W=1000000000\},
\qquad
J_k(\mathcal E_*)=\Pi_{\varnothing}(K_9^k\chi_a),
\tag{4.2}
$$

有严格残差

$$
\begin{aligned}
J_3(\mathcal E_*)+x^2J_1(\mathcal E_*)
 -J_0(\mathcal E_*)-x^2J_2(\mathcal E_*)
 &=-\varepsilon H(\chi_a)<0,\\
\frac{J_3(\mathcal E_*)+x^2J_1(\mathcal E_*)}{1+x^2}
-\frac{J_0(\mathcal E_*)+x^2J_2(\mathcal E_*)}{1+x^2}
 &=-\frac{\varepsilon H(\chi_a)}{1+x^2}.
\end{aligned}
\tag{4.3}
$$

同一四个联合描述的 $I$、$W$ 两个边缘却分别等于参考平方边缘，均满足相应四时恒等式。这里的读取前律及报告绑定是明确的附加条件，其对同一实际 $\Omega$ 的采用仍为 **ASSUMED-UNVERIFIED**；本命题仅陈述该绑定下的条件结论。

证明。直接使用 III (164.17) 的 $z_*=\sum_{s\subseteq O}w_s/\sqrt{32}$。III 式 (164.4)–(164.5) 已给互不相交的 $32$ 个扇区覆盖全部 $89$ 坐标、$\|z_*\|=1$ 且每个坐标非零；III 式 (165.6) 给 $H(z_*)>0$。只为计算原地址九的作用，在同一载体内置

$$
g_d=\sum_{r\subseteq\{2,4,6\}}
 x^{3-|r|}(-y)^{|r|}|r\cup d\rangle
\quad(d=\varnothing,\{8\},\{9\}),\qquad
g_0:=g_{\varnothing},\quad g_8:=g_{\{8\}},\quad g_9:=g_{\{9\}}.
\tag{4.4}
$$

这三个向量支撑不交，由 $x^2+y^2=1$ 正交归一。于是
$w_{\varnothing}=xg_0-yg_8$、$w_{\{9\}}=g_9$，而
$w_\perp=yg_0+xg_8$ 是空奇位扇区中与 $w_{\varnothing}$ 正交的单位向量。这些坐标乘积不引入物理张量因子。

原 $\mathcal P_9$ 在 $(g_0,g_9)$ 上恰为 III (138.2a) 的
$\left(\begin{smallmatrix}x&xy\\xy&x^2\end{smallmatrix}\right)$；
由于 $b_8=1,b_{10}=0$，$\mathcal P_9g_8=0$。地址九不改变其余奇位，故 $z_*$ 中只有 $s=\varnothing,\{9\}$ 两项能在作用后进入 $R_{\varnothing}$。记

$$
\delta_k=\zeta^k-1,\qquad
D=x^2+xy=x(x+y),\quad L=xD,\quad V=yD.
$$

将这两项和阻塞的 $g_8$ 一起代入原
$K_9^k=\zeta^k[I+\delta_k\mathcal P_9]$，精确得到

$$
R_{\varnothing}K_9^kz_*
=\frac{\zeta^k}{\sqrt{32}}
 \bigl[(1+\delta_kL)w_{\varnothing}
       +\delta_kVw_\perp\bigr].
\tag{4.5}
$$

$xy<x$ 和 $x^2+x=1$ 给 $0<D<1$、$0<L<x<1$，所以

$$
|a_{\varnothing}(K_9^kz_*)|
=\frac{|1-L+L\zeta^k|}{\sqrt{32}}\le\frac1{\sqrt{32}},
\qquad
\|v_{\varnothing}(K_9^kz_*)\|
=\frac{|\delta_k|xy(x+y)}{\sqrt{32}}.
\tag{4.6}
$$

对 $k=1,2,3$，$|\delta_k|^2$ 分别为 $2+x,3+x,x^2$，故 $|\delta_k|\ge x$。由 $y(x+y)=xy+x>x^2$ 及 $\kappa_{\varnothing}=x^4$，

$$
\|v_{\varnothing}(K_9^kz_*)\|
\ge\frac{x^2y(x+y)}{\sqrt{32}}
>\frac{x^4}{\sqrt{32}}
\ge\kappa_{\varnothing}|a_{\varnothing}(K_9^kz_*)|.
\tag{4.7}
$$

因此三个 $u_{\varnothing}(K_9^kz_*)$ 都严格为负，令乘积 $H$ 为零。另一方面，III (165.6) 给每个 $u_s(z_*)=x^{2m_s}/32>0$。连续性及非零复缩放不变性使

$$
\mathcal U=\{[z]:H(z)>0\}
 \cap\bigcap_{k=1}^3\{[z]:u_{\varnothing}(K_9^kz)<0\}
\tag{4.8}
$$

成为包含 $[z_*]$ 的非空射影开集。复用 III (144.12) 的唯一 ready 原轨道稠密性，存在实际有限正向字 $a$ 满足 $[\chi_a]\in\mathcal U$。这个同一 $a$ 适用于每个 $0<\varepsilon<1$；不要求精确制备 $z_*$。$R_{\varnothing}$ 只是验证全域函数取值的数学投影，没有将实际载体限制为空奇位扇区。

事件 $\mathcal E_*$ 的十位 $W$ 依原顺序是 $(b_{-1},\ldots,b_8)$，再与 $I=b_9=0$ 合起来，恰指定原配置 $q=\varnothing$。在读取前律、$Q_+=Q_-$ 和立即调用旧字面终端的绑定下，普通推前给 (4.2)，不需要新读口或隐藏轨迹观察。

最后仅消费 [II][II] (86.6)、II 命题 88.1 的两谱多项式计算：原全载体上的 $\mathcal P_9$ 是投影，故
$K_9=\zeta[(I-\mathcal P_9)+\zeta\mathcal P_9]$，每个参考平方坐标沿整数次幂只有 $1,\zeta^k,\zeta^{-k}$ 三种频率。已有多项式

$$
R(s)=(s-1)(s-\zeta)(s-\zeta^{-1})
=s^3-x^2s^2+x^2s-1
$$

消去这三种频率，所以 $B_k:=b_{\varnothing}(K_9^k\chi_a)$ 满足
$B_3+x^2B_1-B_0-x^2B_2=0$。这是对已核对原 $\mathcal P_9$ 的代入，不把 II 定理 86.1 的十三维全上下文重建结论搬到另一作用域。因 $c_{\varnothing}=1$ 且后三个 $H$ 为零，(4.3) 随即成立。III 式 (175.8) 同时给每个 $k$ 的两个边缘等于 $t_i(K_9^k\chi_a)$ 与 $\|N_wK_9^k\chi_a\|^2$；它们各为二次型，故仍被同一个 $R$ 消去。∎

**说明 4.2（实际来源、资源与完整目标的边界）。** 本应用为 repo-derived 的原生联合时间诊断：完整分量守恒、光滑性、节点和归一化本身未迫使 (4.3) 的联合残差为零，两个分别正确的边缘亦未供应该关系。复用的数学内容归属于 II (86.6)、II 命题 88.1，III (144.12)、III (164.3)–(164.7)、III 定理 165.2、III (165.6) 及 III §175；没有新增一般调和重建、选择机制或全球文献优先权主张。

原实际过程另有更强的既定前件。III145 和 [IV][IV] §275 已指定平方电流最小率；保留 IV (276.1) 的整个原生补偿子、路径和档案合同时，IV279.1–281.1 已固定完整原生律，排除这里正 $H$ 前缀上的改变密度。这里没有从无平方前提推出该补偿子。另在 $k=0$，若同时保留 III138.2(2) 的旧终端条件律及原纯投影后继，III (175.7) 强制 $J_{\rm proj}(\mathcal E_*)=b_{\varnothing}(\chi_a)$，而本读取前律与不变配置字面报告给 $J_H(\mathcal E_*)=b_{\varnothing}(\chi_a)+\varepsilon H(\chi_a)$；两项冲突合同不能同时实现。III 定义 166.3、III 命题 175.2 的共同过程与更细可读历史边界仍在；[XI][XI] 定义 23.1、XI 定理 37.1 的完整 $\mathsf A_R$ 消费者及其全部 R 前件亦未因此减弱。尚缺的是在同一原实际 $\Omega$ 上独立说明为何应满足所需联合时间关系，并接到实际报告／过程的来源桥梁。

$a$ 是存在性的有限前缀，未合成见证字，未给有效字长界、统一正间隙、噪声保证、独立重复／IID／采样合同或有限样本证书。四个程序各只在 $a$ 后增加至多三次完整九号脉冲，随后作原保留读和空后字终端；它们的调用档案不同。(4.3) 的正权平均只是单个报告事件的数值关系，不取得免费随机选程序，也不等同完整历史或档案。全部 $89$ 配置与 $26+63$ 扇区、唯一 ready、十一前／七后地址、两个原切口、全细标签及零质量、失败／拒绝／停止／告警／返回、参考／联合／档案和原取得成本均保留；不加入分数脉冲、反馈、复位、后选择或 $610$ 维读器。四个确定性程序仅是完整目标内的一个合法子族，不替代全部合法有限顺序、自适应和并行历史的来源义务。基本关系定义、简单几何、复结构、组合、动力学及量子公理在整个原实际来源上的推导仍须各自取得；本应用未减少这些原始前提，不供应未改实际来源的反模型，不作 Lean 内核验证或完整量子起源完成声明。

[II]: https://github.com/the-omega-institute/trureturing/blob/03150b25ffad5ced1bebdca2efc8c05b484c1eca/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md
[III]: https://github.com/the-omega-institute/trureturing/blob/03150b25ffad5ced1bebdca2efc8c05b484c1eca/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md
[IV]: https://github.com/the-omega-institute/trureturing/blob/03150b25ffad5ced1bebdca2efc8c05b484c1eca/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md
[XI]: https://github.com/the-omega-institute/trureturing/blob/03150b25ffad5ced1bebdca2efc8c05b484c1eca/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md
[DA]: https://arxiv.org/html/0904.2793v1
[DGTZ]: https://arxiv.org/html/quant-ph/0407116v1

## 追加锚（本行以下为增补区）
