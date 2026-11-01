# AURIC：量子起源的关系公理候选

## 共同复相位、唯一本体与正归一读出

定义、定理与纸面证明　v58.0

2026 年 11 月 1 日　Asia/Singapore

> **转换者注（原稿及归属）**：以下正文完整转换自作者提供的 V58 TeX。原稿的“本轮”、来源阅读、历史 HEAD、取得时点、生产方法、独立审读及“未修改项目仓库”等报告均归原作者，不是本转换者的行为报告。数学断言保留；转换者的限定另以具名注释相邻列出。固定源为 48,373 UTF-8 字节，SHA-256：
>
> `1ffde2d341f7fc32` `d63975c581b85b4e` `a208a40a6c5f401d` `2a3d75fca6f60a69`。

<details>
<summary>原作者的 TeX 编译、字体、PDF 元数据、页眉与编号设置（逐字保留）</summary>

<code>% !TeX program = x<wbr>elatex</code><br>
<code>% Compile twice. D<wbr>efine AURICFontPat<wbr>h if the CJK fonts<wbr> are not installed<wbr>.</code><br>
<code>&#92;documentclass[11p<wbr>t,a4paper]{article<wbr>}</code><br>
<code>&#92;usepackage[margin<wbr>=23mm,headheight=1<wbr>6pt]{geometry}</code><br>
<code>&#92;usepackage{fontsp<wbr>ec}</code><br>
<code>&#92;ifdefined&#92;AURICFo<wbr>ntPath</code><br>
<code> &#92;setmainfont[Path<wbr>=&#92;AURICFontPath,Bo<wbr>ldFont=NotoSerifCJ<wbr>Ksc-Bold.otf,</code><br>
<code> ItalicFont=NotoSe<wbr>rifCJKsc-Regular.o<wbr>tf,BoldItalicFont=<wbr>NotoSerifCJKsc-Bol<wbr>d.otf]{NotoSerifCJ<wbr>Ksc-Regular.otf}</code><br>
<code>&#92;else</code><br>
<code> &#92;IfFontExistsTF{N<wbr>oto Serif CJK SC}{</code><br>
<code> &#92;setmainfont[Ital<wbr>icFont=Noto Serif <wbr>CJK SC,BoldItalicF<wbr>ont=Noto Serif CJK<wbr> SC Bold]{Noto Ser<wbr>if CJK SC}</code><br>
<code> }{&#92;setmainfont[Bo<wbr>ldFont=FandolSong-<wbr>Bold.otf,ItalicFon<wbr>t=FandolSong-Regul<wbr>ar.otf,</code><br>
<code> BoldItalicFont=Fa<wbr>ndolSong-Bold.otf]<wbr>{FandolSong-Regula<wbr>r.otf}}</code><br>
<code>&#92;fi</code><br>
<code>&#92;setmonofont{Latin<wbr> Modern Mono}</code><br>
<code>&#92;XeTeXlinebreakloc<wbr>ale &quot;zh&quot;</code><br>
<code>&#92;XeTeXlinebreakski<wbr>p=0pt plus 1pt</code><br>
<code>&#92;usepackage{amsmat<wbr>h,amssymb,amsthm,m<wbr>athtools,bm}</code><br>
<code>&#92;usepackage{bookta<wbr>bs,array,tabularx,<wbr>enumitem,fancyhdr,<wbr>xcolor,needspace}</code><br>
<code>&#92;definecolor{auric<wbr>blue}{RGB}{24,53,7<wbr>9}</code><br>
<code>&#92;usepackage[unicod<wbr>e,colorlinks=true,<wbr>linkcolor=auricblu<wbr>e,urlcolor=auricbl<wbr>ue,citecolor=auric<wbr>blue]{hyperref}</code><br>
<code>&#92;hypersetup{pdftit<wbr>le={AURIC：关系公理、共同复<wbr>相位与量子结构重构},</code><br>
<code>pdfauthor={AURIC r<wbr>esearch continuati<wbr>on},</code><br>
<code>pdfsubject={Real C<wbr>lifford atoms, cen<wbr>tral phase sectors<wbr>, one fixed ontic <wbr>state, positive ef<wbr>fects, Born repres<wbr>entation and unita<wbr>ry histories}}</code><br>
<code>&#92;newcommand{&#92;R}{&#92;m<wbr>athbb R}</code><br>
<code>&#92;newcommand{&#92;C}{&#92;m<wbr>athbb C}</code><br>
<code>&#92;newcommand{&#92;HH}{&#92;<wbr>mathcal H}</code><br>
<code>&#92;newcommand{&#92;A}{&#92;m<wbr>athcal A}</code><br>
<code>&#92;newcommand{&#92;B}{&#92;m<wbr>athcal B}</code><br>
<code>&#92;newcommand{&#92;E}{&#92;m<wbr>athcal E}</code><br>
<code>&#92;newcommand{&#92;Cl}{&#92;<wbr>operatorname{Cl}}</code><br>
<code>&#92;newcommand{&#92;Tr}{&#92;<wbr>operatorname{Tr}}</code><br>
<code>&#92;newcommand{&#92;rank}<wbr>{&#92;operatorname{ran<wbr>k}}</code><br>
<code>&#92;newcommand{&#92;Span}<wbr>{&#92;operatorname{spa<wbr>n}}</code><br>
<code>&#92;newcommand{&#92;id}{&#92;<wbr>operatorname{id}}</code><br>
<code>&#92;newcommand{&#92;sa}{&#92;<wbr>mathrm{sa}}</code><br>
<code>&#92;newcommand{&#92;ket}[<wbr>1]{&#92;lvert#1&#92;rangle<wbr>}</code><br>
<code>&#92;newcommand{&#92;bra}[<wbr>1]{&#92;langle#1&#92;rvert<wbr>}</code><br>
<code>&#92;newcommand{&#92;proj}<wbr>[1]{&#92;ket{#1}&#92;bra{#<wbr>1}}</code><br>
<code>&#92;newcommand{&#92;repo}<wbr>[2]{&#92;href{https://<wbr>github.com/the-ome<wbr>ga-institute/trure<wbr>turing/blob/3d4c9c<wbr>5015546c3d0ea44d3c<wbr>af71ba02b2d0d4a9/d<wbr>ocs/develop/theory<wbr>/#1}{#2}}</code><br>
<code>&#92;theoremstyle{defi<wbr>nition}</code><br>
<code>&#92;newtheorem{defini<wbr>tion}{定义}[section]</code><br>
<code>&#92;newtheorem{axiom}<wbr>[definition]{公理组}</code><br>
<code>&#92;newtheorem{theore<wbr>m}[definition]{定理}</code><br>
<code>&#92;newtheorem{propos<wbr>ition}[definition]<wbr>{命题}</code><br>
<code>&#92;newtheorem{coroll<wbr>ary}[definition]{推<wbr>论}</code><br>
<code>&#92;newtheorem{remark<wbr>}[definition]{说明}</code><br>
<code>&#92;renewcommand{&#92;pro<wbr>ofname}{证明}</code><br>
<code>&#92;renewcommand{&#92;abs<wbr>tractname}{摘要}</code><br>
<code>&#92;renewcommand{&#92;ref<wbr>name}{固定来源与阅读范围}</code><br>
<code>&#92;setlength{&#92;parind<wbr>ent}{1.8em}</code><br>
<code>&#92;setlength{&#92;parski<wbr>p}{2pt}</code><br>
<code>&#92;setlength{&#92;emerge<wbr>ncystretch}{3em}</code><br>
<code>&#92;setlist{nosep,lef<wbr>tmargin=2em}</code><br>
<code>&#92;pagestyle{fancy}&#92;<wbr>fancyhf{}</code><br>
<code>&#92;fancyhead[L]{&#92;sma<wbr>ll AURIC：关系公理与量子结构<wbr>重构}</code><br>
<code>&#92;fancyhead[R]{&#92;sma<wbr>ll v58 / 2026-11-0<wbr>1}</code><br>
<code>&#92;fancyfoot[C]{&#92;the<wbr>page}</code><br>
<code>&#92;allowdisplaybreak<wbr>s[2]</code><br>

</details>

## 摘要

本文把前轮预设的复 Hilbert 空间、Born 形式和酉门，改写为一套明确的关系结构重构条件。
起点为实三轴 Clifford 原子、不同原子的对易复合、同一效果的正归一可加响应，
以及固定本体读出的相对复定向中心确定性。一个原子的体积元给中心复单位；
$N$ 个原子的实张量代数精确分成 $2^{N-1}$ 个复矩阵扇区。
完整效果响应的极端性足以选定一个扇区，但仅有一个全局向量并不足够。
在唯一固定循环向量上，连接树各边的中心线性关系若为零残差，
该关系就传播到整个循环表示，得到通常的复矩阵复合。
近似胶合给中心坏质量、原代数效果概率偏差及完整载体纯态迹距离的不同误差界。
正可加响应产生密度矩阵与 Born 形式，GNS 产生一个固定本体向量，
有限闭合关系自同构产生酉实现；另给内部 ready 接口和正交记录时得到完全正仪器。
文中保留实线性、正锥、完整效果、共同定向与实际控制等前件，
不把局部球面、一个向量或单增门词误当作全量子论的充分原因。
这是一套可证明的候选公理化与公理依赖分析，尚非最小性或物理必然性的证明。

<a id="section-1"></a>

## 1 结论的位置：能进一步重构，尚不能取消全部结构假设

可以得到一组比直接规定“复振幅、Born 法则、酉门”更偏向关系结构的公理。
本轮最有用的推进是把共同复相位的来源单独证明：

$$
\boxed{\begin{gathered}
\text{局部实三轴关系}\ \Longrightarrow\ \text{局部中心复单位};\\
\text{固定本体的中心关系相容}\ \Longrightarrow\ \text{共同复矩阵复合};\\
\text{正归一粗粒化相容}\ \Longrightarrow\ \text{密度态与平方读出}.
\end{gathered}}
$$

这里“更基础”指更少直接使用量子态空间的表象概念，而不是已证明假设数量最少。
每组公理含有实质条件；尤其三轴 Clifford 乘法并非裸二元逻辑的同义词。
全篇采用同一个预先选定的本体响应，随后构造一个固定 $\Omega$。
完整观察者态为 $\Psi_k=U_k\cdots U_1\Omega$；环境、程序、记忆与预测均属同一载体，
局部读口只是内部关系的限制，不重新定义一个外部本体。

项目本轮固定提交为
`3d4c9c5015546c3d0ea44d3caf71ba02b2d0d4a9`。

唯一活动 HEAD 获取于新加坡时间 2026-11-01 01:27:43.117771 完成。
相对 v57 的 `30a086a…`，完整差分为 32 个提交、20 个路径；
未截断的理论树有 1119 个文件，理论目录仅三项变化。
真正新增涉及 CDSO 连接费用、K-bonacci 制备成本和 token 图奇圈。
本轮主线使用的 V30、V37、V47、V48、V52、$\Omega$、Quantum IV 和 RRO 均未改变。
V30 已有 GNS，V47 已有正核及平方权重，V48 已有单原子 Clifford 与图定向拼接。
本文不把这些旧结果再次称为新发现。〔[1](#ref-head), [2](#ref-v30), [4](#ref-v47), [5](#ref-v48), [6](#ref-omega)〕

本轮明确补出的主线是多原子实张量的中心扇区分类、固定本体上的胶合传导、
中心确定性与整体纯性的关系、以及近似胶合的读出误差界。
这是标准代数工具在当前问题中的推论与组织，不作数学史首次发现声明。

<a id="section-2"></a>

## 2 四组候选公理与它们实际承担的工作

#### 定义 2.1（实关系代数、效果和唯一响应）

关系的线性组合先取实系数，关系复合采用有单位的结合乘法。
$*$ 为实线性反对合，满足 $(ab)^*=b^*a^*$。
在下述有限代数中，以有限和 $\sum_j a_j^*a_j$ 定义正锥，
并令

$$
\mathcal{E}(\mathcal{A})=\{E=E^*: E\succeq0,\ 1-E\succeq0\}.
$$

它们是所声明的效果。一个固定准备的响应是单个函数
$p:\mathcal{E}(\mathcal{A})\to[0,1]$。这里尚未把 $p$ 写成平方振幅。

<a id="ax:R"></a>

#### 公理组 2.2（R：线性三轴原子及对易复合）

每个原子 $r$ 有三个自伴二值关系 $X_r,Y_r,Z_r$，满足

$$
X_r^2=Y_r^2=Z_r^2=1,\qquad
X_rY_r=-Y_rX_r,\quad Y_rZ_r=-Z_rY_r,\quad Z_rX_r=-X_rZ_r.
$$

(R)

不同原子的生成元对易。$\mathcal{A}_N$ 是仅由这些关系得到的通用实含幺 $*$ 代数，
没有另加关系；整个模型取有限 $\mathcal{A}_N$，或它们按 $a\mapsto a\otimes1$
递增后的范数完备化。范数取下文有限矩阵块的最大算子范数。

这组条件也可写为：给一个正定实三维关系空间，线性映射
$v\mapsto B(v)$ 满足 $B(v)^*=B(v)$ 及 $B(v)^2=\|v\|_2^2\,1$。
对 $v+w$ 极化得到
$B(v)B(w)+B(w)B(v)=2(v\cdot w)1$。
因此“正交”对应反对易，而不是三个互相排斥的同时测量结果。
实线性、正定二次几何、三轴数目、结合复合和跨原子对易都是输入。
它们可用来解释量子表象，却尚未从“关系存在”一句话中推出。〔[5](#ref-v48), [9](#ref-clifford)〕

<a id="ax:P"></a>

#### 公理组 2.3（P：完整效果的正归一粗粒化响应）

同一个固定响应 $p$ 对全部声明效果满足

$$
p(1)=1,\qquad p(E+F)=p(E)+p(F)\quad(E,F\succeq0,\ E+F\preceq1).
$$

(P)

同一效果在不同菜单中具有相同响应。对递增原子数，
$p_{N+1}(E\otimes1)=p_N(E)$。所给正性是整个关系代数的正性，
不限于积效果上的非负性。

这是一项关于读出相容性的实质公理。允许非对易的 $E,F$ 相加，
是因为 $\{E,F,1-E-F\}$ 本身是一组效果菜单，并非给不同尖锐测量
预先指定共同确定答案。完整效果域比有限实际菜单强；
若只有有限菜单，必须另外证明其实际关系和正性覆盖足以支持扩张。〔[6](#ref-omega), [10](#ref-busch)〕

<a id="ax:C"></a>

#### 公理组 2.4（C：固定本体的相对复定向中心确定性）

定义

$$
J_r=X_rY_rZ_r,\qquad s_r=-J_1J_r\quad(r\ge2).
$$

要求固定响应在这些中心二值关系上确定：

$$
p\!\left(\frac{1+s_r}{2}\right)\in\{0,1\}.
$$

(C)

有限原子时只要求相应有限组；无限时对每个有限编号成立。

下文证明这些量确实是中心投影。该公理比整个响应不可凸分解弱；
后者足以推出它。“只有一个实际 $\Omega$”则不能推出它。
这里对齐的是 $\mathbb Z_2$ 型的相对复结构定向，
不是把所有连续 $U(1)$ 振幅相位或回路相位都设为零。
若局部正反定向已被校准固定，标准同向复合还须该确定值全为一。
若定向仅为坐标选择，可以按实际确定符号重新标记局部轴。

> **转换者注（对象类型）**：这里的中心投影是 $(1\pm s_r)/2$；$s_r$ 本身是中心自伴对合，$J_r$ 是中心斜自伴复单位。原句与原断言保留。

<a id="ax:G"></a>

#### 公理组 2.5（G：实际闭合过程保持完整关系）

每个允许的有限闭合步骤，在 C 选定并校准后的有限关系商块
（下文记为 $\mathcal{B}_M$）上为保持单位、
乘法、伴随及已选中心复结构的可逆自同构，其他内部原子保持不变。
若从未胶合的 $\mathcal{A}_M$ 描述该步骤，还须保持所选扇区理想，
使其能下降到这个商块；仅保持参考 $J_1$ 不足以保证这一点。
实际门词按内部程序逐步追加。用于保存记录、控制和辅助准备的容量若被使用，
也必须属于同一整体并明确供应。

G 不预先假设 Hilbert 酉矩阵；后文从有限矩阵 $*$ 自同构证明酉实现。
它也不声称每一个数学自同构都已进入原生门菜单。
实际控制的可达性、误差和费用是另一项问题。

<a id="section-3"></a>

## 3 一个原子为什么给出复数与受限三维

<a id="thm:local"></a>

#### 定理 3.1（局部中心复结构与矩阵表示）

一个 R 原子的 $J=XYZ$ 满足

$$
J^2=-1,\qquad J^*=-J,\qquad [J,a]=0\quad(a\in\mathcal{A}_1),
$$

并且

$$
XY=JZ,\quad YZ=JX,\quad ZX=JY,\quad Y=JXZ.
$$

有实 $*$ 代数同构

$$
\boxed{\mathcal{A}_1=\operatorname{Cl}_{3,0}\cong M_2(\mathbb{C})_{\mathbb{R}}.}
$$

**证明。**

逆转三个生成元需要三次交换，故
$J^2=-X^2Y^2Z^2=-1$，$J^*=ZYX=-J$。
任一生成元穿过另外两个产生两次负号，所以 $J$ 中心。
例如 $JZ=XY$，$JXZ=Y$，其余同理。
所有词可归约到
$1,X,Y,Z,XY,YZ,ZX,J$ 的实张成。
取 Pauli 表示

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

上述八个词映到 $I,X,Y,Z,iZ,iX,iY,iI$，实线性无关并张成
$M_2(\mathbb{C})$。因此表示恰为同构，且 $*$ 对应矩阵伴随。

□

这不是先规定复振幅再更名：复单位可以由实关系乘积 $XYZ$ 在内部生成。
但其原因正是已声明的 Clifford 复合律。此定理及其旋量解释在项目 V48
已经给出。〔[5](#ref-v48)〕

<a id="cor:bloch"></a>

#### 推论 3.2（归一正关系的三轴球与纯态边界）

在一个复矩阵原子中，任意正迹一矩阵恰可写成

$$
\rho=\frac{I+xX+yY+zZ}{2},\qquad x^2+y^2+z^2\le1.
$$

它秩一当且仅当等号成立。

**证明。**

$I,X,Y,Z$ 构成自伴矩阵实基。反对易关系给
$(xX+yY+zZ)^2=(x^2+y^2+z^2)I$，故 $\rho$ 的特征值为
$(1\pm\sqrt{x^2+y^2+z^2})/2$。正性、迹一与秩一条件随即得到。

□

因此受限三维来自自伴部去掉一个归一标量后的三个实系数；
纯态球面只有两个局部实自由度。它不等于物理空间已经被证明为三维，
也不把高维本体的全部信息无损压缩成三个数。

<a id="section-4"></a>

## 4 多原子为何还需要共同复定向

<a id="thm:sectors"></a>

#### 定理 4.1（全部相对定向扇区的分类）

对 $N\ge1$，R 公理给

$$
\mathcal{A}_N=\operatorname{Cl}_{3,0}^{\otimes_{\mathbb{R}}N}.
$$

各 $s_r=-J_1J_r$ 是中心自伴对合，满足 $J_r=s_rJ_1$。
令 $\epsilon=(\epsilon_2,\ldots,\epsilon_N)\in\{\pm1\}^{N-1}$，

$$
e_\epsilon=\prod_{r=2}^{N}\frac{1+\epsilon_rs_r}{2}.
$$

则 $e_\epsilon$ 是非零、两两正交、和为一的中心投影，且

$$
\boxed{\mathcal{A}_N\cong
\bigoplus_{\epsilon\in\{\pm1\}^{N-1}}M_{2^N}(\mathbb{C})_{\mathbb{R}}.}
$$

(4.1)

**证明。**

每个 $J_r$ 与本原子及其他原子对易，故为全代数中心元。
由 $J_r^*=-J_r$、$J_r^2=-1$ 得
$s_r^*=s_r$、$s_r^2=1$ 和 $J_1s_r=J_r$。
相应二值谱投影的乘积给中心正交分解。

固定 $\epsilon$，在 $e_\epsilon\mathcal{A}_N$ 中以 $J_1$ 作为复数 $i$。
由 $Y_r=\epsilon_rJ_1X_rZ_r$，其中约定 $\epsilon_1=1$，
全部词落在

$$
\left\{\prod_{r=1}^{N}X_r^{a_r}Z_r^{b_r}:
a_r,b_r\in\{0,1\}\right\}
$$

这 $4^N$ 个词的复张成中。
另一方面，在 $(\mathbb{C}^2)^{\otimes N}$ 上令
$X_r=\sigma_x^{(r)}$、$Z_r=\sigma_z^{(r)}$、
$Y_r=\epsilon_r\sigma_y^{(r)}$。
则 $J_1=iI$、$J_r=\epsilon_riI$，指定的 $e_\epsilon$ 映为 $I$，
其余扇区映为零。这 $4^N$ 个词映为线性独立的 Pauli 张量词，
张成 $M_{2^N}(\mathbb{C})$。故每块恰为所述矩阵代数，且均非零。
中心分解给结论。

□

即使尚未胶合，$J_1$ 也已能为整个代数提供一个参考复结构。
缺少的不是“完全没有复数”，而是仍有 $2^{N-1}$ 个
相对复定向的中心扇区。通常的单一复矩阵复合选择其中一个。
这些扇区是可由中心效果区分的额外经典参数。

<a id="thm:quotient"></a>

#### 定理 4.2（共同中心线性关系选出复张量）

施加 $J_r=J_1$，即 $s_r=1$，并令
$e_+=\prod_{r=2}^{N}(1+s_r)/2$。则

$$
\boxed{\begin{aligned}
\mathcal{A}_N/\langle J_r-J_1:r\ge2\rangle
&\cong e_+\mathcal{A}_N\\
&\cong M_{2^N}(\mathbb{C})_{\mathbb{R}}.
\end{aligned}}
$$

以 $J_1=i$ 后，此代数等同于
$M_2(\mathbb{C})^{\otimes_{\mathbb{C}}N}$。

**证明。**

$J_r-J_1=J_1(s_r-1)$ 且 $J_1$ 可逆。
全正扇区上这些差为零；其他任一扇区有某个 $\epsilon_r=-1$，
于是 $e_\epsilon(s_r-1)=-2e_\epsilon$，该整个扇区属于所取理想。
商只留下全正块，应用定理 [4.1](#thm:sectors) 即得。

□

这一步把“关系连接关系”具体化为中心线性关系。
它没有预设 Hilbert 空间的复张量分解，但跨原子对易、完整生成和共享中心
承担了明确的复合公理工作，不能把它们藏在“二元”一词中。

<a id="section-5"></a>

## 5 正归一粗粒化怎样产生状态与 Born 形式

<a id="thm:effect"></a>

#### 定理 5.1（完整效果响应的有限表示）

设 $\mathcal{B}=\bigoplus_\alpha M_{d_\alpha}(\mathbb{C})$，
其效果响应满足 P。则存在唯一一族
$R_\alpha\succeq0$、$\sum_\alpha\operatorname{Tr} R_\alpha=1$，使

$$
\boxed{p(E)=\sum_\alpha\operatorname{Tr}(R_\alpha E_\alpha).}
$$

(5.1)

特别地，单矩阵块上 $p(E)=\operatorname{Tr}(\rho E)$，$\rho\succeq0$、$\operatorname{Tr}\rho=1$。

**证明。**

可加性给 $p(0)=0$；若 $E\preceq F$，由 $F=E+(F-E)$ 得单调性。
把 $E$ 分成 $m$ 份，得 $p(E/m)=p(E)/m$，再得
$p(tE)=tp(E)$ 对所有有理 $t\in[0,1]$ 成立。
以有理数从两侧夹逼实数 $t$，单调性推出全部实齐次性，
无需另外假设连续性。

对任意正元 $A$，取整数 $m\ge\max(1,\|A\|)$，定义
$f(A)=m\,p(A/m)$。比较公共倍数可知它不依赖 $m$。
对 $A,B\succeq0$ 选同一足够大的 $m$，效果可加性给
$f(A+B)=f(A)+f(B)$。令
$f(A-B)=f(A)-f(B)$；若两种正差表示相同，
交叉相加的正元相等，故定义良好。
由此得到自伴部上唯一正归一实线性泛函。

有限维自伴部的非退化实迹配对给唯一自伴 $R_\alpha$ 表示 $f$。
对任意秩一投影非负迫使 $R_\alpha\succeq0$，单位归一给总迹一。
限制回效果得到式 (5.1)。

□

这是 Busch 型完整效果定理的有限维证明，项目 $\Omega$ §6 已采用同一路线。
复二维也成立，是因为输入为全部效果及其粗粒化关系，
不只是成对互补的尖锐投影。〔[10](#ref-busch), [6](#ref-omega)〕

<a id="prop:real"></a>

#### 命题 5.2（从实响应到复正泛函的无歧义步骤）

先把上述自伴响应扩张到实代数：
$f(a)=f((a+a^*)/2)$。选中心复单位 $J=J_1$，定义

$$
\boxed{\omega(a)=f(a)-i f(Ja).}
$$

则以 $J$ 为 $i$ 的代数上，$\omega$ 为复线性、正、归一泛函。

**证明。**

$\omega(Ja)=f(Ja)+if(a)=i\omega(a)$。
因 $f$ 消去斜自伴部分，$f(J)=0$，故 $\omega(1)=1$。
若 $h=a^*a$，中心性给 $(Jh)^*=-Jh$，所以
$\omega(a^*a)=f(a^*a)\ge0$。

□

仅对实线性泛函假设 $f(1)=1$、$f(a^*a)\ge0$ 不够：
在 $\mathbb{C}$ 视为实代数时，$f(x+iy)=x+cy$ 对 $a^*a$ 非负，
却在 $c\ne0$ 时不消去斜自伴部。
本文通过先定义自伴效果响应，明确避免这个漏洞。

<a id="cor:born"></a>

#### 推论 5.3（平方律与整体相位等价）

在完整 $M_d(\mathbb{C})$ 块上，极端响应对应且仅对应秩一 $\rho=\lvert \psi\rangle\langle \psi\rvert$。
于是对单位 $\phi$，

$$
\boxed{p(\lvert \phi\rangle\langle \phi\rvert )=|\langle\phi,\psi\rangle|^2.}
$$

两个单位向量对全部效果响应相同，当且仅当它们相差一个共同 $U(1)$ 相位。

**证明。**

若 $\rho$ 秩大于一，谱分解给非平凡正归一凸分解。
若秩一且 $\rho=t\rho_1+(1-t)\rho_2$、$0<t<1$，
在 $\psi^\perp$ 上非负期望的和为零，使各 $\rho_j$ 均支撑在同一射线，
归一后只能等于 $\rho$。代入迹公式得平方律。
全部效果区分自伴矩阵，故响应相同等价于
$\lvert \psi\rangle\langle \psi\rvert =\lvert \varphi\rangle\langle \varphi\rvert$；两者的像空间相同给
$\varphi=e^{i\theta}\psi$。

□

这里共同相位等价是完整纯态读出的表示结论。
若效果菜单受限，可能存在更多不可区分向量，不能仍断言等价类恰为 $U(1)$。
平方指数也不是“只要归一化就唯一”：非负概率来自完整正锥，
线性来自粗粒化相容，而幅度平方来自所构造的内积。
若另把单通道权重预设为 $|z|^q$，
欧氏等幅正交细分要求 $2(1/\sqrt2)^q=1$，才给 $q=2$。
允许这一细分的欧氏振幅几何是前件，不是由这个等式再次推出的。
项目 V47 的全未归一向量正交权重定理给出了更完整的同类说明。〔[4](#ref-v47)〕

<a id="section-6"></a>

## 6 “本体不可分解”能否产生共同复相位

#### 定义 6.1（极端响应与中心确定）

响应 $p$ 极端，指不存在两个不同、满足 P 的完整效果响应 $p_1,p_2$ 和 $0<t<1$，
使 $p=tp_1+(1-t)p_2$。
合法指满足 P 的整个数学响应凸集；不能因为实际只选一个响应，
就把这个用于检验分解的凸集缩为单点。
中心确定只要求指定中心二值效果的响应取零或一。
前者是相对于完整声明效果域的不可凸分解性，不是“写出了一个向量”的同义词。

<a id="thm:purecenter"></a>

#### 定理 6.2（极端响应选择一个相对定向扇区）

满足 P 的极端响应对每个中心投影 $e$ 都有 $p(e)\in\{0,1\}$。
故有限 $\mathcal{A}_N$ 中恰有一个 $e_\epsilon$ 质量一；
对可数递增原子的整体极端响应，有一条相容的确定符号序列。
将 $Y_r$ 重新标为 $\epsilon_rY_r$ 后，实际支撑中的全部 $J_r$ 共享 $J_1$。

**证明。**

若中心投影 $e$ 满足 $0<m=p(e)<1$，
对任意效果 $E$，$eE$ 与 $(1-e)E$ 均为效果，并且
$E=eE+(1-e)E$。定义

$$
p_e(E)=\frac{p(eE)}m,\qquad
p_{1-e}(E)=\frac{p((1-e)E)}{1-m}.
$$

两者都满足 P，且在 $e$ 上分别取一和零。
于是 $p=mp_e+(1-m)p_{1-e}$ 为非平凡凸分解，矛盾。
有限正交中心分解的各质量均为零或一且和为一，
故恰有一个扇区被选中。

可数情形中，每个 $s_r$ 在加入后续原子后仍是整体中心元，
所以同一论证逐一确定其符号。
有限组确定投影的交仍有质量一：其补投影被有限个零质量补投影之和控制。
因此各有限扇区选择彼此相容。
令 $Y'_r=\epsilon_rY_r$，则
$J'_r=\epsilon_rJ_r=J_1$ 在所选支撑成立。

□

这给“不可分解的本体关系读出”一个精确作用：它消除额外中心随机参数。
若只假设较弱的 C，令
$\epsilon_r=2p((1+s_r)/2)-1$。
每个所选符号的补投影质量为零，有限交的补投影不超过这些补投影之和，
故同样得到 $p(e_\epsilon)=1$。
其余中心块不影响任何效果响应，所以响应经该中心商代数因子化。
有限限制仍可因内部纠缠而为混态，整体极端性没有要求每个原子都在 Bloch 球面上。
反过来，固定一个中心扇区而在该块取 $\rho=I/2^N$，满足 C 却不极端，
说明 C 严格弱于整体纯性。

局部 $Y_r$ 翻号在未胶合实代数上是坐标重定向，
它把相应中心扇区改标到同向扇区。
在已经固定共享 $i$ 的同一个复矩阵块内，只翻一个 $Y_r$ 而保持
$X_r,Z_r,i$ 不变，不保持 $Y_r=iX_rZ_r$，
因而不是该块的自同构，更不能当作实际局域酉门。
同时翻转全部定向不改变相对符号，因而没有推出绝对手性或宇称破缺。

<a id="prop:onevector"></a>

#### 命题 6.3（一个固定向量并不强迫中心确定）

存在同一个固定归一向量 $\Omega$，使两个相对定向扇区各有正质量。

**证明。**

对两个原子取

$$
\pi_+(a\otimes b)=a\otimes b,\qquad
\pi_-(a\otimes b)=a\otimes\bar b.
$$

它们是实 $*$ 表示，$s=-J_1J_2$ 分别映为 $I,-I$。
在 $\mathcal{H}=\mathbb{C}^4\oplus\mathbb{C}^4$ 中取
$v=\lvert 00\rangle$、$\Omega=(v,v)/\sqrt2$，则
$\langle\Omega,\pi((1\pm s)/2)\Omega\rangle=1/2$。
两个矩阵块可分别作用，故 $\Omega$ 还是循环向量。
对任意局部自伴效果 $a,b$，两支响应均为 $a_{00}b_{00}$，
因为自伴矩阵的对角元为实数；中心效果却能区分两支。

□

因此“本体唯一”与“响应极端”是不同命题。
上述反例只用一个 $\Omega$，不依赖多个外部宇宙。
增加纯性或中心确定性，是对同一本体关系的进一步条件。

<a id="section-7"></a>

## 7 一个固定本体向量如何由全部关系构造

完成 C 的支撑选择与定向校准后，有限代数为
$\mathcal{B}_N=M_{2^N}(\mathbb{C})$，嵌入为 $a\mapsto a\otimes I_2$。
定理 [4.1](#thm:sectors) 中相容符号的 Pauli 商映射满足
$q_{N+1}(a\otimes1)=q_N(a)\otimes I_2$，
所以选定中心块后的有限商映射相容，确实得到上述标准嵌入。
它们的范数由矩阵算子范数给出，嵌入等距。
令 $\mathcal{B}=\overline{\bigcup_N\mathcal{B}_N}$；有限模型只取其中一个块。

<a id="thm:gns"></a>

#### 定理 7.1（固定响应的循环表示与唯一态历史）

相容的 P 响应唯一给出 $\mathcal{B}$ 上的复正归一泛函 $\omega$。
存在循环三元组 $(\pi,\mathcal{H}_\omega,\Omega)$，满足

$$
\boxed{\omega(a)=\langle\Omega,\pi(a)\Omega\rangle,\quad
\|\Omega\|=1,\quad \overline{\pi(\mathcal{B})\Omega}=\mathcal{H}_\omega.}
$$

该三元组对已经给定的 $\omega$ 唯一到保持表示与 $\Omega$ 的酉交织。
若 $u_k$ 是实际内部酉元，令

$$
W_0=I,\quad W_k=\pi(u_k\cdots u_1),\quad \Psi_k=W_k\Omega,
$$

则所有 $\Psi_k$ 归一，且

$$
p_k(E)=\omega((u_k\cdots u_1)^*E(u_k\cdots u_1))
=\|\pi(\sqrt E)\Psi_k\|^2.
$$

(7.1)

**证明。**

有限响应的限制相容性在代数并上定义 $\omega$。
正性 Cauchy–Schwarz 及 $a^*a\preceq\|a\|^2I$ 给
$|\omega(a)|\le\|a\|$，所以连续延拓到完备化；用平方根逼近证明延拓仍正。
令

$$
\mathcal N=\{a:\omega(a^*a)=0\},\qquad
\langle[a],[b]\rangle=\omega(a^*b).
$$

正性 Cauchy–Schwarz 使商内积良好。
又因
$\omega(a^*b^*ba)\le\|b\|^2\omega(a^*a)$，
$\mathcal N$ 为左理想，左乘 $[a]\mapsto[ba]$ 有界。
完成该商空间，取 $\Omega=[1]$，即得 $\pi$ 与循环性。
另一循环实现上的映射 $[a]\mapsto\pi'(a)\Omega'$ 保内积，
在稠密子空间上定义后延拓为酉交织。

$u_k^*u_k=u_ku_k^*=1$ 给 $\pi(u_k)$ 为酉，故 $W_k$ 保归一。
利用 $\pi(E)=\pi(\sqrt E)^*\pi(\sqrt E)$ 得式 (7.1)。

□

> **转换者来源注（GNS 原文核验边界）**：本转换者已从所列 LTCC 官方地址取得原始 PDF，并阅读 §8 的 Proposition 8.7、Theorem 8.8 及其证明。原文以复 $C^*$ 代数为域，循环性要求轨道的闭包为整个 Hilbert 空间；8.7 要求两个循环向量产生同一正泛函，8.8 的输入为态。其左乘界为 $\|\gamma(xy)\|^2\le\|x\|^2\|\gamma(y)\|^2$。原文内积第一槽线性，本文采用第二槽线性；本文的含幺情形可取 $\Omega=[1]$，不把该特例替代原文的一般近似单位构造。原作者的阅读报告仍归原作者。

这是标准 GNS 在本轮关系代数上的应用；项目 V30 已有该构造。〔[2](#ref-v30), [11](#ref-gns)〕
它证明固定响应的表示唯一性，没有证明宇宙实际选取的 $\omega$ 由这些公理唯一决定。
实际门词不断追加，指语法前缀增长，不蕴含态的范数、复杂度或熵单调增长。
若要让每个历史前缀都永久可辨，还须有内部正交记录及足够容量。

#### 说明 7.2（整体向量纯与限定读出纯）

即使在一个完整有限关系块上，
$\omega(a)=\operatorname{Tr}(\rho a)$ 也可由

$$
\pi(a)=a\otimes I_r,\qquad
\Omega=\sum_{j=1}^{r}\sqrt{\lambda_j}\lvert j\rangle \lvert j\rangle ,
\quad \rho=\sum_{j=1}^{r}\lambda_j\lvert j\rangle\langle j\rvert ,
\quad \lambda_j>0,\quad r=\operatorname{rank}\rho
$$

表示。这里 $\Omega$ 是一个单位向量，但 $\rho$ 在 $r>1$ 时混合。
辅助表示自由度属于同一数学载体；GNS 不会自动把它们认证为某个实际物理环境。
因此构造一个 $\Omega$ 不证明原可观测代数就是 $B(\mathcal{H}_\omega)$，
也不证明表示维数恰为 $2^N$。若有限完整响应极端，才得到通常的最小纯态表示。

<a id="section-8"></a>

## 8 固定唯一态上的关系如何传导到整个表示

<a id="thm:propagation"></a>

#### 定理 8.1（中心零残差的循环传导）

在未胶合 $\mathcal{A}_N$ 的任一有界循环 $*$ 表示
$(\pi,\mathcal{H},\Omega)$ 中，只对这个已经固定的 $\Omega$ 要求

$$
\|(\pi(J_r)-\pi(J_s))\Omega\|^2=0
$$

在一棵连接全部原子的树的每条边上成立。
则整个循环空间上 $\pi(J_r)=\pi(J_s)$，表示经由共同复相位商因子化。

**证明。**

每个 $c_{rs}=J_r-J_s$ 都在中心。
零残差给 $\pi(c_{rs})\Omega=0$，于是对任意 $a$，

$$
\pi(c_{rs})\pi(a)\Omega=\pi(a)\pi(c_{rs})\Omega=0.
$$

循环性与有界性使 $\pi(c_{rs})=0$。
沿树路径传递等式，全部 $J_r$ 相同；
定理 [4.2](#thm:quotient) 给因子化。

□

这条定理的量词正好符合“唯一本体”的要求：
不是对任意总态作前提，而是检查一个固定根向量上的中心关系，
再由代数结构把它传给全部可表达循环向量。
循环空间包含门词作用向量，也包含其线性张成；
循环性本身不保证每个这样的向量都可由允许酉门从 $\Omega$ 实际制备。

#### 命题 8.2（可数原子的相容延拓）

若在每个有限层上都满足相容的确定符号关系，
则逐原子一次重定向后，所有 $J_r-J_1$ 在整体循环表示中为零。
因此该表示经由共享相位的矩阵归纳极限因子化。

**证明。**

每个差元在整体代数中中心，固定态的零质量关系逐个给零作用，
再应用与定理 [8.1](#thm:propagation) 相同的稠密性论证。
所有差元生成的闭理想都落在表示核内，因此得到商表示。

□

这里不需要假设无限中心投影的乘积已属于原 $C^*$ 代数。
有限相容条件与每个差元的零作用已经足够。

<a id="section-9"></a>

## 9 关系误差本身的归一化与稳定界

本节暂时放松精确 C 条件，研究固定有限层上的中心失配预算；
若 C 已精确成立且已按所选符号校准，以下残差自然全部为零。

#### 定义 9.1（二元中心关系的误差）

对两原子定义

$$
t_{rs}=-J_rJ_s,\qquad E_{rs}=\frac{1+t_{rs}}2,\qquad
D_{rs}=1-E_{rs}.
$$

它们分别是同向与异向中心投影。对固定响应设

$$
\delta_{rs}^2=\omega((J_r-J_s)^*(J_r-J_s)).
$$

在任一向量表示中，它等于
$\|(\pi(J_r)-\pi(J_s))\Omega\|^2$。

<a id="thm:stable"></a>

#### 定理 9.2（有限树上的精确误差预算）

若 $T$ 为连接 $N$ 个原子的树，令
$e_+=\prod_{\{r,s\}\in T}E_{rs}$、$m_+=\omega(e_+)$，则

$$
\boxed{\delta_{rs}^2=4\omega(D_{rs}),\qquad
1-m_+\le\frac14\sum_{\{r,s\}\in T}\delta_{rs}^2.}
$$

(9.1)

若 $m_+>0$，定义内部事件上的条件响应
$\omega_+(a)=\omega(e_+a)/m_+$。在原代数的全部效果上，

$$
\boxed{\sup_{0\preceq E\preceq1}|\omega(E)-\omega_+(E)|
=1-m_+\le\frac14\sum_T\delta_{rs}^2.}
$$

(9.2)

若还有向量表示，置
$\Omega_+=\pi(e_+)\Omega/\sqrt{m_+}$，则在整个 $B(\mathcal{H})$ 的纯态距离中

$$
\boxed{\tfrac12\|\lvert \Omega\rangle\langle \Omega\rvert -\lvert \Omega_+\rangle\langle \Omega_+\rvert \|_1
=\sqrt{1-m_+}\le\frac12\sqrt{\sum_T\delta_{rs}^2}.}
$$

(9.3)

**证明。**

利用 $J_r^*=-J_r$、各 $J_r$ 对易及平方为负单位，

$$
(J_r-J_s)^*(J_r-J_s)=2(1+J_rJ_s)=4D_{rs}.
$$

在中心符号扇区中 $J_r=\epsilon_rJ_1$，
$E_{rs}$ 的值是一，当且仅当 $\epsilon_r=\epsilon_s$。
树连通意味着全部边同向恰好对应全正相对扇区，
故所给乘积等于前文的 $e_+$。
对易投影满足
$1-\prod_T E_{rs}\preceq\sum_T(1-E_{rs})$，取响应得式 (9.1)。

当 $0<m_+<1$ 时，中心性给
$\omega=m_+\omega_++(1-m_+)\omega_-$，
其中 $\omega_-$ 为补事件上的条件态。
两个归一效果响应的差绝对值至多一，故距离至多 $1-m_+$；
在效果 $E=e_+$ 上恰取该值。$m_+=1$ 时同样成立。
最后 $\langle\Omega,\Omega_+\rangle=\sqrt{m_+}$。
当 $m_+<1$ 时，在两向量张成的二维空间直接求纯投影差，
两个非零特征值为 $\pm\sqrt{1-m_+}$；$m_+=1$ 时差为零。
这得到式 (9.3)。

□

若只允许更小实际菜单，式 (9.2) 的上界仍成立；
等号需要中心效果在该菜单中。若 $\sum_T\delta_{rs}^2<4$，已保证 $m_+>0$；
否则条件化仍须另核实分母为正。
这里的误差界是有限层结论；无限层的有用统一界需要可控的总预算。

#### 命题 9.3（中心误差不能被原代数内酉门自动消除）

对任一 $u\in\mathcal{A}_N$ 的酉元，
$\omega(u^*e_+u)=\omega(e_+)$。

**证明。**

$e_+$ 中心，故 $u^*e_+u=e_+u^*u=e_+$。

□

所以稳定预算不是一个免费纠错算法。
选定商代数、假设本体已在指定支撑、条件保留某记录事件，是三个不同操作。
其中条件化也不能在原整体中删除其余分支。

每条关系的正负分支仍可形式化为

$$
\Omega=\pi(E_{rs})\Omega+\pi(D_{rs})\Omega.
$$

记 $\varepsilon=\omega(D_{rs})$，对两个非零归一分支取支撑嵌入，
逻辑二态坐标为 $(\sqrt{1-\varepsilon},\sqrt\varepsilon)$，
于是

$$
(x,y,z)=\bigl(2\sqrt{\varepsilon(1-\varepsilon)},0,1-2\varepsilon\bigr),
\qquad x^2+y^2+z^2=1.
$$

(9.4)

零分支保留零标记即可。这是带支撑嵌入的纯二元几何描述。
因为 $E_{rs}$ 中心，连接两扇区的横向 $X,Y$ 通常不属于原可观测代数；
不能从式 (9.4) 宣称这些相干读口或相应 AURIC 仪器已经实际可用。
式 (9.2) 与式 (9.3) 的不同，正体现了原代数读出与更大载体几何的区别。

<a id="section-10"></a>

## 10 酉性从什么条件成为定理

<a id="thm:unitary"></a>

#### 定理 10.1（有限闭合关系自同构必有酉实现）

每个复线性含幺 $*$ 自同构
$\alpha:M_d(\mathbb{C})\to M_d(\mathbb{C})$ 都有形式

$$
\boxed{\alpha(a)=UaU^\dagger,\qquad U^\dagger U=UU^\dagger=I.}
$$

实 $*$ 自同构若保持中心 $J=iI$，即为复线性；
从恒等连续连接的实 $*$ 自同构必保持 $J$。

**证明。**

标准矩阵单位 $e_{ii}$ 的像是彼此正交且和为一的最小投影。
它们在完整矩阵代数中秩一，写成 $\lvert v_i\rangle\langle v_i\rvert$，其中 $v_i$ 构成正交基。
由 $e_{ii}e_{ij}e_{jj}=e_{ij}$，

$$
\alpha(e_{ij})=c_{ij}\lvert v_i\rangle \langle v_j\rvert .
$$

矩阵单位乘法与伴随给
$|c_{ij}|=1$、$c_{ij}c_{jk}=c_{ik}$、$c_{ji}=\bar c_{ij}$。
令 $c_i=c_{i1}$，则 $c_{ij}=c_i\bar c_j$。
以 $c_iv_i$ 为列构造酉矩阵 $U$，即可在全部矩阵单位上验证该式，
再由复线性扩张。

保持 $J$ 的实线性自同构满足
$\alpha(ia)=\alpha(Ja)=J\alpha(a)=i\alpha(a)$。
中心中满足平方为 $-I$ 的可选像只有 $\pm J$；
连续路径不能改变这个离散符号。

□

因此 R、C 给出复矩阵块后，G 使实际闭合步骤具有酉实现。
单独保持概率归一，或只把每个输出再次归一化，不足以推出这一结论。
自同构要保持乘法、伴随与共同复结构，且必须可逆。
此处不声称无限代数的任意自同构都内实现，也不声称在一个固定 GNS 表示中
所有抽象自同构都可实现为酉。
本模型的实际步骤限于有限内部块，酉元可嵌入同一整体。

同一个酉 $U$ 同时保持主结果与误差之间的整体内积；
非选择的记录摘要或选支更新通常并非酉。
把结果与误差重新写成归一二元关系是有用的表示，
它本身不会使摘要过程恢复为可逆。

<a id="section-11"></a>

## 11 内部记录与测量更新还需什么

#### 定义 11.1（统一内部 ready 接口）

在同一整体的有限内部矩阵块中指定
$\mathcal{H}_S\otimes\mathcal{H}_R$、记录 ready 向量 $\lvert 0\rangle$、整体酉 $U$，
以及记录正交基 $\{\lvert y,\mu\rangle \}$。
定义

$$
K_{y\mu}=(I_S\otimes\langle y,\mu\rvert )U(I_S\otimes\lvert 0\rangle ).
$$

要把这一接口用于实际局部准备及任意保留内部参考 $B$，
还要求输入具有

$$
\rho^{\rm in}_{BSR}=\rho^{\rm in}_{BS}\otimes\lvert 0\rangle\langle 0\rvert _R,
\qquad \text{整体作用在该接口上为 }I_B\otimes U_{SR}.
$$

这项独立 ready 准备不由单个任意相关的 $\Omega$ 自动保证。
所有这些槽位与操作均属于唯一完整观察者载体。

<a id="thm:CP"></a>

#### 定理 11.2（内部记录的完全正仪器）

上述接口满足

$$
\sum_{y,\mu}K_{y\mu}^\dagger K_{y\mu}=I,
\qquad
\mathcal I_y(\rho)=\sum_\mu K_{y\mu}\rho K_{y\mu}^\dagger.
$$

每个 $\mathcal I_y$ 完全正，其和保迹。
记录质量为 $p(y)=\operatorname{Tr}\mathcal I_y(\rho)$，
只在 $p(y)>0$ 时定义条件态 $\mathcal I_y(\rho)/p(y)$。

**证明。**

在 $U^\dagger U=I$ 中插入完整记录基，得到 Kraus 归一式。
对任意内部参考空间及正元 $A$，

$$
(\operatorname{id}\otimes\mathcal I_y)(A)
=\sum_\mu(I\otimes K_{y\mu})A(I\otimes K_{y\mu})^\dagger\succeq0,
$$

故完全正。归一式给总迹守恒，正性给各记录质量非负，
有限记录求和为一。条件化结论随即得到。

□

该证明没有引入本体外的环境，但使用了统一 ready 准备及内部张量接口。
若实际初态中系统与记录已经相关，仅知道实际 $U\Omega$
不足以识别一个对所有假想局部输入都适用的同一 CPTP 映射。
此外，效果 $E$ 只规定概率，不唯一规定状态更新：
例如同一个 $K^\dagger K=E$ 可有不同输出等距部分。
因此 Born 读出定理没有顺便推出唯一塌缩仪器。〔[6](#ref-omega)〕

> **转换者注（转置的维数）**：此处的非完全正转置例在维数至少为二的完整矩阵块上；下文采用二比特 Bell 参考，$F/2$ 的负特征值为 $-1/2$。一维转置为恒等映射。

转置是最小边界例：它正、保迹且可逆，却不是完全正，
因为在内部 Bell 参考上
$(\operatorname{id}\otimes T)(\lvert \Phi^+\rangle\langle \Phi^+\rvert )=F/2$，
交换算子 $F$ 在反对称态上取 $-1$。
所以局部球面、手性或归一性不足以替代完整关联相容。〔[5](#ref-v48)〕

<a id="section-12"></a>

## 12 接回原 AURIC 五模式及递归关系

项目 V37 已有一个固定五效果编码，模式顺序为
$(0,2,3,5,25)=(000,100,010,001,101)$，
对应用户记号 $F[\varnothing],F[1],F[2],F[3],F[13]$。
令

$$
\nu=(1+2\sqrt3+\sqrt{11})^{-1},\quad
a_\nu=\frac{\nu(\sqrt3+\sqrt{11})}{2},\quad
u_0=(a_\nu,a_\nu,\nu).
$$

其效果为

$$
\begin{aligned}
E_{25}&=\tfrac\nu2(\sqrt3 I-X-Y-Z),& E_0&=3E_{25},\\
E_2&=\tfrac\nu2(\sqrt{11}I+3X+Y+Z),\\
E_5&=\tfrac\nu2(\sqrt{11}I+X+3Y+Z),&
E_3&=\nu(I+Z).
\end{aligned}
$$

(12.1)

每个标量系数等于对应 Pauli 向量长度，故效果正且秩一；
相加后 Pauli 系数抵消，单位系数为一。
因此存在固定等距 $V_F:\mathbb{C}^2\to\mathbb{C}^5$，使
$V_F^*\lvert s\rangle\langle s\rvert V_F=E_s$。

#### 命题 12.1（本轮重构与原三轴的接口）

对 $\rho=(I+\mathbf r\cdot\boldsymbol\sigma)/2$，五模式占据均值满足

$$
\boxed{u=u_0+\nu\mathbf r,\qquad \|u-u_0\|^2\le\nu^2.}
$$

若所读二元态纯，等号成立。
三占据轴依次为用户的 $F[1],F[3],F[2]$ 方向；
模式 $F[13]$ 的质量参与前两轴，
而 $F[\varnothing]$ 是一个效果事件。

**证明。**

原占据算子为
$N_x=\operatorname{diag}(0,1,0,0,1)$、
$N_y=\operatorname{diag}(0,0,0,1,1)$、
$N_z=\operatorname{diag}(0,0,1,0,0)$。
由式 (12.1) 得
$V_F^*N_xV_F=a_\nu I+\nu X$、
$V_F^*N_yV_F=a_\nu I+\nu Y$、
$V_F^*N_zV_F=\nu I+\nu Z$，取期望并用推论 [3.2](#cor:bloch) 即得。

□

归一化位于 $\sum_sE_s=I$ 及 $\sum_sp_s=1$，
不能把单独 $F[\varnothing]$ 定义为全部归一化。
$p_0=3p_{25}$ 只在这个固定编码族成立。
三占据来自同一五结果 POVM 的有偏均值，不是同时尖锐的三个 Pauli 值。〔[3](#ref-v37)〕

高维纯态射线可以逐个二元切口进入这种图册，但必须保留有序树、支撑嵌入、
零分支、相对相位和节点间相容关系。
项目 V52 已证明完整二元描述树可恢复纯态射线，并明确区分描述分解
与把未知单份态实际拆成独立节点态的物理过程。
一般高维正关系的二元块还须保留算子值 $S,X,Y,Z$；
不能把每个节点都换成三个标量而声称信息完整。〔[7](#ref-v52)〕

<a id="prop:gram"></a>

#### 命题 12.2（二元合法不能替代整体正性）

所有两两归一关系均合法，仍可能不存在一个共同正关系核。

**证明。**

取

$$
G=\begin{pmatrix}1&-1&-1\\-1&1&-1\\-1&-1&1\end{pmatrix}.
$$

每个二阶主块都为正半定且单位对角，但
$(1,1,1)G(1,1,1)^{\mathsf T}=-3<0$。
所以不存在以 $G$ 为 Gram 矩阵的共同 Hilbert 向量族。

□

这指出递归思想中不能省掉的内容：
关系可继续二分，不代表分开归一后就已全局相容。
本轮的整体正锥、中心胶合及同效果粗粒化，正是在补这个条件。

<a id="section-13"></a>

## 13 三个反模型：为什么更弱的直觉仍不足够

### 13.1 只有正归一与唯一向量，仍可完全经典

交换代数 $\mathbb{C}^m$ 配一个概率向量，同样有正归一泛函、GNS 向量和
$\omega(a^*a)=\|\pi(a)\Omega\|^2$。
但可观测代数完全交换，没有本轮的非交换三轴关系。
因此“能写平方范数”本身不是量子性的充分判据。

### 13.2 平方权重不独自选择复数

实 Hilbert 空间、实对称效果与正交门也有平方概率和可逆等距。
通常的双 rebit 例

$$
\rho_\pm=\frac14(I_4\pm\sigma_y\otimes\sigma_y)
$$

是不同的实正迹一矩阵。
对全部实对称局部效果 $A,B$，
$\operatorname{Tr}(A\sigma_y)=\operatorname{Tr}(B\sigma_y)=0$，故它们的积效果统计完全相同，
而联合量 $\sigma_y\otimes\sigma_y$ 可区分它们。
这说明所采用复合规则下，实理论具有局部积读口看不到的联合参数。
复模型的选择需要额外复结构或适当复合条件。
文献中利用 Jordan 结构、局部层析与 qubit 得复理论的结果，
也明确要求相应复合相容条件，不能缩成“局部层析单独推出量子论”。〔[12](#ref-barnum)〕

### 13.3 二元归一、连续与各向同性仍容许非 Born 响应

令 $a,n$ 为单位 Bloch 方向，定义

$$
p_a(P_n)=\frac{1+(a\cdot n)^3}{2}.
$$

(13.1)

该响应非负、连续、互补归一，并在共同旋转下不变，
本征方向 $n=\pm a$ 的响应为一或零，但它不是仿射 Born 形式。
取单位向量 $b\perp a$，令

$$
n_1=a,\qquad n_2=-a/2+\sqrt3\,b/2,\qquad
n_3=-a/2-\sqrt3\,b/2.
$$

则 $E_j=(2/3)P_{n_j}$ 和为 $I$。
若它能扩展为 P 响应，齐次性给

$$
\sum_{j=1}^3p_a(E_j)
=\frac23\left(1+\frac7{16}+\frac7{16}\right)=\frac54,
$$

与单位归一矛盾。
缺少的正是完整效果间的一致粗粒化，不能用每对概率和为一来替代。
这一类三次反例在项目 V48 已讨论；这里以三效果菜单明确定位冲突。〔[5](#ref-v48)〕

<a id="section-14"></a>

## 14 总重构定理与真正剩余的问题

<a id="thm:main"></a>

#### 定理 14.1（固定唯一本体的条件量子重构）

在 R、P、C 下，每个有限原子层经过一次相容的局部定向校准，
其固定响应的中心支撑选出的关系商代数为 $M_{2^N}(\mathbb{C})$，
响应具有唯一正迹一密度矩阵表示。
相容递增时得到一个固定响应的循环复 Hilbert 表示
$(\pi,\mathcal{H}_\omega,\Omega)$。
再加 G，每个实际有限闭合门都有同一载体上的酉实现，
实际前缀 $\Psi_k=U_k\cdots U_1\Omega$ 归一，全部效果读出具有式 (7.1) 的平方形式。
若另有统一内部 ready 容量与正交记录，则对应摘要仪器完全正。

**证明。**

R 由定理 [3.1](#thm:local)、[4.1](#thm:sectors) 给有限中心块。
P 由定理 [5.1](#thm:effect) 给正归一泛函。
C 选定相容符号块；定理 [4.2](#thm:quotient) 或
[8.1](#thm:propagation) 给共享复相位的矩阵关系。
命题 [5.2](#prop:real) 和定理 [7.1](#thm:gns) 构造固定循环表示。
G 由定理 [10.1](#thm:unitary) 给各有限门的酉元，再由式 (7.1) 给实际平方读出。
附加记录条件满足定理 [11.2](#thm:CP)。

□

> **转换者注（角代数的单位）**：下文的角代数以 $P$ 为单位。它与 $M_d(\mathbb C)$ 同构；当 $P\ne I$ 时，这不是把该单位识别为环境单位 $I$ 的含幺嵌入。

任意有限维 $d$ 的完整矩阵代数可作为足够大 $M_{2^N}(\mathbb{C})$ 的秩 $d$ 角
$PM_{2^N}(\mathbb{C})P$ 表示；这是数学载体嵌入，不保证所需投影和控制已实际取得。
总定理也不保证所有合法密度矩阵都在同一个允许门轨道内。
本轮证明的是所声明关系与读出的量子表示，以及实际门的条件实现。

| 要解释的量子结构 | 本轮真正使用的结构原因 |
| --- | --- |
| 复数与二态旋量 | 实正三轴 Clifford 乘法，其中心体积元平方为负单位 |
| 通常的多体复合 | 跨原子对易、完整生成、相容的中心定向支撑 |
| Born 形式与归一 | 全效果正性、同效果一致、粗粒化可加 |
| 共同 $U(1)$ 等价 | 完整纯态效果响应只依赖秩一投影 |
| 闭合酉演化 | 有限完整关系 $*$ 自同构及共同复结构保持 |
| 测量仪器与 CP | 统一内部 ready 接口、整体酉、正交记录与完整参考相容 |
| 误差稳定 | 指定中心关系残差的有限总预算；不是归一化自动收敛 |

这套公理确实把原先分列的若干量子公理连接到已知数学结构。
但还没有证明 R 的三轴数目、正二次几何或 Clifford 复合是物理唯一选择；
没有从唯一本体推出 C；也没有证明实际所有效果与控制都可取得。
现有完整量子重构文献同样使用有内容的操作公理。
例如 Chiribella–D'Ariano–Perinotti 在其框架中使用因果性、
完美可区分性、理想压缩、局部可区分性、纯条件化及净化，
不是由归一化单独得到完整量子论。〔[13](#ref-cdp)〕

因此下一步最有信息量的问题已经具体化：
能否从项目原生二元窗口、真实读出关系与有限控制中证明 R 的乘法及 P 的全效果覆盖；
能否把 C 作为可检验的中心残差条件取得；能否给内部记录和相互作用的实际成本。
> **转换者来源注（K-bonacci 的世界域）**：所引 §9 完整采用定义 8.1：$c\in(0,\infty)^k$，固定未知量具 $\ell\in[0,\infty)^k\setminus\{0\}$，量具支撑未知；每次制备和每个完整窗口后均强制付费精确读数。结论在此非负非零量具域、无窗口／读数预算的全历史确定性协议类上取最坏值，不是把严格正量具域的逐点结论改写为 $k$。

本轮 K-bonacci 新增定理在其精确收费合同中证明最坏制备数恰为阶数 $k$，
恰好提醒我们表示存在与付费取得是不同定理。〔[8](#ref-kbonacci)〕

最后，本文没有推导三维时空、引力场方程、物理质量与解码复杂度的等同，
也没有唯一选出实际初始 $\omega$ 或 Hamiltonian。
把门词序号解释为内生历史是相容的；
将它变为有物理单位的时间、连续动力学或时空曲率，仍需相应钟与几何关系。
这使“量子起源”成为一项有明确剩余前件的重构问题，
而非把每个归一关系都直接命名为已经得到的完整物理理论。

## 固定来源与阅读范围

<a id="ref-head"></a>

### [1]

trureturing，[本轮固定提交](https://github.com/the-omega-institute/trureturing/commit/3d4c9c5015546c3d0ea44d3caf71ba02b2d0d4a9)。
提交于 2026-11-01 01:26:13 SGT；获取完成于 01:27:43.117771 SGT。
固定 compare、完整 diff 与未截断树核对见本轮来源审计；
未宣称阅读全部 1119 份理论文件。

<a id="ref-v30"></a>

### [2]

trureturing，
[V30：唯一本体、内生观察者与递归时钟](https://github.com/the-omega-institute/trureturing/blob/3d4c9c5015546c3d0ea44d3caf71ba02b2d0d4a9/docs/develop/theory/AURIC_UNIQUE_STATIC_ONTOLOGY_ENDOGENOUS_OBSERVERS_AND_GOLDEN_RECURSIVE_CLOCKS_V30.md)，
本轮重读 84–198 行；§2 的相容泛函、GNS、门轨道及条件记录边界。

<a id="ref-v37"></a>

### [3]

trureturing，
[V37：二元关系、酉表示与原五模式编码](https://github.com/the-omega-institute/trureturing/blob/3d4c9c5015546c3d0ea44d3caf71ba02b2d0d4a9/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)，
本轮重读 150–238 行；固定五效果、等距编码与三占据仿射读出。

<a id="ref-v47"></a>

### [4]

trureturing，
[V47：存在量词、平方权重与提示误差](https://github.com/the-omega-institute/trureturing/blob/3d4c9c5015546c3d0ea44d3caf71ba02b2d0d4a9/docs/develop/theory/AURIC_EXISTENTIAL_QUANTIFIERS_SQUARE_WEIGHTS_AND_PROMPT_ERROR_RELATIONS_V47.md)，
本轮重读 334–455 行；全部未归一复向量的正交权重定理与有限正核。

<a id="ref-v48"></a>

### [5]

trureturing，
[V48：各向同性、手性与条件量子重构](https://github.com/the-omega-institute/trureturing/blob/3d4c9c5015546c3d0ea44d3caf71ba02b2d0d4a9/docs/develop/theory/AURIC_ISOTROPY_CHIRALITY_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V48.md)，
本轮相关有界阅读 367–545、579–726、893–1104 行。
单原子 Clifford 已有；图定向与 $U(1)$ 回路、单体与复合的边界已有。
限定相关来源检索未定位本轮完整多原子中心扇区公式；
这不是全库或全球数学新颖性声明。

<a id="ref-omega"></a>

### [6]

trureturing，
[$\Omega$ 静态相融纤维理论](https://github.com/the-omega-institute/trureturing/blob/3d4c9c5015546c3d0ea44d3caf71ba02b2d0d4a9/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，
假设 1.3；本轮重读相关 195–252、286–338 行。
§6 的全效果 Born 与 CP 前件、内部辅助容量及条件化。

<a id="ref-v52"></a>

### [7]

trureturing，
[V52：纯态商几何与无损递归](https://github.com/the-omega-institute/trureturing/blob/3d4c9c5015546c3d0ea44d3caf71ba02b2d0d4a9/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)，
本轮来源审读 636–816 行；完整二元描述树、算子值关系及物理拆包边界。

<a id="ref-kbonacci"></a>

### [8]

trureturing，
[K-bonacci 端点层析与秩一关系边界](https://github.com/the-omega-institute/trureturing/blob/3d4c9c5015546c3d0ea44d3caf71ba02b2d0d4a9/docs/develop/theory/KBONACCI_ENDPOINT_TOMOGRAPHY_AND_RANK_ONE_RELATION_BOUNDARIES.md)，
本轮新增 §9，定义 9.1、定理 9.2。
对 $k\ge2$，在指定无噪声、同源制备的收费 A 合同中，
所有确定性、历史自适应、逐世界有限终止且精确正确的协议，
其最优最坏制备数恰为 $k$。
这不是每个世界逐点均需 $k$ 次，也不是量子起源公理。

<a id="ref-clifford"></a>

### [9]

D. Lundholm and L. Svensson，
[Clifford algebra, geometric algebra, and applications](https://www.math.lmu.de/~lundholm/clifford.pdf)，
2016 修订讲义。用于标准 Clifford 结构背景；局部同构证明在本文完整给出。

<a id="ref-busch"></a>

### [10]

P. Busch，
[Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem](https://arxiv.org/abs/quant-ph/9909073)，
Phys. Rev. Lett. **91**, 120403 (2003)，
[doi:10.1103/PhysRevLett.91.120403](https://doi.org/10.1103/PhysRevLett.91.120403)。
本轮读取完整效果证明及二维适用边界；本文只使用有限维有限可加版本。

<a id="ref-gns"></a>

### [11]

London Taught Course Centre，
[C*-Algebras notes, §8: GNS construction](https://www.ltcc.ac.uk/media/london-taught-course-centre/documents/C-Star-Algebras-Notes-5.pdf)，
Proposition 8.7、Theorem 8.8；本轮读取循环唯一性与左乘有界证明。

<a id="ref-barnum"></a>

### [12]

H. Barnum and A. Wilce，
[Local tomography and the Jordan structure of quantum theory](https://arxiv.org/abs/1202.4513)，
Foundations of Physics (2014)，
[doi:10.1007/s10701-014-9777-1](https://doi.org/10.1007/s10701-014-9777-1)。
本轮读取摘要、背景及相关定理条件，不声称复核全部分类证明。

<a id="ref-cdp"></a>

### [13]

G. Chiribella, G. M. D'Ariano and P. Perinotti，
[Informational derivation of quantum theory](https://arxiv.org/abs/1011.6451)，
Phys. Rev. A **84**, 012311 (2011)。
本轮读取摘要、引言与公设陈述，仅作公理依赖比较。

> **转换者注（末段报告的归属）**：下列方法、独立审读、PDF 逐页检查及“未修改项目仓库”均为原作者报告。本转换者新增的仅为本 Markdown 与单列的转换者注；本转换不宣称已取得独立审读、形式核验或 GitHub 托管数学渲染认证。

方法说明：全部数学结论采用纸面符号证明及独立审读。
未运行 CAS、数值实验、数学枚举、门搜索或形式证明程序。
程序仅用于来源取得和字节身份核对、文稿排版、PDF 编译及逐页视觉检查。
未修改项目仓库。
