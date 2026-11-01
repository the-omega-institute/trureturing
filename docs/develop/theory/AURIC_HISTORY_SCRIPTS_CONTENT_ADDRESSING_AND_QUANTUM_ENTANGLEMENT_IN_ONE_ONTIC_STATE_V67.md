<details data-production="preamble">
<summary>原始 XeLaTeX 制作设置、元数据与题页（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="原始制作设置">

```tex
% !TeX program = xelatex
% Compile twice with XeLaTeX; optional \def\AURICFontPath{/absolute/font/path/}
% Mathematics is proved on paper. Code was used only for sources, files and PDF production.
\documentclass[11pt,a4paper]{article}
\usepackage[margin=23mm,headheight=16pt]{geometry}
\usepackage{fontspec}
\ifdefined\AURICFontPath
 \setmainfont[Path=\AURICFontPath,BoldFont=NotoSerifCJKsc-Bold.otf,
 ItalicFont=NotoSerifCJKsc-Regular.otf,BoldItalicFont=NotoSerifCJKsc-Bold.otf]{NotoSerifCJKsc-Regular.otf}
\else
 \IfFontExistsTF{Noto Serif CJK SC}{
 \setmainfont[ItalicFont=Noto Serif CJK SC,BoldItalicFont=Noto Serif CJK SC Bold]{Noto Serif CJK SC}
 }{\setmainfont[BoldFont=FandolSong-Bold.otf,ItalicFont=FandolSong-Regular.otf,
 BoldItalicFont=FandolSong-Bold.otf]{FandolSong-Regular.otf}}
\fi
\setmonofont{Latin Modern Mono}
\XeTeXlinebreaklocale "zh"
\XeTeXlinebreakskip=0pt plus 1pt
\usepackage{amsmath,amssymb,amsthm,mathtools,bm}
\usepackage{booktabs,array,tabularx,enumitem,fancyhdr,xcolor,needspace}
\definecolor{auricblue}{RGB}{24,53,79}
\usepackage[unicode,colorlinks=true,linkcolor=auricblue,urlcolor=auricblue,citecolor=auricblue]{hyperref}
\hypersetup{pdftitle={AURIC v67：历史脚本、内容寻址与量子起源},
pdfauthor={AURIC research continuation},
pdfsubject={One ontic state, self-description, coherent histories, entanglement, residual records and conditional quantum reconstruction}}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\Tr}{\operatorname{Tr}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\spanof}{\operatorname{span}}
\newcommand{\Exec}{\operatorname{Exec}}
\newcommand{\addr}{\operatorname{addr}}
\newcommand{\src}{\operatorname{src}}
\newcommand{\Var}{\operatorname{Var}}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/#1}{#2}}
\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{theorem}[definition]{定理}
\newtheorem{proposition}[definition]{命题}
\newtheorem{corollary}[definition]{推论}
\newtheorem{remark}[definition]{说明}
\renewcommand{\proofname}{证明}
\renewcommand{\abstractname}{摘要}
\renewcommand{\refname}{固定来源与文献}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{2pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC：历史脚本、内容寻址与量子起源}
\fancyhead[R]{\small v67 / 2026-11-01}
\fancyfoot[C]{\thepage}
\allowdisplaybreaks[2]
\begin{document}
\begin{center}
{\LARGE\bfseries\color{auricblue} 同一本体中的历史脚本、内容寻址}\\[6pt]
{\LARGE\bfseries\color{auricblue} 与量子纠缠}\\[8pt]
{\large 自描述、相干共享、残余记录与三维关系约束}\\[6pt]
AURIC 量子起源研究\quad 定义、定理与纸面证明\quad v67.0\\[4pt]
2026 年 11 月 1 日\quad Asia/Singapore
\end{center}
```

</div>
</details>

# <span data-prose="0">同一本体中的历史脚本、内容寻址</span>

# <span data-prose="1">与量子纠缠</span>

<span data-prose="2">自描述、相干共享、残余记录与三维关系约束</span>

<span data-prose="3">AURIC 量子起源研究 定义、定理与纸面证明 v67.0</span>

<span data-prose="4">2026 年 11 月 1 日 Asia/Singapore</span>


## <span data-prose="5">摘要</span>


<span data-prose="6">本文接受“门就是完整历史脚本”的定义：历史是有身份的内涵对象，酉算符和实际末态是其执行读出，
无需由一次输入输出反解历史。由此区分内容共享、物理别名、经典共同记录与相干复制，
给出共享历史的 Gram 秩纠缠判据。
对于两个输出及其内部残余记录，推导不同切分的纠缠阈值及一个精确的纯度--negativity 恒等式，
说明保留源记录与相干反计算如何改变输出之间的纠缠。
对多对一内容地址，证明保等距实现所必需的残余正交性与最小容量：
可见地址缩成一个值时，完整历史区别仍可保存在同一本体内部。
随后将二元 Gram 关系、纯态球面及仿射约束统一，精确分类何时留下连续族、两个候选或唯一状态。
Quine 由 Kleene 递归定理实现语义自描述；它与物理态固定点、地址散列固定点及测量选支分别建模。
最后以完整相干正核、可逆续接、正交记录及细化相容性为明示前提，重构 Hilbert 表示、酉作用、
仪器与平方权重，并指出哪些量子结构仍被当作输入。
本文承接项目已有 Gram、AURIC 编码和未来观察商；新组合不作原创优先权主张。</span>


## 1. <span data-prose="7">本轮判断与项目来源范围</span>


**<span data-prose="8">本轮可以把用户的直觉推进为一个有条件的正向命题：
至少含两个非零相干分支的正交历史标签，在两个独立内部接口之间相干地复制，会生成纠缠。
而内容商若只剩一个可见值，保持酉性所要求的是把区别保存到残余，并非自动删除其他分量。</span>**
<span data-prose="9">这两个命题由同一个内积保持条件连接起来。</span>

<span data-prose="10">本轮唯一一次活动 HEAD 请求于新加坡时间 2026-11-01 16:33:58 因本地 socket 权限被拒，
未收到 HTTP 响应，未取得更新提交；没有重试。以下项目结论固定于已核验提交</span>

<span class="katex-display" data-production-value="true"><code>5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b</code></span><span data-prose="11">。</span>


<span data-prose="12">本轮重新核对六份原文的 Git blob 身份，重点读取：历史记录卷 §§116--120；
V22 §§6、8 及相关依赖；静态相融纤维主文 §§1、4、7；V52 §§2、4.2、8.5；
V18 §§2、4、10；有效分辨率文 §3.1.3。另复用上一轮已核对的 V37、V42，
实际重读 V37 §§3--4 与 V42 §§1、3 的模式字典段落。
这限定了本文的“结合项目进展”，不宣称验证了固定提交以后的变化。</span>

<blockquote data-editor-note="史料归属">

**编者限定（史料归属；不属原稿）。** 本节及文献项中关于 16:33:58 的 socket 拒绝、未收 HTTP、未重试、六份 blob、上一轮复用、实际查读范围和纸面方法的叙述，均为作者原稿的历史报告；不表示 Markdown 编者进行了这些历史操作，也不表示当前自动审批拒绝或全库核验。本文固定引用所标提交，不追索更新 HEAD。

</blockquote>


<details data-production="table-1"><summary>原表制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="原表制作源 1">

```tex
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}p{.23\textwidth}X@{}}
\toprule
项目已有结构 & 本轮承接方式\\
\midrule
历史记录卷定理 118.3 & 同一纯共同档案因子不增加分支区分；共同档案长度不是纠缠判据。\\
V22 定理 6.3--6.4 & 完整复正核重构 Hilbert 空间；全部交叉项守恒才允许递归下降。\\
V22 定理 8.4 & 内容商要对全部声明未来读出闭合，才能继续预测。\\
V18 §4 & 几何端点、实际仪器、读得记录后的条件态有分别明确的定义。\\
V52 定理 4.2 & Gram 秩一等价于共同向量共线；纯态不等于参数已经离散。\\
V37 §§3--4 & 固定五模式中有忠实酉表示；其编码球在原 AURIC 三轴中闭合。\\
\bottomrule
\end{tabularx}
\end{center}
```

</div>
</details>

<div class="katex-display" tabindex="0" role="region" aria-label="原表 1">

| <span data-prose="13">项目已有结构</span> | <span data-prose="14">本轮承接方式</span> |
| --- | --- |
| <span data-prose="15">历史记录卷定理 118.3</span> | <span data-prose="16">同一纯共同档案因子不增加分支区分；共同档案长度不是纠缠判据。</span> |
| <span data-prose="17">V22 定理 6.3--6.4</span> | <span data-prose="18">完整复正核重构 Hilbert 空间；全部交叉项守恒才允许递归下降。</span> |
| <span data-prose="19">V22 定理 8.4</span> | <span data-prose="20">内容商要对全部声明未来读出闭合，才能继续预测。</span> |
| <span data-prose="21">V18 §4</span> | <span data-prose="22">几何端点、实际仪器、读得记录后的条件态有分别明确的定义。</span> |
| <span data-prose="23">V52 定理 4.2</span> | <span data-prose="24">Gram 秩一等价于共同向量共线；纯态不等于参数已经离散。</span> |
| <span data-prose="25">V37 §§3--4</span> | <span data-prose="26">固定五模式中有忠实酉表示；其编码球在原 AURIC 三轴中闭合。</span> |

</div>


<span data-prose="27">以下全部数学推导采用纸面证明；没有运行 CAS、数学数值程序、模拟、枚举或数学测试。
公式中的参数族和全称量词定义同一个内部接口的作用，并不假设多个实际宇宙。</span>


## 2. <span data-prose="28">门作为历史：内涵对象、内容地址与实际执行</span>


#### 定义 2.1（<span data-prose="29">唯一来源与实际前缀</span>）


<span data-prose="30">固定一个单位向量</span> <span data-formula="0">$\Omega$</span> <span data-prose="31">和一条实际已执行历史链</span>


<div data-formula="1">

$$
h_0\prec h_1\prec h_2\prec\cdots,\qquad
\Psi_k=G_k\Omega,\qquad G_k=U_k\cdots U_1 .
$$

</div>


<span data-prose="32">程序、工作区、观察者记忆、参考及环境都是此完整载体的内部自由度。
所谓环境，只表示当前指定读口未访问的内部部分。
静态事件结构另记为</span> <span data-formula="2">$\mathfrak G$</span><span data-prose="33">，避免与项目部分文本中用作事件结构的符号</span> <span data-formula="3">$\Omega$</span> <span data-prose="34">混同。</span>


#### 定义 2.2（<span data-prose="35">历史门对象与执行</span>）


<span data-prose="36">给门符号集</span> <span data-formula="4">$\Sigma$</span> <span data-prose="37">和指定解释</span> <span data-formula="5">$a\mapsto U_a$</span><span data-prose="38">。
有限执行历史</span> <span data-formula="6">$h=a_1\cdots a_n$</span> <span data-prose="39">的执行为</span>


<div data-formula="7">

$$
\operatorname{Exec}(h)=U_{a_n}\cdots U_{a_1},\qquad
\operatorname{Exec}(hw)=\operatorname{Exec}(w)\operatorname{Exec}(h).
$$

</div>


<span data-prose="40">可以把“门对象”定义为完整词</span> <span data-formula="8">$h$</span><span data-prose="41">，或保存其引用、端口和事件位置的规范程序图；</span>
<span data-formula="9">$\operatorname{Exec}(h)$</span> <span data-prose="42">是它的物理执行读出。程序代码可含循环和条件分支，
某次已执行的有限历史是它在实际内部记录上的展开。</span>


<span data-prose="43">这一定义直接容纳用户本轮修正。</span><span data-formula="10">$\operatorname{Exec}$</span> <span data-prose="44">不必单射：例如逆门对和空历史可以有相同执行，
却仍是不同历史。历史身份由所保存对象给出，无须从一次末态反演。
项目静态相融纤维主文已经区别门标签、事件位置、历史词与算子求值。</span>[[3]](#ref-omega)


<details data-production="table-2"><summary>原表制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="原表制作源 2">

```tex
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}p{.22\textwidth}X@{}}
\toprule
相同的含义 & 所需相等关系\\
\midrule
相同内容 & 规范代码或展开内容相同。\\
相同事件 & 除标签外，关系位置、端口和来历也相同。\\
相同执行 & $\Exec(h)=\Exec(k)$，或在指定非受控接口上诱导同一通道。\\
相同实际末态 & $\Exec(h)\Omega=e^{i\theta}\Exec(k)\Omega$。\\
相同未来行为 & 对所有声明允许的续接和结束读出给同一响应。\\
同一物理寄存器 & 两个名称只是同一载体的别名。\\
\bottomrule
\end{tabularx}
\end{center}
```

</div>
</details>

<div class="katex-display" tabindex="0" role="region" aria-label="原表 2">

| <span data-prose="45">相同的含义</span> | <span data-prose="46">所需相等关系</span> |
| --- | --- |
| <span data-prose="47">相同内容</span> | <span data-prose="48">规范代码或展开内容相同。</span> |
| <span data-prose="49">相同事件</span> | <span data-prose="50">除标签外，关系位置、端口和来历也相同。</span> |
| <span data-prose="51">相同执行</span> | <span data-formula="11">$\operatorname{Exec}(h)=\operatorname{Exec}(k)$</span><span data-prose="52">，或在指定非受控接口上诱导同一通道。</span> |
| <span data-prose="53">相同实际末态</span> | <span data-formula="12">$\operatorname{Exec}(h)\Omega=e^{i\theta}\operatorname{Exec}(k)\Omega$</span><span data-prose="54">。</span> |
| <span data-prose="55">相同未来行为</span> | <span data-prose="56">对所有声明允许的续接和结束读出给同一响应。</span> |
| <span data-prose="57">同一物理寄存器</span> | <span data-prose="58">两个名称只是同一载体的别名。</span> |

</div>


#### 定理 2.3（<span data-prose="59">有限无环内容的精确递归地址</span>）


<a id="thm:address"></a>


<span data-prose="60">设节点内容为有限、有序、带标签的无环结构</span>
<span data-formula="13">$n=(\operatorname{op}(n),n_1,\ldots,n_\ell)$</span><span data-prose="61">，
并取无歧义单射编码</span> <span data-formula="14">$\operatorname{enc}$</span><span data-prose="62">。定义</span>


<div data-formula="15">

$$
\operatorname{addr}(n)=\operatorname{enc}\bigl(\operatorname{op}(n),
\operatorname{addr}(n_1),\ldots,\operatorname{addr}(n_\ell)\bigr).
$$

</div>


<span data-prose="63">则地址相等当且仅当有序带标签的展开内容树相同。</span>


**证明。**


<span data-prose="64">按节点高度归纳。叶地址由标签单射决定；非叶地址相等，由编码单射性得到根标签、
子节点数和各子地址相同，归纳得到各展开子树相同。反向由定义即得。</span>


∎


<span data-prose="65">这给“内容即地址”一个精确数学版本：相同内容可以共享一份 DAG 节点。
如果两次分配或两个执行位置也必须区分，就要把这些信息纳入内容。
同一展开内容的两个独立副本，与同一副本被引用两次，不能仅由展开树区分。
定长</span> <span data-formula="16">$b$</span> <span data-prose="66">位散列只有</span> <span data-formula="17">$2^b$</span> <span data-prose="67">个取值；内容数超过此容量必碰撞。
精确地址可使用无损变长编码，散列实现则须另给碰撞处理。</span>


#### 定理 2.4（<span data-prose="68">预测充分地址的未来闭包</span>）


<a id="thm:future"></a>


<span data-prose="69">设</span> <span data-formula="18">$\rho_h$</span> <span data-prose="70">是历史配置的完整相关接口态；所有会影响未来的程序和记忆都已纳入接口。
允许续接字集包含空字且对串接封闭，终端效果集为</span> <span data-formula="19">$\mathcal E$</span><span data-prose="71">。定义</span>


<div data-formula="20">

$$
h\sim k
\iff
\operatorname{Tr}(EU_w\rho_hU_w^\dagger)
=\operatorname{Tr}(EU_w\rho_kU_w^\dagger)
\quad\text{对全部允许 }w,E .
$$

</div>


<span data-prose="72">若同一续接</span> <span data-formula="21">$u$</span> <span data-prose="73">对各配置满足</span> <span data-formula="22">$\rho_{hu}=U_u\rho_hU_u^\dagger$</span><span data-prose="74">，
则</span> <span data-formula="23">$h\sim k\Rightarrow hu\sim ku$</span><span data-prose="75">。
任何保留全部这些未来读出的精确地址</span> <span data-formula="24">$c$</span> <span data-prose="76">都必须满足</span>
<span data-formula="25">$c(h)=c(k)\Rightarrow h\sim k$</span><span data-prose="77">。</span>


**证明。**


<span data-prose="78">在</span> <span data-formula="26">$hu,ku$</span> <span data-prose="79">之后测试</span> <span data-formula="27">$w,E$</span><span data-prose="80">，等价于在</span> <span data-formula="28">$h,k$</span> <span data-prose="81">之后测试串接</span> <span data-formula="29">$uw,E$</span><span data-prose="82">，
属于原定义中的允许测试，所以响应相同。
若同一地址对应可由某未来测试区分的两个历史，该测试就不可能仅由地址确定。</span>

<blockquote data-editor-note="未来接口">

**编者限定（未来接口；不属原稿）。** 续接在相同已识别载体上作用，效果为有界 $0\le E\le I$，密度态为迹一正算子（无限维时为迹类），从而迹有定义。全称测试还须包括一切有关记忆、相干参考及操作合法性；若允许配置相关的部分操作，合法域须为等价类之并，或把非法性纳入输出。最粗商的结论只相对于这个固定测试菜单。

</blockquote>


∎


<span data-prose="83">因此此等价关系给声明接口下最粗的预测充分商；它是 V22 定理 8.4 的历史脚本写法。</span>[[2]](#ref-v22)
<span data-prose="84">相同当前人口、相同一次结果或相同代码散列，都不能自动代替这个条件。
若以后允许读取字面历史，或允许先前没有的相干参考，必须把它纳入测试合同。
描述上的归并与物理擦除是不同问题；第</span> [6](#sec:residual) <span data-prose="85">节给物理归并所需的残余。</span>


## 3. <span data-prose="86">Quine：自描述如何与单增历史相容</span>


#### 定义 3.1（<span data-prose="87">有效程序编号</span>）


<span data-prose="88">取部分可计算函数的可接受编号</span> <span data-formula="30">$\varphi_e$</span><span data-prose="89">，以及总可计算专门化函数</span> <span data-formula="31">$s$</span><span data-prose="90">，满足</span>


<div data-formula="32">

$$
\varphi_{s(a,b)}(y)\simeq\varphi_a(b,y).
$$

</div>


<span data-prose="91">符号</span> <span data-formula="33">$\simeq$</span> <span data-prose="92">包含两边同时未定义的情形。</span>


#### 定理 3.2（<span data-prose="93">Kleene 第二递归定理的所需形式</span>）


<a id="thm:quine"></a>


<span data-prose="94">对任意总可计算代码变换</span> <span data-formula="34">$f$</span><span data-prose="95">，存在程序编号</span> <span data-formula="35">$e$</span> <span data-prose="96">使</span>


<div data-formula="36">

$$
\boxed{\varphi_e=\varphi_{f(e)}.}
$$

</div>


**证明。**


<span data-prose="97">有效求值与专门化允许选择二元程序编号</span> <span data-formula="37">$a$</span><span data-prose="98">，使</span>


<div data-formula="38">

$$
\varphi_a(x,y)\simeq\varphi_{f(s(x,x))}(y).
$$

</div>


<span data-prose="99">取</span> <span data-formula="39">$e=s(a,a)$</span><span data-prose="100">，则</span>


<div data-formula="40">

$$
\varphi_e(y)\simeq\varphi_a(a,y)
\simeq\varphi_{f(s(a,a))}(y)
=\varphi_{f(e)}(y).
$$

</div>


∎


<span data-prose="101">这是标准递归定理的证明，不是本轮新发现。
Moschovakis 的作者原文给出此形式及输出自身描述的图灵机定理。</span>[[9]](#ref-moschovakis)
<span data-prose="102">若编号有总可计算源文本译码</span> <span data-formula="41">$\operatorname{src}(n)$</span><span data-prose="103">，取</span> <span data-formula="42">$f(n)$</span> <span data-prose="104">为“打印常量</span> <span data-formula="43">$\operatorname{src}(n)$</span><span data-prose="105">”的代码，
便得到</span> <span data-formula="44">$\varphi_e(y)=\operatorname{src}(e)$</span><span data-prose="106">，即自输出脚本。
项目有效分辨率文 §3.1.3 也明确使用程序语义不动点，并区别字面图像自同一。</span>[[6]](#ref-resolution)

<blockquote data-editor-note="Quine打印合同">

**编者限定（Quine打印合同；不属原稿）。** 这里需一个总可计算的有限源文本译码，以及把任意该文本有效编译为打印常量程序的总构造；源文本与程序行为的语义关联由所选编号保证。可接受编号、有效求值和统一专门化是实质输入；自输出结论不承诺给定长度上界、原生物理执行或自哈希固定点。

</blockquote>


#### 命题 3.3（<span data-prose="107">自输出可作内部可逆过程</span>）


<span data-prose="108">对有限长度的经典代码及计算片段，函数值可通过</span>


<div data-formula="45">

$$
V_f|h,z\rangle=|h,z\oplus f(h)\rangle
$$

</div>


<span data-prose="109">写入内部工作寄存器，同时保留旧输入。
这是基置换，故线性扩张为酉；将一个终止 Quine 的计算逐步可逆实现，
可以输出自身代码并追加执行记录。</span>


**证明。**


<span data-prose="110">再次异或同一个</span> <span data-formula="46">$f(h)$</span> <span data-prose="111">恢复</span> <span data-formula="47">$z$</span><span data-prose="112">，因此映射是双射并保持基内积。
有限计算片段逐步保留需要恢复的旧数据和工作记录，组合仍可逆。
输出副本不要求删除执行时钟或历史。</span>

<blockquote data-editor-note="有限XOR与容量">

**编者限定（有限XOR与容量；不属原稿）。** 该基置换须先固定有限输入域 $H$、同宽输出工作字 $z\in\{0,1\}^m$ 和处处定义的 $f:H\to\{0,1\}^m$；两次 XOR 作用于完全相同的寄存器域。长度不齐时须提供可逆定界、长度寄存器和足够填充。一个已终止计算片段只在已供应足够输入、工作区、时钟和历史槽位时可逐步保留旧数据；此处未执行 Quine，也未由抽象可逆性推出无界实际资源。

</blockquote>


∎


<span data-prose="113">这里需要实际提供就绪空间和可逆计算；无限程序不会由一句自指自动在有限资源中完成。
Quine 固定的是行为</span> <span data-formula="48">$\varphi_e=\varphi_{f(e)}$</span><span data-prose="114">，不是编号等式</span> <span data-formula="49">$e=f(e)$</span><span data-prose="115">。
取</span> <span data-formula="50">$f(e)=e+1$</span><span data-prose="116">，后者无解而递归定理仍成立。
因此自描述也不强迫</span> <span data-formula="51">$U\Omega=\Omega$</span><span data-prose="117">、自哈希数值固定点或动力学收敛。
有限程序的语义自指，可以由按执行顺序展开的无环事件历史实现。</span>


## 4. <span data-prose="118">共享历史什么时候成为纠缠？</span>


### 4.1. <span data-prose="119">先给出实际切分和共同相干关系</span>


#### 定义 4.1（<span data-prose="120">内部相干历史展开</span>）


<span data-prose="121">在同一个实际态</span> <span data-formula="52">$G_k\Omega$</span> <span data-prose="122">的已声明切分</span> <span data-formula="53">$H\otimes B$</span> <span data-prose="123">上，设有限展开</span>


<div data-formula="54">

$$
|\Psi\rangle=\sum_h c_h|h\rangle_H|\chi_h\rangle_B,
\qquad \sum_h|c_h|^2=1,\qquad \|\chi_h\|=1,
$$

</div>


<span data-prose="124">其中</span> <span data-formula="55">$|h\rangle$</span> <span data-prose="125">是正交物理记录，其余相关内部自由度纳入</span> <span data-formula="56">$B$</span><span data-prose="126">。
形式路径求和中的一个索引，不自动是这样的物理记录。</span>


#### 定理 4.2（<span data-prose="127">历史 Gram 秩判据</span>）


<a id="thm:gram"></a>


<span data-prose="128">上述纯态的边缘满足</span>


<div data-formula="57">

$$
(\rho_H)_{hk}=c_h\overline{c_k}\langle\chi_k|\chi_h\rangle,
\qquad
\rho_B=\sum_h|c_h|^2|\chi_h\rangle\langle\chi_h|,
$$

</div>


<div data-formula="58">

$$
\boxed{\operatorname{rank}\rho_H=\operatorname{rank}\rho_B
=\dim\operatorname{span}\{\chi_h:c_h\ne0\}.}
$$

</div>


<span data-prose="129">所以</span> <span data-formula="59">$H|B$</span> <span data-prose="130">不纠缠当且仅当所有非零分支的</span> <span data-formula="60">$\chi_h$</span> <span data-prose="131">共线。</span>


**证明。**


<span data-prose="132">展开</span> <span data-formula="61">$|\Psi\rangle\langle\Psi|$</span> <span data-prose="133">再部分迹即得矩阵元。
定义</span> <span data-formula="62">$X|h\rangle=c_h|\chi_h\rangle$</span><span data-prose="134">，则</span>
<span data-formula="63">$\rho_B=XX^\dagger$</span><span data-prose="135">，</span><span data-formula="64">$\rho_H=(X^\dagger X)^T$</span><span data-prose="136">。
由</span> <span data-formula="65">$\langle v,X^\dagger Xv\rangle=\|Xv\|^2$</span><span data-prose="137">，</span>
<span data-formula="66">$X^\dagger X$</span> <span data-prose="138">与</span> <span data-formula="67">$X$</span> <span data-prose="139">同核，故秩相同；转置不改变秩。
秩一时可提取共同</span> <span data-formula="68">$\chi$</span><span data-prose="140">，写成乘积向量；反之乘积纯态边缘秩一。</span>

<blockquote data-editor-note="有限Gram">

**编者限定（有限Gram；不属原稿）。** 本节秩与张成维数的等式采用已声明有限展开；$X$ 的定义域为有限标签张成空间，值域为其有限维像所在的 $B$。内积对第二变量线性，故转置与系数共轭正如原式。无限历史展开另需收敛及秩概念，本文不把有限秩论证自动外推。

</blockquote>


∎


<span data-prose="141">这是标准 Gram/Schmidt 结构在历史接口上的应用，项目 V52 已给共线与秩一判据。</span>[[4]](#ref-v52)
<span data-prose="142">例如某个实际准备满足</span>


<div data-formula="69">

$$
G_{\rm prep}\Omega=\Bigl(\sum_hc_h|h\rangle_H\Bigr)\otimes|\eta\rangle_B .
$$

</div>


<span data-prose="143">若共同前缀</span> <span data-formula="70">$U_s$</span> <span data-prose="144">和受控后缀</span> <span data-formula="71">$V_h$</span> <span data-prose="145">作用在</span> <span data-formula="72">$B$</span><span data-prose="146">，则</span>
<span data-formula="73">$\chi_h=V_hU_s|\eta\rangle_B$</span><span data-prose="147">，给出上述判据。</span>
<span data-formula="74">$\eta$</span> <span data-prose="148">是这一实际准备的内部因子，不是另一个本体来源。
共同前缀决定输入和交叉重叠，却不单独保证它们非共线。
如果两独立接口已经处于乘积态，后续仅作</span> <span data-formula="75">$U_A\otimes U_B$</span><span data-prose="149">，
结果仍是乘积态。两个指针引用同一寄存器，也不由此产生两个张量因子。</span>

<span data-prose="150">项目历史记录卷定理 118.3 的共同前缀结论同样清楚：
若两分支记录分别为</span> <span data-formula="76">$|C\rangle\otimes|t_0\rangle$</span><span data-prose="151">、</span><span data-formula="77">$|C\rangle\otimes|t_1\rangle$</span><span data-prose="152">，
其内积为</span> <span data-formula="78">$\langle t_1|t_0\rangle$</span><span data-prose="153">。共同纯因子不改变分支区分；
记录分支差异的额外因子才会改变内积。</span>[[1]](#ref-history)


### 4.2. <span data-prose="154">相干复制是一个严格的正向机制</span>


#### 定理 4.3（<span data-prose="155">正交历史标签的相干复制</span>）


<a id="thm:copy"></a>


<span data-prose="156">设</span> <span data-formula="79">$|h\rangle$</span> <span data-prose="157">是有限正交历史标签。定义</span>


<div data-formula="80">

$$
\Delta|h\rangle=|h\rangle_A|h\rangle_B.
$$

</div>


<span data-prose="158">则</span> <span data-formula="81">$\Delta$</span> <span data-prose="159">是等距，可在内部就绪子空间上酉实现。
对</span> <span data-formula="82">$|\chi\rangle=\sum_hc_h|h\rangle$</span><span data-prose="160">，</span>


<div data-formula="83">

$$
\Delta|\chi\rangle=\sum_hc_h|h,h\rangle,
$$

</div>


<span data-prose="161">它纠缠当且仅当至少两个</span> <span data-formula="84">$c_h$</span> <span data-prose="162">非零。</span>


**证明。**


<span data-formula="85">$\langle h,h|k,k\rangle=\delta_{hk}$</span><span data-prose="163">，故保持全部基内积。
有限维就绪子空间上的等距可补齐正交基，扩充成同一总载体上的酉。
输出边缘是</span> <span data-formula="86">$\sum_h|c_h|^2|h\rangle\langle h|$</span><span data-prose="164">，
其秩等于非零系数个数，应用定理</span> [4.2](#thm:gram)<span data-prose="165">。</span>

<blockquote data-editor-note="复制等距的总载体">

**编者限定（复制等距的总载体；不属原稿）。** 复制结论针对非零归一输入，输出标签各在两个独立物理因子中。令输入标签空间嵌入同一有限总载体的 ready 子空间，并供应至少所需标签容量与独立就绪槽位；指定等距的输入、输出子空间等维，且在同一总载体中的正交补维数匹配，才可补基延拓成酉。抽象 $\Delta$ 本身不是两个不同总维度空间之间的酉，也不供应实际就绪资源。

</blockquote>


∎


**<span data-prose="166">由此，用户“共用历史导致纠缠”的直觉可以精确化为：
一个具有相干分支的历史标签，经线性等距复制到两个独立物理记录接口，会形成不可分关系。</span>**
<span data-prose="167">已确定的</span> <span data-formula="87">$|h,h\rangle$</span> <span data-prose="168">是乘积态；
经典共享记录</span> <span data-formula="88">$\sum_hp_h|h,h\rangle\langle h,h|$</span> <span data-prose="169">则按定义可分。</span>

<span data-prose="170">此操作不是任意未知态的克隆：</span>


<div data-formula="89">

$$
\Delta\Bigl(\sum_hc_h|h\rangle\Bigr)
\ne
\Bigl(\sum_hc_h|h\rangle\Bigr)\otimes
\Bigl(\sum_hc_h|h\rangle\Bigr)
$$

</div>


<span data-prose="171">一般成立。若同一等距对两个不同非正交单位向量都实现克隆，
内积</span> <span data-formula="90">$s$</span> <span data-prose="172">必须满足</span> <span data-formula="91">$s=s^2$</span><span data-prose="173">；允许附带依输入变化的单位残余时，
仍有</span> <span data-formula="92">$|s|\le|s|^2$</span><span data-prose="174">，与</span> <span data-formula="93">$0<|s|<1$</span> <span data-prose="175">矛盾。
这是标准不可克隆论证，限制共同设备的接口要求，不禁止为一个已知态定制制备。</span>[[10]](#ref-wootters)


## 5. <span data-prose="176">同一残余记录在两个切分上的作用</span>


#### 定义 5.1（<span data-prose="177">二分支共享源与残余</span>）


<span data-prose="178">在唯一整体的某个准备切面，取</span>


<a id="eq:tripartite"></a>
<div data-formula="94">

$$
|\Xi\rangle=
\sqrt p\,|00\rangle_{AB}|g_0\rangle_G
+e^{i\phi}\sqrt{1-p}\,|11\rangle_{AB}|g_1\rangle_G,
$$

</div>

<span data-equation-number="1">（1）</span>


<div data-formula="95">

$$
0\le p\le1,\quad \|g_0\|=\|g_1\|=1,\quad
\gamma=\langle g_1|g_0\rangle,\quad
q=\sqrt{p(1-p)}\,e^{-i\phi}\gamma .
$$

</div>


<span data-formula="96">$G$</span> <span data-prose="179">保存内部源、程序、路径或环境记录；它不在本体之外。</span>


#### 定理 5.2（<span data-prose="180">两种切分的纠缠与纯度恒等式</span>）


<a id="thm:twocuts"></a>


<span data-prose="181">式</span> [（1）](#eq:tripartite) <span data-prose="182">的</span> <span data-formula="97">$AB$</span> <span data-prose="183">边缘为</span>


<div data-formula="98">

$$
\rho_{AB}=
p|00\rangle\langle00|+(1-p)|11\rangle\langle11|
+q|00\rangle\langle11|+\bar q|11\rangle\langle00|.
$$

</div>


<span data-prose="184">其纠缠条件分别为</span>


<a id="eq:ab"></a>
<a id="eq:abg"></a>
<div data-formula="99">

$$
\begin{aligned}

\rho_{AB}\text{ 在 }A|B\text{ 纠缠}
&\iff p(1-p)>0\ \text{且}\ \gamma\ne0,\\
\Xi\text{ 在 }AB|G\text{ 纠缠}
&\iff p(1-p)>0\ \text{且}\ |\gamma|<1.

\end{aligned}
$$

</div>

<span data-equation-number="2,3">（2），（3）</span>


<span data-prose="185">采用 negativity</span>
<span data-formula="100">$\mathcal N(\rho)=(\|\rho^{T_B}\|_1-1)/2$</span><span data-prose="186">，有</span>


<a id="eq:negativity"></a>
<div data-formula="101">

$$
\mathcal N_{A:B}=\sqrt{p(1-p)}|\gamma|,
\qquad
\boxed{\mathcal N_{A:B}^{\,2}
+\frac{1-\operatorname{Tr}\rho_{AB}^{\,2}}2=p(1-p).}
$$

</div>

<span data-equation-number="4">（4）</span>


**证明。**


<span data-prose="187">对</span> <span data-formula="102">$G$</span> <span data-prose="188">部分迹得</span> <span data-formula="103">$\rho_{AB}$</span><span data-prose="189">。在有序基</span> <span data-formula="104">$00,01,10,11$</span> <span data-prose="190">中，</span>


<div data-formula="105">

$$
\rho_{AB}^{T_B}=
\begin{pmatrix}
p&0&0&0\\
0&0&q&0\\
0&\bar q&0&0\\
0&0&0&1-p
\end{pmatrix}.
$$

</div>


<span data-prose="191">中间块的特征多项式为</span> <span data-formula="106">$\lambda^2-|q|^2$</span><span data-prose="192">，全谱为</span>
<span data-formula="107">$p,1-p,|q|,-|q|$</span><span data-prose="193">。
可分态的局部转置是正矩阵，因为乘积正矩阵的局部转置仍正，非负加权和仍正。
所以</span> <span data-formula="108">$q\ne0$</span> <span data-prose="194">时负特征值见证纠缠；</span><span data-formula="109">$q=0$</span> <span data-prose="195">时上式是显式乘积投影混合。
这证明</span> [（2）](#eq:ab)<span data-prose="196">，不需要一般 PPT 充分性定理。</span>

<span data-prose="197">在逻辑二维支撑</span> <span data-formula="110">$\operatorname{span}\{|00\rangle,|11\rangle\}$</span> <span data-prose="198">上，</span>


<div data-formula="111">

$$
\det\rho_{\rm log}=p(1-p)-|q|^2
=p(1-p)(1-|\gamma|^2).
$$

</div>


<span data-prose="199">结合总态纯性和秩判据，得到</span> [（3）](#eq:abg)<span data-prose="200">。
部分转置迹范数为</span> <span data-formula="112">$1+2|q|$</span><span data-prose="201">，故</span> <span data-formula="113">$\mathcal N=|q|$</span><span data-prose="202">。
最后</span>


<div data-formula="114">

$$
\operatorname{Tr}\rho_{AB}^{\,2}=p^2+(1-p)^2+2|q|^2
$$

</div>


<span data-prose="203">给出</span> [（4）](#eq:negativity)<span data-prose="204">。</span>


∎


<span data-prose="205">Negativity 的定义及可分态局部转置正性是标准结果；
本文为这一明确状态族自行展开全部计算。</span>[[11]](#ref-vidal)
<span data-prose="206">式</span> [（4）](#eq:negativity) <span data-prose="207">仅适用于所列族，不是任意多体态的纠缠守恒定律。
其中纯度亏损在总态纯的条件下见证</span> <span data-formula="115">$AB|G$</span> <span data-prose="208">纠缠，不能直接称作该切分的 negativity。</span>


<details data-production="table-3"><summary>原表制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="原表制作源 3">

```tex
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}p{.21\textwidth}XX@{}}
\toprule
$0<p<1$ 时的残余重叠 & 两输出 $A|B$ & 输出整体与残余 $AB|G$\\
\midrule
$|\gamma|=1$ & 纯纠缠态 & 乘积态，残余可提出\\
$0<|\gamma|<1$ & 混合纠缠态 & 纠缠\\
$\gamma=0$ & 可分但经典相关 & 纠缠\\
\bottomrule
\end{tabularx}
\end{center}
```

</div>
</details>

<div class="katex-display" tabindex="0" role="region" aria-label="原表 3">

| <span data-formula="116">$0<p<1$</span> <span data-prose="209">时的残余重叠</span> | <span data-prose="210">两输出</span> <span data-formula="117">$A\vert B$</span> | <span data-prose="211">输出整体与残余</span> <span data-formula="118">$AB\vert G$</span> |
| --- | --- | --- |
| <span data-formula="119">$\vert \gamma\vert =1$</span> | <span data-prose="212">纯纠缠态</span> | <span data-prose="213">乘积态，残余可提出</span> |
| <span data-formula="120">$0<\vert \gamma\vert <1$</span> | <span data-prose="214">混合纠缠态</span> | <span data-prose="215">纠缠</span> |
| <span data-formula="121">$\gamma=0$</span> | <span data-prose="216">可分但经典相关</span> | <span data-prose="217">纠缠</span> |

</div>


### 5.1. <span data-prose="218">一条实际门序列中的具体实现</span>


<span data-prose="219">设实际准备已使三个内部寄存器处于</span>


<div data-formula="122">

$$
(\alpha|0\rangle+\beta|1\rangle)_R|00\rangle_{AB}.
$$

</div>


<span data-prose="220">依次执行</span> <span data-formula="123">$\operatorname{CNOT}_{R\to A}$</span> <span data-prose="221">和</span>
<span data-formula="124">$\operatorname{CNOT}_{R\to B}$</span><span data-prose="222">，得到</span>


<div data-formula="125">

$$
\alpha|000\rangle_{RAB}+\beta|111\rangle_{RAB}.
$$

</div>


<span data-prose="223">此时</span> <span data-formula="126">$A,B$</span> <span data-prose="224">共用同一个源，但不访问</span> <span data-formula="127">$R$</span> <span data-prose="225">的边缘为</span>


<div data-formula="128">

$$
|\alpha|^2|00\rangle\langle00|+
|\beta|^2|11\rangle\langle11|,
$$

</div>


<span data-prose="226">是可分态。接着执行</span> <span data-formula="129">$\operatorname{CNOT}_{A\to R}$</span><span data-prose="227">，则</span>


<div data-formula="130">

$$
\alpha|000\rangle+\beta|111\rangle
\longmapsto
|0\rangle_R(\alpha|00\rangle+\beta|11\rangle)_{AB}.
$$

</div>


<span data-prose="228">若</span> <span data-formula="131">$\alpha\beta\ne0$</span><span data-prose="229">，输出变成纯纠缠态。
这项联合酉操作利用</span> <span data-formula="132">$A$</span> <span data-prose="230">已保留的区别，把源寄存器相干反计算到就绪态；
没有把两个可区分完整输入映成同一个完整输出。
若还有其他分支记录未反计算，必须将它继续计入</span> <span data-formula="133">$G$</span><span data-prose="231">，不能直接断言输出已纯。</span>

<blockquote data-editor-note="门序列准备">

**编者限定（门序列准备；不属原稿）。** 该三寄存器例子取 $|\alpha|^2+|\beta|^2=1$，所有省略下标的三位串沿用 $RAB$ 次序。纯输出的断言还要求所写准备是与一切其余相关因子解耦的纯准备；若有其他记录，按原文计入 $G$，不可仅用这三道门断言已擦除全部分支区别。端点 $p=0,1$ 的两种切分均可分，表格只讨论 $0<p<1$。

</blockquote>


### 5.2. <span data-prose="232">把这个关系写回三维</span>


<span data-prose="233">在逻辑支撑</span> <span data-formula="134">$|00\rangle,|11\rangle$</span> <span data-prose="234">上写</span>


<div data-formula="135">

$$
\rho_{\rm log}=\frac12(I+x\sigma_x+y\sigma_y+z\sigma_z),
\quad x=2\Re q,\quad y=-2\Im q,\quad z=2p-1.
$$

</div>


<span data-prose="235">于是</span>


<a id="eq:threeway"></a>
<div data-formula="136">

$$
\begin{aligned}

x^2+y^2&=4\mathcal N_{A:B}^{\,2},\\
1-(x^2+y^2+z^2)&=2(1-\operatorname{Tr}\rho_{AB}^{\,2}),\\
\boxed{z^2+4\mathcal N_{A:B}^{\,2}
+2(1-\operatorname{Tr}\rho_{AB}^{\,2})=1.}

\end{aligned}
$$

</div>

<span data-equation-number="5,6,7">（5），（6），（7）</span>


<span data-prose="236">这给“二元关系归一化提升受限三维”一个直接物理含义：
在此族中，轴向不平衡、两输出相干纠缠及输出对残余的纯度亏损有同一个归一化约束。
它们是不同切分下的不同信息，不是三个任意可交换解释的坐标。</span>


## 6. <span data-prose="237">内容归并为何必须留下残余</span>


<a id="sec:residual"></a>


#### 定义 6.1（<span data-prose="238">确定内容的等距解码</span>）


<span data-prose="239">令</span> <span data-formula="137">$|h\rangle$</span> <span data-prose="240">为正交历史记录，</span><span data-formula="138">$|c\rangle$</span> <span data-prose="241">为正交内容记录，给定函数</span>
<span data-formula="139">$f:\mathcal H_{\rm lab}\to\mathcal C_{\rm lab}$</span><span data-prose="242">。要求同一个等距</span> <span data-formula="140">$V$</span> <span data-prose="243">对每个标定基态满足</span>


<div data-formula="141">

$$
V|h\rangle=|f(h)\rangle_C|r_h\rangle_R,\qquad \|r_h\|=1.
$$

</div>


<span data-prose="244">这里</span> <span data-formula="142">$R$</span> <span data-prose="245">是同一本体内部保留的全部相关余码，不是外部垃圾桶。</span>


#### 定理 6.2（<span data-prose="246">地址纤维的残余正交性和最小容量</span>）


<a id="thm:residual"></a>


<span data-prose="247">上述映射为等距当且仅当</span>


<div data-formula="143">

$$
\delta_{hk}=\delta_{f(h),f(k)}\langle r_h|r_k\rangle
\quad\text{对全部 }h,k.
$$

</div>


<span data-prose="248">因此同地址纤维内的余码必须两两正交，有限情形下</span>


<div data-formula="144">

$$
\boxed{\dim R\ge\max_c|f^{-1}(c)|,}
$$

</div>


<span data-prose="249">且这个下界能够达到。</span>


**证明。**


<span data-prose="250">等距性等价于保持基向量全部内积，直接计算即得第一式。
同纤维的不同历史输入正交，内容因子相同，故余码正交，得到下界。
令残余维数等于最大纤维大小，在每一纤维内部给历史分配互异基向量，
不同纤维可重复使用同一组余码。输出仍两两正交，因此达到下界。
有限就绪子空间上的等距可以在匹配总维度的载体上补齐正交基而扩成酉。</span>

<blockquote data-editor-note="残余容量范围">

**编者限定（残余容量范围；不属原稿）。** 最小容量公式与达到构造针对非空有限历史标签集，在其已达到内容像上取最大纤维大小，余码空间可被不同纤维复用。它是精确确定基态解码的数学维数下界；总载体仍须有足够 ready 与工作容量，并满足复制限定中的同载体补空间匹配条件。无限集合的基数、Hilbert 维数及酉延拓须另立条件，不能直接由有限最大值式取得。

</blockquote>


∎


#### 推论 6.3（<span data-prose="251">单值地址可与完整相干性并存</span>）


<a id="cor:oneaddress"></a>


<span data-prose="252">若</span> <span data-formula="145">$f(h_0)=f(h_1)=c$</span><span data-prose="253">，则</span>


<div data-formula="146">

$$
a|h_0\rangle+b|h_1\rangle
\longmapsto
|c\rangle\bigl(a|r_{h_0}\rangle+b|r_{h_1}\rangle\bigr).
$$

</div>


<span data-prose="254">内容端口完全确定，但全态保留原来的区别及相干。</span>

<blockquote data-editor-note="单地址输入">

**编者限定（单地址输入；不属原稿）。** 两个不同历史标签 $h_0\ne h_1$ 正交，取 $|a|^2+|b|^2=1$ 时所示向量为归一态；正交余码保存相对相位。对一般线性组合，原式仍是线性作用式，概率读法须先归一化。

</blockquote>


<span data-prose="255">因此“一个提升或商操作最后只剩一个值”可以精确描述局部接口；
若同时要求全局酉性，它更直接说明信息迁移到了哪里。
即使专门选择一个已知实际向量并把它旋到标准向量，也不能据此推断
同一个校准接口对所有历史都删除了区别。</span>


#### 定理 6.4（<span data-prose="256">丢弃余码后的内容通道</span>）


<a id="thm:quotientchannel"></a>


<span data-prose="257">设</span> <span data-formula="147">$\mathcal E_f(\rho)=\operatorname{Tr}_R(V\rho V^\dagger)$</span><span data-prose="258">。则</span>


<div data-formula="148">

$$
\mathcal E_f(|h\rangle\langle k|)
=\langle r_k|r_h\rangle|f(h)\rangle\langle f(k)|.
$$

</div>


<span data-prose="259">对输入</span> <span data-formula="149">$\sum_ha_h|h\rangle$</span><span data-prose="260">，</span>


<div data-formula="150">

$$
p(c)=\sum_{h:f(h)=c}|a_h|^2 .
$$

</div>


**证明。**


<span data-prose="261">对矩阵单位直接施加</span> <span data-formula="151">$V$</span> <span data-prose="262">并部分迹，得到第一式。
读内容投影</span> <span data-formula="152">$|c\rangle\langle c|$</span> <span data-prose="263">时，仅同纤维项贡献；
同纤维余码内积由定理</span> [6.2](#thm:residual) <span data-prose="264">为</span> <span data-formula="153">$\delta_{hk}$</span><span data-prose="265">，故只剩平方和。</span>


∎


<span data-prose="266">该结论有明确的接口前提：输入是已经正交记录的历史，且每个输入基态确定输出其内容。
真正干涉仪可以把一个路径基映到多个输出叠加，形式路径也可能从未成为物理记录。
对于后者，项目静态相融纤维主文的正确公式仍是</span>


<div data-formula="154">

$$
P(y)=\sum_{h,k\in F_y}A_h\overline{A_k}\langle m_k|m_h\rangle,
$$

</div>


<span data-prose="267">相同记录保留干涉，正交记录消去交叉项。</span>[[3]](#ref-omega)
<span data-prose="268">不能一面把路径当作完整正交档案，一面又在读出中无条件忽略档案的交叉内积。</span>


## 7. <span data-prose="269">线性关系、三维球和离散候选</span>


### 7.1. <span data-prose="270">二元归一化 Gram 提升</span>


#### 定义 7.1（<span data-prose="271">二元关系态</span>）


<span data-prose="272">取不同时为零的共同 Hilbert 向量</span> <span data-formula="155">$u,v$</span><span data-prose="273">，置</span>


<div data-formula="156">

$$
T=\|u\|^2+\|v\|^2,\qquad c=\langle u|v\rangle,
$$

</div>


<div data-formula="157">

$$
|\psi\rangle=\frac{|0\rangle u+|1\rangle v}{\sqrt T},\qquad
R=\frac1T
\begin{pmatrix}\|u\|^2&\bar c\\c&\|v\|^2\end{pmatrix}.
$$

</div>


<span data-prose="274">此</span> <span data-formula="158">$R$</span> <span data-prose="275">是二元标签的约化态；在通常内积约定下它是相应标准 Gram 矩阵的转置。</span>


#### 定理 7.2（<span data-prose="276">Gram--外积--Bloch 恒等式</span>）


<a id="thm:bloch"></a>


<span data-prose="277">令</span>


<div data-formula="159">

$$
\mathbf r=(x,y,z)=\frac1T
\bigl(2\Re c,\ 2\Im c,\ \|u\|^2-\|v\|^2\bigr).
$$

</div>


<span data-prose="278">则</span>


<div data-formula="160">

$$
R=\tfrac12(I+\mathbf r\cdot\boldsymbol\sigma),\qquad
\det R=\frac{\|u\|^2\|v\|^2-|\langle u|v\rangle|^2}{T^2},
$$

</div>


<div data-formula="161">

$$
\boxed{1-\|\mathbf r\|^2
=\frac{4\|u\wedge v\|^2}{T^2}=4\det R,}
\quad
u\wedge v=\frac{u\otimes v-v\otimes u}{\sqrt2}.
$$

</div>


<span data-prose="279">所以</span> <span data-formula="162">$R$</span> <span data-prose="280">纯当且仅当</span> <span data-formula="163">$u,v$</span> <span data-prose="281">线性相关；一般关系态对应闭球，纯关系态对应球面。</span>


**证明。**


<span data-prose="282">比较矩阵元得 Pauli 表达。展开外积范数，两个对角项各为</span>
<span data-formula="164">$\|u\|^2\|v\|^2$</span><span data-prose="283">，两个交叉项各为</span> <span data-formula="165">$|\langle u|v\rangle|^2$</span><span data-prose="284">。
再用</span>


<div data-formula="166">

$$
T^2-(\|u\|^2-\|v\|^2)^2-4|c|^2
=4(\|u\|^2\|v\|^2-|c|^2)
$$

</div>


<span data-prose="285">得恒等式。Cauchy--Schwarz 等号条件给线性相关与纯度等价。</span>


∎


<span data-prose="286">这是项目已有二元 Gram 结构的重述。</span>[[4]](#ref-v52)
<span data-prose="287">若</span> <span data-formula="167">$v=\lambda u$</span><span data-prose="288">，且</span> <span data-formula="168">$u\ne0$</span><span data-prose="289">，则</span>


<div data-formula="169">

$$
\mathbf r(\lambda)=
\left(\frac{2\Re\lambda}{1+|\lambda|^2},
\frac{2\Im\lambda}{1+|\lambda|^2},
\frac{1-|\lambda|^2}{1+|\lambda|^2}\right).
$$

</div>


<span data-formula="170">$\lambda\in\mathbb C\cup\{\infty\}$</span> <span data-prose="290">连续参数化整个球面。
所以</span>**<span data-prose="291">线性相关给出纯度约束，给定的线性关系系数才进一步确定具体纯态</span>**<span data-prose="292">。
一个纯态已经是唯一密度矩阵，仍可对其他基测量给多个概率结果，
例如</span> <span data-formula="171">$|+\rangle$</span> <span data-prose="293">的</span> <span data-formula="172">$Z$</span> <span data-prose="294">读出；状态唯一和所有问题答案确定也有不同含义。</span>


### 7.2. <span data-prose="295">何时真的只剩两个值或一个值</span>


#### 定理 7.3（<span data-prose="296">仿射约束的完整分类</span>）


<a id="thm:affine"></a>


<span data-prose="297">令</span> <span data-formula="173">$L:\mathbb R^3\to\mathbb R^m$</span> <span data-prose="298">秩为</span> <span data-formula="174">$k$</span><span data-prose="299">，一致方程</span> <span data-formula="175">$L\mathbf r=\mathbf b$</span> <span data-prose="300">的最小范数解为</span>
<span data-formula="176">$\mathbf r_0$</span><span data-prose="301">。则球内解恰为</span>


<div data-formula="177">

$$
\mathbf r=\mathbf r_0+\mathbf v,\quad \mathbf v\in\ker L,\quad
\|\mathbf v\|^2\le1-\|\mathbf r_0\|^2.
$$

</div>


<span data-prose="302">纯态解将最后的不等号换成等号即可。</span>


**证明。**


<span data-prose="303">解集是</span> <span data-formula="178">$\mathbf r_0+\ker L$</span><span data-prose="304">，最小范数条件给</span>
<span data-formula="179">$\mathbf r_0\perp\ker L$</span><span data-prose="305">。
故</span> <span data-formula="180">$\|\mathbf r\|^2=\|\mathbf r_0\|^2+\|\mathbf v\|^2$</span><span data-prose="306">，
与单位球或单位球面相交便得结论。</span>


∎


<details data-production="table-4"><summary>原表制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="原表制作源 4">

```tex
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}p{.32\textwidth}XX@{}}
\toprule
条件 & 一般密度态 & 纯态\\
\midrule
$\|\mathbf r_0\|>1$ & 无解 & 无解\\
$\|\mathbf r_0\|=1$ & 唯一切点 & 唯一切点\\
$\|\mathbf r_0\|<1,\ k=0$ & 三维球 & 球面\\
$\|\mathbf r_0\|<1,\ k=1$ & 圆盘 & 圆\\
$\|\mathbf r_0\|<1,\ k=2$ & 线段 & 两点\\
$\|\mathbf r_0\|<1,\ k=3$ & 唯一内部混态 & 无纯态解\\
\bottomrule
\end{tabularx}
\end{center}
```

</div>
</details>

<div class="katex-display" tabindex="0" role="region" aria-label="原表 4">

| <span data-prose="307">条件</span> | <span data-prose="308">一般密度态</span> | <span data-prose="309">纯态</span> |
| --- | --- | --- |
| <span data-formula="181">$\Vert \mathbf r_0\Vert >1$</span> | <span data-prose="310">无解</span> | <span data-prose="311">无解</span> |
| <span data-formula="182">$\Vert \mathbf r_0\Vert =1$</span> | <span data-prose="312">唯一切点</span> | <span data-prose="313">唯一切点</span> |
| <span data-formula="183">$\Vert \mathbf r_0\Vert <1,\ k=0$</span> | <span data-prose="314">三维球</span> | <span data-prose="315">球面</span> |
| <span data-formula="184">$\Vert \mathbf r_0\Vert <1,\ k=1$</span> | <span data-prose="316">圆盘</span> | <span data-prose="317">圆</span> |
| <span data-formula="185">$\Vert \mathbf r_0\Vert <1,\ k=2$</span> | <span data-prose="318">线段</span> | <span data-prose="319">两点</span> |
| <span data-formula="186">$\Vert \mathbf r_0\Vert <1,\ k=3$</span> | <span data-prose="320">唯一内部混态</span> | <span data-prose="321">无纯态解</span> |

</div>


<span data-prose="322">例如已知</span> <span data-formula="187">$x,z$</span> <span data-prose="323">且另知纯态时，</span>


<div data-formula="188">

$$
y=\pm\sqrt{1-x^2-z^2}.
$$

</div>


<span data-prose="324">额外的方向或手性读出可区分两个符号；若没有纯度信息，</span>
<span data-formula="189">$y$</span> <span data-prose="325">可以位于整个相应区间。
相反，一个饱和线性约束</span> <span data-formula="190">$\mathbf n\cdot\mathbf r=1$</span><span data-prose="326">、</span><span data-formula="191">$\|\mathbf n\|=1$</span>
<span data-prose="327">已迫使</span> <span data-formula="192">$\mathbf r=\mathbf n$</span><span data-prose="328">。
这说明用户关于“受限三维中关系可能离散或退化成一点”的直觉可严格成立，
但离散性来自所增加的约束，尚需说明哪一个实际记录提供这些约束。</span>

<blockquote data-editor-note="候选端点">

**编者限定（候选端点；不属原稿）。** 已知 $x,z$ 的例子还须有 $x^2+z^2\le1$；严格小于一时两个符号给不同纯态，等于一时二者重合为 $y=0$，大于一时没有物理态。缺少纯度信息时的区间为 $-\sqrt{1-x^2-z^2}\le y\le\sqrt{1-x^2-z^2}$，其零半径端点同样只有一个候选。仿射分类表已对严格内点、切点及无解分别列出，不能把退化的正负号当作两个可区分记录。

</blockquote>


#### 推论 7.4（<span data-prose="329">近饱和读出的纯目标距离界</span>）


<span data-prose="330">令</span> <span data-formula="193">$\|\mathbf n\|=1$</span><span data-prose="331">、</span><span data-formula="194">$\varepsilon\ge0$</span><span data-prose="332">，</span>
<span data-formula="195">$P_{\mathbf n}=(I+\mathbf n\cdot\boldsymbol\sigma)/2$</span><span data-prose="333">，
若</span> <span data-formula="196">$\operatorname{Tr}(RP_{\mathbf n})\ge1-\varepsilon$</span><span data-prose="334">，则</span>


<div data-formula="197">

$$
D(R,P_{\mathbf n})=\tfrac12\|R-P_{\mathbf n}\|_1
\le\sqrt{\varepsilon}.
$$

</div>


**证明。**


<span data-prose="335">由假设</span> <span data-formula="198">$\mathbf n\cdot\mathbf r\ge1-2\varepsilon$</span><span data-prose="336">，
且</span> <span data-formula="199">$\|\mathbf r\|\le1$</span><span data-prose="337">，得到</span>
<span data-formula="200">$\|\mathbf r-\mathbf n\|^2\le4\varepsilon$</span><span data-prose="338">。
矩阵</span> <span data-formula="201">$R-P_{\mathbf n}=(\mathbf r-\mathbf n)\cdot\boldsymbol\sigma/2$</span>
<span data-prose="339">的特征值为</span> <span data-formula="202">$\pm\|\mathbf r-\mathbf n\|/2$</span><span data-prose="340">，故结论成立。</span>


∎


<span data-prose="341">连续提升本身也不会产生非平凡的确定离散标签：
连通空间</span> <span data-formula="203">$S^2$</span> <span data-prose="342">或</span> <span data-formula="204">$B^3$</span> <span data-prose="343">的连续像仍连通，而有限离散空间的连通子集只有单点。
测量概率函数可以连续；离散实际记录要由另给的记录接口和仪器描述。</span>


### 7.3. <span data-prose="344">与原 AURIC 五模式的精确对应</span>


<span data-prose="345">V37 已构造固定等距</span> <span data-formula="205">$J:\mathbb C^2\to\mathbb C^5$</span><span data-prose="346">，保留模式</span>
<span data-formula="206">$(0,2,3,5,25)$</span> <span data-prose="347">及原三占据读口。</span>[[7]](#ref-v37)
<span data-prose="348">按 V42 的模式字典，数值模式名对应</span>


<div data-formula="207">

$$
(0,2,3,5,25)\longleftrightarrow
(F[\varnothing],F[1],F[2],F[3],F[13]).
$$

</div>


<span data-prose="349">令</span> <span data-formula="208">$\Pi_s=|s\rangle\langle s|$</span><span data-prose="350">，三个占据读口依次是</span>


<div data-formula="209">

$$
N_x=\Pi_2+\Pi_{25},\qquad
N_y=\Pi_5+\Pi_{25},\qquad N_z=\Pi_3.
$$

</div>


<span data-prose="351">因此独占模式概率与三轴均值不能直接混同；空模式是一个事件，
整体归一化由效果和为单位表达。</span>[[8]](#ref-v42)
<span data-prose="352">置</span>


<div data-formula="210">

$$
\nu=\frac1{1+2\sqrt3+\sqrt{11}},\qquad
a_\nu=\frac{\nu(\sqrt3+\sqrt{11})}{2},\qquad
\mathbf u_0=(a_\nu,a_\nu,\nu).
$$

</div>


<span data-prose="353">它给所有二元关系态同一个精确编码：</span>


<div data-formula="211">

$$
\rho_F=JRJ^\dagger,\qquad
(X_{\rm occ},Y_{\rm occ},Z_{\rm occ})=\mathbf u_0+\nu\mathbf r.
$$

</div>


<span data-prose="354">因而上述球、圆、两点和切点，分别成为原金字塔内固定编码球的相应仿射像。
这些坐标是共同五结果读口的均值，经标定恢复逻辑三轴，
不等于一次同时获得三个尖锐 Pauli 结果。</span>

<span data-prose="355">为使该对应完全可检查，V37 所用五效果为</span>


<div data-formula="212">

$$
\begin{aligned}

E_{25}&=\tfrac\nu2(\sqrt3I-\sigma_x-\sigma_y-\sigma_z),&
E_0&=3E_{25},\\
E_2&=\tfrac\nu2(\sqrt{11}I+3\sigma_x+\sigma_y+\sigma_z),\\
E_5&=\tfrac\nu2(\sqrt{11}I+\sigma_x+3\sigma_y+\sigma_z),&
E_3&=\nu(I+\sigma_z).

\end{aligned}
$$

</div>


<span data-prose="356">其每个标量系数等于 Pauli 向量系数的长度，故正且秩一；
相加 Pauli 项抵消、标量和为一，故</span> <span data-formula="213">$\sum_sE_s=I$</span><span data-prose="357">。
写</span> <span data-formula="214">$E_s=|\eta_s\rangle\langle\eta_s|$</span> <span data-prose="358">并定义</span>
<span data-formula="215">$J\psi=\sum_s|s\rangle\langle\eta_s|\psi\rangle$</span><span data-prose="359">，便有</span> <span data-formula="216">$J^\dagger J=I$</span><span data-prose="360">。
相加</span> <span data-formula="217">$E_2+E_{25}$</span><span data-prose="361">、</span><span data-formula="218">$E_5+E_{25}$</span><span data-prose="362">、</span><span data-formula="219">$E_3$</span> <span data-prose="363">即得三均值式。</span>

<span data-prose="364">令</span> <span data-formula="220">$P_J=JJ^\dagger$</span><span data-prose="365">，每个逻辑酉</span> <span data-formula="221">$U$</span> <span data-prose="366">有忠实提升</span>


<div data-formula="222">

$$
\widetilde U=JUJ^\dagger+(I-P_J),\qquad
\widetilde UJ=JU.
$$

</div>


<span data-prose="367">两个正交块上的作用分别为</span> <span data-formula="223">$U$</span> <span data-prose="368">与恒等，故</span> <span data-formula="224">$\widetilde U$</span> <span data-prose="369">酉。
张量内部参考后仍保内积；以</span> <span data-formula="225">$J\otimes J$</span> <span data-prose="370">编码两个输出也保留 Schmidt 系数。
因此本文相干共享与残余记录的数学结论可运输到此 AURIC 编码。
这使用项目已证明的表示，并不额外宣称任意抽象门有原生有限门字的精确实现。</span>


## 8. <span data-prose="371">从唯一值到测量：要补上实际记录</span>


#### 定义 8.1（<span data-prose="372">内生仪器与条件态</span>）


<span data-prose="373">设完整内部载体为</span> <span data-formula="226">$\mathcal H_S\otimes\mathcal H_R$</span><span data-prose="374">，</span>
<span data-formula="227">$S$</span> <span data-prose="375">包括其余所有参考与工作区。当前实际准备满足</span>


<div data-formula="228">

$$
G\Omega=|\psi\rangle_S|0\rangle_R .
$$

</div>


<span data-prose="376">完整酉</span> <span data-formula="229">$U_{\rm m}$</span> <span data-prose="377">在这个就绪子空间上实现</span>


<div data-formula="230">

$$
U_{\rm m}(|\psi\rangle|0\rangle)
=\sum_r M_r|\psi\rangle|r\rangle,\qquad
\sum_rM_r^\dagger M_r=I,
$$

</div>


<span data-prose="378">其中</span> <span data-formula="231">$M_r$</span> <span data-prose="379">作用在</span> <span data-formula="232">$S$</span><span data-prose="380">。令</span> <span data-formula="233">$Q_r=I_S\otimes|r\rangle\langle r|$</span><span data-prose="381">，则</span>


<div data-formula="234">

$$
p_r=\|Q_rU_{\rm m}G\Omega\|^2=\|M_r\psi\|^2,
\qquad
|\Psi_r^{\rm full}\rangle
=\frac{Q_rU_{\rm m}G\Omega}{\sqrt{p_r}}\quad(p_r>0).
$$

</div>


<span data-prose="382">在</span> <span data-formula="235">$S$</span> <span data-prose="383">上的条件态向量为</span> <span data-formula="236">$M_r\psi/\sqrt{p_r}$</span><span data-prose="384">。
不读取记录时，</span><span data-formula="237">$S$</span> <span data-prose="385">的态为</span>
<span data-formula="238">$\sum_rM_r|\psi\rangle\langle\psi|M_r^\dagger$</span><span data-prose="386">。
就绪空间及其准备是明确条件；完整公式始终使用同一个</span> <span data-formula="239">$\Omega$</span><span data-prose="387">。</span>


<span data-prose="388">这就是项目 V18 §4 的操作意义塌缩。</span>[[5]](#ref-v18)
<span data-prose="389">若</span> <span data-formula="240">$M_r=P_r$</span> <span data-prose="390">且</span> <span data-formula="241">$P_r=|r\rangle\langle r|$</span> <span data-prose="391">秩一，
则已知</span> <span data-formula="242">$r$</span> <span data-prose="392">后状态射线为</span> <span data-formula="243">$|r\rangle$</span><span data-prose="393">；线性投影得到一个一维子空间，
再归一化得到唯一纯态。若</span> <span data-formula="244">$P_r$</span> <span data-prose="394">秩大于一，记录只确定一个块，块内相干仍可存在。</span>

<blockquote data-editor-note="测量算子类型">

**编者限定（测量算子类型；不属原稿）。** 此处采用有限结果集、单位范数且与记录槽位解耦的 ready 准备，$M_r:\mathcal H_S\to\mathcal H_S$ 为处处定义有界算子，完备关系须对全部输入成立。$S$ 已包括所有保留参考和工作区；同一完整酉须确已供应，或由匹配有限总载体上的等距补基另行取得。$p_r=0$ 时不定义条件态。系统中的秩一 $P_r$ 与记录因子中的同名基矢分别属于不同空间。

</blockquote>


#### 定理 8.2（<span data-prose="395">条件记录为何呈经典值</span>）


<a id="thm:classical"></a>


<span data-prose="396">令记录投影</span> <span data-formula="245">$Q_r=|r\rangle\langle r|$</span><span data-prose="397">，记录代数为</span>
<span data-formula="246">$\mathcal C=\{\sum_ra_rQ_r\}$</span><span data-prose="398">。
已知记录</span> <span data-formula="247">$r$</span> <span data-prose="399">的条件态在</span> <span data-formula="248">$\mathcal C$</span> <span data-prose="400">上给函数</span>

<blockquote data-editor-note="有限记录代数">

**编者限定（有限记录代数；不属原稿）。** 本定理在有限结果集上取非零、两两正交且在声明记录空间上穷尽单位的投影 $Q_r$；联合载体上使用 $I_S\otimes Q_r$。系数 $a_r$ 因非零正交投影而唯一，$\mathcal C$ 是该空间的含单位交换 $*$ 代数，$A$ 自伴时系数实，正质量记录条件态给归一乘法泛函。未占据的正交补须加为一个非零结果或明确限制支撑。可数或一般无限记录需有界系数、求和拓扑与条件态存在性的另外合同，本文的有限证明不自动承担它们。

</blockquote>


<div data-formula="249">

$$
\omega_r(A)=a_r .
$$

</div>


<span data-prose="401">它满足</span> <span data-formula="250">$\omega_r(AB)=\omega_r(A)\omega_r(B)$</span><span data-prose="402">；
对自伴</span> <span data-formula="251">$A\in\mathcal C$</span><span data-prose="403">，有</span> <span data-formula="252">$\operatorname{Var}_{\omega_r}(A)=0$</span><span data-prose="404">。</span>


**证明。**


<span data-prose="405">正交投影的乘积是</span> <span data-formula="253">$Q_rQ_s=\delta_{rs}Q_r$</span><span data-prose="406">，所以同一记录下</span>
<span data-formula="254">$AB$</span> <span data-prose="407">的系数为</span> <span data-formula="255">$a_rb_r$</span><span data-prose="408">。自伴时</span> <span data-formula="256">$a_r$</span> <span data-prose="409">为实数，</span>
<span data-formula="257">$\omega_r(A^2)-\omega_r(A)^2=a_r^2-a_r^2=0$</span><span data-prose="410">。</span>


∎


<span data-prose="411">因此“关系成为一个唯一值”最准确的对象，是实际记录条件下的交换读出代数。
整个观察者仍可包含别的非交换接口；确定一个经典记录不会把完整量子载体变成一维。
读口稳定可由重复非破坏记录和可区分性给出，上一轮已讨论相应误差界；
本轮增加的是地址余码、纠缠切分和约束几何的定位。</span>

<blockquote data-editor-note="继承V66稳定条件">

**编者限定（继承V66稳定条件；不属原稿）。** 这里承接 V66 原稿固定 QND 合同：有限非零标签投影、同一有限结果仪器 $M_r=\sum_a\sqrt{q_a(r)}e^{i\theta_{ra}}P_a$、每轮新 ready 槽、保留全部旧记录、轮间不混合标签及有限深度所需容量。令 $p_a>0$、$B_{ab}=\sum_r\sqrt{q_a(r)q_b(r)}$；只有读口分布两两不同才有 $B_*<1$，共同误差上界为 $\sum_{a<b}\sqrt{p_ap_b}B_{ab}^{n}$。局部交叉项衰减本身不保证读口取得标签信息。几乎必然后验极化还需一致无限延伸；完整块态收敛还需块内标量 QND，简并块可仍混合。实际与理想的累积误差须控制完整报告通道、所有保留记忆及相同接口；不能以“门越来越准”代替这些前提，也不能从非破坏性单独推出全态收敛。

</blockquote>


<span data-prose="412">纯退相干将交叉项压低，但可以保留两个非零人口。
例如定理</span> [5.2](#thm:twocuts) <span data-prose="413">中</span> <span data-formula="258">$\gamma=0$</span> <span data-prose="414">时，</span>
<span data-formula="259">$\rho_{\rm log}=\operatorname{diag}(p,1-p)$</span><span data-prose="415">，其 Bloch 点落在</span> <span data-formula="260">$z$</span> <span data-prose="416">轴上，
通常既非两个极点之一，也非一个已选择的经典结果。
条件化、局部重置、候选集缩小和非选择退相干各有清楚公式，
不能由其中一个公式直接代替其他过程。</span>


## 9. <span data-prose="417">把“量子公理起源”压缩到什么数学结构？</span>


### 9.1. <span data-prose="418">候选基础：带续接的相干正核</span>


<span data-prose="419">历史脚本、Quine 和内容 DAG 都存在经典实现。
要从它们继续得到相干概率，必须说明历史之间的复交叉关系及其共同相容性。
V22 的正核重构为此提供了一个比逐条宣称 Hilbert 公理更统一的入口。</span>[[2]](#ref-v22)


#### 定义 9.1（<span data-prose="420">历史相干核的候选前提</span>）


<a id="def:kernel"></a>


<span data-prose="421">给历史集</span> <span data-formula="261">$\mathcal W$</span><span data-prose="422">、空历史</span> <span data-formula="262">$e$</span><span data-prose="423">、允许续接及以下数据：</span>


1.  <span data-prose="424">复核</span> <span data-formula="263">$K(v,w)$</span> <span data-prose="425">满足</span>


<div data-formula="264">

$$
K(w,v)=\overline{K(v,w)},\qquad K(h,h)=1,\qquad
\sum_{v,w}\bar a_va_wK(v,w)\ge0
$$

</div>


<span data-prose="426">（最后一式对任意有限支撑系数成立）。</span>


2.  <span data-prose="427">共同续接</span> <span data-formula="265">$\ell_g$</span> <span data-prose="428">保持全部交叉项：</span>
<span data-formula="266">$K(\ell_gv,\ell_gw)=K(v,w)$</span><span data-prose="429">。
需要酉作用时，另要求可逆续接或满射性。</span>


3.  <span data-prose="430">复合端口另给张量积及相位相容的独立寻址；
实际记录由正交内部载体表示。</span>


4.  <span data-prose="431">结果权重在正交细化下可加、非负、与无关坐标选择相容；
读得实际记录后按条件归一化使用后态。</span>


#### 定理 9.2（<span data-prose="432">正核重构与续接作用</span>）


<a id="thm:reconstruct"></a>


<span data-prose="433">在前两项条件下，存在由历史稠密生成的最小复 Hilbert 空间</span> <span data-formula="267">$\mathcal H_K$</span>
<span data-prose="434">和向量</span> <span data-formula="268">$\xi_h$</span><span data-prose="435">，使</span>


<div data-formula="269">

$$
\langle\xi_v|\xi_w\rangle=K(v,w),\qquad \Omega_K=\xi_e .
$$

</div>


<span data-prose="436">该实现唯一到保持所有历史向量的酉同构。
每个续接定义等距</span> <span data-formula="270">$U_g\xi_h=\xi_{\ell_gh}$</span><span data-prose="437">；
有逆续接或该等距满射时，</span><span data-formula="271">$U_g$</span> <span data-prose="438">为酉。</span>


**证明。**


<span data-prose="439">在有限形式复线性组合上定义</span>


<div data-formula="272">

$$
\left\langle\sum_va_v[v],\sum_wb_w[w]\right\rangle
=\sum_{v,w}\bar a_vb_wK(v,w).
$$

</div>


<span data-prose="440">正性给 Cauchy--Schwarz，因此零范数向量与所有向量正交。
除以零范数子空间并完备化即得</span> <span data-formula="273">$\mathcal H_K$</span><span data-prose="441">。
另一最小实现中的同标签映射保持每个有限组合的范数，故良定义且等距；
稠密生成使延拓满射，得到唯一酉同构。</span>

<span data-prose="442">全部交叉项守恒使续接保持每个有限组合的范数，
故把零向量送到零向量并下降到商，随后延拓为等距。
若有逆作用或满射，等距的值域为整个空间，因此酉。</span>

<blockquote data-editor-note="核续接与字面追加">

**编者限定（核续接与字面追加；不属原稿）。** 最小性指历史向量的复线性张成稠密；核仅确定该循环部分。续接须是标签集上的处处定义映射，或先给相容合法域；所谓逆是实际互逆作用，单有一个逆门名称不够。字面追加的公式在 $\ell^2(\Sigma^*)$ 上取有限非空字母表、$g\in\Sigma$、包含空字；这些有界移位定义于全空间，值域是末尾为 $g$ 的闭子空间，空字不在像中。若引入长度生成算子，须在其自然稠密定义域讨论，不能把移位的全空间有界性移给长度算子。

</blockquote>


∎


<span data-prose="443">这是项目 V22 定理 6.3--6.4 的条件重构。
如果从已经给定的唯一实际来源出发，则</span>


<div data-formula="274">

$$
K(v,w)=\langle\Omega|U_v^\dagger U_w|\Omega\rangle .
$$

</div>


<span data-prose="444">重构只确定由声明历史生成的循环部分；未进入任何声明读出的正交补不由此确定。
字面正交历史档案和这些执行态也有不同的核：
保存额外</span> <span data-formula="275">$|h\rangle$</span> <span data-prose="445">标签后，完整记录态的交叉内积还要乘</span>
<span data-formula="276">$\langle h|k\rangle$</span><span data-prose="446">。</span>

<span data-prose="447">“每条历史都归一”只约束对角，并不足以重构续接。
若</span> <span data-formula="277">$\xi_a=\xi_b$</span><span data-prose="448">，某更新却分别指定两个正交单位向量，
则各自范数仍为一，但原零关系</span> <span data-formula="278">$\xi_a-\xi_b=0$</span> <span data-prose="449">被送成非零。
因此实际需要的是完整关系守恒。
在字面历史空间上，追加</span> <span data-formula="279">$S_g|h\rangle=|hg\rangle$</span> <span data-prose="450">也只满足</span>
<span data-formula="280">$S_g^\dagger S_g=I$</span><span data-prose="451">、</span><span data-formula="281">$S_gS_g^\dagger=P_{\rm ends\;g}$</span><span data-prose="452">；
完整酉实现需另给相应载体和就绪资源。</span>[[3]](#ref-omega)


#### 定理 9.3（<span data-prose="453">完整分支核产生量子仪器</span>）


<a id="thm:instrument"></a>


<span data-prose="454">取有限结果集。设后继分支向量的正核为</span> <span data-formula="282">$K_+$</span><span data-prose="455">，
它允许次归一化及零向量，不要求对角等于一。
分支更新标签为</span> <span data-formula="283">$r_o$</span><span data-prose="456">，并对全部历史对满足</span>


<div data-formula="284">

$$
\boxed{K(v,w)=\sum_oK_+(r_ov,r_ow).}
$$

</div>


<span data-prose="457">则</span> <span data-formula="285">$M_o\xi_w=\xi^+_{r_ow}$</span> <span data-prose="458">定义有界线性算子，</span>
<span data-formula="286">$\sum_oM_o^\dagger M_o=I$</span><span data-prose="459">，且</span>
<span data-formula="287">$W\psi=\sum_oM_o\psi\otimes|o\rangle$</span> <span data-prose="460">为等距。</span>


**证明。**


<span data-prose="461">将核恒等式乘</span> <span data-formula="288">$\bar a_va_w$</span> <span data-prose="462">并求和，得到</span>


<div data-formula="289">

$$
\left\|\sum_wa_w\xi_w\right\|^2
=\sum_o\left\|\sum_wa_w\xi^+_{r_ow}\right\|^2.
$$

</div>


<span data-prose="463">原组合为零时，各分支组合都为零，故分支映射下降到商；
各分支范数不超过输入，故延拓为收缩算子。
等式延拓并极化后给完备关系；正交记录再给</span> <span data-formula="290">$W^\dagger W=I$</span><span data-prose="464">。</span>

<blockquote data-editor-note="分支算子陪域">

**编者限定（分支算子陪域；不属原稿）。** 由 $K_+$ 的零范数商与完备化另得 $\mathcal H_{K_+}$。准确类型为 $M_o:\mathcal H_K\to\mathcal H_{K_+}$、$M_o^\dagger:\mathcal H_{K_+}\to\mathcal H_K$，所以完备关系的单位是 $I_{\mathcal H_K}$，而 $W:\mathcal H_K\to\mathcal H_{K_+}\otimes\mathbb C^{|O|}$。无需把输入、后继 Hilbert 空间默认为相同。每个 $r_o$ 落在同一个后继正核的标签域，正核允许零标签；有限结果与全部交叉项恒等式给统一收缩及延拓。若解释为同系统仪器，还须另给后继空间的系统识别；等距并不自动供应实际酉或读出。

</blockquote>


∎


<span data-prose="465">这些算子的后态和效果</span> <span data-formula="291">$E_o=M_o^\dagger M_o$</span> <span data-prose="466">正是一般测量的结构。
此处全交叉项恒等式是前提，不能以只检验各标签概率和为一代替。</span>[[2]](#ref-v22)


### 9.2. <span data-prose="467">二元三维模块还需共同相容</span>


#### 命题 9.4（<span data-prose="468">两两合法不足以拼成共同量子关系</span>）


<a id="prop:pairwise"></a>


<span data-prose="469">存在每个二元主块均正、对角均为一，但全体不是正核的三标签关系。</span>


**证明。**


<span data-prose="470">取实数</span> <span data-formula="292">$1/2<a\le1$</span><span data-prose="471">，令三阶 Hermitian 矩阵对角为一、非对角为</span> <span data-formula="293">$-a$</span><span data-prose="472">。
每个二阶主块的特征值为</span> <span data-formula="294">$1\pm a$</span><span data-prose="473">，都非负。
但对全一向量</span> <span data-formula="295">$\mathbf 1$</span><span data-prose="474">，</span>
<span data-formula="296">$\mathbf1^\dagger K\mathbf1=3-6a<0$</span><span data-prose="475">，所以全矩阵不正。</span>


∎


<span data-prose="476">因此可把高维关系组织成二元模块网络，但必须保留模块之间的共同 Gram 相容条件。
逐个三维球都合法，不意味着它们能同时来自同一个</span> <span data-formula="297">$\Omega$</span><span data-prose="477">。
一个孤立三标量也不保存任意高维联合态的全部参数；完整网络、关系核和内部残余承担其余信息。
这与项目 V52 对“秩一、维数和完整共同实现”的区分一致。</span>[[4]](#ref-v52)

<span data-prose="478">若地址用于相干控制，还要保留控制参照下的相对相位。
例如</span> <span data-formula="298">$I$</span> <span data-prose="479">与</span> <span data-formula="299">$-I$</span> <span data-prose="480">作用于单独数据时诱导同一通道，
但相位已标定的受控实现分别把</span>
<span data-formula="300">$|+\rangle|\psi\rangle$</span> <span data-prose="481">送到</span> <span data-formula="301">$|+\rangle|\psi\rangle$</span> <span data-prose="482">与</span>
<span data-formula="302">$|-\rangle|\psi\rangle$</span><span data-prose="483">。
因此忽略整体相位的程序通道地址，并不自动成为相干程序的完整地址。</span>


### 9.3. <span data-prose="484">平方权重需要什么额外条件</span>


#### 定理 9.5（<span data-prose="485">正交细化相容的平方权重</span>）


<a id="thm:born"></a>


<span data-prose="486">在已重构的 Hilbert 结构中，设分支权重非负、只依赖分支范数，
不依赖无关坐标或正交记录的命名。
令</span> <span data-formula="303">$w(t)$</span> <span data-prose="487">为范数</span> <span data-formula="304">$\sqrt t$</span> <span data-prose="488">的分支权重，</span><span data-formula="305">$0\le t\le1$</span><span data-prose="489">。
进一步要求</span> <span data-formula="306">$w(1)=1$</span><span data-prose="490">，且对允许的正交细化，</span>


<div data-formula="307">

$$
w(s+t)=w(s)+w(t)\qquad(s,t\ge0,\ s+t\le1).
$$

</div>


<span data-prose="491">则</span> <span data-formula="308">$w(t)=t$</span><span data-prose="492">；对归一态的正交分量有</span>


<div data-formula="309">

$$
p_j=\|P_j\psi\|^2,\qquad
p_o=\|M_o\psi\|^2
$$

</div>


<span data-prose="493">（后者通过正交结果记录分量应用）。</span>


**证明。**


<span data-prose="494">加性给</span> <span data-formula="310">$w(0)=0$</span><span data-prose="495">，分割单位区间给</span> <span data-formula="311">$w(1/n)=1/n$</span><span data-prose="496">，
再得</span> <span data-formula="312">$w(m/n)=m/n$</span><span data-prose="497">。
若</span> <span data-formula="313">$s\le t$</span><span data-prose="498">，非负性及加性给</span> <span data-formula="314">$w(t)-w(s)=w(t-s)\ge0$</span><span data-prose="499">，故单调。
用有理数分别从下方和上方逼近任意</span> <span data-formula="315">$t$</span><span data-prose="500">，得到</span> <span data-formula="316">$w(t)=t$</span><span data-prose="501">。
记录分量彼此正交，其范数平方和为一，代入即得两式。</span>

<blockquote data-editor-note="Born全实细化">

**编者限定（Born全实细化；不属原稿）。** 证明要求同一个 $w$ 定义于整个实区间 $[0,1]$，对所有实数 $s,t\ge0$ 且 $s+t\le1$ 都满足所写加性，并允许任意有限等分和相应正交细化（必要时另供应 ready 记录容量）。权重须仅依范数且跨坐标、记录命名及细化上下文一致；非负性、$w(1)=1$ 缺一不可。只在一个固定有限允许细化菜单上检验加性，不能用有理逼近推出整个连续区间的平方律。正交投影族须在态的支撑上穷尽，仪器权重使用已证明等距的正交记录分量。这里的证明只用有限加性与实数序完备性，不额外宣称已从句法导出这些物理条件。

</blockquote>


∎


<span data-prose="502">这给平方律一条清楚的数学来源：正核提供二次范数，
正交可加且不依赖细化的权重把概率固定为范数平方。
复数域、正性、允许的正交细化与分支权重的坐标无关性仍是输入；
这里没有从“逻辑只有加法乘法”或“存在 Quine”单独推出它们。</span>


### 9.4. <span data-prose="503">目前可得到的公理依赖</span>


<details data-production="table-5"><summary>原表制作设置与 TeX（原样保留）</summary>

<div class="katex-display" tabindex="0" role="region" aria-label="原表制作源 5">

```tex
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}p{.28\textwidth}XX@{}}
\toprule
明示输入 & 可证明的结果 & 仍需区分的内容\\
\midrule
程序编号、专门化、有效求值
& 语义自指、Quine
& 物理振幅与概率尚未规定\\
复正核、全部交叉关系
& 最小 Hilbert 表示、二次范数
& 复数域和正性仍是前提\\
保核续接及逆/满射
& 酉演化
& 单增字面历史不自动满射\\
独立内部端口及相干复制
& 指定切分的纠缠
& 别名和经典共享本身不充分\\
完整分支核与正交记录
& 等距仪器、效果、条件态
& 记录可访问性和校准要实际提供\\
非负、坐标无关、细化可加权重
& Born 平方权重
& 不由归一化一条独自产生\\
已知记录及交换记录代数
& 唯一经典值、零条件方差
& 不等于全局分支被删除\\
\bottomrule
\end{tabularx}
\end{center}
```

</div>
</details>

<div class="katex-display" tabindex="0" role="region" aria-label="原表 5">

| <span data-prose="504">明示输入</span> | <span data-prose="505">可证明的结果</span> | <span data-prose="506">仍需区分的内容</span> |
| --- | --- | --- |
| <span data-prose="507">程序编号、专门化、有效求值</span> | <span data-prose="508">语义自指、Quine</span> | <span data-prose="509">物理振幅与概率尚未规定</span> |
| <span data-prose="510">复正核、全部交叉关系</span> | <span data-prose="511">最小 Hilbert 表示、二次范数</span> | <span data-prose="512">复数域和正性仍是前提</span> |
| <span data-prose="513">保核续接及逆/满射</span> | <span data-prose="514">酉演化</span> | <span data-prose="515">单增字面历史不自动满射</span> |
| <span data-prose="516">独立内部端口及相干复制</span> | <span data-prose="517">指定切分的纠缠</span> | <span data-prose="518">别名和经典共享本身不充分</span> |
| <span data-prose="519">完整分支核与正交记录</span> | <span data-prose="520">等距仪器、效果、条件态</span> | <span data-prose="521">记录可访问性和校准要实际提供</span> |
| <span data-prose="522">非负、坐标无关、细化可加权重</span> | <span data-prose="523">Born 平方权重</span> | <span data-prose="524">不由归一化一条独自产生</span> |
| <span data-prose="525">已知记录及交换记录代数</span> | <span data-prose="526">唯一经典值、零条件方差</span> | <span data-prose="527">不等于全局分支被删除</span> |

</div>


<span data-prose="528">内容地址、共享子程序、自输出和可逆执行，都可由经典可逆机器及其档案实现；
把所有可读量限制在对角记录上，就得到一个没有相干纠缠的模型。
因此这些句法前提的确与量子理论相容，却不逻辑强制量子理论。
本轮更基础的候选结构应明确写为</span>

<blockquote data-editor-note="经典反模型范围">

**编者限定（经典反模型范围；不属原稿）。** 这里的反模型可同时把允许准备、操作和可读量取为经典概率、可逆基置换及对角记录，因而这些句法和可逆计算条件有不含相干纠缠的共同实现。把任意已纠缠量子态的读口仅限制为对角读出，并不会使它相对于原张量切分的数学纠缠消失；两者须分别陈述。

</blockquote>


<div data-formula="317">

$$
\boxed{\text{带完整复正核、保核续接与正交记录的内生历史结构。}}
$$

</div>


<span data-prose="529">它把多个量子公理接到同一个数学结构上，同时清楚暴露了还需解释的前提。
若再给可微单参数酉群、参数校准及常数</span> <span data-formula="318">$\hbar$</span><span data-prose="530">，
才可由群生成元得到 Schrödinger 形式；空间局域性、哈密顿量和物理时钟仍需额外结构。</span>

<blockquote data-editor-note="生成元正则性">

**编者限定（生成元正则性；不属原稿）。** 有限维时需同一载体上的可微单参数酉群与群律，以及经校准参数和非零实常数 $\hbar$；$H=i\hbar U^{\prime}(0)$ 是有界自伴生成元，$i\hbar\,d\psi/dt=H\psi$。无限维时，强连续酉群的自伴生成元一般无界，Schrödinger 导数等式只对 $\psi\in D(H)$ 成立并须使用不变自然域；若主张所有向量都可微或范数可微，则是更强的有界生成元条件。这里不从离散事件计数、可逆性或归一化单独推出这些正则性，也不确定物理 Hamiltonian、局域性或时钟。

</blockquote>


## 10. <span data-prose="531">本轮形成的统一解释</span>


<span data-prose="532">用户的“门就是历史脚本”可以保留为基础定义。
在这个定义上，自描述处理的是代码怎样引用和输出自身；
内容寻址处理的是哪些内容可以共用一个表示；
完整相干关系处理的是不同内部分支怎样叠加、干涉及纠缠；
残余定理处理的是局部归并后区别必须保存在哪里。</span>

<span data-prose="533">这使同一个内积保持条件出现于三个相连的位置。
首先，复制正交历史标签保持内积，在至少两项非零的相干输入上生成纠缠。
其次，多对一内容归并也必须保持内积，因此同内容历史要留下正交余码。
最后，二元关系态的行列式和球内半径度量相关向量是否共线；
其边界纯度不自动选定某个关系系数，但实际记录提供的约束可将候选集缩成两点或一点。</span>

<span data-prose="534">所以当前可严格表达的测量图景是：</span>
**<span data-prose="535">同一</span> <span data-formula="319">$\Omega$</span> <span data-prose="536">的内部酉历史建立记录；记录的相干结构决定哪些局部交叉项可见；
在已读得的记录条件下，相关交换代数上的值唯一且稳定。
若某个接口被确定重置，原区别仍在完整内部余码中。</span>**
<span data-prose="537">全局酉态中的其他分量是否在某种本体意义上真正消失，
不由内容地址、Quine 或几何切点这几条数学结论决定。</span>

<blockquote data-editor-note="统一结论的稳定范围">

**编者限定（统一结论的稳定范围；不属原稿）。** 此处“唯一”限于已取得正质量记录后的声明有限交换代数；“稳定”沿用上面的非破坏、持久记录、实际可分辨性与误差合同，不是任意后续门下不变。重置保全区别的结论限定于前述同一个已校准等距／全局酉接口和全部残余载体。

</blockquote>


<span data-prose="538">进一步研究最值得收紧的是定义</span> [9.1](#def:kernel) <span data-prose="539">的复正核前提：
能否由更直接的内部干涉可组合性、参照相容性和可逆实验约束推出，
并区分实、复等不同表示。
这样每一步都能显示减少了哪条独立假设，
而不会把待解释的量子结构隐藏在“归一化”一词中。</span>


<!-- 原稿 \appendix：附录继续保留原顺序。 -->


## A. <span data-prose="540">为什么任意程序没有可计算的完美语义地址</span>


#### 定理 A.1


<span data-prose="541">对于采用可接受编号（具有有效求值与统一专门化）的通用部分可计算程序系统，
不存在总可计算地址</span> <span data-formula="320">$a$</span><span data-prose="542">，使地址相等可判定且</span>


<div data-formula="321">

$$
a(e)=a(f)\iff\varphi_e=\varphi_f .
$$

</div>


**证明。**


<span data-prose="543">给</span> <span data-formula="322">$e,x$</span><span data-prose="544">，有效构造程序</span> <span data-formula="323">$p_{e,x}$</span><span data-prose="545">：在任意输入上先模拟</span> <span data-formula="324">$\varphi_e(x)$</span><span data-prose="546">，
停机就输出零，否则一直模拟。令</span> <span data-formula="325">$z$</span> <span data-prose="547">为恒输出零的程序，则</span>
<span data-formula="326">$\varphi_{p_{e,x}}=\varphi_z$</span> <span data-prose="548">当且仅当</span> <span data-formula="327">$\varphi_e(x)$</span> <span data-prose="549">停机。
若所述地址存在，比较</span> <span data-formula="328">$a(p_{e,x})$</span> <span data-prose="550">和</span> <span data-formula="329">$a(z)$</span> <span data-prose="551">就能判定停机。
若总停机判定器</span> <span data-formula="330">$H$</span> <span data-prose="552">存在，构造程序</span> <span data-formula="331">$D(n)$</span><span data-prose="553">：
在</span> <span data-formula="332">$H(n,n)$</span> <span data-prose="554">判为停机时循环，否则立即停机。
将</span> <span data-formula="333">$D$</span> <span data-prose="555">的自身编号代入，两个判定结果都与实际行为矛盾。</span>


∎


<span data-prose="556">该命题不否认语法内容地址，也不否认有限受限门族可以有有效正规形。
它只限制对任意通用程序的完全行为等价进行统一、精确、可计算归并。</span>


## B. <span data-prose="557">来源归属与使用边界</span>


<span data-prose="558">Quine、不可克隆、Gram/Schmidt、Bloch、正核 Hilbert 重构和 negativity 都是已有数学。
本文的工作是按用户的唯一</span> <span data-formula="334">$\Omega$</span> <span data-prose="559">历史模型组合这些结构，
明列残余与切分，并给本轮特殊状态族及仿射约束的自足推导。
项目文件中已存在的定理均在正文注明。
没有把项目中的自模拟铺砖讨论当作已证明量子起源；
也没有把文献中的原理性结果当作当前原生门菜单的无条件精确编译结论。</span>


## 固定来源与文献


<a id="ref-history"></a>

**[1]** 
<span data-prose="560">TrureTuring 项目，</span>
[<span data-prose="561">AURIC FIB 历史记录与时间箭头</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md)<span data-prose="562">，
固定提交，§§116--120，尤其定理 118.2--118.3、119.2。</span>


<a id="ref-v22"></a>

**[2]** 
<span data-prose="563">TrureTuring 项目，</span>
[<span data-prose="564">AURIC 相对门历史、观察商与递归闭包 V22</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)<span data-prose="565">，
固定提交，§§6、8，尤其定理 6.3--6.4、8.3--8.4。</span>


<a id="ref-omega"></a>

**[3]** 
<span data-prose="566">TrureTuring 项目，</span>
[<span data-prose="567">AURIC 静态相融纤维理论</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)<span data-prose="568">，
固定提交，定义 1.1、假设 1.3、§§4、7。
该文件在事件结构定义中的</span> <span data-formula="335">$\Omega$</span> <span data-prose="569">与本文固定态</span> <span data-formula="336">$\Omega$</span> <span data-prose="570">类型不同。</span>


<a id="ref-v52"></a>

**[4]** 
<span data-prose="571">TrureTuring 项目，</span>
[<span data-prose="572">AURIC 纯态商几何、二次关系生成与无损递归 V52</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)<span data-prose="573">，
固定提交，§§2、4.1--4.2、8.5。</span>


<a id="ref-v18"></a>

**[5]** 
<span data-prose="574">TrureTuring 项目，</span>
[<span data-prose="575">AURIC 三角剖分、条件塌缩与递归酉门 V18</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_TRIANGULATION_COLLAPSE_AND_RECURSIVE_UNITARY_GATES_V18.md)<span data-prose="576">，
固定提交，§§2、4、10。</span>


<a id="ref-resolution"></a>

**[6]** 
<span data-prose="577">TrureTuring 项目，</span>
[<span data-prose="578">递归关系观察与有效分辨率</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md)<span data-prose="579">，
固定提交，§3.1.3。
此处只引用项目对程序语义自指的说明，不宣称本轮重新查读其全部外部依赖。</span>


<a id="ref-v37"></a>

**[7]** 
<span data-prose="580">TrureTuring 项目，</span>
[<span data-prose="581">AURIC 二元关系、酉表示与黄金门通用性 V37</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)<span data-prose="582">，
固定提交，定义 3.1、定理 3.2、定理 4.1。
复用上一轮已核对的固定原文，本轮重读 §§3--4。</span>


<a id="ref-v42"></a>

**[8]** 
<span data-prose="583">TrureTuring 项目，</span>
[<span data-prose="584">AURIC 关系语义、量子三轴与递归相容 V42</span>](https://github.com/the-omega-institute/trureturing/blob/5cf95e1ae01f7ed86735c04ad8d752cb19b1a58b/docs/develop/theory/AURIC_F13_RELATIONAL_SEMANTICS_QUANTUM_THREE_AXES_AND_RECURSIVE_COMPATIBILITY_V42.md)<span data-prose="585">，
固定提交，§1、定义 3.1。
本轮仅复用已核对原文的模式字典及空事件与归一化的区别。</span>


<a id="ref-moschovakis"></a>

**[9]** 
<span data-prose="586">Y. N. Moschovakis,</span>
[*<span data-prose="587">Kleene's Amazing Second Recursion Theorem</span>*](https://www.math.ucla.edu/~ynm/papers/1602-002-1.pdf)<span data-prose="588">,
The Bulletin of Symbolic Logic</span> **<span data-prose="589">16</span>**<span data-prose="590">(2), 189--239 (2010).
实际查读第 190 页 SRT 及证明、第 192--193 页自输出图灵机定理 1.1。
本文不声称已读取 Kleene 1938 原始扫描证明。</span>


<a id="ref-wootters"></a>

**[10]** 
<span data-prose="591">W. K. Wootters and W. H. Zurek,</span>
[*<span data-prose="592">A single quantum cannot be cloned</span>*](https://painterlab.caltech.edu/wp-content/uploads/2019/06/qe_wotters_no_cloning.pdf)<span data-prose="593">,
Nature</span> **<span data-prose="594">299</span>**<span data-prose="595">, 802--803 (1982),</span>
[<span data-prose="596">doi:10.1038/299802a0</span>](https://doi.org/10.1038/299802a0)<span data-prose="597">.
实际查读原刊两页的线性复制论证。</span>


<a id="ref-vidal"></a>

**[11]** 
<span data-prose="598">G. Vidal and R. F. Werner,</span>
[*<span data-prose="599">A computable measure of entanglement</span>*](https://arxiv.org/pdf/quant-ph/0102117)<span data-prose="600">,
Physical Review A</span> **<span data-prose="601">65</span>**<span data-prose="602">, 032314 (2002),</span>
[<span data-prose="603">doi:10.1103/PhysRevA.65.032314</span>](https://doi.org/10.1103/PhysRevA.65.032314)<span data-prose="604">.
实际使用原文开头的 negativity 定义与可分态局部转置正性；
式</span> [（4）](#eq:negativity) <span data-prose="605">的特殊族恒等式由本文自行证明。</span>


`\end{thebibliography}`

`\end{document}`
