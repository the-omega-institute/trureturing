# 算术级数交族的端点定理与内点障碍

## §0. 问题、记号与文献定理

记 \([N]=\{1,\ldots,N\}\)。有限算术级数（简称 AP）是 \(\{a,a+d,\ldots,a+kd\}\)，其中 \(d>0\)、\(k\geq0\)；一、二元非空集也视为 AP。集合族 \(\mathcal F\) 称为良交族，如果任意两个不同成员的交都是非空 AP。令 \(t(N)\) 为这种集合族的最大基数，并设
\[
 C_N=\binom N2+1,\qquad B(N)=C_N+\left\lfloor\frac{N-1}{4}\right\rfloor.
\]
Erdős 问题第 272 题要求确定 \(t(N)\) 及极值族。下列六项是引用的文献结论；其证明不在此重述。

**定理 1（文献，Szabó [Szabó 1999]）.** 对每个 \(N\geq1\)，\(t(N)\geq B(N)\)。

**定理 2（文献，Yang，arXiv:2607.23004，定理 1.1）.** 对 \(3\leq N\leq12\)，\(t(N)=B(N)\)。

**定理 3（文献，Yang，定理 1.4）.** 若良交族的所有成员有公共点，则其基数至多为 \(B(N)\)。

**定理 4（文献，Yang，引理 3.3）.** 设 \(\mathcal S\) 是整数区间 \([-l,r]\ni0\) 的任意族，其中 \(0\leq l\leq\Lambda\)、\(0\leq r\leq P\)、\(l+r\geq3\)。令 \(W(\mathcal S)\) 是被至少一个区间覆盖的数对 \(\{a,b\}\subseteq[-\Lambda,P]\setminus\{0\}\)，满足 \(\gcd(|a|,|b|)=1\) 且 \(\{0,a,b\}\) 不是 AP。则
\[
 |\mathcal S|\leq |W(\mathcal S)|+\mathbf1_{\min(\Lambda,P)\geq2}.
\]
这里是覆盖数，不预设每个区间都有不同的见证数对。

**定理 5（文献，Yang，定理 7.5）.** 若 \(N\geq10^4\)，\(|\mathcal F|>B(N)\)，且 \(\mathcal F\) 中所有至少四元的成员都是 AP，则其三元成员有公共点 \(c\)。

**定理 6（文献，Yang，命题 7.6）.** 在定理 5 的条件下，所有避开 \(c\) 的成员都是至少四元 AP；每个这样的 AP 长于 \(N/12\)，公差至多为 \(12\)。

## §1. 定位与明确阈值

定义
\[
 f(m)=\begin{cases}0&m\leq3,\\1&m=4,\\\lfloor(m+1)^2/4\rfloor-6&m\geq5,\end{cases}
 \qquad U(N)=\sum_{d=1}^{\lfloor(N-1)/3\rfloor}f(\lceil N/d\rceil).
\]

**定理 7.** 任一良交族中至少四元 AP 的数目至多为 \(U(N)\)。若 \(\mathcal G\cup P\) 是一族两两相容的至少四元 AP，则 \(|\mathcal G|+|P|\leq U(N)\)。

**证明.** 同公差 \(d\) 的两 AP 若相交，必在同一模 \(d\) 剩余类；作为该类中的整数区间，两两相交便有公共点。长度至多为 \(m=\lceil N/d\rceil\) 的一条线，在位置 \(j\) 处的含点区间有 \(j(m-j+1)\) 个。剔除长度一、二、三的区间并对 \(j\) 取最大，得到所列 \(f(m)\)；\(m=4\) 的例外值为 \(1\)。对各 \(d\) 相加。第二断言用于合族 \(\mathcal G\cup P\)；其跨族相容性确保仍可逐线应用同一计算。\(\square\)

**定理 8.** 设 \(\mathcal F\) 为至少四元成员全是 AP 且 \(|\mathcal F|>B(N)\) 的良交族。

1. 若 \(N\geq42\)，全部三元成员有公共点 \(c\)。两条不同公差线的相容性界还使这一结论在 \(N=36\) 及每个 \(N\geq38\) 成立；所述计数检验在 \(N=37\) 不成立。
2. 一旦三元成员有公共点，\(N\geq27\) 时没有二元成员避开该点。
3. 在上述条件下，\(N\geq242\) 时每个避点 AP 长于 \(N/12\)；\(N\geq172\) 时每个避点 AP 的公差至多为 \(12\)。这些是所列整数检验的永久阈值。

**证明.** 定理 3 排除公共点族。非公共点族没有单元成员，二元成员至多 \(N-1\) 个。若三元成员无公共点，Hilton–Milner 三元交族界给出至多 \(3N-8\) 个；因此
\[
 |\mathcal F|\leq U(N)+(N-1)+(3N-8).
\]
若三元成员都含 \(c\)，但存在二元避点成员，其每个三元成员的另外两点必须碰到这个二元集，故三元成员至多 \(2N-3\) 个。一个基数为 \(a\) 的避点成员允许的三元联结数恰为
\[
 g_N(a)=\binom{N-1}{2}-\binom{N-1-a}{2}
       =a(N-1)-\frac{a(a+1)}2.
\]
依次将 \(3N-8\)、\(2N-3\)、\(g_N(\lfloor N/12\rfloor)\) 和 \(g_N(\lfloor(N-1)/13\rfloor+1)\) 代入 \(U(N)+(N-1)+\cdot\leq B(N)\)，整数检验所得的末次失败值分别为 \(41,26,241,171\)。前三项的严格反设或第四项的 \(d\geq13\Rightarrow a\leq\lfloor(N-1)/13\rfloor+1\) 给出结论。\(N\leq8191\) 的逐项精确计算及 \(N\geq8192\) 的有理尾界由命令 `python3 -B tools/scripts/agent/openproblem/erdos272-localization-check.py` 核验；尾界使用 \(\sum d^{-2}<33/20\)、\(H_{\lfloor(N-1)/3\rfloor}\leq N/512\)，从而 \(U(N)\leq33N^2/80+NH_{\lfloor(N-1)/3\rfloor}+N/3\)。

较强的第一项有限结论来自不同公差的联合计数。对公差 \(d\ne e\) 及各自固定 Helly 点 \(p,q\)，令 \(C_d(p),C_e(q)\) 为相应含点长 AP 的全集，\(\nu_{de}(p,q)\) 为两全集之间“不相交”图的匹配数。König 定理给出相容并集的准确上界
\[
 M_{de}=\max_{p,q}\bigl(|C_d(p)|+|C_e(q)|-\nu_{de}(p,q)\bigr).
\]
对不重叠公差对作最大权匹配并从 \(U(N)\) 扣除节省量，得到 \(N=36,37,38,39,40,41\) 的 AP 上界分别为 \(500,541,564,599,627,670\)；对应排除无核三元族的上限 \(B(N)-4N+9\) 分别为 \(504,537,570,604,639,676\)。命令 `python3 -B tools/scripts/agent/openproblem/erdos272-localization-check.py` 穷举 \(p,q\) 与二部匹配核验这些整数。\(N\geq42\) 已由上一整数检验覆盖。\(\square\)

## §2. 端局量与 König 公式

固定 \(c\in[N]\)，置 \(V=[N]\setminus\{c\}\)。称非空族 \(\mathcal G\) 可容许，若其成员均为避开 \(c\) 的至少四元 AP，并且任意两个不同成员的交是非空 AP。定义
\[
 H=\bigcap_{A\in\mathcal G}A,\quad
 L=\{e\in\tbinom V2:e\cap A\ne\varnothing\ (A\in\mathcal G)\},
\]
\[
 P=\{Q:\ Q\text{ 是含 }c\text{ 的至少四元 AP},\ Q\cap A\text{ 为非空 AP }(A\in\mathcal G)\}.
\]
将 \(P\) 与 \(L\) 连为二部图：\(Q\sim e\) 当且仅当 \(e\subseteq Q\) 且 \(e\cup\{c\}\) 不是 AP；记最大匹配数为 \(\nu\)。\(\Phi(N,c,\mathcal G)\) 是避点成员恰为 \(\mathcal G\)、其余成员均含 \(c\) 且没有单元成员的良交族最大基数。

**定理 9（公式 (2)）.**
\[
 \boxed{\Phi(N,c,\mathcal G)=|\mathcal G|+|H|+|L|+|P|-\nu.}\tag{2}
\]

**证明.** 可加入的含点二元成员恰为 \(\{c,x\}\)，\(x\in H\)；三元成员恰为 \(\{c\}\cup e\)，\(e\in L\)；至少四元成员恰为 \(P\)。同类成员相容。两个 AP 的非空交仍为 AP，因为共同点构成模其公差最小公倍数的一个剩余类，再截取共同端点区间。含点二元成员与其他含点成员相容；两含点三元成员也相容。余下的冲突正是所定义二部图的边。König 定理给出该图最大独立集大小 \(|L|+|P|-\nu\)，代入即得。\(\square\)

## §3. 本原所有权与 Hall 约化

令 \(\varepsilon_c=\lfloor\min(c-1,N-c)/2\rfloor\)。数对 \(e=\{x,y\}\subseteq V\) 称为坏对，若 \(\{c,x,y\}\) 不是 AP。

**定理 10.** 每个 \(e=\{x,y\}\subseteq V\) 唯一归属公差 \(d=\gcd(|x-c|,|y-c|)\) 的过 \(c\) 线上本原对。写 \(a=(x-c)/d,b=(y-c)/d\)，则它为坏对恰当 \(b\notin\{-a,2a,a/2\}\)。

**证明.** \(a,b\) 互素且均非零；若在另一线上本原，其公差仍必须是两个距离的最大公因数。三点成 AP 恰当其中一点是另两点的平均值，即所列三种等式之一。\(\square\)

对 \(J\subseteq P\)，记 \(B_J\) 为 \(J\) 覆盖的所有坏对，\(N_L(J)=B_J\cap L\)。

**定理 11（Hall 约化）.** 有
\[
 |P|-\nu=\max_{J\subseteq P}\bigl(|J|-|N_L(J)|\bigr),\qquad
 \Phi\leq|\mathcal G|+|H|+|L|+\min\{|P|,\varepsilon_c+|B_P\setminus L|\}.\tag{3}
\]
特别地，
\[
 \Phi\leq\binom N2+1+\varepsilon_c+|\mathcal G|+|H|-N;\tag{4}
\]
故 \(|\mathcal G|+|H|\leq N\) 蕴含 \(\Phi\leq B(N)\)。

**证明.** 第一式是二部图 Hall 缺额公式。按含 \(c\) 的公差 \(d\) 分割 \(J\)，对每条线上的任意子族应用定理 4：该子族至多比其所覆盖的本原坏对多 \(\mathbf1_{2d\leq\min(c-1,N-c)}\) 个。本原对的所有权由定理 10 保证不同线之间不重叠；求和得到 \(|J|\leq|B_J|+\varepsilon_c\)。从 \(B_J\) 删除不属于 \(L\) 的对，便得 \(|J|-|N_L(J)|\leq\varepsilon_c+|B_P\setminus L|\)。同时缺额至多 \(|P|\)，给出 (3)。由于 \(|B_P\setminus L|\leq\binom{N-1}{2}-|L|\)，整理得 (4)。最后 \(\varepsilon_c\leq\lfloor(N-1)/4\rfloor\)。\(\square\)

## §4. 资源计数与联合匹配

置 \(g=|\mathcal G|,h=|H|,p=|P|\)，\(Z=\binom V2\setminus L\)，\(z=|Z|\)，\(t=g+h-N\)，\(\delta=p-\nu\)。于是
\[
 s:=\binom N2+1-\Phi=z-t-\delta.\tag{5}
\]

**定理 12（资源计数）.** 选 \(A_0\in\mathcal G\)。若 \(\mathcal G\setminus\{A_0\}\) 可单射地配给两类互不混淆的资源：\(R\subseteq Z\) 中与所配避点 AP 不相交的对，以及 \(S\subseteq V\setminus H\) 中与所配 AP 不相交的点；又若 \(P\) 中至少 \(p-e\) 个 AP 可单射地配给 \(R\) 外、被该 AP 包含的坏对，则 \(\delta\leq z-|R|+e\) 且 \(s\geq-e\)。全匹配时，可选出 \(\delta\) 个 AP，使它们分别配给 \(Z\setminus R\) 中被自身包含的不同坏对。

**证明.** \(g-1=|R|+|S|\) 且 \(|S|\leq N-1-h\)，所以 \(t\leq|R|\)。设 AP 匹配中有 \(k\) 个像落在 \(Z\)。余下至少 \(p-e-k\) 条边属于定理 9 的图，故 \(\delta\leq e+k\leq e+z-|R|\)，再用 (5)。全匹配的强化从一组 \(P\) 到 \(L\) 的最大匹配出发，对其未匹配的 \(\delta\) 个 AP 沿全匹配与 \(L\)-匹配交替行走。路径不可能终止于未匹配的 \(L\) 对，否则可增广；故终止于不同的 \(Z\setminus R\) 对。翻转这些不相交路径即可。\(\square\)

构造联合图 \(\mathcal J\)：左侧为 \(\mathcal G\sqcup P\)，右侧为 \((V\setminus H)\sqcup(Z\cup B_P)\)；避点 AP 接到与自身不相交的点或对，\(Q\in P\) 接到自身所含坏对。记左侧缺额为 \(D_{\mathcal J}\)。对于 \(X\subseteq\mathcal G\)，写 \(H_X=\bigcap X\)、\(Z_X=\bigcup_{A\in X}\binom{V\setminus A}{2}\)，并约定 \(H_\varnothing=V\)。

**定理 13（联合 Hall 式）.**
\[
 s\geq1-D_{\mathcal J}.\tag{6}
\]
并且 \(D_{\mathcal J}\leq1+\varepsilon_c\) 当且仅当对每个 \(X\subseteq\mathcal G\)、\(Y\subseteq P\) 都有
\[
 |Z_X\setminus B_Y|+|B_Y|-|Y|
 \geq |X|+|H_X|-N-\varepsilon_c.\tag{7}
\]

**证明.** 最大联合匹配若留下 \(u\) 个避点 AP 和 \(v\) 个含点 AP，则 \(D_{\mathcal J}=u+v\)。设已匹配避点 AP 使用 \(R\) 个对资源；点资源至多 \(N-1-h\)，故 \(|R|\geq t+1-u\)。已匹配含点 AP 至多 \(z-|R|\) 个使用 \(Z\) 对，其余给出定理 9 图中的边，因此 \(\delta\leq v+z-|R|\)。代入 (5) 得 (6)。联合图中 \(X\sqcup Y\) 的邻域恰为 \((V\setminus H_X)\sqcup(Z_X\cup B_Y)\)。Hall 缺额公式给出 \(|N(X\sqcup Y)|\geq|X|+|Y|-1-\varepsilon_c\)；展开并移项即 (7)，反向移项亦成立。\(\square\)

## §5. 端点及邻端点

在 \(c=1\) 时写 \(m=N-1\)，把 \(V\) 平移为 \([m]\)。每个含点长 AP 形如 \(Q(d,k)=\{0,d,\ldots,kd\}\)，\(k\geq3\)，其终端像为 \(w(Q)=\{(k-1)d,kd\}\)。令 \(W_F=w(P(F))\)。终端像彼此不同、本原且为坏对：像的差给出 \(d\)，最大点给出 \(k\)，而 \(\gcd(k-1,k)=1\)、\(k\geq3\)。

**定理 14（单公差端点）.** 若 \(c\in\{1,N\}\) 且 \(\mathcal G\) 中避点 AP 只有一种公差，则 \(\Phi\leq C_N\)。

**证明.** 反射到 \(c=1\)。避点 AP 在同一剩余类线上形成两两相交区间，公共交非空。令 \(T\) 为这条线在 \(V\) 中的全体点；若 \(T\in\mathcal G\)，取 \(A_0=T\)，否则任取 \(A_0\)。对其余每个区间，若左右各有紧邻区间外点，配给这两个点组成的对；若只有一边有紧邻点，配给该点。前者在 \(Z\)，后者在 \(V\setminus H\)。双侧像恢复区间的两个端点，单侧像恢复自由端点，且左右两种单侧像落在 \(H\) 的不同侧，所以此配给单射。终端像不能等于双侧像：若等于，该避点区间全部位于含点 AP 的两个相邻点之间，因而与之不相交，违背 \(Q\in P\)。将 \(P\) 全部配给终端像，定理 12 取 \(e=0\) 即得。\(\square\)

**定理 15（单公差邻端点）.** 若 \(c\in\{2,N-1\}\) 且避点 AP 只有一种公差，则 \(\Phi\leq C_N\)。

**证明.** 反射到 \(c=2\)，记避点公差为 \(d_0\)。若避点成员都在 \(2\) 右侧，就在其右侧完整剩余线上使用定理 14 的资源单射。含 \(2\) 的长 AP 或单侧向右，或为 \([1,b]\)，\(b\geq4\)。前一类配给最右两个点，后一类配给 \(\{1,b\}\)。终端像与所保留双侧资源对不碰撞，原因仍是区间落入相邻点空隙；跨点像含 \(1\)，资源对全在右侧。

若某避点成员含 \(1\)，则 \(d_0\geq2\)，全部避点成员位于模 \(d_0\) 的 \(1\) 类。对该完整剩余线作同一资源单射。跨点像 \(\{1,b\}\) 若与资源对冲突，该资源对应的避点 AP 从 \(1+d_0\) 延至 \(b-d_0\)；至少四点迫使 \(b\geq1+5d_0\geq11\)。在 \(d_0=2\) 时改配 \(\{4,b\}\)，在 \(d_0\geq3\) 时改配 \(\{3,b\}\)。首点不在避点剩余类，故不是保留资源；相对 \(c=2\) 的坐标最大公因数分别为 \(\gcd(2,b-2)=1\)（此时 \(b\) 为奇数）及 \(\gcd(1,b-2)=1\)。\(b\) 的下界保证坏对性质。不同 \(b\) 的改配像不同；改配像、原跨点像、其他公差的终端像，以及差为一的本公差终端像之间也不相同。由定理 12 得结论。\(\square\)

对混合公差族 \(F\)，定义 \(Z_F=\bigcup_{A\in F}\binom{V\setminus A}{2}\)。端点所需的自族不等式为
\[
 |Z_F\setminus W_F|\geq |F|+|H_F|-N.\tag{8}
\]
若每个非空子族都满足 (8)，则由于 \(W_F\subseteq W_X\)（\(X\subseteq F\)），用于 \(X\) 的资源图 \((Z_X\setminus W_F)\sqcup(V\setminus H_X)\) 至少有 \(|X|-1\) 个邻居。Hall 定理给出至多一个避点成员未配资源；与含点 AP 的终端全匹配合用定理 13，即 \(s\geq0\)。

**定理 16（无公差一的混合端点）.** 若 \(c\in\{1,N\}\)，\(F\) 混合公差且不含公差一，则 (8) 成立。

**证明.** 反射至 \(c=1\)。令 \(T_m\) 包含所有可能的终端对，\(\tau(m)=|T_m|=\sum_{d=1}^{\lfloor m/3\rfloor}(\lfloor m/d\rfloor-2)\)；像的差与右端点决定 \((d,k)\)，故此计数准确且 \(W_F\subseteq T_m\)。混合公差中有 \(d\geq3\) 的成员 \(A\)。于是 \(b=|V\setminus A|\geq\lfloor2m/3\rfloor\)，而 \(\binom{V\setminus A}{2}\subseteq Z_F\)，故
\[
 |Z_F\setminus T_m|\geq\binom b2-\tau(m).\tag{9}
\]
定理 7 给出 \(|F|\leq\sum_{d=2}^{\lfloor(N-1)/3\rfloor}f(\lceil N/d\rceil)\)。\(N\geq300\) 时，\(\tau(m)\leq N(1+\log N)\)、\(|F|\leq N^2/6+N\log N+N/3\)、\(b\geq2N/3-2\)，因而 (9) 与 \(|F|\) 的差至少为 \(N^2/18-2N\log N-3N+3\geq N^2/180+3>0\)。其中 \(\log N\leq N/50\) 对 \(N\geq300\) 成立。

对于 \(48\leq N\leq299\)，精确整数式
\[
 Q(N)=\binom{\lfloor2(N-1)/3\rfloor}{2}-\tau(N-1)
 -\sum_{d=2}^{\lfloor(N-1)/3\rfloor}f(\lceil N/d\rceil)
\]
的最小值为 \(0\)，在 \(N=53\) 取得。对于 \(13\leq N\leq47\) 且有 \(d\geq4\)，以 \(b\geq m-\lceil m/4\rceil\) 代替，最小值为 \(4\)，在 \(N=14\) 取得。余下差集为 \(\{2,3\}\)。其 \(11\leq N\leq47\) 的粗界只在 \(N=11,13,14,15,17\) 为负，数值依次为 \(-4,-2,-3,-1,-6\)；逐一枚举所有公差三的避点 AP，\(\binom{V\setminus A}{2}\setminus T_m\) 的最小大小依次为 \(10,20,20,27,34\)，而 \(|F|\) 的相应上界为 \(7,13,13,17,25\)。命令 `python3 -B tools/scripts/agent/openproblem/erdos272-endgame-check.py` 逐值核验这些精确整数式。\(N\leq10\) 时混合无公差一族不存在，因为公差三的四元 AP 已放不进 \(V\)。故 \(|Z_F\setminus T_m|\geq|F|\)，而 \(|H_F|\leq N-1\)，得 (8)。\(\square\)

**定理 17（含公差一的混合端点）.** 若 \(c\in\{1,N\}\)，\(F\) 混合公差且含公差一，则 (8) 成立。

**证明.** 反射到 \(c=1\)，令公差一子族为 \(F_1\)，其他为 \(F_*\)，\(I=\bigcap F_1=[a,b]\subseteq[m]\)，\(l=|I|\)，\(L=a-1,R=m-b,e=L+R=m-l\)。取 \(A\in F_*\)，并写 \(W(A)\) 为所有碰到 \(A\) 的含点长 AP 的终端像。置
\[
 S(A,I)=\{\{x,y\}\subseteq V\setminus A:\{x,y\}\cap I\ne\varnothing\}
 \cup\binom{[1,a-1]}2\cup\binom{[b+1,m]}2.
\]
这些对都在 \(Z_F\)：前一类避开 \(A\)，左、右两类各避开 \(F_1\) 中相应的端点极值区间。对 \(F_1\) 中每个 \(x>1,y<m\) 的区间 \([x,y]\)，对 \(\{x-1,y+1\}\) 在 \(Z_F\setminus W_F\)，且一端在 \(I\) 左、另一端在右，故不属于 \(S(A,I)\)；这些对互异。若它是某个可容许 AP 的终端像，该区间将处于两个相邻 AP 点之间，与可容许性矛盾。接触 \(1\) 或 \(m\) 的 \(F_1\) 区间至多 \(e+1\) 个，因此
\[
 |Z_F\setminus W_F|\geq |F_1|-(e+1)+|S(A,I)\setminus W(A)|.\tag{10}
\]
令 \(j=2\)，若 \(F_*\) 全为公差二；否则取公差至少三的 \(A\) 并令 \(j=3\)。由定理 7 的逐线计数，\(|F_*|\leq G_2(m)=f(\lceil m/2\rceil)\) 或 \(|F_*|\leq G_3(m)=\sum_{d=2}^{\lfloor m/3\rfloor}f(\lceil m/d\rceil)\)。又 \(|H_F|\leq|A\cap I|\leq\lceil l/j\rceil\)。设 \(b_0=m-\lceil m/j\rceil\)、\(u_0=l-\lceil l/j\rceil\)。前一类 \(S\) 至少有 \(\binom{b_0}2-\binom{b_0-u_0}2\) 个对，两侧池另给 \(\binom L2+\binom R2\) 个；\(|W(A)|\leq\tau(m)\)。代入 (10) 后，(8) 的足够整数裕量恰为
\[
 M_j=\binom{b_0}2-\binom{b_0-u_0}2+\binom L2+\binom R2
 +l-\lceil l/j\rceil-\tau(m)-G_j(m).\tag{11}
\]
固定 \(m,l\) 时两侧二项式之和在 \(L,R\) 平衡处最小。命令 `python3 -B tools/scripts/agent/openproblem/erdos272-endgame-check.py` 精确核验 \(46\leq m\leq999\)、\(1\leq l\leq m\) 的 (11)：\(j=2\) 的最小值为 \(7\)（\(m=47\)），\(j=3\) 的最小值为 \(31\)（\(m=49\)）。

对于 \(m\geq1000\)，\(\binom L2+\binom R2\geq e^2/4-e/2\) 且 \(b_0-u_0\leq\lceil(j-1)e/j\rceil\)，所以 (11) 的资源部分至少为 \(\binom{b_0}2-2m\)。利用 \(\tau(m)\leq m(1+\log m)\) 与
\[
 G_2(m)\leq m^2/16+m/2+1,\qquad
 G_3(m)\leq m^2/6+m\log m+m/3
\]
得到 \(M_2\geq m^2/16-m\log m-17m/4\)、\(M_3\geq m^2/18-2m\log m-13m/3+1\)。因 \(\log m\leq m/100\)，两者分别至少为 \(19m^2/400\) 和 \(11m^2/360+1\)，均为正。

最后，对 \(m\leq45\) 且粗裕量 (11) 为负的参数，直接以实际集合 \(S(A,I)\setminus W(A)\) 检验更强的不等式
\[
 |S(A,I)\setminus W(A)|+l-|A\cap I|\geq G_j(m).\tag{12}
\]
命令 `python3 -B tools/scripts/agent/openproblem/erdos272-endgame-check.py` 枚举全部相应 \((m,A,I)\)：\(j=2\) 共 \(224176\) 项，\(j=3\) 共 \(138\) 项，两支 (12) 的最小裕量均为 \(3\)。枚举还包含不可能组成相容族的参数，故覆盖所需情形。\(m<7\) 无四元公差二避点 AP，\(m<10\) 无四元公差至少三避点 AP。三段合并即得 (8)。\(\square\)

**定理 18（全部端点）.** 对任意非空可容许 \(\mathcal G\) 及 \(c\in\{1,N\}\)，有 \(\Phi(N,c,\mathcal G)\leq C_N\)。

**证明.** 每个非空子族或为单公差族，或无公差一的混合族，或含公差一的混合族。定理 14、16、17 分别给出所需资源单射或 (8)。对固定全族，\(W_{\mathcal G}\subseteq W_X\) 允许把各子族的 (8) 用于同一个终端禁用集；Hall 定理使其避点资源匹配至多漏一个。含点 AP 则全由互异终端像匹配，故定理 13 给出 \(s\geq0\)。反射处理 \(c=N\)。\(\square\)

## §6. 有效充分条件的反例

以下否定的都是辅助不等式；它们不否定 \(\Phi\leq B(N)\)。

**定理 19.** 将 (3) 中的 \(|B_P\setminus L|\) 全部按可用缺额计入，所得充分条件
\[
 |\mathcal G|+|H|+|L|+\min\{|P|,\varepsilon_c+|B_P\setminus L|\}
 \leq\binom{N-1}{2}+N
\]
是假的。

**证明.** 取 \(N=7,c=1\)，\(\mathcal G=\{[2,5],[2,6],[2,7],[3,6],[3,7]\}\)。直接交集给 \(|H|=3\)，十五个候选联结对中恰 \(\{2,7\},\{6,7\}\) 不在 \(L\)，故 \(|L|=13\)。满足全部避点区间的含点长 AP 有五个；两个缺失对均为被覆盖坏对，且 \(\varepsilon_c=0\)。左侧为 \(5+3+13+2=23\)，右侧为 \(\binom62+7=22\)。实际图的 \(\nu=5\)，公式 (2) 给 \(\Phi=21\)。\(\square\)

**定理 20.** 充分条件
\[
 z\geq g+h-N+p-\left\lfloor\frac{N-1}{4}\right\rfloor\tag{13}
\]
在无穷多个 \(N\) 的混合公差、多避点成员情形下失败。

**证明.** 任取偶数 \(k\geq36\)，令
\[
 N=64k+1,\ c=32k+1,\ u=2k+2,\ v=62k-2,
 \quad H_4=\{u,u+4,\ldots,v\}.
\]
对 \(d=2,4\)，取全部 \([u-id,v+jd]_d\subseteq[N]\)（\(i,j\geq0\)），组成 \(\mathcal G\)。所有成员包含 \(H_4\)，避开奇数 \(c\)；\(H_4\) 自身在族中，所以 \(H=H_4\)，而 \(L\) 恰为碰到 \(H_4\) 的对。左右扩展分别计数给出
\[
 g=(k+1)(k+2)+(k/2+1)^2=5k^2/4+4k+3,
 \quad h=15k,\quad t=5k^2/4-45k+2>0,\quad z=\binom{49k}{2}.
\]
对任意奇数 \(d\in\{1,3,5,7,9\}\)，每个含 \(c\) 的四元以上公差 \(d\) 的 AP 在离 \(c\) 至多 \(3d\) 处碰到 \(H_4\)，故属于 \(P\)。其数为 \((\lfloor32k/d\rfloor+1)^2-6\)。由于 \(\sum_{d=1,3,5,7,9}d^{-2}=117469/99225>151/128\)，得到 \(p>1208k^2-30\)，而
\[
 z-t+\lfloor(N-1)/4\rfloor=4797k^2/4+73k/2-2.
\]
故 \(p-(z-t+\lfloor(N-1)/4\rfloor)>35k^2/4-73k/2-28>0\)，证明 (13) 失败。\(k=36\) 时，逐个奇公差计数给 \((g,h,z,p)=(1767,540,1554966,1640365)\)，(13) 的左减右为 \(-84825\)；命令 `python3 -B tools/scripts/agent/openproblem/erdos272-endgame-check.py` 核验该精确值。

此族并不违反端局目标：对 \(l=3,7,\ldots,30k-1\)、\(1\leq r\leq32k\)、\(r\ne l\)，把 \([c-l,c+r]\) 配给 \(\{c-l,c+r\}\)。左端在 \(H_4\)，这些是不同的图边，给出 \(\nu\geq(15k/2)(32k-1)\)。偶公差过 \(c\) 的 AP 全是奇数，不能碰到 \(H_4\)；对奇公差忽略可容许性与短区间限制，则 \(p\leq\sum_{d\leq\lfloor64k/3\rfloor,\ d\text{ 奇}}(32k/d+1)^2\)。利用 \(\sum_{d\geq1,\ d\text{ 奇}}d^{-2}\leq1+1/9+1/25+1/49+1/14<5/4\)、\(\sum_{d\leq D}d^{-1}\leq1+\log D\) 及 \(\log(64k/3)\leq k\)，得到 \(p\leq1344k^2+256k/3\)。代回 (5) 可得 \(s\geq381k^2/4-217k/3-2>0\)。\(\square\)

**定理 21.** 对某条含点公差线，保留定理 4 的 \(\varepsilon_d\) 之后再删去避点 AP 所占的保留坏对，所得逐线 Hall 不等式可能失败。

**证明.** 取 \(N=25,c=13\)，避点公差三，\(T=\{2,5,8,11,14,17,20,23\}\)、\(A=\{8,11,14,17,20\}\)、\(\mathcal G=\{T,A\}\)。\(T\) 是完整剩余线；\(A\) 两侧紧邻外点的保留对为 \(\{5,23\}\)。公差二过 \(c\) 的坐标线为 \(-6,\ldots,6\)。全部 \((l,r)\in[0,6]^2\)、\(l+r\geq3\) 的 \(43\) 个区间都碰到 \(A\)：\(l\geq1\) 时碰到 \(11\)，\(l=0\) 时 \(r\geq3\)，碰到 \(17\)。被覆盖的本原坏对为 \(42\) 个；同号两侧各 \(10\) 个，异号六列依次有 \(5,3,4,3,5,2\) 个。保留对的本线坐标为 \((-4,5)\)，是其中一个本原坏对。删后只有 \(41\) 个对供 \(43\) 个区间，而该线 \(\varepsilon_2=1\)，故 Hall 缺额至少为 \(2\)。(2) 的实际值为 \(236<C_{25}=301\)。\(\square\)

**定理 22.** 记 \(M(N,c)=\max_{\mathcal G}\Phi(N,c,\mathcal G)\)。向中间移动的严格单调性不成立：\(M(10,4)=41<42=M(10,5)\)。

**证明.** 两处分别只有 \(511\)、\(143\) 个非空相容避点 AP 子族。逐一用公式 (2) 的整数最大匹配计算，最大值分别为 \(41\)、\(42\)；相应唯一取极值的避点族为 \(\{[5,10]\}\) 和 \(\{\{1,4,7,10\}\}\)。命令 `python3 -B tools/scripts/agent/openproblem/erdos272-endgame-check.py` 穷尽这些子族并复算最大值。\(\square\)

**定理 23.** 单靠删除一个非中心点并对余下标号保序压缩，不能把每个端局族归纳为较小的同类端局族。

**证明.** 对任意 \(N\geq5\) 取 \(c=1\) 与唯一避点成员 \(A=[N-3,N]\)。删除 \(N\) 后该成员只有三个点，其他成员仍含 \(c\)，因此压缩后的像中没有至少四元避点 AP。更强地，令 \(N=3d+1\)、\(d\geq2\)，\(A=\{1,1+d,1+2d,N\}\)，\(c\notin A\)。删除 \(A\) 的点使它不足四点；删除 \(A\) 外任一点使三个原本相等的间隙中恰一个由 \(d\) 减为 \(d-1\)，四点像不再是 AP。任一删除位置均无同类避点成员可保留。\(\square\)

## §7. 有限计算命题

**定理 24（有限计算命题）.** 对 \(N\leq18\)，至少四元成员均为 AP 的良交族满足 \(|\mathcal F|\leq B(N)\)。其中 \(3\leq N\leq12\) 是定理 2 的无条件结论；\(N=13\) 的完整二元整数规划，以及 \(14\leq N\leq18\) 的分类二元整数规划，其求解器均报告不可行。后者所核验的对象是下述整数规划的求解器状态，而非可独立检查的不可行性证明。

**证明.** \(N=1,2\) 时，非空且两两相交的子集族分别至多有 \(1,2\) 个，等于 \(B(1),B(2)\)。对每个二元成员、三元成员及至少四元 AP 设一个 \(0\)-\(1\) 变量，对交为空或非 AP 的每对成员施加和至多一，并要求变量总和至少 \(B(N)+1\)。非星形族没有单元成员；星形族由定理 3 已受界。分类整数规划将三元族分为无公共点及有公共点 \(c\) 两支；前支加 Hilton–Milner 界，后支逐点枚举 \(c\) 并要求避点成员。固定公差的 AP 还受定理 7 的 Helly 选点约束。这些约束都由候选反例满足。命令 `python3 -B tools/scripts/agent/openproblem/erdos272-case-milp.py` 给出 \(N=13\) 完整整数规划的不可行状态；同一路径的命令分别加 `--n 14`、`--n 15`、`--n 16`、`--n 17`、`--n 18`，给出全部分类分支的不可行状态。此处只据所列求解器状态作有限计算结论；没有独立的形式化不可行性证明迹。\(\square\)

**定理 25（有理 LP 证书）.** 对 \(N\leq16\) 的每个中心，固定中心冲突图的全部极大团 LP（附 \(0\leq x_v\leq1\) 及至少选一个避点 AP）若可行，其最优值至多为 \(B(N)\)。共有 \(121\) 个可行中心实例；最小 \(B(N)\) 裕量为 \(1\)。\(N=14,c=7\) 的分数最优值为 \(1663/18=C_{14}+7/18\)，所以较强界 \(C_N\) 不能由此 LP 普遍推出。

**证明.** 每个顶点代表一个避点长 AP、含点二元集、含点三元集或含点长 AP；冲突边恰为交为空或非 AP。每个极大冲突团的变量和至多一。原始变量的非负性、单点上界及避点变量和至少一，组成所述 LP。对每个可行实例，求解得到的数值原始解 \(x\) 与对偶权 \(y\) 化为有理数；逐行以精确算术验证原始可行，对每个顶点验证对偶覆盖至少一，并验证两目标有理数相等且不超过 \(B(N)\)。命令 `python3 -B tools/scripts/agent/openproblem/erdos272-lp-certificates.py` 重新生成图与全部极大团，调用 HiGHS 求解，再以 `Fraction` 核验上述每个等式与不等式，不使用预存证书。其余中心不可行是由于根本没有长避点 AP。由此有理证书给出所述精确 LP 上界，而整数端局族必满足 LP 约束。\(\square\)

上述整数式、有理证书与求解器状态的核验命令及墙钟时间列于下表。所有命令均从仓库根目录执行，`real` 取 `/usr/bin/time -p` 所报的秒数。

| 对象 | 命令 | `real`（秒） |
| --- | --- | ---: |
| 端点整数式与反例 | `/usr/bin/time -p python3 -B tools/scripts/agent/openproblem/erdos272-endgame-check.py` | 38.39 |
| 定位阈值与双线界 | `/usr/bin/time -p python3 -B tools/scripts/agent/openproblem/erdos272-localization-check.py` | 7.30 |
| 有理 LP 证书 | `/usr/bin/time -p python3 -B tools/scripts/agent/openproblem/erdos272-lp-certificates.py` | 7.33 |
| \(N=13\) 完整整数规划 | `/usr/bin/time -p python3 -B tools/scripts/agent/openproblem/erdos272-case-milp.py` | 72.01 |
| \(N=14\) 分类整数规划 | `/usr/bin/time -p python3 -B tools/scripts/agent/openproblem/erdos272-case-milp.py --n 14` | 207.28 |
| \(N=15\) 分类整数规划 | `/usr/bin/time -p python3 -B tools/scripts/agent/openproblem/erdos272-case-milp.py --n 15` | 414.59 |
| \(N=16\) 分类整数规划 | `/usr/bin/time -p python3 -B tools/scripts/agent/openproblem/erdos272-case-milp.py --n 16` | 908.53 |
| \(N=17\) 分类整数规划 | `/usr/bin/time -p python3 -B tools/scripts/agent/openproblem/erdos272-case-milp.py --n 17` | 2289.24 |
| \(N=18\) 分类整数规划 | `/usr/bin/time -p python3 -B tools/scripts/agent/openproblem/erdos272-case-milp.py --n 18` | 5064.98 |

## §8. 内点待证不等式

**假设 E.** 对每个 \(N\)、每个内点 \(2\leq c\leq N-1\) 及每个非空可容许 \(\mathcal G\)，
\[
 \Phi(N,c,\mathcal G)\leq B(N),\qquad
 s\geq-\left\lfloor\frac{N-1}{4}\right\rfloor.\tag{14}
\]
定理 11 已处理 \(g+h\leq N\)，定理 15 已处理 \(c=2,N-1\) 的单公差族，定理 25 已处理 \(N\leq16\)。其余情形中，一个明确的充分条件是对全部 \(X\subseteq\mathcal G\)、\(Y\subseteq P\) 证明 (7)，即
\[
 |Z_X\setminus B_Y|+|B_Y|-|Y|
 \geq |X|+|H_X|-N-\varepsilon_c.
\]
它精确等价于联合图 \(D_{\mathcal J}\leq1+\varepsilon_c\)，而定理 13 说明该条件推出 (14)。若只允许某条含点公差线使用避点资源未占的本原坏对，则所需逐线 Hall 条件还必须逐子族检验；定理 21 表明保留每线原有的一个缺额并不足够。对邻端点混合公差及更深内点的其余族，(7) 或另一能直接控制 \(\delta\) 的不等式仍为待证。

## 参考文献

1. P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L’Enseignement Mathématique 28, Genève, 1980.
2. A. J. W. Hilton and E. C. Milner, “Some intersection theorems for systems of finite sets,” *Quart. J. Math. Oxford Ser.* (2) **18** (1967), 369–384.
3. M. Simonovits and V. T. Sós, “Intersection properties of subsets of integers,” *European J. Combin.* **2** (1981), 363–372.
4. T. Szabó, “Intersection properties of subsets of integers,” *European J. Combin.* **20** (1999), no. 5, 429–444.
5. Zhanfu Yang, “Exact values and exact upper bounds for families of integers with arithmetic progression intersections (Erdős Problem #272),” arXiv:2607.23004 (2026), https://arxiv.org/abs/2607.23004.
6. T. F. Bloom, “Erdős Problem #272,” https://www.erdosproblems.com/272.
