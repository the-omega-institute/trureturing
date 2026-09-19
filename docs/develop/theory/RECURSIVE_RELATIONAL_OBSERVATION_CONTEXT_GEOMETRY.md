# 递归关系观察：可执行上下文几何

空间拼接、时间接续和记忆更新都可以作为带输入输出的关系操作。要用一份几何比较这些操作，首先必须固定哪些上下文实际允许执行，以及一个上下文怎样接到另一个上下文之后。本卷以有类型的配置、允许箭头和带度量的读数为共同数据，构造保留全部指定行为、满足指定增益的最小扩展伪度量。任意参数的笛卡尔代数是它的一种特化；取得常量、复制资源和拼接共同来源的权限则由实际语言决定。

[RRO主卷](RECURSIVE_RELATIONAL_OBSERVATION.md) 第120节给出精确实验行为与最小表示，第121节研究保留式档案、观察核细化与正交信息增量，第122节区分取反的保持、乘法的弱化与投影边界耦合，第124节保留共同来源，第125–128节研究线性响应、记忆和概率，第133–136节研究运输与资源。本卷增加这些接口在有限误差下的组合条件。一个距离由全部允许实验定义，不代表观察者已经执行这些实验；有限预算的可取得部分在第7节另行构造。

## 1. 配置、允许箭头与失败

**定义 1.1（带增益的有类型实验语言）。** 设 $S$ 为类型集合。每个类型 $s$ 有配置集合 $X_s$；配置包括当前任务所需的对象、记录、共享来源与资源状态。每个允许生成箭头 $h:s\to t$ 指定一个总函数
$$
h:X_s\to X_t
$$
和有限正增益 $L_h>0$。每个类型有一族基础读数 $f:X_s\to Y_f$，其中 $Y_f$ 配扩展度量 $\rho_f:Y_f\times Y_f\to[0,\infty]$：对称、满足三角不等式，且 $\rho_f(u,v)=0$ 当且仅当 $u=v$。普通有限值度量是其特例。

一个允许上下文 $C:s\to t$ 是类型匹配的有限箭头路径。空路径是恒等上下文。路径作用取函数复合，增益取乘积：
$$
\ell(\mathrm{id}_s)=1,\qquad
\ell(C\circ h)=\ell(C)L_h.
$$
一个闭实验是上下文 $C:s\to t$ 后接基础读数 $f:X_t\to Y_f$。所有生成箭头与读数构成集合，所以以下测试上确界具有固定索引集合。相同函数的两条执行路径可以具有不同的增益或代价，在这些数据被证明可识别之前不将路径合并。

此处 $L_h$ 是所研究接口指定的增益要求；不预先假定任意给定的有限状态度量都满足它。第2节证明何时存在最小的兼容距离，以及不相容要求怎样导致无穷距离。严格正性用于路径除法；常值操作可以使用任意经过验证的正上界，并不因此失去其实际零变化性质。

**约定 1.2（部分动作的总化）。** 对部分动作 $h:D_h\to X_t$，可以在各类型加入声明的失败结果，将域外输入送往相应失败标签；失败之后的接续按明确的传播或恢复规则定义。成功、失败和任务所需原因进入读数。也可以使用共同定义域作为类型，但接续必须确实保持相应类型。把两个各自合法的输入拼成一个元组，需要另证这个元组合法。

这些总函数描述一次协议怎样作用于任一候选配置，不赋予在未知配置上提前读取隐藏信息的权限。例如自适应策略可以根据已经读到的历史选择下一步；它不能根据未读到的变量选择分支。所需策略状态可纳入配置，已声明的策略作为允许箭头。所有未来允许路径与某一条已经执行的历史是不同的对象。

**命题 1.3（成对删除失败会破坏伪度量）。** 若比较两个配置时只保留对二者都成功的实验，所得成对测试上确界不一定满足三角不等式，也不一定产生传递的零距离关系。

**证明。** 取 $X=\{a,b,c\}$，当前读数恒定，另有部分实验 $e$ 满足 $e(a)=0,e(c)=1$，在 $b$ 处失败。输出用离散距离。只比较双方成功的实验，并把空族上确界取零，得到
$$
d(a,b)=0,\qquad d(b,c)=0,\qquad d(a,c)=1.
$$
所以 $d(a,c)>d(a,b)+d(b,c)$，同时 $a,b$ 与 $b,c$ 零距离而 $a,c$ 非零距离。此处每一对输入使用了不同的测试索引集合。将失败保留为单独结果，才能对同一个测试函数拉回度量。$\square$

**命题 1.4（准入边界不由数值接近自动保持）。** 设实数状态上的动作在 $x\ge0$ 时成功、在 $x<0$ 时失败，成功与失败的输出距离为一。它相对于输入的通常距离不存在全局有限 Lipschitz 常数。

**证明。** 对任意 $\varepsilon>0$，输入 $\varepsilon,-\varepsilon$ 的距离是 $2\varepsilon$，输出距离是一。若有统一有限常数 $L$，则所有 $\varepsilon>0$ 都满足 $1\le2L\varepsilon$，矛盾。$\square$

若任务要求合法性完全保持，可把域保持作为精确关系运输，或给成功与失败之间无穷距离。若选有限处罚，得到的是对应处罚下的近似保证，仍须用实际误差与准入间隔证明某次动作不会跨界。

## 2. 最小上下文距离与递归闭合

**定义 2.1（完整上下文距离）。** 对 $x,y\in X_s$，置
$$
D_s(x,y)=\sup_{\substack{C:s\to t\\f:X_t\to Y_f}}
\frac{\rho_f(f(Cx),f(Cy))}{\ell(C)}.
\tag{2.1}
$$
空测试族的上确界取零。每条有限路径的增益均有限且严格正，因此除法没有零分母；$D_s$ 可以取无穷值。

**定理 2.2（最小增益兼容几何）。** 定义2.1满足：

1. 每个 $D_s$ 是扩展伪度量。
2. $D_s(x,y)=0$ 当且仅当全部允许闭实验在 $x,y$ 上取得相同结果。
3. 每个基础读数满足 $\rho_f(fx,fy)\le D_s(x,y)$，每个允许生成箭头满足
$$
D_t(hx,hy)\le L_hD_s(x,y).
\tag{2.2}
$$
4. 若另一扩展伪度量族 $p_s$ 使全部基础读数为 $1$-Lipschitz，并使每条允许箭头满足相同的 $L_h$ 界，则 $D_s\le p_s$ 逐点成立。

因此 $D$ 自身满足所列要求，并且是满足这些要求的逐点最小者。一份全域有限的合格 $p$ 也给出 $D$ 全域有限的证书。

**证明。** 对固定实验 $(C,f)$，把 $\rho_f$ 沿 $f\circ C$ 拉回，再乘正数 $1/\ell(C)$，得到扩展伪度量。其上确界仍在对角线为零且对称。对任意 $x,y,z$，每一项满足
$$
\frac{\rho_f(fCx,fCz)}{\ell(C)}
\le D_s(x,y)+D_s(y,z),
$$
取上确界得到三角不等式，包括无穷值的情况。全部项非负，且读数度量分离点，所以零上确界等价于每个实验结果相等。恒等上下文给基础读数界。

对箭头 $h:s\to t$ 和输出实验 $(C,f)$，$C\circ h$ 仍是允许上下文，且 $\ell(C\circ h)=\ell(C)L_h$。于是
$$
\frac{\rho_f(fChx,fChy)}{\ell(C)}
\le L_hD_s(x,y).
$$
对输出实验取上确界得到式(2.2)。若 $p$ 满足同样的生成箭头条件，对路径长度归纳得到 $p_t(Cx,Cy)\le\ell(C)p_s(x,y)$。基础读数条件继而给每个实验的归一化差不超过 $p_s(x,y)$，取上确界得 $D_s\le p_s$。$\square$

**命题 2.3（递归闭合与有限深度）。** 令
$$
o_s(x,y)=\sup_{f:X_s\to Y_f}\rho_f(fx,fy),
$$
并在所有类型上的非负扩展值二元函数族 $p$ 上定义
$$
(\mathcal Tp)_s(x,y)=
\max\left\{o_s(x,y),
\sup_{h:s\to t}\frac{p_t(hx,hy)}{L_h}\right\}.
\tag{2.3}
$$
记 $D^{[N]}$ 为式(2.1)中只取长度至多 $N$ 的路径所得距离。则
$$
D^{[0]}=o,\qquad D^{[N+1]}=\mathcal T D^{[N]},
\qquad D=\sup_{N\ge0}D^{[N]},\qquad D=\mathcal TD.
\tag{2.4}
$$
而且 $D$ 是所有满足 $\mathcal Tp\le p$ 的非负扩展值函数族中逐点最小者，故也是 $\mathcal T$ 的最小不动点。

**证明。** 长度至多 $N+1$ 的路径要么为空，要么有首箭头 $h$，其后长度至多 $N$。相应增益分解为 $L_h$ 乘剩余路径增益，故测试上确界恰为式(2.3)。每条允许路径有限，所有路径是各有限深度族之并，因此 $D=\sup_ND^{[N]}$。把完整路径同样按空路径和首箭头分解，得 $D=\mathcal TD$。

若 $\mathcal Tp\le p$，则 $o\le p$ 且每条箭头的拉回满足 $p_t(hx,hy)\le L_hp_s(x,y)$。沿每条有限路径归纳后，用 $o\le p$ 得该路径的实验贡献不超过 $p_s(x,y)$，取上确界得 $D\le p$。此步甚至不需要竞争函数 $p$ 预先满足伪度量律。$\square$

式(2.3)将“当前能区分什么”与“允许操作后还能区分什么”放进同一个闭合规则。它关于这份语言的实验行为，不是物理系统停止变化的不动点。 主卷第121节的累计档案增长描述已取得记录及其可见空间的扩展；本卷路径上确界描述指定语言中全部允许实验的分离能力。允许一种实验、实际取得一次读数、保留这次记录是不同条件。主卷第122节的条件期望保留取反而可能破坏乘法，属于带共同概率律的投影接口；本卷的度量零核本身不替代该乘法缺陷和边界耦合。

**命题 2.4（增益与语言的单调性）。** 在相同实验语言上，若逐生成箭头增加增益 $L_h\le L'_h$，则 $D'\le D$，且两者具有相同零核。在保持旧路径及其增益不变的条件下增加允许箭头或基础读数，则完整距离不减，零核只会缩小。

**证明。** 前一种变化使每条路径分母不减，所以每个实验贡献不增；严格正有限的分母不改变某个贡献是否为零。后一种变化使旧测试族包含于新测试族，其上确界不减，实验相等的条件相应增强。$\square$

**命题 2.5（有限性不能靠指定收缩获得）。** 存在当前可区分的两个点、恒等更新 $h=\mathrm{id}$，使任何指定的 $0<L_h<1$ 都让其完整上下文距离为无穷。

**证明。** 设一个当前读数差为 $c>0$。长度 $n$ 的恒等更新路径具有增益 $L_h^n$，其贡献为 $cL_h^{-n}$。这些值无上界，故 $D(x,y)=\infty$。$\square$

因此较小增益是更强的兼容要求。它可能要求把某些可区分配置置于无穷远，不能免费把一个实际不收缩的过程变成有限距离中的收缩过程。

## 3. 行为商与保真辅助运输

**定义 3.1（实际行为像）。** 对每个类型，令
$$
\beta_s(x)=\bigl(f(Cx)\bigr)_{(C,f)},
\qquad Q_s=\beta_s[X_s].
$$
定义 $x\sim_sy$ 当且仅当 $D_s(x,y)=0$。实际行为像只包含由某个合法配置实现的实验结果族。

**定理 3.2（零核商的规范距离）。** $\sim_s$ 是等价关系，并有自然双射 $X_s/{\sim_s}\cong Q_s$。公式
$$
\overline D_s(\beta_sx,\beta_sy)=D_s(x,y)
\tag{3.1}
$$
在 $Q_s$ 上定义良好的扩展度量。每条允许箭头唯一下降为 $\overline h:Q_s\to Q_t$，满足
$$
\overline h\,\beta_s=\beta_t h,
\qquad
\overline D_t(\overline h b,\overline h b')\le L_h\overline D_s(b,b').
$$

**证明。** 扩展伪度量的零距离由三角不等式成为等价关系；定理2.2将它识别为全部实验读数的共同核，从而得到所述商与实际像双射。若 $D(x,x')=D(y,y')=0$，两次三角不等式给 $D(x,y)\le D(x',y')$ 和反向不等式，故式(3.1)与代表无关。零距离的两个实际行为必相同，所以它是扩展度量。由式(2.2)，零距离输入在 $h$ 后仍零距离，因而按代表定义 $\overline h(\beta_sx)=\beta_t(hx)$ 良好；实际像保证唯一性，增益界直接由式(2.2)得到。$\square$

若另有实际像表示 $q_s:X_s\twoheadrightarrow B_s$，且基础读数和全部允许箭头都通过 $q$ 下降，那么每个路径实验经归纳也通过 $q$ 因子化。因此 $q_s(x)=q_s(y)$ 蕴含 $\beta_s(x)=\beta_s(y)$，并有唯一满射 $B_s\to Q_s$ 与这些读数、操作相容。这是RRO第120节的精确最小表示判据；式(3.1)同时给它由实验增益确定的几何。集合上的因子化本身不提供恢复算法或稳定常数。

**定理 3.3（相同实验语言下的等距运输）。** 给两套定义1.1的实现 $X_s,\widetilde X_s$，使用同一个有类型生成箭头图、同一组基础读数标签、同一读数值域与度量，以及相同的增益。设映射 $r_s:\widetilde X_s\to X_s$ 满足
$$
r_t\widetilde h=h r_s,\qquad \widetilde f=f r_s
\tag{3.2}
$$
对全部生成箭头和基础读数成立，且两套实验都恰由这些生成数据形成。则
$$
\widetilde D_s(\widetilde x,\widetilde y)
=D_s(r_s\widetilde x,r_s\widetilde y).
\tag{3.3}
$$
这不要求 $r_s$ 单射或满射。若各 $r_s$ 满射，则两套实际行为商通过 $\widetilde\beta_s(\widetilde x)\mapsto\beta_s(r_s\widetilde x)$ 等距同构。

**证明。** 对同一个路径词归纳，式(3.2)给 $r_t\widetilde C=C r_s$。因此每个对应实验的结果相同，增益相同，式(2.1)的每项贡献相同；两边按同一实验索引取上确界，得到式(3.3)。满射时基础行为像也全部被覆盖，零核由式(3.3)相应识别，实际行为商上的映射遂为双射且保持距离。$\square$

式(3.2)需要覆盖实际语言。若 $\widetilde X=X\times Z$，$r$ 为第一投影，辅助读数全部取自 $X$，第二坐标可以被消去；一旦允许独立读取 $Z$，就新增了未被运输的实验。取 $X$ 为单点、$Z=\{0,1\}$，原距离为零，新读数的距离为一，式(3.3)不再成立。

**命题 3.4（路径模拟的单向度量控制）。** 设每个源实验 $(C,f)$ 都能由辅助系统中的一个允许实验 $(\widetilde C,\widetilde f)$ 模拟，在比较的全部辅助配置上满足
$$
\widetilde f(\widetilde C\widetilde x)=f(Cr_s\widetilde x),
\qquad
\widetilde\ell(\widetilde C)\le K_s\ell(C),
$$
其中对应读数使用同一个值域和度量，$0<K_s<\infty$ 与具体实验无关。则
$$
D_s(r_s\widetilde x,r_s\widetilde y)
\le K_s\widetilde D_s(\widetilde x,\widetilde y).
\tag{3.4}
$$

**证明。** 对每个源实验，将相同的读数差除以 $\ell(C)$，再乘除 $\widetilde\ell(\widetilde C)$，得到其贡献至多 $K_s\widetilde D_s$。对全部源实验取上确界即可。$\square$

单向模拟不提供反向界，允许辅助系统额外读取的区别也不会由式(3.4)消失。模拟路径的时间与费用同样应按实际执行计算；函数相同而增益不同，或者一次调用被展开为多次实验，都必须携带相应数据运输。

## 4. 多元拼接与合法替换链

**定义 4.1（全参数多元特化）。** 设每个多元组合是总函数
$$
g:X_{s_1}\times\cdots\times X_{s_m}\to X_t,
$$
并为其第 $i$ 孔指定 $L_{g,i}>0$。若对全部相应类型的旁支参数 $a_j$ 都允许箭头
$$
x\longmapsto g(a_1,\ldots,a_{i-1},x,a_{i+1},\ldots,a_m),
$$
且其增益为 $L_{g,i}$，则称实验语言包含该组合的全部参数平移。零元操作给常量，没有输入孔。

**定理 4.2（全参数的多元增益）。** 在定义4.1的条件下，对全部输入元组有
$$
D_t(g(x_1,\ldots,x_m),g(y_1,\ldots,y_m))
\le\sum_{i=1}^mL_{g,i}D_{s_i}(x_i,y_i).
\tag{4.1}
$$
若整个生成箭头族恰由这些参数平移组成，则第2节构造的距离是使基础读数为 $1$-Lipschitz、每个组合孔具有指定增益的逐点最小扩展伪度量族。若还保留其他生成箭头，最小性同时相对于那些箭头的增益要求成立。

**证明。** 从 $g(x_1,\ldots,x_m)$ 开始，依次把第 $i$ 个孔的值换成 $y_i$。其他孔值在每一步都属于允许固定的参数集合，因此定理2.2控制每一步变化，三角不等式给式(4.1)。当 $m=0$ 时两边都是零。指定各孔的增益与指定全部相应平移箭头的增益是同一要求，所以最小性正是定理2.2的第四项。$\square$

这个全参数模型可以比较任意载体元组，却没有自动证明有限观察者已经取得全部旁支参数。参数可以用于语义上的分离证明，而其实际制备、复制与接入仍是另外的关系。

**命题 4.3（受限常量不保证全代数同余）。** 如果上下文旁支只能由一部分可取得常量生成，完整上下文距离不一定满足其余未允许平移的增益界；即使所有指定增益均为一，零核也不一定是全代数的同余。

**证明。** 取 $X=\{0,1,2\}$，唯一可取得常量是 $0$。定义 $g(1,1)=2$，其余二元输入都输出零；读数为 $f(0)=f(1)=0,f(2)=1$，值域使用离散距离。由结构归纳，全部闭项仍等于零，任何非恒等严格单孔上下文因旁支为零而恒为零。因此受限上下文距离是 $D(x,y)=|f(x)-f(y)|$。但
$$
D(0,1)=0,\qquad
D(g(0,1),g(1,1))=D(0,2)=1.
$$
平移 $g(-,1)$ 不在当前语言内，却会把原来零距离的输入分开。$\square$

**命题 4.4（两点的数值边界）。** 单个类型只含两个点时，受限常量也能使某个未允许平移违反指定的严格小于一的增益。

**证明。** 令 $X=\{0,1\}$，唯一常量为零，$g(x,y)=xy$，读数为恒等映射，两孔均指定增益 $1/4$。任意非恒等受限单孔上下文恒为零，故 $D(0,1)=1$。未允许的平移 $g(-,1)$ 为恒等函数，其所需不等式变成 $1\le1/4$，失败。单点载体的全部点对距离为零，不能给这种反例。$\square$

若可取得集合 $K_s$ 对操作封闭，并且所需旁支值能够同时取得、按声明次数使用，则可将定理4.2限制在这些子载体上。仅仅每个值分别可取得，不保证它们能出现在同一份合法联合配置中。

**命题 4.5（合法混合链）。** 对部分组合 $g:R\to X_t$，其中 $R\subseteq\prod_iX_{s_i}$，设两个合法元组由有限链
$$
\boldsymbol z^0=\boldsymbol x,\quad
\boldsymbol z^1,\ldots,\boldsymbol z^k=\boldsymbol y
$$
连接。要求每个 $\boldsymbol z^j\in R$，第 $j$ 步仅改变第 $i_j$ 孔，且该步固定旁支的允许操作已经满足增益 $L_j$。则
$$
D_t(g\boldsymbol x,g\boldsymbol y)
\le\sum_{j=1}^kL_jD_{s_{i_j}}(z^{j-1}_{i_j},z^j_{i_j}).
\tag{4.2}
$$

**证明。** 对链上每个相邻合法元组使用该步的实际增益界，再沿输出链使用三角不等式。$\square$

若每个孔恰好替换一次，就返回式(4.1)的端点加权和；若必须绕行，则应使用实际链的代价。对所有合法链的上界取下确界仍是有效上界，空链族按无穷计，但这不证明链存在或代价有限。

**命题 4.6（合法端点不足以产生混合链）。** 仅要求两个端点合法，且所有两端都合法的逐孔变化满足增益，不能推出式(4.1)。

**证明。** 取 $X=\{0,1\}$、$R=\{(0,0),(1,1)\}$，定义 $g(i,i)=i$，输出使用离散距离。固定一孔后，合法另一孔值至多一个，所以所有合法逐孔比较都是同一点比较。输入零伪度量满足这些逐孔条件，但两个合法元组输出距离为一，端点加权和为零。中间元组 $(0,1),(1,0)$ 都非法。若将失败读数纳入完整总化模型，输入零伪度量便不再满足那份更强的完整实验条件。$\square$

## 5. 复制、共享变量与共同概率来源

**约定 5.1（一个外部接口与内部扇出）。** 允许上下文只有一份外部输入接口，不意味着内部表达式只能使用该输入一次。若协议允许复制，需把复制作为箭头 $\operatorname{copy}:X\to X\times X$，或直接允许带合法扇出布线的单输入上下文图。联合接口及其后续操作必须与这份复制相容。资源规则不允许的复制，不由集合上存在对角函数自动取得。

在命题4.3的三点模型中，若复制合法，则 $x\mapsto g(x,x)$ 是可执行实验，它区分零与一。此时必须扩展测试族，不能继续使用排除了复制的距离宣称已经覆盖所有实际实验。

**命题 5.2（重复变量的增益按路径相加）。** 在定理4.2的全参数条件下，对二元组合及重复输入有
$$
D_t(g(x,x),g(y,y))
\le(L_{g,1}+L_{g,2})D_s(x,y).
\tag{5.1}
$$
对更一般的有限确定性组合图，在每个节点满足所用多元增益界、共享节点的值被保留复用的前提下，展开为树并对每次使用路径累计增益，给出的确定性误差上界仍然有效；同源误差不需要相互独立。

**证明。** 式(5.1)直接使用式(4.1)，或插入中间值 $g(y,x)$ 后两次应用单孔界。一般有限图可按拓扑顺序求值；展开树的每个共享叶仍读取原图同一个值，因此两种表达的输出逐点相同。每次出现该值时使用同一个误差上界，再沿各路径传播，只增加上界的重复项，没有使用误差独立性。$\square$

以通常距离和加减法为例，$x+x$ 的增益为二；$x-x$ 则恒为零。通用逐孔上界给后者至多 $2\varepsilon$，有效但不紧。改进这种上界需要使用真实的相消关系，不能仅因两次出现同一个名称就删去一条路径的误差。

**命题 5.3（相同边缘不保证拼接误差为零）。** 存在两份输入联合律，各对应边缘完全相同，而同一二元读数的输出律距离为一。

**证明。** 令 $U$ 为公平比特，取
$$
P=\operatorname{Law}(U,U),\qquad
Q=\operatorname{Law}(U,1-U).
$$
两个输入坐标的边缘在 $P,Q$ 下均为公平比特。但 XOR 输出分别恒为零和恒为一，其全变差距离为一。因此不能把两份边缘距离零代入联合操作的误差和式，得出输出误差为零。$\square$

若操作的输入是概率律，联合律必须成为实际输入，或通过共同耦合明确给出。两个边缘上分别达到的最优耦合，不必能够同时实现原来两份联合律。

**命题 5.4（共同耦合上的期望与成功概率）。** 设在同一概率空间上有随机元组 $\boldsymbol X,\boldsymbol Y$，所有距离与输出均可测，并且几乎处处满足
$$
D_t(g\boldsymbol X,g\boldsymbol Y)
\le\sum_iL_iD_{s_i}(X_i,Y_i).
$$
则非负扩展期望满足
$$
\mathbb E D_t(g\boldsymbol X,g\boldsymbol Y)
\le\sum_iL_i\mathbb E D_{s_i}(X_i,Y_i).
\tag{5.2}
$$
若有限个局部证书在事件 $E_i$ 上成立，且 $\Pr(E_i^c)\le\alpha_i$，那么全部证书共同成立的概率至少为 $1-\sum_i\alpha_i$。

**证明。** 第一式由期望单调性和有限非负求和的线性性得到，不需要独立性。第二式由 $\Pr(\bigcup_iE_i^c)\le\sum_i\Pr(E_i^c)$ 得到。$\square$

**命题 5.5（重新抽取不保持共享图的语义）。** 将共享随机节点的两次使用改成两次独立调用，可能改变完整输出分布，即使每个节点的边缘分布不变。

**证明。** 抽取一次公平比特 $U$ 并计算 $U\operatorname{XOR}U$，输出恒为零。改成独立抽取公平比特 $U,V$ 后，$U\operatorname{XOR}V$ 为公平比特。两次调用的单独边缘相同，输出律不同。$\square$

保持语义的展开应复用同一个已取得值，或将完整随机源及消费位置纳入状态并证明展开保持该来源。把一个已缓存样本重复读取，并不会产生第二份独立实验信息。RRO第124、135节关于共同来源与复制碰撞的结论在这里成为误差传播的前提。

## 6. 局部缺陷怎样传到整体

**定义 6.1（近似实现的局部缺陷）。** 在定理4.2的全参数模型中，给同签名实现 $\widetilde X_s,\widetilde g$ 及映射 $r_s:\widetilde X_s\to X_s$，不要求满射或单射。对每个组合，指定有限非负数 $\delta_g$，并要求在实际将使用的全部输入上
$$
D_t\bigl(r_t\widetilde g(\widetilde x_1,\ldots,\widetilde x_m),
g(r_{s_1}\widetilde x_1,\ldots,r_{s_m}\widetilde x_m)\bigr)
\le\delta_g.
\tag{6.1}
$$
这些输入可以限制在一个已经证明在执行中封闭的可达域。对部分操作，式(6.1)中插入的中间元组也必须合法，或按已声明失败规则总化。只在两个实际端点各自合法时检验当前读数，不足以提供式(6.1)。

**定理 6.2（有限树的缺陷传播）。** 给同一有限类型正确的组合树 $\mathcal T$，在两套实现中分别求值。每个对应叶满足
$$
D_s(r_s\widetilde x,x)\le\varepsilon_{\rm leaf}<\infty.
$$
定义有限实数预算
$$
E_{\rm leaf}=\varepsilon_{\rm leaf},\qquad
E_{g(\mathcal T_1,\ldots,\mathcal T_m)}
=\delta_g+\sum_{i=1}^mL_{g,i}E_{\mathcal T_i}.
\tag{6.2}
$$
则根的实际距离不超过 $E_{\mathcal T}$。每个叶误差乘其到根路径的增益积，每个节点缺陷乘其严格上方路径的增益积，再全部相加，得到同一个预算。零元组合的预算是其 $\delta_g$。

**证明。** 对有限树归纳。叶处由假设成立。设内部节点的理想子值为 $x_i$、实现子值为 $\widetilde x_i$，插入 $g(r\widetilde x_1,\ldots,r\widetilde x_m)$，依次使用三角不等式、局部缺陷和式(4.1)，得到
$$
\begin{aligned}
&D_t(r\widetilde g(\widetilde{\boldsymbol x}),g(\boldsymbol x))\\
&\le\delta_g+
D_t(g(r\widetilde x_1,\ldots,r\widetilde x_m),g(x_1,\ldots,x_m))\\
&\le\delta_g+\sum_iL_{g,i}D_{s_i}(r\widetilde x_i,x_i)\\
&\le\delta_g+\sum_iL_{g,i}E_{\mathcal T_i}.
\end{aligned}
$$
零元节点直接使用式(6.1)。反复分配式(6.2)得到路径展开。$\square$

若只知道合法混合链，则在每个节点用式(4.2)替代式(4.1)，使用实际链上各步误差；只有链上这些误差由子预算控制时才能继续递推。定理6.2的简洁端点和式不免除这项义务。

**推论 6.3（终端读取误差）。** 假设对应终端读数取值于同一度量空间，且
$$
\rho_f(\widetilde f(\widetilde z),f(r_t\widetilde z))\le\eta_f
$$
在实际终端状态上成立。则整棵树的最终读数误差至多 $\eta_f+E_{\mathcal T}$。

**证明。** 在两个终端读数之间插入 $f(r_t\widetilde z)$。第一段由 $\eta_f$ 控制，第二段由基础读数的 $1$-Lipschitz 性和定理6.2控制。$\square$

当前读数误差不能代替完整距离缺陷。取两比特配置，当前读第一位，后续允许交换两位。状态 $(0,0),(0,1)$ 当前差为零，交换后的读数差为一。因此某局部替换即使当前输出完全正确，也可能把下一步要读取的关系改变；式(6.1)使用的正是后续允许上下文能揭示的缺陷。

**推论 6.4（时间接续的增益乘积）。** 一元动作链每步增益为 $L_k>0$、有限缺陷预算为 $\delta_k\ge0$，初始预算为 $E_0<\infty$。设实际误差由非负实数预算满足 $E_{k+1}\le L_kE_k+\delta_k$。则
$$
E_n\le
\left(\prod_{k=0}^{n-1}L_k\right)E_0+
\sum_{j=0}^{n-1}\left(\prod_{k=j+1}^{n-1}L_k\right)\delta_j.
\tag{6.3}
$$
若 $L_k\le L$、$\delta_k\le\delta$，则
$$
E_n\le
\begin{cases}
L^nE_0+\delta(1-L^n)/(1-L),&0<L<1,\\
E_0+n\delta,&L=1,\\
L^nE_0+\delta(L^n-1)/(L-1),&L>1.
\end{cases}
\tag{6.4}
$$

**证明。** 定理6.2在一元链上提供所需递推预算。对递推逐次代入得到式(6.3)；它也是离散 Gronwall 乘积公式的直接代入。统一上界后计算有限几何和得到式(6.4)，空乘积与空和保证 $n=0$ 时返回初值。$\square$

式(6.3)的算术部分已由钉版 Mathlib 的 discrete_gronwall_prod_general 覆盖；一元近似半共轭、收缩预算和输出轨迹也已有项目结果。这里需要额外证明的是局部证书的实际定义域、所控制的完整上下文距离，以及多元拼接是否具有合法替换链。

**命题 6.5（两次近似辅助运输）。** 设 $X''\xrightarrow{r_2}X'\xrightarrow{r_1}X$，三套系统具有对应一元操作 $h'',h',h$。设 $0\le K,\delta_1,\delta_2<\infty$，$r_1$ 相对于所选距离是 $K$-Lipschitz，且在实际状态上
$$
D(r_1h'x',h r_1x')\le\delta_1,\qquad
D'(r_2h''x'',h'r_2x'')\le\delta_2.
$$
则复合运输的缺陷不超过 $\delta_1+K\delta_2$。

**证明。** 在 $r_1r_2h''x''$ 与 $h r_1r_2x''$ 之间插入 $r_1h'r_2x''$。第一段由 $K\delta_2$ 控制，第二段由 $\delta_1$ 控制，三角不等式给结论。$\square$

**命题 6.6（正容差不是等价关系）。** 对一般度量，关系 $D(x,y)\le\varepsilon$ 在 $\varepsilon>0$ 时不必传递；两次容差替换一般只能给半径相加的保证。

**证明。** 通常实数距离下，$0,\varepsilon,2\varepsilon$ 的相邻距离均为 $\varepsilon$，端点距离为 $2\varepsilon$。一般地，$D(x,y)\le\varepsilon,D(y,z)\le\eta$ 由三角不等式只推出 $D(x,z)\le\varepsilon+\eta$。$\square$

因此零核的精确商不能无条件改成正容差商。近似表示应保留误差大小及其传播关系，而不是把一串各自“足够近”的状态直接认作同一个等价类。

## 7. 有限深度、有限费用与未读取的上下文

**定理 7.1（深度消耗与统一尾界）。** 定义2.3的有限深度距离满足
$$
D_s^{[N]}\uparrow D_s,\qquad
D_t^{[N]}(hx,hy)\le L_hD_s^{[N+1]}(x,y).
\tag{7.1}
$$
在全参数多元模型中，同样有
$$
D_t^{[N]}(g\boldsymbol x,g\boldsymbol y)
\le\sum_iL_{g,i}D_{s_i}^{[N+1]}(x_i,y_i).
\tag{7.2}
$$
若全部读数空间直径统一不超过 $M<\infty$，且所有生成箭头 $L_h\ge\lambda>1$，则
$$
D_s^{[N]}(x,y)\le D_s(x,y)
\le\max\{D_s^{[N]}(x,y),M\lambda^{-(N+1)}\}.
\tag{7.3}
$$

**证明。** 递增极限已由式(2.4)证明。把长度至多 $N$ 的输出路径前接一个箭头，输入路径长度至多 $N+1$，得到式(7.1)；逐孔替换同样给式(7.2)。每条被截去的路径长度至少 $N+1$，增益至少 $\lambda^{N+1}$，读数差至多 $M$。将上确界分成保留与截去两族，得到式(7.3)。$\square$

**命题 7.2（多一层不能无条件省去）。** 存在一步更新，使式(7.1)在 $N=0$ 时把右侧深度也改为零就失败。

**证明。** 取 $X=\{0,1\}^2$、读数 $f(a,b)=a$，更新 $h(a,b)=(b,0)$，增益一。状态 $x=(0,0),y=(0,1)$ 的当前距离为零，但更新后的当前距离为一。$\square$

**命题 7.3（二进制移位的尾界）。** 令 $X=\{0,1\}^{\mathbb N}$，更新 $T$ 为左移，唯一读数为首位，使用离散距离。指定增益 $L\ge1$，则
$$
D_L(x,y)=\sup_{n\ge0}L^{-n}|x_n-y_n|.
$$
若 $x\ne y$ 且首次差异在位置 $m$，则 $D_L(x,y)=L^{-m}$。特别地 $L=1$ 时完整距离是离散距离；$L>1$ 时式(7.3)的尾界可达到。

**证明。** 路径正是 $T^n$。首次差异之前各项为零，首次差异项为 $L^{-m}$，其后各项不超过它。对给定 $N$，取两序列只在位置 $N+1$ 不同，则 $D_L^{[N]}=0$ 而 $D_L=L^{-(N+1)}$。$\square$

不折扣时，任意有限深度的统一误差仍可为一；折扣后远期差异变轻，但更新允许把距离放大 $L$ 倍。这改变了任务对远期差异的计量，未保持同一份不折扣的统一精度要求。该一元公式及首次差异结论已有项目来源，见第8节。

**定义 7.4（包含读取费用的预算距离）。** 给每条生成箭头有限非负费用 $c_h$，路径费用相加，空路径费用为零；给每个基础读数有限非负费用 $c_f$。完整实验费用为
$$
b(C,f)=c(C)+c_f.
$$
在固定共同实验语言中，定义
$$
D_s^{\langle B\rangle}(x,y)=
\sup_{\substack{C:s\to t,\ f\\b(C,f)\le B}}
\frac{\rho_f(fCx,fCy)}{\ell(C)},\qquad B\ge0.
\tag{7.4}
$$
每条路径与读数费用均有限，因此 $D_s=\sup_{B\ge0}D_s^{\langle B\rangle}$。这里使用对该共同配置类型成立的费用合同；状态依赖的准入与资源消费可纳入配置，或使用统一的费用上界，不按每一对状态临时删除测试。

**定理 7.5（接续需要增加输入预算）。** 对费用 $c_h$ 的箭头 $h:s\to t$，有
$$
D_t^{\langle B\rangle}(hx,hy)
\le L_hD_s^{\langle B+c_h\rangle}(x,y).
\tag{7.5}
$$
若 $B\ge c_h$，等价地有 $D_t^{\langle B-c_h\rangle}(hx,hy)\le L_hD_s^{\langle B\rangle}(x,y)$。两边保留相同预算的式子一般不成立。

**证明。** 每个输出实验 $(C,f)$ 的费用至多 $B$；前接 $h$ 后费用为 $c_h+b(C,f)\le B+c_h$，增益乘 $L_h$。因此输入预算族包含全部以 $h$ 开头的拉回实验，取上确界得到式(7.5)。它一般还包含其他实验，故这里只有所述方向的不等式。反例用命题7.2，令更新费用一、读数费用零，预算零即可。$\square$

若实际费用仅有统一上界 $\widehat c_h$，并且相应接续在共同类型上成立，则同一证明给保守预算 $B+\widehat c_h$。单独知道两个端点各自付得起，不足以替代共同可执行语言。

**命题 7.6（按点对删去超预算实验也会破坏三角）。** 对状态依赖费用，若仅比较在两个端点都付得起的实验，则预算距离不一定是伪度量。

**证明。** 取三点 $a,b,c$，当前读数恒定。一个实验在 $a,c$ 处费用一并分别输出零、一，在 $b$ 处费用二。预算为一时，成对删去付不起的实验给 $D(a,b)=D(b,c)=0,D(a,c)=1$，与命题1.3相同。将“超预算”作为读数标签总化，或固定共同资源类型与统一协议族，才恢复固定测试族的前提。$\square$

**定理 7.7（一般预算尾证书）。** 对每个类型定义
$$
\varepsilon_s(B)=
\sup_{\substack{C:s\to t,\ f\\b(C,f)>B}}
\frac{\operatorname{diam}(Y_f)}{\ell(C)},
\tag{7.6}
$$
其中空族取零，直径允许为无穷。则
$$
D_s^{\langle B\rangle}(x,y)\le D_s(x,y)
\le\max\{D_s^{\langle B\rangle}(x,y),\varepsilon_s(B)\}.
\tag{7.7}
$$
若 $\varepsilon_s(B)\to0$ 且 $D_s$ 在所有点对上有限，则预算距离以相应加性尾界一致逼近完整距离。一个可检验的充分条件是：读数直径统一不超过有限数 $M\ge0$、读取费用统一不超过有限数 $c_*\ge0$，并存在 $\alpha>0$ 使每条允许路径满足
$$
\ell(C)\ge e^{\alpha c(C)}.
\tag{7.8}
$$
此时 $B\ge c_*$ 时有
$$
\varepsilon_s(B)\le M e^{-\alpha(B-c_*)}.
\tag{7.9}
$$

**证明。** 把全部实验分成费用不超过 $B$ 与超过 $B$ 两族。前者给式(7.4)，后者的每一项由式(7.6)控制，得到式(7.7)。若距离有限，$\max\{a,e\}\le a+e$ 给加性尾界。对超预算实验，$c(C)>B-c_f\ge B-c_*$；式(7.8)与统一直径界给每项至多 $M e^{-\alpha(B-c_*)}$，再取上确界得式(7.9)。$\square$

逐生成箭头条件 $L_h\ge e^{\alpha c_h}$ 足以推出式(7.8)，因为路径增益相乘而费用相加；它只是充分条件，证明本身只需要预算外归一化读数差具有趋零上界。增益与费用是不同的数据，不因都标在一条箭头上就自动满足指数关系。允许零费用箭头也不破坏定理7.7，但可能使某一预算内仍有无限多个测试。

**命题 7.8（预算内有限枚举的充分条件）。** 固定初始类型。若每个可达类型只有有限条出箭头和有限个基础读数，且全部箭头费用具有统一下界 $c_h\ge c_0>0$，则任意有限预算 $B$ 内的实验族有限。

**证明。** 路径长度至多 $\lfloor B/c_0\rfloor$。有限分叉按深度归纳给有限条该长度范围内的路径；每个终点的基础读数族也有限，所以闭实验族有限。$\square$

**命题 7.9（深度、费用与有限测试是不同条件）。** 有限深度或有限预算不自动给有限测试族；逐箭头严格正费用也不自动给预算内长度上界。

**证明。** 取无限比特序列类型 $X$，比特类型 $Y$。对每个 $n$ 允许一条箭头 $h_n:X\to Y$ 读取第 $n$ 位，每条费用一、增益一，$Y$ 只有恒等读数且读取费用零。预算一、深度一内已经有无限测试。任意有限测试子族只读取有限坐标，在其他位置首次不同的两序列对这些测试相同，而完整预算内距离为一；所以它们不能给误差小于一的统一有限测试替代。

若只有零费用左移与零费用首位读数，预算零内包含全部有限次左移，仍有无限测试。即使每条箭头费用严格正，也可取类型链 $X_0\to X_1\to\cdots$，每个类型均为比特序列，箭头为左移，费用为 $2^{-n-1}$、增益为一；每个类型有零费用首位读数。从 $X_0$ 出发任意长路径总费用小于一，故预算一内长度无界。$\square$

有限枚举也不保证尾误差趋零：命题7.3中给左移单位费用、单位增益，有限预算只检查有限前缀，完整距离却在任意两个不同序列上为一。因此有限枚举的条件与定理7.7的统一尾证书分别承担不同义务。

## 8. 恢复接口与数学来源

第2节的最小距离由一份可执行语言和增益数据共同决定；第3节证明准确运输这份语言时，其行为商几何随之运输。状态坐标、未来响应和当前预测记忆若满足RRO第120节的精确交织条件，并同时保持本卷读数度量及增益，就属于定理3.3的不同表示。额外的欧氏内积、概率律和物理时间尺度仍须各自运输，不能由行为核相同自动取得。

稳定恢复则要求恢复映射相对于指定输入输出距离具有可控制的增益；恢复公式存在本身不提供该常数。把一个恢复模块接到后续操作前，首先证明它的误差在式(6.1)所用几何中有界，再用有限树或路径预算传播。对一族联合任务，误差证书还须属于同一个联合实现，不能把分别可达的最佳误差直接放进一份共同输出。加权线性恢复与原子代价闭包由伴随卷[恢复几何](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)进一步研究。

本卷的共同结构是有类型的允许路径、读数和可检验的误差关系。它给出相对于指定任务的最小性与保真条件；不要求所有物理模型具有相同的实验语言，也不由任意边界投影推出引力对偶或面积熵定律。

| 数学来源 | 本卷使用的范围 |
|---|---|
| [StrictOneHoleContexts](../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean)，contextual_equivalence_is_greatest | 严格部分上下文、失败标签、全部旁支参数及精确最大同余；第1、3、4节保留这些条件，并区别实际可取得语言。 |
| [PartialFunctionDomainObservation](../../../D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.lean)，common_success_domain_refutation | 双方成功时读数相同不足以保持动作定义域；命题1.3将成对删测试的失败明确为三角律反例。 |
| [EvaluationSupremumMinimality](../../../D5/S3/Observer/MetricGeometryLaws/EvaluationSupremumMinimality.lean)，evaluation_suprema_are_least_dominating；[DualSupremumPseudometricKernels](../../../D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels.lean) | 评价上确界的最小支配及零核组件；任意路径增益与允许箭头的闭合由第2节直接给出。 |
| [CanonicalDiscountedFutureGeometry](../../../D5/S3/Observer/MetricGeometryLaws/CanonicalDiscountedFutureGeometry.lean)，canonical_discounted_future_geometry；[FirstDifferencePowerLaw](../../../D5/S3/Observer/MetricGeometryLaws/FirstDifferencePowerLaw.lean)，first_difference_power_law | 有界读数下一元折扣距离、更新增益与首次差异公式；命题7.3是二进制移位实例。 |
| [FinitePredictionTruncation](../../../D5/S3/Observer/MetricGeometry/FinitePredictionTruncation.lean)，finite_prediction_truncation_formula_and_error | 一元有限预测和几何尾界；第7节另保留路径深度消耗、实际费用与有限枚举的条件。 |
| [IteratedDefectAccumulation](../../../D5/S3/Observer/Naturality/IteratedDefectAccumulation.lean)，iterated_naturality_defect_bound；[ApproximateSemiconjugacyError](../../../D5/S3/Observer/Naturality/ApproximateSemiconjugacyError.lean)，approximate_semiconjugacy_error | 近似交织的一元轨道缺陷与收缩预算；本卷使用同一递推，另证明多元局部证书到树形预算的条件。 |
| [Mathlib DiscreteGronwall](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/ODE/DiscreteGronwall.lean)，discrete_gronwall_prod_general | 在递推前提成立后，式(6.3)为非负实数增益下的直接参数代入。 |
| [SemiconjugacyComposition](../../../D5/S3/Observer/MetricGeometry/SemiconjugacyComposition.lean)，semiconjugacy_defect_composition；[MetricEntourageComposition](../../../D5/S3/Observer/MetricGeometryLaws/MetricEntourageComposition.lean)，metric_entourage_comp_subset | 两次近似运输的缺陷和式、正容差复合半径相加。 |
| [定量对角化与观察者完成化](QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md) 第24节 | 一元折扣几何、递归表达、截断与近似半共轭的既有正文；本卷不把这些一元结果作为新的缺口。 |
| Matteo Mio、Ralph Sarkis、Valeria Vignudelli，[*Beyond Nonexpansive Operations in Quantitative Algebraic Reasoning*](https://arxiv.org/abs/2201.09087v1)，2022，DOI 10.1145/3531130.3533366 | 为运算指定输入距离提升、再要求非扩张的成熟框架。本卷采用扩展值、异质读数与逐箭头增益；不将论文中有界距离的整个元定理未经对应地直接套用。 |

这些来源分别承担上确界、Lipschitz 组合、精确上下文核与离散误差累积。正文给出的普通数学证明说明它们如何在实际允许语言中接续；数学来源、形式化状态和可执行实验能力是不同的陈述。

## 追加锚（本行以下为增补区）
## 9. 经典概率拼接、记忆增益与可组合恢复

### 9.1 同一联合律、零切片与扩展KL

**定义 9.1（有限实验、扩展KL与条件信息）。** 本节概率恢复部分的随机变量取值于有限非空集合，使用自然对数。对两份概率质量函数$p,q$，定义
$$
D(p\Vert q)=
\begin{cases}
\displaystyle\sum_{x:p(x)>0}p(x)\log\frac{p(x)}{q(x)},
&p(x)>0\Longrightarrow q(x)>0,\\
+\infty,&\text{否则}.
\end{cases}
\tag{9.1}
$$
零质量项按零处理，正质量事件被赋零预测时使用无穷分支。

固定一份$P_{ABC}$。其边缘始终由这份共同律求和得到。仅在$P_B(b)>0$时定义$P_{C|b}(c)=P_{BC}(b,c)/P_B(b)$。如需全定义核，可在零$B$切片任选一行概率；乘回$P_B(b)=0$后所有有关联合律都与选择无关。定义
$$
I_P(A:C\mid B)
=\sum_{b:P_B(b)>0}P_B(b)
D(P_{AC|b}\Vert P_{A|b}P_{C|b}).
\tag{9.2}
$$
在所有条件量中，零概率条件切片均省略。

**引理 9.2（有限支持与非负性）。** 有限载体上，$D(p\Vert q)$有限当且仅当$p$的正支持包含于$q$的正支持；总有$D(p\Vert q)\ge0$，且等号当且仅当$p=q$。式（9.2）总为有限非负数。

**证明。** 支持条件直接来自定义9.1。设该条件成立，以$S=\{x:p(x)>0\}$记正支持。由$-\log u\ge1-u$及其等号条件，
$$
D(p\Vert q)\ge\sum_{x\in S}(p(x)-q(x))=1-q(S)\ge0.
$$
若KL为零，则这两个不等式都取等号，迫使$S$上$q(x)/p(x)=1$，且$q(S)=1$，因此$p=q$；反向立即成立。无穷分支不可能取等号。对式（9.2）的任一正条件行，正联合项的两个边缘均正，故相对乘积边缘的KL有限；有限非负加权和仍有限非负。相应有限条件信息接口为[`ConditionalMutualInformation`](../../../D5/S3/Entropy/Submodularity/ConditionalMutualInformation.lean)中的`conditional_mutual_information_nonneg`与`conditional_mutual_information_eq_entropy_defect`；其首坐标是条件坐标，对本式使用$(B,(A,C))$的次序。证毕。

### 9.2 条件独立拼接及其准确含义

**命题 9.3（共同边缘下的经典拼接）。** 从定义9.1中$P$的两份重叠边缘构造
$$
P^{\mathrm{glue}}(a,b,c)=
\begin{cases}
P_{AB}(a,b)P_{BC}(b,c)/P_B(b),&P_B(b)>0,\\
0,&P_B(b)=0.
\end{cases}
\tag{9.3}
$$
$P^{\mathrm{glue}}$是概率，保留$AB$与$BC$两个边缘，并有
$$
D(P\Vert P^{\mathrm{glue}})
=I_P(A:C\mid B)
=H(P^{\mathrm{glue}})-H(P).
\tag{9.4}
$$
它是在给定两份边缘的相容联合律中唯一的最大熵者；缺陷为零当且仅当$A\perp C\mid B$。

**证明。** 这是主卷定理124.14在同一$P$的边缘上的直接应用。其支持条件是：若$P(a,b,c)>0$，则$P_{AB}(a,b),P_{BC}(b,c),P_B(b)$均正，所以$P^{\mathrm{glue}}(a,b,c)>0$。所有熵与该KL因而有限。CMI零集亦由[`MarkovDataProcessing`](../../../D5/S3/Entropy/Submodularity/MarkovDataProcessing.lean)的`conditional_mutual_information_eq_zero_iff_conditional_product`给出，只约束正质量条件切片。

该结论不声明拼接恢复了原来的共同来源。主卷命题124.15取$B$恒定、$A=C$为公平位，原律给$\Pr(A=C)=1$，拼接律给$1/2$。式（9.4）的熵差只比较同一边缘约束下的两份联合律；其假设没有指定物理耗散过程，故不给产热结论。证毕。

### 9.3 任意恢复核的误差分解

**定义 9.4（只访问边界的经典恢复核）。** 一个候选恢复器是逐行归一化的核$r(c\mid b)\ge0$。它保留已有的$(A,B)$，仅根据$B$生成候选$C$，所得联合律为
$$
Q_r(a,b,c)=P_{AB}(a,b)r(c\mid b).
\tag{9.5}
$$
这是恢复器的无旁路条件：同一个$b$使用同一行$r$，不能暗中访问$a$或未知来源标签。给出一个数学核不等于已取得其参数或已获准物理执行。

**定理 9.5（结构缺陷加恢复核失配）。** 对任意定义9.4的$r$，扩展非负实数中有
$$
\begin{aligned}
D(P_{ABC}\Vert Q_r)
&=I_P(A:C\mid B)
  +D(P_{BC}\Vert P_Br)\\
&=I_P(A:C\mid B)
  +\sum_{b:P_B(b)>0}P_B(b)D(P_{C|b}\Vert r(\cdot\mid b)).
\end{aligned}
\tag{9.6}
$$
这里$(P_Br)(b,c)=P_B(b)r(c\mid b)$。所以
$$
\min_r D(P_{ABC}\Vert P_{AB}r)=I_P(A:C\mid B),
\tag{9.7}
$$
且最小值恰由正$P_B$切片上$r(\cdot\mid b)=P_{C|b}$的核取得；零切片上的行不受约束。

**证明。** 先核对无穷分支。若存在$P_{BC}(b,c)>0$而$r(c\mid b)=0$，则$P_B(b)>0$，并有某个$a$使$P(a,b,c)>0$。该点$Q_r=0$，故式（9.6）左边无穷，右边的第二项及对应条件KL也无穷。第一项有限，因此整条式子是$+\infty=\text{有限数}+(+\infty)$，没有无穷减无穷。

否则$r(c\mid b)>0$在$P_{BC}$的正支持上成立。于是所有需取对数的比值均正。在$P(a,b,c)>0$处有
$$
\frac{P(a,b,c)}{P_{AB}(a,b)r(c\mid b)}
=\frac{P(a,b,c)P_B(b)}{P_{AB}(a,b)P_{BC}(b,c)}
 \frac{P_{BC}(b,c)}{P_B(b)r(c\mid b)}.
$$
取对数、乘$P(a,b,c)$并求有限和。第一项由式（9.4）为$I_P(A:C\mid B)$；第二项先对$a$求和，得到$D(P_{BC}\Vert P_Br)$。再把$P_{BC}=P_BP_{C|b}$代入正$B$切片，约去同一个$P_B$，得到式（9.6）的第二行。$P_B=0$时非负边缘和为零迫使整片$P_{BC}$和$P$均为零，因此不出现任何遗漏项。

所有条件KL非负，选$r=P_{C|B}$并任意补全零行，得到最小值。由于$I_P(A:C\mid B)$有限，等于最小值当且仅当第二项为零；有限和中每个正$P_B$权重的KL均必须为零，即该行$r=P_{C|b}$。

一般组合积的成熟KL链式公式见钉版Mathlib [`KullbackLeibler/ChainRule.lean`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean)中的`InformationTheory.klDiv_compProd_eq_add`：其前提为有限测度及Markov核，证明包括非绝对连续和不可积导致的无穷分支。项目[`Divergence/ChainRule`](../../../D5/S3/Divergence/ChainRule.lean)的`kl_divergence_chain_rule`则要求有限质量函数处处严格正；上面的支持分类明确处理了超出该严格正接口的情形。证毕。

**推论 9.6（对数评分的两层代价）。** 给定完整$(A,B)$的最佳期望对数损失为$H(C\mid A,B)$；只用$B$并实际选取定义9.4的$r$时，其期望损失为
$$
H(C\mid A,B)+I_P(A:C\mid B)
+\sum_{b:P_B(b)>0}P_B(b)D(P_{C|b}\Vert r(\cdot\mid b)).
\tag{9.8}
$$
**证明。** 在每个正条件行展开$-\log r=-\log P_{C|b}+\log(P_{C|b}/r)$，再用有限条件熵链式法则；零预测的分支两边同为无穷。最优评分结论是[ML伴卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定理18.2的直接应用。式（9.8）的最小值是在指定核集合上取得的数学值，其前提不包含真实条件律的估计或执行成本。证毕。

### 9.4 保留式记忆追加的精确缺陷收支

**定义 9.7（固定未来目标的记忆缺陷）。** 固定同一份联合律$P_{HF}$，其中$H$是完整历史或所声明的完整来源，$F$是同一个未来任务变量。给确定函数
$$
M=m(H),\qquad Z=g(H),\qquad M^+=(M,Z).
$$
它们都取有限值。若用$M$预测$F$，其条件独立模拟律为
$$
Q_M(h,f)=P_H(h)P_{F|M}(f\mid m(h)),
$$
零$M$切片任选补全；以$M^+$代替$M$同样定义$Q_{M^+}$。记
$$
\Delta_M=D(P_{HF}\Vert Q_M)=I_P(H:F\mid M),
\qquad
\Delta_{M^+}=D(P_{HF}\Vert Q_{M^+})=I_P(H:F\mid M,Z).
\tag{9.9}
$$
等式由式（9.4）在$(H,M,F)$及$(H,M^+,F)$图律上的直接应用得到；去掉由$h$决定的记忆坐标只是对非零项重编号。

**定理 9.8（追加记录恰减少其条件目标信息）。** 在定义9.7下，
$$
\Delta_M=\Delta_{M^+}+I_P(Z:F\mid M),
\qquad
\Delta_M-\Delta_{M^+}=I_P(Z:F\mid M)\ge0.
\tag{9.10}
$$
等号$\Delta_M=\Delta_{M^+}$恰在每个正$M$切片上$Z,F$条件独立时成立。因而增加记录数、增加档案熵和减少本目标的预测缺陷是不同的陈述。

**证明。** 由有限条件熵链式法则，
$$
I(H:F\mid M)=H(F\mid M)-H(F\mid H,M).
$$
由于$M=m(H)$，在每个正$H$切片上，加入$M$不会改变$F$的条件律，故$H(F\mid H,M)=H(F\mid H)$。同理，$(M,Z)$由$H$决定，故
$$
\Delta_M=H(F\mid M)-H(F\mid H),\qquad
\Delta_{M^+}=H(F\mid M,Z)-H(F\mid H).
$$
两式相减给$H(F\mid M)-H(F\mid M,Z)=I(Z:F\mid M)$。全部条件熵有限，因此这里的减法合法。式（9.2）给非负性及条件独立的等号判据。

同一计算还给$I(F;H)=I(F;M)+\Delta_M$与$I(F;M^+)-I(F;M)=I(F;Z\mid M)$，即主卷式（121.27）的残差表达。所用链式法则为[`MutualInformationChainRule`](../../../D5/S3/Entropy/Submodularity/MutualInformationChainRule.lean)中的`mutual_information_chain_rule`；主卷§81.2、§121.9及§127.7具有相同的固定目标、共同联合律条件。此证明没有独立噪声假设。证毕。

**命题 9.9（额外记录依赖其他来源时的修正项）。** 对任意共同有限联合律$(H,F,M,Z)$，不假定$Z$由$H$决定时，有
$$
I(H:F\mid M)-I(H:F\mid M,Z)
=I(Z:F\mid M)-I(Z:F\mid H,M).
\tag{9.11}
$$
**证明。** 将$I((H,Z):F\mid M)$分别按$H$先、$Z$先展开，并移项即得。取独立公平位$H,F$、常值$M$以及$Z=H\mathbin{\mathrm{XOR}}F$，则$I(H:F\mid M)=0$，给定$Z$后$H$决定$F$，所以$I(H:F\mid M,Z)=\log2$。此时$I(Z:F\mid M)=0$而$I(Z:F\mid H,M)=\log2$，验证缺陷可以增加。证毕。

### 9.5 固定策略与恢复器的量词

**定义 9.10（固定策略的共同实验合同）。** 对未来任务变量$F$及控制策略$\pi$，指定完整实验律$P^\pi_{HF}$。策略只能根据已取得的历史自适应选动作，所有随机分支、失败标记和共同来源均保留在该实验中。比较两种摘要时固定同一$\pi$、同一个$F$及同一份联合律；“同一策略”指同一个根据可访问记录选择动作的规则，不允许一侧根据另一侧没有的隐藏变量分支。

若协议使用随机种子，依主卷§121.10将种子及实际数据的共同来源纳入完整模型；是否写入可访问档案另行指定。扩展$H$后使用定义9.7时，完整来源及全部条件量按扩展后的同一联合律定义，不混用不同$H$对应的缺陷。

**推论 9.11（逐策略增益与共同策略族的最坏缺陷）。** 在定义9.10中，对每个固定合法策略$\pi$及同一确定摘要$M=m(H),Z=g(H)$，有
$$
\text{对每个固定合法 }\pi,\qquad
\Delta_M^\pi=\Delta_{M^+}^\pi+I_{P^\pi}(Z:F\mid M).
\tag{9.12}
$$
若同一个策略族$\Pi$在两种表示下都合法，而且每个$\pi$的共同实验律已给定，则
$$
\sup_{\pi\in\Pi}\Delta_{M^+}^\pi
\le\sup_{\pi\in\Pi}\Delta_M^\pi.
\tag{9.13}
$$

**证明。** 对每个$P^\pi$直接应用定理9.8，得到式（9.12）。去掉非负增益项并对同一索引族取上确界，得到式（9.13）。该论证不把两个最坏值之差等同于某个未指定策略的条件互信息；策略族随记忆能力变化时，须先满足本命题的共同索引及合法执行条件。证毕。

**命题 9.12（换策略不能套用同律缺陷差）。** 保留旧记录同时换用另一未来策略后，新旧缺陷不必单调。

**证明。** 令$H=(U,V)$，其中$U,V$为独立公平位，$M$恒定，$Z=U$。策略$\pi_0$使未来目标输出$F_0$恒为零，则$\Delta_M^{\pi_0}=0$。策略$\pi_1$使未来输出$F_1=V$，则
$$
\Delta_{M^+}^{\pi_1}=I((U,V):V\mid U)=\log2.
$$
记录已增加，而跨策略缺陷从零变为$\log2$。这不反驳式（9.12）：在固定$\pi_1$下，旧缺陷也是$\log2$，新增$U$带来的条件目标信息为零。证毕。

**命题 9.13（逐实验恢复与一份通用恢复器不同）。** 即使每个实验的CMI均为零，也不保证存在一份不接收实验标签的核$r(F\mid M)$同时恢复全部实验。

更一般地，对一族已指定实验$i$，存在同一个核$r(c\mid b)$达到各自式（9.7）的最小值，当且仅当所有满足$P_B^i(b)>0$的实验在该$b$上的$P^i_{C|b}$相同。若要求各实验误差都为零，还须各自的CMI为零。

**证明。** 对第一项，令$H,M$都为单点。实验$0$令$F=0$，实验$1$令$F=1$。两实验各自CMI均为零，并分别由核$\delta_0$、$\delta_1$准确恢复。若同一$r$同时恢复两者，则它的一行既等于$\delta_0$又等于$\delta_1$，矛盾。若标签$\pi$本来就是恢复器合法可访问的输入，则可以使用$r(F\mid M,\pi)$；这符合扩充输入类型后的合同。

一般判据的必要性由定理9.5的等号条件得到；充分性是在有质量的$b$上取公共行，在所有实验均零质量的$b$上任选概率行。定理9.5还说明，在达到最小值后误差为零恰要求各自CMI为零。证毕。

### 9.6 支持上的充分性、平均界与最坏情形

**命题 9.14（正支持上的预测充分性）。** 将$P_{HF}$写为$\mu(h)K(f\mid h)$，令$M=m(H)$，则
$$
\Delta_M=0
\iff
\forall h,h',\quad
\bigl[\mu(h)>0,\ \mu(h')>0,\ m(h)=m(h')\bigr]
\Longrightarrow K(\cdot\mid h)=K(\cdot\mid h').
\tag{9.14}
$$
若$\mu$在全部候选历史上全支持，该判据给全域纤维充分性；一般先验只约束其正支持。对每个Dirac先验分别有零缺陷，不能替代一份全支持先验。

**证明。** 式（9.14）直接应用[`ConditionalInformationSufficiency`](../../../D5/S3/ConceptDynamics/Completion/ConditionalInformationSufficiency.lean)中的`conditional_information_zero_iff_support_sufficiency`，将该声明的`prior`、`kernel`、`concept`依次取为$\mu,K,m$。全支持时，两个正概率前提对全部$h,h'$成立。反之，Dirac条件下$H$恒定，不论$m$怎样丢信息，其缺陷都为零；例如两个历史对应不同的确定未来，常值$m$在各Dirac先验下缺陷均零，却不满足全域纤维充分性。证毕。

**推论 9.15（平均TV界及最坏纤维的反例）。** 对定理9.5中的任意$r$，定义$\operatorname{TV}(p,q)=\tfrac12\sum_x|p(x)-q(x)|$，则
$$
\operatorname{TV}(P,Q_r)
\le\sqrt{\frac{I_P(A:C\mid B)+D(P_{BC}\Vert P_Br)}{2}}.
\tag{9.15}
$$
取$r=P_{C|B}$并按共同$AB$边缘求和，还得到
$$
\sum_{a,b:P_{AB}(a,b)>0}P_{AB}(a,b)
\operatorname{TV}(P_{C|a,b},P_{C|b})
\le\sqrt{I_P(A:C\mid B)/2}.
\tag{9.16}
$$
小CMI不保证同摘要纤维内各历史的未来条件律一致接近。

**证明。** 将[ML伴卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)命题18.3证明中的有限Pinsker不等式$\operatorname{TV}(p,q)\le\sqrt{D(p\Vert q)/2}$应用于$(P,Q_r)$，再代入定理9.5，得到式（9.15）。该Pinsker证明经二元合并与二项KL的二阶导数下界，包含端点和无穷分支；KL无穷时这里只给平凡上界。取$r=P_{C|B}$后，两联合律具有相同$AB$边缘，逐正切片提取权重，得到式（9.16）左侧恰为$\operatorname{TV}(P,P^{\mathrm{glue}})$，故第二式成立。

反例仍取该命题的稀有状态模型：$\Pr(H=1)=\varepsilon\in(0,1)$、$F=H$、$M$恒定时，$\Delta_M=h(\varepsilon)\to0$，而两个历史的真实未来条件律之间TV始终为一。每个先验都有全支持，但正概率下界随$\varepsilon$趋零，故不能推出统一最坏纤维误差。证毕。

### 9.7 进入后续实验所需的共同接口

**命题 9.16（相同随机后处理保存联合误差证书）。** 设两份有限配置律$P,Q$包含后续任务所需的全部共同来源。某一允许后续实验及其读数由同一个逐行归一化核$L(y\mid x)$作用于两份配置。则
$$
\operatorname{TV}(LP,LQ)\le\operatorname{TV}(P,Q).
\tag{9.17}
$$
因此，当本卷定义2.1的所有允许生成箭头均为这样的随机核、读数距离为TV且各增益取一时，由式（9.15）得到完整上下文距离的同一个上界。

**证明。** 逐输出使用三角不等式并交换有限和，
$$
\begin{aligned}
\tfrac12\sum_y\left|\sum_xL(y\mid x)(P(x)-Q(x))\right|
&\le\tfrac12\sum_{y,x}L(y\mid x)|P(x)-Q(x)|\\
&=\tfrac12\sum_x|P(x)-Q(x)|.
\end{aligned}
$$
归一化核的复合仍归一化，所以每个合法有限上下文均满足此界；再对固定实验族取上确界即得结论。

一个有限自适应协议也可写成这种核：给每个可访问历史一行明确的动作随机化和结果转移，沿有限树把联合概率相乘并对内部变量求和，逐层行和为一。必须在两边使用同一协议，并保留成功、失败及协议所需的来源；对成功分支后选择并重新归一化通常不是同一个归一化线性核，不由式（9.17）保证收缩。若人为要求生成箭头具有小于一的增益，也不能由TV收缩直接推出相应归一化完整距离的同一界。

本命题的输入是完整联合律。仅有边缘相同不够，反例由本卷命题5.3给出；只比较一条策略不提供定义2.1完整实验族中的统一条件。若摘要通过ML伴卷定理17.3的联合“输出—后继摘要”核因子化，则可对每个可访问历史归纳，得到同一自适应协议的完整记录律；该卷命题17.7给出分别保留输出和后继摘要边缘仍失败的两步反例。这些条件均保留共同来源，与式（9.17）的完整联合输入要求一致。证毕。

**定义 9.17（关系表示及执行资源合同）。** 一个参与本节恢复比较的关系接口，同时指定配置域、共同来源、允许操作、读数、状态与操作的表示，以及实际调用的非负资源向量。图用于登记合法连接、来源和依赖；矩阵表示已指定的线性映射；张量表示多接口及其已给出的收缩；几何代数使用明确的二次型、分次及乘法；概率核使用非负性和归一化；逻辑接口使用已指定的后承与证书转换。这些表示之间的连接沿用主卷各自的有类型合同：§132.1—132.2的张量割与自动机矩阵，§129的Clifford/外代数及条件协方差投影，§131的外幂/Hodge运输，以及§136.3的保真辅助线和证明运输。

其中主卷§129.7的向量乘法缺陷引用的是平均条件协方差；§129.8将概率质量重建与Clifford线性读出分别定义在概率质量空间和Clifford空间，二者只共享条件投影；§136.3的证明运输使用保持后承、需要时反射后承及证书转换的条件。本合同保留这些原有类型及条件，不把同一矩阵写法视为映射相同或因果次序可交换。

条件律的测量、拟合、存储、核调用、取得额外权重或相干资源，以及实际计时，均作为该合同的额外输入。费用依本卷第7节及恢复几何卷逐资源坐标计账；概率熵、恢复误差和时间费用保留各自单位，定义9.1—9.14不提供这些量之间的兑换率。

### 9.8 递归历史增长在指定距离下的维数

**定理 9.18（禁止长串的首差Hausdorff维数）。** 对整数$k\ge2$，采用主卷§132.2定义的根$\lambda_k$：
$$
\sum_{j=1}^k\lambda_k^{-j}=1,\qquad 1<\lambda_k<2,\qquad\lambda_k\uparrow2
\quad(k\ge2).
\tag{9.18}
$$
令
$$
X_k=\{x\in\{0,1\}^{\mathbb N_0}:x\text{不含连续}k\text{个}1\},
$$
并对$x\ne y$定义
$$
d(x,y)=2^{-\min\{j\ge0:x_j\ne y_j\}},\qquad d(x,x)=0.
$$
则
$$
\dim_{\mathrm H}(X_k,d)=D_k:=\frac{\log\lambda_k}{\log2},
\qquad D_k\uparrow1.
\tag{9.19}
$$
这里Hausdorff测度沿用主卷定义33.0的无额外系数约定，以任意可数覆盖的直径幂和定义；覆盖集不必可测。

**证明。** 主卷§132.2给出合法长度$n$词数$a_n^{(k)}$的$k$阶递推及界$a_n^{(k)}\le C_k\lambda_k^n$，其中$C_k<\infty$；同时给出式（9.18）的根与极限。$k=2$的维数结论亦是主卷定理33.2的精确实例。

共享前缀使$d$满足强三角不等式；它给出二进制乘积拓扑。禁止模式的补集是开柱的并，故$X_k$闭于紧致二进制乘积空间，所以紧致。每个合法有限词后补全零仍合法，故每个合法柱非空。长度$n$柱的直径至多$2^{-n}$，全部$a_n^{(k)}$个柱覆盖$X_k$。因此对任意$s>D_k$，
$$
\mathcal H^s_{d,2^{-n}}(X_k)
\le C_k\lambda_k^n2^{-ns}
=C_k2^{-n(s-D_k)}\longrightarrow0,
$$
给出维数上界。在临界指数$D_k$同样给$\mathcal H^{D_k}_d(X_k)\le C_k$。

下界需要相容概率，不能将每层均匀词分布自动当作同一个无限来源。令状态$i\in\{0,\ldots,k-1\}$记当前末尾连续$1$的数目，初态为$0$。给出正权
$$
r_i=\sum_{j=1}^{k-i}\lambda_k^{-j},\qquad
r_0=1,\quad0<r_i\le1.
$$
当$i<k-1$，有$\lambda_kr_i=r_0+r_{i+1}$；当$i=k-1$，有$\lambda_kr_{k-1}=r_0$。因此以下是逐行归一化的转移：输出$0$并转到$0$的概率为$r_0/(\lambda_kr_i)$；若$i<k-1$，输出$1$并转到$i+1$的概率为$r_{i+1}/(\lambda_kr_i)$。在$i=k-1$时只能输出$0$，其概率为一。其余转移概率为零。

这是对原允许图的Perron正权重加权，即通常的Parry转移构造；此处固定初态$0$，不额外称所构造的词概率平稳。主卷§132.2的计数矩阵按“列输入、行输出”书写，而此处$r$满足其转置的正特征向量方程，故不能误把原右特征向量直接当作这里的行归一化权重。

对合法长度$n$词$w$，其状态路径从$0$唯一确定，末态记$i_n$。沿路径概率相乘，各$r$望远镜相消，得到柱质量
$$
\mu([w])=\frac{r_{i_n}}{\lambda_k^nr_0}
\le\lambda_k^{-n}=2^{-nD_k}.
\tag{9.20}
$$
行和为一使父柱质量恰等于子柱质量之和，空柱质量为一。与主卷定理33.1相同，这在有限柱并的开闭代数上定义相容有限预测度：若不交开闭集之并仍开闭，紧性给有限子覆盖，所以实际只有有限个非空成员，确保该代数上的可数可加性。有限预测度的测度扩张定理因此给$X_k$上的Borel概率$\mu$。由式（9.20），每个点的质量被$2^{-nD_k}\to0$控制，所以$\mu$无原子。

对任意包含至少两点的$U\subseteq X_k$，在其不同点对的首差下标中取最小值$m$。所有点共享前$m$位，且存在两点在第$m$位不同，所以$\operatorname{diam}_dU=2^{-m}$，而$U$包含于一个长度$m$柱。于是外测度满足
$$
\mu^*(U)\le2^{-mD_k}=(\operatorname{diam}_dU)^{D_k}.
$$
空集及单点由无原子性满足同一界。对任意可数覆盖$X_k\subseteq\bigcup_jU_j$，外测度次可加性给
$$
1\le\sum_j\mu^*(U_j)
\le\sum_j(\operatorname{diam}_dU_j)^{D_k}.
$$
故$\mathcal H^{D_k}_d(X_k)\ge1>0$，给出维数下界。与上界合并得到式（9.19）；$D_k\uparrow1$直接由式（9.18）及对数连续严格递增性得到。

下界所用质量分布方法对应钉版Mathlib的[`Measure.le_hausdorffMeasure`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Measure/Hausdorff.lean)，其条件是集合质量不超过直径幂；[`dimH_of_hausdorffMeasure_ne_zero_ne_top`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/MetricSpace/HausdorffDimension.lean)给正有限临界测度的维数结论。证毕。

**推论 9.19（距离尺度与词语言的范围）。** 在定理9.18的同一$X_k$上，把距离改成$d_\theta(x,y)=\theta^{\min\{j:x_j\ne y_j\}}$、$0<\theta<1$，并令相等点距离为零，则Hausdorff维数为$\log\lambda_k/(-\log\theta)$。式（9.19）不指定其他物理空间或Hilbert空间的维数，也不适用于任意一条固定合法词的因子语言。

**证明。** 长度$n$柱直径改为至多$\theta^n$，式（9.20）的质量界仍为$\lambda_k^{-n}$。令$s_\theta=\log\lambda_k/(-\log\theta)$，则$\lambda_k^{-n}=(\theta^n)^{s_\theta}$；定理9.18的柱覆盖、任意集合质量界及正有限临界测度证明逐项成立，给出所述维数。它依赖所指定的载体与距离，故不给未指定空间的维数结论。

固定词语言的区别可由[`SubshiftHausdorffDimension`](../../../D5/S1/Words/Complexity/SubshiftHausdorffDimension.lean)中的`dimH_goldenSubshift_eq_zero`见证：该结论研究一条固定黄金词的因子语言，其复杂度线性、Hausdorff维数为零；它的载体不是所有禁止$11$的序列，所以与$D_2>0$的结论适用域不同。证毕。

## 9.99 追加锚

## 10. 量子条件互信息、共用恢复与参考系统

**定义 10.1（有限维量子恢复的对象与距离）。** 以下所有系统均为非零有限维复 Hilbert 空间。记 $\mathcal L(A)$ 为 $A$ 上的线性算子空间，$\mathcal D(A)$ 为密度算子集。量子通道均为完全正且保迹的线性映射，简称 CPTP。对 $\rho_{ABC}\in\mathcal D(A\otimes B\otimes C)$，下标表示相应偏迹边缘，定义
$$
S(\rho)=-\operatorname{Tr}(\rho\ln\rho),\qquad
I(A:C\mid B)_\rho
=S(\rho_{AB})+S(\rho_{BC})-S(\rho_B)-S(\rho_{ABC}),
\tag{10.1}
$$
其中 $0\ln0=0$。本节全部熵使用自然对数。对同一系统上的密度算子，定义根保真度与半迹距离
$$
F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1,\qquad
d_1(\rho,\sigma)=\frac12\|\rho-\sigma\|_1.
\tag{10.2}
$$
因此 $F$ 不是某些文献采用的平方保真度 $F^2$。恢复映射的类型固定为
$$
\mathcal R:\mathcal L(B)\longrightarrow\mathcal L(B\otimes C),\qquad
\widehat\rho_{ABC}=(\operatorname{id}_A\otimes\mathcal R)(\rho_{AB}).
\tag{10.3}
$$
恢复比较的是整个 $ABC$ 联合态；系统 $A$ 上保持恒等通道。

**定理 10.2（Fawzi–Renner 恢复界）。** 对每个 $\rho_{ABC}$，存在 CPTP 映射 $\mathcal R:B\to BC$，使
$$
F(\rho_{ABC},\widehat\rho_{ABC})
\ge \exp\!\left[-\frac12 I(A:C\mid B)_\rho\right].
\tag{10.4}
$$
同一个恢复映射满足
$$
d_1(\rho_{ABC},\widehat\rho_{ABC})
\le \sqrt{1-\exp[-I(A:C\mid B)_\rho]}
\le \sqrt{I(A:C\mid B)_\rho}.
\tag{10.5}
$$

这里的结论是 $\rho$ 接近某个从其自身 $AB$ 边缘恢复的态 $\widehat\rho$。定理没有断言 $I(A:C\mid B)_{\widehat\rho}=0$，也没有给出到全部精确 Markov 态集合的同一距离界；这一差别见下引 Fawzi–Renner 论文第1节对近似 Markov 性的讨论。

**证明。** 式(10.4)是 Omar Fawzi、Renato Renner，[*Quantum conditional mutual information and approximate Markov chains*](https://arxiv.org/abs/1410.0664v3)，Theorem 5.1，式(102)的有限维版本。原文熵以二为底，因 $I_{\mathrm{nat}}=(\ln2)I_{\mathrm{bits}}$，其 $2^{-I_{\mathrm{bits}}/2}$ 正好成为式(10.4)。式(10.5)由同文 Lemma B.1 在归一化态上的不等式
$$
d_1(\rho,\sigma)^2\le 1-F(\rho,\sigma)^2
$$
以及 $1-e^{-x}\le x$（$x\ge0$）直接得到。非负性 $I(A:C\mid B)_\rho\ge0$ 是强次可加性。$\square$

**推论 10.3（零条件互信息与精确恢复等价）。** 对有限维三方态，
$$
I(A:C\mid B)_\rho=0
\quad\Longleftrightarrow\quad
\exists\mathcal R:B\to BC\ \mathrm{CPTP},\
(\operatorname{id}_A\otimes\mathcal R)(\rho_{AB})=\rho_{ABC}.
\tag{10.6}
$$

**证明。** 正向由式(10.5)得到半迹距离为零。反向设精确恢复成立。互信息在局部通道下满足数据处理，因此对输入 $\rho_{AB}$ 上的通道 $\mathcal R$ 有
$$
I(A:BC)_\rho\le I(A:B)_\rho.
$$
而熵的链式恒等式给出
$$
I(A:C\mid B)_\rho=I(A:BC)_\rho-I(A:B)_\rho\le0.
$$
结合强次可加性得零。$\square$

**定理 10.4（固定边缘的通用恢复器）。** 固定任意 $\omega_{BC}\in\mathcal D(B\otimes C)$，存在一个 CPTP 映射 $\mathcal R_\omega:B\to BC$，使对每个有限维系统 $A$ 及每个满足 $\rho_{BC}=\omega_{BC}$ 的扩展 $\rho_{ABC}$，都有
$$
F\!\left(\rho_{ABC},
(\operatorname{id}_A\otimes\mathcal R_\omega)(\rho_{AB})\right)
\ge e^{-I(A:C\mid B)_\rho/2}.
\tag{10.7}
$$
其量词顺序为
$$
\forall\omega_{BC}\ \exists\mathcal R_\omega\
\forall A\ \forall\rho_{ABC}\text{ 满足 }\rho_{BC}=\omega_{BC}.
\tag{10.8}
$$
这是 David Sutter、Omar Fawzi、Renato Renner，[*Universal recovery map for approximate Markov chains*](https://arxiv.org/abs/1504.07251v3)，Theorem 2.1 的有限维、自然对数版本。

同一映射还满足
$$
\mathcal R_\omega(\omega_B)=\omega_{BC}.
\tag{10.9}
$$

式(10.9)约束指定输入 $\omega_B$，并不把 $\operatorname{Tr}_C\circ\mathcal R_\omega$ 规定为整个 $\mathcal L(B)$ 上的恒等通道。式(10.8)也没有将恢复器统一到所有彼此不同的 $BC$ 边缘上。上述来源的 Corollary 2.4 对其显式结构给出线性化保真度界；这里引用的是 Theorem 2.1 的存在性与完整指数界。

**证明。** 对式(10.9)，取任意乘积扩展 $\rho_{ABC}=\rho_A\otimes\omega_{BC}$。其条件互信息为零；式(10.7)及式(10.5)中的保真度到迹距离转换给出精确恢复。对 $A$ 取偏迹即得式(10.9)。这也是原文 Remark 2.3。$\square$

**推论 10.5（固定边缘态族的共同误差）。** 设 $\mathcal F$ 是非空的一族有限维三方态，所有成员具有同一个 $BC$ 边缘 $\omega_{BC}$；参考系统 $A$ 的有限维数可以随成员变化。若存在 $\varepsilon\ge0$ 使
$$
I(A:C\mid B)_\rho\le\varepsilon\qquad(\rho\in\mathcal F),
$$
则定理10.4中的同一个 $\mathcal R_\omega$ 满足
$$
\sup_{\rho\in\mathcal F}
d_1\!\left(\rho_{ABC},
(\operatorname{id}_A\otimes\mathcal R_\omega)(\rho_{AB})\right)
\le\sqrt{1-e^{-\varepsilon}}\le\sqrt\varepsilon.
\tag{10.10}
$$

**证明。** 对每个成员用式(10.7)及保真度到迹距离转换；函数 $x\mapsto\sqrt{1-e^{-x}}$ 在非负半轴上递增，所以各项由同一右端控制，取上确界即可。$\square$

**引理 10.6（CPTP 后处理的迹距离收缩）。** 若 $\Lambda:\mathcal L(X)\to\mathcal L(Y)$ 为 CPTP，则对任意 $\rho,\sigma\in\mathcal D(X)$，
$$
d_1(\Lambda(\rho),\Lambda(\sigma))\le d_1(\rho,\sigma).
\tag{10.11}
$$
这对任何有限维参考系统 $E$ 上的 $\Lambda\otimes\operatorname{id}_E$ 同样成立。

**证明。** 写 Hermitian 差的 Jordan 分解 $\rho-\sigma=H_+-H_-$，其中 $H_\pm\ge0$ 且
$$
\|\rho-\sigma\|_1=\operatorname{Tr}H_++\operatorname{Tr}H_-.
$$
由正性、保迹性和三角不等式，
$$
\|\Lambda(\rho-\sigma)\|_1
\le\|\Lambda(H_+)\|_1+\|\Lambda(H_-)\|_1
=\operatorname{Tr}H_++\operatorname{Tr}H_-.
$$
除以二得式(10.11)。完全正性保证 $\Lambda\otimes\operatorname{id}_E$ 为正，且该映射仍保迹，故同证适用。

这一证明使用的正负部分分解与本库 [FiniteTraceDistance](../../../D5/S3/Quantum/Foundation/FiniteTraceDistance.lean) 的 **traceDistance_contract** 相同；后者的通道声明采用相同输入输出载体。本节允许不同有限维输入输出，并显式保留参考。一般迹范数收缩也见 John Watrous，[*The Theory of Quantum Information*](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，Corollary 3.40，式(3.241)。 $\square$

**命题 10.7（通道距离的参考量词）。** 对两个同型 CPTP 通道 $\Phi,\Psi:\mathcal L(X)\to\mathcal L(Y)$，定义
$$
d_\diamond(\Phi,\Psi)
=\sup_{\substack{E\text{ 有限维}\\
                  \eta_{XE}\in\mathcal D(X\otimes E)}}
d_1\!\left((\Phi\otimes\operatorname{id}_E)(\eta),
           (\Psi\otimes\operatorname{id}_E)(\eta)\right).
\tag{10.12}
$$
此量等于标准 diamond 范数距离 $\frac12\|\Phi-\Psi\|_\diamond$，且满足 $0\le d_\diamond\le1$。上确界可在 $\dim E=\dim X$ 的纯态输入上取到最大值。

式(10.12)沿用[量子上下文卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)第72、120节的完整通道比较：输入可以与保留参考纠缠，且两个通道接受同一个联合输入。参考不经被比较通道处理；若某个记忆寄存器在槽内参与相互作用，它属于该槽的输入输出对象。

**证明。** 通道差保持 Hermitian 性，因此标准 diamond 范数与式(10.12)的相等性由 Watrous 上引书 Theorem 3.51，式(3.291)给出。参考维数的约化还可直接从式(10.12)看出：对任意混合输入作纯态凸分解，迹范数凸性表明其值不超过分解中各纯态值的最大值；每个纯态在 $X:E$ 切分上的 Schmidt 秩至多为 $\dim X$。将其参考支撑等距嵌入一个 $\dim X$ 维的空间，不改变输出差的非零奇异值。反之该固定参考本就在允许上确界内；纯态集的紧性和迹范数连续性给出最大值。输出均为归一化态，故距离至多一。$\square$

**命题 10.8（共同 CPTP 上下文不放大通道误差）。** 对任意 CPTP 通道 $\Gamma:W\to X$、$\Lambda:Y\to Z$，
$$
d_\diamond(\Lambda\circ\Phi\circ\Gamma,\,
           \Lambda\circ\Psi\circ\Gamma)
\le d_\diamond(\Phi,\Psi).
\tag{10.13}
$$
对任意有限维旁观系统 $M$，
$$
d_\diamond(\Phi\otimes\operatorname{id}_M,\,
           \Psi\otimes\operatorname{id}_M)
=d_\diamond(\Phi,\Psi).
\tag{10.14}
$$
更一般地，若共同接线由 CPTP 映射
$$
\Gamma:W\to X\otimes M,\qquad
\Lambda:Y\otimes M\to Z
$$
给出，则
$$
d_\diamond\!\left(
\Lambda\circ(\Phi\otimes\operatorname{id}_M)\circ\Gamma,\,
\Lambda\circ(\Psi\otimes\operatorname{id}_M)\circ\Gamma
\right)
\le d_\diamond(\Phi,\Psi).
\tag{10.15}
$$

这是 Watrous 上引书 Proposition 3.48 与参考稳定性的应用，也是量子上下文卷第72节历史抬升误差界的单槽条件。前后处理必须在两个被比较对象间共用；若更换控制器或遗漏会参与后续操作的寄存器，就改变了式(10.15)的比较对象。

**证明。** 固定任意参考 $E$ 和联合输入 $\eta_{WE}$。$\Gamma\otimes\operatorname{id}_E$ 的输出仍是合法密度算子，因此中间通道差由式(10.12)控制；再用引理10.6处理 $\Lambda\otimes\operatorname{id}_E$，最后取上确界，得到式(10.13)。在式(10.14)左端，将 $M\otimes E$ 整体视为 $\Phi,\Psi$ 的参考，得“$\le$”；在右端任意测试输入上额外张量一个固定的 $M$ 态，迹范数因 $\|\tau_M\|_1=1$ 而不变，得“$\ge$”。式(10.15)由式(10.13)、(10.14)接续得到。$\square$

**命题 10.9（共用恢复器的两态下界）。** 设 $\mathcal E:X\to Y$ 为保留记录通道，$\mathcal T:X\to Z$ 为目标通道，$\mathcal R:Y\to Z$ 为任意共用 CPTP 恢复器。对任意 $\rho,\sigma\in\mathcal D(X)$，令
$$
e_\rho=d_1(\mathcal T(\rho),\mathcal R\mathcal E(\rho)),
\qquad
e_\sigma=d_1(\mathcal T(\sigma),\mathcal R\mathcal E(\sigma)).
$$
则
$$
\max\{e_\rho,e_\sigma\}
\ge\frac12\left[
d_1(\mathcal T(\rho),\mathcal T(\sigma))
-d_1(\mathcal E(\rho),\mathcal E(\sigma))
\right].
\tag{10.16}
$$

**证明。** 在两个目标态之间插入 $\mathcal R\mathcal E(\rho)$ 和 $\mathcal R\mathcal E(\sigma)$，两次三角不等式及引理10.6给出
$$
d_1(\mathcal T(\rho),\mathcal T(\sigma))
\le e_\rho+
d_1(\mathcal E(\rho),\mathcal E(\sigma))+e_\sigma.
$$
再用 $e_\rho+e_\sigma\le2\max\{e_\rho,e_\sigma\}$。

式(10.16)是量子上下文卷第120.4节相位态反例所用的两态论证；本库 [FiniteRecordRecoveryError](../../../D5/S3/Quantum/Decoherence/FiniteRecordRecoveryError.lean) 的 **finite_record_recovery_error_lower_bound** 将同一论证用于有限移位记录通道，得到 $(1-|\gamma|)/2$ 的恢复误差下界。 $\square$

**命题 10.10（逐态存在不允许交换量词：擦除反例）。** 令 $X=\mathbb C^2$、$Y=\mathbb C$，取擦除通道
$$
\mathcal E(H)=\operatorname{Tr}H,\qquad
\rho_0=|0\rangle\langle0|,\qquad
\rho_1=|1\rangle\langle1|.
$$
分别定义制备通道 $\mathcal R_i(z)=z\rho_i$。则
$$
\forall i\in\{0,1\}\ \exists\mathcal R_i,\quad
\mathcal R_i\mathcal E(\rho_i)=\rho_i,
$$
但任何共用恢复器 $\mathcal R$ 都满足
$$
\max_{i\in\{0,1\}}d_1(\rho_i,\mathcal R\mathcal E(\rho_i))
\ge\frac12.
\tag{10.17}
$$

**证明。** 两个擦除输出相同，而目标态距离为一，代入式(10.16)即可。制备 $\tau=I_X/2$ 时，两项距离均为 $1/2$，所以式(10.17)在这两个测试态组成的态族上最优。若固定 $\mathcal R_0$，则恢复在 $\rho_0$ 上误差为零，在 $\rho_1$ 上误差为一，从而
$$
d_\diamond(\operatorname{id}_X,\mathcal R_0\circ\mathcal E)=1.
\tag{10.18}
$$
下界由输入 $\rho_1$ 给出，上界由命题10.7给出。

把此例中的 $A,B$ 取为一维、$C=X$，每个 $\rho_i$ 的 $I(A:C\mid B)$ 都为零；但两个 $BC$ 边缘不同，所以它不满足定理10.4的共同边缘假设。式(10.18)同时表明，某个输入上的零恢复误差不能推出该恢复通道的 diamond 误差小。 $\square$

**推论 10.11（恢复误差对后续任务的有效范围）。** 在推论10.5的假设下，对每个 $\rho\in\mathcal F$，令 $\widehat\rho=(\operatorname{id}_A\otimes\mathcal R_\omega)(\rho_{AB})$。若 $\Lambda$ 是定义于完整 $ABC$ 输出上的共同 CPTP 后处理，则
$$
d_1(\Lambda(\rho),\Lambda(\widehat\rho))
\le\sqrt{1-e^{-\varepsilon}}.
\tag{10.19}
$$
特别地，对任意有限结果的共同 POVM 读出，其输出概率分布的总变差距离至多为此值；任意取值于 $[0,L]$ 的共同损失函数之期望差，绝对值至多为 $L\sqrt{1-e^{-\varepsilon}}$。

这一任务界控制所声明的固定边缘态族。定理10.4虽然量化所有有限维 $A$，仍要求每个联合输入的 $BC$ 边缘等于 $\omega_{BC}$；diamond 距离则对全部输入态取上确界。要得到
$$
d_\diamond(\operatorname{id}_{BC},
           \mathcal R_\omega\circ\operatorname{Tr}_C)\le\delta,
$$
必须另外证明同一个 $\mathcal R_\omega$ 对式(10.12)中的全部联合输入具有误差界 $\delta$。固定边缘上的估计不包含这个额外量词。相反，一旦 diamond 界成立，命题10.8就使它对所有共同 CPTP 接线成立。这与量子上下文卷第120—122节区分状态族缺陷、完整过程缺陷及共同模拟器的方式一致。

**证明。** 式(10.19)是式(10.10)与引理10.6的组合。POVM 是到经典对角态的 CPTP 通道，而对角态的半迹距离正好是总变差距离。若输出分布为 $p,q$，写 $\Delta=p-q$，则 $\sum\Delta=0$、正部分与负部分的总质量均为 $\operatorname{TV}(p,q)$。因此 $0\le\ell\le L$ 给
$$
\left|\sum_y\ell(y)(p(y)-q(y))\right|
\le L\,\operatorname{TV}(p,q).
$$
$\square$

## 10.99 追加锚

## 11. 带记忆量子过程的表示、历史概率与可访问关系

**定义 11.1（有限维载体与 Choi 约定）。** 全部 Hilbert 空间均为非零有限维复空间，$\mathcal L(A)$ 表示 $A$ 上的全部复线性算子。对每个输入空间 $A$ 固定正交归一基 $\{|i\rangle\}_{i=1}^{d_A}$，把输入参考副本 $A'$ 与 $A$ 按此基识别，并记
$$
E_{ij}=|i\rangle\langle j|,\qquad
|\Omega_A\rangle=\sum_{i=1}^{d_A}|i\rangle_{A'}\otimes|i\rangle_A.
\tag{11.1}
$$
对复线性映射 $\Phi:\mathcal L(A)\to\mathcal L(B)$，取输入参考在前、输出在后的未归一化 Choi 算子
$$
J(\Phi)
=(\operatorname{id}_{A'}\otimes\Phi)(|\Omega_A\rangle\langle\Omega_A|)
=\sum_{i,j}E_{ij}^{A'}\otimes\Phi(E_{ij})
\in\mathcal L(A'\otimes B).
\tag{11.2}
$$
符号 $\mathsf T$ 表示所选基中的普通转置，$\dagger$ 表示共轭转置；基底运输同时运输转置约定。无歧义时将 $A'$ 简写为 $A$。完全正量化所有有限参考 $R$ 上 $\operatorname{id}_R\otimes\Phi$ 的正性；不增迹指对每个 $X\ge0$ 有 $\operatorname{Tr}\Phi(X)\le\operatorname{Tr}X$。

**定理 11.2（Choi 重建与完全正、迹条件）。** 定义11.1给出全部复线性映射与 $\mathcal L(A'\otimes B)$ 之间的线性双射，逆映射为
$$
\Phi(X)=\operatorname{Tr}_{A'}\bigl[(X^{\mathsf T}\otimes I_B)J(\Phi)\bigr].
\tag{11.3}
$$
且
$$
\begin{aligned}
\Phi\text{ 完全正}&\iff J(\Phi)\ge0,\\
\Phi\text{ 保迹}&\iff \operatorname{Tr}_B J(\Phi)=I_{A'},\\
\Phi\text{ 完全正且不增迹}
&\iff J(\Phi)\ge0\ \text{且}\ \operatorname{Tr}_B J(\Phi)\le I_{A'}.
\end{aligned}
\tag{11.4}
$$

**证明。** 因为 $\operatorname{Tr}(X^{\mathsf T}E_{ij})=X_{ij}$，式(11.3)返回 $\sum_{ij}X_{ij}\Phi(E_{ij})$。反过来，任意 $J$ 的 $(i,j)$ 输入块唯一指定 $\Phi(E_{ij})$；矩阵单位是一组复基，因此得到双射。

若 $\Phi$ 完全正，式(11.2)是正算子在正性放大下的像。若 $J(\Phi)\ge0$，取有限谱分解
$$
J(\Phi)=\sum_\alpha|v_\alpha\rangle\langle v_\alpha|,
\qquad v_\alpha=\sum_i|i\rangle\otimes K_\alpha|i\rangle,
\tag{11.5}
$$
其中特征值平方根吸入 $v_\alpha$，$K_\alpha:A\to B$ 由其列确定。逐输入块比较得
$$
\Phi(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger.
\tag{11.6}
$$
任意参考上的放大为 $\sum_\alpha(I_R\otimes K_\alpha)X(I_R\otimes K_\alpha)^\dagger$，故保持正性。零 Choi 算子取空和。

$\operatorname{Tr}_BJ(\Phi)$ 的 $(i,j)$ 元为 $\operatorname{Tr}\Phi(E_{ij})$，所以它等于 $I$ 当且仅当 $\Phi$ 在全部矩阵单位、进而全部复矩阵上保迹。对完全正映射，令 $F=\sum_\alpha K_\alpha^\dagger K_\alpha\ge0$。迹循环给 $\operatorname{Tr}\Phi(X)=\operatorname{Tr}(FX)$，且 $\operatorname{Tr}_BJ(\Phi)=F^{\mathsf T}$。对全部 $X\ge0$ 不增迹等价于 $F\le I$：充分性用正算子的迹配对非负，必要性取 $X=|u\rangle\langle u|$。转置保持正序，得到式(11.4)。

这是 Choi—Kraus 定理的有限维形式，见 Watrous，*The Theory of Quantum Information*，2018，[第2章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，式(2.64)—(2.66)、定理2.22与2.26，印刷第78、82—84、87—89页。完整 Kraus 族的通道接口亦见 [FiniteKrausChannel](../../../D5/S3/Quantum/Foundation/FiniteKrausChannel.lean) 的 finite_kraus_quantum_channel。$\square$

**命题 11.3（因子次序与归一化运输）。** Watrous 的输出在前约定 $J_W(\Phi)\in\mathcal L(B\otimes A')$ 与式(11.2)由交换两因子的固定酉映射对应。通道满足 $\operatorname{Tr}J(\Phi)=d_A$。归一化 Bell 输入给出的 $\widehat J=J/d_A$ 满足
$$
\operatorname{Tr}\widehat J=1,\qquad
\operatorname{Tr}_B\widehat J=I_{A'}/d_A,
$$
且以 $\widehat J$ 重建时，式(11.3)右侧须乘 $d_A$。

**证明。** 对式(11.2)逐项交换张量因子即得文献约定。对式(11.4)的偏迹等式取总迹，得 $\operatorname{Tr}J=d_A$；其余由线性缩放得到。$\square$

**命题 11.4（顺序接线的 Choi 收缩）。** 若 $\Phi:\mathcal L(A)\to\mathcal L(B)$、$\Psi:\mathcal L(B)\to\mathcal L(C)$，则在 $A\otimes B\otimes C$ 的次序下
$$
J(\Psi\circ\Phi)
=\operatorname{Tr}_B\!\left[
\bigl(J(\Phi)^{\mathsf T_B}\otimes I_C\bigr)
\bigl(I_A\otimes J(\Psi)\bigr)
\right].
\tag{11.7}
$$
这里 $\mathsf T_B$ 只转置接线空间 $B$；两个乘因子不要求交换。

**证明。** 展开 $J(\Phi)=\sum_{ij}E_{ij}\otimes\Phi(E_{ij})$ 与 $J(\Psi)=\sum_{kl}E_{kl}\otimes\Psi(E_{kl})$，再用
$$
\operatorname{Tr}\bigl(\Phi(E_{ij})^{\mathsf T}E_{kl}\bigr)
=\Phi(E_{ij})_{kl},
$$
所得 $(i,j)$ 块正是 $\Psi(\Phi(E_{ij}))$。这是 Chiribella、D’Ariano、Perinotti，*Theoretical framework for quantum networks*，Physical Review A 80，022339（2009），[arXiv:0904.4483v2](https://arxiv.org/pdf/0904.4483v2)，定理1及式(13)，PDF第3页的 link product 在本节次序下的形式。中间乘积不必 Hermitian；复合完全正时最终 Choi 算子的正性由定理11.2保证。$\square$

**定义 11.5（因果梳与实际记忆接线）。** 固定 $n\ge1$。第 $k$ 轮先接收 $A_k$、再输出 $B_k$，之后才进入第 $k+1$ 轮；实验者可以根据先前输出及其保留记忆制备后续输入。令
$$
\mathcal H_k=A_1'\otimes B_1\otimes\cdots\otimes A_k'\otimes B_k,
\qquad\mathcal H_0=\mathbb C.
\tag{11.8}
$$
确定性因果梳由正算子 $R^{(k)}\in\mathcal L(\mathcal H_k)$ 给出，满足
$$
R^{(0)}=1,\qquad
\operatorname{Tr}_{B_k}R^{(k)}=R^{(k-1)}\otimes I_{A_k'}
\quad(1\le k\le n).
\tag{11.9}
$$
右侧次序为 $\mathcal H_{k-1}\otimes A_k'$。从末时刻向前排列时，同一条件写为 $I_{A_k'}\otimes R^{(k-1)}$，两种写法以固定因子置换对应。

顺序网络的 Choi 算子指：将网络视作从 $\bigotimes_kA_k$ 到 $\bigotimes_kB_k$ 的多部件通道，按式(11.2)取 Choi 算子，再排成式(11.8)。实际环境若跨两步回流，就作为同一个内部记忆接线；用两个约化系统通道替代该接线，须另有约化闭合等式。因果梳的时域 $n$、内部记忆实现和实验者可接入的端口分别作为数据；固定有限时域的记忆实现不附带跨全部时域的统一维数合同。

**定理 11.6（有限时域梳的实现）。** 在定义11.5的有限维、固定时间次序下，正性与式(11.9)等价于存在有限维记忆 $M_k$、$M_0=\mathbb C$ 及等距映射
$$
V_k:M_{k-1}\otimes A_k\longrightarrow B_k\otimes M_k,
\qquad V_k^\dagger V_k=I,
\tag{11.10}
$$
使顺序网络在最后舍弃 $M_n$ 后给出 $R^{(n)}$。允许一般逐轮 CPTP 映射给出同一类梳。其迹满足
$$
\operatorname{Tr}R^{(k)}=\prod_{j=1}^k d_{A_j}.
\tag{11.11}
$$

**证明。** 充分性是 Chiribella、D’Ariano、Perinotti 所引版本定理3与定理5，PDF第7、11页：取文献的 $H_{2k-2}=A_k$、$H_{2k-1}=B_k$，再置换成式(11.8)。一般 CPTP 实现的逐轮 Stinespring 环境可并入后续记忆；混合初始记忆可在第一轮制备并净化。

对必要性，令 $\Gamma_k$ 为前 $k$ 轮后舍弃内部记忆的多部件通道。最后一次操作保迹，故对全部输入算子 $X$ 有
$$
\operatorname{Tr}_{B_k}\Gamma_k(X)
=\Gamma_{k-1}(\operatorname{Tr}_{A_k}X).
\tag{11.12}
$$
此前输出上隐含恒等映射。把 $X$ 展开成输入矩阵单位，$A_k$ 上的迹给 $\delta_{ij}$，正好得到式(11.9)。这也适用于跨时间输入相关的 $X$。反复取迹给式(11.11)。文献第7—8页以各前缀 Choi 秩构造等距实现的记忆维数上界；该上界描述一种实现，不等同于最小物理记忆或最小控制门数。$\square$

**命题 11.7（整体保迹不足以保证时间因果性）。** 存在多部件酉通道不满足定义11.5的指定时间次序。

**证明。** 取两个 qubit 输入，以交换通道把 $A_2$ 送至 $B_1$、$A_1$ 送至 $B_2$。它完全正且保迹。固定 $A_1$，分别输入 $A_2=|0\rangle$ 或 $|1\rangle$，第一轮输出 $B_1$ 随第二轮输入改变，违反式(11.12)，故不满足式(11.9)。$\square$

**定义 11.8（过程张量与梳的端口对应）。** 固定时刻 $0,\ldots,k$、系统端口 $S_j^{\mathrm{in}}$ 和 $S_j^{\mathrm{out}}$。控制分支为完全正不增迹映射 $\mathcal A_j:\mathcal L(S_j^{\mathrm{in}})\to\mathcal L(S_j^{\mathrm{out}})$；确定性控制为 CPTP。给共同初态 $\rho_{S_0E}$，其中 $S_0=S_0^{\mathrm{in}}$，及同型接续的 CPTP 映射 $\mathcal U_{j+1:j}:\mathcal L(S_j^{\mathrm{out}}\otimes E)\to\mathcal L(S_{j+1}^{\mathrm{in}}\otimes E)$，定义
$$
\mathfrak T_{k:0}[\mathcal A_{k-1},\ldots,\mathcal A_0]
=\operatorname{Tr}_E\!\left[
\mathcal U_{k:k-1}(\mathcal A_{k-1}\otimes\operatorname{id}_E)
\cdots\mathcal U_{1:0}(\mathcal A_0\otimes\operatorname{id}_E)
(\rho_{S_0E})\right].
\tag{11.13}
$$
其值为未归一化终态，迹为所选结果序列的概率。独立控制时它对各 $\mathcal A_j$ 分别线性，进而在线性张量积上延伸；反馈或反复接触同一个控制辅助系统时，控制对象取具有对应时间次序的联合控制梳，保持同一辅助实现。

在各系统端口同维且联合演化为酉时，式(11.13)即为 Pollock、Rodríguez-Rosario、Frauenheim、Paternostro、Modi，*Non-Markovian quantum processes: complete framework and efficient characterisation*，[arXiv:1512.00589v3](https://arxiv.org/pdf/1512.00589v3)，定义1、性质P1—P3及定理2，PDF第2—3页的开放量子演化式(2)。其完全正性量化带控制辅助系统的物理输出，containment 按已声明的槽填充操作抽取子区间；在同型槽填入恒等控制与舍弃前段后重置环境是不同操作。该文图4（第5页）将过程及相关控制都表示为量子梳，定理4（第7页）给多时 Choi 表示，第IV.C节（第8页）给因果偏迹及子过程收缩。

本节按定义11.5表示同一端口结构：令 $n=k+1$、$A_1=\mathbb C$、$B_1=S_0^{\mathrm{in}}$，并对 $0\le j<k$ 取
$$
A_{j+2}=S_j^{\mathrm{out}},\qquad B_{j+2}=S_{j+1}^{\mathrm{in}}.
\tag{11.14}
$$
因此过程首先输出初始系统，随后每次接收控制后的系统并给出下一系统；控制 $\mathcal A_j$ 接在 $B_{j+1}$ 与 $A_{j+2}$ 之间。未归一化 Choi 梳具有正性与式(11.9)的因果偏迹条件，$R^{(1)}=\rho_{S_0}$；其实现取定理11.6。若以迹一多时 Choi 密度表示，则除以 $\prod_{j=0}^{k-1}\dim S_j^{\mathrm{out}}$，相应收缩公式同时运输此因子。端口量化、归一化与允许控制族属于同一表示合同。

**定义 11.9（历史索引仪器）。** 使用[量子卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)第72节的完整历史、活动记忆与惰性参考规范。固定时域 $N$、非空有限结果集 $Y_t$ 和每层共同有限维载体 $Q_t$。$Q_t=S_t\otimes M_t$ 包含系统与仍会回流的物理记忆。不同历史的载体通过已声明的共同嵌入识别；动作和仪器的类型在同层一致。

对已取得历史 $h=(y_1,\ldots,y_{t-1})$，控制器选择 $a=\pi_t(h)$，并指定
$$
\Phi^{h,a}_{t,y}:\mathcal L(Q_{t-1})\to\mathcal L(Q_t)
\quad(y\in Y_t),\qquad
\Phi^{h,a}_{t,y}\text{ 完全正},\qquad
\sum_y\Phi^{h,a}_{t,y}\text{ 保迹}.
\tag{11.15}
$$
在所比较输入族的每个可达正概率历史上动作须合法；或以失败结果给出总化仪器。全族都不可达的历史可作同型合法扩展，但扩展对各输入共同固定。随机控制的实际随机变量及复用位置并入历史或载体。

给任意有限惰性参考 $R$ 及共同初态密度 $\rho_{RQ_0}$，定义
$$
\sigma_\varnothing=\rho_{RQ_0},\qquad
\sigma_{hy}=(\operatorname{id}_R\otimes\Phi^{h,\pi_t(h)}_{t,y})(\sigma_h),
\qquad p(h)=\operatorname{Tr}\sigma_h,
\tag{11.16}
$$
并令 $\Phi_h$ 为沿 $h$ 按时间从右向左的分支复合，$\Phi_\varnothing=\operatorname{id}$。全过程使用同一初态及物理记忆，不要求 $R$ 与 $Q_0$ 独立。仪器的完全正分支及经典旗标约定亦见 Watrous 所引第2章第2.3.2节、式(2.255)—(2.262)，印刷第111—113页。

**定理 11.10（历史树归一化与历史 POVM）。** 定义11.9给出非负联合概率，满足
$$
\sum_{y\in Y_t}p(hy)=p(h),\qquad
\sum_{h\in Y_1\times\cdots\times Y_t}p(h)=1.
\tag{11.17}
$$
对任意前缀 $h$，全部有限后续结果求和仍为 $p(h)$。每层的 $\sum_{|h|=t}\Phi_h$ 是 CPTP，并且
$$
\sigma_h=(\operatorname{id}_R\otimes\Phi_h)(\rho_{RQ_0}),\qquad
E_h=\Phi_h^*(I_{Q_t})\ge0,\qquad
\sum_{|h|=t}E_h=I_{Q_0},\qquad
p(h)=\operatorname{Tr}(E_h\rho_{Q_0}),
\tag{11.18}
$$
其中 $\Phi_h^*$ 为 Hilbert–Schmidt 伴随。仅当 $p(h)>0$ 时定义条件态 $\sigma_h/p(h)$ 与下一结果概率 $p(hy)/p(h)$。正概率完整历史满足
$$
p(y_1,\ldots,y_t)=\prod_{j=1}^t p(y_j\mid y_1,\ldots,y_{j-1}).
\tag{11.19}
$$

**证明。** 完全正保证各 $\sigma_h\ge0$。固定父历史后，仪器之和保迹，故
$$
\sum_y\operatorname{Tr}\sigma_{hy}
=\operatorname{Tr}\left[(\operatorname{id}_R\otimes\sum_y\Phi^{h,\pi_t(h)}_{t,y})(\sigma_h)\right]
=\operatorname{Tr}\sigma_h.
$$
从 $p(\varnothing)=1$ 按层归纳得归一化，从末层向前求和得前缀一致性。正算子迹零必为零，故零概率父支的全部后继也为零。

每个 $\Phi_h$ 完全正。同一历史树逐层求和保迹，故其层和是通道；完全正伴随及其保单位性给式(11.18)。最后一个迹恒等式由 Hilbert–Schmidt 伴随的定义及参考系统偏迹直接得到。同一输入输出载体时，亦可应用 [FiniteKrausInstrumentBornMarginal](../../../D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean) 的 finite_kraus_instrument_born_marginal；本节允许不同 $Q_0,Q_t$ 的情形由上述直接计算承担。式(11.19)由各相邻比值望远镜相乘得到。条件概率依赖同一前缀的条件态与动作，不能由该式换为无条件边缘的乘积。$\square$

**定义 11.11（经典档案、活动记忆与参考）。** 历史档案 $H_t$ 具有正交基 $\{|h\rangle\}_{|h|=t}$，对应联合记录为
$$
\Omega_t=\sum_{|h|=t}|h\rangle\langle h|_{H_t}\otimes\sigma_h
\in\mathcal L(H_t\otimes R\otimes Q_t).
\tag{11.20}
$$
经典性指定 $H_t$ 基中的块对角结构；各 $RQ_t$ 块仍保留其量子关联。活动记忆 $M_t$ 指已声明分解 $Q_t=S_t\otimes M_t$ 中后续可相互作用的因子，其控制权限、重置及回流均属于操作合同。惰性参考 $R$ 指过程中始终不被操作的关联因子；若后来与系统相互作用，该因子转入活动载体或开放端口。档案可读字段及可复制标签、物理记忆可控制操作、参考的可制备与终端可读取范围分别指定。

**命题 11.12（记录归一化、压缩与反馈取值）。** 式(11.20)为密度矩阵；舍弃档案给 $\sum_h\sigma_h$。对经典函数 $q:H_t\to Z$，压缩给
$$
\Omega_t^q=\sum_z|z\rangle\langle z|\otimes\sum_{q(h)=z}\sigma_h.
\tag{11.21}
$$
仅以 $z=q(h)$ 选择与原策略相同的确定性动作，当且仅当 $\pi$ 在 $q$ 的每个相关纤维上常值。

**证明。** 每块正且块迹之和由式(11.17)为一。偏迹与经典推前逐块计算即得两种输出。若 $\pi=\bar\pi\circ q$，同纤维的动作相同；反之，在每个非空相关纤维取该共同动作便定义 $\bar\pi$。这项等价只约束依赖档案的动作函数；若允许从 $Q_t$ 另读信息，须验证该额外读出及其扰动是否实现相同协议。受控充分状态与统一过程模拟的相应条件见量子卷第118.16、120节。$\square$

**命题 11.13（有限载体与条件状态个数）。** 固定时域 $t$ 的档案基大小为 $\prod_{j=1}^t|Y_j|$；固定有限维物理载体的跨时域可达密度集合却可以无限。

**证明。** 前一式为有限笛卡尔积计数。后一式取单结果 qubit 仪器 $\rho\mapsto U\rho U^\dagger$，其中 $U=\operatorname{diag}(1,e^{i\theta})$、$\theta/(2\pi)$ 无理，初态为 $|+\rangle\langle+|$。第 $t$ 步非对角元为 $e^{-it\theta}/2$，不同 $t\ge0$ 给不同密度。于是载体维数二并不给有限个可达条件态。量子卷第151节的有限经典隐状态实现另以保留全部旗标的逐块纠缠破坏为前提，且限定中途干预及端点输出；本例不取消或代替这些条件。$\square$

**命题 11.14（相同局部态与记录访问的区别）。** 取 qubit $S,M$，令
$$
|\pm\rangle=\frac{|0\rangle\pm|1\rangle}{\sqrt2},\qquad
|\Phi_\pm\rangle=\frac{|00\rangle\pm|11\rangle}{\sqrt2}.
\tag{11.22}
$$
两联合纯态正交，双方局部态均为 $I_2/2$。未来若仅操作 $S$ 及独立于 $SM$、且制备不依赖符号的辅助系统，$M$ 始终不回流，则全部这类仪器历史统计相同。若允许控制 $SM$ 上的耦合 $U|i,j\rangle=|i,j\mathbin{\mathrm{XOR}}i\rangle$，则逆耦合后测量 $S$ 的 $X$ 基能完全区分两态。若实际测量 $M$ 的计算基并只保存经典结果及 $S$，两个输出反而相同。

**证明。** 取 $\rho=|+\rangle\langle+|$、$\sigma=|-\rangle\langle-|$，它们对角元相同且非对角元不同。[CanonicalRecordAccessRecovery](../../../D5/S3/Quantum/Decoherence/CanonicalRecordAccessRecovery.lean) 的 reduced_irreversibility_is_canonical_record_access_defect 直接给 copied-address 模型的全局区别、约化同一、无共同约化恢复函数及实际记录的逆耦合恢复。此例中
$$
U(|\pm\rangle_S|0\rangle_M)=|\Phi_\pm\rangle,
\qquad U^\dagger|\Phi_\pm\rangle=|\pm\rangle_S|0\rangle_M.
\tag{11.23}
$$
局部偏迹各为 $I_2/2$，故限定局部协议从同一局部态出发，定理11.10给相同历史权重。允许 $U^\dagger=U$ 时，后续 $\{|+\rangle\langle+|,|-\rangle\langle-|\}$ 测量分别给确定结果。计算基测量 $M$ 后的经典记录与条件 $S$ 态对两个符号均为
$$
\frac12|0\rangle\langle0|_H\otimes|0\rangle\langle0|_S
+\frac12|1\rangle\langle1|_H\otimes|1\rangle\langle1|_S.
\tag{11.24}
$$
该相同输出的任何共同后处理仍相同，故保存标签本身不恢复相位。$\square$

**定理 11.15（精确不可克隆与经典档案的恢复界限）。** 设单位向量 $\psi,\phi\in H$ 满足 $0<|\langle\psi,\phi\rangle|<1$，记 $P_\psi=|\psi\rangle\langle\psi|$。不存在同一个 CPTP 映射 $\mathcal C:\mathcal L(H)\to\mathcal L(H\otimes H)$ 同时满足
$$
\mathcal C(P_\psi)=P_\psi\otimes P_\psi,\qquad
\mathcal C(P_\phi)=P_\phi\otimes P_\phi.
\tag{11.25}
$$
因此，对任何包含这两个态的输入族，不存在取值于有限经典寄存器的 CPTP 编码 $\mathcal E$ 及共同 CPTP 解码 $\mathcal R$，使 $\mathcal R\mathcal E$ 在该族上精确恢复原态。此结论的量词是同一确定性编码、解码对一个未知输入样本的精确全态恢复。

**证明。** 从式(11.6)及 $\sum_\alpha K_\alpha^\dagger K_\alpha=I$ 构造有限 Stinespring 等距映射 $Vx=\sum_\alpha K_\alpha x\otimes|\alpha\rangle_E$。若 $\mathcal C(P_\psi)=P_\psi\otimes P_\psi$，输出的纯性使
$$
V\psi=\psi\otimes\psi\otimes e_\psi
$$
对某个单位环境向量成立：投影至 $\psi\otimes\psi$ 正交补后的范数平方，等于该输出边缘在正交补上的迹，因而为零。同理 $V\phi=\phi\otimes\phi\otimes e_\phi$。等距性给
$$
|\langle\psi,\phi\rangle|
=|\langle\psi,\phi\rangle|^2|\langle e_\psi,e_\phi\rangle|
\le |\langle\psi,\phi\rangle|^2,
$$
与严格介于零和一矛盾。在没有剩余环境、指定共同空白及精确向量等式的等距模型中，这正是 [NoCloningInnerProductCriterion](../../../D5/S3/Quantum/PureState/NoCloningInnerProductCriterion.lean) 的 no_cloning_inner_product_criterion；量子卷第90.2节保留了该模型的假设。

再设经典编码与解码存在。对每个输入纯态，写 $\mathcal E(P_\psi)=\sum_zp_\psi(z)|z\rangle\langle z|$，$\tau_z=\mathcal R(|z\rangle\langle z|)$。若 $\sum_zp_\psi(z)\tau_z=P_\psi$，在 $\psi$ 的正交补上取迹，由每项非负可知所有 $p_\psi(z)>0$ 的 $\tau_z$ 均等于 $P_\psi$。经典复制通道 $\Delta(|z\rangle\langle z|)=|z,z\rangle\langle z,z|$ 因而使
$$
(\mathcal R\otimes\mathcal R)\Delta\mathcal E(P_\psi)
=\sum_zp_\psi(z)\tau_z\otimes\tau_z=P_\psi\otimes P_\psi.
$$
同一通道也复制 $P_\phi$，与前半部矛盾。正交标签的复制不满足 $0<|\langle\psi,\phi\rangle|<1$，故不受该禁制；带误差恢复或仅恢复指定任务也不满足式(11.25)的精确全态假设。$\square$

**定义 11.16（允许 tester 与过程距离）。** 对共同端口的确定性梳，固定一族实际允许的顺序 tester $\mathfrak T$，每个 tester 包含准备、槽间控制、其活动记忆与终端读出，并给有限经典输出分布 $p_T^R$。定义
$$
d_{\mathfrak T}(R,S)=\sup_{T\in\mathfrak T}\operatorname{TV}(p_T^R,p_T^S),
\tag{11.26}
$$
空族取零。tester 的正性、归一化与顺序实现采用 Chiribella等所引版本定义11及定理11，PDF第17页。实际允许族另受本卷共同实验语言、来源与费用合同约束。

**命题 11.17（共同 tester 距离的范围）。** $d_{\mathfrak T}$ 是值域 $[0,1]$ 的伪度量，其零核恰为所有 $T\in\mathfrak T$ 下输出分布相同的关系。固定接线和反馈得到的普通通道可使用第10节的 diamond 接口；若测试族允许槽间变化，则固定接线只贡献式(11.26)上确界中的一个子族。

**证明。** 每个总变差距离非负、对称且不超过一。逐 tester 的三角不等式取上确界仍给三角不等式；上确界为零当且仅当各项为零。固定共同控制并把活动记忆及历史保留在轮次类型中，CPTP 映射的有限复合仍为通道；扩大 tester 族只增大上确界。这是本卷既有固定读数族上确界构造的实例，量子卷第120.3节的固定接线与 comb 区别采用同一量词。$\square$

**定义 11.18（历史误差与资源接口）。** 对定义11.9的两个候选实现，完整轮次比较采用量子卷第72节的历史旗标通道，其输出包含 $H_t,Q_t$，并按第10节保留同一参考；式(11.16)的未归一化分支为其历史块。第12节的误差预算以这些共同类型、共同控制器及实际可达输入为合同。仅比较归一化后态的证书须另带正概率条件及分支权重；仅比较非选择和的证书不充作完整带旗标证书。

过程矩阵的数学给定、由有限实验估计该矩阵、实现其内部记忆及执行所选 tester 分别指定误差和费用。操作费用取本卷第7节的实际允许路径合同；Choi 或梳的存在表示本身不将准备、复制、记忆访问及读取操作加入允许语言。

## 11.99 追加锚

## 12. 可组合恢复、连续缺陷与相对时钟

**定义 12.1（同一任务的通道接口）。** 设 $X,B,A$ 为有限维复 Hilbert 空间，所有通道均完全正且保迹。固定边界编码 $\mathcal E:X\to B$、目标读出 $\mathcal Q:X\to A$、边界解码 $\mathcal S:B\to A$，以及完整操作 $\mathcal T_j:X\to X$ 和边界操作 $\overline{\mathcal T}_j:B\to B$。这里箭头表示相应矩阵代数间的通道。采用第10节包含外部参考的半 diamond 距离，记
$$
\kappa=d_\diamond(\mathcal S\mathcal E,\mathcal Q),\qquad
\varepsilon_j=d_\diamond(\mathcal E\mathcal T_j,
\overline{\mathcal T}_j\mathcal E).
\tag{12.1}
$$
这些是对同一通道族的统一界，不是对每个输入分别选择解码器后取得的最小值。取 $A=X,\mathcal Q=\operatorname{id}_X,\mathcal S=\mathcal R$，得到恢复完整输入的特例；一般 $\mathcal Q$ 则只指定任务需要的输出。空间类型包含会在后续再次操作的记录和物理记忆；始终不被操作的外部系统才作为惰性参考。

本卷第6节已经给出局部缺陷的路径传播，[量子卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) §72给出保留完整历史和活动记忆的通道望远镜界，§52给出无外部参考的末端预测界。以下将统一解码误差接到该既有传播结构，不把一般望远镜法视作新的原理。完全有界迹范数的成熟性质见 Watrous，[*The Theory of Quantum Information*](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，§3.3，Proposition 3.48及式（3.306）。

**定理 12.2（恢复误差与关系运输误差的共同预算）。** 在定义12.1下，对每个 $n\ge0$，有
$$
\boxed{
d_\diamond\!\left(
\mathcal S\overline{\mathcal T}_n\cdots
\overline{\mathcal T}_1\mathcal E,
\mathcal Q\mathcal T_n\cdots\mathcal T_1
\right)
\le\min\left\{1,\kappa+\sum_{j=1}^n\varepsilon_j\right\}.}
\tag{12.2}
$$
因而接上同一个任意合法终端测量，全部输出分布的总变差也受此界控制。有限经典随机核采用 $d_{\rm cl}(P,Q)=\max_x\operatorname{TV}(P(\cdot\mid x),Q(\cdot\mid x))$ 时，同一式（12.2）成立。完整恢复特例就是
$$
d_\diamond(\mathcal R\overline{\mathcal T}_n\cdots
\overline{\mathcal T}_1\mathcal E,
\mathcal T_n\cdots\mathcal T_1)
\le\min\{1,\kappa+\textstyle\sum_j\varepsilon_j\}.
\tag{12.3}
$$
同一结论允许轮次类型改变：给 $\mathcal E_j:X_j\to B_j$、$\mathcal T_j:X_{j-1}\to X_j$、$\overline{\mathcal T}_j:B_{j-1}\to B_j$、$\mathcal Q_n:X_n\to A$ 与 $\mathcal S_n:B_n\to A$，取
$$
\kappa_n=d_\diamond(\mathcal S_n\mathcal E_n,\mathcal Q_n),\qquad
\varepsilon_j=d_\diamond(\mathcal E_j\mathcal T_j,
\overline{\mathcal T}_j\mathcal E_{j-1}).
$$
则
$$
d_\diamond(\mathcal S_n\overline{\mathcal T}_n\cdots\overline{\mathcal T}_1\mathcal E_0,
\mathcal Q_n\mathcal T_n\cdots\mathcal T_1)
\le\min\{1,\kappa_n+\textstyle\sum_j\varepsilon_j\}.
\tag{12.3a}
$$

**证明。** 置 $D_j=\mathcal E\mathcal T_j-
\overline{\mathcal T}_j\mathcal E$。直接插入中间项得
$$
\mathcal E\mathcal T_n\cdots\mathcal T_1-
\overline{\mathcal T}_n\cdots\overline{\mathcal T}_1\mathcal E
=\sum_{j=1}^n
\overline{\mathcal T}_n\cdots\overline{\mathcal T}_{j+1}
D_j\mathcal T_{j-1}\cdots\mathcal T_1.
\tag{12.4}
$$
空乘积取恒等通道。每项前后均为通道，其 diamond 范数为一，故半范数至多 $\varepsilon_j$。左接 $\mathcal S$ 不放大差；再插入 $\mathcal S\mathcal E\mathcal T_n\cdots\mathcal T_1$，余项为 $(\mathcal S\mathcal E-\mathcal Q)\mathcal T_n\cdots\mathcal T_1$，半范数至多 $\kappa$。三角不等式和两个通道距离不超过一给式（12.2）。同一测量仍是通道，故输出距离不增，经典对角态的迹距离等于总变差。变类型情形把第 $j$ 项的 $D_j$ 换为 $\mathcal E_j\mathcal T_j-\overline{\mathcal T}_j\mathcal E_{j-1}$，内部编码仍逐项抵消，末端改插入 $\mathcal S_n\mathcal E_n\mathcal T_n\cdots\mathcal T_1$，证明完全同样。经典版本直接用随机核的总变差收缩：对任意共同输入分布，两核输出差的总变差至多各点输入差的最大值；前接随机核为凸组合，后接随机核收缩。对同一望远镜恒等式逐项应用即可。$\square$

**命题 12.3（任务恢复与全部量子状态恢复的维数边界）。** 若定义12.1的完整恢复满足 $\mathcal R\mathcal E=\operatorname{id}_X$，则 $\dim B\ge\dim X$。任务恢复 $\mathcal S\mathcal E=\mathcal Q$ 不具有这一普遍下界。例如 $\mathcal Q$ 是只输出一个固定态的通道时，一维边界已经充分。

**证明。** $\mathcal E$ 具有线性左逆，因此在复向量空间 $\mathcal L(X)$ 上单射。于是 $(\dim X)^2\le(\dim B)^2$。固定态目标经一维迹通道再制备该固定态即得。故要求保留指定任务，与要求可逆编码所有未知量子状态具有不同量词。$\square$

**定义 12.4（受限输入与自适应续接）。** 若只在输入族或码空间上使用恢复保证，指定每个时刻允许的、可带参考的联合态集合 $\mathscr A_j$。要求理想前缀把 $\mathscr A_0$ 送入 $\mathscr A_j$；第 $j$ 步缺陷在 $\mathscr A_{j-1}$ 上统一成立，末端恢复缺陷在 $\mathscr A_n$ 上成立。各误差界必须采用同一解码、同一控制器与同一参考约定。对有限自适应协议，历史、控制器和活动量子记忆纳入各轮次类型；追加历史导致类型改变时，每轮编码及解码须有相应类型，不能把这些轮次写成一个固定空间上的幂。

量子卷§72.1、§72.3的完整轮次模型已经承担自适应误差传播：若控制器相同且每一步先将历史去相干，输入在历史寄存器上为块对角，则统一的逐历史分支界可经块权重求和用于整步。若控制器不同，其差异进入对应轮次缺陷；若历史相干，逐经典分支最大值不是完整通道界。这里的受限族定义不赋予未声明的复制或记录访问权限。

**命题 12.5（受限证书的传播及失效见证）。** 在定义12.4的受限族条件下，若 $\kappa,\varepsilon_j$ 是相应受限态上的统一预算，则对每个允许参考 $R$ 及 $\rho_{XR}\in\mathscr A_0$，
$$
\frac12\left\|\bigl[(\mathcal S\overline{\mathcal T}_n\cdots\overline{\mathcal T}_1\mathcal E-\mathcal Q\mathcal T_n\cdots\mathcal T_1)\otimes\operatorname{id}_R\bigr](\rho_{XR})\right\|_1
\le\min\{1,\kappa+\textstyle\sum_j\varepsilon_j\}.
$$
该式按定义12.1写成固定类型；逐轮采用式（12.3a）的类型和相应受限输入族时，同一证明给变类型版本。这只是受限态保证，不断言全空间 diamond 缺陷同样小。如果缺少沿理想前缀的不变范围，结论不成立。对成功条件化的实验，未经归一化的通道误差也不直接给同值的条件误差。

**证明。** 对给定联合态使用式（12.4）；第 $j$ 项右侧的理想前缀将它送入 $\mathscr A_{j-1}$，故该项可使用受限缺陷。左侧的其余通道仍收缩迹距离；末端恢复项使用 $\mathscr A_n$ 上的界。求和得结论。

为说明范围必要性，取经典两态 $X=\{0,1\}$，边界为单点，$\mathcal E$ 擦除，$\mathcal R$ 总制备零，$\mathcal T$ 交换两态，边界更新恒等。初态族仅为零态；其恢复缺陷为零，编码交织缺陷处处为零。然而一步后理想态为一、恢复态为零，总变差为一。原因是末端已经离开恢复有效域。

条件化方面，设成功子态为 $A,B\succeq0$，$p=\operatorname{Tr}A>0,q=\operatorname{Tr}B>0$，且 $\|A-B\|_1\le e$。由 $|p-q|\le e$，
$$
\left\|\frac A p-\frac B q\right\|_1
\le\frac{\|A-B\|_1}{p}+\frac{|p-q|}{p}
\le\frac{2e}{p}.
\tag{12.5}
$$
故成功概率的共同下界 $p,q\ge s>0$ 给条件态迹距离至多 $\min\{1,e/s\}$。下界不能删除：两个经典联合输出分别以概率 $s$ 成功并输出相反比特，以概率 $1-s$ 给同一失败标签；完整输出总变差为 $s\to0$，成功条件分布的总变差却恒为一。失败旗标保留时仍可使用原通道界。$\square$

**定理 12.6（连续时间的交织缺陷）。** 在有限维空间中，设 $\mathcal T_t=e^{t\mathcal L}$、$\overline{\mathcal T}_t=e^{t\overline{\mathcal L}}$ 对全部 $t\ge0$ 均为通道。定义
$$
\mathcal K=\mathcal E\mathcal L-\overline{\mathcal L}\mathcal E,
\qquad \delta=\tfrac12\|\mathcal K\|_\diamond.
\tag{12.6}
$$
则
$$
\mathcal E\mathcal T_t-\overline{\mathcal T}_t\mathcal E
=\int_0^t\overline{\mathcal T}_{t-s}\mathcal K\mathcal T_s\,ds,
\tag{12.7}
$$
$$
d_\diamond(\mathcal E\mathcal T_t,\overline{\mathcal T}_t\mathcal E)
\le\min\{1,t\delta\},\qquad
d_\diamond(\mathcal S\overline{\mathcal T}_t\mathcal E,
\mathcal Q\mathcal T_t)\le\min\{1,\kappa+t\delta\}.
\tag{12.8}
$$
更一般地，连续时变生成元具有通道传播子 $\mathcal T(t,s)$、$\overline{\mathcal T}(t,s)$，且固定 $\mathcal E$ 满足 $\mathcal K(s)=\mathcal E\mathcal L(s)-\overline{\mathcal L}(s)\mathcal E$，则上述 $t\delta$ 替换为 $\int_{t_0}^{t_1}\tfrac12\|\mathcal K(s)\|_\diamond ds$。

**证明。** 对 $F(s)=e^{(t-s)\overline{\mathcal L}}\mathcal E e^{s\mathcal L}$ 求导，有限维乘积法则给 $F'(s)=\overline{\mathcal T}_{t-s}\mathcal K\mathcal T_s$。积分后两端分别为 $\mathcal E\mathcal T_t$ 与 $\overline{\mathcal T}_t\mathcal E$。范数积分不等式及通道范数一给首个界，插入 $\mathcal S\mathcal E\mathcal T_t$ 给恢复界。

时变情形对 $F(s)=\overline{\mathcal T}(t_1,s)\mathcal E\mathcal T(s,t_0)$ 使用传播子的前向、后向微分方程，得到相同积分恒等式。这里没有把非交换时变生成元的传播子替换成一般错误的 $e^{\int\mathcal L(s)ds}$。这是有限维变常数公式在交织缺陷上的应用；离散对应式已见[形式观察者卷](FORMAL_OBSERVER_COMPLETION_REFLECTION.md)定理17.1。$\square$

**定理 12.7（时间标记与费用测度的一致运输）。** 对定理12.6的时变过程，令 $t=f(\tau)$ 是区间上的 $C^1$ 严格递增换元，$f'(\tau)>0$。运输后的传播子为
$$
\mathcal T^f(\tau_1,\tau_0)
=\mathcal T(f(\tau_1),f(\tau_0)),
$$
边界传播子同理；相应生成元为 $\mathcal L^f(\tau)=f'(\tau)\mathcal L(f(\tau))$ 与 $\overline{\mathcal L}^f(\tau)=f'(\tau)\overline{\mathcal L}(f(\tau))$。于是
$$
\mathcal K^f(\tau)=f'(\tau)\mathcal K(f(\tau)),\qquad
\delta^f(\tau)=f'(\tau)\delta(f(\tau)),
\qquad
\int_{\tau_0}^{\tau_1}\delta^f(\tau)d\tau
=\int_{f(\tau_0)}^{f(\tau_1)}\delta(t)dt.
\tag{12.9}
$$
若某一非负费用坐标的累积量按 $\int c(t)dt+\sum_j b_j$ 定义，连续费率运输为 $c^f(\tau)=f'(\tau)c(f(\tau))$；时刻 $t_j$ 的点操作费用 $b_j$ 移至 $\tau_j=f^{-1}(t_j)$，其数值不变。相同区间的累计费用和累计缺陷均不变。这里每次实际记录的时刻 $t_j$ 仅重新标为 $f^{-1}(t_j)$，读数、条件化和控制协议保持同一物理实现；若改成在新钟上重新等步采样，通常改变了原物理样点，不能直接使用这条重参数化结论。

**证明。** 传播子的链式法则给生成元公式，固定 $\mathcal E$ 后交织缺陷同乘 $f'$。范数正齐次性给 $\delta^f$，积分换元给式（12.9）。连续费用用同一换元；有限点费用只是索引重排，故不乘 $f'$。可数可和的非负点费用也由单调极限得到同样结论。$\square$

**定义 12.8（允许的坐标运输及资源合同）。** 若 $F:X\to X'$、$G:B\to B'$、$H:A\to A'$ 是酉共轭通道，定义
$$
\mathcal E'=G\mathcal E F^{-1},\quad
\mathcal Q'=H\mathcal QF^{-1},\quad
\mathcal S'=H\mathcal SG^{-1},\quad
\mathcal T_j'=F\mathcal T_jF^{-1},\quad
\overline{\mathcal T}_j'=G\overline{\mathcal T}_jG^{-1}.
\tag{12.10}
$$
坐标运输本身不指称执行这些酉操作；若协议实际执行它们，执行费用另计。一个已准许路径的费用合同可以取任意有限维非负向量，逐坐标相加：编码、边界操作、解码分别有界为 $c_E,c_j,c_S$ 时，实现路径的费用不超过 $c_E+\sum_jc_j+c_S$。共同来源、同时取得的旁支、失败和复制许可仍按本卷第1、4、5、7节声明；误差上界不生成这些许可。

**命题 12.9（缺陷的合法运输与多层接口）。** 式（12.10）给
$$
\mathcal E'\mathcal T_j'-\overline{\mathcal T}_j'\mathcal E'
=G(\mathcal E\mathcal T_j-\overline{\mathcal T}_j\mathcal E)F^{-1},
\qquad
\mathcal S'\mathcal E'-\mathcal Q'=H(\mathcal S\mathcal E-\mathcal Q)F^{-1}.
\tag{12.11}
$$
所以 $\kappa,\varepsilon_j$ 保持不变。一般可逆线性变换仅给代数共轭恒等式，不保证通道合法性或范数保持。

若另外有第二层编码 $\mathcal E_2:B\to C$、解码 $\mathcal R_2:C\to B$ 和操作 $\widetilde{\mathcal T}_j$，令
$$
\kappa_2=d_\diamond(\mathcal R_2\mathcal E_2,\operatorname{id}_B),\qquad
\eta_j=d_\diamond(\mathcal E_2\overline{\mathcal T}_j,
\widetilde{\mathcal T}_j\mathcal E_2).
$$
复合编码 $\mathcal E_2\mathcal E$、解码 $\mathcal S\mathcal R_2$ 对同一目标 $\mathcal Q$ 的恢复缺陷至多 $\kappa+\kappa_2$，每步交织缺陷至多 $\varepsilon_j+\eta_j$。因此整段实验误差至多
$$
\min\{1,\kappa+\kappa_2+\textstyle\sum_j(\varepsilon_j+\eta_j)\}.
\tag{12.12}
$$

**证明。** 展开共轭并约去相邻逆映射得式（12.11）。酉通道及其逆均收缩 diamond 范数，两个方向的界给等号。第二层恢复差插入 $\mathcal S\mathcal E$；第二层交织差插入 $\mathcal E_2\overline{\mathcal T}_j\mathcal E$。三角不等式和通道收缩给两项缺陷预算，再应用定理12.2。这是本卷命题6.5在合法量子接口上的同一复合规则。$\square$

**定理 12.10（采样记忆接口接入稳定反馈的充分条件）。** 设 $U$ 为有限维实内积空间，$K,\widehat K:[0,\infty)\to\mathcal L(U)$ 可测且算子范数可积。令
$$
k=\int_0^\infty\|K(t)\|dt,\quad
\widehat k=\int_0^\infty\|\widehat K(t)\|dt,\quad
e_K=\int_0^\infty\|K(t)-\widehat K(t)\|dt.
$$
固定同一线性反馈 $A:U\to U$，$L=\|A\|$，并假设 $Lk<1,L\widehat k<1$。对有界可测 $f,\widehat f,g$，以下因果卷积方程在 $L^\infty([0,\infty);U)$ 中各有唯一解：
$$
x=f+K*(Ax+g),\qquad
\widehat x=\widehat f+\widehat K*(A\widehat x+g).
\tag{12.13}
$$
若 $\|f-\widehat f\|_\infty\le e_f$、$\|g\|_\infty\le G$，则
$$
\|x\|_\infty\le\frac{\|f\|_\infty+kG}{1-Lk},\qquad
\boxed{\|x-\widehat x\|_\infty
\le\frac{e_f+e_K(L\|x\|_\infty+G)}{1-L\widehat k}.}
\tag{12.14}
$$
恢复几何卷第11节的共同正谱隙模型给 $k\le m/a$、$\widehat k\le\widehat m/a$，其命题11.7给 $e_K\le\Phi_a(m+\widehat m,\varepsilon)$；第12节的积分误差比较的是两份前缀的规范模型；用于实际模型时，另须其命题12.6所列的实际—规范同一性或响应误差依据。例如实际—规范核的积分误差已有 $e_{\rm model}$ 上界时，可取 $e_K\le e_{\rm model}+2\sqrt R\,d_J/a+R d_A/a^2$，其中 Frobenius 界同时控制算子范数。满足这里的小增益条件后，这些边界采样证书便控制同一反馈中的完整响应。

**证明。** 令 $V_Kx=K*(Ax)$。积分三角不等式给 $\|V_K\|_{\infty\to\infty}\le kL<1$；因此 $\sum_{n\ge0}V_K^n$ 在算子范数中收敛，且为 $I-V_K$ 的逆。这是 Banach 空间上的 Neumann 级数。应用于 $f+K*g$ 得唯一性及第一个界；第二系统同理。

相减并使用同一个实际反馈 $A$，得
$$
\widehat x-x=(\widehat f-f)
+\widehat K*A(\widehat x-x)
+(\widehat K-K)*(Ax+g).
$$
取 $L^\infty$ 范数，把 $L\widehat k\|\widehat x-x\|_\infty$ 移到左边，得到式（12.14）。每个卷积及其幂均因果，级数极限也保留因果性。初态引起的外源项须归入 $f,\widehat f$ 并实际控制 $e_f$；核误差本身不给该控制。本结论针对式（12.13）及其小增益假设，不把核逼近自动提升为任意微分反馈方程的稳定性。$\square$

## 12.99 追加锚
