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

## 13. 完整已获记录、因果割与边界运输

**定义 13.1（共同实现上的完整已获记录）。** 固定非空有限集合 $\Omega$，以及任意指标集 $A$ 上的一族已取得记录 $R_\alpha:\Omega\to\mathcal R_\alpha$。指标包含来源身份；内在记录、外部档案及已经取得的关系读数，凡在这个协议中表示者均列入此族。定义
$$
\omega\sim_C\omega'
\iff \forall\alpha\in A,\ R_\alpha(\omega)=R_\alpha(\omega'),
\qquad C:\Omega\to\mathcal C:=\Omega/{\sim_C}.
\tag{13.1}
$$
$C$ 称为本协议的完整已获记录接口。有限性来自 $\Omega$，不要求 $A$ 有限，也不把实际观察者等同于有限身体或一份预选短表。这里的商表示记录已经具有的区分；其构造不附带免费取得记录、免费计算商标签或有效解码的假设。

此处的共同实现与完整记录约定接续本卷第9节“经典概率拼接、记忆增益与可组合恢复”的同律条件，第10节“量子条件互信息、共用恢复与参考系统”的共同来源量词，第11节“带记忆量子过程的表示、历史概率与可访问关系”的档案与策略，以及第12节“可组合恢复、连续缺陷与相对时钟”的有类型续接。以下采用有限经典、不扰动的读数协议；不由此给量子仪器的不同控制分支指定未经假设的共同反事实取值。

**命题 13.2（完整记录商的精确性）。** 每个 $R_\alpha$ 唯一因子化为 $h_\alpha C$，且
$$
\sigma(C)=\sigma(R_\alpha:\alpha\in A).
\tag{13.2}
$$
若摘要 $M=m(C)$ 还满足每个 $R_\alpha$ 均通过 $M$ 因子化，则 $C$ 也通过 $M$ 因子化。因此，在没有另证所需充分性的情况下，用更粗的任务摘要替换 $C$ 会改变条件化所保留的信息。

**证明。** $R_\alpha$ 在每个 $C$ 类上常值，故在实际像上定义 $h_\alpha([\omega])=R_\alpha(\omega)$，良定义且唯一。这给 $\sigma(R_\alpha:\alpha\in A)\subseteq\sigma(C)$。固定 $\omega$；对每个不在其类中的 $\omega'$，选择一个区分二者的指标 $\alpha_{\omega'}$。这样的 $\omega'$ 只有有限个，相应等值事件的交恰为 $[\omega]$。无类外点时这个交为 $\Omega$。每个类均属于右侧的 $\sigma$ 代数，故反向包含成立。最后，若 $M(\omega)=M(\omega')$，全部 $R_\alpha$ 相同，所以 $C(\omega)=C(\omega')$；按 $M$ 的非空纤维定义因子即得结论。$\square$

**定义 13.3（固定读数协议的合法割）。** 给有限偏序集 $(E,\le)$；$e\in E$ 是带来源身份的事件，具有读数 $X_e:\Omega\to\mathcal X_e$。同一 $\omega$ 同时规定全部这些读数，允许的取得动作不改变它们。记 $\mathcal J(E)$ 为序理想全体：$I\subseteq E$ 属于 $\mathcal J(E)$，意为 $e\in I,d\le e$ 蕴含 $d\in I$。称其为合法割，并定义
$$
q_I(\omega)=\bigl(C(\omega),(X_e(\omega))_{e\in I}\bigr),
\qquad B_I=q_I[\Omega].
\tag{13.3}
$$
乘积按事件索引，不按书写次序索引。事件 $e$ 在 $I$ 启用，意为 $e\notin I$ 且每个 $d<e$ 已在 $I$；写 $I+e=I\cup\{e\}$。两个不同事件同时启用时必不可比。此偏序只规定动作先后是否合法；它不规定读数的概率独立性。若实际动作会扰动后续读数，须另给包含该动作及实际结果的实现与历史；这里固定读数的假设本身不提供这种模型。把运动作为动作时，同样须指定它改变哪些合法取得映射、实际结果或扰动关系。

**定理 13.4（保留前缀、取得关系与确定性细化障碍）。** 对合法割 $I\subseteq J$，存在唯一满射 $r_{JI}:B_J\to B_I$ 使 $r_{JI}q_J=q_I$。对 $I\subseteq J\subseteq K$，
$$
r_{II}=\operatorname{id}_{B_I},\qquad
r_{KI}=r_{JI}r_{KJ},\qquad
\ker q_J\subseteq\ker q_I.
\tag{13.4}
$$
从旧记录到新记录的实际取得关系为
$$
\mathcal R_{IJ}:=\{(q_I\omega,q_J\omega):\omega\in\Omega\}
=\{(b,d)\in B_I\times B_J:b=r_{JI}(d)\}.
\tag{13.5}
$$
按先 $\mathcal R_{IJ}$ 后 $\mathcal R_{JK}$ 的关系复合约定，有 $\mathcal R_{JK}\circ\mathcal R_{IJ}=\mathcal R_{IK}$。存在全定义确定性映射 $u:B_I\to B_J$ 满足 $q_J=uq_I$，当且仅当 $\ker q_I\subseteq\ker q_J$；在保留式记录下，这恰为两核相等。因而只以旧记录为输入的确定性更新不能严格细化实际信息。

**证明。** $r_{JI}$ 删除不属于 $I$ 的事件坐标，保留 $C$。任取 $b=q_I\omega$，$q_J\omega$ 是其原像，故满射；$q_J$ 满射到实际像又给唯一性。重复删除给复合式；若 $q_J$ 相等，其前缀相等，故核包含成立。

式（13.5）的左侧必满足右侧等式。反之，对 $d\in B_J$ 取 $\omega$ 使 $q_J\omega=d$，则 $q_I\omega=r_{JI}(d)=b$。复合关系中的中间项必为 $r_{KJ}(d)$，所以其存在恰要求 $b=r_{JI}r_{KJ}(d)=r_{KI}(d)$，得精确复合。这里使用了同一份 $\Omega$、实际像和嵌套前缀。

若 $q_J=uq_I$，旧记录相等必给新记录相等。反之，所述核包含使 $u(q_I\omega):=q_J\omega$ 与代表无关；它定义在整个 $B_I$。结合已经证明的反向包含即得等核判据。$\square$

**命题 13.5（策略、实际结果与保留读数）。** 设当前完整历史 $H$ 保留 $C$、已取得的带来源读数及任务所需的动作信息。确定性策略取 $a=\pi(H)$，取得动作产生实际结果 $Y$ 后，保留式更新为
$$
H'=(H,a,Y).
\tag{13.6}
$$
若存在同一旧历史而不同 $Y$ 的两个合法实现，则 $H'$ 不能是仅以 $H$ 为输入的确定性函数。另一方面，对 $I\subseteq J$，每个旧读数 $f=h(q_I)$ 都满足
$$
f=(h\circ r_{JI})(q_J).
\tag{13.7}
$$

**证明。** 相同 $H$ 给相同 $a$，不同 $Y$ 给不同有序三元组，违反函数的单值性。若规定 $Y=g(H,a)$，得到的只是这个规则规定的值；它与实际取得结果相等还须在全部合法实现上验证。若结果随机，须给包含旧记录及来源的联合律；结果核来自该律在正概率历史上的条件分布。随机策略所用的随机记录亦须按其实际可访问性纳入历史。式（13.7）由 $r_{JI}q_J=q_I$ 代入得到；它保持已经取得的函数值，不断言微观状态不变。$\square$

**引理 13.6（合法枚举的相邻交换连通性）。** 对有限偏序集的两个合法割 $I\subseteq J$，从 $I$ 到 $J$ 每次加入一个启用事件的路径，恰对应诱导偏序 $J\setminus I$ 的线性扩张。任意两条这样的路径可由有限次相邻不可比事件交换连接，每次交换仍给合法路径。

**证明。** 路径必须把每个前驱先于其后继加入，故给线性扩张。反之，按线性扩张添加元素时，新元素在 $J$ 内的前驱或已在 $I$，或位于扩张中更早的位置；$J$ 为理想保证它没有位于 $J$ 外的前驱，故每步合法。有限非空偏序必有极小元，否则不断取严格更小元会在有限集内造成严格序循环；逐次取出极小元，便给至少一条线性扩张。

取目标扩张的首项 $a$。在另一扩张中，位于 $a$ 之前而需要被它越过的任何 $b$ 都与 $a$ 不可比：若 $b<a$，目标不能以 $a$ 开头；若 $a<b$，另一扩张不能以 $b$ 先于 $a$。逐次向左交换使 $a$ 到达首位，每次只交换不可比相邻项，仍是线性扩张。固定共同首项，在剩余有限偏序上归纳；空集终止。对于路径的每次局部交换，这两个事件在共同前缀后均已启用，因此交换对应一个合法方块。$\square$

**定义 13.7（一般因果割上的指定边界）。** 在同一有限偏序 $E$ 上，对每个 $I\in\mathcal J(E)$ 给集合 $\mathsf X_I$、$\mathsf B_I$ 及满射 $\beta_I:\mathsf X_I\twoheadrightarrow\mathsf B_I$；对每个在 $I$ 启用的 $e$ 给全定义合法映射
$$
U_{I,e}:\mathsf X_I\to\mathsf X_{I+e}.
\tag{13.8}
$$
这些集合不必是定义13.3的实际读数空间。指定边界任务形如 $h_I\beta_I$；某个后续操作可在边界执行，意为它在对应边界纤维上具有一致结果。这是[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第120节“可组合关系的最小行为表示与保真辅助构造”中任务商的有限割型情形；表示及后续操作的共同运输采用其第133节“共同实现、概率与演化的同步运输”、第134节“关系表示的探针充分性与三种闭合”的类型约定。

**定理 13.8（边下降与可观察方块的充要性）。** 定义13.7的数据具有唯一的边界映射族 $\overline U_{IJ}:\mathsf B_I\to\mathsf B_J$，使每条边下降、每条合法路径的诱导复合只依赖端点，并满足
$$
\overline U_{II}=\operatorname{id}_{\mathsf B_I},\qquad
\overline U_{IK}=\overline U_{JK}\overline U_{IJ}
\quad(I\subseteq J\subseteq K),
\tag{13.9}
$$
当且仅当以下两项成立。第一，每条边保边界纤维：
$$
\beta_I(x)=\beta_I(x')
\Longrightarrow
\beta_{I+e}(U_{I,e}x)=\beta_{I+e}(U_{I,e}x').
\tag{13.10}
$$
第二，每个合法割 $I$ 及每对不同的同时启用事件 $e,f$ 满足可观察方块等式：
$$
\beta_{I+e+f}U_{I+e,f}U_{I,e}
=
\beta_{I+e+f}U_{I+f,e}U_{I,f}
\quad\text{作为 }\mathsf X_I\to\mathsf B_{I+e+f}\text{ 的映射}.
\tag{13.11}
$$
此结论只运输已指定的边界任务及能够通过边界下降的后续操作。

**证明。** 在式（13.10）下定义
$$
\overline U_{I,I+e}(\beta_Ix):=\beta_{I+e}(U_{I,e}x).
$$
纤维一致性给良定义，满射性给全定义及唯一性。将两条边下降式接续，再用式（13.11），得到两条边界方块复合在每个 $\beta_Ix$ 上相同；满射性使两映射在全部 $\mathsf B_I$ 上相同。

任取从 $I$ 到 $J$ 的两路径。引理13.6把它们连接为相邻方块交换。交换前缀不变，方块在边界上的输出相同，交换后的任意共同后缀由边界映射继续作用，输出仍相同。等价地，在完整状态上，方块两条路产生的状态只需具有相同 $\beta$ 值；式（13.10）逐步把这种相等沿后缀传播，不要求完整状态相等。因此全部路径诱导同一 $\overline U_{IJ}$。空路径给恒等；将两段路径连接给式（13.9）。任何满足要求的族在边上已唯一，在路径复合上也唯一。

反之，边界边映射存在立即给式（13.10）。两条合法二步路径具有同端点，路径无关给边界方块相等，再与 $\beta_I$ 复合得式（13.11）。对任务 $h_J\beta_J$，末端取 $h_J$ 即得任务值不变；后续操作只有满足相应下降条件才能沿同一论证接续。一般原状态读数未必因子化，故不在此量词内。特别地，本定理的确定性运输不生成新取得结果；若把边界解释为保留式实际记录，还必须满足定理13.4的等核障碍，或另把实际结果作为输入。$\square$

**命题 13.9（完整更新不交换而指定边界方块交换）。** 取二元反链 $E=\{e,f\}$，对每个割令 $\mathsf X_I=\{0,1\}^2$、$\mathsf B_I=\{0,1\}$，$\beta_I(b,z)=b$。事件 $e$ 的每条边执行 $(b,z)\mapsto(b,1-z)$，事件 $f$ 的每条边执行 $(b,z)\mapsto(b,0)$。全部边下降且可观察方块交换，但完整更新方块不交换。

**证明。** 两类操作都保留第一坐标，所以每条边的边界映射为恒等，式（13.10）及（13.11）成立。先 $e$ 后 $f$ 的第二坐标为 $0$，先 $f$ 后 $e$ 的第二坐标为 $1$，故完整状态不同。$\square$

**命题 13.10（来源索引档案与时间顺序档案）。** 在定义13.3下，同一合法割 $I$ 的任何合法枚举都给相同 $q_I$。若 $I$ 含有两个不可比事件且任务还要求时间顺序档案
$$
A_\ell(\omega)=\bigl(C(\omega),((e_1,X_{e_1}(\omega)),\ldots,(e_m,X_{e_m}(\omega)))\bigr),
\tag{13.12}
$$
其中 $\ell=(e_1,\ldots,e_m)$ 是所用枚举，则存在两个合法枚举，在同一 $\omega$ 上给出相同 $q_I(\omega)$ 而不同的 $A_\ell(\omega)$。

**证明。** $q_I$ 的 $e$ 坐标始终为同一个 $X_e(\omega)$，枚举不改变事件身份或值。在 $I$ 中取不可比的 $e,f$。在 $I$ 的严格偏序中分别加入 $e<f$ 或 $f<e$ 并取传递闭包；若前者产生环，原偏序必已有从 $f$ 到 $e$ 的路径，后者同理，均与不可比性矛盾。因此两者仍为有限偏序，各自逐次选取剩余极小元得到线性扩张，给出 $I$ 的两个合法枚举，分别使 $e$ 先于 $f$ 和 $f$ 先于 $e$。固定同一来源点 $\omega$，二者给出相同的 $q_I(\omega)$，而式（13.12）的事件标签顺序不同，即使读数值相同，序列仍不同。因此来源索引档案满足的交换等式不能自动用于需要时间顺序的任务；保留该任务时，档案须包含枚举。$\square$

**命题 13.11（共同来源的纤维交与成对盲区）。** 对任意有限族合法割 $I_t$ 与候选记录 $b_t\in B_{I_t}$，它们有同一实际实现，当且仅当
$$
\bigcap_t q_{I_t}^{-1}(\{b_t\})\ne\varnothing.
\tag{13.13}
$$
即使各对候选都有共同实现，也不保证式（13.13）。

**证明。** 交集的元素恰为同时产生全部记录的 $\omega$。取 $\Omega=\{0,1\}^2$，$C$ 常值，三个事件为反链，读数为 $a,b,a\mathbin\oplus b$。任意两读数的联合映射都满射到 $\{0,1\}^2$：给 $a$ 与 $a\oplus b$ 可唯一解出 $b$，其余两种情形同理。但候选三元组 $(0,0,1)$ 无实现，因 $0\oplus0=0$。其三个指定单坐标纤维两两相交而共同交为空。这是[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第124节“共同来源的拼接、补全与归一化”中实际像限制的有限例；定理13.4的嵌套复合不授权跨不相关实现拼接。$\square$

**定义 13.12（局部事件费用与端点钟）。** 对每条启用边给 $c(I,e)\in[0,\infty)$。路径费用是其边费用之和。端点钟是函数 $\tau:\mathcal J(E)\to\mathbb R$，满足 $\tau(\varnothing)=0$ 及
$$
\tau(I+e)-\tau(I)=c(I,e).
\tag{13.14}
$$
也允许固定有限维非负向量费用，等式逐坐标解释。这些钟计量指定事件费用；未指定任何衰减、波动或场方程。

**定理 13.13（费用方块与端点势）。** 定义13.12的端点钟存在且唯一，当且仅当每对不同同时启用事件满足
$$
c(I,e)+c(I+e,f)=c(I,f)+c(I+f,e).
\tag{13.15}
$$
此时任意 $I\subseteq J$ 的合法路径费用均为 $\tau(J)-\tau(I)$，且 $\tau$ 随割包含单调。向量费用的结论逐坐标成立。

**证明。** 若端点钟存在，两条二步路径的增量均望远镜求和为 $\tau(I+e+f)-\tau(I)$，故式（13.15）必要。反之，从空割沿任意合法路径到 $I$，以其费用和定义 $\tau(I)$。引理13.6给路径间的相邻交换连通性；每次交换由式（13.15）保持和，故定义无关路径。延长一条路径便得式（13.14）。任意候选钟沿该路径求和得到同一值，所以唯一。任意 $I$ 到 $J$ 的路径上再望远镜求和得端点差；非负费用给单调性。有限向量的每个坐标独立适用同一证明。$\square$

**命题 13.14（共同约束下的多个事件钟与标量次序）。** 对事件子集 $L_1,\ldots,L_m\subseteq E$，令 $\tau_j(I)=|I\cap L_j|$。它们同时满足定理13.13，边增量为 $\mathbf1_{e\in L_j}$，不必彼此相等。有限偏序总有严格保先后次序的标量时间戳；但若有不可比元素，则不存在实值 $t$ 满足
$$
e\le f\iff t(e)\le t(f)\quad\text{对全部 }e,f\in E.
\tag{13.16}
$$
这不排除标量对有限数据的单射编码。

**证明。** 加入 $e$ 时计数增量就是所给指标，交换两次加入的总增量相同。例如二元反链取 $L_1=\{e\},L_2=\{f\}$，四个割的钟向量为 $(0,0),(1,0),(0,1),(1,1)$，两只钟同属一份割结构。逐次选剩余偏序的极小元得到线性扩张；以位置为时间戳，$e<f$ 蕴含 $t(e)<t(f)$。若 $e,f$ 不可比，实数全序仍使 $t(e)\le t(f)$ 或 $t(f)\le t(e)$，反映次序将错误地强迫一次比较，故式（13.16）不可能。上述四个割也可用 $\mathbf1_{e\in I}+2\mathbf1_{f\in I}$ 编为 $0,1,2,3$ 并唯一解码；这个单射并不反映割包含的偏序。$\square$

**命题 13.15（相同事件计数不保证更新方块）。** 在 $\{0,1\}$ 上令 $A(x)=1-x$、$B(x)=0$，并允许两个事件以任一次序各执行一次。两条路径的事件计数及单位总费用相同，末端读数却不同。

**证明。** $B(A(x))=0$ 而 $A(B(x))=1$。两条路径均各计一次 $A$、一次 $B$，总费用均为 $2$。因此费用方块可以成立而状态或指定输出的方块失败；时钟值不能替代定理13.8的可观察方块条件。$\square$

## 14. 给定完整记录的交互分解与合法显露几何

**定义 14.1（同律条件投影与隐藏余项）。** 在定义13.1、13.3的同一个有限 $\Omega$ 上固定概率律 $\mu$。以下实 Hilbert 空间为 $\mathcal H=L^2(\Omega,\mu;\mathbb R)$，把零概率点上的差别识别；算子恒等及函数恢复均按此约定解释。对任意 Boolean 子集 $S\subseteq E$，定义
$$
\mathcal F_S=\sigma(C,X_e:e\in S),\qquad
P_Sf=\mathbb E_\mu[f\mid\mathcal F_S],\qquad
P_\varnothing=P_C,\qquad Q=\operatorname{Id}_{\mathcal H}-P_E.
\tag{14.1}
$$
这里 $C$ 始终是全部已表示旧记录的商；$P_C$ 不一般是常数投影。$P_S$ 是到 $\mathcal F_S$ 可测函数空间的正交投影。具体地，在正概率记录纤维 $F$ 上，$P_S f$ 等于 $\sum_{\omega\in F}\mu(\omega)f(\omega)/\mu(F)$；逐纤维求和显示 $f-P_Sf$ 与所有纤维常值函数正交，从而给该投影刻画。$S$ 不为理想时，$P_S$ 仅是用于分解的数学辅助算子，不宣告这些事件可单独合法取得。$Q$ 保留全部具名记录仍未观察到的方向。

对 $f\in\mathcal H$，定义积分均方风险
$$
\mathscr R_I(f)=\|f-P_If\|_2^2
=\sum_{\omega\in\Omega}\mu(\omega)|f(\omega)-P_If(\omega)|^2
\quad(I\in\mathcal J(E)).
\tag{14.2}
$$
它对全部实现积分，不是某次实际记录取值上的条件方差。固定这份 $\mu$ 是风险比较的共同前提。

**定理 14.2（任意依赖下的 Boolean 反演）。** 定义自伴算子
$$
D_S=\sum_{T\subseteq S}(-1)^{|S|-|T|}P_T,
\qquad D_\varnothing=P_C.
\tag{14.3}
$$
无需任何独立性，就有
$$
P_A=\sum_{S\subseteq A}D_S\quad(A\subseteq E),\qquad
\operatorname{Id}_{\mathcal H}=Q+\sum_{S\subseteq E}D_S.
\tag{14.4}
$$
在任意依赖下，这只是算子加法恒等式，不断言各 $D_S$ 是正交投影。

**证明。** 将式（14.3）代入第一式的右侧，$P_T$ 的系数为
$$
\sum_{T\subseteq S\subseteq A}(-1)^{|S|-|T|}
=(1-1)^{|A\setminus T|},
$$
它在 $T=A$ 时为 $1$，其余为 $0$。再用 $Q=\operatorname{Id}-P_E$ 得第二式。自伴性来自各 $P_T$ 自伴及系数实值。这是 Boolean 格的 Möbius 反演；在乘积测度的函数 ANOVA 中，同一反演见 Art B. Owen，*Monte Carlo theory, methods and examples*，附录 [The ANOVA decomposition of $[0,1]^d$](https://artowen.su.domains/mc/A-anova.pdf)，§A.4，式（A.11）—（A.12）。$\square$

**命题 14.3（合法观察塔的正交增量）。** 对嵌套合法割
$\varnothing=I_0\subseteq I_1\subseteq\cdots\subseteq I_m$，令 $\Delta_k=P_{I_k}-P_{I_{k-1}}$。即使读数相依，各 $\Delta_k$ 仍是两两正交的自伴投影，与 $P_C$ 正交，且
$$
\Delta_k=\sum_{\substack{S\subseteq I_k\\S\nsubseteq I_{k-1}}}D_S,
\qquad
f=P_Cf+\sum_{k=1}^m\Delta_kf+(\operatorname{Id}-P_{I_m})f.
\tag{14.5}
$$
对任意合法割 $I\subseteq J$，
$$
\mathscr R_I(f)-\mathscr R_J(f)=\|(P_J-P_I)f\|_2^2\ge0.
\tag{14.6}
$$

**证明。** $\mathcal F_I\subseteq\mathcal F_J$ 给嵌套可测子空间，故 $P_JP_I=P_I$；取伴随得 $P_IP_J=P_I$。于是 $(P_J-P_I)^2=P_J-P_I$，且它自伴。对 $k<\ell$ 展开 $\Delta_k\Delta_\ell$，四项按较小下标投影分别抵消为零；同样有 $P_C\Delta_k=0$。式（14.5）第一式从式（14.4）相减，第二式望远镜求和。最后
$$
f-P_If=(f-P_Jf)+(P_J-P_I)f
$$
的两项正交，因为第一项正交于全部 $\mathcal F_J$ 可测函数，第二项属于该空间。取范数平方即得式（14.6）。这正是[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第121节“保留式观察的正交增量与记录时间”中§121.4—121.6的观察塔公式，所增加的等式是它与式（14.3）的连接。$\square$

**假设 14.4（相对于完整旧记录的联合条件独立）。** 对每个 $\mu(C=c)>0$ 的类及每个取值元组，要求
$$
\mu(X_E=x_E\mid C=c)
=\prod_{e\in E}p_e(x_e\mid c),\qquad
p_e(x_e\mid c):=\mu(X_e=x_e\mid C=c).
\tag{14.7}
$$
这是全部 $X_e$ 给定 $C$ 后的相互独立，既不以两两独立代替，也不以无条件独立代替。$\Omega$ 可另含未被 $(C,X_E)$ 决定的变量；式（14.7）不假定 $P_E=\operatorname{Id}$。零概率 $C$ 类与乘积权重为零的元组不承担条件等式。

**定理 14.5（逐旧记录纤维的条件 ANOVA）。** 在假设14.4下，对任意 $S,T,A\subseteq E$，
$$
P_SP_T=P_{S\cap T},\qquad
P_AD_S=
\begin{cases}
D_S,&S\subseteq A,\\
0,&S\nsubseteq A.
\end{cases}
\tag{14.8}
$$
全部 $D_S$ 是两两正交的自伴投影，并且 $QD_S=D_SQ=0$。因此
$$
\mathcal H=\operatorname{ran}Q\ \oplus\bigoplus_{S\subseteq E}\operatorname{ran}D_S,
\qquad
\|f\|_2^2=\|Qf\|_2^2+\sum_{S\subseteq E}\|D_Sf\|_2^2.
\tag{14.9}
$$
这是标准 Hoeffding／函数 ANOVA 在固定旧记录纤维上的有限乘积形式。非条件乘积分解及正交性见 Owen 所引附录§A.2—A.3，尤其引理A.3—A.4；[QUANTUM-RH 卷](QUANTUM-RH.md)题为“三十一、把 $5040$ 的 $(4,2,1,1)$ 从‘指数向量’提升为真正的交互几何”的一节也使用其有限寄存器形式。这里保留变化的条件权重、完整 $C$ 与 $Q$。

**证明。** 任取 $f\in\mathcal H$，先令 $g=P_Ef$。由嵌套塔式关系，对所有 $S$ 有 $P_Sf=P_Sg$，所以隐藏变量先通过 $g$ 的全记录条件平均进入计算。固定正概率 $c$，把 $g$ 写成全记录上的函数 $g(c,x_E)$。式（14.7）使正概率记录支撑恰为各正条件边缘支撑的乘积；在该支撑上
$$
(P_Sg)(c,x_S)
=\sum_{z_{E\setminus S}}g(c,x_S,z_{E\setminus S})
\prod_{e\notin S}p_e(z_e\mid c).
\tag{14.10}
$$
分母中固定坐标的正权重约去即得此式；零权重项可以删去。

令 $A_0=S\cap T$、$B_0=S\setminus T$、$D_0=T\setminus S$、$F_0=E\setminus(S\cup T)$。先取 $P_Tg$，式（14.10）对 $B_0,F_0$ 求积权平均，结果只依赖 $A_0,D_0$。再取 $P_S$，对 $D_0$ 求平均，已经不出现的 $F_0$ 的权重和为一，已经在第一步消去的 $B_0$ 不会重新出现。合并有限求和恰对 $B_0,D_0,F_0$ 全部求平均，所得是 $P_{A_0}g$。各正概率 $c$ 都成立，故 $P_SP_Tf=P_{S\cap T}f$ 在 $\mathcal H$ 成立。

将这一等式代入 $P_AD_S$。若 $S\subseteq A$，每个 $T\subseteq S$ 有 $A\cap T=T$，故得 $D_S$。否则选 $e\in S\setminus A$，在式（14.3）中将不含 $e$ 的 $T$ 与 $T\cup\{e\}$ 配对；二者交 $A$ 后相同而符号相反，所以和为零。

为证明投影性，对每个 $S$ 有算子乘积表示
$$
D_S=P_S\prod_{e\in S}\bigl(\operatorname{Id}-P_{E\setminus\{e\}}\bigr).
\tag{14.11}
$$
展开右侧，对选择的 $R\subseteq S$ 使用已经证明的交集乘法律，得到 $(-1)^{|R|}P_{S\setminus R}$，总和即式（14.3）；$S=\varnothing$ 时为空乘积。右侧各因子均为互相交换的自伴投影，所以乘积自伴且平方等于自身。

若 $S\ne T$，交换二者名称后可取 $e\in S\setminus T$。由式（14.8），$P_TD_S=0$，而 $D_T=P_TD_T=D_TP_T$，故 $D_TD_S=0$；取伴随得反向复合也为零。又 $P_ED_S=D_S$，故与 $Q$ 正交。式（14.4）已给这些投影之和为恒等，因而得到直和；分量的存在来自该算子恒等式，唯一性与范数公式来自正交性。$\square$

**定义 14.6（按因果下闭包分组的交互算子）。** 对 $S\subseteq E$ 定义
$$
\downarrow S=\{d\in E:\exists e\in S,\ d\le e\},\qquad
K_J=\sum_{\substack{S\subseteq E\\\downarrow S=J}}D_S
\quad(J\in\mathcal J(E)).
\tag{14.12}
$$
$K_J$ 按包含索引集 $S$ 所需的最小合法割 $J=\downarrow S$ 对 Boolean 交互分组；$K_\varnothing=D_\varnothing=P_C$。记 $\operatorname{Max}(J)$ 为 $J$ 的极大元集合，$\operatorname{Max}(\varnothing)=\varnothing$。

**定理 14.7（合法割上的反演与增量）。** 在任意联合律下，
$$
P_I=\sum_{\substack{J\in\mathcal J(E)\\J\subseteq I}}K_J,
\qquad
K_J=\sum_{R\subseteq\operatorname{Max}(J)}(-1)^{|R|}P_{J\setminus R}.
\tag{14.13}
$$
后式的每个 $J\setminus R$ 都是合法割。对合法 $I\subseteq I'$，
$$
P_{I'}-P_I
=\sum_{\substack{J\in\mathcal J(E)\\J\subseteq I',\ J\nsubseteq I}}K_J.
\tag{14.14}
$$
在假设14.4下，各 $K_J$ 是两两正交的自伴投影，$P_E=\sum_JK_J$；它们与 $Q$ 正交。

**证明。** 因 $I$ 为理想，$S\subseteq I$ 当且仅当 $\downarrow S\subseteq I$。按此下闭包分组式（14.4），得到第一式；相减得到式（14.14）。

从理想中只删除极大元仍为理想：若 $x\in J\setminus R$ 且 $y\le x$，则 $y\in J$；若 $y\in R$，其极大性迫使 $y=x$，与 $x\notin R$ 矛盾。把式（14.4）代入式（14.13）第二式的右侧，某个 $D_S$ 在 $S\subseteq J$ 时的系数为
$$
\sum_{R\subseteq\operatorname{Max}(J)\setminus S}(-1)^{|R|},
$$
否则为零。该和恰在 $\operatorname{Max}(J)\subseteq S\subseteq J$ 时为 $1$。有限理想的每个元素都在某个极大元之下，故这一条件蕴含 $\downarrow S=J$。反之，若 $\downarrow S=J$，任意极大元 $m$ 必满足 $m\le s$ 对某个 $s\in S\subseteq J$ 成立，极大性给 $s=m$，所以全部极大元属于 $S$。系数恰选出定义14.6中的项，证明所需公式。

在条件乘积假设下，定理14.5的正交投影被分成互不相交的有限组；每组之和仍自伴幂等，不同组乘积为零，且每项都与 $Q$ 正交。第二式是这个序理想格的具体反演公式，其符号只沿被删除的极大元子集使用，不能换成对所有子理想一律赋 $(-1)^{|J|-|I|}$。$\square$

**命题 14.8（反链、链与分支割的具体分组）。** 若 $E$ 为反链，则 $K_J=D_J$。若 $E=\{e_1<\cdots<e_n\}$ 为链，令 $I_k=\{e_1,\ldots,e_k\}$，则
$$
K_{I_k}=P_{I_k}-P_{I_{k-1}}\quad(1\le k\le n).
\tag{14.15}
$$
链中的这些 $K$ 在任意依赖下已是正交投影。若 $E=\{a,b,c\}$，仅有 $a<b,a<c$，则非空合法割为 $a,ab,ac,abc$，下标用连写表示子集，有
$$
\begin{aligned}
K_a&=D_a,\qquad K_{ab}=D_b+D_{ab}=P_{ab}-P_a,\\
K_{ac}&=D_c+D_{ac}=P_{ac}-P_a,\\
K_{abc}&=D_{bc}+D_{abc}=P_{abc}-P_{ab}-P_{ac}+P_a.
\end{aligned}
\tag{14.16}
$$

**证明。** 反链的每个子集等于自身的下闭包，故分组不改变单项。链的非空理想只有一个极大元 $e_k$，式（14.13）只有保留和删除它两项，给式（14.15）；命题14.3给正交性而不需要条件独立。分支偏序的下闭包分别把 $\{b\},\{a,b\}$ 并为 $ab$，把 $\{c\},\{a,c\}$ 并为 $ac$，把 $\{b,c\},\{a,b,c\}$ 并为 $abc$，其余项不变。顶割的极大元为 $b,c$，删除它们的四种方式给式（14.16）最后一个等式。对于一般分支偏序，定理14.5的条件独立是使全部这些组正交的一项充分条件；链的结论不要求把这项充分条件当成必要条件。$\square$

**定理 14.9（目标恢复与含隐藏余项的积分风险）。** 在假设14.4下，对任意 $f\in\mathcal H$ 和合法割 $I$，以下三个条件等价：
$$
\begin{aligned}
f=P_If
&\iff \bigl[Qf=0\ \text{且}\ D_Sf=0\text{ 对每个 }S\nsubseteq I\bigr]\\
&\iff \bigl[Qf=0\ \text{且}\ K_Jf=0\text{ 对每个 }J\in\mathcal J(E),\ J\nsubseteq I\bigr].
\end{aligned}
\tag{14.17}
$$
它们也等价于存在 $h:B_I\to\mathbb R$ 使 $f=h(q_I)$ 在 $\mu$ 几乎处处成立。并且
$$
\mathscr R_I(f)
=\|Qf\|_2^2+\sum_{S\nsubseteq I}\|D_Sf\|_2^2
=\|Qf\|_2^2+\sum_{\substack{J\in\mathcal J(E)\\J\nsubseteq I}}\|K_Jf\|_2^2.
\tag{14.18}
$$
对 $I\subseteq I'$ 的风险下降为
$$
\mathscr R_I(f)-\mathscr R_{I'}(f)
=\sum_{\substack{S\subseteq I'\\S\nsubseteq I}}\|D_Sf\|_2^2
=\sum_{\substack{J\subseteq I',\ J\nsubseteq I\\J\in\mathcal J(E)}}\|K_Jf\|_2^2.
\tag{14.19}
$$

**证明。** 式（14.4）给
$$
f-P_If=Qf+\sum_{S\nsubseteq I}D_Sf.
$$
各项由定理14.5互相正交；同样按下闭包分组，定理14.7给 $Qf+\sum_{J\nsubseteq I}K_Jf$。两次取范数平方得到式（14.18），有限个非负平方和为零恰为每一项为零，所以得到式（14.17）。条件期望投影的像是 $\mathcal F_I$ 可测函数类；有限空间中，这等价于在各正概率 $q_I$ 纤维上几乎处处常值。以该值定义 $h$，在零概率纤维上任意扩展，便得因子化；反向由可测性立得。相减式（14.18）给式（14.19）。

若 $\mu$ 对 $\Omega$ 全支撑，几乎处处等式就是逐点等式。否则若要对全部 $\Omega$ 作逐点恢复，仍须另验集合意义上的 $q_I$ 纤维常值性。此处结论针对指定 $f$ 与指定律，不由目标风险给出内部参数稳定重建、任意维度实现的唯一性或物理空间度量。去掉假设14.4后仍保留命题14.3的嵌套风险恒等式，但本证明不再给按 $D_S$ 或一般 $K_J$ 分项的平方和。$\square$

**定理 14.10（合法次序决定显露时刻而不改变最终空间）。** 给 $E$ 的一个合法全枚举 $\ell=(e_1,\ldots,e_n)$，令 $I_k=\{e_1,\ldots,e_k\}$。对非空 $S\subseteq E$ 定义
$$
\rho_\ell(S)=\max\{k:e_k\in S\}.
\tag{14.20}
$$
它既是首次包含 $S$ 的割下标，也是首次包含 $\downarrow S$ 的割下标。任意联合律下有
$$
\Delta_k=P_{I_k}-P_{I_{k-1}}
=\sum_{\rho_\ell(S)=k}D_S
=\sum_{\substack{J\subseteq I_k,\ J\nsubseteq I_{k-1}\\J\in\mathcal J(E)}}K_J.
\tag{14.21}
$$
在假设14.4下，非零 $D_S$ 的空间在 $\rho_\ell(S)$ 之前与当前观察空间正交，在该时刻起被完全包含；且
$$
\sum_{k=1}^n\|\Delta_k f\|_2^2
=\|P_Ef-P_Cf\|_2^2
=\mathscr R_\varnothing(f)-\mathscr R_E(f)
=\sum_{\varnothing\ne S\subseteq E}\|D_Sf\|_2^2.
\tag{14.22}
$$
左边按取得时刻分配的各项可以随合法枚举变化，最终空间 $\operatorname{ran}P_E$ 和总风险下降不变。式（14.22）前三项的相等无需条件独立。

**证明。** $I_k$ 包含 $S$ 恰在其最后一个成员取得后；因 $I_k$ 为理想，包含 $S$ 与包含 $\downarrow S$ 等价。式（14.21）来自命题14.3及定理14.7。在条件乘积情形，式（14.8）给 $P_{I_k}D_S$ 在 $S\nsubseteq I_k$ 时为零，在 $S\subseteq I_k$ 时为 $D_S$，即所述正交及包含。式（14.22）前两个等号由命题14.3的正交增量与式（14.6）望远镜求和得到；最后一个等号由 $P_E-P_C=\sum_{S\ne\varnothing}D_S$ 的正交性得到。端点不依赖枚举，故总量不变。

这里每个枚举事先固定，比较中读数函数与概率律也固定。若下一事件由当前记录自适应选择，实际割及顺序成为随机历史的一部分；本式不提供未经相应历史条件化的自适应 ANOVA 公式。[QUANTUM-RH 卷](QUANTUM-RH.md)题为“三十五、现在把‘空间阶数’与‘离散时间’真正放到一张图里”的一节控制演化算子在交互阶数间的有限传播；其传播步数与这里固定读数的取得次序是不同索引。$\square$

**命题 14.11（相同最终任务的两种显露分配与联合读数）。** 取 $\Omega=\{-1,1\}^2$ 上均匀律，$u,v$ 为独立坐标，$C$ 常值，$E$ 为读 $u,v$ 的二元反链，$f=u+uv$。先读 $u$ 后读 $v$ 的两次增量平方范数为 $(1,1)$；反向为 $(0,2)$。此外，$uv$ 属于联合读数空间，却正交于两个单坐标读数空间之和。

**证明。** 四点上的 $1,u,v,uv$ 构成正交归一基：每个非空坐标乘积的均值为零，其平方为一，不同乘积的内积仍为一个非空乘积的均值。故
$$
P_Cf=0,\qquad P_uf=u,\qquad P_vf=0,\qquad P_{uv}f=f.
$$
前向增量为 $u,uv$，各平方范数为 $1$；反向为 $0,u+uv$，平方范数为 $0,2$。单坐标的全部可测函数分别为 $\operatorname{span}\{1,u\}$ 与 $\operatorname{span}\{1,v\}$，其和不包含非零且与它正交的 $uv$。但 $\sigma(u,v)$ 给全部四点，故 $uv$ 联合可测。因此联合 $\sigma$ 代数的函数空间不同于边缘函数空间的线性和。此 Walsh 区分采用[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)§28.3“受限线性读出的历史关系容量”、§28.4“可逆重编码保持信息，却改变受限可访问性”的共同函数空间解释。$\square$

**命题 14.12（已获 XOR 记录破坏无条件乘积的交互正性）。** 环境恰取 $\Omega=\{0,1\}^2$，均匀律下 $X,Y$ 为坐标，完整旧记录为 $C=X\mathbin\oplus Y$，之后两个具名读数为 $X,Y$。虽然 $X,Y$ 无条件独立，仍有
$$
P_{\{X\}}=P_{\{Y\}}=P_{\{X,Y\}}=\operatorname{Id}_{\mathcal H},\qquad
D_{\{X,Y\}}=P_C-\operatorname{Id}_{\mathcal H}.
\tag{14.23}
$$
后者在非零的 $\operatorname{ran}(\operatorname{Id}-P_C)$ 上具有严格负二次型，因而不是正交投影。任一嵌套取得顺序的风险改善仍非负。

**证明。** 给定 $(C,X)$ 可由 $Y=C\oplus X$ 恢复整个点；给定 $(C,Y)$ 同理，所以前三个投影均为恒等。代入式（14.3）给 $D_{\{X,Y\}}=\operatorname{Id}-\operatorname{Id}-\operatorname{Id}+P_C$。若 $P_Cg=0$ 且 $g\ne0$，则 $\langle g,D_{\{X,Y\}}g\rangle=-\|g\|_2^2<0$；例如 $g=(-1)^X$，在每个奇偶类上取两种符号且等权，故 $P_Cg=0$、$\|g\|_2^2=1$。给定 $C=0$ 时 $X=Y$，且各自仍为公平位，联合并不等于条件边缘的乘积，明确违反假设14.4。

沿任一种顺序，两个塔增量均依次为 $\operatorname{Id}-P_C$ 与 $0$，所以命题14.3给非负风险下降。若另扩充环境加入未观察变量，前三个投影只能由上述记录确定为 $P_E$，不能自动写成环境上的恒等；这里限定为恰好四点保证了式（14.23）。$\square$

**命题 14.13（记录交互全部为零仍有隐藏目标）。** 取 $\Omega=\{-1,1\}^3$ 上均匀律，坐标 $u,v,z$ 独立，$C$ 常值，事件只记录 $u,v$。对目标 $f=z$，假设14.4成立，但
$$
D_Sf=0\quad(S\subseteq\{u,v\}),\qquad
K_Jf=0\quad(J\in\mathcal J(E)),\qquad
Qf=f,\quad\|Qf\|_2^2=1.
\tag{14.24}
$$

**证明。** 给定 $u,v$ 的任意子集后，$z$ 仍独立且均值为零，故每个 $P_Sf=0$。式（14.3）及（14.12）给全部所列 $D_Sf,K_Jf$ 为零，而 $P_Ef=0$ 给 $Qf=f$；$z^2=1$ 给范数平方为一。因此即使全部已记录交互都没有未显露能量，也不能删除定理14.9中的 $Qf=0$ 条件。$\square$

## 14.99 追加锚

## 15. 有限受控预测接口与实际概率域的几何

**约定 15.1（联合仪器、完整档案与预测任务）。** 以下三节是普通数学推导；所用成熟结果在使用处注明来源，不宣称新增 Lean 核验或世界范围原创。第13—14节的固定、不扰动读数族在此扩展为会改变后继状态的受控实验。取有限非空集合 $X,A,Y$，分别表示隐藏当前状态、动作和输出，令 $n=|X|$。给非负矩阵
$$
K_{a,y}\in\mathbb R^{X\times X},\qquad
\sum_{y\in Y}K_{a,y}\mathbf1=\mathbf1\quad(a\in A).
\tag{15.1}
$$
所有 $a$ 在每个状态均合法；若要表示失败或终止，须把其输出及后继吸收状态纳入这同一个仪器，完整记录保留这些标签。记 $\Delta_X=\{p\in\mathbb R^X:p_x\ge0,\ \sum_xp_x=1\}$；行向量 $p\in\Delta_X$ 表示当前状态律，矩阵作用于列函数。带输出的动作词 $w=(a_1,y_1)\cdots(a_k,y_k)$ 按时间先后定义
$$
K_w=K_{a_1,y_1}\cdots K_{a_k,y_k},\qquad
K_\varnothing=I,\qquad pK_w\mathbf1.
\tag{15.2}
$$
末项是固定执行动作词 $(a_1,\ldots,a_k)$ 时取得整个输出词 $(y_1,\ldots,y_k)$ 的概率，不是只看末端输出的边缘。

记 $C$ 为全部已表示的、带来源的旧档案，$H_t$ 为保留 $C$ 的完整可访问历史。允许策略采用独立于初态和环境噪声的外部随机源，并按下列条件核逐步生成联合律：对每个正概率条件事件，
$$
\Pr(A_t=a,Y_{t+1}=y,X_{t+1}=x'\mid
\Theta=\theta,X_t=x,H_t=h)
=\pi_t(a\mid h)K_{a,y}(x,x').
\tag{15.3}
$$
$\Theta$ 是可选的固定来源标签；没有该标签时删去它。给定更早隐藏状态路径时也使用同一右侧，所以式（15.3）是顺序生成契约，不仅是一个孤立的边缘条件等式。随机源初始独立不能替代此受支撑条件化契约。记录按 $H_{t+1}=(H_t,A_t,Y_{t+1})$ 扩充；若控制器还访问其他随机记录或内部记忆，须将其相应信息包含在所声明的访问历史中。这里采用[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定义17.1的联合核语义；其定理17.2—17.3提供完整开环记录与自适应实验的精确接口，命题17.7已经排除了分别拼接输出和后继边缘的替代方案。

正概率分支 $\ell=pK_{a,y}\mathbf1>0$ 的当前状态后验为 $pK_{a,y}/\ell$。这是已声明联合模型中的统计条件化；$K_{a,y}$ 已包含真实状态改变，后验更新不等于免费取得或制备微观状态。$p$ 及下文的 $s$ 只是任务工作接口，完整档案 $C$ 和控制器访问权另行保留。本节的有限预测表示沿用 Michael L. Littman、Richard S. Sutton、Satinder Singh，[*Predictive Representations of State*](https://proceedings.neurips.cc/paper_files/paper/2001/file/1e4d36177d71bbb3558e43af9577d70e-Paper.pdf)，NeurIPS 14（2001），PDF第7页式（3）、定理1及第7—11页的有限 POMDP 构造；该文第11页也明确给出带负投影系数的例子。

**命题 15.2（全部词的有限不变张成）。** 在约定15.1下，置
$$
V=\operatorname{span}\{K_w\mathbf1:w\text{ 为任意有限词}\},\qquad
V_0=\operatorname{span}\{\mathbf1\},\qquad
V_{j+1}=V_j+\sum_{a,y}K_{a,y}V_j.
\tag{15.4}
$$
则 $V_j$ 恰由长度至多 $j$ 的词列张成；若 $V_{j+1}=V_j$，此后全部等于 $V_j=V$。特别地 $V_{n-1}=V$，严格增长至多发生 $n-1$ 次。这是词深度界，不是词个数、采样次数或实验预算界。

**证明。** $j=0$ 对应空词。归纳时，左乘 $K_{a,y}$ 正好在旧词前加一对动作与输出；连同旧词，得到全部长度至多 $j+1$ 的生成元。若相邻空间相等，则每个 $K_{a,y}$ 都保持 $V_j$，由词长归纳全部词列属于它，故稳定并等于 $V$。否则每步维数至少加一；从维数一开始，在 $n$ 维空间中最多严格增长 $n-1$ 次，得指定深度结论。$n=1$ 时 $V_0=\mathbb R^X$，无需增长。枚举至该深度仍可能涉及 $\sum_{j=0}^{n-1}(|A||Y|)^j$ 个词，且精确取得核或预测值的费用未由此消失。

这是上述 PSR 构造使用的不变张成法，与[量子算术卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)§57的未来 effect 空间、§73的有限 Hankel 实现及[5040卷](ZECKENDORF_EULER_5040.md)“最小线性实现的维数恰好等于这个秩”一段中的加权自动机方法相接。这里的生成元换为联合仪器的全部词；[DynamicClosureMinimality](../../../D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean)的有限干预轨迹最小闭包供应相应的集合结构，但不直接代替概率核证明。不把既有有限维闭包方法另称为新原理。$\square$

**定理 15.3（预测坐标、正锥与支撑内更新）。** 令 $r=\dim V$，选列基矩阵 $B\in\mathbb R^{X\times r}$，第一列为 $\mathbf1$。记 $e_1$ 为 $\mathbb R^r$ 的第一标准列向量。存在唯一矩阵 $M_{a,y}\in\mathbb R^{r\times r}$ 满足
$$
K_{a,y}B=BM_{a,y}.
\tag{15.5}
$$
定义实际归一化预测域及未归一化正锥
$$
\mathcal P=\{pB:p\in\Delta_X\}
=\operatorname{conv}\{B(x,:):x\in X\},\qquad
\mathcal C=\{uB:u\in\mathbb R^X_{\ge0}\}.
\tag{15.6}
$$
对任意 $s\in\mathcal P$，有 $se_1=1$，且
$$
\ell_{a,y}(s)=sM_{a,y}e_1\ge0,\qquad
\sum_y\ell_{a,y}(s)=1.
\tag{15.7}
$$
当 $\ell_{a,y}(s)>0$ 时，
$$
F_{a,y}(s)=\frac{sM_{a,y}}{\ell_{a,y}(s)}\in\mathcal P
\tag{15.8}
$$
与 $s=pB$ 所选的代表 $p$ 无关。若分支质量为零，则 $sM_{a,y}=0$，而该分支没有由条件化确定的后验。每个 $M_{a,y}$ 保持 $\mathcal C$；其矩阵元素无需逐项非负。

**证明。** 命题15.2给 $K_{a,y}V\subseteq V$，所以 $K_{a,y}B$ 的各列在基 $B$ 中有唯一坐标，得到式（15.5）。对任意 $u\ge0$，
$$
(uB)M_{a,y}=(uK_{a,y})B\in\mathcal C.
$$
若 $s=pB$，则 $se_1=p\mathbf1=1$，且 $sM_{a,y}e_1=pK_{a,y}\mathbf1$；非负性与输出质量和由式（15.1）给出。正质量时 $p'=pK_{a,y}/\ell$ 是概率行向量，$p'B$ 就是式（15.8）。其右侧只依赖 $s,a,y$，因此代表无关。质量为零时非负行向量 $pK_{a,y}$ 的坐标和为零，故它全部为零，进而 $sM_{a,y}=0$；不对 $0/0$ 作后验解释。相同论证还表明 $c\in\mathcal C$ 且 $ce_1=0$ 必有 $c=0$。

对词定义 $M_w=M_{a_1,y_1}\cdots M_{a_k,y_k}$、$M_\varnothing=I$。逐次应用式（15.5）得 $K_wB=BM_w$，故所有词概率为 $sM_we_1$。概率正性由实际锥保证，而非由任意坐标矩阵的符号保证。第15.7条将直接展示负元素。上述归一化公式是所引 PSR 文献式（3）在含常数列的基上的写法；其适用范围始终是 $\mathcal P$，没有把整个超平面 $se_1=1$ 宣告为可实现概率态。$\square$

**定理 15.4（实际预测商、线性维数与可恢复目标）。** 在上述同一仪器下，对任意 $p,q\in\Delta_X$，
$$
pB=qB
\iff \forall w, pK_w\mathbf1=qK_w\mathbf1.
\tag{15.9}
$$
在相同固定初始可访问记录、相同控制器状态及式（15.3）的策略契约下，这还等价于全部允许有限自适应实验的完整动作—输出记录律相等。因而 $\mathcal P$ 表示实际实现的预测等价类；任何能决定全部这些词概率的集合统计量 $T$，在其实际像上唯一决定 $s$。

若竞争表示是未归一化输入上的齐次线性映射 $L:\mathbb R^X\to W$，其中 $W$ 有限维，并且相同 $L(u)$ 对全部 $u\ge0$ 决定相同的每个 $uK_w\mathbf1$，则 $\dim\operatorname{ran}L\ge r$；$u\mapsto uB$ 达到 $r$。归一化域 $\mathcal P$ 的仿射维数恰为 $r-1$。

对任意列函数 $h\in\mathbb R^X$，存在解码器 $g:\mathcal P\to\mathbb R$ 使
$$
g(pB)=ph\quad\text{对全部 }p\in\Delta_X
\quad\Longleftrightarrow\quad h\in V.
\tag{15.10}
$$
特别地，从 $s$ 恢复全部初态分布 $p$ 的充要条件为 $V=\mathbb R^X$。这些是全先验结论；某个受限可达先验族可以有额外关系。

**证明。** $pB=qB$ 使 $p-q$ 消去 $V$，故消去每个词列；反向由生成元张成 $V$ 得到。各输出词的概率相等即为固定动作词下的完整输出律相等。直接应用[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定理17.2的逐记录策略乘子论证得到自适应等价；初态是混合律时，同一乘子仍与被求和的隐藏状态无关。固定词本身属于策略族，给反向。确定性闭包对应[观察者闭包谱卷](OBSERVER_CLOSURE_SPECTRUM.md)§16；这里不将控制器能读取隐藏状态的策略算入允许族。

若 $T(p)=T(q)$，其预测充分性使式（15.9）右侧成立，故可定义 $\varphi(T(p))=pB$。它良定义且在实际像上唯一，给集合意义的最小性；此为[PredictiveStateUniversalMinimality](../../../D5/S3/ObserverMemory/PredictionFactors/PredictiveStateUniversalMinimality.lean)的实际像唯一因子化结构，不是任意编码长度下界。[CanonicalPredictiveStateSufficiency](../../../D5/S3/ObserverMemory/PredictionFactors/CanonicalPredictiveStateSufficiency.lean)的充分性也针对已指定的未来条件律。

对齐次线性下界，取 $d\in\ker L$，将它分成 $d=d^+-d^-$，其中 $d^\pm\ge0$。线性性给 $L(d^+)=L(d^-)$，假设遂给 $dK_w\mathbf1=0$ 对所有词成立，故 $dB=0$。于是 $u\mapsto uB$ 通过 $\operatorname{ran}L$ 线性因子化，而 $B$ 列满秩使其像维数为 $r$，得到下界。归一化方面，$\mathcal P$ 的全部行顶点候选均在 $se_1=1$ 上。固定一个这样的行 $v_0$，其余行之差都在 $se_1=0$；$v_0$ 与差空间线性独立。全部行的线性张成维数为 $r$，所以差空间维数为 $r-1$，正是仿射维数。$r=1$ 时 $\mathcal P$ 是单点。这与[MinimalPredictiveSummary](../../../D5/S3/Quantum/Fibers/MinimalPredictiveSummary.lean)的线性范围维数界、[AllFutureStatisticsSufficiency](../../../D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency.lean)的未来张成判据使用同一线性结构，但载体及生成算子按本节重新指定。

若 $h=B\alpha$，取 $g(s)=s\alpha$ 即可恢复。若 $h\notin V$，有限维线性分离给非零行向量 $d$，满足 $dB=0$ 而 $dh\ne0$；因 $\mathbf1\in V$，有 $d\mathbf1=0$。取内点均匀先验 $p_0$，再取 $\varepsilon>0$ 足够小使 $\varepsilon|d_x|<1/n$ 对所有 $x$ 成立。则 $p_\pm=p_0\pm\varepsilon d\in\Delta_X$，两者预测态相同而目标差为 $2\varepsilon dh\ne0$，排除任何解码器。恢复全部 $p$ 等价于恢复每个坐标指标函数；这些函数张成 $\mathbb R^X$，得最后结论。任意非线性集合编码的实坐标数或位数，均未受这里的线性维数论证约束。$\square$

**定理 15.5（概率单纯形上的目标最小最坏误差）。** 对同一 $B,V$ 及任意 $h\in\mathbb R^X$，允许所有集合函数解码器，有
$$
\inf_{g:\mathcal P\to\mathbb R}
\sup_{p\in\Delta_X}|ph-g(pB)|
=\operatorname{dist}_\infty(h,V)
:=\min_{v\in V}\max_{x\in X}|h_x-v_x|.
\tag{15.11}
$$
右侧的最佳逼近存在，且一个线性读出已达到该误差。该式是在有界概率域上的目标恢复结论；[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定理1.4针对无界线性输入得到的无穷风险不能转移到这里。它与该卷§3.1的候选纤维半径公式相容。

**证明。** $V$ 是有限维闭子空间。极小化序列的 $\|h-v\|_\infty$ 有界，故 $\|v\|_\infty$ 有界；取收敛子列，极限仍在 $V$，给最佳 $v_*$。写 $v_*=B\alpha$，则 $g(s)=s\alpha$ 满足
$$
|ph-g(pB)|=|p(h-v_*)|\le\|h-v_*\|_\infty
$$
对每个概率 $p$ 成立，给上界。

令 $d=\operatorname{dist}_\infty(h,V)$。$d=0$ 时上界已给零风险。若 $d>0$，在商空间 $\mathbb R^X/V$ 的 $\ell_\infty$ 商范数下，对非零元 $h+V$ 取范数一的支撑泛函，并延拓到整个商空间。有限维 Hahn–Banach 定理及 $\ell_\infty$ 与 $\ell_1$ 的对偶给行向量 $z$，使
$$
zv=0\ (v\in V),\qquad \|z\|_1=1,\qquad zh=d.
\tag{15.12}
$$
此处使用的是成熟的商范数对偶，见 Walter Rudin，*Functional Analysis*，第二版（1991），第3章的 Hahn–Banach 延拓与分离定理；式（15.12）亦由将上述商泛函拉回原空间直接得到。因为 $z\mathbf1=0$，其正、负部分的质量同为 $1/2$。故 $p=2z^+$、$q=2z^-$ 是概率分布，$pB=qB$，而 $ph-qh=2d$。任意解码器在同一个预测值上只给一个实数 $c$；由 $|ph-qh|\le|ph-c|+|qh-c|$，至少一个误差不小于 $d$。这与上界吻合。零先验坐标不需条件化，因而边界分布同样是合法下界见证。$\square$

**定理 15.6（预测多面体的正实现与全制备域下界）。** 设 $v_1,\ldots,v_k$ 是 $\mathcal P$ 的全部不同顶点。存在一个 $k$ 隐状态、动作集 $A$、输出集 $Y$ 的非负联合仪器，其全概率单纯形的预测像恰为 $\mathcal P$，且对每个 $s\in\mathcal P$ 保留全部受控词概率及允许的自适应记录律。

比较另一 $N$ 隐状态仪器时，要求每个 $\lambda\in\Delta_N$ 都是允许制备，并且在同一词概率识别下，其整个 $\Delta_N$ 的预测像恰好等于 $\mathcal P$。在这些量词下必有 $N\ge k$，所以前述构造最小。该下界不适用于只准许单纯形的一个子集、允许更大预测域或只指定一个初始制备的竞争问题。正实现的隐状态数也不是确定性观察者可取的预测态数：[量子算术卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)§151—155已经分别研究有限隐状态生成、无限精确预测商及有限精度历史记忆。

**证明。** 固定 $i,a,y$。定理15.3使 $v_iM_{a,y}\in\mathcal C$，质量 $\ell_i=v_iM_{a,y}e_1\ge0$。若 $\ell_i>0$，其归一化位于 $\mathcal P$，故可选顶点分解
$$
\frac{v_iM_{a,y}}{\ell_i}=\sum_j\alpha_{i,a,y,j}v_j,\qquad
\alpha_{i,a,y,j}\ge0,\qquad\sum_j\alpha_{i,a,y,j}=1.
$$
置 $\widehat K_{a,y}(i,j)=\ell_i\alpha_{i,a,y,j}$。若 $\ell_i=0$，则未归一化向量为零，将该分支整行置零。于是 $\widehat K$ 非负，且对每个 $i,a$ 有 $\sum_{y,j}\widehat K_{a,y}(i,j)=1$。令 $R$ 的第 $i$ 行为 $v_i$，便有
$$
\widehat K_{a,y}R=RM_{a,y},\qquad Re_1=\mathbf1.
\tag{15.13}
$$
对任意分解 $s=\lambda R$、$\lambda\in\Delta_k$，逐词相乘得
$$
\lambda\widehat K_w\mathbf1=sM_we_1.
$$
因而每个分解都给相同测试律，式（15.9）的自适应等价给完整实验结论。其全制备像为全部顶点的凸包，恰是 $\mathcal P$。

对竞争实现，令 $t_i\in\mathcal P$ 为第 $i$ 个纯态的预测像。测试概率对初始混合是仿射的，而它们识别 $s$，故整个单纯形的像为 $\operatorname{conv}\{t_1,\ldots,t_N\}=\mathcal P$。任一顶点 $v$ 写成这些 $t_i$ 的凸组合时，极端性迫使所有正权重项都等于 $v$；于是每个不同顶点必须由至少一个纯态给出，$N\ge k$。分解系数无须唯一，证明只给存在的正实现，不给免费、唯一的隐态解码器，也不把混合分布当作已取得的隐态样本。

受限制备确实改变结论。取 $\Delta_3$ 中的六边形 $D=\{p:p_i\le2/3\}$；其顶点是 $(2/3,1/3,0)$ 的六个排列：在平面 $\sum_ip_i=1$ 内，顶点至少有两个独立的坐标边界约束；两个零或两个 $2/3$ 都不满足总和条件，故只能一个零、一个 $2/3$、另一个 $1/3$，而这六个点确实各由两个边界唯一确定。三个隐状态、唯一动作读取状态符号 $i\in\{1,2,3\}$ 后重置到均匀律，则初始 $p$ 的未来是首符号服从 $p$、以后独立均匀。只准许 $p\in D$ 时，其预测域有六顶点却只用三个隐状态，且重置均匀律仍属 $D$。同一预测域也可由六态全制备实现：第 $i$ 态按第 $i$ 个顶点的三符号概率输出，再独立重置到六态均匀律。六顶点的平均是三符号均匀律，故全部后续词匹配。三态系统被排除的纯制备恰在 $D$ 外，因此没有违反全单纯形下界。$\square$

**命题 15.7（正方形预测域与不能恢复的交互目标）。** 取 $X=\{00,01,10,11\}$，$A=\{1,2\}$，$Y=\{0,1\}$。动作 $i$ 读出当前第 $i$ 位后重置为 $00$，即
$$
K_{i,y}(x,x')=\mathbf1_{\{x_i=y\}}\mathbf1_{\{x'=00\}}.
\tag{15.14}
$$
则 $V=\operatorname{span}\{\mathbf1,x_1,x_2\}$，齐次线性维数 $r=3$，$\mathcal P=\{(1,u,v):0\le u,v\le1\}$ 有四顶点。在定理15.6的全制备、精确相同预测域量词下，正实现恰需四个隐状态。初始交互目标 $h=x_1x_2$ 不能精确恢复，其最小最坏误差为 $1/4$。

**证明。** 一步词列为 $x_i$ 或 $1-x_i$。读出后已是 $00$，所有后续输出均为零，所以非空词列或为上述一步词列，或为零；连同空词，恰张成所述三维空间。以 $B=(\mathbf1,x_1,x_2)$ 为基，四行就是正方形四顶点，因此两种维数与顶点结论分别来自定理15.4和15.6。相应四个 $M_{i,y}$ 除第一列外全为零，其第一列依次为
$$
M_{1,0}e_1=(1,-1,0)^{\mathsf T},\quad
M_{1,1}e_1=(0,1,0)^{\mathsf T},\quad
M_{2,0}e_1=(1,0,-1)^{\mathsf T},\quad
M_{2,1}e_1=(0,0,1)^{\mathsf T}.
\tag{15.15}
$$
故分支质量为 $1-u,u,1-v,v$，每个正质量分支都更新为 $(1,0,0)$；零质量分支没有后验。这里的负元素已在实际域上给合法概率，无须另换基。

令 $p_{\rm even}$ 在 $00,11$ 上各取 $1/2$，$p_{\rm odd}$ 在 $01,10$ 上各取 $1/2$。它们均给 $s=(1,1/2,1/2)$，但 $p_{\rm even}h=1/2$、$p_{\rm odd}h=0$，故任意解码器的最坏误差至少 $1/4$。列函数
$$
v_*=(x_1+x_2)/2-1/4
$$
在四点上与 $h$ 的差依次为 $1/4,-1/4,-1/4,1/4$，给上界 $1/4$，并具体实现定理15.5。两个同边缘先验的全部允许未来词律已相同；要取得区分它们的新数据，必须扩充原先声明的动作或测试语言，不能仅重新计算 $s$。$\square$

**命题 15.8（当前预测商不恢复来源档案）。** 在命题15.7的同一仪器中，设初始位对为 $(\Theta,0)$，$\Theta$ 公平，$C$ 可包含任何已取得旧记录。先执行动作1并保留输出。两个正概率历史 $H_1=(C,1,0)$、$H_1=(C,1,1)$ 在共同 $C$ 的正概率纤维上均可出现时，它们的当前预测态同为 $(1,0,0)$，全部环境未来输出都为零，但来源后验分别为 $\Theta=0$、$\Theta=1$ 的点质量。

**证明。** 动作1输出初始 $\Theta$，随后两支均重置为 $00$，故当前律与未来预测相同，而保留的输出精确决定来源。条件为两支正概率；若 $C$ 已决定 $\Theta$，就在相应纤维只保留有支撑的一支，不制造另一支条件律。因此 $s$ 不能重建完整 $H_1$ 或来源后验。若控制器以后根据旧输出选择动作，两个历史还可产生不同的动作记录；定理15.4的反馈比较要求相同的初始控制器访问情境，不能用环境预测相同删除这项要求。[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)§38.1—38.2已区分任务摘要、合法动作与旧档案的在线取得；本例给出其与状态重置的连接。$\square$

## 16. 固定动作词与反馈实验的同核异距

**定义 16.1（共同仪器的有限时域距离）。** 固定约定15.1的同一有限仪器、同一个确定的初始可访问记录 $H_0=c$ 及相同控制器初始状态。两个先验 $p,q\in\Delta_X$ 只改变隐藏初态律，不改变策略、动作访问权或核。对整数 $H\ge1$，定义
$$
\begin{aligned}
d_{{\rm ol},H}(p,q)
&=\max_{\boldsymbol a\in A^H}
\operatorname{TV}(P_p^{\boldsymbol a},P_q^{\boldsymbol a}),\\
d_{{\rm fb},H}(p,q)
&=\sup_{\pi}
\operatorname{TV}(P_p^{\pi,H},P_q^{\pi,H}),\qquad
\operatorname{TV}(P,Q)=\tfrac12\sum_z|P(z)-Q(z)|.
\end{aligned}
\tag{16.1}
$$
前者的随机对象是整个输出词；后者为整个动作—输出记录，$\pi$ 遍历满足式（15.3）的共同历史反馈策略。固定词实验的动作是确定的，将它附在输出词上不改变 TV。外部随机策略种子独立于隐藏初态及环境噪声；所比较的双方使用同一策略机制，条件核契约仍须成立。定义 $d_{{\rm ol},0}=d_{{\rm fb},0}=0$，因为初始可访问记录已固定相同。随机终止若纳入模型，完整记录用共同吸收符号延长到 $H$。

**定理 16.2（有限时域比较界）。** 令 $m=|A|\ge1$。定义16.1的两个量是 $\Delta_X$ 上的伪度量，并满足
$$
d_{{\rm ol},H}\le d_{{\rm fb},H}
\le\min\{1,m^{H-1}d_{{\rm ol},H}\}\qquad(H\ge1).
\tag{16.2}
$$
对单个确定性策略树 $\pi$，可将右侧因子换成 $N_\pi$：它是在 $p$ 或 $q$ 的记录支撑上出现的不同完整动作词数，$1\le N_\pi\le m^{H-1}$。随机策略的统一结论使用 $m^{H-1}$，不把不同确定性树的词数未经控制地合成一个更小因子。$H=1$ 或 $m=1$ 时两个距离相等。

**证明。** 每个固定实验的 TV 满足非负性、对称性、对角为零和三角不等式；在同一个预先固定的实验族上取上确界仍有这些性质。这是[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)§17.4—17.5的一般行为伪度量方法在有限 $H$ 上的直接应用。固定动作词属于反馈策略族，给左侧界，TV 本身给上界一。

先取确定性策略树。初始记录相同且固定，所以首动作固定。将全部可能记录按其完整动作词 $\boldsymbol a$ 分组；对每组令 $E_{\boldsymbol a}\subseteq Y^H$ 为沿该输出词恰使策略选择 $\boldsymbol a$ 的输出集合。这个相容性集合由同一策略决定，与 $p,q$ 无关。由式（15.3），在相容记录上策略概率因子全为一，因此
$$
\begin{aligned}
\operatorname{TV}(P_p^{\pi,H},P_q^{\pi,H})
&=\frac12\sum_{\boldsymbol a}
\sum_{\boldsymbol y\in E_{\boldsymbol a}}
\left|pK_{a_1,y_1}\cdots K_{a_H,y_H}\mathbf1
-qK_{a_1,y_1}\cdots K_{a_H,y_H}\mathbf1\right|\\
&\le\sum_{\boldsymbol a\ {\rm realized}}
\operatorname{TV}(P_p^{\boldsymbol a},P_q^{\boldsymbol a})
\le N_\pi d_{{\rm ol},H}(p,q).
\end{aligned}
\tag{16.3}
$$
任一方支撑均为空的组贡献零，可以删去；其余组的受限非负绝对值和至多为全输出词之和。首动作固定，剩余 $H-1$ 个动作每步至多 $m$ 种，故 $N_\pi\le m^{H-1}$。

有限时域、有限动作输出下，行为随机策略可在开始前对每个可能历史节点独立抽取其动作，把它写成有限个确定性策略树的混合。混合权重只依赖策略核，与隐藏初态及环境噪声独立，并在两侧相同。一般独立随机种子的策略也可先固定种子而得到确定性树，再按树合并权重。TV 的凸性使每个分量的统一 $m^{H-1}$ 界在混合后仍成立。若独立种子也写入被比较的记录，按该种子分层计算 TV 是分量 TV 的平均，同一界仍有效；没有把种子当成隐藏状态的额外观测。最后取策略上确界得式（16.2）。$H=1$ 或 $m=1$ 时因子为一，与左界夹合；$H=0$ 按定义另行取零，无需解释负指数。

固定 $c$ 是该计数证明的条件。如果未条件化的随机旧档案已经能选择首动作，就不能直接套用“首动作固定”的 $m^{H-1}$ 论证；应在共同正概率档案纤维上比较，或为所使用的初始记录实验族另立界。$\square$

**定理 16.3（随时域变化的锐挑战仪器）。** 对每个 $m\ge2,H\ge2$，存在满足约定15.1的有限、时间齐次仪器及两个具有相同初始可访问记录的初态 $p,q$，使
$$
d_{{\rm ol},H}(p,q)=m^{-(H-1)},\qquad
d_{{\rm fb},H}(p,q)=1.
\tag{16.4}
$$
所有动作均合法，失败完整保留。这给出式（16.2）指数因子的锐例族；它排除跨全部有限模型及全部时域的统一常数，而不声称某一个固定模型在任意大 $H$ 都有该精确比值。

**证明。** 令 $A=\{1,\ldots,m\}$，初态为携带隐藏位 $z\in\{0,1\}$ 的 $S_z$，$p=\delta_{S_0}$、$q=\delta_{S_1}$。输出字母为互不混淆的挑战符号 $c_r$、最终位符号 $b_0,b_1$、失败符号 $\dagger$ 与完成后符号 $*$。从 $S_z$ 执行任意动作，都均匀输出 $c_{r_1}$，并进入状态 $(z,2,r_1)$。一般待执行阶段状态 $(z,t,r)$ 满足 $2\le t\le H$：若动作 $a\ne r$，输出 $\dagger$ 并进入失败吸收态；若 $a=r$ 且 $t<H$，独立均匀生成新挑战 $r'$，输出 $c_{r'}$ 并进入 $(z,t+1,r')$；若 $a=r$ 且 $t=H$，输出 $b_z$ 并进入完成吸收态。失败态永远输出 $\dagger$，完成态永远输出 $*$，两者对所有动作均保持自身。把阶段计数纳入有限状态后，这是一套时间齐次、逐行动总质量为一的非负联合核。

固定动作词 $(a_1,\ldots,a_H)$。到达最终位输出当且仅当每个 $r_{t-1}=a_t$，$2\le t\le H$，其概率为
$$
\alpha=m^{-(H-1)}.
$$
第一次动作不影响挑战律。可以事先生成独立公平挑战序列，在两种 $z$ 下共用它；每个失败记录的概率由挑战和动作决定，与 $z$ 无关。成功记录则在最终位符号上分别为 $b_0,b_1$，两个成功部分支撑不交，各有质量 $\alpha$。故半 $\ell_1$ 差恰为 $\alpha$，对每个固定动作词都相同。

反馈策略任取首动作，以后总选择刚读到的挑战值。每步匹配，因此成功概率为一，最后必读到 $b_z$；两种初态的完整记录支撑不交，TV 为一。保留失败记录是固定词 TV 计算的一部分，没有通过条件成功后丢弃概率质量来放大距离。每个 $H$ 的阶段状态集合不同，正说明此处量词是一个模型族。$\square$

**命题 16.4（同一锐例中的固定来源创新）。** 在定理16.3的仪器中，把隐藏初始位作为固定来源目标 $Z\sim\operatorname{Bernoulli}(1/2)$，初始档案常值。固定动作词的总均方创新及末端 Bayes 风险分别为
$$
I_{\rm ol}=\frac{\alpha}{4},\qquad
R_{\rm ol}=\frac{1-\alpha}{4},\qquad\alpha=m^{-(H-1)}.
\tag{16.5}
$$
匹配挑战的反馈策略对应 $I_{\rm fb}=1/4$、$R_{\rm fb}=0$。这里总创新指
$\mathbb E[(\mathbb E[Z\mid H_H]-1/2)^2]$。

**证明。** 在任一挑战前缀及每个失败记录上，$Z$ 的条件律仍为公平位，因为该记录只由独立挑战与已指定动作生成。固定词成功时才观察 $b_Z$，随后后验为点质量。因此末端条件均值在失败时为 $1/2$，在成功时为 $Z$；均方创新为 $\alpha(1/2)^2$。末端条件方差在失败时为 $1/4$，在成功时为零，积分给风险式。反馈匹配必然成功，所以获得全部初始 $1/4$ 风险预算。第17节的固定目标塔公式将把总创新分成实际各步之和。两种策略分别诱导不同的完整联合律；策略计算只选择了更有效的取得路径，并没有无输入地创造来源信息。$\square$

**推论 16.5（精确商相同不等于统一的稳定性常数）。** 对定义16.1的每个有限 $H$，$d_{{\rm ol},H}$ 与 $d_{{\rm fb},H}$ 有同一零核；在所有有限 $H$ 上同时取零，恰得到定理15.4的预测商。但若只给一个 $H$ 步开环误差预算，转为该时域反馈误差的统一乘法常数不能小于定理16.3例族的 $m^{H-1}$。

**证明。** 有限正因子的双边界（16.2）给同零核，遍历全部 $H$ 即为全部词的相等关系。把定理16.3的两个数代入任何候选乘法界 $d_{{\rm fb},H}\le c\,d_{{\rm ol},H}$，得到 $c\ge m^{H-1}$。因此在同一个语义商上，允许实验族仍决定误差几何。

[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定理21.6从全状态、全动作的输出—后继摘要联合核缺陷得到完整记录界 $1-(1-\varepsilon)^H\le H\varepsilon$；它的前提比这里只约束固定词记录的前提不同，本锐例不反驳该逐步联合证书。若比较两套模型，可用带不变模型标签的互不相交状态并集、块对角共同仪器及同一动作输出字母表，将比较写成一套源模型上的两个先验；已有档案、失败语义与策略访问权仍须对齐。该构造直接保留两套联合核，并不允许把独立取得的边缘读数拼成共同实现。$\square$

## 17. 固定来源目标的动作依赖创新与联合记忆

**定义 17.1（完整历史上的来源后验与有效似然）。** 固定有限非空来源标签集 $\Theta$、有限当前状态集 $X$、有限非空动作与输出集、有限的已表示旧档案字母集，以及有限时域 $T\ge0$。$\Theta$ 表示同一个固定来源目标，例如初始状态的标签；隐藏当前状态 $X_t$ 可以被动作和输出共同改变。以 $H_0=C$ 开始，$C$ 包括全部已表示的来源记录、内外档案及控制器初始可访问关系；以后 $H_{t+1}=(H_t,A_t,Y_{t+1})$ 保留旧历史。给定允许策略及受控模型，得到一份完整联合律。对正概率条件事件采用顺序生成契约
$$
\Pr(A_t=a,Y_{t+1}=y,X_{t+1}=x'\mid
\Theta=\theta,X_t=x,H_t=h)
=\pi_t(a\mid h)T_t(x',y\mid\theta,x,h,a),
\tag{17.1}
$$
其中 $T_t$ 是逐输入归一化的非负核；给定更早隐藏路径也使用此核。$\pi_t$ 只能访问实际 $h$ 及允许的独立随机源，不直接访问 $\theta,x$。动作守卫若存在，$\pi_t$ 支撑于已声明的合法动作。这个[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定义17.1型条件因子化，比仅说“开始时抽了一枚独立种子”更具体。

在 $\Pr(H_t=h)>0$ 时令 $b_h(\theta)=\Pr(\Theta=\theta\mid h)$，以下把 $b_h$ 写成概率列向量。对 $\pi_t(a\mid h)>0$ 的动作，及 $b_h(\theta)>0$ 的来源类，定义
$$
\begin{aligned}
\mu_h(\theta,x)&=\Pr(\Theta=\theta,X_t=x\mid h),\\
L_{h,a}(y\mid\theta)
&=\sum_x\frac{\mu_h(\theta,x)}{b_h(\theta)}
\sum_{x'}T_t(x',y\mid\theta,x,h,a).
\end{aligned}
\tag{17.2}
$$
它是从完整受控联合律导出的有效似然。$b_h(\theta)=0$ 时可给 $L_{h,a}(\cdot\mid\theta)$ 任意概率行，其后总被零质量乘掉；$h$ 无支撑时不定义其后验。未被该策略选择的合法动作若要参与比较，须有已指定的干预核 $T_t$，再用式（17.2）定义相应实验，不能把零概率条件事件当作实际观测。

仅给 $b_h$ 不保证能得到式（17.2）：同来源条件下的当前状态律、历史依赖核及动作守卫均可能仍缺失。若要闭合递推，须增加任务实际需要的联合状态或历史关系。[AdaptivePosteriorPolicySufficiency](../../../D5/S3/Estimation/DataProcessing/AdaptivePosteriorPolicySufficiency.lean)要求共同来源条件实验核及正确 Bayes 历史扩展；它不把这些前提从来源边缘后验中自动导出。本节讨论概率、投影和固定目标风险，不从“状态”“空间”“时间”或“创新”的名称推出物理波、场或衰变定律。

**命题 17.2（动作选择本身的来源零创新）。** 在定义17.1的正概率历史 $h$ 及被选择概率为正的动作 $a$ 上，
$$
\Pr(\Theta=\theta\mid H_t=h,A_t=a)=b_h(\theta).
\tag{17.3}
$$
确定性动作可测于 $H_t$，不增加其 $\sigma$ 代数；随机动作虽可增加记录的 $\sigma$ 代数，却在式（17.1）下不改变来源后验。该结论不适用于与隐藏来源相关而未满足此条件因子化的随机化。

**证明。** 将式（17.1）对 $x',y$ 求和，并按 $\mu_h(\theta,x)$ 对 $x$ 积分，得到
$$
\Pr(\Theta=\theta,A_t=a\mid h)=b_h(\theta)\pi_t(a\mid h).
$$
除以正数 $\pi_t(a\mid h)$ 给式（17.3），即条件独立。确定性时 $A_t=\pi_t(h)$ 直接为历史函数。若反而让动作取未被历史揭示的来源位 $A_t=\Theta$，公平来源、常值历史下动作就揭示来源，明确违反上述因子化，因而不是本命题的反例。$\square$

**定理 17.3（单步来源创新协方差与剩余预算）。** 固定定义17.1的正概率 $h,a$，记 $b=b_h$、$L=L_{h,a}$，并置
$$
q_y(\theta)=b(\theta)L(y\mid\theta),\qquad
p_y=\sum_\theta q_y(\theta),\qquad
b_y=q_y/p_y\quad(p_y>0).
\tag{17.4}
$$
则 $\sum_yq_y=b$、$\sum_yp_y=1$，正质量时 $b_y$ 是给定新动作与输出后的来源后验。定义
$$
\begin{aligned}
G(h,a)
&=\sum_{y:p_y>0}\frac{q_yq_y^{\mathsf T}}{p_y}-bb^{\mathsf T}\\
&=\sum_{y:p_y>0}p_y(b_y-b)(b_y-b)^{\mathsf T}.
\end{aligned}
\tag{17.5}
$$
有
$$
0\preceq G(h,a)\preceq\operatorname{Diag}(b)-bb^{\mathsf T},\qquad
G(h,a)\mathbf1=0,
\tag{17.6}
$$
以及精确预算恒等式
$$
\operatorname{Diag}(b)-bb^{\mathsf T}
=G(h,a)+\sum_{y:p_y>0}p_y
\bigl[\operatorname{Diag}(b_y)-b_yb_y^{\mathsf T}\bigr].
\tag{17.7}
$$

**证明。** 似然每行和为一，故对 $y$ 求和给 $b$，再对来源求和给一。命题17.2使选择动作前后的 $b$ 相同，随后 Bayes 公式给式（17.4）。$p_y=0$ 时非负向量 $q_y$ 必为零；不定义 $b_y$，该项从全部和中删去。展开式（17.5）第二行，并使用 $\sum_{p_y>0}p_yb_y=b$，得到第一行。

每个外积 $(b_y-b)(b_y-b)^{\mathsf T}$ 半正定，故 $G\succeq0$；且 $(b_y-b)^{\mathsf T}\mathbf1=0$，给 $G\mathbf1=0$。任意概率列 $u$ 满足
$$
v^{\mathsf T}[\operatorname{Diag}(u)-uu^{\mathsf T}]v
=\sum_\theta u_\theta(v_\theta-u^{\mathsf T}v)^2\ge0
$$
对每个实列 $v$ 成立。最后 $\sum_yp_y\operatorname{Diag}(b_y)=\operatorname{Diag}(b)$，而 $\sum_yp_yb_yb_y^{\mathsf T}=G+bb^{\mathsf T}$，相减即式（17.7）；余项半正定给上界。若来源支撑为单点，左侧为零，必有 $G=0$；若某个来源质量为零，其在所有正质量后验中也为零，对应行列均不贡献。

这是来源指标向量 $\mathbf e_\Theta$ 的全协方差公式：总条件协方差等于条件均值的协方差加平均剩余协方差。所用条件期望及塔式恒等式是成熟概率论，见 David Williams，*Probability with Martingales*（1991），第9章；这里已用有限求和完整展开。它是本卷命题14.3的固定律嵌套投影在来源指标函数上的矩阵形式，不要求读数之间独立。$\square$

**定理 17.4（固定目标的风险下降与实际策略总创新）。** 在定义17.1的一份实际联合律下，给定固定函数 $f:\Theta\to\mathbb R$，将其值列记为 $f$。对每个正概率 $h,a$，一次观测的条件 Bayes 均方风险下降等于
$$
\operatorname{Var}(f(\Theta)\mid h)
-\sum_{y:p_y>0}p_y\operatorname{Var}(f(\Theta)\mid h,a,y)
=f^{\mathsf T}G(h,a)f.
\tag{17.8}
$$
令 $m_t=\mathbb E[f(\Theta)\mid H_t]$。则
$$
\begin{aligned}
\sum_{t=0}^{T-1}\mathbb E[f^{\mathsf T}G(H_t,A_t)f]
&=\sum_{t=0}^{T-1}\mathbb E[(m_{t+1}-m_t)^2]\\
&=\mathbb E[(m_T-m_0)^2]\\
&=\mathbb E[\operatorname{Var}(f(\Theta)\mid C)]
-\mathbb E[\operatorname{Var}(f(\Theta)\mid H_T)]\\
&\le\mathbb E[\operatorname{Var}(f(\Theta)\mid C)].
\end{aligned}
\tag{17.9}
$$
各期望只在其实际历史和动作支撑上求和。停止后的吸收延续不增加来源信息时，其创新为零。$T=0$ 时空和及风险差均为零。

**证明。** 用 $f$ 左右乘式（17.7），各协方差二次型正是相应条件方差，得式（17.8）。也可在每个后验下展开平方损失：对任意实数 $d$，
$$
\mathbb E[(f(\Theta)-d)^2\mid h]
=\operatorname{Var}(f(\Theta)\mid h)+(b_h^{\mathsf T}f-d)^2,
$$
故条件均值为 Bayes 解。命题17.2使给定 $H_t,A_t$ 的观测前条件均值仍为 $m_t$，式（17.5）遂给
$\mathbb E[(m_{t+1}-m_t)^2\mid H_t,A_t]=f^{\mathsf T}G(H_t,A_t)f$。

历史保留使各 $\sigma(H_t)$ 嵌套，同一固定目标的 $m_t$ 为鞅。对于 $i<j$，$m_{i+1}-m_i$ 在 $H_j$ 下可测，而 $\mathbb E[m_{j+1}-m_j\mid H_j]=0$，所以两增量的内积期望为零。正交增量求和得式（17.9）的第二行；把单步风险差积分后望远镜求和得第三行，末端风险非负给最后界。本卷命题14.3、[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)§121及[ConditionalExpectationRefinementPythagoras](../../../D5/S3/ConceptDynamics/Prediction/ConditionalExpectationRefinementPythagoras.lean)已给嵌套条件期望的同一 Pythagoras 供应结构；本式将其落实到受控历史上的 $G(H_t,A_t)$。

此处非负的是对下一观测平均后的风险下降，不声称每个分支的条件方差都下降。例如 $\Theta\sim\operatorname{Bernoulli}(1/10)$，取二元输出满足 $L(1\mid1)=1$、$L(1\mid0)=1/9$。则 $p_1=1/5$，该支后验公平，方差 $1/4$ 大于先验方差 $9/100$；另一支后验为零态，平均剩余风险为 $1/20$，总下降 $1/25>0$。不同策略产生不同联合律，各自按式（17.9）结算，不把分别可达的逐步最大创新当作同一策略的同时收益。$\square$

**命题 17.5（移动当前目标不满足固定目标望远镜式）。** 即使全部输出无信息，$f(X_t)$ 的当前状态风险也可随状态扰动增加，因此不能将式（17.9）的 $f(\Theta)$ 直接替换为每步变化的 $f(X_t)$。

**证明。** 取 $X=\{0,1\}$、唯一动作、唯一输出 $*$，仪器从任一状态以概率各 $1/2$ 转到 $0,1$ 并输出 $*$。初态确定为 $X_0=0$，档案常值，令 $f(x)=x$。初始目标 $f(X_0)$ 的风险为零；一步后 $X_1$ 为不可见公平位，所以当前目标 $f(X_1)$ 的风险为 $1/4$，历史观测没有增加信息。若对每时刻当前目标错误使用固定目标风险差，就得到 $-1/4$，无法等于非负创新。真正固定的来源 $\Theta=X_0$ 始终确定，其来源创新和风险均为零，完全符合式（17.9）。改变被预测随机变量引入预测漂移；这一差异是目标定义的变化，不是任何物理熵定律的推论。$\square$

**命题 17.6（自适应读取混合既有交互扇区）。** 在均匀四点空间上取独立 $U,V\in\{-1,1\}$，旧档案常值，动作均为不扰动读取。先读 $U$，仅当 $U=1$ 时读 $V$，否则停止，并把停止及已读内容保留为记录 $H$。令 $P_H=\mathbb E[\cdot\mid H]$，$D_V$ 为原固定乘积空间中投影到 $\operatorname{span}\{V\}$ 的 Walsh 扇区投影，则
$$
P_HV=\mathbf1_{\{U=1\}}V=\frac{V+UV}{2},\qquad
D_VP_HV=\frac V2\ne\frac{V+UV}{2}=P_HD_VV.
\tag{17.10}
$$
因此 $P_H$ 不是第14节那些固定 $D_S$ 的某个子族之和；实际嵌套历史仍有正交创新。

**证明。** $U=1$ 时记录包含 $V$，条件均值为 $V$；$U=-1$ 时两种 $V$ 仍等概率，条件均值为零。独立公平位的 $1,U,V,UV$ 是正交归一基，故投影到 $V$ 扇区只保留 $(V+UV)/2$ 的 $V/2$ 部分，得到不交换式。任何固定正交 $D_S$ 的和都与每个 $D_S$ 交换，因而不能等于 $P_H$。具体地，$P_HV$ 的平方范数为 $1/2$，其旧扇区 $V$、$UV$ 分量的平方范数各为 $1/4$。从常值记录到读 $U$ 再到 $H$ 的投影仍嵌套，定理17.4或命题14.3给正交增量；改变的是“某个旧扇区在固定时刻完整显露”的解释条件。此例没有扰动，已经越出定理14.10的事先固定全枚举前提。$\square$

**定理 17.7（保留来源标记的有限预测接口）。** 对约定15.1的共同有限仪器，进一步要求未来核给定当前 $X_t$ 后不直接依赖来源 $\Theta$ 或历史，且来源标签自身不变。令 $B,M_{a,y}$ 如定理15.3。对任意正概率历史 $h$ 的联合后验 $\mu_h(\theta,x)$，定义行按来源排列的矩阵
$$
J_h(\theta,:)=\mu_h(\theta,:)B.
\tag{17.11}
$$
则来源边缘、当前环境预测态及来源标记词概率分别为
$$
b_h=J_he_1,\qquad
s_h=\sum_\theta J_h(\theta,:),\qquad
\Pr(\Theta=\theta,\text{输出词 }\boldsymbol y
\mid h,\text{执行固定动作词 }\boldsymbol a)
=J_h(\theta,:)M_we_1.
\tag{17.12}
$$
这里的“执行固定动作词”表示指定干预实验，并非对一个反馈策略末端动作词的事后条件化。对已选择动作 $a$ 的输出分支，总质量
$$
\ell=\sum_\theta J_h(\theta,:)M_{a,y}e_1
$$
为正时，联合预测接口更新为
$$
J_{hay}=\frac{J_hM_{a,y}}{\ell}.
\tag{17.13}
$$
零质量分支没有条件接口。两个联合后验的 $J$ 相等，当且仅当全部来源标记有限词概率相等，包括空词的来源质量；在相同初始可访问记录和同一策略契约下，还保留全部来源—自适应完整记录联合律。

**证明。** 对 $\mu_h$ 的每个来源行应用 $Be_1=\mathbf1$，得来源边缘；对来源行求和得当前状态边缘的 $B$ 读出。固定来源标签不变、仪器在给定 $X_t$ 后共同，故来源标记词概率为 $\mu_h(\theta,:)K_w\mathbf1$。由 $K_wB=BM_w$ 得式（17.12）。式（15.3）使选择动作的因子与 $\theta,x$ 无关；选择动作后联合后验仍为 $\mu_h$，而观察输出后变为
$$
\mu_{hay}(\theta,:)=\mu_h(\theta,:)K_{a,y}/\ell.
$$
右乘 $B$ 得更新式。质量为零时各来源行对应的非负输出质量都为零，无须也不能除以零。若 $b_h(\theta)=0$，则 $\mu_h(\theta,:)=0$、$J_h(\theta,:)=0$；其全部标记词概率为零。

$J$ 相等显然给所有标记词概率相等。反向，逐来源行的联合后验差消去全部 $K_w\mathbf1$，由它们张成 $V$，该行乘 $B$ 为零；逐行即得 $J$ 相等。对任一来源标记的完整自适应记录，用共同记录策略乘子乘式（17.12），再按[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定理17.2的同一逐记录论证，得联合律相等。与[PredictiveStateUnifilarUpdate](../../../D5/S3/ObserverMemory/ContextUpdates/PredictiveStateUnifilarUpdate.lean)相同，条件递推仅在正质量分支上由未来律唯一确定。

给定 $J_h$ 后，单步 $q_y$ 的来源分量就是 $J_h(\theta,:)M_{a,y}e_1$，所以式（17.5）的 $G(h,a)$ 也能计算。该接口保留任务可见的来源—未来关系，而删去逐来源行中消去 $V$ 的隐藏坐标；完整微观联合后验是一种充分表示，不因此成为必要表示。例如定理15.7的同预测先验分别配置在相同来源行上，便可有不同微观后验而同 $J$。这里没有宣称任意编码的实坐标或位数最小性。

若核直接依赖 $\Theta$，应将来源并入被声明的状态或采用相容的来源专属张成及矩阵；若核直接依赖历史，还须加入使核闭合的历史状态，且有限性须另证。未完成这些补充时，不能沿用一个共同 $M$。$J_h$ 也不代替已取得的 $C$ 或控制器需要的旧档案；未来来源标记概率的相等只针对声明的实验语言。$\square$

**命题 17.8（同一模型中相同来源边缘与预测边缘仍有不同创新）。** 存在一个有限、唯一动作的受控模型，两条正概率历史具有相同来源后验、相同当前状态预测态和全部环境未来输出律，却对下一读数给不同的 $G$。因此 $(b_h,s_h)$ 一般不能替代来源标记接口 $J_h$。

**证明。** 令来源 $\Theta$ 公平。隐藏状态有初始态 $S_0,S_1$、就绪态 $R_0,R_1$ 及重置态 $O$，初态为 $S_\Theta$；来源标签固定保留在联合律中。首步输出独立公平模式位 $R$：当 $R=0$ 时转到 $R_\Theta$，当 $R=1$ 时另抽独立公平位 $Z$ 并转到 $R_Z$。明确地，从 $S_\theta$ 到输出模式0、就绪态 $R_\theta$ 的概率为 $1/2$；到输出模式1、任一就绪态 $R_z$ 的概率各为 $1/4$。从 $R_z$ 下一步输出读数位 $z$ 并转到 $O$；$O$ 此后恒输出共同吸收符号。模式输出与读数输出采用不同标签，状态内阶段使这是一套时间齐次仪器。

两个正概率历史 $h_0=(C,R=0)$、$h_1=(C,R=1)$ 的概率各为 $1/2$，$C$ 常值。因为模式独立，两个来源后验均为 $(1/2,1/2)^{\mathsf T}$。在两支下就绪位边缘均公平，所以当前状态律均在 $R_0,R_1$ 上各半，未来都先读一个公平位再吸收，预测态相同。但 $h_0$ 下读数位等于来源，$h_1$ 下读数位独立于来源，因此
$$
G(h_0,a)=\frac14
\begin{pmatrix}1&-1\\-1&1\end{pmatrix},\qquad
G(h_1,a)=0.
\tag{17.14}
$$
第一式因两个后验分别为来源点质量而来自式（17.5），第二式因每个后验都仍为公平来源。对 $f(\theta)=\theta$，创新分别为 $1/4$ 与零。来源标记下一读数的联合律分别是对角的两点各半与四点各 $1/4$，所以定理17.7的 $J$ 必然不同。两个档案中的模式记录确实不同并被保留；例子正是说明省略它及其所决定的联合关系会丢失来源创新信息，不把这两个历史冒充相同访问记录。命题15.8另显示重置可使当前预测完全相同，而档案仍保留不同来源事实。$\square$

**定理 17.9（完整来源—记录联合误差控制总创新）。** 在同一有限字母空间上给两个概率律 $P_{\Theta,H},Q_{\Theta,H}$；记录通过同一个映射 $C=c(H)$ 保留旧档案。假设两律的 $(\Theta,C)$ 边缘相同。给固定 $f:\Theta\to[m_f,M_f]$，$D=M_f-m_f\ge0$，记
$$
\delta=\operatorname{TV}(P_{\Theta,H},Q_{\Theta,H}),\qquad
m_C=\mathbb E[f(\Theta)\mid C]
$$
为共同初始条件均值，并定义
$$
I(P)=\mathbb E_P[(\mathbb E_P[f(\Theta)\mid H]-m_C)^2],
\qquad I(Q)\text{ 同理}.
\tag{17.15}
$$
则
$$
|I(P)-I(Q)|\le D^2\delta.
\tag{17.16}
$$
常数一不能统一缩小。这里只需完整联合律的 TV，不需要逐历史的后验误差界。

**证明。** 由 $C$ 被 $H$ 保留，在每份律中对固定目标应用嵌套投影，得
$$
I(P)=R_C-R(P),\qquad
R(P)=\inf_g\mathbb E_P[(f(\Theta)-g(H))^2],
\tag{17.17}
$$
其中 $R_C=\mathbb E[(f(\Theta)-m_C)^2]$ 由共同 $(\Theta,C)$ 边缘决定，$Q$ 亦同。把任何 $g$ 裁剪到 $[m_f,M_f]$ 只会逐点减小平方损失，故两个下确界都可取同一个有界解码器类。零概率历史上任选此区间中的值即可，不影响相应期望；有限支撑使条件均值达到最小值。

对每个这样的 $g$，损失 $\ell_g(\theta,h)=(f(\theta)-g(h))^2$ 属于 $[0,D^2]$。由 TV 的有界损失对偶，
$$
|\mathbb E_P\ell_g-\mathbb E_Q\ell_g|\le D^2\delta.
$$
有限情形直接可证：将带符号质量 $P-Q$ 分成正、负部分，两部分质量都为 $\delta$，把 $0\le\ell_g\le D^2$ 分别用于两部分即可。此成熟 TV 期望界也是[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定理21.6的共同记录奖励界所用的不等式。对统一解码器类取下确界，分别得到 $R(P)\le R(Q)+D^2\delta$ 及反向，结合共同 $R_C$ 即式（17.16）。$D=0$ 时所有风险和创新均为零；$\delta=0$ 时两律相同，两种情形无需除法。

为证常数锐性，取常值 $C$、$\Theta\sim\operatorname{Bernoulli}(p)$，$0<p<1$，$f(\theta)=\theta$。令 $P$ 中 $H=\Theta$，$Q$ 中 $H\equiv0$，两者定义在相同 $\{0,1\}^2$ 上且来源边缘相同。两律共有 $(0,0)$ 的质量 $1-p$，其余质量 $p$ 分别在 $(1,1)$ 与 $(1,0)$，故 $\delta=p$。前者完全恢复来源，$I(P)=p(1-p)$；后者没有新信息，$I(Q)=0$。于是创新差与 $D^2\delta$ 之比为 $1-p\to1$，任何小于一的统一常数均被足够小的正 $p$ 排除；$p=0,1$ 的退化来源风险均为零。

若 $H$ 是逐步过程的整个末端档案，可在包含不可变来源标签及旧档案的扩充系统上使用机器学习卷定理21.6：要求双方初始 $(\Theta,C)$ 一致、初始摘要按指定映射耦合，并对每个扩充状态和动作统一控制“输出与后继摘要”的联合 TV 缺陷，且摘要保留来源标签。此时该定理给来源—完整记录的 $\delta\le1-(1-\varepsilon)^T$，再代入式（17.16）。只控制未带来源的输出核或末端状态边缘，不满足这个扩充联合输入契约。支撑内条件更新的精确性也不提供稀有分支的统一稳定性；本卷命题12.5已有条件化的 $e/s$ 放大与稀有成功支反例，本定理只控制积分创新。$\square$

**命题 17.10（记录边缘相同不足以控制来源创新）。** 即使 $P_H=Q_H$ 且两律具有相同 $(\Theta,C)$ 边缘，创新也可相差 $1/4$，所以式（17.16）中的来源—记录联合 TV 不能换成记录边缘 TV。

**证明。** 令 $C$ 常值、来源公平、$f(\theta)=\theta$。在 $P$ 下令 $H=\Theta$，在 $Q$ 下令 $H$ 为与来源独立的公平位。两份记录边缘都是公平位，故其 TV 为零。$P$ 下后验为点质量，创新 $1/4$；$Q$ 下后验始终公平，创新零。联合律的 TV 实为 $1/2$，因此没有违反定理17.9。命题17.8已在同一受控模型的两个合法历史中实现同一种联合区别。由此，环境全部未来预测、来源标记未来预测以及完整已获档案是相互关联但不同的任务；它们能否互相恢复，分别取决于定理15.4的可见张成、定理17.7的共同来源核与保留式历史条件，不能由边缘相同或坐标名称代替。$\square$

## 17.99 追加锚

## 18. 局部容量、共同钟率与边界时间取得

**定义 18.1（固定关系图上的容量与物理端口）。** 取有 $n\ge2$ 个顶点的有限连通无向图，每条边具有固定正权；在固定顶点坐标中记其 Laplacian 为 $L$。取正对角容量矩阵 $M$，定义
$$
S_M(t)=\exp(-tM^{-1}L),\qquad t\ge0.
\tag{18.1}
$$
这里直接采用[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第123.4节的图关系律：若 $D_G$ 是定向差分、$W$ 是边权对角矩阵，则 $L=D_G^*WD_G$；正顶点权作为容量不要求总和为一。尤其 $L\mathbf1=0$、$\ker L=\mathbb R\mathbf1$，且每个 $L_{ii}>0$。本节比较固定图和固定顶点坐标中的不同常值 $M$，不把顶点重标或状态坐标共轭算作同一个矩阵等式。

固定物理输入 $B:\mathbb R^p\to\mathbb R^n$ 和读出 $H:\mathbb R^n\to\mathbb R^q$。对 $u\in L^1_{\rm loc}([0,\infty);\mathbb R^p)$，状态 $x$ 在每个有限区间绝对连续，动力学几乎处处成立，输出为
$$
M\dot x=-Lx+Bu,\qquad o=Hx.
\tag{18.2}
$$
输入、读出单位和端口身份均保持固定。以下脉冲响应使用零初态，或在固定完整历史下已由制备与独立已知项扣除自由响应的条件；未知初态不因指定 $B,H$ 而自动消失。该取得合同沿用本卷定义13.1、命题13.2及定义13.3的完整记录与共同来源，及[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)命题16.6的初态边界。

**定理 18.2（完整状态演化的常值容量钟刚性）。** 设 $M,N$ 均为正对角矩阵，$\phi:[0,\infty)\to[0,\infty)$ 是任意函数。则
$$
S_N(t)=S_M(\phi(t))\quad\text{对所有 }t\ge0
\tag{18.3}
$$
当且仅当存在 $c>0$ 使
$$
\boxed{\phi(t)=ct\quad(t\ge0),\qquad N=M/c.}
\tag{18.4}
$$
若另有 $\operatorname{tr}N=\operatorname{tr}M$，则 $c=1,N=M$。式（18.3）是全部初态上的完整状态等式；一个边界端口的相同响应不具有此推论。无需预设 $\phi$ 连续或可微。

**证明。** 矩阵指数的标准恒等式 $\det(e^A)=e^{\operatorname{tr}A}$ 给
$$
e^{-t\operatorname{tr}(N^{-1}L)}
=e^{-\phi(t)\operatorname{tr}(M^{-1}L)}.
$$
两个迹均为严格正数，因为它们分别为 $\sum_iL_{ii}/N_{ii}$ 和 $\sum_iL_{ii}/M_{ii}$。实指数单射，故对每个 $t\ge0$，
$$
\phi(t)=ct,\qquad
c=\frac{\operatorname{tr}(N^{-1}L)}{\operatorname{tr}(M^{-1}L)}>0.
$$
行列式这一步只确定共同时间尺度。将已得的线性时间代回完整矩阵等式，在零处取右导数得到
$$
(N^{-1}-cM^{-1})L=0.
$$
因前一因子为对角矩阵，比较第 $i$ 个对角元并用 $L_{ii}>0$，得 $N_{ii}^{-1}=cM_{ii}^{-1}$，即 $N=M/c$。反向代入指数立即得式（18.3）。容量总和相同使 $\operatorname{tr}M/c=\operatorname{tr}M>0$，故 $c=1$。本证明只使用主卷第123.4节的图核与正对角性质及有限维矩阵指数恒等式，不另加能量或熵演化假设。$\square$

**命题 18.3（物理强迫、端口归一化与换钟密度）。** 在定义18.1的制备条件下，固定物理 $B,H$ 给
$$
o_M(t)=\int_0^t K_M(t-s)u(s)\,ds,\qquad
K_M(t)=H S_M(t)M^{-1}B.
\tag{18.5}
$$
因此对 $N=M/c$，
$$
\boxed{K_N(t)=cK_M(ct).}
\tag{18.6}
$$
当 $H=B^*$ 时，令 $C_M=M^{-1/2}LM^{-1/2}$、$J_M=M^{-1/2}B$，则
$$
K_M(t)=J_M^*e^{-tC_M}J_M,\qquad
\lim_{t\to\infty}K_M(t)
=\frac{B^*\mathbf1\mathbf1^*B}{\mathbf1^*M\mathbf1}.
\tag{18.7}
$$
若 $B^*\mathbf1\ne0$，极限非零，未阻尼的 $\int_0^\infty K_M(t)dt$ 不为有限算子积分。特别地，端点端口 $B=e_i$ 保留零模态，不能直接套用恢复几何卷假设15.1及推论16.5的严格正谱积分公式。

对于同一既有响应的时间重标 $t=c\tau$，输入密度必须按本卷定理12.7、恢复几何卷命题15.9运输：
$$
o_M(c\tau)=\int_0^\tau K_M(c(\tau-\sigma))\,
[c\,u(c\sigma)]\,d\sigma.
\tag{18.8}
$$
等价地，在容量 $N=M/c$、输入 $u_N(\sigma)=u(c\sigma)$ 的物理系统中，$o_N(\tau)=o_M(c\tau)$，Jacobian 因子 $c$ 已由 $K_N$ 承担。一般 $C^1$ 严格递增换钟 $\phi$，$\phi(0)=0,\phi'>0$，给同一强迫接口的两时核
$$
o_M(\phi(t))=\int_0^t
\underbrace{\phi'(s)K_M(\phi(t)-\phi(s))}_{\text{相对于 }ds\text{ 的两时核}}
\,u(\phi(s))\,ds.
\tag{18.9}
$$
一个标量曲线 $a k(\phi(t))$ 本身不自动是此强迫接口的脉冲响应密度。

**证明。** 对式（18.2）应用有限维变常数公式得式（18.5）。定理18.2给 $S_N(t)=S_M(ct)$，又有 $N^{-1}=cM^{-1}$，故式（18.6）成立。相似变换
$$
M^{-1}L=M^{-1/2}C_M M^{1/2}
$$
给式（18.7）的对称坐标表达。主卷第123.4节的连通图核结论给 $\ker C_M=\mathbb R M^{1/2}\mathbf1$；谱定理使 $e^{-tC_M}$ 趋向此直线的正交投影，代入得到极限。若 $B^*\mathbf1\ne0$，可取端口向量使该极限的二次型严格正，其时间积分发散，因而算子积分不收敛。式（18.8）与式（18.9）直接应用既有时间运输的积分换元，分别用 $s=c\sigma$ 和旧时间 $s_{\rm old}=\phi(s)$。相应运输状态满足 $d[x_M(\phi(t))]/dt=\phi'(t)[-M^{-1}Lx_M(\phi(t))+M^{-1}Bu(\phi(t))]$，所以输入与生成元同受时间 Jacobian 作用。$\square$

**命题 18.4（三节点端口的完整可见与不可见参数）。** 取单位边权三节点路径
$$
L=\begin{pmatrix}1&-1&0\\-1&2&-1\\0&-1&1\end{pmatrix},\qquad
M_r=\operatorname{diag}(1,r,1),\quad r>0.
\tag{18.10}
$$
固定物理输入、读出为 $B=b,H=b^*$。若 $b=(e_1-e_3)/\sqrt2$，整个响应核为 $e^{-t}$，与 $r$ 无关。若 $b=e_1$，则核为
$$
\boxed{k_r(t)=\frac1{r+2}+\frac12e^{-t}
+\frac{r}{2(r+2)}e^{-(1+2/r)t},}
\tag{18.11}
$$
从而
$$
k_r(0)=1,\qquad k_r'(0)=-1,\qquad
k_r''(0)=1+\frac1r,\qquad k_r(\infty)=\frac1{r+2}.
\tag{18.12}
$$
因此同一图族中，一个固定端口对局部容量完全失明，另一个固定端口的时间关系却含有该容量。可见谱随 $r$ 改变且包含零率，故这个参数族不是恢复几何卷第15节固定严格正谱元组的实例。

**证明。** 广义特征问题 $Lq=\lambda M_rq$ 的三组向量与特征值可取
$$
q_0=(1,1,1)^*,\quad\lambda_0=0;\qquad
q_1=(1,0,-1)^*,\quad\lambda_1=1;\qquad
q_2=(1,-2/r,1)^*,\quad\lambda_2=1+2/r.
$$
它们关于 $\langle v,w\rangle_{M_r}=v^*M_rw$ 两两正交，平方范数依次为 $r+2,2,2(r+2)/r$。命题18.3的对称谱表示等价于
$$
b^*S_{M_r}(t)M_r^{-1}b
=\sum_{j=0}^2e^{-\lambda_jt}
\frac{(b^*q_j)^2}{q_j^*M_rq_j}.
$$
对反对称端口，只有 $j=1$ 的项非零，其权为一；对端点 $e_1$，三个分子均为一，得到式（18.11）。对有限指数和逐项求导给
$$
-k_r'(0)=\frac12+\frac{r}{2(r+2)}\frac{r+2}{r}=1,
\qquad
k_r''(0)=\frac12+\frac{r+2}{2r}=1+\frac1r.
$$
零时值及无穷极限也由式（18.11）直接得到。这里端点的零模态和随 $r$ 改变的正率都是实际物理端口的谱项；比较未知 $r$ 时须使用精确参数纤维，或另证紧凸联合像，或仅使用明确的外界，不能以固定谱的凸合同替换该族。$\square$

**定理 18.5（固定原点的未知增益与常钟率下取得局部容量）。** 在命题18.4的端点制备及物理端口条件下，假设实际取得整条标量响应的零时值、右一阶及右二阶导数。令
$$
F(t)=a k_r(ct),\qquad a,c,r>0,
$$
其中增益 $a$、共同钟率 $c$ 均为未知常数，零标签对应同一经过时间原点。则
$$
\boxed{I=\frac{F(0)F''(0)}{(F'(0))^2}=1+\frac1r>1,\qquad
r=\frac1{I-1}.}
\tag{18.13}
$$
逆映射的局部导数绝对值为 $r^2$。若真实 $I$ 与估计 $\widehat I$ 均不小于 $1+\delta$，$\delta>0$，则
$$
\left|\frac1{\widehat I-1}-\frac1{I-1}\right|
\le\frac{|\widehat I-I|}{\delta^2}.
\tag{18.14}
$$
这是已获得导数关系后的逆误差界，不提供由有限带噪样本估计导数的结论。

**证明。** 式（18.12）及链式法则给 $F(0)=a,F'(0)=-ac,F''(0)=ac^2(1+1/r)$，分母非零，约去 $a^2c^2$ 得式（18.13）。微分 $r(I)=(I-1)^{-1}$ 得 $|r'(I)|=(I-1)^{-2}=r^2$；两个倒数之差的分母为 $(\widehat I-1)(I-1)\ge\delta^2$，给式（18.14）。

这些等式依赖实际零时及导数访问、共同时间原点和固定制备。条件制备、增益恒定及导数误差合同须分别声明；完整曲线的数学存在不赋予这些取得能力。改变 $M_r$ 改变来源动力学，移动读出位置或改变 $B,H$ 改变取得映射。命题18.4的两个固定端口正好区分这两种改变，且不从单端口取得推断一般未知图的识别。$\square$

**命题 18.6（非线性钟的二阶混淆与全曲线极限）。** 保留命题18.4的端点族与未知常增益 $a>0$，设 $\phi:[0,\infty)\to[0,\infty)$ 在零处二次可微，$\phi(0)=0,\phi'(0)>0$。对标量观测 $F(t)=a k_r(\phi(t))$，有
$$
\boxed{\frac{F(0)F''(0)}{(F'(0))^2}
=1+\frac1r-\frac{\phi''(0)}{(\phi'(0))^2}.}
\tag{18.15}
$$
这只给二阶关系中的容量—钟曲率混淆。若另有 $\phi(t)\to\infty$，并具有完整曲线的极限访问，则
$$
\boxed{\frac{F(\infty)}{F(0)}=\frac1{r+2},\qquad
r=\frac{F(0)}{F(\infty)}-2.}
\tag{18.16}
$$
所以式（18.15）不推出任意非线性钟下的全曲线不可识别性。对比值 $J=1/(r+2)$，若 $J,\widehat J\ge\delta>0$，其反演误差同样至多为 $|\widehat J-J|/\delta^2$；该条件不估计无穷极限。

**证明。** 链式法则与式（18.12）给
$$
F'(0)=-a\phi'(0),\qquad
F''(0)=a\left[(1+1/r)(\phi'(0))^2-\phi''(0)\right].
$$
代入并约分得式（18.15）。在只给零处二阶数据时，任取两个正参数 $r,\widetilde r$ 和同一个 $p>0$，把第二条钟的二阶导数改为
$$
\widetilde\phi''(0)=\phi''(0)+p^2(1/\widetilde r-1/r),
\qquad\widetilde\phi'(0)=p=\phi'(0),
$$
即可使两条曲线的零、一、二阶数据相同；这些钟的二阶展开在充分小的右邻域保持正导数。此构造仅匹配二阶数据。若另要求钟趋于无穷，式（18.11）的两个正率项趋零，$F(\infty)=a/(r+2)$，约去 $F(0)=a$ 即得式（18.16）。倒数差给所述误差界。导数访问、极限访问、常增益、制备和误差稳定性是各自独立的假设；式（18.9）还表明该标量重标曲线不应未经输入密度运输就当作非线性换钟的强迫核。$\square$

**命题 18.7（时变容量的两种关系律）。** 取同一固定图 $L$、可微正对角 $M(t)$ 及可微状态 $x(t)$，定义加权总量 $m(t)=\mathbf1^*M(t)x(t)$。若演化律为 $M(t)\dot x(t)=-Lx(t)$，则 $\dot m(t)=\mathbf1^*\dot M(t)x(t)$；若演化律为 $d(M(t)x(t))/dt=-Lx(t)$，则 $\dot m(t)=0$。**证明。** 对第一式使用乘积法则，再用 $\mathbf1^*L=0$；对第二式左乘 $\mathbf1^*$ 即得两项结论。容量为常值时，两种演化律一致；定理18.2比较的是常值容量。$\square$

## 18.99 追加锚

## 19. 共同跳链的路径钟与容量读数距离

**定义 19.1（固定导纳与有限正容量）。** 设 `V` 有限，图连通且至少有两个顶点。令 `w_ij=w_ji≥0`、`w_ii=0`，正权边组成该连通图；记

$$
d_i=\sum_j w_{ij}>0,\qquad
L_{ii}=d_i,\quad L_{ij}=-w_{ij}\quad(i\ne j),
$$
$$
M=\operatorname{diag}(m_i),\qquad
N=\operatorname{diag}(n_i),\qquad m_i,n_i>0.
$$

以行生成元作用于函数的约定，

$$
(Q_Mf)(i)=\frac1{m_i}\sum_jw_{ij}(f(j)-f(i)),
\qquad Q_M=-M^{-1}L.
$$

从 `i` 离开的速率是 `λ_i^M=d_i/m_i`，平均停留时间 `m_i/d_i`；离开后跳到 `j` 的条件概率

$$
P_{ij}=\frac{w_{ij}}{d_i}
\tag{19.101}
$$

与 `M` 无关。

这里 `e^{tQ_M}f(i)=E_i[f(X^M_t)]` 是向后半群，解 `M ḟ=−Lf`。若 `p` 是列概率质量，则它解向前方程

$$
\dot p=Q_M^Tp=-LM^{-1}p,
\qquad \sum_i p_i=1.
$$

不能把质量 `p` 和相对参考密度/状态函数混作同一坐标。

这一生成元沿用[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第123.4节。路径换钟的成熟背景为 Andres–Deuschel–Slowik, *Heat kernel estimates and intrinsic metric for random walks with general speed measure under degenerate conductances*, arXiv:1711.11119v2，式(1.1)及其后关于速度测度的说明；以下只使用有限图。

**定理 19.2（同一跳链、指数等待与路径换钟）。** 定义19.1的两份容量可以耦合在同一随机来源上，使 $X^N(t)=X^M(A^{-1}(t))$，其中 $A(s)=\int_0^s n_{X^M_u}/m_{X^M_u}\,du$。

证明。在同一个概率空间上取：

- 初态 `Z₀` 服从任意指定的共同分布 `ν`；
- 从该初态开始、转移矩阵为式（19.101）的离散 Markov 跳链 `Z₀,Z₁,…`；
- 与整条跳链独立的 iid 随机数 `E₀,E₁,…∼Exp(1)`。

对两份容量使用**同一** `Z_k,E_k`，定义

$$
H_k^M=\frac{m_{Z_k}}{d_{Z_k}}E_k,
\qquad
H_k^N=\frac{n_{Z_k}}{d_{Z_k}}E_k,
$$
$$
T_0^M=T_0^N=0,\qquad
T_k^M=\sum_{j<k}H_j^M,\quad
T_k^N=\sum_{j<k}H_j^N.
$$

在 `[T_k^M,T_(k+1)^M)` 上置 `X^M_s=Z_k`，`N` 链同理。给定当前访问状态 `i`，`H_k^M` 是速率 `d_i/m_i` 的指数等待，与该次下一跳选择独立，故这正是生成元 `Q_M` 的链。`N` 链同理具有生成元 `Q_N`。

有限性和严格正容量给

$$
0<\min_i\frac{m_i}{d_i}\le\max_i\frac{m_i}{d_i}<\infty,
$$

`N` 也一样。iid 正指数变量之和几乎处处发散，所以两组跳跃时刻都趋于无穷；等价地，有限最大退出速率给标准非爆炸保证。每个有限时间窗只有有限次跳跃，右连续路径在所有非负时间上定义。

这项构造是数学耦合，建立在同一完整随机来源上。它不证明两次实际实验天然共享相同随机数；若要将耦合解释为可执行实验转换，还须提供合法制备、干预与数据取得合同。

继续核对时钟的方向。

令 `α_i=n_i/m_i`，有限正容量给常数

$$
0<\alpha_{\min}\le\alpha_i\le\alpha_{\max}<\infty.
$$

于是逐路径

$$
A(s)=\int_0^s\alpha_{X^M_u}\,du
$$

连续、严格递增，满足 `α_min s≤A(s)≤α_max s`，且趋于无穷。因此它有唯一连续严格递增逆函数 `T(t)=A⁻¹(t)`，对所有 `t≥0` 定义。

在第 `k` 段停留区间，`A` 的斜率是 `n_(Z_k)/m_(Z_k)`，所以

$$
A(T_{k+1}^M)-A(T_k^M)
=\frac{n_{Z_k}}{m_{Z_k}}H_k^M
=H_k^N.
$$

从零点累加即得

$$
\boxed{A(T_k^M)=T_k^N,\qquad
X^M(A^{-1}(t))=X^N(t).}
\tag{19.102}
$$

等式包括跳跃时刻，采用上述右连续区间约定。记 $Y_t=X^M(A^{-1}(t))$，由该恒等式，$Y$ 恰有生成元 $Q_N$。形式上逆钟的几乎处处导数为

$$
T'(t)=\frac{m_{Y_t}}{n_{Y_t}},
$$

对应生成元的逐行缩放 `Q_N=diag(m_i/n_i)Q_M`。若容量增加为 `N=αM`，则 `A(s)=αs`、`Y_t=X^M_(t/α)`，与生成元 `Q_N=Q_M/α` 一致。

一般 `A` 依赖实际访问状态，且与轨迹相关。它是适应于该路径的连续加性泛函；逆钟可作原过滤族的停止时刻，时间改变后的过程使用相应改变的过滤族。此处的 Markov 性与生成元已经由共同指数等待构造直接认证，不必假设任意随机换钟都会保持 Markov 性。

逆向重建也使用同一路径：

$$
A^{-1}(t)=\int_0^t\frac{m_{Y_v}}{n_{Y_v}}\,dv.
$$

不能将 `A` 单独抽样后与另一条独立的 `X^M` 组合：那一般不再给式（19.102）的联合律。

有限图的全时间结论不能仅凭“每个顶点容量为正”搬到无限图。无限图还须另证原链非爆炸及 `A(s)→∞`；没有全局正下界的比率可能把无限原时间压缩到有限新时间。本节的有限性已排除这些问题。

**命题 19.3（跳跃顺序、时间占据与初始律）。** 耦合逐路径保留完整的访问状态序列，包括事件顺序、按跳数计的到达位置及不依赖等待时间的首次命中事件。实际第 `k` 次跳跃时刻由 `T_k^M` 变成 `T_k^N`；固定物理时刻前的跳数、定时状态分布、停留时长和时间折扣量一般改变。

证明。对不同顶点 $i,j$，两条链分别满足详细平衡：

$$
\pi_i^M=\frac{m_i}{\sum_jm_j},\qquad
\pi_i^MQ_M(i,j)=\frac{w_{ij}}{\sum_km_k}
=\pi_j^MQ_M(j,i),
$$

`N` 的唯一平稳分布则是 `π_i^N=n_i/Σn`。总概率守恒并未丢失；变化的是同一条访问序列在时间轴上的驻留比例。

跳链自己的不变分布是

$$
\widehat\pi_i=\frac{d_i}{\sum_jd_j},
$$

与容量无关。它描述按访问次数计的平稳权重；不等于连续时间链的时间占据分布。有限图跳链可以有周期，不能因此附带声称其每步边缘律总是收敛。

对角项的平衡等式恒真，连通性使链不可约，有限不可约链的平稳分布唯一。沿各停留段对 $t=A(s)$ 换元，时间占据的转换有精确 Jacobian：对任意状态函数 `g` 和原时间终点 `S`，

$$
\boxed{
\int_0^{A(S)}g(Y_t)\,dt
=\int_0^Sg(X^M_s)\frac{n_{X^M_s}}{m_{X^M_s}}\,ds.
}
\tag{19.103}
$$

结合有限不可约连续时间链的遍历定理（Norris, *Markov Chains*, Cambridge University Press, 1997，第3章），归一化时间占据由 `π^M_i` 乘 `n_i/m_i` 后再归一化，正好得到 `π^N_i`。

初始分布必须另行保留：式（19.102）的耦合有 `Y₀=X₀^M`。若原链从 `π^M` 启动，新链也从 `π^M` 启动，通常**不是**从 `π^N` 启动。不能仅凭路径换钟声称两边从各自稳态启动且仍共享同一初态。要构造新链的平稳版本，须使用正确初始律或相应的时间原点加权；这与现有同初态耦合是不同的准备合同。

**命题 19.4（随机路径钟与完整半群钟的不同量词）。** 确定共同钟要求一个不依赖初态、随机实现或观测端口的函数 `φ`，使

$$
e^{tQ_N}=e^{\phi(t)Q_M}\quad\text{对全部 }t\ge0
$$

作为算子恒等。固定非平凡连通图时，由本卷定理18.2，该条件只容许 `N=M/c`、`φ(t)=ct`。比例情形恰是式（19.102）中状态无关的特例。

非比例时，定理19.2给出的却是

$$
e^{tQ_N}f(i)=E_i^M\big[f(X^M_{A^{-1}(t)})\big],
$$

其中随机时间 `A⁻¹(t)` 与该路径共同生成。一般不能将它改成 `e^{E[A⁻¹(t)]Q_M}`，也不能仅按随机时间的边缘分布对 `e^{sQ_M}` 作独立混合：给定停止时间的事件会同时改变路径的条件律。

因此“状态路径可由依赖路径的钟对应”不推出“平均热场在同一时刻相同”，更不推出固定输入、固定读出、固定采样表的响应核相同。它允许相同跳跃关系与不同相对衰减谱同时存在，也允许先前的三点路径例子中确定性状态场轨迹方向随容量改变。

**命题 19.5（粗读数上的钟可识别条件与反例）。** 若完整记录给出了全部真实跳跃状态、跳跃时刻以及同源已知的 `m,n`，则可以逐段重建 `A`，并给旧事件附上新标签 `A(T_k^M)`。旧时间、原始记录和来源身份必须保留，不能用新标签覆盖掉原来已经取得的实验事实。重标同一事件也不等于在新钟的等距时刻重新采样。

对粗读出 `h:V→O`，一个直接充分条件是比率在每个读出纤维上恒定：

$$
\alpha_i=\bar\alpha(h(i)).
$$

若完整连续读出及其原时间戳可取得，则

$$
A(s)=\int_0^s\bar\alpha(h(X^M_u))\,du
$$

可以从该读出计算。仅有有限离散时刻的读数仍不自动给出所有区间内驻留时间，需另有取得或估计证书。

相反，若存在仍被完整档案允许的 `i,j`，满足 `h(i)=h(j)` 但 `n_i/m_i≠n_j/m_j`，并允许它们作为备选初态，那么在一个固定正时间窗内“不跳跃”的事件在两种初态下分别具有概率 $e^{-d_iS/m_i}>0$、$e^{-d_jS/m_j}>0$，其中 $S>0$ 是窗口长度。两份完整粗读出都是同一个常值时间记录，却有

$$
A_i(s)=(n_i/m_i)s\ne(n_j/m_j)s=A_j(s).
$$

于是该粗读出本身不确定路径钟。这个例子针对所列允许状态与记录纤维；若旧档案已经识别了初态、提供了内部轨迹或排除了其中一份实现，必须把这些信息一起使用，不能删除它们来制造不可识别性。

局部响应核还可能连某些动力学模式都看不见。例如三点路径 `M_r=diag(1,r,1)` 的固定端口 `u=(1,0,−1)/√2` 对所有 `r` 都给核 `e^(−t)`，但这既不提供实现路径钟所需的状态驻留信息，也不使完整状态半群相同。可见平均响应、一次实际路径及其时钟是不同的观测对象，必须保持各自的共同来源关系。

移动观察者、改变端口或主动制备若改变导纳、容量、干预规则或读取权限，已经改变定义19.1的固定模型/取得合同。数学上存在这个换钟，不赋予观察者访问隐藏状态、修改真实等待时间或执行相同随机来源的能力。

**命题 19.6（能量恒等与容量规范）。** 固定有限连通图 `V`，至少两个顶点。边上 `w_xy=w_yx>0`，无边为零，`w_xx=0`；顶点容量 `m_x>0`。记

$$
d_x=\sum_yw_{xy},\quad L=D^{\mathsf T}WD,
\quad (Q_mf)(x)=\frac1{m_x}\sum_yw_{xy}(f(y)-f(x))=(-M^{-1}Lf)(x).
$$

把 $\langle f,g\rangle_m=\sum_xm_xf(x)g(x)$ 固定为参考内积；对称导纳使每条无向边的两项相加为平方差乘积，因此同一能量形式为

$$
\mathcal E_w(f,g)=\sum_{\{x,y\}\in E}w_{xy}(f(y)-f(x))(g(y)-g(x))
=\langle f,-Q_mg\rangle_m.
\tag{19.111}
$$

固定 `w` 时，能量形式的这一表达不随 `m` 改变；改变的是参考内积、生成元和下面读数的局部预算。顶点 `x` 的退出速率是 `d_x/m_x`，平均停留时间是 `m_x/d_x`，跳到 `y` 的条件概率 `w_xy/d_x` 不变。

整体缩放 `n=αm` 给出精确关系

$$
Q_{\alpha m}=Q_m/\alpha,\qquad
e^{tQ_{\alpha m}}=e^{(t/\alpha)Q_m},\qquad
H_k^{\alpha m}=\alpha H_k^m
\tag{19.112}
$$

（最后一式使用同一跳链、同一指数等待随机数）。若一般容量满足

$$
0<a\le n_x/m_x\le b<\infty\quad\text{对所有 }x,
\tag{19.113}
$$

则定理19.2的共同路径换钟

$$
A(s)=\int_0^s\frac{n_{X^m(u)}}{m_{X^m(u)}}\,du
$$

满足 `as≤A(s)≤bs`、`t/b≤A⁻¹(t)≤t/a`，每次共同访问的等待时间也满足 `aH_k^m≤H_k^n≤bH_k^m`。非比例时，这不是一个所有初态和路径通用的确定时钟，不给半群逐项大小排序。

[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第123.4节 使用归一化概率参考 `μ`。本题保留任意正容量的绝对尺度；若令 `μ=m/Σm`，要保留 `Q_m` 就须同时把边导纳改成 `w/Σm`。只归一化容量会改变时钟，不能省略总容量因子。

**定义 19.7（截断逐边长度的路径距离）。**

令

$$
r_m(e)=\frac{\min(m_x,m_y)}{w_{xy}},\qquad
\ell_m(e)=\sqrt{\min\{1,r_m(e)\}}
\quad(e=\{x,y\}),
$$
$$
\boxed{\ d_m^{\rm ADS}(i,j)=\inf_{\gamma:i\leadsto j}\sum_{e\in\gamma}\ell_m(e).\ }
\tag{19.114}
$$

这正是论文取 `θ=m, ω=w` 的式 (1.2)。`1` 与**整个比值**取最小值，不是把容量先与 1 取最小值再除以导纳。有限连通图与正边长使它成为有限距离，且 `d_m^{ADS}≤d_graph`。

**命题 19.8（逐边对偶、缩放与截断）。** Andres–Deuschel–Slowik 的 Proposition 2.3 给精确对偶形式

$$
d_m^{\rm ADS}(i,j)=\sup\left\{f(j)-f(i):
|f(y)-f(x)|\le1,\quad
w_{xy}|f(y)-f(x)|^2\le\min(m_x,m_y)\quad\forall\{x,y\}\in E\right\}.
\tag{19.115}
$$

这是**逐边**约束。论文的 `dΓ^ω(f,f)(e)=w_e(Df(e))²` 是这里的边能量读数；它不是下一节把所有邻边在一个顶点相加的预算。使用论文的 intrinsic 名称时必须保留这份定义。比如三叶单位星、全部容量为 1 时，式（19.114） 是图距离，中心的 `Σ_y w_xy d(x,y)²=3>2m_x`，所以仅引用论文名词也不能推出本题的顶点平方和条件。

证明。整体容量缩放时的准确式子是

$$
\ell_{\alpha m}(e)=\sqrt{\min\{1,\alpha r_m(e)\}}.
\tag{19.116}
$$

因此

$$
\min\{1,\sqrt\alpha\}\,d_m^{\rm ADS}
\le d_{\alpha m}^{\rm ADS}
\le\max\{1,\sqrt\alpha\}\,d_m^{\rm ADS}.
\tag{19.117}
$$

若所有边在缩放前后都未超过截断，即 `max{1,α}r_m(e)≤1`，则所有边长共同乘以 `√α`，这时才有全距离的 `d_{αm}^{ADS}=√α d_m^{ADS}`。这是一个明确充分条件，不是逐点相等的必要条件。反例只需一条权为 1、两端容量为 1 的边：容量乘以 4 后，等待时间乘以 4，但距离仍为 1，不是 2。有限图上，当 `α≥max_e w_e/min(m_x,m_y)` 时，所有边长均为 1，距离恰为图距离，继续增加容量不再改变这份截断距离。

一般比率合同 （19.113） 给

$$
\boxed{\ \min\{1,\sqrt a\}\,d_m^{\rm ADS}
\le d_n^{\rm ADS}
\le\max\{1,\sqrt b\}\,d_m^{\rm ADS}.\ }
\tag{19.118}
$$

依据是逐边 `a r_m(e)≤r_n(e)≤b r_m(e)`，对 `min(1,·)` 保留截断后再对路径求和、取下确界。不能省去式（19.118） 两侧的 `min/max`。

**定义 19.9（同一顶点预算的能量读数距离）。**

现在独立定义

$$
\mathcal F_m=\left\{f:V\to\mathbb R:
\sum_yw_{xy}(f(y)-f(x))^2\le2m_x\quad\forall x\right\},
$$
$$
\boxed{\ D_m(i,j)=\sup_{f\in\mathcal F_m}|f(i)-f(j)|.\ }
\tag{19.119}
$$

**定理 19.10（能量读数距离与容量比较）。** 等价地，`Γ_m(f)(x)=(2m_x)⁻¹Σ_yw_xy(f(y)−f(x))²≤1`；因子 2 在这里固定，不与论文的逐边约定混用。所有点对使用同一个 `𝓕_m`，因此直接承接本卷定理2.2的固定读数族上确界伪度量结构。可行函数在每条边的差不超过 `√[2min(m_x,m_y)/w_xy]`，连通性给有限的路径上界。取 $\delta=\min_x\sqrt{2m_x/d_x}>0$，函数 $\delta\mathbf1_{\{i\}}$ 在每个顶点的平方差和不超过 $\delta^2d_x\le2m_x$，且分离 $i$ 与任意其他顶点。因此在当前有限连通模型上它确为距离。

它没有逐边 `1` 截断，齐次性准确给出

$$
\mathcal F_{\alpha m}=\sqrt\alpha\,\mathcal F_m,
\qquad
\boxed{\ D_{\alpha m}=\sqrt\alpha\,D_m.\ }
\tag{19.120}
$$

对 （19.113），同一个可行集包含关系

$$
\sqrt a\,\mathcal F_m\subseteq\mathcal F_n
\subseteq\sqrt b\,\mathcal F_m
$$

给出

$$
\boxed{\ \sqrt a\,D_m(i,j)\le D_n(i,j)\le\sqrt b\,D_m(i,j).\ }
\tag{19.121}
$$

这些是对同一组 `w`、同一顶点及整体可行读数族的比较；无需把不同点对的最优读数认作同一函数。

**命题 19.11（逐对上确界不保留同一顶点预算）。**

取路径 `0—1—2`，两条导纳和三个容量都为 1。可行性恰要求

$$
(f_0-f_1)^2\le2,\quad
(f_0-f_1)^2+(f_2-f_1)^2\le2,\quad
(f_2-f_1)^2\le2.
$$

| 标识 | 点对 | 精确距离 | 达到上界的读数 `(f₀,f₁,f₂)` | 三个顶点的平方和 |
| --- | --- | --- | --- | --- |
| 19.11表1行1 | `(0,1)` | `√2` | `(√2,0,0)` | `(2,2,0)` |
| 19.11表1行2 | `(1,2)` | `√2` | `(0,0,√2)` | `(0,2,2)` |
| 19.11表1行3 | `(0,2)` | `2` | `(1,0,−1)` | `(1,2,1)` |

前两项上界来自单边约束，第三项上界来自 `(f₀−f₂)²≤2[(f₀−f₁)²+(f₂−f₁)²]≤4`，所以表中等式全部是精确结果。中心顶点却有

$$
\boxed{\ \sum_yw_{1y}D_m(1,y)^2=2+2=4>2=2m_1.\ }
\tag{19.122}
$$

甚至距离函数 `g(y)=D_m(1,y)` 本身也不属于 `𝓕_m`。逐对最优函数分别花满中心预算，但不能同时占用这两份预算；将每个坐标的上确界拼成向量正是失效步骤。它不影响三角不等式，因为对每个固定可行函数，三角界由同一函数给出，再对单个左端取上确界即可。

同一三点模型中，论文距离的相邻值均为 1、端点值为 2；能量读数距离的相邻值均为 `√2`、端点值为 2。因此两者甚至不是在这个实例上相差一个共同常数。

**推论 19.12（同一容量尺度的时间与距离平方）。** 在固定导纳下，$m\mapsto\alpha m$ 使定理19.2的每次等待乘 $\alpha$、定理19.10的 $D_m^2$ 乘 $\alpha$；定义19.7的截断距离仅在命题19.8的未截断条件下具有同一齐次关系。证明。分别代入所引三项的缩放公式即得。一般 $am\le n\le bm$ 时，路径钟满足 $as\le A(s)\le bs$，能量距离满足 $\sqrt aD_m\le D_n\le\sqrt bD_m$，截断距离保留命题19.8的最小值、最大值因子。这些是指定生成元与两种指定距离的数学关系，不是命中时间等式或物理速度定律；可行读数的上确界也不表示这些读数已被共同取得。$\square$

## 20. 非线性共同钟的有限纤维与完整历史

**假设 20.1（有限端点记录与自由光滑钟）。** 使用命题18.4的 $k_r$，$r>0$，同源响应为 $F(s)=a k_r(\phi(s))$，$a>0$。真实零点、稳定增益、制备和全部旧档案按[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)假设19.1保留。当前有限记录是
$$
0=s_0<s_1<\cdots<s_n<\infty,\qquad
1=z_0>z_1>\cdots>z_n>0,\qquad F(s_i)=az_i.
$$
钟类暂取 $\phi\in C^\infty([0,\infty))$，$\phi(0)=0$，$\phi'>0$，$\phi(s)\to\infty$。$n=0$ 时相邻不等式为空。以下精确纤维针对所列记录；若旧档案另有钟或来源限制，须与其共同相交，不能用本节纤维覆盖旧信息。

**定理 20.2（任意有限前缀的精确参数投影）。** 在假设20.1且无其他限制时，相容参数恰为
$$
\mathcal R_D=\{r>0:p_r<z_n\}
=\bigl(\max\{0,z_n^{-1}-2\},\infty\bigr),\qquad p_r=\frac1{r+2}.
\tag{20.101}
$$
相容性的量词是对每个候选 $r$ 存在一条可依赖 $r$ 的共同钟，拟合该份全部有限记录。

证明。由命题18.4，$k_r(0)=1$，$k_r'(t)=-(e^{-t}+e^{-(1+2/r)t})/2<0$，$k_r(t)\to p_r$，且每个有限 $t$ 有 $k_r(t)>p_r$。因此 $k_r:[0,\infty)\to(p_r,1]$ 连续严格递减双射。有限标签只能给有限内部时间，故 $z_n>p_r$ 必要，等号不能拟合。

反之，设 $n\ge1$ 且 $p_r<z_n$。令 $t_i=k_r^{-1}(z_i)$，则 $0=t_0<t_1<\cdots<t_n<\infty$。写 $\Delta s_i=s_i-s_{i-1}$、$\Delta t_i=t_i-t_{i-1}$，选择
$$
0<\varepsilon<\min_{1\le i\le n}\frac{\Delta t_i}{\Delta s_i}.
$$
在每个开区间 $(s_{i-1},s_i)$ 取非负、积分为一的 $C_c^\infty$ 隆起函数 $b_i$，向区间外延拓为零，置
$$
d(s)=\varepsilon+\sum_{i=1}^n(\Delta t_i-\varepsilon\Delta s_i)b_i(s),
\qquad \phi(s)=\int_0^s d(u)\,du.
\tag{20.102}
$$
每个系数正，故 $d\ge\varepsilon>0$；紧支撑严格位于区间内部，零延拓及其有限和在全部标签和原点光滑。每段积分为 $\varepsilon\Delta s_i+\Delta t_i-\varepsilon\Delta s_i=\Delta t_i$，所以 $\phi(s_i)=t_i$。末点以后 $\phi(s)=t_n+\varepsilon(s-s_n)$，故无界。若 $n=0$，直接取 $\phi(s)=s$，不对空集取最小值。全部正参数均满足 $p_r<z_0=1$。这证明充分性。

若 $z_n<1/2$，记录给严格下界 $r>z_n^{-1}-2$；若 $z_n\ge1/2$，每个正参数都相容。早期数值和时间间隔约束插值钟，但在此钟类中不给额外的 $r$ 限制。这沿用恢复几何卷引理15.8的单调反演机制；该引理严格正生成元的零平台值域在这里换成精确的 $(p_r,1]$，不搬用其原值域。$\square$

**命题 20.3（完整无界历史与有限前缀的量词差）。** 若 $s_j\to\infty$ 且一对 $(r,\phi)$ 同时实现所有记录，则
$$
\ell=\lim_j z_j=p_r,\qquad r=\ell^{-1}-2,\qquad 0<\ell<1/2.
$$
但每个有限前缀分别有一条无界钟，并不保证全部历史有一条共同钟。

证明。共同钟无界且递增，故 $\phi(s_j)\to\infty$，代入 $k_r$ 的平台极限得到首项。若实际参数为 $r_0$，$z_j\downarrow p_{r_0}$，任意固定 $r>r_0$ 都因 $p_r<p_{r_0}<z_j$ 而通过每个有限前缀。然而此候选所需时间满足
$$
k_r^{-1}(z_j)\longrightarrow k_r^{-1}(p_{r_0})<\infty,
$$
所以不存在在全部 $s_j\to\infty$ 取这些值的无界共同钟。即 $\forall n\,\exists\phi_n$ 不推出 $\exists\phi\,\forall j$。只有无穷多个标签而标签有界时，不能使用这里的平台论证；平台极限也不是有限预算自动取得的样本。$\square$

**定义 20.4（已知共同钟率界）。** 给 $0<m\le M<\infty$，用 $\mathcal C_{m,M}$ 表示全部 $\phi(0)=0$ 且满足
$$
m(v-u)\le\phi(v)-\phi(u)\le M(v-u)\qquad(0\le u\le v)
\tag{20.103}
$$
的连续钟。这等价于局部绝对连续且几乎处处 $m\le\phi'\le M$：一个方向积分导数，另一个方向由 Lipschitz 函数的绝对连续性、几乎处处可微性及差商界得到。特别 $\phi(s)\ge ms$，无界性自动成立。定义 $t_i(r)=k_r^{-1}(z_i)$、$t_0=0$、$\Delta_i(r)=t_i(r)-t_{i-1}(r)$ 和 $L_i=s_i-s_{i-1}>0$，逆仅在 $p_r<z_n$ 时使用。

**定理 20.5（绝对连续钟的精确增量判据）。** 若 $n\ge1$，相容参数集恰为
$$
\mathcal R_{\rm AC}={r>0:p_r<z_n,\quad
mL_i\le\Delta_i(r)\le ML_i\ (1\le i\le n)\}.
\tag{20.104}
$$
$n=0$ 时每个正参数相容。$m=M$ 时唯一钟为 $\phi(s)=ms$，条件化为 $t_i(r)=ms_i$。

证明。对相邻标签应用式（20.103）给必要性。反向，在每段线性插值 $\phi(s_i)=t_i(r)$，斜率 $\Delta_i/L_i\in[m,M]$；末点以后以任意固定 $[m,M]$ 内斜率延伸，即得全域绝对连续钟。两端速率等号允许，但有限时间平台等号不允许。$n=0$ 取任一合法线性钟，$m=M$ 则式（20.103）本身强制唯一钟。

只检查从原点累计的 $ms_i\le t_i\le Ms_i$ 不够。例如 $m=1,M=2,s_1=1,s_2=2,t_1=2,t_2=21/10$ 满足累计界，却有 $t_2-t_1=1/10<1$。任取正 $r$ 并令 $z_i=k_r(t_i)$，就在本模型中实现这些读数及该失败。$\square$

**定理 20.6（光滑钟的饱和邻接判据）。** 设 $m<M$。对固定满足式（20.104）的 $r$，令 $c_i=\Delta_i/L_i$，把 $c_i=m$、$c_i=M$ 分别称为下界、上界饱和。存在全域 $C^\infty$ 钟且处处 $m\le\phi'\le M$，当且仅当不存在两个相邻区间分别饱和于相反端点。

证明。若连续导数 $d\in[m,M]$ 在一段均值为 $m$，则非负连续函数 $d-m$ 积分为零，故该闭段处处 $d=m$；均值为 $M$ 同理。相反饱和邻段在共同端点要求两个不同导数，矛盾。

反向，在每个标签选导数值 $q_j\in[m,M]$。饱和邻段规定它等于其端点界，两侧规定相容恰是所述条件；没有规定时可取 $(m+M)/2$。饱和区间上取常导数。在内点斜率区间，把其长度、目标均值及端点导数写为 $L,c,A,B$，其中 $m<c<M$。取端点附近支撑互不相交的光滑截断 $\rho_0,\rho_1\in[0,1]$，各自近相应端点恒为一，远离端点为零，令
$$
\alpha=\int_0^L\rho_0,\quad\beta=\int_0^L\rho_1,\quad
v=\frac{cL-A\alpha-B\beta}{L-\alpha-\beta}.
$$
缩小支撑使 $\alpha+\beta<L$ 且 $v\in(m,M)$，这是因为 $v\to c$。置
$$
d(u)=v+(A-v)\rho_0(u)+(B-v)\rho_1(u).
\tag{20.105}
$$
支撑不相交使每点是 $v$ 与至多一个端点值的凸组合，故 $m\le d\le M$。积分恰为 $cL$，两端邻域为指定常数，因而各段光滑拼接。末点以后取最后端点的常导数，积分即得所需钟。故严格内点斜率充分但非必要；孤立饱和段及同端饱和邻段均可接受。$m=M$ 已由定理20.5处理。$\square$

**命题 20.7（逆时间增量的参数单调性与闭性）。** 对固定有限记录，每个 $\Delta_i(r)$ 在 $D=\{r>0:p_r<z_n\}$ 连续严格递减。因此 $\mathcal R_{\rm AC}$ 是相对于 $(0,\infty)$ 闭的区间，可为空或单点；其与正参数紧集的交为紧集。光滑可行参数集要么为空，要么恰等于 $\mathcal R_{\rm AC}$。

证明。令 $\lambda_r=1+2/r$，使用恢复几何卷定理19.2的参数导数和命题18.4的时间导数，隐函数求导得
$$
\partial_r k_r^{-1}(z)=-H_r(k_r^{-1}(z)),\qquad
H_r(t)=\frac{2[1-(1+\lambda_rt)e^{-\lambda_rt}]}
{(r+2)^2(e^{-t}+e^{-\lambda_rt})}.
\tag{20.106}
$$
$H_r(0)=0$；分子在 $t>0$ 正且严格递增，其导数除正常数外为 $\lambda_r^2te^{-\lambda_rt}$，正分母严格递减，故 $H_r$ 严格递增。于是
$$
\Delta_i'(r)=-H_r(t_i(r))+H_r(t_{i-1}(r))<0.
$$
连续性由时间导数非零的隐函数定理给出。每项上下界的逆像都是区间；上速率界限制参数下端，下速率界限制参数上端，交仍是区间。

闭性还需检查严格平台边界。若可行 $r_j\to r_*>0$，则 $t_n(r_j)\le Ms_n$，所以 $k_{r_j}(Ms_n)\le z_n$。取极限得 $p_{r_*}<k_{r_*}(Ms_n)\le z_n$。逆时间在该点有定义且连续，所有增量不等式传到极限，故相对闭。

若某个 AC 可行 $r_*$ 有定理20.6的相反饱和邻段，则其中一个增量等于下界，另一个等于上界。严格递减性使每个 $r>r_*$ 违反前者下界、每个 $r<r_*$ 且在 $D$ 内者违反后者上界；$D$ 外已不可行。因此整个 AC 集只有 $r_*$，而光滑集为空。若没有这种候选，全部 AC 可行参数均能光滑实现，证明最后结论。它没有省略饱和条件，也没有断言光滑钟族在局部一致拓扑中闭。$\square$

**定理 20.8（紧参数与共同钟的完整记录实现）。** 固定非空紧集 $K\subset(0,\infty)$。若每个有限记录子集在同一 $K\times\mathcal C_{m,M}$ 中有共同实现，则全部记录有一对共同实现 $(r_*,\phi_*)$。附加约束在此联合拓扑下闭时可以一并保留。

证明。钟取紧区间上一致收敛拓扑。每个钟 $M$-Lipschitz，$[0,T]$ 上取值在 $[0,MT]$，原点与式（20.103）在局部一致极限下闭。直接应用紧开形式的 Arzelà–Ascoli 定理，$\mathcal C_{m,M}$ 紧。其使用条件分别是局部等度连续、逐点紧值界和闭性；无需另证一份一般紧性定理。$K\times\mathcal C_{m,M}$ 亦紧，且每条条件 $k_r(\phi(s_i))=z_i$ 由评价与 $(r,t)\mapsto k_r(t)$ 连续而为闭集。紧集的闭集有限交性质给全部条件的共同点。顺序历史亦可用嵌套非空紧集交定理。极限仍有 $\phi_*(s)\ge ms$，所以无界。

这里复用 Mathlib 的 `ArzelaAscoli.compactSpace_of_isClosedEmbedding` 和 `IsCompact.inter_iInter_nonempty` 所表述的一般紧性结论。每次改变 $K$、丢弃旧记录、只检查各条记录单独可行均不满足共同有限交前提。导数读数不自动对局部一致拓扑连续，需另加相应拓扑合同。上界 $M$ 提供局部有界和等度连续；下界 $m>0$ 使无界性保留；只有各钟分别无界不是闭条件。$\square$

**定理 20.9（局部有限的无界标签上的共同光滑钟）。** 设 $s_j\uparrow\infty$，每个有限前缀在同一紧集 $K\subset(0,\infty)$ 中有光滑可行参数，钟率共同在 $[m,M]$。则有单一 $r_*\in K$ 与单一全域光滑钟实现全部历史。

证明。固定候选 $r$ 时，若每个前缀满足式（20.104），在全部相邻区间分段线性插值已得共同 AC 钟，且 $t_j(r)\ge ms_j\to\infty$。对参数变化的光滑情形，由命题20.7，每个非空前缀光滑参数集等于对应 AC 集，与 $K$ 的交紧且嵌套。嵌套紧交定理给 $r_*$，它满足所有有限前缀的增量和饱和邻接条件。在每个相邻区间按定理20.6构造导数，标签导数依两侧饱和段统一选择。$s_j\to\infty$ 使任一有界区间只有有限接点，近接点的常导数片段保证全域光滑。积分后给共同钟。$m=M$ 时直接取线性钟。

此证明使用参数闭性和显式重建，不把光滑钟的局部一致极限宣称为光滑。命题20.3中固定 $r>r_0$ 的反例在这里必失败于某个有限前缀，因为其必需逆时间有界而 $ms_j\to\infty$。对任何实际共同实现，平台仍唯一确定 $r_*$，并不确定孤立标签之间的钟。$\square$

**命题 20.10（没有紧参数控制时的逃逸）。** 取 $m=1,M=2,s_j=j,z_j=e^{-j}$。每个有限前缀有正有限参数的光滑实现，全部历史却没有任何有限正参数实现。

证明。$r\to\infty$ 时 $k_r(t)\to e^{-t}$；对每个固定 $i$，逆 $t_i(r)\to i$，因而 $\Delta_i(r)\to1$。逆收敛可由严格单调性在 $i\pm\eta$ 两侧夹逼得到。若 $g_r(s)=k_r^{-1}(e^{-s})$ 有定义，$s>0$ 时
$$
g_r'(s)=\frac{k_r(g_r(s))}{-k_r'(g_r(s))}>1,
\qquad k_r(t)+k_r'(t)=p_r(1-e^{-(1+2/r)t})>0.
$$
每个固定前缀的大参数因而同时具有 $1<\Delta_i(r)<2$，由定理20.6光滑可行。但完整 $z_j\to0$，与任何正有限 $r$ 的正平台矛盾。共同钟率界不替代参数紧性。$\square$

**命题 20.11（有限聚点使逐前缀光滑性不能拼接）。** 设 $m<M$，固定 $r_0>0$，令
$$
u=\frac{2m+M}{3},\quad v=\frac{m+2M}{3},\quad
s_i=1-2^{-i}\ (i\ge0),\quad c_i=u,v,u,v,\ldots,
$$
$$
t_0=0,\qquad t_i=\sum_{j=1}^i c_j2^{-j},\qquad z_i=k_{r_0}(t_i).
$$
每个有限前缀在同一紧集 $K=\{r_0\}$ 中光滑可行，整份历史有 AC 实现，却没有 $C^1$ 实现。

证明。全部区间斜率严格在 $(m,M)$，故有限光滑可行由定理20.6给出。逐段线性插值，在 $s=1$ 取连续极限，之后以 $[m,M]$ 内常率延伸，给共同 AC 钟。若有 $C^1$ 钟，严格反演强制 $\phi(s_i)=t_i$，均值定理在每段给 $\xi_i\in(s_{i-1},s_i)$，使 $\phi'(\xi_i)=c_i$。$\xi_i\to1$ 与导数连续性强制两种交替且不同的速率趋于同一极限，矛盾。故一般有聚点历史仅由定理20.8保证 AC 实现；光滑实现还须相容的各阶导数或更强光滑拓扑中的紧闭条件。$\square$

## 21. 同源双端口的内部钟与容量反演

**假设 21.1（固定制备、共同时间与认证读出）。** 令

$$
M_r=\operatorname{diag}(1,r,1),\qquad
L=\begin{pmatrix}1&-1&0\\-1&2&-1\\0&-1&1\end{pmatrix},
\qquad
S_{M_r}(t)=e^{-tM_r^{-1}L},\qquad r>0.
$$

初态位移为 $e_1$，或经已认证的配对制备与相减取得同一位移响应。两个线性读出作用于同一个状态：

$$
u(t)=(e_1-e_3)^{\mathsf T}S_{M_r}(t)e_1=e^{-t},
$$

$$
v(t)=e_1^{\mathsf T}S_{M_r}(t)e_1=k_r(t)
=\frac1{r+2}+\frac12e^{-t}
+\frac{r}{2(r+2)}e^{-(1+2/r)t}.
\tag{21.101}
$$

第一式也由 $(e_1-e_3)^{\mathsf T}M_r^{-1}L=(e_1-e_3)^{\mathsf T}$ 直接核对；其特征衰减率 $1$ 不依赖 $r$。这里的内部时间单位由单位边权和两个单位端点容量决定。若实际导纳整体为 $\kappa L$，而 $\kappa>0$ 未知，则 $-\log u=\kappa t_{\mathrm{external}}$：取得的是尺度乘外部经过时间，不能分离这两个量，也不能认定外部物理秒已校准。

两个通道可以有不同但各自保持不变的未知正增益：

$$
Y_u(s)=g_u e^{-\phi(s)},\qquad
Y_v(s)=g_v k_r(\phi(s)),\qquad g_u,g_v>0.
\tag{21.102}
$$

共同钟满足 $\phi(0)=0$，严格递增；在同一正标签 $s_*>0$ 读取时，两个通道必须对应同一实际经过时间 $t=\phi(s_*)>0$。不要求钟率已知。单点结论不需要钟函数可微；既有光滑无界钟类当然包含在适用范围内。

真实零时刻给 $Y_u(0)=g_u,\ Y_v(0)=g_v$，从而

$$
u=\frac{Y_u(s_*)}{Y_u(0)},\qquad
v=\frac{Y_v(s_*)}{Y_v(0)}.
\tag{21.103}
$$

因此“一个正时刻读数对”是两个额外标量读出，另需各通道的真实零点校准或已认证同源增益。若两个通道共享同一已认证增益，可以复用相应校准；否则不能用一个通道的零点值替另一个通道校准。

$g_u$ 的标量模型还要求整个线性泛函 $(e_1-e_3)^{\mathsf T}$ 已被认证。若用两个独立传感器相减实现它，必须先校准相对权重；$e_1$ 初态在第三坐标的零点值为零，该次零点读取不能校准第三传感器的增益。未经相对校准的差分不能当作(21.102)中的 $g_u u$。

增益漂移、未知加性基线、未建模的后续强迫、不同初态、不同来源或读出扰动均不在(21.102)内。配对制备必须认证相同生成元、相同实际延迟和同一初始位移；两个独立实验拥有相同显示标签并不自动证明这些关系。若两次读出会改变状态，须另行取得同一状态的合法联合读出，或认证等价的配对协议。

这里消去的是共同自由演化时间参数。若实际制备使用外部脉冲，脉冲幅度、输入测度与钟变换的强迫密度因子仍须满足既有运输合同；两个自由演化读出的关系不自动认证这些输入合同。

**定理 21.2（源参数与内部时间的开楔形坐标）。** 在假设21.1下，一个正时刻的已校准同刻读数对唯一恢复 $r>0$ 与该次内部时间 $t>0$，并给下述开楔形的光滑坐标。证明。应用[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定理19.2、19.3的核单调性与逆稳定结果。

消去 $t=-\log u$，得到

$$
\boxed{
v=G_r(u):=\frac1{r+2}+\frac u2
+\frac{r}{2(r+2)}u^{1+2/r},
\qquad 0<u<1.}
\tag{21.104}
$$

因此同一未知非线性钟的具体形式从这一个同刻关系中消去。直接求 $u$ 导数，以及把既有 $\partial_r k_r(t)$ 公式代入 $t=-\log u$，给

$$
\boxed{\partial_uG_r(u)=\frac{1+u^{2/r}}2\in(1/2,1),}
\tag{21.105}
$$

$$
\boxed{
\partial_rG_r(u)
=-\frac{H((1+2/r)(-\log u))}{(r+2)^2}<0,
\qquad H(w)=1-(1+w)e^{-w}.}
\tag{21.106}
$$

这里 $H$ 就是恢复几何卷第19节中的 $h$，换字母仅为避免混同采样间隔。对 $w>0$，$H(w)>0$，且 $H'(w)=we^{-w}>0$。

恢复几何卷定理19.2的端点极限直接成为

$$
\lim_{r\to\infty}G_r(u)=u,\qquad
\lim_{r\downarrow0}G_r(u)=\frac{1+u}{2}.
\tag{21.107}
$$

连续严格反单调性表明，固定 $u\in(0,1)$ 时，$r\mapsto G_r(u)$ 恰把 $(0,\infty)$ 一一映到 $(u,(1+u)/2)$。所以

$$
\boxed{
(r,t)\in(0,\infty)^2
\longmapsto (e^{-t},k_r(t))
}
$$

恰为

$$
\boxed{\mathcal W=\{(u,v):0<u<1,\ u<v<(1+u)/2\}}
\tag{21.108}
$$

的一一参数化。逆像由 $t=-\log u$ 和唯一方程 $G_r(u)=v$ 确定。前向映射光滑，Jacobian 为

$$
\det\frac{\partial(u,v)}{\partial(r,t)}
=u\,\partial_rG_r(u)<0.
$$

直接应用通常的局部反函数定理，并利用已得的全局单射与满射，逆映射在整个 $\mathcal W$ 上光滑。这里的 $\mathcal W$ 是精确的开区域；边界 $v=u$、$v=(1+u)/2$ 分别对应 $r\to\infty$、$r\downarrow0$，不能解释为有限正质量参数。

$t=0$ 时两值同为 $1$，只承担校准而不识别 $r$。$u=0$ 对应无限经过时间极限，不属于一次有限正时刻的读数合同。

**命题 21.3（单个内时点不恢复钟的间隙）。** 第一通道单独对 $r$ 完全不敏感，却给出 $t=-\log u$。第二通道因而成为已知内部时间的核读数，直接进入原有单调反演。参数盲通道的作用是约束另一个通道中的未知时间；没有声称它单独新增了关于 $r$ 的信息。

一个读数对不确定采样之间的钟函数。例如，固定读出标签 $s_*>0$ 和所得 $t>0$，令 $\alpha=t/s_*$，取非零 $\psi\in C_c^\infty((0,s_*))$。当

$$
|\varepsilon|\,\|\psi'\|_\infty<\alpha
$$

时，

$$
\phi_\varepsilon(s)=\alpha s+\varepsilon\psi(s)
$$

都是严格递增、光滑、无界的钟，满足 $\phi_\varepsilon(0)=0$、$\phi_\varepsilon(s_*)=t$，却在采样之间不同。钟率、钟加速度及完整钟函数没有被该单点结论识别。

**定理 21.4（参数与时间的不同稳定常数）。** 现在把真实参数和该次真实读数限制在已认证范围

$$
0<\ell\le r\le R<\infty,\qquad
0<u_{\min}\le u\le u_{\max}<1.
\tag{21.109}
$$

这些是有效的参数/取得约束，不能仅因把观测值截入区间就宣称真实值满足它们。假设同一误差事件上有

$$
|\widehat u-u|\le\delta_u,\qquad
|\widehat v-v|\le\delta_v.
\tag{21.110}
$$

先取

$$
\widetilde u=\operatorname{proj}_{[u_{\min},u_{\max}]}(\widehat u),
\qquad
J(\widetilde u)=[G_R(\widetilde u),G_\ell(\widetilde u)],
$$

$$
\widetilde v=\operatorname{proj}_{J(\widetilde u)}(\widehat v).
$$

令 $\widehat r\in[\ell,R]$ 满足

$$
G_{\widehat r}(\widetilde u)=\widetilde v,\qquad
\widehat t=-\log\widetilde u.
\tag{21.111}
$$

存在唯一逆像；$\ell=R$ 时参数本来已知，直接取该值即可。

由(21.106)及 $H$ 单调性，整个矩形上的参数灵敏度下界为

$$
\boxed{
m=\frac{H((1+2/R)(-\log u_{\max}))}{(R+2)^2}>0.}
\tag{21.112}
$$

它正是在角点 $(R,u_{\max})$ 取得的最小灵敏度。类似地，(21.105)给

$$
L_u=\frac{1+u_{\max}^{2/R}}2<1,\qquad
|\partial_uG_r(u)|\le L_u.
$$

投影不增加 $\widetilde u$ 到真实 $u$ 的距离，因此 $|\widetilde u-u|\le\delta_u$。关键是用 $G_r(\widetilde u)\in J(\widetilde u)$ 作为第二次投影的比较点：

$$
\begin{aligned}
|\widetilde v-G_r(\widetilde u)|
&\le|\widehat v-G_r(\widetilde u)|\\
&\le\delta_v+|G_r(u)-G_r(\widetilde u)|\\
&\le\delta_v+L_u\delta_u.
\end{aligned}
$$

直接复用恢复几何卷定理19.3的导数下界/差商界，得到

$$
\boxed{
|\widehat r-r|
\le\frac{L_u\delta_u+\delta_v}{m}
\le\frac{\delta_u+\delta_v}{m}.}
\tag{21.113}
$$

参数误差界成立，并可使用这里稍紧的 $L_u<1$。若数值求根仅认证了额外核残差 $\eta$，则(21.113)的分子另加 $\eta$，沿用恢复几何卷定理19.3的误差规则。

时间误差是独立的一项：

$$
\boxed{
|\widehat t-t|
\le\frac{|\widetilde u-u|}{u_{\min}}
\le\frac{\delta_u}{u_{\min}}.}
\tag{21.114}
$$

直接用 $G_r(u)$ 处理参数反演，避免了把时间误差的 $1/u_{\min}$ 因子再无谓地加进(21.113)；但恢复时间本身仍必须承担它。若要报告两项绝对误差之和，可把(21.113)与(21.114)相加。

本结论没有全域统一常数：$u_{\max}\uparrow1$ 时参数灵敏度消失；没有有限 $R$ 时同样失去参数逆稳定。另一方面，(21.112)的 $m$ 和 $L_u$ 都不依赖 $u_{\min}$。保持 $u_{\max}<1$ 与 $[\ell,R]$ 固定而令 $u_{\min}\downarrow0$，不会破坏(21.113)的参数稳定常数；失去统一稳定性的是(21.114)中的内部时间恢复。这两个条件数不能混同。$u=0$ 本身仍是无限经过时间极限，不能称为一次有限时刻可取得的读数。

**命题 21.5（投影估计不保证原始残差）。** 第二次投影依赖已经改动的横坐标 $\widetilde u$。真实 $v=G_r(u)$ 不一定属于 $J(\widetilde u)$，所以不能声称该投影单独不增加到真实 $v$ 的误差。

一个精确例子：真实 $r=2$、$u=1/2$、$v=9/16$，取参数区间 $[1,2]$、读数区间 $[2/5,4/5]$，观测为

$$
\widehat u=3/5,\quad\delta_u=1/10,\qquad
\widehat v=9/16,\quad\delta_v=0.
$$

因为 $G_2(w)=(1+w)^2/4$，投影输出

$$
\widetilde u=3/5,\qquad
\widetilde v=G_2(3/5)=16/25,\qquad
\widehat r=2.
$$

于是

$$
|\widetilde v-\widehat v|=31/400>0=\delta_v.
$$

它仍满足(21.113)–(21.114)，但预测的同刻读数对不满足原来的第二条零误差残差。若交付要求一份与全部已获记录相容的模型，必须另验同一个候选满足原始两条残差及旧档案；不能把这里的投影操作称为该共同可行性的证书。

**命题 21.6（四个原始读数的共同误差）。** 沿用恢复几何卷第19节的比值误差界。设每个通道的真实零点及当前读数分别为 $g_u,g_uu$ 和 $g_v,g_vv$，四条已认证原始误差为 $\epsilon_{u0},\epsilon_{us},\epsilon_{v0},\epsilon_{vs}$。若观测零点满足

$$
\widehat Y_{u0}>\epsilon_{u0},\qquad
\widehat Y_{v0}>\epsilon_{v0},
$$

则归一化观测可取

$$
\widehat u=\widehat Y_{us}/\widehat Y_{u0},\qquad
\widehat v=\widehat Y_{vs}/\widehat Y_{v0},
$$

$$
\delta_u=
\frac{\epsilon_{us}+\epsilon_{u0}}{\widehat Y_{u0}},
\qquad
\delta_v=
\frac{\epsilon_{vs}+\epsilon_{v0}}{\widehat Y_{v0}}.
\tag{21.115}
$$

这里只用 $0<u,v<1$ 和
$(\widehat Y_{us}-u\widehat Y_{u0})/\widehat Y_{u0}$ 的恒等式，另一通道同理。两通道和零点的误差可以相关；预算必须在同一联合事件上成立，不能把共享校准误差另当独立抽样。若读数来自配对差分，相应制备与差分误差先进入这些原始界。没有安全正分母或增益下界时，不存在这种统一绝对噪声保证。

若要求一份原始仪器记录的合法拟合，应保留同一个 $(r,t,g_u,g_v)$ 的四个残差，而不只保留式（21.115）的两个外包半径。例如默认误差盒的精确候选集为
$$
\begin{aligned}
\mathcal F_Y=\{(r,t,g_u,g_v):\;&r,t,g_u,g_v>0,\\
&|g_u-\widehat Y_{u0}|\le\epsilon_{u0},\quad
|g_u e^{-t}-\widehat Y_{us}|\le\epsilon_{us},\\
&|g_v-\widehat Y_{v0}|\le\epsilon_{v0},\quad
|g_vk_r(t)-\widehat Y_{vs}|\le\epsilon_{vs},\\
&\text{同一来源、钟、校准与全部旧档案相容}\}.
\end{aligned}
\tag{21.116}
$$
已知更小的联合误差集时，四个盒条件换成同一个原始残差向量属于该集；两个归一化区间分别非空不证明 $\mathcal F_Y$ 非空。假设21.1的共同时间、实际读出泛函及制备条件也始终保留。

**命题 21.7（增益、读出泛函、同刻与制备的必要性见证）。** **没有增益校准。** 即使两个通道共享一个未知正增益 $g$，单个原始正读数对仍可对 $r$ 完全不识别。给定任意 $0<U<V$，设 $\rho=V/U>1$。对每个 $r>0$，

$$
e^tk_r(t)=\frac{e^t}{r+2}+\frac12
+\frac{r}{2(r+2)}e^{-2t/r}
$$

从 $1$ 严格增至无穷，其导数为

$$
\frac{e^t-e^{-2t/r}}{r+2}>0\quad(t>0).
$$

因此存在 $t_r>0$ 使 $e^{t_r}k_r(t_r)=\rho$，再置 $g_r=Ue^{t_r}$，每个 $r>0$ 都产生同一原始读数对 $(U,V)$。不同未校准增益只会引入更多自由度。

即使两个输出零点都为 $1$，差分端口的相对权重也可能错。真实 $r=2,t=\log2$ 时，两个端点状态值为 $9/16,1/16$。若仪器实际相减的是第一坐标减去两倍第三坐标，会报告 $(u,v)=(7/16,9/16)$，其零点读数仍均为 $1$。该对位于开楔形内，却有 $G_2(7/16)=529/1024\ne9/16$，会把内部时间和参数都识别错。这属于未认证读出泛函，不能由标量零点归一化补救。

**两个通道没有共同经过时间。** 若实际为 $u=e^{-t_u}$、$v=k_r(t_v)$，则第一值只确定 $t_u$。例如固定已归一化对 $(u,v)=(1/2,9/16)$：对每个 $r>0$，因 $p_r<1/2<9/16<1$，均可取 $t_v=k_r^{-1}(9/16)$，同时取 $t_u=\log2$。两个不同的线性钟已足以在同一显示标签产生这些值。真实零点和增益校准都不能替代共同时间关系。

**初态来源不对，即使零点读数都正确也会误判。** 真实参数取 $r=2$，实际初态却为

$$
w=e_1+\frac19e_2.
$$

两通道在真实零点仍均读 $1$。中点初态的端点传递为

$$
e_1^{\mathsf T}S_{M_r}(t)e_2
=\frac{r}{r+2}\bigl(1-e^{-(1+2/r)t}\bigr),
$$

而它对差分端口的贡献为零。因此在 $t=\log2$ 时，

$$
u=1/2,\qquad
v=\frac9{16}+\frac19\frac38
=\frac{29}{48}=G_1(1/2).
$$

同一时刻、正确的两个零点值、位于开楔形内部的读数对，却与“初态 $e_1$、参数 $r=1$”完全相同。单对读数不能认证初态来源。未建模强迫或读出导致的状态扰动同样不能由同刻标签排除。

**显示零点不是真实制备零点。** 真实 $r=2$，显示零点落在真实 $b=\log2$，再过 $t=\log2$ 读取并分别除以显示零点值。差分端口给 $u=e^{-t}=1/2$，但端点通道给

$$
v=\frac{k_2(2\log2)}{k_2(\log2)}
=\frac{25/64}{9/16}
=\frac{25}{36}.
$$

该对仍位于开楔形内部，却不是 $G_2(1/2)=9/16$。强行使用(21.104)会得到另一个参数。差分端口能正确给出这段时间增量，不代表端点通道已取得正确的增益归一化。

这些反例均由所列恒等式成立。它们说明新桥所需的是实际共同关系：固定来源、合法初态、真实零点、稳定增益、已认证读出泛函和同一状态/经过时间。新增读出与旧档案共同约束模型，不替换已经取得的其他记录。

在上述同源制备和校准假设下，定理21.2使用一个正时刻的两个通道，[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定理20.2使用从零开始的五个等步单端口值；前者允许未知共同非线性钟，后者要求未知正线性钟。这是不同取得合同下的两种充分关系，不能由读数个数推出费用优劣。合法通道、准备、校准、等待、存储及算术各有费用，仍须分别计量。

## 22. 推进操作、输入测度与谱记忆的钟运输

**定理 22.1（一维时变系统的任意阶标签 Hankel 秩）。** 下列同一个一维系统经已知非线性钟重标后，普通等步标签读数具有任意大的 Hankel 秩；其正确强迫接口和物理变换仍可运输。证明。

先固定同一个物理系统

$$
\dot x(t)=-x(t)+u(t),\qquad y(t)=x(t).
$$

零输入、已制备初态 x(0)=1 的完整响应为 K(t)=e^{-t}。其物理时间离散序列 e^{-n} 的所有非空 Hankel 块都秩一。

取已知钟 t=φ(τ)=log(1+τ)。它光滑、φ(0)=0、φ′(τ)=1/(1+τ)>0，且趋于无穷。实际重标曲线为

$$
k(\tau)=K(\phi(\tau))=\frac1{1+\tau}
=\int_0^\infty e^{-\lambda}e^{-\lambda\tau}\,d\lambda.
$$

最后等式是直接积分；这是标记曲线的一个连续正谱表示。它不可能写成有限正原子和 Σ_j w_j e^{-λ_j τ}，其中 w_j>0、λ_j≥0：有零率原子就有非零平台；没有零率原子时，有限集合的最小率 λ_min>0 给指数上界 (Σw_j)e^{-λ_min τ}，与 1/(1+τ) 的尾部矛盾。这只排除指定的有限正谱类，不把“连续谱表示”直接认作原系统的物理隐藏状态。

更强且只用实际离散读数的下界为

$$
H_N(i,j)=k(i+j)=\frac1{i+j+1}=\int_0^1 z^{i+j}\,dz,
\qquad 0\le i,j<N.
$$

任意非零 a∈R^N 给非零多项式 P(z)=Σ_i a_i z^i。P 不会在整个 (0,1) 恒为零；连续性给一个区间上 P²>0。因此

$$
a^T H_Na=\int_0^1P(z)^2\,dz>0.
$$

故 rank H_N=N。应用 `HankelRankMinimality.finiteHankel_eq_observability_comp_controllability`，任意 d 维线性时不变实现的 Hankel 块由观测矩阵乘可达矩阵分解，秩≤d；取 N=d+1 即矛盾。所以整个序列 k(n) 没有有限维 LTI 实现。只取得前 2N−1 个精确读数时，能推出的是任何与该前缀匹配的 LTI 实现维数至少 N；有限 N 不证明原物理系统有无限状态。

原系统仍有一个动态状态。 令 X(τ)=x(φ(τ))、v(τ)=u(φ(τ))，合法运输得到

$$
X'(\tau)=\frac{-X(\tau)+v(\tau)}{1+\tau}.
$$

这是一维时变实现。若要求自主形式，可增加已知钟态 r′=1、r(0)=1，写 X′=(-X+v)/r；它是二维自主非线性控制系统，不是有限维 LTI 实现。两种维数陈述的模型类不同。

继续比较同一个强迫协议。 零初态时，保留 力值 输入 v=u∘φ，换元给

$$
X(\tau)=\int_0^\tau
 e^{-(\phi(\tau)-\phi(\sigma))}\phi'(\sigma)v(\sigma)\,d\sigma
=\int_0^\tau\frac{v(\sigma)}{1+\tau}\,d\sigma.
$$

这里是两时接口的核；本例中的 σ 依赖恰好相消。它仍不是 k(τ−σ)。取合法有限矩形输入 v=1_[1,2]，即物理 u=1_[log 2,log 3]。在 τ=2，真实输出为 1/3；误把初态曲线当新卷积核则给

$$
\int_1^2 k(2-\sigma)\,d\sigma=\log 2.
$$

这不是分布脉冲，也没有改变比较中的输入或初态。若改用输入密度 w(σ)=φ′(σ)u(φ(σ))，则积分核相应为 (1+σ)/(1+τ)。两种输入约定各自成立，不可混用。

积分与频域条件同样运输。 原 ∫K(t)dt=1；新 ∫k(τ)dτ 发散；保留物理测度则

$$
\int_0^\infty k(\tau)\phi'(\tau)\,d\tau=1.
$$

因此不能把物理核的 L1 小增益合同直接移给 k(τ−σ)。普通未阻尼 Fourier 变换的绝对可积前提也不能直接移过来；这里不排除个别非零频率的条件收敛。保留正确相位与测度时，物理 Fourier 响应仍为

$$
\int_0^\infty e^{-i\omega\phi(\tau)}k(\tau)\phi'(\tau)d\tau
=\frac1{1+i\omega}.
$$

**命题 22.2（共同有界钟率下的物理谱歧义）。** 定理22.1的 φ′ 没有正的统一下界。下面的同一缺口在共同双边钟率合同内仍出现，首先给出有限秩一与二的区别。

令 U=R。两个物理正实现为

$$
C_A=1,\quad J_A=1,\quad K_A(t)=e^{-t};
\qquad
C_B=\operatorname{diag}(1,2),\quad
J_B=(1/\sqrt2,1/\sqrt2)^T,\quad
K_B(s)=\tfrac12(e^{-s}+e^{-2s}).
$$

均满足 K=J*e^{-tC}J；初态制备 x(0)=J1、输出 J*x 给相应零输入响应。两者初始输出都为 1，谱都在共同区间 [1,2]。

在 A 使用未知钟

$$
\phi(s)=-\log K_B(s)
=s+\log2-\log(1+e^{-s}),
$$

在 B 使用恒等钟。直接求导得

$$
\phi'(s)=\frac{1+2e^{-s}}{1+e^{-s}}\in(1,3/2],\quad
\phi(0)=0,\quad \phi(s)\to\infty.
$$

所以两种钟均满足共同合同 1≤钟率≤3/2，且完整标记响应逐点相等：K_A(φ(s))=K_B(s)。本例连无穷尾部都相同，两者平台都为零，因此不与 本卷命题18.6 的特定非零平台识别矛盾。

取任意 h>0，令 x=e^{-h}、z=e^{-2h}，共同数据 a_n=(x^n+z^n)/2 给

$$
a_0a_2-a_1^2=\tfrac14(x-z)^2>0.
$$

由 Hankel 因子化，B 的物理最小 LTI 维数至少 2，而展示的实现给上界 2；A 的物理最小维数为 1。`FinitePronyHankelReconstruction.prony_hankel_rank` 也直接给共同标记序列的秩 2。

物理时间 Laplace 目标同样不同：对 p>0，

$$
\widehat K_A(p)=\frac1{p+1},\qquad
\widehat K_B(p)=\frac1{2(p+1)}+\frac1{2(p+2)}.
$$

在 p=1 分别为 1/2 与 5/12。因此观察对象只包含完整标记曲线及上述共同谱界/钟率界时，物理最小维数和物理 Laplace 响应都不在观察纤维上恒定。所有后处理，包括精确求标记曲线的 Fourier/Laplace 变换，都不能将这两个世界分开。

这个反例不需要固定正幅度的钟率不确定性。将第二率改成 1+δ，δ>0，并令 φ=-log[(e^{-s}+e^{-(1+δ)s})/2]，则 1<φ′≤1+δ/2；对任意 ε>0，选 δ≤min(1,2ε)，仍有秩 1/2 歧义而钟率落在 [1,1+ε]。这不涵盖 ε=0。

同一构造覆盖任意有限正谱族。给定 F(s)=Σ_j w_j e^{-λ_j s}，w_j>0、Σw_j=1、λ_j>0，取 λ_0>0，令 φ(s)=-log F(s)/λ_0 及倾斜权重 π_j(s)=w_j e^{-λ_j s}/F(s)。则

$$
F=e^{-\lambda_0\phi},\qquad
\phi'=\frac{\sum_j\pi_j\lambda_j}{\lambda_0}
\in[\lambda_{\min}/\lambda_0,\lambda_{\max}/\lambda_0],
\qquad
\phi''=-\frac{\operatorname{Var}_{\pi(s)}(\lambda)}{\lambda_0}\le0.
$$

证明为 F′/F 的直接微分：π_j′=π_j(Σ_kπ_kλ_k−λ_j)，代回即给负方差。正率还给 φ(0)=0 与 φ→∞。故允许这些未知钟时，任意有限谱复杂度都能吸收到单模的钟里。给定先验钟率 [m,M] 时仍须核实本例实际 φ′ 位于该区间；上述端点界是充分条件，不声称任意谱自动适配任意先验。特别，对任意 ε>0 和任意整数 $N\ge2$，可以选 N 个互异 λ_j∈[1,1+min(ε,1)]、λ_0=1 与正归一化权重，得到共同钟率 [1,1+ε]、共同物理谱界 [1,2] 下的维数 1/N 歧义。这是标准 log-sum-exp 导数恒等式与既有 Prony 秩定理的组合，不是新的对数配分函数理论。

限制：比较的是完整零输入初态响应，不是所有驱动实验的等价。若档案已有各物理采样时刻、校准钟、能区分的输入实验或与物理时间绑定的实际费用读数，这些资料必须并入观察 Q；上述两个世界未被证明在扩大的 Q 下仍相同。不能删掉档案来制造碰撞。

**命题 22.3（记录核、推进交织与实际费用）。** 对已知、共同、连续严格递增且满射的 $\phi:[0,\infty)\to[0,\infty)$，定义 R_φf=f∘φ。它在完整函数空间上可逆。任意记录映射 Q 都有

$$
R_\phi Q(x)=R_\phi Q(y)\iff Q(x)=Q(y).
$$

因此仅改记录坐标不改变观察核，也不改变“目标在每条观察纤维上恒定”的准确可恢复性。命题22.2变粗的是**未知钟也属于待识别对象**时的观察映射；不同对象使用不同 φ，不能用一个共同已知的逆变换撤回。

然而物理平移 S_hf(t)=f(t+h) 在重标记录上的运输是

$$
(\widetilde S_hF)(s)
=F\bigl(\phi^{-1}(\phi(s)+h)\bigr),
\qquad
R_\phi S_h=\widetilde S_hR_\phi.
$$

这正是 `BehaviorCompletionTranslation.behavior_completion_translation` 所需的交织条件。对单模的 F=e^{-φ(s)}，有 S̃_hF=e^{-h}F，运输后的闭合仍一维。普通标签平移 F(s+h) 则在定理22.1给无限维平移闭合，在命题22.2给二维。将 S̃_h 换成普通平移，不再是 `DynamicClosureMinimality.dynamic_closure_is_least` 中相同的干预族。

再假设 $\phi$ 为 $C^1$ 且 $\phi'>0$，物理 Laplace 的合法计算为

$$
\widehat K(p)=\int_0^\infty
 e^{-p\phi(s)}K(\phi(s))\phi'(s)\,ds.
$$

普通标签变换 ∫e^{-ps}K(φ(s))ds 是另一个目标。仿射 φ(s)=cs 才有熟悉的 $\mathcal L[K(c\,\cdot)](p)=c^{-1}\widehat K(p/c)$。Fourier 同样必须运输相位及测度；完整数据的单射编码与目标运算闭合是分开的条件，正如[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)定理31.15 已证明的代数观察现象。

有限取得时只有原样点会被重标。新钟等步点一般不是已有物理等步点；从有限向量做可逆 DFT 保留该向量的核，但不给未测的点、整个响应、导数或无穷极限。连续 Laplace/Fourier 积分不是这个有限 DFT 所附赠的接口。

[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)命题4.7 精确说明有限宏读数如何回到同一原始记录：p=B^Tz，宏系数 u 实际展开为 Bu，盒噪声幅度为 ε||Bu||_{1,σ}。共享原始噪声的变换系数不能被重新宣布独立；已支付的取得费用也不因表达变短而退款。本卷定理12.7 对真实重标保留点操作费用，连续费率乘 φ′；命题22.2若把物理钟费用加入 Q，就必须重新检验同纤维条件。

## 23. 可读模态的相位幅度钟与素数参照

**定义 23.1（闭合模态接口）。** 给集合 X 与作用 T_t:X→X（t≥0），满足 T_0=id、T_{t+s}=T_tT_s。给定 $N\ge1$ 个复值可读函数 χ_j:X→ℂ 和已知复数 s_j，满足

$$
\chi_j(T_t x)=e^{s_jt}\chi_j(x)\qquad(t\ge0,x\in X).
\tag{23.101}
$$

记 Ψ(x)=(χ_j(x))_{j=1}^N，并以 y(x)=Σ_jχ_j(x) 为指定标量读出。可读意味着当前协议允许取得该值，或已给出从现有合法记录恢复它的映射与条件；式(23.101)本身不授予访问权限。一般系统也不自动存在这样一组有限模态。写 s_j=−γ_j+iω_j 只是在此闭合模型内拆分生成元，不是概率或物理假设。

**命题 23.2（当前模态与指定未来响应的闭合）。** 有

$$
\Psi(T_t x)=\operatorname{diag}(e^{s_1t},\ldots,e^{s_Nt})\Psi(x),
\qquad y(T_t x)=\sum_j e^{s_jt}\chi_j(x).
\tag{23.102}
$$

所以 Ψ 相等的两个状态具有相同的全部 y 未来。若存在 h>0 使 m_j=e^{s_jh} 互异，则相同的前 N 个 h 间隔 y 读数也强制 Ψ 相等。因此该有限窗口、Ψ 和全部 y 未来在 X 上具有同一个观察核。

**证明。** 前式逐坐标就是(23.101)，求和给后式。窗口是 VΨ，其中 V_{nj}=m_j^n、0≤n<N。节点互异，直接应用已有 Vandermonde 窗口单射性，即`FiniteCrystalTimeFrequencyBridge.first_crystal_time_window_injective` 的复数实例。全部未来包含该窗口，所以三个核相等。此论证恢复的是指定模态任务商；除非另证 Ψ 对 X 单射，不恢复全部微观状态。□

复数 s_j 互异不保证采样节点 m_j 互异。纯衰减实率互异在任意 h>0 下给互异节点；含相位时还须排除相差 2πik/h 的率。

**定义 23.3（同源非零衰减模态记录）。** 固定 x∈X、一个满足(23.101)的模态 χ，令 s=−γ+iω、γ>0、χ(x)≠0。标签区间 I 含初始点 τ_0，φ:I→[0,∞) 连续严格递增，φ(τ_0)=0；实际记录为

$$
Z(\tau)=g\,\chi(T_{\phi(\tau)}x),\qquad g\in\mathbb C\setminus\{0\}
\tag{23.103}
$$

且 g 在该记录内固定。它可以未知，因为以下比值使用同一个传感器的实际初始记录 Z_0=Z(τ_0)。不允许任意时间变增益、遗漏初始记录或把两来源记录拼作同一模态。

定义 A(τ)=|Z(τ)|、a(τ)=−log[A(τ)/A(τ_0)]。令 θ 是 Z/|Z| 的连续实相位提升，初值 θ(τ_0)已固定。相位提升是完整连续非零轨迹的数学对象；它是否实际可得须另外由连续记录或已认证的绕数信息保证。

**命题 23.4（共同钟消去及尺度边界）。** 对所有 τ∈I，

$$
a(\tau)=\gamma\phi(\tau),\qquad
\theta(\tau)-\theta(\tau_0)=\omega\phi(\tau)
=\frac\omega\gamma a(\tau).
\tag{23.104}
$$

若 φ 可微且 φ′>0，则局部衰减率 a′=γφ′ 与相位率 θ′=ωφ′ 同乘换钟因子；其比为 ω/γ。任何两个幅度相差二倍的已记录点之间，连续累计相位差为 (ω/γ)log2。若 γ已知，则幅度给相对内部时间 φ=a/γ；若 γ未知，(γ,ω,φ)→(cγ,cω,φ/c)、c>0 保持全部 Z，不识别绝对率与绝对时间单位。

**证明。** 由(23.101)，Z/Z_0=e^{(−γ+iω)φ}，取模和实对数得第一式。函数 θ_0+ωφ 是相应单位相位的一份连续提升；任意同初值提升与它的差属于2πℤ且连续，在区间上必恒为零，故得第二式。求导给局部公式；两点 a 差等于log2给半幅公式。最后直接代入尺度变换。□

γ=0 时幅度恒定，不能充当这一内部钟；χ(x)=0 时整个模态不可见；只有 |Z| 时 ω完全不可见。任意混合读出 Σχ_j 的相位与模长也不满足(23.104)，除非另证它自身是一份非零模态。常数增益能由同源比值消去不意味着时变增益也能消去。

若传感器只读强度 |Z|²，对数比为2γφ，应保留因子2；只读实部也不提供复相位。相位方向的坐标约定须固定，未知复共轭会留下ω/γ与−ω/γ的歧义。反过来，观察到(23.104)形式也不单独认证一模来源：任意严格正的实混合衰减都有恒定相位和零斜率，仍须保留已声明模态类及共同来源条件。

“周期”在此只指纯相位因子的一次闭合；γ>0 的完整 Z 轨迹不具有正周期。半幅不是概率半衰或熵变化。[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第127.13节的热流/波动比较已经承担两种演化规则的区别，此处保留该区别。

**推论 23.5（参照模态确定相对谱图）。** 在定义23.1的同一系统、同一 x、同一未知 φ 下，另有一个合法可读参照模态 ζ，满足 ζ(T_t x)=e^{(−γ_*+iω_*)t}ζ(x)、γ_*>0、ζ(x)≠0。令

$$
u(\tau)=\frac{|\zeta(T_{\phi(\tau)}x)|}{|\zeta(x)|}\in(0,1],
\qquad a_*(\tau)=-\log u(\tau).
$$

则每个选定模态满足

$$
\chi_j(T_{\phi(\tau)}x)
=\chi_j(x)\exp\!\left[-\frac{s_j}{\gamma_*}\log u(\tau)\right].
\tag{23.105}
$$

因此消去未知共同标签后，记录落在由初始模态与相对率 s_j/γ_* 确定的一张图上。

**证明。** 命题23.4给 φ=−log u/γ_*，代入(23.101)。u>0，所以这里使用唯一实对数，不涉及复对数选支。□

若连续相位和非零初值的各个模态确已可读，可以由各模态的对数幅度、展开相位相对于 a_* 的斜率恢复相对率；这只是(23.104)逐模态应用。单个标量混合响应没有免费提供这些独立通道。[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)引理15.8的单调共享迹是另一种内部钟，不须把正谱混合迹错误拆成已取得的每个模态。

**命题 23.6（校准素数热坐标与未知尺度纤维）。** 使用 `PrimeZeckendorfFrequencyBridge.first_excited_prime_frequency` 的既有 $\lambda_p=\varphi^2\log p$（第一激发层），以及 `PrimeGoldenComplexMode.first_golden_complex_mode_euler` 和模长公式。这里不重证一般素数对数独立性；读数也不恢复该频率所忽略的层坐标。

令 $\varphi=(1+\sqrt5)/2$ 为黄金比，$c=\varphi^2>0$、$\lambda_p=c\log p$，其中p为素数，故λ_p>0。定义
$$
A_p(\sigma)=e^{-\sigma\lambda_p},\qquad
M_p(\sigma,t)=e^{-\sigma\lambda_p}e^{it\lambda_p}.
$$
若σ>0已知，精确合法幅度A=A_p(σ)唯一确定
$$
\boxed{p=\exp\!\left(\frac{-\log A}{c\sigma}\right).}
\tag{23.111}
$$
所以完整复读数也确定p，而无需先解相位绕数。若σ作为未知参数可取任意正数，则对任意两个素数p,q，置
$$
\sigma_q=\sigma_p\frac{\log p}{\log q}>0
$$
就有A_q(σ_q)=A_p(σ_p)。联合观测(p,σ)↦A因此不单射。

**证明。** 取实对数给−log A=cσlog p，除以正cσ并取指数得到(23.111)；这等价于 `PrimeZeckendorfTemporalization.first_excited_heat_multiplier_injective` 的正热坐标单射性。碰撞直接由σ_q log q=σ_p log p得到。对于复读数，进一步取 $t_q=t_p\log p/\log q$ 即保证完整 $M$ 也相同；固定已知t时，不可仅凭幅度碰撞断言复读数相同。□

(23.111)以数据确属所声明素数模态类为前提；任意带噪A代入后得到的正实数不能自动取整为认证素数。精确单射也不提供整个无界素数集合上的统一绝对误差间隔，因为A_p(σ)随p→∞趋零。

**命题 23.7（素数模态的共同钟代入与全记录碰撞）。**

固定a>0、b∈ℝ。设h:I→[0,∞)连续严格递增，h(τ_0)=0，实际零点归一化复记录为
$$
Z_p(\tau)=M_p(a h(\tau),b h(\tau))
=\exp\!\left[(-a+ib)\lambda_p h(\tau)\right].
\tag{23.112}
$$
若θ是初值为零的连续相位提升，令L=−log|Z_p|，则
$$
L(\tau)=a\lambda_p h(\tau),\qquad
\theta(\tau)=b\lambda_p h(\tau),\qquad
\boxed{\theta=(b/a)L.}
\tag{23.113}
$$
因此任一正时间处、在相位提升可取得的条件下，θ/L只给b/a，不给p。对任意素数q，令h_q=(log p/log q)h；则同样a,b下有Z_q[h_q]=Z_p[h]，整条复记录逐点相同。

**证明。** 直接取模、实对数和显式连续相位，得(23.113)。λ_qh_q=λ_ph使(23.112)的完整指数相等。□

碰撞假设候选钟类允许这一正缩放；有额外钟率界、真实时间点或费用读数时，必须检查h_q仍满足全部旧档案。它保留的是同一**标签**记录，不宣称已校准原时间的两系统相同。有限复样本仅给相位模2π，不能免费给(23.113)中的累计θ；仅看幅度或实部更不够。若读数带未知但恒定非零复增益，可用同一传感器的真实零点读数归一化；时变增益不能这样消去。

**命题 23.8（半衰与联合熵、全流反演的两种反例）。** 对任意γ>0，以下两项同时成立。

1. 存在具有固定坐标半衰期log2/γ的二维全流，它可逆、保面积，具有明确的时间反演，并保持任意具有有限微分熵的联合概率密度之微分熵。
2. 存在两态连续时间Markov过程，其存活概率以固定半衰期log2/γ指数衰减，但两态Shannon熵先增后减。

**证明。** 第一项取
$$
\Phi_t(x,p)=(e^{-\gamma t}x,e^{\gamma t}p),\qquad t\in\mathbb R.
$$
它满足Φ_{t+s}=Φ_tΦ_s、Φ_t^{-1}=Φ_{−t}、det DΦ_t=1，且x(t+log2/γ)=x(t)/2。交换R(x,p)=(p,x)满足R²=id及RΦ_tR=Φ_{−t}，给出具体反演。若初始密度ρ≥0、积分为一、ρlogρ可积，推前密度为ρ_t=ρ∘Φ_{−t}；变量替换和Jacobian一给
$$
-\int\rho_t\log\rho_t\,dx\,dp
=-\int\rho\log\rho\,dx\,dp.
$$
这是`DifferentialEntropyChangeOfVariables` 的变量替换公式的常Jacobian特例。一个坐标的收缩由另一个坐标的扩张补偿；这里只声称联合微分熵，不将它改称热力学熵。

第二项取存活态到吸收态的跃迁率γ，后者吸收，从存活态确定初态开始。列概率满足q′=−γq、q(0)=1，所以p(t)=(q,1−q)、q=e^{−γt}。对t>0，两质量严格正，直接微分得到
$$
H'(p(t))=\gamma q(t)\log\frac{q(t)}{1-q(t)}.
$$
因此0<t<log2/γ时导数正，在该时刻为零，此后导数负；H由零升至log2再趋零，而每段长度log2/γ仍使存活概率减半。这是合法吸收Markov模型，却没有[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第127.2节要求的对称双随机生成元；故不与那里已证明的熵增冲突。□

## 24. p 进数字历史、最小闭合与相容完成

**定义 24.1（共同初态、精度与合法加一历史）。** 固定素数 $p\ge2$，以 $\mathbb Z_p$ 为 p 进整数环，$q_m:\mathbb Z_p\to\mathbb Z/p^m\mathbb Z$ 为自然投影，$m\ge0$，$q_0$ 是模一的唯一读数。$[q_m(x)]\in\{0,\ldots,p^m-1\}$ 表示规范整数代表。初始协议仅允许单位动作
$$
T(x)=x+1,\qquad T^n(x)=x+n\quad(n\in\mathbb N).
$$
所有读数不扰动状态，来自同一初态和同一条轨道。动作数、精度、传感器身份及实际结果均保留在档案。已知事件数 $n_i\in\mathbb N$、深度 $m_i$ 的实际记录为
$$
y_i=q_{m_i}(x+n_i).
\tag{24.101}
$$
若有完整旧记录 $C$，所有新增条件均与 $C^{-1}(C_{\rm actual})$ 相交。初态 $x$ 与当前态 $x+n_i$ 是不同目标，由已知事件数运输；未知事件数、起点、增量或传感器标度须列为共同未知量。数学上的所有可能历史不是实际已执行的有限历史，也不提供秒、回溯或复制许可。

使用 $d_p(x,y)=|x-y|_p$、$|p|_p=p^{-1}$，有
$$
q_m(x)=q_m(y)\iff x-y\in p^m\mathbb Z_p
\iff d_p(x,y)\le p^{-m}.
\tag{24.102}
$$
这是 p 进整数投影核与距离的标准关系，参见 Gouvêa, *p-adic Numbers: An Introduction*, 2nd ed., Springer, 1997，及 Mathlib `PadicInt.ker_toZModPow`、`ext_of_toZModPow`。仓内 `PadicBallFiberCorrespondence.modeq_iff_padic_dist_le` 的整数输入结论是它在 $\mathbb Z$ 上的特化；此处完整载体为 $\mathbb Z_p$。

**命题 24.2（有限层周期与完整态非周期）。** 对 $m\ge0$、$x\in\mathbb Z_p$、$n\ge0$，
$$
q_m(T^n x)=q_m(x)\iff p^m\mid n.
$$
每条 $q_m$ 读数序列的最小正事件周期是 $p^m$，$m=0$ 时为一。完整状态无正整数周期，$T$ 是可逆等距映射。

证明。环同态性给 $q_m(x+n)=q_m(x)+q_m(n)$，消去得相等恰当 $p^m\mid n$。完整状态若 $x+n=x$，则整数 $n$ 在 $\mathbb Z_p$ 中为零，整数嵌入单射使 $n=0$。亦可由共同周期被所有 $p^m$ 整除，再取 $p^m>n$ 得到矛盾。逆映射是 $x\mapsto x-1$，距离等式来自 $(x+1)-(y+1)=x-y$。代数可逆性不把逆动作加入定义24.1的合法协议。

所以每个有限精度存在周期，不等于存在一个对全部精度有效的共同正周期。分辨率 $p^{-m}$ 与可见事件周期 $p^m$ 的倒数关系属于此指定动作和距离规范，不是普适物理尺度律；这里没有收缩、半衰或熵产生。$\square$

**命题 24.3（合法正步抽样与代数逆步扩展）。** 若已知每次样本跨过正整数 $a\ge1$ 次加一，实际序列 $q_m(x+aj)$ 的最小正样本周期是
$$
\frac{p^m}{\gcd(p^m,a)}=p^{\max\{m-v_p(a),0\}}.
\tag{24.103}
$$
$a=0$ 单独表示不推进时的重复记录，读数恒定、周期一，不代入 $v_p(0)$。若另外明确允许合法执行 $T^{-1}$，才可把公式扩展到负整数步 $a$，此时代入 $|a|$。

证明。正步可由合法单位动作复合执行；周期 $h\ge1$ 恰满足 $p^m\mid ah$。写 $a=p^v u$ 且 $p\nmid u$，条件等价于 $p^{\max(m-v,0)}\mid h$，得到最小值。零步直接恒定；负步的同余计算相同，但其实际执行要求所述逆动作许可。未知步长可以改变读数周期，例如 $a=p^m$ 使第 $m$ 层记录恒定。换事件标签只有在运输同一实际样点时保留实验，重新等步抽样是另一协议。$\square$

**命题 24.4（固定低模读数已经动态闭合）。** 对 $m,N\ge0$，令
$$
Q_{m,N}(x)=(q_m(x),q_m(Tx),\ldots,q_m(T^Nx)).
$$
则 $\ker Q_{m,N}=\ker q_m$，全部无穷未来历史也有相同核。更一般，任意非空已知时刻集合上的同精度读数具有同一核。

证明。每个读数为 $q_m(x)+q_m(n)$，所以 $q_m$ 相等迫使所有读数相等；反向从任一已知时刻消去 $q_m(n)$。因而等待不提高初态分辨率，虽然动作档案仍增长。例如 $x$ 与 $x+p^m$ 有相同全部 $q_m$ 历史而 $q_{m+1}$ 不同。闭合接口能预测当前模态及全部未来低模值，不恢复更高位。$\square$

**定理 24.5（不同精度的共同纤维）。** 对有限非空记录（24.101），令 $K=\max_i m_i$，$z_i=y_i-q_{m_i}(n_i)$。共同候选非空，当且仅当每对 $z_i,z_j$ 在模 $p^{\min(m_i,m_j)}$ 下相同。相容时，选 $m_j=K$，令 $a=[z_j]$，则全部新记录的纤维恰为
$$
\mathcal F=a+p^K\mathbb Z_p.
\tag{24.104}
$$
完整候选仍为 $\mathcal F\cap C^{-1}(C_{\rm actual})$。

证明。共同 $x$ 的所有投影必相容，得必要性。若相容，最高精度 $z_j$ 的每个相应约化等于 $z_i$，故每个 $x\equiv a\pmod{p^K}$ 都满足记录。反之，第 $j$ 条已强制该同余。精度集非空且有有限上界时，即使记录无限，其最大精度仍在集合中，使用同一论证仍为该球。无界相容深度的情况由命题24.12给出。不同读数分别可能，不足以替代共同相容性。$\square$

**命题 24.6（没有附加先验时的锐恢复半径）。** 对式（24.104）的非空球，若全部球内初态均被允许且输出可取任意 $\mathbb Z_p$ 点，最小最坏 $d_p$ 误差恰为 $p^{-K}$，每个相容中心都达到。

证明。若 $b\in\mathcal F$，全部 $x\in\mathcal F$ 有 $|x-b|_p\le p^{-K}$，而 $x=b+p^K$ 达到等号。若 $b\notin\mathcal F$，则 $|b-a|_p>p^{-K}$，强三角关系使每个 $x\in\mathcal F$ 都满足 $|x-b|_p=|a-b|_p>p^{-K}$。故半径等于球直径，不是实线段的半直径。附加旧档案可缩小纤维，所述无先验下界不直接适用于该交集。[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)的纤维恢复原则可以使用，其实凸对偶与中点公式不能无条件搬到此超度量。$\square$

**定义 24.7（单个高位与固定连续协议）。** 对 $k\ge0$，令 $P=p^k$，
$$
d_k(x)=\left\lfloor\frac{[q_{k+1}(x)]}{P}\right\rfloor\in\{0,\ldots,p-1\},
\qquad [q_{k+1}(x)]=bP+r,\quad 0\le b<p,\ 0\le r<P.
$$
该传感器只读第 $k$ 位，不是完整低模 $q_k$。固定协议
$$
W_{k,N}(x)=(d_k(x),d_k(Tx),\ldots,d_k(T^Nx))
$$
使用 $N$ 次演化、$N+1$ 次实际读取，样点恰为 $0,\ldots,N$。

**定理 24.8（携带显露的精确恢复）。** 有 $\ker W_{k,P-1}=\ker q_{k+1}$。首读数给 $b$；若时刻 $1,\ldots,P-1$ 首次在 $\tau$ 观察到不同于 $b$ 的值，则 $r=P-\tau$；若无变化，则 $r=0$。因此 $P=p^k$ 次读数精确恢复 $q_{k+1}(x)$。

证明。在 $0\le n\le P-1$ 内，$0\le r+n\le2P-2$，最多向第 $k$ 位携带一次，且
$$
d_k(x+n)=\left(b+\left\lfloor\frac{r+n}{P}\right\rfloor\right)\bmod p.
\tag{24.105}
$$
$r=0$ 时商始终零；$r>0$ 时首次商一恰在 $\tau=P-r\in\{1,\ldots,P-1\}$。$p\ge2$ 保证 $b$ 与 $(b+1)\bmod p$ 不同，包括 $b=p-1$ 到零的环绕。故变化时刻恢复低位余数。反向，所有加一后的高位都通过 $q_{k+1}$ 因子化，得到核等式。$k=0$ 时 $P=1$、只读一次，变化时刻集为空，$r$ 只能为零，恰为 $d_0=q_1$。$\square$

**定理 24.9（固定连续协议的锐最坏时域）。** 对 $k\ge1$，若 $0\le N<P-1$，则 $W_{k,N}$ 不能在全部初态上恢复 $q_{k+1}$。该协议的必要且充分最大时域为 $P-1$，读数数为 $P$。

证明。取整数初态 $x=0,x'=1$，高位均为零、低位余数分别零和一。$0\le n\le N\le P-2$ 时，$n,n+1\in[0,P-1]$，所以两个高位读数都为零，但 $q_{k+1}(0)\ne q_{k+1}(1)$。在 $n=P-1$ 后一条首次变一，前一条仍零。充分性由定理24.8给出。

该下界仅针对规定的从零开始连续全采样协议，不比较自适应、跳跃采样、二分搜索、变更端口或直接读取 $q_{k+1}$；这些协议另需时刻可达、回溯、复制及费用合同。等待时域和实际读取次数是不同费用坐标。$\square$

**推论 24.10（单高位的最小动态稳定细化）。** 对唯一合法动作 $T$ 和传感器 $d_k$，
$$
\bigl[\forall n\ge0,\ d_k(T^nx)=d_k(T^ny)\bigr]
\iff q_{k+1}(x)=q_{k+1}(y).
$$
最小保留 $d_k$ 且在 $T$ 下闭合的实际行为表示就是 $q_{k+1}$，有 $p^{k+1}$ 个行为类。

证明。定理24.8给从全部历史相等到模态相等，模 $p^{k+1}$ 的加一闭合给反向。若表示 $r_*$ 恢复 $d_k$ 且满足 $r_*T=\overline T r_*$，归纳使相同表示给全部未来高位相同，继而给相同 $q_{k+1}$。后者本身恢复 $d_k$ 且满足 $q_{k+1}(Tx)=q_{k+1}(x)+1$。直接应用本卷第2—3节及 `DynamicClosureMinimality.dynamic_closure_is_least` 的一般最小因子化结论即可。

更长历史不能区分 $x$ 与 $x+p^{k+1}$。当前只有 $p$ 值的高位接口，经最多 $p^k-1$ 步可恢复 $p^{k+1}$ 个行为类；也可由较宽的当前 $q_{k+1}$ 直接承载它们。事件数始终保留，恢复初始模态后可算当前模态。与命题24.4对照，已经闭合的 $q_k$ 等待不增加区别，未闭合的 $d_k$ 则通过携带取得遗漏低位；两者都不能继续取得未耦合到接口的更高位。$\square$

**命题 24.11（有限角色、事件频率与其核）。** 对 $m\ge0$、$j\in\mathbb Z/p^m\mathbb Z$，定义
$$
\chi_{m,j}(x)=\exp\left(\frac{2\pi i j[q_m(x)]}{p^m}\right).
$$
它是连续加法角色，满足
$$
\chi_{m,j}(Tx)=e^{2\pi i j/p^m}\chi_{m,j}(x).
\tag{24.106}
$$
其最小正事件周期为 $p^m/\gcd(j,p^m)$，$j=0$ 时取一。$m\ge1$ 时，与 $p$ 互素的 $j$ 恰具有 $q_m$ 的完整分辨率；$m=0$ 为唯一平凡角色。

证明。更换整数代表只改变指数中 $2\pi i$ 的整数倍，加法公式给同态性。它通过连续有限离散商 $q_m$ 因子化，故连续；代入 $x+1$ 给式（24.106）。正周期 $h$ 恰满足 $p^m\mid jh$，同命题24.3的除法得到最小值。两个初态在全部该角色历史下相同，恰当
$$
j(q_m(x)-q_m(y))=0\pmod {p^m}.
$$
$j$ 与 $p$ 互素时可消去；不互素时有非零模差被其消去。特别 $j=1$ 的 $p^m$ 个相位值互异。此处频率单位是每次加一，角频率按 $2\pi$ 取模；有限精确相位的访问仍须协议许可。标准紧群平移与角色背景参见 Walters, *An Introduction to Ergodic Theory*, Springer, 1982。这里仅定义 p 幂子族，不声称已证明全部 $\mathbb Z_p$ 连续角色的分类，也不把全模 profinite 分类未经映射直接移来。$\square$

**命题 24.12（完整相容读数与有限球）。** 任意相容序列 $a_m\in\mathbb Z/p^m\mathbb Z$，满足 $a_{m+1}\bmod p^m=a_m$，由唯一 $x\in\mathbb Z_p$ 实现。有限前缀 $a_0,\ldots,a_K$ 的实现则恰为 $a+p^K\mathbb Z_p$，其中 $a$ 是 $a_K$ 的整数提升。

证明。取规范整数代表 $r_m=[a_m]$；$m\ge n$ 时 $p^n\mid r_m-r_n$，故 $(r_m)$ 为 p 进 Cauchy 序列。完备性给极限 $x$，各 $q_n$ 连续且纤维闭，尾部 $q_n(r_m)=a_n$，所以 $q_n(x)=a_n$。若 $x,y$ 全部投影相同，$|x-y|_p\le p^{-n}$ 对每个 $n$ 成立，故 $x=y$。有限前缀由最高精度同余给出。无界深度的相容子序列也决定全部层：对每层选任意更细读数约化，相容性使选择无关。

每个有限前缀可有非负整数代表，完整极限未必非负整数，例如 $a_m=p^m-1$ 实现 $x=-1$，其非负代表作为实数发散。甚至完整极限未必属于任何普通整数：令 $a_m$ 是 $1+p$ 在模 $p^m$ 下的乘法逆，唯一性保证这些值相容，其极限为 $(1+p)^{-1}\in\mathbb Z_p$，而没有整数 $z$ 满足 $(1+p)z=1$。完成域的实现不等于原载体的实现；相容完成也不生成下一位或分配概率。$\square$

**命题 24.13（确定轨道的有限访问计数）。** 对固定 $x,m$ 和模 $p^m$ 的目标值，每 $p^m$ 个连续时刻恰访问一次。前 $N\ge1$ 个时刻的访问数为 $\lfloor N/p^m\rfloor$ 或 $\lceil N/p^m\rceil$，频率与 $p^{-m}$ 之差至多 $1/N$。

证明。$q_m(x+n)$ 在每个完整块遍历有限循环一次，除法算法把 $N$ 拆成完整块及一个不完整块，后者对每个值至多增加一次。此比例不需要概率律，也不同于命题24.11的相位频率；若实际停留长度依状态改变，按钟时的比例还需运输相应权重，本命题只计已知等步事件。$\square$

**假设 24.14（额外指定 Haar 初态律）。** 另在紧加法群 $\mathbb Z_p$ 上指定归一化平移不变 Haar 概率 $\mu$，令 $X\sim\mu$。一般紧群 Haar 定理提供该律，亦可用独立均匀 p 进数字构造；完成化与加一动作自身不指定此律。下项仅对有限商和有限记录计算自然对数 Shannon 熵，不给整个无穷精度状态定义有限离散熵。

**命题 24.15（同源历史熵与确定性显露）。** 在假设24.14下，
$$
\mu(a+p^m\mathbb Z_p)=p^{-m},\quad
H(q_m(X))=m\log p,\quad
H(q_{m+1}(X)\mid q_m(X))=\log p.
\tag{24.107}
$$
固定低模的任何包含至少一次已知时刻读数的有限历史熵为 $m\log p$，其后新增同精度读数条件熵为零；而
$$
H(W_{k,p^k-1}(X))=(k+1)\log p,\qquad
H(W_{k,p^k-1}(X)\mid d_k(X))=k\log p.
\tag{24.108}
$$
证明。$p^m$ 个剩余类被平移互换且分割全空间，所以各质量为 $p^{-m}$。等概率有限集合的熵即 $m\log p$；每个旧球的 $p$ 个更细球各占条件质量 $1/p$，给条件熵。命题24.4使低模历史与 $q_m$ 的实际像双射，后续读数由它确定。定理24.8使指定高位历史与 $q_{k+1}$ 的实际像双射，故联合熵为 $(k+1)\log p$；$d_k$ 均匀于 $p$ 个值且是该历史的分量，条件熵为相减所得 $k\log p$。

这些读数高度相关，不能把 $p^k$ 份单次熵直接相加。增长来自同一初态的低位被显露，动作没有增加随机创新；$T$ 保持 $\mu$ 且可逆等距，不由记录熵增长推出热力学熵增或物理反演破缺。若另有旧记录，应在保留的同一联合律下条件化；非 Haar 初态的球概率不同，Dirac 初态更使全部记录熵为零。有限加一与携带恢复的算术对任意整数基 $b\ge2$ 同样成立，故层级周期本身不能识别素数；标准 $\mathbb Z_p$ 赋值和距离才使用素数假设。传感器误码或动作漏记不在定义24.1内，需另立共同误差纤维，不能继续声称这里的锐阈值。$\square$

## 24.99 追加锚

## 25. 非线性双端口、共同钟与档案相容图

**定义 25.1（实际混合响应合同）。** 固定已知 $\nu>0$、紧区间 $I=[b_-,b_+]$（允许单点）和 $T_0>0$，记 $B=\max\{|b_-|,|b_+|\}$。同一来源、模型、校准和内部时间下有实际实值响应 $r(\beta,t),z(\beta,t)$，定义在 $I$ 的开邻域乘 $[0,T_0]$ 上，满足
$$
r(\beta,0)=z(\beta,0)=0,\quad r_t(\beta,0)=\nu,
\quad z_t(\beta,0)=\beta.
\tag{25.101}
$$
假设时间二阶导数及其一次 $\beta$ 导数连续，所需低阶导数亦连续，时间端点取单侧导数；在 $I\times[0,T_0]$ 有非负有限常数
$$
|r_{tt}|\le A_r,\quad |r_{\beta tt}|\le A_1,
\qquad |z_{tt}|\le C_z,\quad |z_{\beta tt}|\le C_1.
\tag{25.102}
$$
这些是实际响应的估计前提，不是参数单射性前提。置
$$
\kappa=C_1/2+A_1(B+C_zT_0)/\nu,
\quad 0<T\le T_0,\quad A_rT\le\nu/2,\quad\kappa T\le1/2,
$$
$$
s_*=\nu T/2,\qquad L_g=2(B+C_zT)/\nu.
\tag{25.103}
$$
零系数不限制 $T$，所以这样的正 $T$ 存在。这里 $A_r$ 是进度响应常数，与准备幅度上界 $A_\alpha$ 无关。

**定理 25.2（阈值图、精确像与共同短时单射）。** 在定义25.1下，每个 $\beta\in I$、$s\in[0,s_*]$ 有唯一 $t_\beta(s)\in[0,T]$ 使 $r(\beta,t_\beta(s))=s$。设 $G_s(\beta)=z(\beta,t_\beta(s))$，则正阈值处
$$
\frac{2s}{3\nu}\le t_\beta(s)\le\frac{2s}\nu,
\qquad \partial_s t_\beta=\frac1{r_t},\quad
\partial_\beta t_\beta=-\frac{r_\beta}{r_t},
\tag{25.104}
$$
$$
\partial_\beta G_s=z_\beta-z_t\frac{r_\beta}{r_t},
\quad \frac{s}{3\nu}\le\partial_\beta G_s\le\frac{3s}{\nu},
\quad
\left|\partial_\beta G_s-\frac{s}{\nu}\right|
\le\frac4{\nu^2}\left(\kappa+\frac{A_r}{2\nu}\right)s^2.
\tag{25.105}
$$
实际映射 $\Psi(\beta,t)=(r(\beta,t),z(\beta,t))$ 在
$$
W=\{(\beta,t):\beta\in I,\ 0<t\le T,\ 0<r(\beta,t)\le s_*\}
\tag{25.106}
$$
上单射，其精确像为
$$
Y=\{(s,w):0<s\le s_*,\quad G_s(b_-)\le w\le G_s(b_+)\}.
\tag{25.107}
$$
域含 $I\times(0,T/3]$。按坐标次序 $(t,\beta)$，Jacobian 行列式满足
$$
\Delta=r_tz_\beta-r_\beta z_t\ge\nu t/4>0.
\tag{25.108}
$$

证明。Taylor 积分式及其参数微分给
$$
\begin{aligned}
|r-\nu t|&\le A_rt^2/2,& |r_t-\nu|&\le A_rt,& |r_\beta|&\le A_1t^2/2,\\
|z-\beta t|&\le C_zt^2/2,& |z_t-\beta|&\le C_zt,& |z_\beta-t|&\le C_1t^2/2.
\end{aligned}
\tag{25.109}
$$
例如 $r-\nu t=\int_0^t(t-v)r_{tt}(\beta,v)dv$；混合导数连续使在此积分下对 $\beta$ 求导合法，其余五式同理。因此 $\nu/2\le r_t\le3\nu/2$，积分得 $(\nu/2)t\le r\le(3\nu/2)t$。更精细地 $r(\beta,T)\ge3\nu T/4>s_*$，故介值性及严格时间单调性给唯一阈值时刻，且正阈值严格在 $T$ 之前。隐函数定理在这些内部时间点适用；参数开邻域保证区间端点的导数也是限制所得。$s=0$ 时 $t_\beta(0)=0$，公式按单侧连续意义延伸。

链式法则必须保留参数依赖的阈值时间，给（25.105）的首式。记 $t=t_\beta(s)$，有
$$
|\partial_\beta G_s-t|
\le\left(C_1/2+A_1(B+C_zT)/\nu\right)t^2
\le\kappa t^2\le t/2.
$$
结合（25.104）的时间界即得两侧导数界；再用 $|t-s/\nu|\le A_rt^2/(2\nu)$ 得二阶渐近界。因此每条正阈值图对参数严格递增。两份相等读数先落在同一正阈值，再由严格递增得同一参数，最后由 $r$ 的时间单调性得同一时间。连续严格单调函数的像是端点间闭区间，给（25.107）；单点参数时该像退化成一条曲线。$t\le T/3$ 保证 $r\le s_*$。最后 $\Delta=r_t\partial_\beta G_s\ge(\nu/2)(t/2)$。此证明没有把 $r$ 假定成与参数无关，也没有将 $t=s/\nu$ 或 $\beta=\nu w/s$ 当作精确反演式。$\square$

**定理 25.3（两份实际读数的参数与时间误差）。** 对 $(s,w)=\Psi(\beta,t)$、$(s',w')=\Psi(\beta',t')\in Y$，置 $m=\min\{s,s'\}>0$。则
$$
|\beta-\beta'|\le\frac{3\nu}{m}\bigl(|w-w'|+L_g|s-s'|\bigr),
\tag{25.110}
$$
$$
|t-t'|\le\frac2\nu|s-s'|+
 \frac{4A_1m^2}{\nu^3}|\beta-\beta'|,
\tag{25.111}
$$
因而
$$
|t-t'|\le\left(\frac2\nu+\frac{12A_1L_gm}{\nu^2}\right)|s-s'|
 +\frac{12A_1m}{\nu^2}|w-w'|.
\tag{25.112}
$$
若同一测得坐标的真实点和拟合点均在 $s\ge s_0>0$ 的图中，且各有坐标残差至多 $\epsilon_r,\epsilon_z$，则参数差至多 $6\nu(\epsilon_z+L_g\epsilon_r)/s_0$。

证明。由（25.104）和（25.109），$|\partial_sG_s|=|z_t/r_t|\le L_g$。不妨 $s=m\le s'$，则在同一阈值 $m$ 比较两个参数，得到
$$
\frac{m}{3\nu}|\beta-\beta'|
\le|G_m(\beta)-G_m(\beta')|
\le |w-w'|+L_g(s'-m).
$$
这给（25.110）。阈值时间的导数满足 $|\partial_st|\le2/\nu$，在 $m$ 处 $|\partial_\beta t_\beta(m)|\le A_1t_\beta(m)^2/\nu\le4A_1m^2/\nu^3$；同样先同阈值比参数再移动阈值给（25.111），代入得（25.112）。噪声结论用两个候选之间的坐标差各至多两倍残差界。测得坐标本身无需在 $Y$ 中。

正阈值下截断图的逆统一 Lipschitz；靠近零时参数界的 $1/m$ 因子不能仅凭时间界删掉。例如合法响应 $r=\nu t,z=\beta t$ 在固定 $t$ 给 $|\delta z|=t|\delta\beta|$，已排除延伸到零的统一参数 Lipschitz 常数。$\square$

**约定 25.4（同轨迹同时取得与未知钟）。** 双端口实际取得须同时、不扰动，或有已认证的等价共同轨迹，使两数确实等于同一 $\Psi(\beta,t)$。仅有“两个仪器同时开机”不足以证明测量干预没有改变方程。固定同一个严格递增连续钟 $t=h(\theta)$、$h(0)=0$。如果实际 $(\beta,h(\theta))\in W$，同时读数经上述逆确定参数和该样点的内部时间，无需钟导数。有限多个样点只确定相应 $h(\theta_i)$，不确定未采样插值。校准、黏性、模型和已知准备幅度必须在所有候选间固定。

阈值 $s$ 是已读第一坐标，不额外算一次导数测量。若实际采用首次阈值触发，则另须有事件检测权限、第一分支保证，以及 $h(\theta_{\rm end})\ge t_\beta(s)$ 的可达性；$h(\theta_{\rm end})\ge2s/\nu$ 或 $\ge T$ 是充分条件。连续性给到达，初始分支严格单调性给唯一首次交叉。仅严格增的钟 $h(\theta)=c(1-e^{-\theta})$ 在 $0<c<t_\beta(s)$ 时永远不到阈值。任意迟时样点的 $r$ 数值小也不证明它在初始分支；预定外部时刻需独立的内部时间上界或分支证书。

**定义 25.5（完整观察者与共同实现交集）。** 完整观察者明确写为
$$
H=(C,\mathcal A,d_{\rm raw}).
\tag{25.113}
$$
$C$ 包含所有已取得的内部／外部旧记录及其关系；$\mathcal A$ 是带来源索引的合法取得历史，保留每次动作、端口、外部标签、校准及共同轨迹证书；$d_{\rm raw}$ 是当前实际原始对，不能由预测值代写。

固定模型和校准后，令 $\Omega$ 为完整实现集合。每个 $\omega\in\Omega$ 同时包含一个来源身份、参数 $\beta(\omega)$、同一准备生成的整条实际轨迹、一个共同钟 $h_\omega$，以及解释全部旧记录所需的辅助变量、误差和关系。每条旧记录 $c_i\in C$ 有其声明的约束 $\mathcal R_i(\omega,c_i)$；关系可包括跨端口、跨时刻和跨来源的已获信息，不能逐条另选实现。令 $\operatorname{Hist}(\omega,\mathcal A)$ 断言该一份实现确实支持所记合法取得及同时无扰动／等价轨迹条件。当前外部时刻 $\theta_*$ 的内部时刻为 $t(\omega)=h_\omega(\theta_*)$。将原始对按固定校准换为 $(r_{\rm obs},z_{\rm obs})$，其共同误差事件记为 $\mathcal E_H$。定义
$$
\begin{aligned}
\mathfrak F_H=\{\omega\in\Omega:\;&\operatorname{Hist}(\omega,\mathcal A),\quad
 \mathcal R_i(\omega,c_i)\ \text{对全部旧记录成立},\\
 & (\beta(\omega),t(\omega))\in W,\quad \omega\in\mathcal E_H,\\
 &|r(\beta(\omega),t(\omega))-r_{\rm obs}|\le\epsilon_r,\\
 &|z(\beta(\omega),t(\omega))-z_{\rm obs}|\le\epsilon_z\},
\end{aligned}
\tag{25.114}
$$
并令 $K_H=\{(\beta(\omega),t(\omega)):\omega\in\mathfrak F_H\}$。如果原始实际误差为 $|x_{\rm obs}-x|\le\epsilon_x$、$|y_{\rm obs}-y|\le\epsilon_y$，且 $r=1-2x/\alpha,z=-4y/\alpha$，则在同一个联合误差事件上使用
$$
\epsilon_r=2\epsilon_x/|\alpha|,\qquad
\epsilon_z=4\epsilon_y/|\alpha|.
\tag{25.115}
$$
此处 $\alpha$ 已知固定，不将含噪幅度代入当作新的联合识别证明。$\mathcal E_H$ 可以施加更强的相关误差约束，无独立噪声前提。

**命题 25.6（外包界可限制，档案见证不可省略）。** 令
$$
K_{\rm pair}=\{(\beta,t)\in W:
 |r(\beta,t)-r_{\rm obs}|\le\epsilon_r,
 |z(\beta,t)-z_{\rm obs}|\le\epsilon_z\}.
\tag{25.116}
$$
则 $K_H\subseteq K_{\rm pair}$。定理25.3对任意两个外包候选的直径上界也对 $K_H$ 成立；第27节的共同剩余时域界亦如此。但是声称拟合点与完整档案相容，必须给 $\widehat\omega\in\mathfrak F_H$，不能只给 $(\widehat\beta,\widehat t)\in K_{\rm pair}$。

证明。集合包含由（25.114）投影直接得到；全称成对不等式可限制到子集。反方向失败：某条旧约束可能要求 $\beta=b_-$，而当前精确对只由另一个参数生成，外包非空而交集空。全部旧记录分别可拟合也不推出一个共同 $\omega$ 存在。若实际来源、档案、第一分支和联合误差假设均成立，真实 $\omega$ 就给非空见证；否则不能以空集上的真空全称断言授权动作。完整 $H$ 的保留还意味着从两数恢复场并不等于从两数重建整份档案。$\square$

## 26. 全 PDE 的参数差商与联合识别实例

**定理 26.1（开邻域上的实际参数导数）。** 固定已知 $\nu>0$、$0<a\le|\alpha|\le A_\alpha$ 及 $B_0\ge0$，使用[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定义25.1的全部空间、归一化、准备和常数 $R,\tau$。令 $X=C([0,\tau];H^2_\sigma)$、$\lambda=1/(4R)$、$\delta_\beta=R/24$。同一实际温和解可定义在参数开区间
$$
J_\beta=(-B_0-\delta_\beta,B_0+\delta_\beta),
\tag{26.101}
$$
且 $\beta\mapsto u_\beta\in X$ 为 $C^1$，满足
$$
\|\partial_\beta u_\beta\|_X\le6.
\tag{26.102}
$$

证明。只使用恢复卷定理25.3的同一双线性算子 $\mathcal B$，不重新构造 PDE。将 $\beta$ 投影到 $[-B_0,B_0]$，初态范数增加至多 $3\delta_\beta=R/8$，故开区间初态范数小于或等于 $5R/8$。同一 $R$ 球上的映射像范数至多 $5R/8+R/4=7R/8$，收缩系数仍为 $1/2$。因此同一时间与同一球适用，且相减仍给 $\|u_\beta-u_\gamma\|_X\le6|\beta-\gamma|$。

定义有界线性算子 $\mathcal A_\beta v=\mathcal B(v,u_\beta)+\mathcal B(u_\beta,v)$，其范数至多 $2\lambda R=1/2$。Neumann 级数给 $(I+\mathcal A_\beta)^{-1}$，范数至多二。令
$$
v_\beta=(I+\mathcal A_\beta)^{-1}E(\cdot)b_0,
\quad
v_\beta=E(\cdot)b_0-\mathcal B(v_\beta,u_\beta)-\mathcal B(u_\beta,v_\beta).
\tag{26.103}
$$
$\|b_0\|_{H^2}=3$ 给 $\|v_\beta\|_X\le6$。对 $h\ne0$ 且 $\beta+h\in J_\beta$，实际差商 $q_h=(u_{\beta+h}-u_\beta)/h$ 满足 $\|q_h\|_X\le6$。将两个二次温和方程精确相减得
$$
(I+\mathcal A_\beta)q_h=E(\cdot)b_0-h\mathcal B(q_h,q_h),
\quad
\|q_h-v_\beta\|_X\le72\lambda|h|.
\tag{26.104}
$$
这证明真实参数导数存在于整个时间 Banach 空间，而不是假定逐点可微。再将（26.103）在两参数处相减，得到
$$
\|v_\beta-v_\gamma\|_X
\le2\|\mathcal A_\beta-\mathcal A_\gamma\|\,\|v_\gamma\|_X
\le24\lambda\|u_\beta-u_\gamma\|_X
\le144\lambda|\beta-\gamma|.
\tag{26.105}
$$
故导数连续；原闭区间端点的导数来自这个真正的开邻域。$\square$

**定理 26.2（$DF$、$DG$ 与连续混合端口界）。** 继续使用恢复卷的 $F:H^2_\sigma\to L^2_\sigma$、$Q_\phi$、$G_\phi$、$M_F,D_F,J,M$。对其任一配对端口 $(\ell,\phi)$，
$$
DF(u)h=\nu\Delta h-\mathbb P((h\cdot\nabla)u+(u\cdot\nabla)h),
$$
$$
DG_\phi(u)h=-\nu\ell(DF(u)h)
 -D^2Q_\phi(h,F(u))-DQ_\phi(u)DF(u)h.
\tag{26.106}
$$
这些是连续 Fréchet 导数；在半径 $R$ 球中
$$
\|DF(u)h\|_2\le D_F\|h\|_{H^2},\qquad
|DG_\phi(u)h|\le J\|h\|_{H^2}.
\tag{26.107}
$$
实际两个端口满足
$$
|x_{tt}|,|y_{tt}|\le M,\qquad
|\partial_\beta x_{tt}|,|\partial_\beta y_{tt}|\le6J,
\tag{26.108}
$$
这些混合导数在参数与时间上连续，包含时间零点的单侧值。

证明。恢复卷的 $\|u\|_\infty\le4\|u\|_{H^2}$ 使对流为连续双线性映射 $H^2\times H^2\to L^2$。二次展开余项至多 $4\|h\|_{H^2}^2$，故 $DF$ 的公式与连续性确实成立，范数界为 $\nu+8R$。恢复卷引理25.5已在完整 $L^2$ 空间证明 $Q_\phi,DQ_\phi,D^2Q_\phi$ 及其界；此处对 $G_\phi=-\nu\ell F-DQ_\phi(\cdot)F$ 用乘积法则，给（26.106）。三项界之和为
$$
\nu D_F+M_F+RD_F=\nu^2+10\nu R+12R^2=J.
$$
$G_\phi$ 是 $H^2$ 上连续线性、双线性、三线性映射之和。将这些映射逐时作用于 $C_tH^2$，仍为连续多线性映射，因而诱导映射 $C_tH^2\to C_t\mathbb R$ 为 $C^1$，导数逐时为 $DG_\phi$。定理26.1于是给
$$
\partial_\beta a_{tt}(\beta,t)=DG_\phi(u_\beta(t))v_\beta(t),
$$
范数至多 $6J$，且联合连续。绝对二阶界是恢复卷定理25.6的 $M$。最后由
$$
a(\beta,t)=a(\beta,0)+t a_t(\beta,0)
 +\int_0^t(t-s)G_\phi(u_\beta(s))\,ds
\tag{26.109}
$$
在连续时间函数空间对参数求导，其结果可再对时间微分两次，正好得到上式。因此没有把未证的混合导数交换作为前提，也没有要求 $u_{tt}\in L^2$ 或 $u_t\in H^2$。$\square$

**推论 26.3（已校准 PDE 的双端口绝对钟图）。** 对恢复卷（25.115）的实际端口置
$$
r=1-2x/\alpha,\qquad z=-4y/\alpha,\qquad
A_r=2M/a,\quad C_z=4M/a,\quad A_1=12J/a,\quad C_1=24J/a.
\tag{26.110}
$$
取 $I=[-B_0,B_0]$、$T_0=\tau$，并取
$$
\kappa=C_1/2+A_1(B_0+C_z\tau)/\nu,
\quad T=\min\{\tau,\nu/(2A_r),1/(2\kappa)\},\quad s_*=\nu T/2.
\tag{26.111}
$$
则定义25.1的全部条件实际成立，定理25.2、25.3的图、精确像、单射性及全部误差界适用于这个全 PDE。这里 $A_r,\kappa$ 严格正，故公式无零分母。

证明。恢复卷的初始系数识别给 $x(0)=\alpha/2$、$y(0)=0$、$y_t(0)=-\alpha\beta/4$。没有两个非零初始频率相加为 $(1,0)$，所以该处非线性导数为零，$x_t(0)=-\nu\alpha/2$。由真实 $u_t=F(u)$ 得 $r_t(0)=\nu,z_t(0)=\beta$，并非有限槽的代数代替了演化。定理26.2乘固定比例并用 $|\alpha|\ge a$ 给（26.110），定理26.1供应开邻域。时间选择满足（25.103），直接使用已证一般图定理即可。

在同轨迹同时读出及第一分支条件下，一对正时原始数据确定 $\beta$ 和该样点内部时间；多个样点仍只给采样处的钟值。带噪应用须用定义25.5的一份实现与联合事件，尤其原始误差转换严格为（25.115）。本结论固定 $\alpha,\nu$、模型及校准；恢复卷的含噪 $\alpha$ 标量估计不将这些固定量变成未知量。

若 $B_0>0$，不同初态在时间零的规范读数全为 $(0,0)$，所以不能将它加入原始图并保留单射性。若 $B_0=0$，初态已知且参数域单点，$r_t\ge\nu/2$ 使加入时间零仍单射；正阈值的参数除法界仍只在其原声明域内使用。$\square$

**命题 26.4（未知黏性的精确钟碰撞与条件性纤维）。** 在 $\beta=0$ 的实际 PDE 中，
$$
u(X,t)=\alpha e^{-\nu t}(0,\cos X_1),\quad p=0,
\quad r=1-e^{-\nu t},\quad z=0.
\tag{26.112}
$$
两种正黏性及满足 $\nu_1h_1=\nu_2h_2$ 的钟给相同的整个双端口历史，故未知黏性下不能在包含此准备的族上由这些历史恢复绝对内部时间。该例不证明隐藏参数不同，因为两例都取 $\beta=0$。

证明。该剪切的对流为零、Laplacian 为负自身，所以方程逐项成立；读出与钟等式直接代入即得。一般混合合同本身也不能识别三个量：精确响应 $r=\nu t,z=\beta t$ 在 $(\nu,\beta,t)\mapsto(c\nu,c\beta,t/c)$ 下不变。后者只是合同反例，不是固定 $\alpha$ 的非线性 PDE 缩放定律。

另有如下严格条件命题：若额外证明实际响应在正黏性开邻域对 $(\nu,\beta,t)$ 为 $C^1$，且在所考察内点有统一渐近
$$
r_\nu=t+O(t^2),\quad z_\nu=O(t^2),\quad
r_t=\nu+O(t),\quad z_t=\beta+O(t),\quad
r_\beta=O(t^2),\quad z_\beta=t+O(t^2),
\tag{26.113}
$$
则固定一对足够短正时读数时，隐函数定理给随 $\nu$ 改变的精确局部纤维 $(\beta(\nu),t(\nu))$，且
$$
\frac{dt}{d\nu}=\frac{r_\beta z_\nu-z_\beta r_\nu}{\Delta}
=-\frac t\nu+O(t^2),\quad
\frac{d\beta}{d\nu}=\frac{z_t r_\nu-r_tz_\nu}{\Delta}
=\frac\beta\nu+O(t).
\tag{26.114}
$$
证明这个条件命题只需定理25.2的非零 Jacobian：对固定读数求导解二乘二线性方程，代入（26.113）及 $\Delta=\nu t+O(t^2)$ 即得。在非零内点 $\beta$ 处，充分小时间使两导数非零。定理26.1仅证明固定黏性下的 $\beta$ 可微性，没有证明（26.113）的黏性前提，所以这里保持条件命题；不将它升级为本节已履行的 PDE 黏性识别或不识别结论。更多端口或整条非退化响应曲线需要另行研究。$\square$

## 27. 比值边界、完整场因子与部分续接

**定理 27.1（隐藏初始方向的正则比值坐标）。** 固定推论26.3的全部准备、黏性、常数和第一分支。置
$$
\vartheta(\beta,t)=\nu z(\beta,t)/r(\beta,t)\quad(t>0),
\qquad \vartheta(\beta,0)=\beta,
$$
$$
Z_*=B_0+C_zT/2,\quad E_\vartheta=C_z+A_rB_0/\nu,
\quad L_\vartheta=C_z+2A_rZ_*/\nu,
\quad D_\vartheta=C_1+A_r/\nu+2A_1Z_*/\nu.
\tag{27.101}
$$
则 $\vartheta$ 是 $[-B_0,B_0]\times[0,T]$ 上的 $C^1$ 函数（时间端点单侧），并有
$$
|\vartheta-\beta|\le E_\vartheta t,\quad
|\vartheta_t|\le L_\vartheta,\quad
|\vartheta_\beta-1|\le D_\vartheta t,
\quad 1/3\le\vartheta_\beta\le3.
\tag{27.102}
$$
初始边界导数为
$$
\vartheta_\beta(\beta,0)=1,\qquad
\vartheta_t(\beta,0)=\tfrac12 z_{tt}(\beta,0)
 -\frac{\beta}{2\nu}r_{tt}(\beta,0).
\tag{27.103}
$$

证明。先分离已知的一阶时间零点，定义
$$
U(\beta,t)=\int_0^1r_t(\beta,qt)\,dq,
\quad V(\beta,t)=\int_0^1z_t(\beta,qt)\,dq.
\tag{27.104}
$$
于是 $r=tU,z=tV$，$U(\beta,0)=\nu,V(\beta,0)=\beta$。第26节的连续混合正则性保证 $U,V$ 均 $C^1$，且由（25.109）积分得到
$$
\begin{gathered}
U\ge\nu/2,\quad |U-\nu|\le A_rt/2,\quad
|V-\beta|\le C_zt/2,\quad |V|\le Z_*,\\
|U_t|\le A_r/2,\quad |V_t|\le C_z/2,\quad
|U_\beta|\le A_1t/2,\quad |V_\beta-1|\le C_1t/2.
\end{gathered}
\tag{27.105}
$$
因此 $\nu V/U$ 就是在零点也有定义的 $C^1$ 延伸。由 $\nu V-\beta U=\nu(V-\beta)+\beta(\nu-U)$ 得第一误差界；对商求时间导数，用（27.105）给 $C_z+2A_rZ_*/\nu$。参数导数减一，分别界定 $\nu(V_\beta-1)/U$、$\nu/U-1$ 及 $\nu VU_\beta/U^2$，得到 $D_\vartheta t$。代入零点的积分导数给（27.103）。

正的参数导数不需再缩短 $T$。对 $t>0$，
$$
\vartheta_\beta=\frac\nu r\left(z_\beta-\frac zr r_\beta\right),\qquad
\left|z_\beta-\frac zr r_\beta-t\right|
\le\left(C_1/2+A_1Z_*/\nu\right)t^2
\le\kappa t^2\le t/2.
$$
再用 $(\nu/2)t\le r\le(3\nu/2)t$ 得 $1/3\le\vartheta_\beta\le3$，零点由（27.103）直接成立。$\square$

**定理 27.2（闭合提升图及两种完成）。** 令
$$
\overline W=\{(\beta,t):|\beta|\le B_0,\ 0\le t\le T,
\ r(\beta,t)\le s_*\},\quad
\widetilde\Psi(\beta,t)=(r(\beta,t),\vartheta(\beta,t)).
\tag{27.106}
$$
该图在闭域上单射，且为双 Lipschitz 坐标。置 $\Theta_s(\beta)=\vartheta(\beta,t_\beta(s))$，包括 $\Theta_0(\beta)=\beta$，$L_s=2L_\vartheta/\nu$。其精确像是闭带
$$
\widetilde Y=\{(s,v):0\le s\le s_*,\quad
\Theta_s(-B_0)\le v\le\Theta_s(B_0)\},
\tag{27.107}
$$
且任意两份提升图读数 $(s,v),(s',v')$、$m=\min\{s,s'\}\ge0$ 满足
$$
|\beta-\beta'|\le3(|v-v'|+L_s|s-s'|),
\qquad
|t-t'|\le\frac2\nu|s-s'|+
 \frac{4A_1m^2}{\nu^3}|\beta-\beta'|.
\tag{27.108}
$$
当 $B_0>0$ 时，原始正时间图 $Y$ 的 Euclidean 完成只在初始边界加一个点 $(0,0)$，提升图正时间部分的 Euclidean 完成却加整段 $\{0\}\times[-B_0,B_0]$。两种误差几何在该边界附近不统一等价。

证明。正 $s$ 处，$\Theta_s=(\nu/s)G_s$，所以（25.105）给 $1/3\le\partial_\beta\Theta_s\le3$；零点的导数为一。$|\partial_s\Theta_s|=|\vartheta_t/r_t|\le L_s$。正时间的单射性复用定理25.2；$s=0$ 强制 $t=0$，第二坐标恰是参数。连续单调阈值图给闭带像。两参数先在较小阈值 $m$ 比较，再沿阈值移动，得（27.108）；$m=0$ 时阈值时间恒为零，所以其参数变化项就是零，毋须除零或极限论证。前向估计为
$$
|s-s'|\le\tfrac12A_1T^2|\beta-\beta'|+\tfrac32\nu|t-t'|,
\quad
|v-v'|\le3|\beta-\beta'|+L_\vartheta|t-t'|.
\tag{27.109}
$$
这是沿环境参数／时间矩形的两段比较，故不要求连接线留在 $\overline W$。逆估计中的 $m\le s_*$ 给统一常数，证明双 Lipschitz 性。

正时 Jacobian 为
$$
r_t\vartheta_\beta-r_\beta\vartheta_t
=\frac\nu r\Delta\ge\nu/6,
\tag{27.110}
$$
零时为 $\nu$。若需普通开集上的局部逆，可以在负时间附近定义 $U=\nu+t r_{tt}(\beta,0)/2$、$V=\beta+t z_{tt}(\beta,0)/2$。第26节混合导数使这些初始系数对参数 $C^1$，两侧的一阶值吻合，给 $C^1$ 延伸及非零 Jacobian。正阈值端点严格小于 $T$，参数端点有开邻域，故局部逆在所有相关边界均以限制意义成立。此代数延伸不声称负时间 PDE 演化存在。

原始图精确分解为
$$
(\beta,t)\longmapsto(s,\vartheta)
\longmapsto(s,s\vartheta/\nu)=(r,z).
\tag{27.111}
$$
闭参数／阈值域紧，两个完整像均为紧集，其正阈值部分稠密，故各自闭像就是各自 Euclidean 完成。第二映射在 $s=0$ 将整段压为一点。选不同的 $\beta,\beta'$，$s_n=s_*/(n+1)\downarrow0$，两原始序列 $(s_n,G_{s_n}(\beta))$、$(s_n,G_{s_n}(\beta'))$ 均趋 $(0,0)$，但提升序列分别趋 $(0,\beta)$、$(0,\beta')$。所以原始到提升的正时间变换不统一连续。普通原始度量的完成不能凭空恢复这些标签。

已有 [GoldenThreadBlowup](../../../D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.lean) 的 `golden_thread_completion_value_eq`、`golden_thread_tangent_injective` 与 `golden_geometric_thread_origin_recovery` 分别给相同完成值、可区别的来源切向与有限深度交比重标后的来源恢复。本节使用同样的“端点值与归一化方向不同”区分，其实际 PDE 估计与取得条件由第25—26节供应，不声称除以消失坐标能增加观测信息。该来源中的几何 blowup 是坐标分辨，和恢复卷第26节的流体奇异性不同。$\square$

**命题 27.3（比值噪声与原始读数的必要误差量级）。** 在正时间实际对 $(s,w)=(r,z)$ 上，若 $|\delta s|\le\epsilon_r<s$、$|\delta w|\le\epsilon_z$，计算比值 $\widetilde\vartheta=\nu(w+\delta w)/(s+\delta s)$ 满足
$$
\widetilde\vartheta-\vartheta
=\frac{\nu\delta w-\vartheta\delta s}{s+\delta s},\qquad
|\widetilde\vartheta-\vartheta|
\le\frac{\nu\epsilon_z+|\vartheta|\epsilon_r}{s-\epsilon_r}.
\tag{27.112}
$$
又 $|\vartheta|\le2Z_*$；$\epsilon_r\le s/2$ 时上界至多 $2(\nu\epsilon_z+2Z_*\epsilon_r)/s$。当 $B_0>0$，仅由一对读数、内部时间未知且没有进一步区分这对候选的档案时，即使第一坐标精确已知，任意确定性参数估计器的最坏误差至少为
$$
\min\{B_0,\nu\epsilon_z/(3s)\}.
\tag{27.113}
$$

证明。通分给（27.112），分母和三角界给所列估计，$\vartheta=\nu V/U$ 给 $2Z_*$。取 $d=\min\{B_0,\nu\epsilon_z/(3s)\}$。参数 $d,-d$ 在各自阈值时间的第二读数相差至多 $6sd/\nu\le2\epsilon_z$，由（25.105）的上界积分可得；第一读数均为 $s$。共同中点同时是两种合法含噪输出，参数相距 $2d$，故至少一个估计误差不小于 $d$。$d=0$ 时下界自然为零。

此两点论证针对仅此原始对的外包合同；若加入旧档案 $C$ 或精确时间旁路，须另证明两候选都在同一个 $K_H$ 中，不能自动把下界限制到任意较小交集。$B_0=0$ 时参数已知，不存在该参数歧义。单个初始原始对 $(0,0)$ 不能计算 $\vartheta(\beta,0)=\beta$；该边界标签需独立提供。提升图的统一稳定性针对提升坐标自身的误差，原始测量转换的 $1/s$ 代价仍在。$\square$

**命题 27.4（准备场上的既有精确因子化及其定量界）。** 置
$$
\mathcal S=\{u_\beta(t):(\beta,t)\in W\},\quad
\mathcal I=\Psi^{-1}:Y\to W,\quad
\mathcal D(a)=u_\beta(t)\ \text{其中 }\mathcal I(a)=(\beta,t),
$$
$$
\mathcal O(U)=(1-2\ell_x(U)/\alpha,-4\ell_y(U)/\alpha).
\tag{27.114}
$$
则 $\mathcal O|_{\mathcal S}$ 与 $\mathcal D$ 互逆。因此任意精确任务 $\mathcal T:\mathcal S\to Z_{\mathcal T}$ 都在实际读数像上有唯一因子 $\mathcal T\circ\mathcal D$；这直接使用既有 [InjectiveInterfaceTargetFactorization](../../../D5/S3/ConceptDynamics/RefinementFactorization/InjectiveInterfaceTargetFactorization.lean) 的 `injective_interface_factors_every_target` 及 [RealizedImageKernelFactorization](../../../D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.lean) 的 `realized_image_unique_factorization_iff_reverse_kernel`，不是另立一般解码原理。

具体定量内容为
$$
\|u_\beta(t)-u_{\beta'}(t')\|_2
\le6|\beta-\beta'|+M_F|t-t'|.
\tag{27.115}
$$
对两份原始图坐标，令 $m=\min\{r,r'\}>0$、$P_m=6+4M_FA_1m^2/\nu^3$，则
$$
\|\mathcal D(r,z)-\mathcal D(r',z')\|_2
\le\frac{3\nu P_m}{m}(|z-z'|+L_g|r-r'|)
 +\frac{2M_F}{\nu}|r-r'|.
\tag{27.116}
$$
在提升闭图上，边界标签已给时定义 $\widetilde{\mathcal D}(\widetilde\Psi(\beta,t))=u_\beta(t)$；此时允许 $m=0$，且
$$
\|\widetilde{\mathcal D}(r,v)-\widetilde{\mathcal D}(r',v')\|_2
\le3P_m(|v-v'|+L_s|r-r'|)+\frac{2M_F}{\nu}|r-r'|.
\tag{27.117}
$$

证明。直接有 $\mathcal O(\mathcal D(a))=a$。若 $U=u_\beta(t)\in\mathcal S$，则 $\mathcal O(U)=\Psi(\beta,t)$，图单射给 $\mathcal D(\mathcal O(U))=U$。所以观察在此准备场集合上单射，满足所引现成精确因子化前提。恢复卷（25.106）在共同时间比较参数，恢复卷（25.111）的 $L^2$ 速度界在时间段积分，得（27.115）；没有声称 $H^2$ 时间速度有同一界。代入本卷（25.110）—（25.111）得（27.116），代入（27.108）得（27.117）。提升边界的初态由已给 $\beta$ 决定，定义良好。

任意精确任务可因子化，不意味着它定量稳定。若另外证明 $d_{\mathcal T}(\mathcal T(U),\mathcal T(V))\le L_{\mathcal T}\|U-V\|_2$，才可将这些界乘 $L_{\mathcal T}$；更一般须有自己的 $L^2$ 连续模数。点值、梯度或不连续任务不能自动使用此结论。解码对象是准备场及指定任务，不是整个 $C$ 或取得历史。两数充分也没有证明它们在所有可能传感器或费用合同中全局最优。$\square$

**定理 27.5（续接的定义域等式与自主 PDE 交织）。** 写 $t_*(\beta)=t_\beta(s_*)$，则 $W=\{(\beta,t):|\beta|\le B_0,0<t\le t_*(\beta)\}$。对已知非负内部增量 $\sigma$，定义域子类型上的操作为
$$
\operatorname{Dom}_\sigma=\{a\in Y:\mathcal I(a)=(\beta,t),\quad
 0\le\sigma\le t_*(\beta)-t\},\qquad
\mathcal U_\sigma(a)=\Psi(\beta,t+\sigma).
\tag{27.118}
$$
对任意 $\sigma,\eta\ge0$，
$$
\operatorname{Dom}_{\sigma+\eta}
=\{a\in\operatorname{Dom}_\sigma:\mathcal U_\sigma(a)\in\operatorname{Dom}_\eta\},
\qquad \mathcal U_{\sigma+\eta}=\mathcal U_\eta\circ\mathcal U_\sigma,
\quad\mathcal U_0=\operatorname{id}.
\tag{27.119}
$$
若 $S_\sigma$ 是实际自主 PDE 从该准备场重启的、限制在上述允许域内的续接，则
$$
\mathcal D(\mathcal U_\sigma(a))=S_\sigma(\mathcal D(a))=u_\beta(t+\sigma).
\tag{27.120}
$$
同样的定义与等式适用于边界标签已供给的提升图。

证明。$r$ 在初始分支严格递增，给域的精确形式。两次合法条件分别为 $\sigma\le t_*(\beta)-t$ 和 $\eta\le t_*(\beta)-t-\sigma$，非负增量下它们等价于 $\sigma+\eta\le t_*(\beta)-t$，同时中间时刻必在域内。图逆在第一步后给 $(\beta,t+\sigma)$，代入第二步即得值的复合等式。零步不改变参数或时间，且总在图内合法。移位路径 $q\mapsto u_\beta(t+q)$ 从 $u_\beta(t)$ 解同一自主方程；恢复卷的温和解唯一性将它识别为重启解，证明（27.120）。

对两个都允许同一 $\sigma$ 的图点，推进后参数差及时间差不变，仍在共同 PDE 区间内，故（27.115）仍给相同右界；代入原始输入或提升输入的参数／时间界，（27.116）或（27.117）的原右侧也界定其推进后的场差。这里没有声称实际误差在演化中单调下降。

这些部分操作属于本卷约定1.2和命题1.4的域保持语义；[StrictOneHoleContexts](../../../D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean) 的 `PartialSignature`、`sourceOperationEquiv` 及 `contextual_equivalence_is_greatest` 已供应域子类型与严格失败传播的形式接口。可将 $\mathcal U_\sigma$ 总化为成功／失败标签，任何失败后的续接仍传播该失败，不返回一个默认场。域外输入与域内却超越剩余时域的非法增量应分别标记；两类都不同于下面的噪声证书未通过。$\square$

**约定 27.6（实际观察者操作保留档案）。** （27.118）是精确图坐标上的数学更新。对完整观察者 $H=(C,\mathcal A,d_{\rm raw})$ 执行操作时，旧 $C$ 逐条保留，当前原始对连同来源、原标签及误差合同保留为旧记录；实际执行的内部推进及新取得动作追加到 $\mathcal A$。若协议确实在推进后取得新的同轨迹双端口对，才把该原始对放入新的 $d_{\rm raw}$，并将其残差与全部旧约束一起加入同一个延伸实现集合。新的相容集合是旧共同实现先经实际操作运输，再与实际新记录约束取交。

若只计算 $\mathcal U_\sigma(a)$、$\mathcal D(a)$ 或预测的新读数，它们只能作为标明的派生值；没有执行推进就不记已推进，没有重新取得就保留最近原始对的原时间标签，不将预测冒充当前测量。两次推进之间取得一次额外记录，会让完整取得历史不同于直接推进一次；（27.119）保证参数、场及合法域的复合等式，不抹去这项历史区别。历史按实际动作序列串接，结合律保留记录次序；只有声明同一个展开协议时，才可将两种动作写法视为同一历史。

严格失败语义至少区分：输入精确值不在图中；共同实现集 $\mathfrak F_H$ 为空；已有精确图点但 $\sigma$ 超过（27.118）的上界；共同实现非空但噪声裕量证书没有通过。前三者均不能通过默认补一个状态继续；第四者表示尚未认证，不能推断实际增量非法。若采用总化编码，这些标签都在其后的严格接续中原样传播。由于 $\mathfrak F_H=\varnothing$ 没有实际见证，即使零步也不能以它认证一个被假定存在的来源；对任意非空相容图集合，零步始终是合法恒等操作。

**定理 27.7（完整相容集合的剩余时域证书）。** 定义
$$
\ell_{\rm rem}(\beta,t)=t_\beta(s_*)-t,\qquad
K_*=4A_1s_*^2/\nu^3.
\tag{27.121}
$$
取定义25.5的一份实际档案相容拟合见证 $\widehat\omega\in\mathfrak F_H$，其投影为 $(\widehat\beta,\widehat t)$。若
$$
\underline r=r_{\rm obs}-\epsilon_r>0,
\quad B_{\rm err}=\frac{6\nu}{\underline r}(\epsilon_z+L_g\epsilon_r),
\quad T_{\rm err}=\frac{4\epsilon_r}{\nu}+K_*B_{\rm err},
$$
$$
E_{\rm adm}=\frac{4\epsilon_r}{\nu}+2K_*B_{\rm err},\qquad
\widehat\ell=\ell_{\rm rem}(\widehat\beta,\widehat t),
\tag{27.122}
$$
则任意两个 $K_H$ 中的候选参数差、时间差分别至多 $B_{\rm err},T_{\rm err}$，剩余时域差至多 $E_{\rm adm}$。因此每个相容候选都允许同一个已知内部增量
$$
0\le\sigma\le\max\{0,\widehat\ell-E_{\rm adm}\}.
\tag{27.123}
$$
推进后实际相容场与拟合续接场满足
$$
\|u_\beta(t+\sigma)-u_{\widehat\beta}(\widehat t+\sigma)\|_2
\le6B_{\rm err}+M_FT_{\rm err}.
\tag{27.124}
$$
该区间仅为充分证书；不能认证某正增量，不证明该增量非法。

证明。阈值时间导数给 $|\partial_\beta t_\beta(s_*)|\le K_*$，故
$$
|\ell_{\rm rem}(\beta,t)-\ell_{\rm rem}(\beta',t')|
\le K_*|\beta-\beta'|+|t-t'|.
\tag{27.125}
$$
先对较大的 $K_{\rm pair}$ 证明界：任意两个候选坐标差至多 $2\epsilon_r,2\epsilon_z$，其较小真实第一坐标满足 $\underline r\le m\le s_*$。定理25.3依次给 $B_{\rm err}$、$4\epsilon_r/\nu+K_*B_{\rm err}$，代入（27.125）给 $E_{\rm adm}$。这些全称界通过 $K_H\subseteq K_{\rm pair}$ 限制到真正档案交集；拟合点具有交集见证，故任意实际相容剩余时域至少 $\widehat\ell-E_{\rm adm}$。正裕量情形可用（27.118）；若该数为负，只保留零步，零步由图域定义独立合法。因此（27.123）在所有情况成立，且从未对负裕量作不合法的正步授权。（27.124）是（27.115）的直接应用。

若实际来源确在初始图上、旧档案相容、同时取得条件成立且共同误差事件为真，则真实实现在 $\mathfrak F_H$，证书便约束真实动作。若交集空，或拟合只属于 $K_{\rm pair}$ 而无共同档案见证，不能称此证书已对完整观察者实例化。测得原始对不在精确图像中，并不自动使交集空；噪声情形须用残差判断。一个数值实现可以将 $\widehat\ell$ 换成其认证下界，但计算该下界与提供拟合见证仍有独立成本。

每个候选推进后的剩余时域都严格减去同一个 $\sigma$，与拟合的剩余时域差不变。因此对未新增测量的传播候选集，所有累计增量不超过原正裕量的序列继续被同一个 $E_{\rm adm}$ 支持；（27.119）给域与值的复合。实际新增记录只在同一延伸实现上进一步取交，不能重新挑一个不兼容的来源来维持拟合。

$B_0=0$ 时参数已知，可令 $B_{\rm err}=0$、$T_{\rm err}=E_{\rm adm}=4\epsilon_r/\nu$；$r_t\ge\nu/2$ 直接界定任意两候选的时间差，此单点版本可包含已知初始时刻且无需 $\underline r>0$。非空共同见证仍必需。对于非单点参数，正下界失败只表明（27.122）不能使用，不等于实际离开图域或正增量非法。$\square$

**注记 27.8（内部续接、来源标签与关系范围）。** 所有续接都要求已知内部时长 $\sigma$；未知共同钟下等待一个指定外部时长并不提供它，须另有时钟运输或实际取得证书。修改初态、外力、黏性、校准或测量干预是另一种操作，不能沿用当前的闭合域。越过 $t_*(\beta)$ 未获本接口许可，即使 PDE 本身仍可继续也一样。

在这里声明的自主非负推进下，恢复出的来源标签 $\beta$ 不变、内部时间平移；相同 $\beta$ 的两图点依时间顺序由一个允许前进量连接，不同 $\beta$ 则不能由这些操作连接。这是相对于规定操作的轨道标签，完整场仍随时间变化；它不表示所有空间场静止，也不把时间从空间推出。比值边界只是改变表示与误差几何，既不供应初始原始对所缺的标签，也不分配概率。

全场解码及响应逆的存在不使其求值免费：所需实际 PDE 求解、逆响应认证、端口取得、阈值监测、钟可达性和档案共同见证各有原来的资源条件。本文的数学陈述是普通证明，适用范围为固定准备族的共同短时图；有限维、全 PDE、精确识别、稳定性、合法操作和完整已获档案分别由各自明确条件承担。

## 27.99 追加锚

## 28. 有向初始图、三阶识别与黏性纤维

**定义 28.1（校准尺度与参数任务）。** 固定有符号且已校准的 $\alpha\ne0$，采用[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定义27.1的实际无外力 PDE、同源准备和端口。用
$$
p=(m,k)=\left(\frac\beta\nu,\frac{\alpha^2}{\nu^2}\right),\quad k>0,
\qquad \nu(p)=\frac{|\alpha|}{\sqrt k},\quad
\beta(p)=\frac{m|\alpha|}{\sqrt k}
\tag{28.101}
$$
作为参数坐标；它与 $(\beta,\nu)\in\mathbb R\times(0,\infty)$ 光滑互逆。$p$ 不表示流体压力。本节的图关系是同一实际轨迹上 $r_p(t)=1-2x_p(t)/\alpha$、$z_p(t)=-4y_p(t)/\alpha$ 所形成的有向初始关系。所有已获时间戳、钟限制、准备与旧档案关系仍按定义25.5保留；这里消去时间参数只为识别 $(\beta,\nu)$ 及指定准备场任务。

**定理 28.2（参数依赖的初始逆时间）。** 在任意紧参数集 $K$ 的开邻域内，缩短恢复卷的共同 $H^{12}$ 时间后，存在共同 $T_g,r_*>0$，使 $0\le r\le r_*$ 有唯一初始分支时间 $t_p(r)\in[0,T_g]$。函数 $t(p,r)$ 及
$$
g(p,r)=z_p(t_p(r)),\qquad g(p,0)=0
\tag{28.102}
$$
联合 $C^5$ 至 $r=0$，且对 $\xi=m,k$ 有
$$
\partial_rt_p(r)=\frac1{\partial_tr_p(t_p(r))},\qquad
\partial_\xi t_p(r)=-\frac{\partial_\xi r_p(t_p(r))}{\partial_tr_p(t_p(r))}.
\tag{28.103}
$$

证明。恢复卷定理27.3—27.4给联合 $C^5$ 的真实端口及 $r_t(p,0)=\nu(p)>0$。在 $K$ 的稍大紧邻域取 $\nu_{\min}>0$；联合连续性允许同一 $T_g\le T_{12}$ 使 $r_t\ge\nu_{\min}/2$。可取 $r_*\le\nu_{\min}T_g/4$，介值定理和严格单调性给唯一逆，且正端点离 $T_g$ 留有裕量。

为使用普通开域逆函数定理，在负时间把每个端口延成其零点的五次 Taylor 多项式。恢复卷（27.111）说明各初始系数对参数光滑；正时间的全部所需混合导数连续至零，所以正负两侧在总阶至多五的导数上相合，得到联合 $C^5$ 延拓。它只是一种函数延拓，绝非负时间 PDE 解。对 $(p,t)\mapsto(p,r_p(t))$ 使用逆函数定理，$r_t>0$ 给可逆导数；局部逆由单调性一致拼接，限制回非负 $r$ 得所需函数。对 $r_p(t_p(r))=r$ 求导得到（28.103），再复合真实 $z$ 得 $g$。这同时供应连续的 $\partial_m\partial_r^4g,\partial_k\partial_r^4g$：参数微分逆时间可出现第五时间导数，已由恢复卷供应，没有对外部未知钟求导。

普通逆函数步骤的钉版直接供应者是 Mathlib 的 [InverseFunctionTheorem/ContDiff.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean) 中 `ContDiffAt.toOpenPartialHomeomorph`、`ContDiffAt.localInverse`、`ContDiffAt.to_localInverse`；这些有限维逆接口不承担恢复卷的 PDE 正则性。$\square$

**定理 28.3（精确三阶图像及其逆）。** 令 $g_j=\partial_r^jg(p,0)$。全部实际准备满足
$$
g_1=m,\qquad g_2=F(m):=-\frac{m(m^2+30)}{10},\qquad
g_3=G(m,k):=\frac m{100}(3m^4+95m^2+300-10k).
\tag{28.104}
$$
在 $\beta\ne0,\nu>0$ 上，三阶图射流全局单射到其精确像。给定 $(m,j_2,j_3)$ 属于此非退化像，当且仅当
$$
m\ne0,\qquad j_2=F(m),\qquad
Q=\frac{3m^4+95m^2+300}{10}-\frac{10j_3}{m}>0.
\tag{28.105}
$$
其唯一逆为 $k=Q,\nu=|\alpha|/\sqrt Q,\beta=m|\alpha|/\sqrt Q$；另有参数先验时还须检查逆值落在先验内。前两阶图射流不能在此二维参数族中识别黏性。

证明。在 $z_p(t)=g(p,r_p(t))$ 中求三次实际时间导数，得到
$$
g_1=\frac{z_t(0)}{r_t(0)},\quad
g_2=\frac{z_{tt}(0)-g_1r_{tt}(0)}{r_t(0)^2},\quad
g_3=\frac{z_{ttt}(0)-g_1r_{ttt}(0)-3g_2r_t(0)r_{tt}(0)}{r_t(0)^3}.
\tag{28.106}
$$
代入恢复卷（27.114）给（28.104）；解第三式给 $Q=k$。反之，（28.105）定义正黏性和非零 $\beta$，代回全部三式正好复现供给的射流，证明必要与充分。此为有限射流相容性，不保证任意带有该射流的整条曲线都来自 PDE。$Q\le0$ 不能实现为有限正黏性，不能静默投影至正数；$m=0$ 不在除法公式域内。

固定任何非零 $m$，$(\beta,\nu)=(m\nu,\nu)$ 随正 $\nu$ 改变时 $g_1,g_2$ 相同，$g_3$ 随 $\alpha^2/\nu^2$ 改变。任意含两点的这类局部线段已给前两阶不足；最小阶数的结论只针对准备初点的这些图射流，不比较任意有限传感器协议。逆在 $m\ne0,Q>0$ 上光滑，局部 Lipschitz，离这两条退化边界有正距离的紧射流域上可取统一常数；特别
$$
\frac{\partial Q}{\partial j_3}=-\frac{10}{m},\qquad
\frac{\partial\nu}{\partial j_3}=\frac{5|\alpha|}{mQ^{3/2}}.
\tag{28.107}
$$
故不能跨越 $\beta=0$ 声称统一稳定性。

在固定校准的 Euclidean 端口平面，曲率只是这些导数的另一表达：
$$
\kappa_0=\frac{F(m)}{(1+m^2)^{3/2}},\qquad
\frac{d\kappa}{d\ell}(0)=\frac{G(m,k)}{(1+m^2)^2}
 -\frac{3mF(m)^2}{(1+m^2)^3}.
\tag{28.108}
$$
这里 $\ell$ 是沿增大 $r$ 的弧长；由 $\kappa=g''/(1+g'^2)^{3/2}$ 及 $d/d\ell=(1+g'^2)^{-1/2}d/dr$ 直接求导。初始曲率已由切向 $m$ 决定，曲率变化才携带第三阶信息；这没有增加一个状态或一次测量，也不声称对任意端口重校准不变。$\square$

**引理 28.4（一次统一的混合四阶图余项）。** 在定理28.2的较小紧参数邻域和共同 $[0,r_*]$ 上，定义
$$
R(p,r)=g(p,r)-mr-\tfrac12F(m)r^2-\tfrac16G(m,k)r^3.
\tag{28.109}
$$
对 $a=0,m,k$，记 $D_0$ 为恒等、$D_m=\partial_m,D_k=\partial_k$，并令 $M_a=\sup|D_a\partial_r^4g|<\infty$。则
$$
D_aR(p,r)=\frac16\int_0^r(r-v)^3D_a\partial_r^4g(p,v)\,dv,
\qquad |D_aR(p,r)|\le\frac{M_a}{24}r^4.
\tag{28.110}
$$
因此 $g=mr+F(m)r^2/2+G(p)r^3/6+O_{C^1(p)}(r^4)$，一致地有
$$
\partial_mg(p,r)=r+O(r^2),\qquad
\partial_kg(p,r)=-\frac m{60}r^3+O(r^4).
\tag{28.111}
$$

证明。对 $g$ 使用四阶积分 Taylor 公式，定理28.3给零至三阶系数。定理28.2的联合 $C^5$ 保证对参数在积分下微分合法且混合导数交换，得到同一公式的 $D_m,D_k$ 版本。$\int_0^r(r-v)^3dv=r^4/4$ 给常数 $1/24$；紧性给有限的 $M_a$。最后对系数求导，$G_k=-m/10$，即得（28.111）。后文的有限记录和有限差分共用此余项，不另假定解析性。积分 Taylor 的钉版直接供应者是 Mathlib [Taylor.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Taylor.lean) 的 `taylor_integral_remainder`、`taylor_mean_remainder_bound`；这里的 $1/24$ 来自所展示的积分而非额外经验常数。$\square$

**推论 28.5（履行命题26.4的黏性前提）。** 固定 $\alpha\ne0$ 和 $(\beta_0,\nu_0)$ 的正黏性内点邻域。实际 PDE 满足命题26.4（26.113）的全部统一渐近。因而在 $\beta_0\ne0$ 的内点，一份足够短正内部时间的同时端口对，仍有该命题所述随 $\nu$ 变化的精确局部 $(\beta(\nu),t(\nu))$ 纤维，且（26.114）的两导数均非零。

证明。恢复卷定理27.2—27.4给开参数域上的光滑性及初始恒等式。对这些初值作参数微分：$r_\nu(0)=r_\beta(0)=z_\nu(0)=z_\beta(0)=0$，而 $r_{\nu t}(0)=1,r_{\beta t}(0)=z_{\nu t}(0)=0,z_{\beta t}(0)=1$。在紧邻域上二阶时间导数及其参数导数一致有界，Taylor 积分式遂给
$$
r_\nu=t+O(t^2),\quad z_\nu=O(t^2),\quad
r_t=\nu+O(t),\quad z_t=\beta+O(t),\quad
r_\beta=O(t^2),\quad z_\beta=t+O(t^2).
\tag{28.112}
$$
这正是继承的（26.113）；直接应用命题26.4的条件纤维结论，无需第二次一般隐函数证明。固定充分小 $t>0$ 后，$-t/\nu+O(t^2)$ 和 $\beta/\nu+O(t)$ 在非零 $\beta$ 内点均非零。旧命题的原条件文本仍成立，此处履行其当时尚缺的实际黏性正则性前提。

纤维首先属于单份读数的参数／时间任务载体；要把其中两点称为完整观察者不可区分，仍须使同一完整旧档案、所记时间戳和允许钟关系各有对应的完整实现。已知内部时间或其它旧记录可切开此纤维。本推论不把它变成任何传感器数的普遍最优性断言。$\square$

**命题 28.6（剪切边界与幅度、黏性、时间的共同缩放）。** 非退化识别保留如下精确边界。$\beta=0$ 的整个图恒为 $z=0$，不同正黏性的未知钟碰撞由命题26.4（26.112）给出；$\alpha=0$ 的原始双端口历史恒零，由恢复卷命题25.7（25.120）的不可见剪切给出。这两项直接复用既有精确解及证明。$\nu=0$ 时 $r_t(0)=0$，本节的正则图逆前提失效，并无由本证明得到的无黏性结论。

如果准备幅度绝对尺度未知，则对任意 $c>0$，实际 PDE 有缩放
$$
u^c(t,X)=c\,u(ct,X),\quad \Pi^c(t,X)=c^2\Pi(ct,X),\qquad
(\alpha,\beta,\nu)\mapsto(c\alpha,c\beta,c\nu),
$$
$$
r^c(t)=r(ct),\qquad z^c(t)=z(ct).
\tag{28.113}
$$
此外 $X\mapsto X+(\pi,\pi)$ 将 $\alpha$ 变为 $-\alpha$ 而保持 $\beta$；原始双端口都变号，归一化图保持。故仅无参数化归一化图的三阶非退化射流给 $\beta/\nu$ 和 $|\alpha|/\nu$，不提供三者的绝对尺度或 $\alpha$ 的符号。

证明。缩放后的时间导数、对流、黏性项和压力梯度都是原方程对应项的 $c^2$ 倍，初态正好具有所列幅度；归一化抵消外侧 $c$。平移对初始可见余弦给负号、对 $X_2-X_1$ 模态给正号；方程平移不变及唯一性延伸此关系，两读出模态的相位均为 $-1$，所以所列端口关系对整条实际轨迹成立。

若允许未知共同传感器增益 $a_g$，将它改为 $a_g/c$ 并把候选钟改成原钟的 $1/c$，便与（28.113）一同保留全部这些原始测量值；额外档案约束仍须逐项满足。相反，若初始校准原始读数 $x(0)$ 已实际取得，$\alpha=2x(0)$ 供应有符号尺度，无需再次免费给一项测量。此陈述不含新的含噪 $\alpha$ 联合逆定理。独立未知增益、丢失空间相位、异步端口、缺失初始准备点、改变初态族或扰动演化的测量，均不满足本节合同，须各自解决识别与共同轨迹合法性。$\square$

**推论 28.7（图访问、已获样点时间及既有因子化的任务域）。** 设共同外部钟 $\theta$ 连续严格递增、$\theta(0)=0$，同源且同时的端口读数为 $(r_p(\theta(s)),z_p(\theta(s)))$。若实际访问到零点附近任意小正内部时间，观察到的有向图 germ 就是 $g_p$；此结论无需 $\theta$ 可微或有正导数。三阶射流识别之后，对任一已获且有初始分支证书的样点 $(s_i,r_i,z_i)$，唯一内部时间和准备场分别为
$$
\theta(s_i)=t_p(r_i),\qquad u_p(t_p(r_i)).
\tag{28.114}
$$
只有这些实际已获样点的钟值由此确定，不确定未采样钟插值，更不重建或商掉完整档案。

证明。$r_t>0$ 和 $\theta$ 的连续严格单调性保留图与方向，零点相连的小正访问保留 germ。对已识别参数应用定理28.2的单调逆，得到（28.114）。有初始跳跃的钟不必提供 germ；没有到达指定正阈值的钟也不提供该记录。

精确图射流属于理想访问，不是免费有限记录。即便确实取得 $r=0,h,2h,3h$、且 $g(0)=0$ 精确，第三前向差分 $[g(3h)-3g(2h)+3g(h)]/h^3$ 在三个非初始标量各有误差 $\epsilon$ 时仅噪声项已有 $7\epsilon/h^3$ 界；截断偏差还需四阶导数，位置误差另计。第29节另给两份实际记录的局部结论。

对一个选定的参数邻域，以参数 $p$ 为载体，精确射流接口由定理28.3单射；若要解码已获样点的准备场，则载体取带这些实际 $r_i$ 的 $(p,(r_i)_i)$，接口同时保留射流与 $(r_i)_i$，仍单射。直接应用既有 [InjectiveInterfaceTargetFactorization](../../../D5/S3/ConceptDynamics/RefinementFactorization/InjectiveInterfaceTargetFactorization.lean) 的 `injective_interface_factors_every_target`，或 [RealizedImageKernelFactorization](../../../D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.lean) 的 `realized_image_unique_factorization_iff_reverse_kernel`，可因子化参数与这些指定准备场任务。此单射前提不施于含任意钟和旧记录的完整实现集合；后者可有多个实现共享同一参数任务。任务的稳定性、求值资源和新操作合法性仍须各自的界。

共同钟消去沿用定理21.2与命题23.4—推论23.5的任务区别，初始方向与端点值的区别沿用第27节及 [GoldenThreadBlowup](../../../D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.lean)。成熟的初始输出／Lie 导数方法见 Sontag, *Dynamic compensation, parameter identifiability, and equivariances*, PLOS Computational Biology（2017），[作者原文](https://www.sontaglab.org/FTPDIR/dynamic_compensation_parameter_identifiability_equivariances_sontag_plos2017.pdf)第5—6页；这里仅使用有限阶导数，不假定解析性，也不从所有 Taylor 系数相同反推一般光滑轨迹相同。[FiniteCrystalTimeFrequencyBridge](../../../D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge.lean) 的 `first_crystal_time_window_injective` 与 [FinitePronyNodeIdentification](../../../D5/S3/Analytic/GoldenTomography/FinitePronyNodeIdentification.lean) 的 `recurrence_window_identifies_node_roots` 要求其有限指数模态模型；这里没有这种不变模态前提。[ProjectiveJetScaleInvariance](../../../D5/S3/Analytic/Toroidal/ProjectiveJetScaleInvariance.lean) 处理常值输出尺度，[PairCalibratedSecondMagnusObservability](../../../D5/S3/Observer/AgencyHolonomy/PairCalibratedSecondMagnusObservability.lean) 允许各对不同时间，均不替代此处的共同阈值与全 PDE 桥梁。$\square$

## 29. 两份有限记录的统一逆、取得资源与受限实验下界

**定义 29.1（一个完整实现集合上的两份记录）。** 继续定义25.5、第27节的完整观察者语义，现在令 $\Omega$ 中的每份实现 $\omega$ 同时包含来源身份、固定已校准 $\alpha$、参数 $p(\omega)=(m,k)$、由同一准备生成的实际轨迹 $u_p$、一个允许的连续严格递增钟 $\theta_\omega$，以及解释全部旧记录、误差和关系的辅助量。完整已获信息写为 $H=(C,\mathcal A,D_1,D_2)$：$C$ 保留全部先前内部／外部记录及关系，$\mathcal A$ 保留合法动作、端口、校准、分支和共同轨迹证书，$D_j=(s_j,\widetilde r_j,\widetilde z_j)$ 是两份有序实际同时记录，$s_1<s_2$ 是保留的外部时间戳。对已声明局部先验 $U$ 和第28节初始图域，令 $t_j(\omega)=\theta_\omega(s_j)$、$r_j(\omega)=r_{p(\omega)}(t_j(\omega))$，定义
$$
\begin{aligned}
\mathfrak F_H=\{\omega\in\Omega:\;&p(\omega)\in U,\quad
\operatorname{Hist}(\omega,\mathcal A),\quad
\mathcal R_i(\omega,c_i)\ \text{对全部 }c_i\in C,\\
&\omega\in\mathcal E_H,\quad
0<t_1(\omega)<t_2(\omega)\le T_g,\quad
0<r_1(\omega)<r_2(\omega)\le r_*,\\
&|r_j(\omega)-\widetilde r_j|\le\epsilon_r,\quad
|g_{p(\omega)}(r_j(\omega))-\widetilde z_j|\le\epsilon_z\quad(j=1,2)\},\\
\mathcal K_H&=\{p(\omega):\omega\in\mathfrak F_H\}.
\end{aligned}
\tag{29.101}
$$
$\mathcal E_H$ 是一份联合误差事件，可施加相关性和其它旧限制，不预设独立噪声。旧钟校准、同源关系或额外传感器均仍在 $\mathcal R_i$ 内；不能为两份记录或各条旧约束另选互不相容的实现。若测量由原始 $x,y$ 换算，则在同一联合事件上严格使用
$$
\epsilon_r=\frac{2\epsilon_x}{|\alpha|},\qquad
\epsilon_z=\frac{4\epsilon_y}{|\alpha|}.
\tag{29.102}
$$
这里 $\alpha$ 固定且已校准。精确事件是误差为零且 $r_j=j\eta$ 的特例；两记录和校准初点均仍附于完整档案。模型预测不替代实际取得，重开缓存第一记录不产生第二记录。

**定理 29.2（两精确阈值的局部识别与三次病态量级）。** 固定 $p_0=(m_0,k_0)$，$m_0\ne0,k_0>0$。对充分小 $\eta>0$，两份已实际取得的初始分支精确阈值响应定义
$$
\mathcal O_\eta(p)=(g_p(\eta),g_p(2\eta)).
\tag{29.103}
$$
它在 $p_0$ 附近有 $C^1$ 局部逆，且
$$
\det D\mathcal O_\eta(p_0)=-\frac{m_0}{10}\eta^4+O(\eta^5),
\qquad \|(D\mathcal O_\eta(p_0))^{-1}\|_2=\Theta(\eta^{-3}).
\tag{29.104}
$$

证明。仅用引理28.4的一致混合余项，$\partial_mg(r)=r+O(r^2)$，$\partial_kg(r)=-mr^3/60+O(r^4)$，故
$$
\det D\mathcal O_\eta
 =(\eta+O(\eta^2))\left(-\frac{8m}{60}\eta^3+O(\eta^4)\right)
 -(2\eta+O(\eta^2))\left(-\frac m{60}\eta^3+O(\eta^4)\right)
 =-\frac m{10}\eta^4+O(\eta^5).
\tag{29.105}
$$
非零 $m_0$ 使充分小正 $\eta$ 时行列式非零，有限维逆函数定理给局部逆。若 $|\det D\mathcal O_\eta+m_0\eta^4/10|\le C_D\eta^5$，$C_D>0$ 时附加 $\eta\le|m_0|/(20C_D)$ 就足以保留非零性；还须满足共同图域限制。第一参数列为 $(\eta,2\eta)+O(\eta^2)$，故大奇异值有上下界常数乘 $\eta$；奇异值乘积为行列式绝对值，给小奇异值为常数乘 $\eta^3$，从而得到逆导数的精确量级。

此为局部两记录逆；定理28.3在其精确三阶射流像上的全局逆并不把这里升级为任意参数盒上的全局两样点逆。精确阈值仍须实际取得，同一完整见证仍须满足定义29.1。把导数识别转成有限样点的 Taylor／Vandermonde、余项与最小奇异值方法，见 Sontag, *A concept of local observability*, Systems & Control Letters 5（1984），41–47，[作者原文](https://www.sontaglab.org/FTPDIR/localobs.pdf)，Lemma 3.4（第44页）及 Section 4 的证明（第45—46页），Lemma 3.5 使用逆函数定理。该文对象是有限维受控系统；这里的全 PDE 参数正则性、阈值图及特定系数分别由恢复卷第27节和本卷第28节承担，不由该有限维结果直接推出。$\square$

**定理 29.3（显式预条件与一个固定凸参数邻域）。** 令 $F,G$ 如（28.104），已知位置比的设计域为
$$
\mathcal D=[3/4,5/4]\times[7/4,9/4],\qquad (\lambda,\mu)\in\mathcal D.
\tag{29.106}
$$
对 $3\eta\le r_*$ 定义
$$
A_{\eta,\lambda}(p)=\frac{g_p(\lambda\eta)}{\lambda\eta},
$$
$$
B_{\eta,\lambda,\mu}(p)=\frac1\eta\left[
 \frac{2\{g_p(\mu\eta)-(\mu/\lambda)g_p(\lambda\eta)\}}
 {\mu(\mu-\lambda)\eta^2}-F(A_{\eta,\lambda}(p))\right],\qquad
\mathcal P_{\eta,\lambda,\mu}=(A_{\eta,\lambda},B_{\eta,\lambda,\mu}).
\tag{29.107}
$$
存在一个固定闭凸球 $U=\overline B(p_0,\rho)$、共同 $\eta_0>0,K<\infty$，使对所有 $p,q\in U,(\lambda,\mu)\in\mathcal D,0<\eta\le\eta_0$，
$$
\|\mathcal P_{\eta,\lambda,\mu}(p)-\mathcal P_{\eta,\lambda,\mu}(q)\|_2
 \ge\frac{\|p-q\|_2}{2K}.
\tag{29.108}
$$
球 $U$ 在参数空间，不是与 $\eta$ 无关的原始输出球。

证明。固定正 $\eta,\lambda,\mu$ 时，（29.107）是两个输出 $z_1,z_2$ 的可逆变换：$z_1=\lambda\eta A$，
$z_2=(\mu/\lambda)z_1+\mu(\mu-\lambda)\eta^2[F(A)+\eta B]/2$。它只重表达两条既有记录，不增加测量。

引理28.4给一致于 $\mathcal D$ 的 $C^1(p)$ 展开
$$
A=m+\frac\lambda2F(m)\eta+O_{C^1}(\eta^2),\qquad
\mathcal P_{\eta,\lambda,\mu}\longrightarrow
\mathcal P_{0,\lambda,\mu}=(m,J_{\lambda,\mu}(m,k)),
$$
$$
J_{\lambda,\mu}=\frac{\lambda+\mu}{3}G(m,k)-\frac\lambda2F'(m)F(m),
\qquad \partial_kJ_{\lambda,\mu}=-\frac{(\lambda+\mu)m}{30}.
\tag{29.109}
$$
收敛的 $C^1$ 误差为 $O(\eta)$。确实，$B$ 方括号中首项展开成
$F(m)+(\lambda+\mu)G\eta/3+O_{C^1}(\eta^2)$，而
$F(A)=F(m)+\lambda F'(m)F(m)\eta/2+O_{C^1}(\eta^2)$；相减除以 $\eta$ 即得。多项式 $F$ 及一致 $C^1$ 余项保证参数导数亦有相同阶数。

令
$$
L_{\lambda,\mu}=D\mathcal P_{0,\lambda,\mu}(p_0),\qquad
K=\max_{(\lambda,\mu)\in\mathcal D}\|L_{\lambda,\mu}^{-1}\|_2.
\tag{29.110}
$$
$L$ 第一行为 $(1,0)$，行列式为 $-(\lambda+\mu)m_0/30\ne0$；连续性和紧性给 $0<K<\infty$。在共同开图参数域内选择
$0<\rho<\min\{|m_0|/2,k_0/2\}$，使闭球 $U$ 连同邻域留在该域，且
$$
K\sup_{p\in U,(\lambda,\mu)\in\mathcal D}
 \|D\mathcal P_{0,\lambda,\mu}(p)-L_{\lambda,\mu}\|_2\le\tfrac14.
\tag{29.111}
$$
这由紧设计域上的一致连续性实现。再用一致 $C^1$ 收敛选择 $0<\eta_0\le\min\{1,r_*/3\}$，使
$$
K\sup_{p\in U,(\lambda,\mu)\in\mathcal D}
 \|D\mathcal P_{\eta,\lambda,\mu}(p)-D\mathcal P_{0,\lambda,\mu}(p)\|_2
 \le\tfrac14\quad(0<\eta\le\eta_0).
\tag{29.112}
$$
若一致 $C^1$ 余项界为 $C_R\eta$，$C_R>0$ 时还可用 $\eta_0\le1/(4KC_R)$。这些给定的是导数界的充分条件和有限常数的存在，不给未经计算的数值 PDE 半径。

两项四分之一界合成 $\sup_U\|L^{-1}D\mathcal P_\eta-I\|_2\le1/2$。对 $p,q\in U$，整条直线段在 $U$ 中，故
$$
L^{-1}(\mathcal P_\eta(p)-\mathcal P_\eta(q))
 =(p-q)+\int_0^1(L^{-1}D\mathcal P_\eta(q+s(p-q))-I)(p-q)\,ds.
\tag{29.113}
$$
右侧范数至少 $\|p-q\|_2/2$，左侧至多 $K\|\mathcal P_\eta(p)-\mathcal P_\eta(q)\|_2$，得（29.108）。这一步把点态导数条件提升为统一非线性比较；固定 $U$ 不随 $\eta$ 缩小，其实际预条件输出像上的逆 Lipschitz 常数至多 $2K$。原始输出的误差仍被（29.107）的 $\eta$ 分母放大。$\square$

**定理 29.4（已获含噪记录的完整可行集直径）。** 使用定理29.3的同一个 $U,\eta_0$，取 $0<\eta\le\eta_0$。实际测得位置满足
$$
\widetilde r_1\in[3\eta/4,5\eta/4],\qquad
\widetilde r_2\in[7\eta/4,9\eta/4],\qquad
0\le\epsilon_r\le\eta/8.
\tag{29.114}
$$
取实际记录的固定设计比 $\lambda=\widetilde r_1/\eta,\mu=\widetilde r_2/\eta$。令
$$
L_g=\sup_{p\in U,0\le r\le r_*}|\partial_rg_p(r)|,\quad
e=\epsilon_z+L_g\epsilon_r,\quad
C_F=\sup_{|v|\le L_g}|F'(v)|=3+\tfrac3{10}L_g^2,
$$
$$
C_T=\sqrt{(4/3)^2+(64/7+4C_F/3)^2}.
\tag{29.115}
$$
对完整可行集 $\mathcal K_H$ 中任意两候选 $p,q$，都有
$$
\|p-q\|_2\le4Ke\left[
\frac1{\lambda^2\eta^2}
 +\left\{\frac{2(1+\mu/\lambda)}{\mu(\mu-\lambda)\eta^3}
             +\frac{C_F}{\lambda\eta^2}\right\}^2\right]^{1/2},
\tag{29.116}
$$
$$
\|p-q\|_2\le\min\left\{2\rho,\frac{4KC_Te}{\eta^3}\right\}.
\tag{29.117}
$$
若一个真实完整实现同时满足全部旧约束、取得历史和两条新原始误差约束，则 $\mathfrak F_H\ne\varnothing$；此时对任意有完整见证的拟合 $q$ 与真实参数 $p_*$，同一界给 $\|q-p_*\|_2$。

证明。任何候选的真实 $r$ 值落在互不相交的正区间 $[5\eta/8,11\eta/8]$ 和 $[13\eta/8,19\eta/8]$，均含于 $[0,r_*]$，因为 $3\eta\le r_*$。窗口本身不证明同源或第一分支，这两项由定义29.1的见证承担。沿图坐标用中值定理，得到
$$
|g_p(\widetilde r_j)-\widetilde z_j|\le e\quad(j=1,2).
\tag{29.118}
$$
故任意两候选在这两个固定测得位置的精确预测值各相差至多 $2e$。$g_p(0)=0$ 还给 $|A_{\eta,\lambda}(p)|\le L_g$。将（29.107）用于两组精确预测，用 $F$ 的中值界得到
$$
|\Delta A|\le\frac{2e}{\lambda\eta},\qquad
|\Delta B|\le2e\left[
\frac{2(1+\mu/\lambda)}{\mu(\mu-\lambda)\eta^3}
 +\frac{C_F}{\lambda\eta^2}\right].
\tag{29.119}
$$
与（29.108）合用即得（29.116）。设计域给 $\lambda\ge3/4,\mu\ge7/4,\mu-\lambda\ge1/2,\mu/\lambda\le3$；再用 $\eta\le1$ 得 $C_T/\eta^3$ 的上界。$p,q\in\overline B(p_0,\rho)$ 给直径上限 $2\rho$。这些是整个完整可行集的成对界，无需噪声记录本身位于精确模型像内。

一个真实完整见证才保证非空；只对新对成立的原始误差假设至多保证对记录外包集合非空，不保证与旧档案交集非空。若 $\mathfrak F_H$ 为空，本定理不产生拟合参数，不能用静默投影替代；空集上的全称界也不授权后续操作。较强旧约束只缩小可行集，仍保留上界。已知的测得位置偏移属于这份设计，只有未确定的真实 $r$ 偏差由 $\epsilon_r$ 计入噪声。

因此请求参数坐标误差 $\delta>0$ 时，一个明确充分精度条件为
$$
\epsilon_z+L_g\epsilon_r\le\frac{\delta\eta^3}{4KC_T},\qquad
\epsilon_r\le\eta/8,
\tag{29.120}
$$
同时保留局部先验、同源第一分支和非空完整见证。为转换物理参数，令 $k_{\min}=\min_Uk>0,M_m=\max_U|m|$，
$$
N=\frac{|\alpha|}{\sqrt{k_{\min}}},\qquad
C_\nu=\frac{|\alpha|}{2k_{\min}^{3/2}}.
$$
$$
|\nu(p)-\nu(q)|\le C_\nu|k_p-k_q|,\qquad
|\beta(p)-\beta(q)|\le N|m_p-m_q|+M_mC_\nu|k_p-k_q|.
\tag{29.121}
$$
第一式由 $k^{-1/2}$ 的中值定理，第二式由 $m_p\nu_p-m_q\nu_q=\nu_p(m_p-m_q)+m_q(\nu_p-\nu_q)$。代入（29.117）给黏性及隐藏幅度的实际误差界。$g_q(\widetilde r_j)$ 是核对候选的预测，不是另一条取得记录；新增记录仍取同一个完整实现集合的交集。

精确两记录在 $U$ 上单射后，对参数载体或带已获 $r_i$ 的准备场载体，直接应用推论28.7所引现成因子化结果。它不声称对整个 $\Omega$ 单射，不消除已保留钟信息，也不赋予含噪档案一个精确一般解码器。$\square$

**定理 29.5（内部阈值成本与条件外部期限）。** 在固定实际校准 $\alpha$ 的局部先验上，选界
$$
0<a\le|\alpha|\le A,\qquad 0<b\le|\beta|\le B,\qquad
0<\nu_{\min}\le\nu\le\nu_{\max}.
\tag{29.122}
$$
取恢复卷第25节的同一 $H^2$ 常数在此参数域上的上包络
$$
R=2\sqrt{2A^2+9B^2},\quad \tau_*=\frac{\nu_{\min}}{16384R^2},\quad
M_*=(\nu_{\max}+R)(\nu_{\max}R+4R^2),\quad D_*=\frac{2M_*}{a},
$$
$$
T_*=\min\left\{\tau_*,\frac{\nu_{\min}}{2D_*}\right\},\qquad
T_c=\min\{T_{12},T_g,T_*\},\qquad
0<\eta\le\min\left\{\eta_0,\frac{\nu_{\min}T_c}{4}\right\}.
\tag{29.123}
$$
其中 $T_{12}$ 来自恢复卷的开参数族，$T_g,r_*$ 来自定理28.2，$\eta_0\le r_*/3$ 来自定理29.3，均在同一稍大参数邻域上选择。则两个精确初始阈值有唯一内部时刻 $0<t_1<t_2\le T_c$，且
$$
\frac{2j\eta}{3\nu}\le t_j\le\frac{2j\eta}{\nu},\qquad
\frac{2j\eta}{3\nu_{\max}}\le t_j\le\frac{2j\eta}{\nu_{\min}}\quad(j=1,2),
$$
$$
\frac{2\eta}{3\nu}\le t_2-t_1\le\frac{2\eta}{\nu},\qquad
 t_2\le\frac{4\eta}{\nu_{\min}}.
\tag{29.124}
$$
若允许钟另满足下增量率 $c>0$，即
$$
\theta(s')-\theta(s)\ge c(s'-s)\quad(0\le s<s'\le S),
\tag{29.125}
$$
且钟和实际同时事件取得接口可用至 $S_*=4\eta/(c\nu_{\min})$，则两个精确阈值事件均在该外部期限内可达；其外部时刻满足
$$
s_j\le\frac{2j\eta}{c\nu}\le\frac{2j\eta}{c\nu_{\min}},\qquad
s_2-s_1\le\frac{2\eta}{c\nu}\le\frac{2\eta}{c\nu_{\min}}.
\tag{29.126}
$$

证明。恢复卷定理25.3、25.6给 $[0,\tau_*]$ 上同一 $H^2$ 解及 $|x_{tt}|\le M_*$；与恢复卷定理27.2的解由唯一性一致。故 $|r_{tt}|\le D_*$，从 $r_t(0)=\nu$ 积分，在 $[0,T_*]$ 得
$$
|r_t(t)-\nu|\le D_*t\le\nu_{\min}/2\le\nu/2,\qquad
\nu/2\le r_t(t)\le3\nu/2,\quad
\nu t/2\le r(t)\le3\nu t/2.
\tag{29.127}
$$
$\beta$ 的正下界只用于非退化识别，此取得计算也适用于 $\beta=0$。$r(T_c)\ge\nu_{\min}T_c/2\ge2\eta$，连续严格单调性给两个唯一内部 hit；将（29.127）分别在零点至 hit 及两 hit 之间积分，得到（29.124）。$T_c$ 与 $\eta_0$ 的交集使 $H^{12}$ 正则、图逆、非线性参数逆和 $H^2$ 取得界在同一实验同时有效。

对任意定义在 $[0,S]$ 的连续严格递增钟，两个事件在 $S$ 前出现当且仅当 $\theta(S)\ge t_2$，出现时 $s_j=\theta^{-1}(t_j)$。一个统一充分端点条件为 $\theta(S)\ge4\eta/\nu_{\min}$。（29.125）给 $\theta(S_*)\ge cS_*$；在相应 hit 时刻使用原点与两点增量不等式，得到（29.126）。绝对连续且几乎处处 $\theta'\ge c$ 是（29.125）的充分条件。仅 $\theta(s)\ge cs$ 已足够给总期限，但不能替代两点增量条件来给事件间隔界；允许任意快钟，所以没有统一正的外部下时间界。取得在第二 hit 停止，不使用超过 $T_c$ 的 PDE 演化。

在 $[0,\infty)$ 上若 $L=\lim_{s\to\infty}\theta(s)<\infty$，严格增加使有限时刻不达 $L$，故有限时刻到达第 $j$ 事件恰需 $t_j<L$；$L=\infty$ 时两个内部 hit 均最终可达。仅连续严格增加不足以保证最终取得：取 $L=\eta/(3\nu_{\max})$、$\theta(s)=L(1-e^{-s})$，则始终 $\theta(s)<L<t_1$。即使只许无界钟仍无统一期限：给任何 $D>0$，$\theta(s)=\eta s/(3\nu_{\max}D)$ 无界严格递增，却有 $\theta(D)=\eta/(3\nu_{\max})<t_1$。这些反例在同一个固定准备轨迹上就成立。

以上期限专属于两个精确阈值事件及真实可用的同时事件接口。任意有限个点查询不自动构成精确连续事件检测；检测器精度、带宽、延迟以及测量无扰动／等价轨迹须有各自假设。数值相同的迟时 $r$ 读数也不证明初始分支。定理29.4允许已经取得的偏离阈值记录，真实第二位置可达 $19\eta/8>2\eta$；本定理不把 $S_*$ 自动赋给这种记录或检测延迟。应用相同期限必须另给它们实际取得的证书，或另证更大目标及延迟的时域界，而不凭空指定取得算法。$\square$

**定理 29.6（相容竖直参数段上的三次有限差分）。** 固定 $m_0\ne0$，取 $d_0>0$ 使
$$
I=\{(m_0,k):k_0-d_0\le k\le k_0+d_0\}\subset U,\qquad k_0-d_0>0.
\tag{29.128}
$$
这里 $\nu(k)=|\alpha|/\sqrt k,\beta(k)=m_0\nu(k)$。令
$$
M_4=\sup_{(m_0,k)\in I,0\le r\le r_*}|\partial_k\partial_r^4g(m_0,k,r)|<\infty.
\tag{29.129}
$$
取 $\eta$ 满足（29.123），且 $2\eta\le r_*$；$M_4>0$ 时再要求 $\eta\le|m_0|/(10M_4)$，$M_4=0$ 时不加此限制。则对任意段内 $k,k'$，
$$
Q_\eta(k)=(g_{m_0,k}(\eta),g_{m_0,k}(2\eta)),\qquad
\frac{|m_0|}{15}\eta^3|k-k'|
 \le\|Q_\eta(k)-Q_\eta(k')\|_\infty
 \le\frac{|m_0|}{5}\eta^3|k-k'|.
\tag{29.130}
$$

证明。使用引理28.4的同一个参数微分积分余项，$F_k=0,G_k=-m_0/10$ 给
$$
\left|\partial_kg(m_0,k,r)+\frac{m_0}{60}r^3\right|
 \le\frac{M_4}{24}r^4.
\tag{29.131}
$$
对 $0<r\le2\eta$，附加小性使误差至多 $|m_0|r^3/120$，所以导数恒具有 $-\operatorname{sign}(m_0)$ 的符号，且
$$
\frac{|m_0|}{120}r^3\le|\partial_kg(m_0,k,r)|\le\frac{|m_0|}{40}r^3.
\tag{29.132}
$$
沿完整 $k$ 线段积分，固定符号排除抵消；第二输出在 $r=2\eta$ 给下界 $8/120=1/15$，两输出的最大上界为 $8/40=1/5$，得到真正有限差分（29.130）。几何包含 $I\subset U$ 本身不证明档案相容；下项对实际完整实现另加明确条件。$\square$

**定理 29.7（保留时间戳及全部已获 $r$ 迹的受限两点下界）。** 使用定理29.6的参数段和阈值。实验允许两个精确 $r$ 阈值 $\eta,2\eta$、它们的同时 $z$ 读数各有绝对误差至多 $\epsilon$，并保留所有校准、初点、准备族、局部先验、开始事件、取得历史和时间戳。可额外把 $m=m_0$ 精确告诉观察者。基础钟类取全部零点为零的连续严格递增钟；任何更强钟限制仍作为旧约束保留，并须通过下述完整端点条件。先声明两个 $z$ 坐标允许完整的 sup 范数误差球 $\{e:\|e\|_\infty\le\epsilon\}$；若实际联合噪声集更小，则以下两条构造误差向量必须分别被该集合允许。给 $\epsilon>0$，令
$$
d=\min\left\{d_0,\frac{5\epsilon}{|m_0|\eta^3}\right\},\qquad
k_-=k_0-d,\quad k_+=k_0+d,\qquad
\widetilde Z=\tfrac12(Q_\eta(k_+)+Q_\eta(k_-)).
\tag{29.133}
$$
对于所考察的固定完整旧档案，假设存在两个完整端点见证：参数为 $k_-,k_+$ 的实际 PDE、下面的各自单一钟、所构造噪声及所有辅助量，分别满足每条旧约束与合法取得关系，并给同一完整观察结果。则该受限实验的每个估计器，在这两份允许实现之一的绝对 $k$ 误差至少为 $d$；同样的界适用于 $(m,k)$ Euclidean 误差。以 $k_{\max}=k_0+d_0$ 计，物理坐标的最坏误差至少分别为
$$
\frac{|\alpha|}{2k_{\max}^{3/2}}d\quad\text{（黏性）},\qquad
\frac{|m_0\alpha|}{2k_{\max}^{3/2}}d\quad\text{（隐藏幅度）}.
\tag{29.134}
$$

证明。（29.130）给 $\|Q_\eta(k_+)-Q_\eta(k_-)\|_\infty\le2\epsilon$，故两个端点的误差向量 $e_\pm=\widetilde Z-Q_\eta(k_\pm)$ 都有 sup 范数至多 $\epsilon$。完整误差球允许这两个向量；若只给相关联合噪声限制，必须检查 $e_\pm$ 连同其它误差的实际联合归属，不能仅从逐坐标界推断允许。每个端点均是一条不同参数的真实光滑 PDE 轨迹，每份实现内部的两记录来自同一轨迹。

为保持外部时间戳，固定任意 $S>0$，对段内各参数取定理28.2的真实逆时间并令
$$
\theta_k(s)=t_k(\eta s/S)\quad(0\le s\le2S),\qquad
r_k(\theta_k(s))=\eta s/S.
\tag{29.135}
$$
这是连续严格递增、零点为零的钟，其内部像留在（29.123）的取得区间内。两次事件在全部候选中都有相同外部时间戳 $S,2S$；若取得时实际保留了整条 $r$ 监测迹，第二式也使这整条迹一致。需要时可在 $2S$ 后连续严格增加地延长钟，但延长部分的 PDE 读出和旧约束仍须有自身合法域。该钟是构造允许世界的见证，不是要求观察者预知隐藏参数的算法；每个世界用一个钟贯穿两事件，两个世界可以有不同允许钟。

基本档案只含上述共同校准、初始端口值、准备族／局部先验、开始事件及这些取得记录，并且准备标签没有泄露 $\beta,\nu$ 时，这两份完整见证确实相容：$x(0)=\alpha/2,y(0)=0$ 相同，阈值、时戳与 $r$ 迹由构造相同，$z$ 读数由中点噪声相同，准备和分支由实际解保证。对更丰富的档案，定理假设要求这些同一完整见证同时满足全部旧关系；旧钟校准、其它传感器、早先 $z$ 记录或准备元数据若排除任一端点，下界就不能用于该档案，不能删除这些信息来保留下界。尤其定理29.5用于充分取得的下增量率／期限限制不自动被（29.135）满足；若实验强制这些额外钟条件，须另外核对这两个钟在该固定合同下的可接受性。

估计器在同一完整观察结果上输出 $a$，三角不等式给
$$
2d=|k_+-k_-|\le|a-k_+|+|a-k_-|.
\tag{29.136}
$$
至少一项不小于 $d$。在以上限定的有界对抗噪声实验中因此有
$$
\text{minimax 绝对 }k\text{ 误差}\ \ge
\min\left\{d_0,\frac{5\epsilon}{|m_0|\eta^3}\right\}.
\tag{29.137}
$$
随机估计器在相同数据上有相同输出律，对三角不等式取期望也给最坏期望绝对误差的相同下界。这里无噪声独立性或随机分布前提。$\epsilon=0$ 时取 $d=0$，下界为零。

沿该段 $|\nu'(k)|=|\alpha|/(2k^{3/2})\ge|\alpha|/(2k_{\max}^{3/2})$ 且符号固定，端点差至少 $|\alpha|d/k_{\max}^{3/2}$。对物理参数的输出再次用两点三角不等式，取端点差的一半，即得（29.134）；$\beta=m_0\nu$ 给幅度常数。因此若所要求的最坏 $k$ 误差 $\delta<d_0$，在上述端点相容的噪声级别必须满足
$$
\epsilon\le\frac{|m_0|\delta}{5}\eta^3.
\tag{29.138}
$$

量词上，对给定 $(\eta,\epsilon)$，只要求（29.133）的两个端点连同钟、误差与旧记录的完整见证成立；要对每个噪声级别统一宣称（29.137），就须对全部相应 $d$ 验证这一条件，例如有一整段同时符合固定旧档案的完整见证族，并对每级中点误差保有联合允许性。仅 $I\subset U$ 或各条记录分别可拟合都不足。已知精确原始 $r$ 是允许的子实验，所以该下界与（29.117）在 $\epsilon_r=0$ 时的 $\eta^{-3}$ 量级相配，均在先验半径处饱和。

两个内部事件的间隔由（29.124）上下夹在常数乘 $\eta$ 之间，而剩余 $k$ 参数的输出分离仅为三次阶。这不是外部等待时间下界，因为（29.135）保留相同外部时刻。此匹配结论只针对声明的局部两端口、初始阈值、允许钟和联合噪声实验，不覆盖其它传感器、额外已获信息、任意后期时间、不同准备或更强先验，也不给普遍最优传感器数。方法是标准误差球重叠的两点估计论证；这里的具体桥梁是实际 PDE 系数给出的有限差分、保留时戳与 $r$ 迹的显式钟，以及完整档案的同时可实现条件。$\square$

## 29.99 追加锚

## 30. 异步双端口的完整实验、相对登记与识别恢复

**定义 30.1（固定的双记录器合同与完整世界）。** 固定定义28.1的已校准有符号 $\alpha\ne0$、实际无外力 PDE、准备族及端口，仍用 $p=(m,k)$、$\nu=|\alpha|/\sqrt k$、$\beta=m\nu$。本节另立异步取得合同，不把定义29.1中的一只共同钟暗换成两只钟。先固定实验 $\mathcal X$：两个本地标签域 $I_r,I_z$、实际允许的取得动作与费用、钟类、先验、旧档案解释规则及一份联合误差模型。完整世界 $\omega\in\Omega_{\mathcal X}$ 含实际来源、参数、由该准备生成的同一轨迹 $u_p$、两只允许钟 $\theta_r:I_r\to[0,T]$、$\theta_z:I_z\to[0,T]$，以及实现记录、误差、延迟和旧关系所需的辅助量。初始窗口取两标签域均含零，钟连续严格递增且 $\theta_r(0)=\theta_z(0)=0$；后文改变窗口时明列端点。钟值本身是潜变量，除非已实际取得。

完整观察者为
$$
H_{\rm async}=(C,\mathcal A,D_r,D_z,J),\qquad
D_r=(s,\widetilde R(s))_{s\in L_r},\quad
D_z=(v,\widetilde Z(v))_{v\in L_z},
\tag{30.101}
$$
其中 $L_i\subseteq I_i$ 是实际保留的有限、稠密或完整标签集，不能随候选改变。$C$ 保留全部先前取得的来源索引、内部／外部记录及关系；$\mathcal A$ 保留动作、端口、标签、费用、初点、校准、分支和无扰动／等价轨迹证书；$J$ 保留每一项实际取得的跨端口关系，包括同时性、顺序、检索、到达和动作记录。$\operatorname{Hist}_{\rm async}(\omega,\mathcal A)$ 断言这一份世界确实实现全部合法动作和记录，不要求不同端口的同名标签表示同一内部事件。两只仪器在同一物理事件无扰动读取同一状态时，它们读的内部时间当然相同；本合同描述分别标时、跨端口登记未必已知的取得。

以 $\mathcal C_{\mathcal X}$ 表示允许钟对、$\mathcal E_H$ 表示包括所有误差相关限制的一份联合事件，$\mathcal R_i,\mathcal J_\ell$ 分别解释旧记录和已获跨端口关系。给定共同初始分支及参数域 $P$，唯一的完整可行集是
$$
\begin{aligned}
\mathfrak F_H^{\rm async}=\{\omega\in\Omega_{\mathcal X}:\;&p(\omega)\in P,\quad
 (\theta_r,\theta_z)\in\mathcal C_{\mathcal X},\quad
 \operatorname{Hist}_{\rm async}(\omega,\mathcal A),\\
&\mathcal R_i(\omega,c_i)\quad(\text{全部 }c_i\in C),\quad
 \mathcal J_\ell(\omega,j_\ell)\quad(\text{全部 }j_\ell\in J),\\
&\omega\in\mathcal E_H,\quad
 \theta_r(L_r),\theta_z(L_z)\ \text{均在所证同源初始分支内},\\
&\widetilde R(s)=r_p(\theta_r(s))+e_r(s)\quad(s\in L_r),\\
&\widetilde Z(v)=z_p(\theta_z(v))+e_z(v)\quad(v\in L_z)\},\qquad
\mathcal K_H^{\rm async}=p(\mathfrak F_H^{\rm async}).
\end{aligned}
\tag{30.102}
$$
误差界是 $\mathcal E_H$ 的条件，不将各坐标盒自动宣布为真实联合模型。先固定 $\mathcal X,C,\mathcal A,J$、标签及误差规则，再选择竞争世界；两条绘图曲线相同不够证明完整观察相同。原始 $x,y$ 的噪声仍按（29.102）使用已知 $\alpha$ 换算，未知增益、相位或有噪校准属于不同合同。

若已认证 $\theta_r=\theta_z$，且选出的两份记录实际同时、同源、合法，满足定义29.1的分支、顺序、先验和联合误差全部前提，则在保留其它记录的条件下返回第29节合同。仅有同一开始事件、同名标签或两条钟各自严格增加不够。若 $C$ 已含定理29.3所需的精确识别对，则相应参数已被切开，下文不同参数碰撞不能满足该 $C$；有一条可用定理并不表示观察者已取得其所需实验。

**引理 30.2（实际共同单调分支与逆域）。** 固定 $m_0\ne0,k_0>0$，取其开邻域内的紧参数邻域 $P$，使 $m$ 的符号恒为 $\sigma=\operatorname{sign}(m_0)$、$|m|$ 有正下界且 $k>0$。可以在同一个实际初始时间段 $[0,T]$ 上，使全部 $p\in P$ 的 $r_p$ 和 $w_p=\sigma z_p$ 从零严格增加，并有共同正逆域 $[0,r_*]$、$[0,w_*]$，其逆像在 $[0,T]$ 内留有端点裕量。图 $g_p=z_p\circ r_p^{-1}$ 在此共同图域上满足
$$
g_p(r)=mr+\frac{F(m)}2r^2+\frac{G(m,k)}6r^3+O_{C^1(p)}(r^4),
\quad F(m)=-\frac{m(m^2+30)}{10},\quad
G(m,k)=\frac{m(3m^4+95m^2+300-10k)}{100}.
\tag{30.103}
$$
余项、参数导数和所有后续常数均在同一稍大紧邻域与共同分支上选取。

证明。[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定理27.2—27.4给实际端口的联合 $C^5$、$r_p(0)=z_p(0)=0$、$r_{p,t}(0)=\nu(p)>0$ 和 $w_{p,t}(0)=|\beta(p)|>0$。紧性给 $\nu_{\min},b_{\min}>0$，联合连续性允许同一个 $T>0$ 使 $r_t\ge\nu_{\min}/2$、$w_t\ge b_{\min}/2$。故可取 $r_*\le\nu_{\min}T/4,w_*\le b_{\min}T/4$，介值性给存在，严格增加给唯一，端点在 $T$ 之前。逆的联合正则性直接沿定理28.2的非零导数逆函数论证，对 $w$ 同样适用；零点处只用其函数延拓，不制造负时间 PDE。式（30.103）及其混合余项正是定理28.3、引理28.4，没有新的 PDE 或形式幂级数假设。$\square$

**定理 30.3（固定初始窗口的完整局部流碰撞）。** 在引理30.2下，固定 $S_r,S_z>0$ 及连续严格递增的满射
$$
R:[0,S_r]\to[0,r_a],\qquad W:[0,S_z]\to[0,w_a],
\quad 0<r_a<r_*,\quad0<w_a<w_*.
\tag{30.104}
$$
对每个 $p\in P$，两只实际逆钟
$$
\theta_{r,p}=r_p^{-1}\circ R,\qquad
\theta_{z,p}=w_p^{-1}\circ W
\tag{30.105}
$$
在整个固定标签域给出相同精确流 $R(s),\sigma W(v)$。存在下面明确的固定双记录器实验，使这些不同参数世界给同一个完整 $H_{\rm async}$；在该实验内，即使全部初始窗口逐点精确保留，也不能局部识别 $\nu$ 或 $\beta$。对更丰富的实际档案，这一结论以同一批完整世界同时满足（30.102）的每一项为条件。

证明。两逆钟连续严格递增、共同零点为零，像在实际初始分支内。直接代入得
$$
r_p(\theta_{r,p}(s))=R(s),\qquad
z_p(\theta_{z,p}(v))=\sigma W(v)
\quad(0\le s\le S_r,\ 0\le v\le S_z).
\tag{30.106}
$$
固定的基本实验如下：同一来源身份在共同准备事件启动两台无扰动记录器，各在预先声明的本地标签区间保留该端口全流；读取不改变 PDE，两个本地钟允许（30.105）这类任意连续严格增钟。准备档案记模型、先验、已校准 $\alpha$ 和初始值 $x(0)=\alpha/2,y(0)=0$，其标签不泄露 $\beta,\nu$。每台在自己的末标签停录。费用按该固定记录合同计，所有候选相同；不把无限精确流说成有限次数、有限存储或有限费用的取得。$J$ 在准备后没有跨端口比较，历史只保留共同开始、各自取得顺序和本地停止。参数、实际轨迹及逆钟按上式取，噪声为零，已有初点和所有本地标签／读值均相同，所以这确实是一个先固定实验中的完整见证族。$P$ 内改变 $k$ 会改变 $\nu$，改变 $m$ 会改变 $\beta$，故两者皆无局部唯一性。

若合同另外包含事后检索或包到达记录，也须保留。例如基本实验可允许未知无上界存储／传送延迟，在所有录制结束后才以同一顺序检索两个缓冲区；在紧族上选晚于全部端点的共同释放时刻即可在每个世界实现相同的这种记录。若精确检索时间、到达时间、已知延迟界、物理费用或动作顺序已实际取得，其对应约束必须由这些同一世界满足，不能删掉再援用例子。未知延迟下的包到达顺序不等于取得顺序；反之，真实取得顺序若已记录，也不能假装它只是包顺序。式（30.105）是不同允许世界的潜在钟，不是一种预先知道隐藏参数才会运行的取得算法。

在定向初始分支，$z$ 的增加／减少方向给 $\beta$ 的符号；$\beta=0$ 的恒零 $z$ 及剪切钟碰撞直接用命题26.4（26.112），非零 $\beta$ 在该分支上不恒零。这里仅断言这两类区别仍可见，不分类全时间的全部不变量。当前结论只涉及共同初始窗口：可在各端标签后以正斜率连续延长钟至无界，但这不等化任何未观测的后续 PDE 读出，也不延长已证 PDE 域。

若另一个合同允许有界钟及全部非负标签，则取 $R(s)=r_a(1-e^{-s}),W(v)=w_a(1-e^{-v})$，并令 $r_a,w_a$ 严格位于共同逆域内部。式（30.105）对所有非负标签成立，内部时间分别趋于有限的逆端点。于是无限标签并不等于无界内部观察时间；正统一下率或无界钟合同排除这个构造。独立无界钟下的全时间历史识别仍是另一个问题。$\square$

**命题 30.4（正宽度双边速率带仍容许碰撞）。** 固定 $0<c_-<c_+$ 和内点 $c\in(c_-,c_+)$。取足够小 $S>0$，固定真实基准 $p_0$ 的流
$$
R(s)=r_{p_0}(cs),\qquad Z(s)=z_{p_0}(cs),\qquad0\le s\le S.
\tag{30.107}
$$
限制到 $p_0$ 的一个较小参数邻域后，实际逆钟 $\theta_{r,p}=r_p^{-1}\circ R$、$\theta_{z,p}=z_p^{-1}\circ Z$ 均满足整个区间上的 $c_-<\theta'_{i,p}<c_+$，并保留相同完整局部流；档案条件仍为定理30.3的完整见证条件。

证明。选 $S$ 使两流的闭值域严格位于引理30.2的共同逆域；$z$ 负向时用 $\sigma z$ 的递增逆定义同一个 $z_p^{-1}\circ Z$，两个减函数的复合仍增加。非零导数和联合逆函数正则性给
$$
\theta'_{r,p}(s)=\frac{c\,r_{p_0,t}(cs)}{r_{p,t}(\theta_{r,p}(s))},\qquad
\theta'_{z,p}(s)=\frac{c\,z_{p_0,t}(cs)}{z_{p,t}(\theta_{z,p}(s))}.
\tag{30.108}
$$
分母在紧域上绝对值有正下界，分子分母同向。联合连续的逆函数在紧 $s$ 区间上一致连续，所以 $\theta_{i,p}\to cs$ 一致；再用上式的联合连续性得导数一致收敛至 $c$。这证明实际逆钟对参数的 $C^1([0,S])$ 连续性，而非仅逐点连续。令 $\gamma=\min\{c-c_-,c_+-c\}>0$，将两导数的统一偏差缩到 $\gamma/2$ 以下即得双边界；流相同由直接代入。若导数各自被钉为同一个精确常数 $c$，再加共同零点，则积分得两钟都等于 $cs$；绝对连续且几乎处处导数恒等于 $c$ 时也一样。这是更强的同步数据。正下增量率可按定理29.5供应阈值到达或期限条件，却不自动供应跨端口配对。$\square$

**命题 30.5（相对登记的定义域、三个射流与已知登记逆）。** 为讨论“同数值标签”画出的关系，先把两记录限制到一个共同标签区间 $I=[0,S]$，要求其全部内部时间和下述复合均在引理30.2的实际分支内。定义
$$
T_r=\theta_r(I),\quad T_z=\theta_z(I),\qquad
\delta=\theta_z\circ\theta_r^{-1}:T_r\to T_z,
\quad h=r_p\circ\delta\circ r_p^{-1}:r_p(T_r)\to r_p(T_z).
\tag{30.109}
$$
这里 $\delta$ 是同标签的内部时间登记，不是从 $r$ 标签到同时 $z$ 标签的匹配。后一映射只在内部像交集上为 $\theta_z^{-1}\circ\theta_r$。无噪同标签图 $f=Z\circ R^{-1}$ 恰为 $g_p\circ h$。若 $h$ 在零点为 $C^3$，$h(0)=0$，记 $a=h'(0)>0,b=h''(0),c_3=h'''(0)$，则
$$
\begin{aligned}
f'(0)&=ma,\\
f''(0)&=F(m)a^2+mb,\\
f'''(0)&=G(m,k)a^3+3F(m)ab+mc_3.
\end{aligned}
\tag{30.110}
$$
若三个登记射流已经独立获知，且 $f$ 的真实初始射流也可访问，则
$$
m=\frac{f'(0)}a,\qquad
G_* =\frac{f'''(0)-3F(m)ab-mc_3}{a^3},\qquad
k=\frac{3m^4+95m^2+300}{10}-\frac{10G_*}{m}.
\tag{30.111}
$$
必须有 $m\ne0,k>0$、逆值在先验内，并核对第二阶式；这些是此射流逆的模型相容条件，不认证任意整曲线为 PDE 曲线。

证明。对 $s\in I$，$h(R(s))=r_p(\theta_z(s))$，故 $g_p(h(R(s)))=z_p(\theta_z(s))=Z(s)$，且所写逆只在其实际值域上使用。三次一元链式法则为
$$
f'=g_p'(h)h',\qquad
f''=g_p''(h)(h')^2+g_p'(h)h'',
$$
$$
f'''=g_p'''(h)(h')^3+3g_p''(h)h'h''+g_p'(h)h'''.
\tag{30.112}
$$
在零点代入定理28.3给（30.110）；先解第一式得 $m$，再解第三式得 $G_*$，最后直接用（28.105）得（30.111）。共同内部时间使 $h$ 为恒等；共同来源、共同零点、各自单调、双边速率及增益校准都不单独给此恒等式。已知登记射流是附加资源，不能由这里的代数逆倒称它们已从两条标量流取得。$\square$

**定理 30.6（二阶登记相同仍有精确全流碰撞）。** 固定 $m\ne0$，取邻近的 $p=(m,k_p),q=(m,k_q)$。缩小共同正图区间至 $[0,r_a]$，使 $g_p([0,r_a])$ 含于 $g_q$ 的初始逆值域，令
$$
h=g_q^{-1}\circ g_p,\qquad g_q\circ h=g_p.
\tag{30.113}
$$
则 $h$ 严格增加且
$$
h(0)=0,\quad h'(0)=1,\quad h''(0)=0,\quad
h'''(0)=\frac{k_q-k_p}{10},\qquad
h(r)=r+\frac{k_q-k_p}{60}r^3+O(r^4).
\tag{30.114}
$$
存在实现这一精确全流等式的实际钟；因此初始一、二阶相对登记正确仍不识别黏性。其内部时间共轭 $\delta=r_q^{-1}\circ h\circ r_q$ 满足
$$
\delta'(0)=1,\quad\delta''(0)=0,\quad
\delta'''(0)=\frac{\nu(q)^2(k_q-k_p)}{10}.
\tag{30.115}
$$

证明。$\sigma g_p,\sigma g_q$ 由引理30.2在共同分支严格增加，其零点导数绝对值有正下界。选 $r_a$ 足够小给所需像包含；逆及 $h$ 为 $C^4$。在 $g_q(h(r))=g_p(r)$ 中依次求一、二、三阶导数，得 $mh'=m$，$F(m)(h')^2+mh''=F(m)$，以及在 $h'=1,h''=0$ 下
$$
G(m,k_q)+mh'''(0)=G(m,k_p).
\tag{30.116}
$$
$G(m,k_p)-G(m,k_q)=m(k_q-k_p)/10$ 给第三导数，Taylor 公式给（30.114）的系数 $1/60$。任取固定连续严格递增满射 $R:[0,S]\to[0,r_a]$，基准世界取两钟均为 $r_p^{-1}\circ R$；$q$ 世界取
$$
\theta_{r,q}(s)=r_q^{-1}(R(s)),\qquad
\theta_{z,q}(s)=r_q^{-1}(h(R(s))).
\tag{30.117}
$$
它们都在实际分支，给同一 $R(s)$ 和同一 $g_p(R(s))$，保留整个标签记录。定理30.3的基本实验容许这些世界；更丰富档案须另核完整相容。取命题30.4的平滑基准 $R$、参数足够邻近时，上述钟也可同时留在正宽度速率带中，因为第二钟亦等于 $z_q^{-1}\circ z_p\circ r_p^{-1}\circ R$，适用同一 $C^1$ 逆连续性。

为核内部时间系数，令 $A=(k_q-k_p)/60$。$r_q(t)=\nu(q)t+O(t^2)$ 给 $h(r_q(t))-r_q(t)=A\nu(q)^3t^3+O(t^4)$。$r_q^{-1}$ 在零点的导数为 $1/\nu(q)$，其导数沿该初始区间为 $1/\nu(q)+O(t)$，故 $\delta(t)=t+A\nu(q)^2t^3+O(t^4)$，得到（30.115）。歧义不来自图坐标选择。

反向地，若登记 $h$ 为 $C^3$ 且 $h(r)=r+o(r^3)$，将 $h$ 的三阶 Taylor 展开与此式比较，先除以 $r$、再 $r^2$、再 $r^3$，依次得 $h'(0)=1,h''(0)=h'''(0)=0$。式（30.110）使真实 $g_p$ 和表观 $f$ 有同一三阶射流，定理28.3遂识别非零 $m$ 的参数。只有 $O(r^3)$ 时，（30.114）就是反例。这里的必要边界专属于已访问真实初始射流的协议，不是任意传感器实验的普遍定理。$\square$

**命题 30.7（一个正同步端点的纤维及端点固定全流见证）。** 固定内点 $p_0=(m_0,k_0)$，$m_0\ne0$，以及充分小的 $\eta>0$。一份正同时对 $r=\eta,z=g_{p_0}(\eta)$ 的已有局部纤维，在 $(m,k)$ 坐标中写成
$$
g_{m(k),k}(\eta)=g_{p_0}(\eta),\qquad
m(k_0)=m_0,\qquad
m'(k)=\frac{m(k)\eta^2}{60}+O(\eta^3).
\tag{30.118}
$$
对其每个邻近点 $q=(m(k),k)$，有 $h_q=g_q^{-1}\circ g_{p_0}$，且 $h_q(0)=0,h_q(\eta)=\eta$。该 $h_q$ 给一个共同初点和一个正同步端点都正确、全部内部本地流仍相同的实际双钟世界族。

证明。存在的精确一对纤维直接复用命题26.4，实际黏性前提已由推论28.5履行；定理28.2消去这一对的时间，坐标（28.101）把它送为上式的图水平集。黏性参数到 $k=\alpha^2/\nu^2$ 的导数非零，所以该曲线可用 $k$ 参数化。引理28.4给 $\partial_mg(\eta)=\eta+O(\eta^2)\ne0$，对已有水平集求导即得
$$
m'(k)=-\frac{\partial_kg_{m(k),k}(\eta)}{\partial_mg_{m(k),k}(\eta)}
=-\frac{-m(k)\eta^3/60+O(\eta^4)}{\eta+O(\eta^2)},
\tag{30.119}
$$
故为（30.118）；紧的固定符号邻域使该导数在足够小 $\eta$ 下非零。没有重证另一条一般隐函数定理。单调性和端点等值保证 $g_{p_0}([0,\eta])$ 正好是 $g_q([0,\eta])$，故 $h_q$ 定义在整个 $[0,\eta]$，且固定两端点。固定 $R:[0,S]\to[0,\eta]$ 严格递增满射，用（30.117）将 $p$ 换成 $p_0$，便得
$$
\theta_{r,q}(0)=\theta_{z,q}(0)=0,\qquad
\theta_{r,q}(S)=\theta_{z,q}(S)=r_q^{-1}(\eta),
\quad (R(s),Z(s))=(R(s),g_{p_0}(R(s))).
\tag{30.120}
$$
所以在基本实验额外保留端点同时证书，也不能分开该族。端点的物理经过时间 $r_q^{-1}(\eta)$ 未知并可随候选变化；把它作为一个已知数保留是另一合同。此处 $m$ 变化，$h_q'(0)=m_0/m(k)$ 一般不为一，故本纤维不同时保留定理30.6的固定 $m$ 初始登记条件。精确初始相对速率加正同步点可以带来额外独立信息，不能把两个不同反例的保留条件无证明地合并。$\square$

**推论 30.8（两实际配对事件与一个混合理想协议）。** 取定理29.3的同一个 $U,\eta_0$，$0<\eta\le\eta_0$。若完整档案实际含两对标签 $(s_j,v_j)$，并认证它们在同一实际初始分支、
$$
\theta_r(s_j)=\theta_z(v_j),\qquad
r_p(\theta_r(s_j))=j\eta\quad(j=1,2),
\tag{30.121}
$$
则两份精确 $z$ 值在 $U$ 内唯一确定 $p$，不需两事件之间钟相等。在没有额外参数信息的这个有限配对协议中，一份正配对不足、两份足够；准备零对恒为 $(0,0)$，不给额外参数约束。

证明。实际同时性将两读出严格投为 $g_p(\eta),g_p(2\eta)$。将定理29.3（29.108）用于 $\lambda=1,\mu=2$，相同两值给相同预条件像，遂得 $p=q$。命题30.7的一维纤维给一份不足，并且保留了所有本地流；结论是该固定基本实验内的局部事件计数，不是费用或所有传感器的最小性。若拟合要称为完整档案相容，仍需（30.102）的世界；这里没有从两数反造旧档案。定理29.5关于真正同时阈值检测的资源前提也没有被省略。

另有不同的混合理想协议：若 $h'(0)=1$ 已认证且真实表观斜率 $f'(0)$ 已经取得，则命题30.5先给 $m=f'(0)\ne0$。对固定 $m$ 的紧 $k$ 区间，引理28.4给 $\partial_kg(\eta)=-m\eta^3/60+O(\eta^4)$；缩小 $\eta$ 使余项绝对值小于 $|m|\eta^3/120$，该导数恒非零且符号固定。沿任意两个 $k$ 之间积分，$g_{m,k}(\eta)$ 严格单调，所以再有一份实际正配对便唯一确定 $k$。这额外用了导数访问，不以有限样点免费替代斜率。精确参数到指定准备场任务的因子化仍直接用推论28.7的既有接口，作用域不是含任意钟和旧记录的整个世界集合。$\square$

**命题 30.9（实际共享单调标记所给的配对）。** 额外假设两端口在每次取得时无扰动记录同一个来源的标记 $M(t)$，它在所用实际时间区间连续严格单调，因而单射。标记值、共同来源和这种单射性均是合同输入。任何两个实际标记读数满足
$$
M(\theta_r(s))=M(\theta_z(v))
\quad\Longleftrightarrow\quad\theta_r(s)=\theta_z(v).
\tag{30.122}
$$
若完整标记流已精确取得，则在两内部像的交集上，其唯一匹配为
$$
(M\circ\theta_z)^{-1}\circ(M\circ\theta_r)
=\theta_z^{-1}\circ\theta_r.
\tag{30.123}
$$
两次实际匹配且满足（30.121）的事件即可使用推论30.8。

证明。正向由明确假设的 $M$ 单射性，反向由同一个函数作用于相同内部时间；严格单调性使每个完整流在其实际值域上可逆，从而给复合式和唯一性。此为成熟的单调逆匹配机制。[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)引理15.8（15.17）在 $C=C^*>0,J_S\ne0$、相同耦合、增益及端口内积下，以 $M(t)=\operatorname{tr}(J_S^*e^{-tC}J_S)$ 证明这一机制的专门实例；其正半群迹假设不证明本 PDE 自带任意严格单调标记。因此这里把一般 $M$ 的单射性明列为新增前提，并直接完成所需推导。

标记的存在、实际相等值、覆盖区间、检测器权限与精度、校准、延迟和费用均不由原两标量流推出。有限个不相等标记值及插值不认证精确同时事件；已获共同标记关系不能在构造碰撞时删除。严格单调但未知函数只供应实际值域交集内的配对，不提供绝对时间标尺或全域稳定常数，边界亦见恢复卷命题15.10。$\square$


## 31. 完整异步档案上的定时精度与联合下界

**定理 31.1（两位置比较中的定时误差）。** 使用定义30.1的固定实验、定理29.3的同一个闭凸 $U=\overline B(p_0,\rho)$、$K,\eta_0$ 及共同图域 $[0,r_*]$。设 $0<\eta\le\eta_0\le\min\{1,r_*/3\}$，已测第一端口位置仍满足
$$
\widetilde r_1\in[3\eta/4,5\eta/4],\qquad
\widetilde r_2\in[7\eta/4,9\eta/4],\qquad
0\le\epsilon_r\le\eta/8.
\tag{31.101}
$$
每份完整世界的实际事件时间记为 $t_j^r=\theta_r(s_j)$、$t_j^z=\theta_z(v_j)$；两事件须在同源初始分支，相关图坐标及其间线段均在共同图域。假设同一联合事件 $\mathcal E_H$ 对全部候选同时供应
$$
\begin{aligned}
|r_p(t_j^r)-\widetilde r_j|&\le\epsilon_r,\qquad
|z_p(t_j^z)-\widetilde z_j|\le\epsilon_z,\\
|r_p(t_j^z)-r_p(t_j^r)|&\le\delta_r\quad(j=1,2).
\end{aligned}
\tag{31.102}
$$
这里 $\delta_r\ge0$ 是独立认证的图坐标错位界，勿与（30.109）的登记映射 $\delta$ 混同。用（29.115）的 $L_g,C_F,C_T$，令
$$
e_{\rm async}=\epsilon_z+L_g(\epsilon_r+\delta_r).
\tag{31.103}
$$
则实际完整参数可行集中任意 $p,q$ 满足
$$
\|p-q\|_2\le
\min\left\{2\rho,\frac{4KC_Te_{\rm async}}{\eta^3}\right\}.
\tag{31.104}
$$
若另有独立认证的 $|t_j^z-t_j^r|\le d_t$ 和同一实际候选时域上的统一 $|\partial_tz_p|\le B_z$，则可把（31.103）换成 $\epsilon_z+L_g\epsilon_r+B_zd_t$；两种证书兼有时取两项定时贡献的较小者。

证明。真实 $r_j=r_p(t_j^r)$ 仍落在定理29.4证明所列的$[5\eta/8,11\eta/8]$、$[13\eta/8,19\eta/8]$，均在 $[0,r_*]$。分支条件另保证 $r_p(t_j^z)$ 在图域内，不能只靠窗口推出这一点。对同一实际 $p$，
$$
\begin{aligned}
|z_p(t_j^z)-g_p(r_j)|
&=|g_p(r_p(t_j^z))-g_p(r_j)|\le L_g\delta_r,\\
|g_p(\widetilde r_j)-\widetilde z_j|
&\le L_g\epsilon_r+L_g\delta_r+\epsilon_z=e_{\rm async}.
\end{aligned}
\tag{31.105}
$$
这些只是完整世界的必要投影约束。任意两候选在固定测得位置的预测差至多 $2e_{\rm async}$。取 $\lambda=\widetilde r_1/\eta,\mu=\widetilde r_2/\eta$，它们在（29.106）的设计域；直接使用定理29.3的解析两位置比较，并按定理29.4（29.119）的残差计算得
$$
|\Delta A|\le\frac{2e_{\rm async}}{\lambda\eta},\qquad
|\Delta B|\le2e_{\rm async}\left[
\frac{2(1+\mu/\lambda)}{\mu(\mu-\lambda)\eta^3}
+\frac{C_F}{\lambda\eta^2}\right].
\tag{31.106}
$$
用（29.108）与原来相同的设计常数界就得（31.104）。这是对投影约束的解析比较，没有把双钟世界变成定义29.1的一钟世界。若用内部时间证书，则在两实际时刻之间积分 $z_t$ 得 $|z_p(t_j^z)-z_p(t_j^r)|\le B_zd_t$，其余步骤相同。相同外部标签和各自速率界不使 $d_t$ 为零；把外部标签差换成内部错位必须另有登记或定时证书。

若真实世界实现全部档案及联合事件，它给非空见证，对任意同样有完整见证的拟合，式（31.104）给真实误差界；否则只是条件成对界，不产生参数。只拟合（31.105）不保证旧关系、动作、两钟和误差能共同实现。物理参数上界直接沿用（29.121）；较强旧档案可缩小完整纤维，不能以一个残差拟合替掉完整交集。$\square$

**引理 31.2（先证明逆值域裕量的三次登记界）。** 固定 $m\ne0$，令
$$
I_k=[k_0-d_0,k_0+d_0],\qquad d_0>0,\quad k_0-d_0>0,
\qquad P_I=\{(m,k):k\in I_k\}.
\tag{31.107}
$$
该段须在同一共同分支／先验内；与定理31.1比较时还要求 $P_I\subset U$。缩短共同图域到 $[0,\bar r]$，可以对全部 $k\in I_k$ 保证
$$
|\partial_kg_{m,k}(r)|\le\frac{|m|}{40}r^3,\qquad
|\partial_rg_{m,k}(r)|\ge\frac{|m|}{2},\qquad
\operatorname{sign}(\partial_rg_{m,k})=\sigma=\operatorname{sign}(m).
\tag{31.108}
$$
取 $0<\eta\le\bar r/3$、$d_0\eta^2\le1$。对任意 $k_a,k_b\in I_k$ 且 $|k_a-k_b|\le d_0$，$g_{m,k_b}([0,2\eta])$ 在 $g_{m,k_a}([0,3\eta])$ 的逆值域中；具体地，写 $w_k=\sigma g_{m,k}$，有
$$
w_{k_a}(3\eta)-w_{k_b}(2\eta)\ge\frac{3|m|\eta}{10}>0.
\tag{31.109}
$$
因此实际登记
$$
h_{a,b}=g_{m,k_a}^{-1}\circ g_{m,k_b}:[0,2\eta]\to[0,3\eta]
\tag{31.110}
$$
连续严格增加、$h_{a,b}(0)=0$，并满足
$$
|h_{a,b}(r)-r|\le\frac{|k_a-k_b|}{20}r^3
\quad(0\le r\le2\eta).
\tag{31.111}
$$

证明。引理28.4给 $\partial_kg=-mr^3/60+O(r^4)$；在此固定紧段上取统一余项界 $Cr^4$，$C\bar r\le|m|/120$ 足以给第一界。$g_r(0)=m$ 和联合连续性允许再缩 $\bar r$ 得后两界。这里使用实际混合 Taylor 余项，不由有限数值点猜全域导数界。

先在已知正向域证明逆像存在：$w_k(0)=0$，且 $w_k'\ge|m|/2$，故
$$
\begin{aligned}
w_{k_a}(3\eta)-w_{k_b}(2\eta)
&=[w_{k_a}(3\eta)-w_{k_a}(2\eta)]
  +[w_{k_a}(2\eta)-w_{k_b}(2\eta)]\\
&\ge\frac{|m|\eta}{2}
 -\frac{|m|\,|k_a-k_b|}{40}(2\eta)^3\\
&\ge |m|\eta\left(\frac12-\frac{d_0\eta^2}{5}\right)
 \ge\frac{3|m|\eta}{10}.
\end{aligned}
\tag{31.112}
$$
第二差沿位于 $I_k$ 内的参数线段积分。严格增加及共同零点使每个 $w_{k_b}(r)$ 都落在 $w_{k_a}([0,3\eta])$，因此（31.110）已定义且其值确实在导数估计域内。现在才能在 $r$ 和 $h_{a,b}(r)$ 之间用导数下界：
$$
\frac{|m|}{2}|h_{a,b}(r)-r|
\le |g_{m,k_a}(h_{a,b}(r))-g_{m,k_a}(r)|
=|g_{m,k_b}(r)-g_{m,k_a}(r)|
\le\frac{|m|\,|k_a-k_b|}{40}r^3.
\tag{31.113}
$$
约去正 $|m|/2$ 得（31.111），没有预设逆像仍在域内的循环论证。固定参考 $k_b=k_{\rm ref}$ 时就给 $|h_k(r)-r|\le|k-k_{\rm ref}|r^3/20$。$k_a,k_b$ 各在 $I_k$ 并不足以给距离 $\le d_0$；本引理明确保留这一附加条件，下一定理以同侧参数保证它。$\square$

**定理 31.3（整条流的联合噪声／同步两世界下界）。** 使用引理31.2的固定参数段、$\eta$ 和分支。先固定定义30.1的一次实验及其完整旧档案，令两个本地标签域均为 $[0,2S_0]$，$S_0>0$；该合同允许精确 $r$ 流、整条 $z$ 报告流上的绝对误差至多 $\epsilon\ge0$，以及图坐标登记的统一误差 $\sup_{0\le r\le2\eta}|h(r)-r|\le\tau$，$\tau\ge0$。这些是联合有界对抗误差合同，不声明独立随机样本。可把 $m$ 精确给予观察者。置
$$
E=\frac{5\epsilon}{|m|\eta^3},\qquad
S=\frac{5\tau}{2\eta^3},\qquad
d=\min\{d_0,E+S\},\quad d_n=\min\{d,E\},\quad d_s=d-d_n,
\tag{31.114}
$$
并用 $\varsigma\in\{-1,1\}$ 区别两世界，勿与分支方向 $\sigma$ 混同。真实参数、辅助中间参数及登记分别为
$$
k_{{\rm true},\varsigma}=k_0+\varsigma d,\qquad
k_{{\rm int},\varsigma}=k_0+\varsigma d_n,\qquad
h_\varsigma=g_{m,k_{{\rm true},\varsigma}}^{-1}
                 \circ g_{m,k_{{\rm int},\varsigma}}.
\tag{31.115}
$$
假设下述同一对实际 PDE／钟／误差世界在这个固定实验中分别被允许，且实现全部同一旧记录、动作、费用和已获跨端口关系。则任何估计器的最坏绝对 $k$ 误差至少
$$
d=\min\left\{d_0,
\frac{5\epsilon}{|m|\eta^3}+\frac{5\tau}{2\eta^3}\right\}.
\tag{31.116}
$$
此下界也适用于 $(m,k)$ Euclidean 误差，以及随机估计器的最坏期望绝对损失。以 $k_{\max}=k_0+d_0$ 计，黏性和隐藏幅度的最坏绝对误差下界分别为
$$
\frac{|\alpha|d}{2k_{\max}^{3/2}},\qquad
\frac{|m\alpha|d}{2k_{\max}^{3/2}}.
\tag{31.117}
$$

证明。由定义 $0\le d_n\le E$、$0\le d_s\le S$：若 $d\le E$ 则 $d_s=0$，若 $d>E$ 则 $d_s=d-E\le S$。真实与中间参数都在 $I_k$ 内，且每个同侧距离恰为 $d_s\le d_0$，不是两个真实端点之间的 $2d$。故引理31.2先给每个登记的 $3|m|\eta/10$ 逆域裕量，再给
$$
\sup_{0\le r\le2\eta}|h_\varsigma(r)-r|
\le\frac{d_s(2\eta)^3}{20}
=\frac25d_s\eta^3\le\tau.
\tag{31.118}
$$
这里 $h_\varsigma$ 取值在 $[0,3\eta]$，真实两端口须可取得到所构造的初始内部时刻，不能把所需 $3\eta$ 图域缩成未经证明的 $2\eta$ 域。

取固定的整个报告 $r$ 流 $R(s)=\eta s/S_0$，$0\le s\le2S_0$。以 $r_{\rm true,\varsigma}$ 表示真实参数的实际 PDE 第一端口，给每个世界两只钟
$$
\begin{aligned}
\theta_{r,\varsigma}(s)&=r_{{\rm true},\varsigma}^{-1}(R(s)),\\
\theta_{z,\varsigma}(s)&=r_{{\rm true},\varsigma}^{-1}
                                  (h_\varsigma(R(s))).
\end{aligned}
\tag{31.119}
$$
这些是连续严格递增、共同零点为零的实际钟，其第二钟在图域至多 $3\eta$ 内；两世界的 $r$ 阈值 $\eta,2\eta$ 都保留同一外部时间戳 $S_0,2S_0$。真实 $z$ 流在这些钟下恰为 $g_{m,k_{{\rm int},\varsigma}}(R(s))$。辅助中间参数仅定义这一函数，不是同一世界内另换了一条 PDE 轨迹。定义完整流误差
$$
e_\varsigma(r)=g_{m,k_0}(r)-g_{m,k_{{\rm int},\varsigma}}(r),
\qquad e_{z,\varsigma}(s)=e_\varsigma(R(s)),\quad e_{r,\varsigma}=0.
\tag{31.120}
$$
沿中间参数至 $k_0$ 的线段积分（31.108）给
$$
\sup_{0\le r\le2\eta}|e_\varsigma(r)|
\le\frac{|m|d_n(2\eta)^3}{40}
=\frac{|m|d_n\eta^3}{5}\le\epsilon.
\tag{31.121}
$$
从而两世界的整个已报告流完全相同：
$$
\widetilde R_\varsigma(s)=R(s),\qquad
\widetilde Z_\varsigma(s)
=z_{{\rm true},\varsigma}(\theta_{z,\varsigma}(s))+e_{z,\varsigma}(s)
=g_{m,k_0}(R(s)).
\tag{31.122}
$$
全部本地标签、初点、$r$ 监测迹及两个阈值时间戳均被保留；这两个阈值上的 $z$ 标签并未被说成同时事件，也没有宣称两记录器的物理停止端点相同。定理30.6用于同一固定 $m$ 还给 $h_\varsigma'(0)=1,h_\varsigma''(0)=0$，所以此构造保留这两个额外初始登记条件，内部共轭也保留相应一、二阶条件。

基本档案可取定理30.3的固定双记录器合同，附加实际（31.118）的登记容差，联合误差集容许上述整条有界误差函数。准备初点、来源、分支、记录及校准由实际解和钟见证完成，故两世界确实相容。对于给定的更丰富档案，定理的完整世界条件不可省略：同一误差函数必须与所有其它误差一同属于实际 $\mathcal E_H$，同一两钟必须满足全部旧钟限制和动作历史。已知延迟方向、取得顺序、共同终止规则、更紧速率或额外读数可排除其中一个世界。小参数段或分别满足标量误差盒不证明联合允许性。尤其构造的误差依赖参数且沿整流相关，不能移到独立随机误差模型中冒用。按引理31.2证明所用的余项小性，$\sigma\partial_kg\le-|m|r^3/120<0$（$r>0$）。当 $d_s>0$ 时，沿同侧参数段积分给 $w_{k_{{\rm true},+}}(r)<w_{k_{{\rm int},+}}(r)$、$w_{k_{{\rm true},-}}(r)>w_{k_{{\rm int},-}}(r)$，由各真实 $w$ 严格增加得 $h_+(r)>r$、$h_-(r)<r$；$d_s=0$ 时两登记均为恒等。因此仅容许一种登记方向的先验可以排除一端，不能删掉该先验来保留下界。

一旦完整观察确实相同，定理29.7的标准两点三角论证直接适用。具体地，任意共同输出 $a$ 满足
$$
2d=|k_{{\rm true},+}-k_{{\rm true},-}|
\le |a-k_{{\rm true},+}|+|a-k_{{\rm true},-}|.
\tag{31.123}
$$
故至少一个世界误差不小于 $d$，再对估计器取下确界得（31.116）。随机估计器在同一完整记录上有同一输出律，对该不等式取期望即可；即使期望无穷，下界仍成立。沿真实参数段，$\nu'(k)=-|\alpha|/(2k^{3/2})$ 固定符号且绝对值至少 $|\alpha|/(2k_{\max}^{3/2})$。两真实黏性之差至少 $|\alpha|d/k_{\max}^{3/2}$，对黏性估计再取两点差的一半；$\beta=m\nu$ 给幅度下界。这里与（29.134）是同一物理坐标计算。

$E+S\ge d_0$ 时界在固定先验段半宽 $d_0$ 饱和；$\epsilon=\tau=0$ 时 $d=d_n=d_s=0$，两个世界合一，所得零下界不否定精确配对识别。任何一级 $(\eta,\epsilon,\tau)$ 的下界只在该级这两个完整见证被实际固定合同允许时成立；若要对全部噪声／同步级别统一声称下界，须对每一级验证该允许性。$\square$

**推论 31.4（纯同步及必要三次精度的协议范围）。** 在定理31.3的完整见证条件下，取 $\epsilon=0$ 直接得纯同步下界
$$
\text{最坏绝对 }k\text{ 误差}\ge
\min\left\{d_0,\frac{5\tau}{2\eta^3}\right\}.
\tag{31.124}
$$
若要求最坏绝对 $k$ 误差至多 $\Delta<d_0$，则在该级允许见证的实验中必须有
$$
\frac{5\epsilon}{|m|}+\frac{5\tau}{2}\le\Delta\eta^3;
\qquad \epsilon=0\ \Longrightarrow\ \tau\le\frac25\Delta\eta^3.
\tag{31.125}
$$

证明。$\epsilon=0$ 使 $d_n=0,d_s=d$，是同一构造的特例，无需另一个下界证明。所需损失上限迫使 $d\le\Delta$；因 $\Delta<d_0$，这只能由 $E+S\le\Delta$ 达成，代入即得。若一族缩窗实验每一级都容许这些完整见证，且要求其最坏误差趋零，则必要有 $\epsilon/\eta^3\to0$ 及 $\tau/\eta^3\to0$（此处 $m,d_0$ 固定）。只有 $O(\eta^3)$ 的允许定时误差可以隐藏固定正参数差；定理31.1在相同 $U$、共同域及完整非空条件下给相应三次尺度的充分界，所以量级相配，数值常数不宣称最优。

下界即使给予精确 $m$、完整局部流及一、二阶初始登记仍成立，但不能用于取得了共享标记、精确共同顺序或其它排除见证的协议。任意反馈实验也不自动属于这个固定记录器实验。[SharpChallengeInstrument](../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SharpChallengeInstrument.lean) 的 `result` 在其有限概率仪器中区别固定动作词和因果反馈的记录距离；它只强化这里必须声明协议的边界，不供应本 PDE 的定时下界或随机噪声定律。本节的噪声证书、联合允许性和取得资源均不可由该模块替代。$\square$


## 32. 已获联合顺序的精确配对与有限括区间

**定理 32.1（稠密精确顺序切割确定匹配标签）。** 使用定义30.1的同源、合法、实际连续严格增钟，限制第二标签域为闭区间 $[v_-,v_+]$。令 $D\subseteq[v_-,v_+]$ 稠密并包含两端点，所有 $v\in D$ 的精确 $z$ 读值 $Z(v)=z_p(\theta_z(v))$ 已实际保留。对某一已获 $r$ 事件 $s$，假设其实际内部时间落在 $\theta_z([v_-,v_+])$ 中，并且档案 $J$ 含每一项比较
$$
\theta_z(v)\le\theta_r(s)\qquad(v\in D)
\tag{32.101}
$$
的精确真值，包括为假的那些比较。则档案确定的下切口给实际匹配标签
$$
v(s)=\sup\bigl(\{v\in D:\theta_z(v)\le\theta_r(s)\}\cup\{v_-\}\bigr)
=\theta_z^{-1}(\theta_r(s)).
\tag{32.102}
$$
相应同时 $z$ 值由已获值或其唯一连续延拓决定。完整连续记录是 $D=[v_-,v_+]$ 的特例。

证明。连续严格增加及实际时间重叠给唯一 $v_*\in[v_-,v_+]$ 使 $\theta_z(v_*)=\theta_r(s)$。严格增加使比较为真恰当且仅当 $v\le v_*$，所以下集合正好是 $D\cap[v_-,v_*]$，上界为 $v_*$。若 $v_*>v_-$，任意 $a<v_*$ 且 $a\ge v_-$ 时，稠密性在 $(a,v_*)$ 中给一个 $v\in D$，故上确界不小于任意这样的 $a$，必等于 $v_*$。若 $v_*=v_-$，附加的 $v_-$ 保证集合非空且上确界正为左端；若 $v_*=v_+$，右端已被记录且其比较为真，上确界是右端。等号采用“$\le$”真值约定，没有以严格不等式遗漏端点。

若 $v_*\in D$，匹配读数本已实际取得。否则由稠密性选 $v_n\in D$ 趋于 $v_*$，实际 $Z=z_p\circ\theta_z$ 连续，故 $Z(v_n)\to Z(v_*)$。任意两个与全部稠密精确值相合的连续函数在每点用这样的序列取极限都相等，所以该延拓唯一且与序列无关。这是已有无限精确记录的数学解码，不声称新的测量、有限查询算法或有限误差保证。

因此，如果定理30.3的完整初始双流还保留这里的全部真实跨端口顺序，则每个处于实际像交集的 $r$ 事件都取得唯一的同时 $z$ 值。对共同零点附近的正重叠区间，精确全 $r$ 流给真实 $g_p$ 的初始 germ；非零 $m$ 时定理28.3切开不同参数。或者当两处所需 $r$ 阈值都处于重叠域时，用推论30.8的两位置逆。故不能声称完整联合时间顺序下仍有原先只有边缘流的参数碰撞；这些竞争世界必须在某些已获比较上不同或参数已经相同。

顺序切割来自共同实现的实际取得顺序，不由两份无关本地时间戳表推得。未知延迟的包到达顺序也不认证（32.101）。内部像无重叠的部分没有这个逆匹配，不得外推；有限个比较一般只把 $v_*$ 夹在一个区间，不享有稠密极限结论。$\square$

**命题 32.2（实际有限顺序给出的精确输出区间）。** 对 $j=1,2$，完整档案实际保留同源的一个 $r$ 事件、两个 $z$ 事件及同一世界内的顺序证书
$$
t_j^-\le t_j^r\le t_j^+,\qquad
r_j=r_p(t_j^r),\quad z_j^-=z_p(t_j^-),\quad z_j^+=z_p(t_j^+).
\tag{32.103}
$$
全部事件在引理30.2同一方向 $\sigma$ 的初始分支内。则准确的单调区间约束为
$$
\sigma g_p(r_j)\in[\sigma z_j^-,\sigma z_j^+],
\qquad
|g_p(r_j)-c_j|\le w_j,
\quad c_j=\frac{z_j^-+z_j^+}{2},\quad
w_j=\frac{|z_j^+-z_j^-|}{2}.
\tag{32.104}
$$
此区间是顺序与单调性推出的必要区间，不断言其中每个值都有满足整份 PDE 档案的实现。

证明。$\sigma z_p(t)$ 在共同分支严格增加，所以（32.103）给
$\sigma z_j^-\le\sigma z_p(t_j^r)\le\sigma z_j^+$。$z_p(t_j^r)=g_p(r_j)$。区间中心为 $\sigma(z_j^-+z_j^+)/2$、半宽为 $\sigma(z_j^+-z_j^-)/2=|z_j^+-z_j^-|/2$；把中心乘回 $\sigma$ 就得绝对误差式。端点重合给零宽，允许实际同时事件。

$c_j$ 是由原记录计算的任务摘要，不是一次已获同时 $z$ 测量。两个 $r$ 读数、两组所有 $z$ 端点、来源／校准／分支及实际顺序证书都仍保留；若两个组共享同一端点，该记录也不会因重复使用变成独立的新读数。$\square$

**定理 32.3（含噪顺序区间与完整参数纤维）。** 继续命题32.2，实际报告为 $\widetilde r_j,\zeta_j^-,\zeta_j^+$。在同一个联合事件内，对全部完整候选有
$$
|r_j-\widetilde r_j|\le\epsilon_r,\qquad
|z_j^- -\zeta_j^-|\le\epsilon_j^-,\qquad
|z_j^+ -\zeta_j^+|\le\epsilon_j^+,
\tag{32.105}
$$
端点误差界非负。令
$$
A_j=\sigma\zeta_j^- -\epsilon_j^-,\qquad
B_j=\sigma\zeta_j^+ +\epsilon_j^+.
\tag{32.106}
$$
若任一个 $A_j>B_j$，在声明的顺序、分支和误差合同下无完整见证。否则取由记录导出的中心和半径
$$
c_j=\frac{\sigma(A_j+B_j)}2,\qquad
w_j=\frac{B_j-A_j}{2}\ge0,\qquad w=\max\{w_1,w_2\}.
\tag{32.107}
$$
若参数域及测得位置满足定理31.1继承的 $U,\eta_0$、（31.101）和共同图域条件，则每个完整候选满足
$$
|g_p(\widetilde r_j)-c_j|\le w_j+L_g\epsilon_r,\qquad
\operatorname{diam}\mathcal K_H^{\rm async}
\le\min\left\{2\rho,\frac{4KC_T(w+L_g\epsilon_r)}{\eta^3}\right\}.
\tag{32.108}
$$

证明。先按同一实际世界的端点误差和方向取界：
$$
A_j\le\sigma z_j^-\le\sigma g_p(r_j)
\le\sigma z_j^+\le B_j.
\tag{32.109}
$$
若 $A_j>B_j$，该不等式链不可能，故完整可行集为空；不能把倒置区间静默投影为一个非空区间。若顺序正确，（32.109）推出 $|g_p(r_j)-c_j|\le w_j$。由 $|r_j-\widetilde r_j|\le\epsilon_r$ 及共同 $L_g$ 界，三角不等式给（32.108）的残差。两个完整候选在同一测得位置的预测差各至多 $2(w+L_g\epsilon_r)$，直接应用定理29.3的解析比较和定理29.4（29.119）的相同计算即得直径界。

推导只用真实联合事件的必要坐标界，没有假定四个端点误差独立。$A_j\le B_j$ 也不证明完整档案非空：更强联合噪声、其它端点、钟或动作关系仍可排除所有世界。一个数值候选只拟合这两个区间，仍须给原始端点、实际顺序与所有旧关系共同成立的世界，才可称为档案相容。真实世界若满足全部前提，就供给非空见证，任一有完整见证的拟合相对它亦满足所列参数界；物理参数误差继续按（29.121）换算。$\square$

**命题 32.4（实际网格宽度与原始中点的另一误差界）。** 在命题32.2的实际括区间中，设两个 $z$ 标签为 $v_j^-\le v_j^+$，同一 $z$ 钟在相应区间满足上增量率
$$
0\le\theta_z(v')-\theta_z(v)\le\Lambda(v'-v)
\quad(v_j^-\le v\le v'\le v_j^+),\qquad
\Delta v_j=v_j^+-v_j^-.
\tag{32.110}
$$
还要求 $|z_{p,t}|\le B_z$ 在这些实际内部区间成立。则真实半宽满足
$$
\frac{|z_j^+-z_j^-|}{2}
\le\frac{B_z\Lambda\Delta v_j}{2}.
\tag{32.111}
$$
在（32.105）的同一联合误差事件上，原始报告中点 $c_j^{\rm raw}=(\zeta_j^-+\zeta_j^+)/2$ 满足另一条证书
$$
|g_p(r_j)-c_j^{\rm raw}|
\le\frac{B_z\Lambda\Delta v_j}{2}
 +\frac{\epsilon_j^-+\epsilon_j^+}{2}.
\tag{32.112}
$$
若这些上率及速度界对同一参数／钟候选域统一成立，可在测得 $r$ 处另加 $L_g\epsilon_r$，再用定理29.3比较完整参数纤维。

证明。顺序证书先保证 $t_j^r$ 确实在两个端点之间，而两端点来自同一 $z$ 钟，所以 $t_j^+-t_j^-\le\Lambda\Delta v_j$。沿实际时间积分给
$$
|z_j^+-z_j^-|=\left|\int_{t_j^-}^{t_j^+}z_{p,t}(t)\,dt\right|
\le B_z(t_j^+-t_j^-)\le B_z\Lambda\Delta v_j.
\tag{32.113}
$$
真实中点 $c_j^{\rm true}=(z_j^-+z_j^+)/2$ 到 $g_p(r_j)$ 的距离至多真实半宽，且
$|c_j^{\rm raw}-c_j^{\rm true}|\le(\epsilon_j^-+\epsilon_j^+)/2$，相加得（32.112）。噪声可完全相关。此原始中点界与定理32.3的观测区间中心／半径是两个不同的有效摘要；误差不对称时两中心一般不同，不能把一个中心配上另一个未经证明的半径。

只有本地标签与上率界不证明跨端口的 $t_j^-\le t_j^r\le t_j^+$；顺序证书必须已实际取得。此处不给截止期限、自动检测器或查询最优性。若后来实际取得包含该 $r$ 事件且嵌于旧时间括区间的新括区间，精确输出区间按单调性嵌套，因而半宽不增；带噪情形保留并相交全部旧、新有效输出区间，若交集非空其宽度不增，若为空则无共同见证。更细的已获标签括区间在相同上率、速度及不增端点误差预算下也改善（32.112）的网格项。所有旧原始记录始终留在（30.102）中，不能用一次新的中点替换它们。$\square$

**约定 32.5（关系接口的依赖、来源及未解边界）。** 第30—32节在固定校准准备族内连接同源标量流、潜在局部钟、已获联合顺序与参数任务。命题21.7的双钟单对反例在定理30.3中接到实际 PDE 的完整初始流；命题22.2—22.3关于未知钟、记录核、推进操作及实际费用的区别仍保留。这里变动的是允许世界中的潜在登记，不能用一次共同已知坐标变换消除，也不能由被动流碰撞推出受驱动实验的碰撞。实际正黏性解及时间／参数正则性由恢复卷定理27.2—27.4承担；共同图逆、三阶识别、一次混合 Taylor 余项由本卷定理28.2—引理28.4承担；一份正对纤维由命题26.4及推论28.5承担；两位置解析逆和残差比较由定理29.3—29.4承担。$\alpha$ 的符号、绝对尺度和剪切退化仍按命题28.6，准备场任务的因子化仍按推论28.7的既有接口，不在这里另造一般恢复定理。

这些源推导属于仓内综合（repo-derived）。链式法则、非零导数的逆匹配、积分 Taylor、中值估计、两点三角下界及稠密顺序切割均为成熟机制；逆函数与 Taylor 的具体文献／上游入口已在定理28.2、引理28.4列明，输出导数与有限记录的辨识方法沿用推论28.7、定理29.2所列 Sontag 文献。恢复卷引理15.8只供应其专门共享正半群迹的匹配，不承担任意标记的存在。本节增加的是这些机制在实际异步 PDE 取得合同下的适用前提、完整钟／误差见证、共同逆域裕量和误差运输，未提出一般原创性或新的全 PDE 正则性主张。

数学接口与待解条件可写为如下关系图；`derived` 只指本节在明列假设下的普通推导，`open` 指仍未解决的问题，不表示形式化账目状态。

```text
actual prepared source + complete retained archive
  +-- separate local streams ----------> clock-fiber collisions       [derived]
  +-- registration jets ---------------> third-jet inverse            [derived]
  +-- two certified paired events -----> local finite-record inverse  [derived]
  +-- joint noise / timing allowances -> cubic two-world lower bound  [derived]
  +-- exact dense cross-port order ----> pairing on actual overlap    [derived]
  +-- acquired finite order brackets --> interval / diameter bounds   [derived]
  +-- independent unbounded clocks ----> global-history invariants    [open]
  +-- specified stochastic timing law -> law-specific identification [open]
  +-- fixed acquisition cost model ----> optimal protocol / constants [open]
```

仍须分别解决：给定更丰富实际档案是否允许所展示的同一完整竞争世界；独立无界钟的全时间不变量；特定相关定时噪声定律下的精确或稳定识别；固定费用模型下的最优同步协议、常数及资源；不在实际重叠域内的恢复。有限窗上可延长钟并不履行这些问题，这些局部观察结论不扩展其 PDE 适用域。

空间复相位与实际已获初始参考、参考共用误差，以及独立未知增益是另列的接口问题：本节始终固定真实端口方向、相位和有符号 $\alpha$，不以同步数据代替相位校准，不丢弃已获初始参考，也不从本节声称含噪校准逆已解决。整体关系统一的目标还包括空间、边界、记忆及其允许后续实验的保真运输；本节只完成这一固定时钟接口的条件推导，不给物理时空密度、时间涌现、任意流体初态或整个研究目标的结论。

## 32.99 追加锚

## 33. 相干复数世界、实际配对与共用初始参考的误差几何

**定义 33.1（复端口实验与完整共同实现）。** 先固定一次实验 $\mathcal X_{\rm phase}$：独立已知的物理幅度 $a_{\rm cal}>0$；[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定义28.1的 Fourier 标架、分量方向及相干复校准；固定平移的无外力准备族；黏性／径向先验；来源及分支规则；两个本地标签域 $I_A,I_C$；允许动作、钟对、延迟及费用；全部旧记录的解释规则；一份联合原始误差模型。这另立复数平移准备合同，定义29.1的有符号实端口单钟世界不是它的世界集合。

一份完整世界 $w\in\Omega_{\mathcal X_{\rm phase}}$ 含一个被研究的实际来源、$\alpha\in\{a_{\rm cal},-a_{\rm cal}\}$、$\beta\in\mathbb R$、$\nu>0$、固定 $q\in\mathbb T^2$、相应实际平移 PDE 轨迹 $u^q$、允许取得映射，以及解释全部档案所需的辅助量和联合误差。已有其它来源的记录和来源间关系亦由这一份世界的辅助量共同解释。初始标签域含零，$\theta_A:I_A\to[0,T_{12}]$、$\theta_C:I_C\to[0,T_{12}]$ 连续严格递增，$\theta_A(0)=\theta_C(0)=0$；更强已获钟限制仍属于允许钟对集合 $\mathcal C_{\mathcal X}$。钟的实际内部值是潜变量，除非已被取得。此处两钟可各自未知，不声明它们统计独立。

完整已获档案为
$$
H_{\rm phase}=(C,\mathcal A,D_0,D_A,D_C,J),\qquad
D_0=(\text{初始事件证书},A_0^{\rm obs}),
$$
$$
D_A=(s,A^{\rm obs}(s))_{s\in L_A},\qquad
D_C=(v,C^{\rm obs}(v))_{v\in L_C},\qquad L_A\subseteq I_A,\ L_C\subseteq I_C.
\tag{33.101}
$$
$C$ 保留每一项先前内部／外部记录、来源关系和参考；$\mathcal A$ 保留带来源索引的全部实际动作、校准、费用、延迟及取得历史；$J$ 保留全部已获跨端口配对、实际顺序、时间、来源及联合取得关系，包括第32节形式的已获顺序约束。$D_A,D_C$ 保留完整复值及本地标签，$L_A,L_C$ 在选候选世界之前固定。初始参考有误差仍是已获记录，不能被 $|A_0|=a_{\rm cal}/2$ 替换。

明确令 $\operatorname{Hist}_{\rm phase}(w,\mathcal A,D_0)$ 断言：每次所记动作由其声明来源在对应潜在内部时刻合法实施，满足所记费用、延迟和校准；读出的真实量就是该世界同一实际轨迹的指定 Fourier 积分；初始参考事件确为该准备的 $t=0$；取得无扰动，或有已认证的等价共同轨迹；每份分支证书在实际轨迹上成立。该谓词既不以模型预测伪造取得，也不把到达顺序当作未经认证的内部取得顺序。用 $\mathcal R_i,\mathcal J_\ell$ 分别解释所有旧记录与联合关系。对非退化任务置
$$
\mathcal B(w)=\beta(w)\chi_b(q(w)),\quad
p(w)=(m_+(w),k(w))=\left(\frac{|\beta(w)|}{\nu(w)},
 \frac{a_{\rm cal}^2}{\nu(w)^2}\right),\quad
\omega(w)=\frac{\mathcal B(w)}{|\mathcal B(w)|}.
\tag{33.102}
$$
给定实验先验 $P_{\mathcal X}\subset(0,\infty)^2$，完整可行交集为
$$
\begin{aligned}
\mathfrak F_H^{\rm phase}=\{w\in\Omega_{\mathcal X_{\rm phase}}:\;&
 \beta(w)\ne0,\quad p(w)\in P_{\mathcal X},\quad
 (\theta_A,\theta_C)\in\mathcal C_{\mathcal X},\\
&\operatorname{Hist}_{\rm phase}(w,\mathcal A,D_0),\quad
 \mathcal R_i(w,c_i)\ (\text{全部 }c_i\in C),\\
&\mathcal J_\ell(w,j_\ell)\ (\text{全部 }j_\ell\in J),\quad w\in\mathcal E_H,\\
&A_0^{\rm obs}=A_0(w)+\varepsilon_0(w),\\
&A^{\rm obs}(s)=A_w^{q(w)}(\theta_A(s))+\varepsilon_A(w,s)
 \quad(s\in L_A),\\
&C^{\rm obs}(v)=C_w^{q(w)}(\theta_C(v))+\varepsilon_C(w,v)
 \quad(v\in L_C)\},\qquad
\mathcal K_H^{\rm phase}=p(\mathfrak F_H^{\rm phase}).
\end{aligned}
\tag{33.103}
$$
$\mathcal E_H$ 是同一联合事件，含原始误差全部相关限制；其必要坐标界不替代它。任一重复出现的参考或读数指同一个误差变量。各条关系不得另选互不相容的世界。有限恢复另外要求 $J$ 确实含两个已获标签对 $(s_j,v_j)$ 的同源配对证书
$$
t_j(w):=\theta_A(s_j)=\theta_C(v_j),\qquad
0<t_1(w)<t_2(w)\le T_g,\qquad
r_j(w):=R_w(t_j(w))\in(0,r_*]\quad(j=1,2).
\tag{33.104}
$$
这是推论30.8的实际事件条件，不要求两事件之间 $\theta_A=\theta_C$。两个无关联流或同数值标签不提供该证书。理想射流定理则另要求取得零点附近任意小正水平的对齐初始图 germ；两个有限配对不自动提供这种理想数据。

所有归一化、实部和模都是 $H_{\rm phase}$ 的计算摘要，不能删除 $A_0^{\rm obs}$、原复数、虚部、来源、动作或联合时间顺序。沿用定义25.5及定义30.1的共同实现语义，数值摘要拟合不是完整世界见证。非空恢复须有 $w_*\in\mathfrak F_H^{\rm phase}$；空集上的成对不等式不产生参数、场或合法动作。

**定理 33.2（复三阶图射流的精确像及二阶不足）。** 在定义33.1的相干标架、已知 $a_{\rm cal}$、$\beta\ne0$ 下，假设已取得真实对齐初始图 $Z=\mathcal G(R)$ 的三阶射流。记
$$
M=\frac{\mathcal B}{\nu}\ne0,\qquad J_j=\partial_r^j\mathcal G(0).
$$
实际射流满足
$$
\mathcal G(0)=0,\quad J_1=M,\quad
J_2=-\frac{M(|M|^2+30)}{10},\quad
J_3=\frac M{100}(3|M|^4+95|M|^2+300-10k).
\tag{33.105}
$$
对给定 $M\ne0,J_2,J_3\in\mathbb C$ 及 $\mathcal G(0)=0$，其在这个非退化准备族中的有限射流相容性恰需第二阶等式与
$$
Q:=\frac{3|M|^4+95|M|^2+300}{10}-10\frac{J_3}{M}
 \in\mathbb R_{>0}.
\tag{33.106}
$$
逆为
$$
k=Q,\qquad \nu=\frac{a_{\rm cal}}{\sqrt Q},\qquad
\mathcal B=\nu M.
\tag{33.107}
$$
有额外参数先验时还须 $(|M|,Q)\in P_{\mathcal X}$。任一指定 $|A_0|=a_{\rm cal}/2$ 可同时实现。相反，在不另限死黏性的局部径向／黏性族中，前两阶不能识别黏性。

证明。恢复卷定理28.3给 $\mathcal G=\omega g_p$，其中 $m_+=|M|$、$\omega m_+=M$。直接将本卷定理28.3的真实图射流乘常值 $\omega$ 即得（33.105）。这是 $r$ 实变量的右导数，继承实联合 $C^5$，没有把曲线当作全纯函数。解第三式即得 $Q=k>0$，且 $J_3/M$ 必为实数。

反之，令 $\alpha=a_{\rm cal}$、$\nu=a_{\rm cal}/\sqrt Q$、$\beta=\nu|M|>0$。按恢复卷定理28.4的整数字符基，选择固定 $q$ 同时满足
$$
\chi_a(q)=2A_0/a_{\rm cal},\qquad \chi_b(q)=M/|M|.
\tag{33.108}
$$
两右端均为单位复数，故存在且模环面周期唯一；实际解存在且具有（33.105）指定的射流。这里只证明有限射流实现，不证明任意具有该射流的整条曲线来自 PDE，更不反造全部旧档案。若 $M=0$ 或 $Q$ 非正实数，不能使用该非退化逆或静默改正数据。

固定非零复数 $M$ 与已获 $A_0$，沿任意含两个不同正黏性的局部区间，令 $\mathcal B=\nu M$ 并使用（33.108）的同一 $q$，$\beta=\nu|M|$。这些真实准备的 $J_1,J_2$ 不变，而 $\nu$ 与 $k=a_{\rm cal}^2/\nu^2$ 改变，证明二阶不足。该射流任务的碰撞仅在两个完整世界也满足全部旧关系时才是完整档案碰撞；其它已获信息可以区分它们。$\square$

**定理 33.3（两实际复配对的径向参数与单位相位恢复）。** 固定正内点 $p_0=(m_{+,0},k_0)$。使用定理29.3的同一个闭凸参数球 $U=\overline B(p_0,\rho)\subset(0,\infty)^2$、逆常数 $K$，并以 $P_{\mathcal X}=U$ 限制定义33.1的完整候选。令 $m_{\min}=\min_U m_+>0$，按照恢复卷（28.112）缩小共同初始图域，使 $g'_p\ge m_{\min}/2$；再缩小共同 $\eta_0$ 以保留定理29.3及 $\eta_0\le\min\{1,r_*/3\}$。参数球在参数空间固定，不宣称原始输出含一个与 $\eta$ 无关的固定球。

设 $0<\eta\le\eta_0$，已校准初始参考和两份原始配对均精确，且（33.104）确实在 $r_1=\eta,r_2=2\eta$ 取得。记 $A_j=A^q(t_j),C_j=C^q(t_j)$、$Z_j=2iC_j/A_0$。若完整可行集非空，这些有限记录唯一确定其参数任务 $p,\nu,\mathcal B$ 及实际初始准备场，具体为
$$
\omega=\frac{Z_1}{|Z_1|},\qquad
(|Z_1|,|Z_2|)=(g_p(\eta),g_p(2\eta)),\qquad
\nu=\frac{a_{\rm cal}}{\sqrt k},\quad
\mathcal B=\frac{a_{\rm cal}m_+}{\sqrt k}\frac{Z_1}{|Z_1|}.
\tag{33.109}
$$
其两响应的精确任务像为
$$
\mathcal I_{\eta,U}
 =\{(\omega g_p(\eta),\omega g_p(2\eta)):
       p\in U,\ \omega\in\mathbb S^1\}.
\tag{33.110}
$$
一对数属于这个像，当且仅当 $Z_1\ne0$、$Z_2/Z_1\in\mathbb R_{>0}$，且两模属于同一实际标量像
$\{(g_p(\eta),g_p(2\eta)):p\in U\}$。只满足同射线条件不足。这个任务像不是整份档案的实现判据。

证明。两个实际同源配对分别处于同一内部时刻，故恢复卷（28.111）在两事件给 $Z_j=\omega g_p(j\eta)$。共同正下界使 $g_p(j\eta)\ge m_{\min}j\eta/2>0$，所以第一复值的单位方向就是 $\omega$，取模得到两份真实正代表值。将定理29.3（29.108）用于 $(\lambda,\mu)=(1,2)$，相同两标量值给相同预条件像，从而 $p$ 相同；恢复物理量得（33.109）。这是推论30.8的事件配对内容与解析两位置逆的合用，不把复数世界认作定义29.1的单钟世界。$A_0$ 再经恢复卷（28.113）给实际准备场；四重或固定有符号 $\alpha$ 时的两重标签仍依恢复卷定理28.4。

必要的像条件由正射线表示直接给出。反之，若模在实际标量像，取其 $p$，令 $\omega=Z_1/|Z_1|$；正实比保证第二数的方向也等于 $\omega$。再取 $\alpha=a_{\rm cal}$、$\beta=\nu m_+$ 以及同时实现 $\chi_a(q)=2A_0/a_{\rm cal},\chi_b(q)=\omega$ 的平移，得到这两个真正图响应。要使声明的标签、钟类、实际动作及所有旧记录同时实现，仍须（33.103）的完整见证；图像实现不替代它。

若只在精确参考与精确位置下给第一复响应误差 $|W_1-Z_1|\le\epsilon<|Z_1|$，则 $W_1\ne0$，并有
$$
\left|\frac{W_1}{|W_1|}-\frac{Z_1}{|Z_1|}\right|
 \le\frac{2\epsilon}{|Z_1|}
 \le\frac{4\epsilon}{m_{\min}\eta}.
\tag{33.111}
$$
确实，在中间插入 $W_1/|Z_1|$，第一差为
$\bigl||Z_1|-|W_1|\bigr|/|Z_1|$，第二差为 $|W_1-Z_1|/|Z_1|$，反三角界给结论。该单读数界不包办参考、位置和两份记录的联合误差。

单位复相位的识别在整个 $\mathbb S^1$ 有效，无需选连续实相位提升或推断绕行次数。结论只在 $U$ 内识别径向参数，不重建完整档案或未采样钟插值。两内部阈值的存在、时间界及条件外部期限直接使用定理29.5在同一正代表的条件；两个钟需分别实际覆盖所需事件，且配对接口可用。严格增加自身不供应取得期限、精确检测器或延迟保证。$\square$

**定理 33.4（同一参考的原始复误差运输）。** 使用定义33.1、定理33.3的同一正域 $U$ 和共同分支，且保留（33.104）的两个实际配对；现在原始参考及读数可有误差。置 $a_{\rm ref}=a_{\rm cal}/2=|A_0|$。在一份实际联合事件 $\mathcal E_H$ 上，对每份完整候选同时要求
$$
|A_0^{\rm obs}-A_0|\le e_0<a_{\rm ref},\qquad
|A_j^{\rm obs}-A_j|\le e_A,\quad
|C_j^{\rm obs}-C_j|\le e_C\quad(j=1,2),
\qquad e_0,e_A,e_C\ge0.
\tag{33.112}
$$
这里 $A_j,C_j$ 在每个 $j$ 内来自同一真实内部时刻，两个除法共用同一个 $A_0^{\rm obs}$。定义计算摘要
$$
V_j=1-\frac{A_j^{\rm obs}}{A_0^{\rm obs}},\qquad
r_{{\rm obs},j}=\operatorname{Re}V_j,\qquad
W_j=\frac{2iC_j^{\rm obs}}{A_0^{\rm obs}},\qquad
z_{{\rm obs},j}=|W_j|.
\tag{33.113}
$$
令 $L_g=\sup_{p\in U,\,0\le r\le r_*}|g'_p(r)|$，并取
$$
B_A=\max\{1,|1-r_*|\},\quad B_Z=L_gr_*,\qquad
e_r=\frac{e_A+B_Ae_0}{a_{\rm ref}-e_0},\quad
e_Z=\frac{2e_C+B_Ze_0}{a_{\rm ref}-e_0}.
\tag{33.114}
$$
则每份完整候选的真实 $r_j=R(t_j)$、$Z_j=\omega g_p(r_j)$ 满足
$$
|V_j-r_j|\le e_r,\quad
|r_{{\rm obs},j}-r_j|\le e_r,\quad
|\operatorname{Im}V_j|\le e_r,
$$
$$
|W_j-Z_j|\le e_Z,\qquad
\bigl||W_j|-g_p(r_j)\bigr|\le e_Z.
\tag{33.115}
$$
可将（33.114）两分母统一替换为实际非零的 $|A_0^{\rm obs}|$ 得到同样有效且不大的误差界。

证明。任何完整候选都有 $|A_0^{\rm obs}|\ge a_{\rm ref}-e_0>0$，所以计算摘要定义良好。精确除法恒等式为
$$
\frac{A_j^{\rm obs}}{A_0^{\rm obs}}-\frac{A_j}{A_0}
 =\frac{(A_j^{\rm obs}-A_j)
       -(A_j/A_0)(A_0^{\rm obs}-A_0)}{A_0^{\rm obs}}.
\tag{33.116}
$$
共同实际分支给 $A_j/A_0=1-r_j$、$|1-r_j|\le B_A$，故三角不等式得 $|V_j-r_j|\le e_r$。由于真实 $r_j$ 为实数，其实部与虚部界同时跟随，不能只保留实部而抛掉虚部约束。第二端口同样给
$$
W_j-Z_j
 =\frac{2i(C_j^{\rm obs}-C_j)-Z_j(A_0^{\rm obs}-A_0)}{A_0^{\rm obs}}.
\tag{33.117}
$$
由 $g_p(0)=0$、$|g'_p|\le L_g$ 以及 $0\le r_j\le r_*$，得
$|Z_j|=g_p(r_j)\le B_Z$，从而 $|W_j-Z_j|\le e_Z$。复模的反三角不等式及 $g_p(r_j)\ge0$ 得最后一界。保留精确分母即可得到所述改进。所有分支和范数包络须对同一完整候选域成立。

式（33.116）—（33.117）显示同一参考误差同时进入两个位置和两个复响应；投影后的误差一般相关。整个复数摘要 $V_j$（包括 $\operatorname{Im}V_j$）、$W_j$ 及对应原始复读数、参考与来源记录仍由（33.103）保留。仅各边缘误差事件有某概率，不证明这些界在同一联合事件上仍有该概率；若另给真实联合事件的概率保证，本定理只在该事件上作确定性运输，不添加独立性假设。$\square$

**定理 33.5（投影残差上的固定邻域比较）。** 在定理33.4下，进一步要求
$$
r_{{\rm obs},1}\in[3\eta/4,5\eta/4],\qquad
r_{{\rm obs},2}\in[7\eta/4,9\eta/4],\qquad
e_r\le\eta/8,\qquad 0<\eta\le\eta_0\le\min\{1,r_*/3\}.
\tag{33.118}
$$
置
$$
e=e_Z+L_ge_r,\qquad C_F=3+3L_g^2/10,\qquad
C_T=\sqrt{(4/3)^2+(64/7+4C_F/3)^2},
$$
$$
D_p=\min\left\{2\rho,\frac{4KC_T(e_Z+L_ge_r)}{\eta^3}\right\}.
\tag{33.119}
$$
每份完整候选满足 $|g_p(r_{{\rm obs},j})-z_{{\rm obs},j}|\le e$；任意两个完整候选的径向参数 $p,p'$ 满足 $\|p-p'\|_2\le D_p$。

证明。（33.115）与窗口使真实两位置分别落在
$[5\eta/8,11\eta/8]$、$[13\eta/8,19\eta/8]$，均处于共同图域。所需同源第一分支由（33.104）承担，不能由位置窗口替代。在同一个候选世界内沿图积分，
$$
|g_p(r_{{\rm obs},j})-z_{{\rm obs},j}|
 \le L_g|r_{{\rm obs},j}-r_j|+
       |g_p(r_j)-|W_j||\le e.
\tag{33.120}
$$
任意两候选在这两个固定观测位置的真实预测差各至多 $2e$。令
$\lambda=r_{{\rm obs},1}/\eta,\mu=r_{{\rm obs},2}/\eta$，它们属于定理29.3的设计域。将（29.107）的预条件算子作用于两组精确预测，其两坐标差记为 $\Delta A_{\rm pre},\Delta B_{\rm pre}$；这些符号不是原始 Fourier 端口。因 $|g_p(\lambda\eta)/(\lambda\eta)|\le L_g$，$F'(v)=-3-3v^2/10$ 的中值界给
$$
|\Delta A_{\rm pre}|\le\frac{2e}{\lambda\eta},\qquad
|\Delta B_{\rm pre}|\le2e\left[
\frac{2(1+\mu/\lambda)}{\mu(\mu-\lambda)\eta^3}
 +\frac{C_F}{\lambda\eta^2}\right].
\tag{33.121}
$$
这正是定理29.4（29.119）的解析残差计算。$\lambda\ge3/4,\mu\ge7/4,\mu-\lambda\ge1/2,\mu/\lambda\le3$，又 $\eta\le1$，故两坐标差的 Euclidean 范数至多 $2eC_T/\eta^3$。定理29.3（29.108）给参数差至多 $2K$ 倍该范数，球 $U$ 的直径又至多 $2\rho$，得到（33.119）。

此处与定理31.1同样，仅将真正复数世界投到必要标量残差，再使用定理29.3的解析比较；未把它们变成定义29.1的一钟、有符号实端口世界。反向提升不存在于本结论：任意两个模的拟合可以违反相位、$\operatorname{Im}V_j$、参考、旧档案或联合时间条件。只有 $w_*\in\mathfrak F_H^{\rm phase}$ 才给非空与真实参数；任一同样有完整世界见证的拟合相对它才享有所列误差界。$\square$

**定理 33.6（单位相位、物理参数及准备场的可行直径）。** 在定理33.5的全部同一候选域条件下，设共同正导数界为 $g'_p\ge m_{\min}/2$，定义
$$
h=\frac{m_{\min}}2(r_{{\rm obs},1}-e_r)
 \ge\frac{5m_{\min}\eta}{16}>0,\qquad
D_\omega=\min\{2,2e_Z/h\}.
\tag{33.122}
$$
任意两个完整可行世界 $w,w'$ 的单位复相位满足
$|\omega(w)-\omega(w')|\le D_\omega$，即使 $W_1=0$ 也成立。若另有 $e_Z<h$ 且完整可行集非空，则 $W_1\ne0$，点估计 $W_1/|W_1|$ 对每个可行单位相位的误差至多 $2e_Z/h$。

在同一闭凸 $U$ 上置
$$
k_{\min}=\min_Uk>0,\qquad M_m=\max_Um_+,\qquad
N=\frac{a_{\rm cal}}{\sqrt{k_{\min}}},\qquad
C_\nu=\frac{a_{\rm cal}}{2k_{\min}^{3/2}},
$$
$$
B_{\max}=NM_m,\qquad C_B=\sqrt{N^2+(M_mC_\nu)^2},\qquad
D_B=\min\{2B_{\max},C_BD_p+B_{\max}D_\omega\}.
\tag{33.123}
$$
则任意两个完整可行世界满足
$$
|\nu(w)-\nu(w')|\le C_\nu D_p,\qquad
|\mathcal B(w)-\mathcal B(w')|\le D_B,
$$
$$
\|u_{0,w}-u_{0,w'}\|_{L^2}
 \le\sqrt{8e_0^2+D_B^2}.
\tag{33.124}
$$
这些是完整可行集的任务直径，不是尚未证明的后续流误差界。

证明。写两世界的第一真实复响应为 $Z=\varrho\omega$、$Z'=\varrho'\omega'$。由真实位置下界及恢复卷（28.112）的正图估计，$\varrho,\varrho'\ge h$。单位复数的内积展开给精确恒等式
$$
|\varrho\omega-\varrho'\omega'|^2
 =(\varrho-\varrho')^2+\varrho\varrho'|\omega-\omega'|^2.
\tag{33.125}
$$
确实左侧等于 $\varrho^2+(\varrho')^2-2\varrho\varrho'\operatorname{Re}(\omega\overline{\omega'})$，而 $|\omega-\omega'|^2=2-2\operatorname{Re}(\omega\overline{\omega'})$。两个真实响应处于同一以 $W_1$ 为中心的 $e_Z$ 球，故距离至多 $2e_Z$。舍去非负径向平方并用 $\varrho\varrho'\ge h^2$ 得相位差至多 $2e_Z/h$，单位圆直径给上限二；没有除以 $W_1$。若 $e_Z<h$，任一完整候选给 $|W_1|\ge|Z|-e_Z\ge h-e_Z>0$，再用（33.111）的归一化三角证明得点估计误差。

物理黏性和径向幅度函数为 $\nu(p)=a_{\rm cal}k^{-1/2}$、$b(p)=|\mathcal B|=a_{\rm cal}m_+k^{-1/2}$。其梯度是
$$
\nabla\nu=\left(0,-\frac{a_{\rm cal}}{2k^{3/2}}\right),\qquad
\nabla b=\left(\frac{a_{\rm cal}}{\sqrt k},
 -\frac{a_{\rm cal}m_+}{2k^{3/2}}\right),
\tag{33.126}
$$
范数分别至多 $C_\nu,C_B$。在连接 $p,p'$ 的整条 $U$ 内线段上积分，给
$|\nu(p)-\nu(p')|\le C_\nu D_p$、$|b(p)-b(p')|\le C_BD_p$。再由
$$
|b\omega-b'\omega'|
 \le|b-b'|+b'|\omega-\omega'|
 \le C_BD_p+B_{\max}D_\omega,
$$
以及两幅度各至多 $B_{\max}$，得到 $D_B$。参考本身的误差不能省略：两份真实 $A_0$ 均在同一 $A_0^{\rm obs}$ 的 $e_0$ 球内，故 $|A_0(w)-A_0(w')|\le2e_0$。将此界与 $D_B$ 代入恢复卷定理28.5的精确两分量正交恒等式
$$
\|u_{0,w}-u_{0,w'}\|_2^2
 =2|A_0(w)-A_0(w')|^2+|\mathcal B(w)-\mathcal B(w')|^2
$$
即得（33.124）。即使径向参数精确，已获参考的不确定性仍贡献准备场误差。选一个点作为恢复场还须实际完整世界见证；在空可行集上不生成场，也不由单位相位点估计自动构造联合可行参数。$\square$

**命题 33.7（常值增益模型的两种相位碰撞与尺度边界）。** 下述各项是明确改变校准假设的精确模型，不属于定理33.4的已校准加性原始误差合同。每个碰撞均要求声明的完整旧档案及全部动作、来源、参考和联合时间约束容许两份构造世界。

若同一未知常值 $\gamma\in\mathbb C\setminus\{0\}$ 乘于 $A,C$ 及已获初始参考，且物理 $a_{\rm cal}$ 独立已知，则它从 $R,Z$ 抵消；在相应理想图或有限配对条件下，（33.107）或（33.109）仍识别 $\nu,\mathcal B$，但不识别物理 $A_0$ 相位。精确增益模型中只有模恒等式
$$
|\gamma|=\frac{2|A_0^{\rm obs}|}{a_{\rm cal}}.
\tag{33.127}
$$
若相对 $A$ 的 $C$ 校准另有未知单位因子，则 $\mathcal B$ 相位可以不可识别，而已知模的相对相位不影响黏性射流公式。若物理 $a_{\rm cal}$ 也没有独立固定且共用增益未知，则正的幅度／黏性／内部钟缩放歧义恢复。

证明。第一种模型的原始记录为 $\gamma A^q(t),\gamma C^q(t),\gamma A_0$，其共用非零因子从两归一化量直接消去。用恢复卷定理28.4的对角平移，作
$$
q\mapsto q+(s,s),\qquad \gamma\mapsto\gamma e^{-is}.
\tag{33.128}
$$
$A^q,C^q,A_0$ 都乘 $e^{is}$，所以完整的这些原始增益读数（包括初始参考）逐项不变；时钟和取得事件可保持。$s\notin2\pi\mathbb Z$ 时物理非零 $A_0$ 改变，但 $\mathcal B$ 不变。若基础档案只有这些读数和对称允许的准备、钟及动作证书，就给完整原始记录碰撞；其它已获相位校准或准备来源可以排除它。式（33.127）由取模给出，只属于无加性参考误差的精确增益模型。

第二种模型设 $C$ 另乘未知常值 $\zeta\in\mathbb S^1$，其余相对模校准已知。作
$$
q\mapsto q+(0,s),\qquad \zeta\mapsto\zeta e^{-is}.
\tag{33.129}
$$
$a$ 字符不变、$c,b$ 字符乘 $e^{is}$，故所有原始 $A,C$ 报告和已获参考保持，物理 $\mathcal B$ 乘 $e^{is}$。在同样完整见证条件下，$\mathcal B$ 相位未被切开。另一方面，图及其各实导数同乘 $\zeta$，所以观测 $|M|$ 与 $J_3/M$ 不变，黏性公式依然成立；若相对模是另一个已知正数，先除去它再用此论证。没有据此处理一般独立未知复增益。

最后直接复用命题28.6的实际缩放：对 $\lambda>0$，
$$
u^\lambda(t,X)=\lambda u(\lambda t,X),\quad
(\alpha,\beta,\nu)\mapsto(\lambda\alpha,\lambda\beta,\lambda\nu),\quad
\theta_A,\theta_C\mapsto\theta_A/\lambda,\theta_C/\lambda,
\quad \gamma\mapsto\gamma/\lambda.
\tag{33.130}
$$
两端口及其初始参考的物理值均乘 $\lambda$，共用增益抵消，所有所记本地标签和配对顺序可保持。两世界是否仍合法取决于原实验钟类、物理费用和全部旧记录；若它们都允许这次缩放就有绝对尺度碰撞。独立固定的 $a_{\rm cal}$ 只允许 $\lambda=1$，排除这条歧义。$\square$

**约定 33.8（退化域、成熟机制与任务边界）。** 有限记录的正向恢复及误差定理要求 $a_{\rm cal}>0,\beta\ne0,\nu>0$、固定平移、相干完整复校准、真实已获初始参考、同一来源的真实配对、共同初始正图域、指定局部先验及完整非空见证。$\beta=0$ 时 $Z\equiv0$，由命题28.6的剪切解没有可恢复射线，正径向逆不适用；$\alpha=0$ 使 $A_0=0$，除法无定义；$\nu=0$ 使初始 $r_t(0)=0$，正黏性图逆失效。迟时的 $Z=0$ 不提供该时刻的相位射线。未知共轭、改变 Fourier 方向、移动平移 $q(t)$、时变增益、未配对异步流、未获初始参考、不同准备或外力不满足同一个正向合同。

这里的仓内综合使用恢复卷全 PDE 唯一性、字符协变和准备场正交身份，把本卷第28节实际实图及第29节两位置逆接到完整复数世界。字符理论、复除法、单位向量归一化及有限维梯度估计是成熟机制；Fourier 正交来源见恢复卷定理28.2所引 Stein–Shakarchi，输出导数、有限样点及参数辨识的方法背景见本卷推论28.7及定理29.2所引 Sontag（2017、1984）。本节的图导数仅为实变量导数；常值复因子抵消不把实 $C^5$ 提升为全纯性，有限指数模态的谱运输也不供应非线性 PDE 的不变有限模态闭合。

准备场任务商只消除恢复卷定理28.4所证的场标签冗余，完整观察者仍含所有已获参考、来源关系、内部／外部档案和联合时间顺序。本节没有噪声射流预言器、逐样本实相位提升、绕行次数、全时间识别、后续轨迹扰动上界、自动取得器、无条件外部期限或普遍最优协议。一般独立未知增益及其另行的多记录恢复仍是不同问题；既有第32节顺序记录继续约束世界，但本节不另给复相位括区间定理。

## 33.99 追加锚

## 34. 完整档案上的有效未来管与含源多层消元

### 34.1 有效状态附着于全部已获档案

**定义 34.1（完整档案可行世界与共同视界）。** 令 $D$ 表示当前全部已获档案，包含已取得的内部／外部记录、来源身份及来源间关系、实际准备记录、初始参考、校准与误差合同、合法动作、联合时间顺序、时钟关系和费用。以 $\mathcal F(D)$ 表示与这整份档案及已声明先验同时相容的联合世界集合，要求 $\mathcal F(D)\ne\varnothing$，并明确以实际世界属于它为适用前提。未精确获知的量作为同一世界中的未知量受全部记录共同约束；不把“准备确已执行”偷换为“其隐藏坐标已精确测得”。空可行集表示记录或模型合同不相容，不作为零误差预测的证书。

一个世界 $\theta$ 同时指定模型参数、联合初态、观测误差、合法取得历史、共同来源、时间标记与资源合同。其可见量使用同一个有限维 Hilbert 空间 $U$ 和同一范数；若最初采用不同坐标，必须先给合法的有类型运输及其范数增益。隐藏空间可随模型指定，但每个模型都须满足[恢复卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)定义29.1的有限维、自伴、常系数自治方程。所有要比较的未来路径在一个共同视界 $I_T$ 上定义，$T\in(0,\infty]$，$T=\infty$ 指全部非负时间。

对每个 $\theta\in\mathcal F(D)$，记实际可见路径与静态路径为
$$
x_\theta(t),\qquad X_\theta(t)=e^{-tS_\theta}x_{0,\theta}.
$$
一个可用的恢复证书是有限非负函数 $E_\theta(t)$，连同其全部适用前提，满足
$$
\forall\theta\in\mathcal F(D)\ \forall t\in I_T,\qquad
\|x_\theta(t)-X_\theta(t)\|\le E_\theta(t).
\tag{34.1}
$$
例如可选择恢复卷定理29.4的速度与初始层界，或定理29.6的能量坐标界；半正定而无正隙时保留其式（29.9）的有限视界范围，图模型仅在命题29.9已证明的中心化域使用正隙。每份 $E_\theta$ 的 $a_0,c_0,b,V,r_0$ 或 $G,w_0,\gamma_0,N_0$ 都属于同一个 $\theta$，视界与实际准备也相同。存在有限数值不等于取得它；用于档案预测还要求有实际可认证的共同上界。

完整观察者仍由 $D$ 表示；有效状态只是附在 $D$ 上供指定任务调用的视图。本卷定义13.1、命题13.2及主卷§120、§138的已有区分继续适用：隐藏于当前投影的坐标可以已被旧参考或旁路记录约束，不能把短摘要中看不到当成完整观察者不知道。也不准将一个来源允许的 $h_0$ 与另一来源允许的 $S$ 自由拼成新世界。若 $\mathcal F(D)$ 来自统计置信域，需要另给覆盖真实世界的共同事件及其概率；本节的确定性条件结论不会生成一个置信水平。

### 34.2 同一世界的整条预测管与模型散布

**命题 34.2（从逐模型静态证书到档案预测）。** 在定义34.1下，每个固定世界的整条实际路径属于
$$
\mathcal T_\theta
=\{y:I_T\to U:\ \forall t\in I_T,
\ \|y(t)-X_\theta(t)\|\le E_\theta(t)\}.
\tag{34.2}
$$
因此实际候选路径族包含于 $\bigcup_{\theta\in\mathcal F(D)}\mathcal T_\theta$。若给定一条仅用合法可访问档案 $D$ 计算的共同预测路径 $p_D:I_T\to U$，则对每个 $t\in I_T$，
$$
\sup_{\theta\in\mathcal F(D)}\|x_\theta(t)-p_D(t)\|
\le\sup_{\theta\in\mathcal F(D)}
 \left[E_\theta(t)+\|X_\theta(t)-p_D(t)\|\right].
\tag{34.3}
$$
整段路径的版本为
$$
\sup_{\theta\in\mathcal F(D)}\|x_\theta-p_D\|_{\infty,I_T}
\le\sup_{\theta\in\mathcal F(D)}\sup_{t\in I_T}
 \left[E_\theta(t)+\|X_\theta(t)-p_D(t)\|\right]
\le E_D^T+M_D^T,
\tag{34.4}
$$
其中
$$
E_D^T=\sup_{\theta\in\mathcal F(D)}\sup_{t\in I_T}E_\theta(t),
\qquad
M_D^T=\sup_{\theta\in\mathcal F(D)}\|X_\theta-p_D\|_{\infty,I_T}.
$$
声称有限半径时须实际认证所用右侧有限；最后一个较松界要求 $E_D^T,M_D^T$ 均有限。若有限精度路径 $\widehat p_D$ 满足已认证的
$\|\widehat p_D-p_D\|_{\infty,I_T}\le\varepsilon_{\rm eval}$，则式（34.4）相应右侧再加 $\varepsilon_{\rm eval}$。

证明。式（34.1）的两个全称量词给每条固定世界路径的管包含。对固定的同一个 $\theta,t$，三角不等式给
$$
\|x_\theta(t)-p_D(t)\|
\le\|x_\theta(t)-X_\theta(t)\|
 +\|X_\theta(t)-p_D(t)\|
\le E_\theta(t)+\|X_\theta(t)-p_D(t)\|.
$$
取同一可行集上的上确界得到式（34.3），再对共同 $I_T$ 取上确界得到式（34.4）的第一步。每个世界的两项分别不超过 $E_D^T,M_D^T$，给最后一步；这一步是上界放宽，不声称两个最坏值能在同一世界同时取到。插入 $p_D$ 再用已认证计算误差得到有限精度项。$\square$

这里 $M_D^T$ 是围绕所选 $p_D$ 的静态模型散布，不能因某一模型的动态近似误差很小而删去。当 $S_\theta,x_{0,\theta}$ 尚随世界变化时，恢复卷最初供应的是一族整条路径管，不是一条已取得的统一预测。即使每时刻允许分别选择一个世界的点值，拼出的曲线也未必属于式（34.2）的任何固定世界管；$\bigcup_\theta\mathcal T_\theta$ 的含义是先选一个世界再约束所有时间，不把世界变成时间函数。交换数值上确界 $\sup_\theta\sup_t=\sup_t\sup_\theta$ 不改变这个实现量词，也不授权这种拼接。

若模型和可见初态已由完整档案确定，可选 $p_D=X$，从而 $M_D^T=0$；仍须计算和认证 $p_D$。一般情况下模型估计与可行集求界是额外任务，式（34.3）没有提供估计器、可行集非空性算法或最优预测中心。尺度族要得到单一路径预测的一致收敛，所选适用证书、模型散布及计算／解码误差的完整预算须在同一可行族上一致趋零。恢复卷推论29.8只供应其中的动态近似项。一份适用且完整趋零的预算已经足够；另一较松预算不趋零不证明实际不收敛。

### 34.3 终端任务、整路径任务与合法域

**推论 34.3（声明任务的误差运输）。** 在定义34.1及命题34.2的共同路径、有限误差预算和数值计算合同下，设共同合法状态域 $\mathcal A\subseteq U$ 包含所考察时刻的全部 $x_\theta(t),X_\theta(t)$，且同一终端读出 $f:\mathcal A\to(Y,d_Y)$ 满足
$$
d_Y(f(u),f(v))\le\ell\|u-v\|\quad(u,v\in\mathcal A),
\qquad 0\le\ell<\infty.
$$
则
$$
d_Y(f(x_\theta(t)),f(X_\theta(t)))\le\ell E_\theta(t).
\tag{34.5}
$$
若还用共同预测 $\widehat p_D(t)\in\mathcal A$，且其任务数值解码 $\widehat f_D(t)$ 满足
$d_Y(\widehat f_D(t),f(\widehat p_D(t)))\le\varepsilon_{\rm dec}(t)$，那么
$$
\sup_{\theta\in\mathcal F(D)}d_Y(f(x_\theta(t)),\widehat f_D(t))
\le\ell\left(
 \sup_{\theta\in\mathcal F(D)}[E_\theta(t)+\|X_\theta(t)-p_D(t)\|]
 +\varepsilon_{\rm eval}\right)+\varepsilon_{\rm dec}(t).
\tag{34.6}
$$
对于共同合法路径域 $\mathcal P\subseteq\{y:I_T\to U\}$，若同一整路径任务 $F:\mathcal P\to(Y,d_Y)$ 对路径上确界距离一致 $\ell$-Lipschitz，且全部待比较路径属于 $\mathcal P$，则式（34.5）–（34.6）分别使用 $\sup_{t\in I_T}E_\theta(t)$、式（34.4）的路径预算及相应整路径计算／解码界。

证明。合法域使每个读出均有定义。把式（34.1）代入 $f$ 的 Lipschitz 条件得到式（34.5）。对 $f(x_\theta(t)),\widehat f_D(t)$ 插入 $f(\widehat p_D(t))$，先用同一 Lipschitz 界，再用命题34.2及解码界，最后对共同世界集取上确界，即得式（34.6）。整路径版本把状态域和范数替换为已声明路径域和路径距离，逐项相同。$\square$

这是本卷第6节误差传播接口在这些指定读出上的应用。若继续接多元拼接或动作链，须使用该节的共同操作、合法混合输入、逐孔增益和实际可达域合同。状态范数小不直接控制任意不连续的自适应动作选择，也不保证换反馈、加干预后仍满足恢复卷的同一自治模型。概率律距离、全部允许实验的行为距离和包含外部量子参考的通道距离，需要各自的合同，不能由这里的实向量范数自动获得。

若把 $X_\theta$ 或 $\widehat p_D$ 宣称为概率状态，正锥和归一化条件须在其实际表示中另外证明。也可提供一个合法修正映射并认证实际修正量 $\varepsilon_{\rm legal}$，把它加入状态预算后再调用上面的读出界；域内性与该修正量都是前提，不能由范数接近自动得到。

### 34.4 精确行为闭合、相对钟与预测的含义

**约定 34.4（既有行为接口的时间重标应用）。** 对一份完整允许实现域 $\mathcal X$ 及半群 $T_t$，取实际像表示 $q:\mathcal X\to Z=q[\mathcal X]$。需要精确未来任务时，先指定常数 $\kappa>0$，并要求
$$
qT_{\kappa t}=\overline T_tq\quad(t\ge0),\qquad f=\overline f q.
\tag{34.7}
$$
这是主卷定理120.2、120.4、§138.1和本卷第2–3节已有行为闭合接口的应用；恢复卷第29节的近似界本身不建立式（34.7）。其存在性按原有核稳定判据检验：$qx=qy$ 必须蕴含 $qT_{\kappa t}x=qT_{\kappa t}y$。在实际像上按代表定义更新，便有唯一 $\overline T_t$；将 $T_{\kappa(t+s)}=T_{\kappa t}T_{\kappa s}$ 代入式（34.7）给继承的半群律。任务等式的应用为
$$
f(T_{\kappa t}x)=\overline f(\overline T_t(qx)).
$$
这里只因子化已声明任务；更大干预或拼接语言须重新查核稳定与合法性。

若第二个精确接口满足 $q_2\overline T_{\lambda t}=\widetilde T_tq_2$、$\lambda>0$，则直接复合得到
$$
(q_2q)T_{\kappa\lambda t}
=q_2\overline T_{\lambda t}q
=\widetilde T_t(q_2q).
\tag{34.8}
$$
所以常数时间因子相乘；原时钟视界 $T$ 对应第一有效钟视界 $T/\kappa$，再接第二层为 $T/(\kappa\lambda)$。参数、实际采样标签、联合先后和费用均须按同一钟关系运输，不能只重标生成元。

对于 $t=\phi(\tau)$ 的一般 $C^1$ 严格递增重参数化，要求 $\phi'>0$。通常应使用
$T^\phi(\tau_1,\tau_0)=T_{\phi(\tau_1)-\phi(\tau_0)}$，或时变生成元；例如恢复卷式（29.1）运输为 $dz/d\tau=-\phi'(\tau)Lz$。除非另有可验证的齐次结构，$T_{\phi(\tau)}$ 不继承以 $\tau$ 为参数的齐次半群律。本卷定理12.7的时钟与费用换元规则要求连续费率乘 $\phi'$、点操作费用只改标签，每次已取得样点运输为 $\phi^{-1}(t_j)$；在新钟上另行等步采样是另一个取得协议。该运输并不把时变方程重新变成恢复卷定理29.6的常系数前提。共同事件时间、各地已认证的相对钟和尺度指标因此分开声明；空间重标中的动态指数也须由具体模型提供。

预测若为随机任务，按本卷第9节使用同一个共同来源与固定合法策略 $\pi$ 的联合律：在其有限变量正支持合同下，预测充分性要求
$$
P^\pi(F\in\cdot\mid\mathcal H)
=P^\pi(F\in\cdot\mid q\mathcal H),
$$
其中 $\mathcal H$ 是该协议的完整已获历史。充分性只保留条件律，不把未实现的未来样本变为已获事实；逐模型、逐策略分别可选的恢复器也不能替代一个合法可调用的共同恢复器。

主卷定义138.6及本卷第13节已经给出确定性后处理边界。对完整档案映射 $\mathsf D$ 计算 $g(\mathsf D)$，有 $\ker(\mathsf D,g\mathsf D)=\ker\mathsf D$；只保留 $g\mathsf D$ 则可以合并更多旧区别。故有效结构能够使已有关系更易计算和认证，或降低声明的计算费用，却不能仅由后处理切开旧档案纤维，也不能取得未来样本。此处始终保留 $D$，不把任务视图当成观察者的全部状态。

### 34.5 同一初始源的多层精确运输

**接口 34.5（消元同时运输算子和右端）。** 固定同一联合线性方程
$$
\begin{pmatrix}\mathsf E&\mathsf F\\\mathsf G&\mathsf H\end{pmatrix}
\binom xy=\binom uv,
$$
其中 $x,u\in V$、$y,v\in K$ 为有限维空间中的向量，各块有相应类型，且 $\mathsf H:K\to K$ 有已给定的双侧逆。精确保留方程是
$$
(\mathsf E-\mathsf F\mathsf H^{-1}\mathsf G)x
=u-\mathsf F\mathsf H^{-1}v,\qquad
 y=\mathsf H^{-1}(v-\mathsf Gx).
\tag{34.9}
$$
其等价性由第二行解出 $y$ 后代入第一行得到；反向将所给 $y$ 代回两行即可。因而输出对象是一对“保留算子、保留源”，以及需要时的隐藏重建关系。源可以含初态、参考和输入，必须与算子来自同一个实际方程。

对恢复卷的 $L\succeq0,C\succ0$ 系统，主卷命题127.2已经供应完整 Laplace 方程。用 $\sigma>0$ 避免与状态或谱隙符号混淆，它为
$$
[\sigma I_U+A-B(\sigma I_H+C)^{-1}B^*]\widehat x(\sigma)
=x_0-B(\sigma I_H+C)^{-1}h_0.
\tag{34.10}
$$
该源保存同一联合初始对，且 $\sigma>0$ 使相关正定块的逆存在。$\sigma=0$ 的有效算子极限不同时提供无权状态积分及其逆；守恒分量仍须按恢复卷命题29.9处理。

多层时，将原空间写成 $V_0\oplus V_1\oplus V_2$，算子块记为 $A_{ij}:V_j\to V_i$，同一右端记为 $(u_0,u_1,u_2)$。若 $A_{22}$ 及
$H_1=A_{11}-A_{12}A_{22}^{-1}A_{21}$ 均有双侧逆，先消去第2块得到
$$
\widetilde A_{ij}=A_{ij}-A_{i2}A_{22}^{-1}A_{2j},\qquad
\widetilde u_i=u_i-A_{i2}A_{22}^{-1}u_2,\qquad i,j\in\{0,1\}.
$$
再消去第1块，右端必须为
$$
u_0^{\rm seq}
=u_0-A_{02}A_{22}^{-1}u_2
 -(A_{01}-A_{02}A_{22}^{-1}A_{21})H_1^{-1}
   (u_1-A_{12}A_{22}^{-1}u_2).
\tag{34.11}
$$
设共同隐藏块为
$\mathsf H_{12}=\begin{pmatrix}A_{11}&A_{12}\\A_{21}&A_{22}\end{pmatrix}$。
上述逆条件使它可逆：对任意右端 $(v_1,v_2)$，唯一解是
$$
y_1=H_1^{-1}(v_1-A_{12}A_{22}^{-1}v_2),\qquad
 y_2=A_{22}^{-1}(v_2-A_{21}y_1).
$$
两行代入验证存在性，逐行消去验证唯一性。因此一次消去同一隐藏块的源为
$$
u_0^{\rm joint}
=u_0-(A_{01}\ \ A_{02})\mathsf H_{12}^{-1}\binom{u_1}{u_2}.
\tag{34.12}
$$
把刚给出的 $y_1,y_2$ 用于 $(v_1,v_2)=(u_1,u_2)$，则
$A_{01}y_1+A_{02}y_2=A_{02}A_{22}^{-1}u_2+(A_{01}-A_{02}A_{22}^{-1}A_{21})H_1^{-1}(u_1-A_{12}A_{22}^{-1}u_2)$，从而式（34.11）与（34.12）相等。这个源运输核对不把保留算子的结合律重新宣称为新的一般结果。

保留算子的对应等式复用既有 [`SchurComplementAssociativity`](../../../D5/S3/Weil/ZetaLinear/SchurComplementAssociativity.lean) 的 `schur_complement_associativity`；它在复 Hilbert 有界算子上明确假定末块及约化块的左逆见证、联合隐藏块的右逆见证。它不证明这些逆存在，也没有右端源作为结论。本节有限维双侧逆条件是一份足够合同；在实矩阵情形可复化到该算子恒等式再限制回实空间。更多层对式（34.9）的算子和源同时迭代，每一步都须检查逆及共同初值，不能只运输左端。

[《量子实在》](QUANTUM-REALITY.md)推论14.1在固定频率 $K-z^2M$ 下应用同一精确算子结合律，定理14.2还保留隐藏初始坐标／动量的齐次源与振荡记忆；它的二阶模型并不满足恢复卷第29节的一阶耗散合同。该卷§341的三步回声显示零阶记忆截断会丢失第三步返回，§342.1保留全部记忆系数与同一预解算子的初始源；这要求为选定截断另给视界和误差，不是否定所有有限记忆近似。

### 34.6 共同因子、近似层与独立资源坐标

**约定 34.6（多层近似的进入条件）。** 主卷命题124.24及§124.10.2–124.10.3供应共同变量消元的顺序条件：必须先纳入所有依赖共享接口的因子，再消去该变量；共享先验只计一次。一个局部外露接口可以成为整体内部变量，但它的共同来源不能被分别边缘化后以独立副本替代。对于正定联合 Gaussian 模型，主卷命题130.8（§130.7）、命题130.9（§130.8）及§130.9分别保留 Schur 二次型、Gaussian 行列式因子与坐标 Jacobian。逐层与一次积分比较使用同一个参考测度；行列式乘积的一致性来自同一个块行列式分解，不能只比较指数二次型。退化平坦方向或负方向须按该卷§130.8.1重新查积分存在性，不能沿用正定全空间积分公式。

精确动态消去中间层通常留下记忆与初始源，所以中间对象不自动又是一个符合恢复卷定义29.1的常系数一阶自伴块系统。要在每层调用其静态近似界，必须逐层给出真实模型、实际初始化、适用视界、谱隙／速度或能量证书，并证明层间运输在共同合法域上的增益；另一条允许路线是先对共同隐藏空间精确联合消元，再认证一次近似。已有本卷第6节的组合预算在其合法性与增益条件下使用，每层误差沿后继路径乘增益后相加。精确消元的顺序相容性不证明提前静态化、截断或近似后的顺序相容性，也不授权删除某层的初始源。

一份可执行预测同时保留各自有单位的资源坐标：实际初态准备及重复准备、参数与谱隙认证、记录取得及校准、时钟同步与标签运输、完整档案存储及有效状态工作存储、矩阵指数／卷积等数值计算、证书与解码精度及验证费用。依据本卷第7节和定义12.8，可以在同一已声明执行路径上逐坐标核算累计费用；没有给换算关系时，不将这些坐标压成一个无依据的标量。$h_0=-C^{-1}B^*x_0$ 的制备费用、$V$ 或 $\gamma_0$ 的认证费用、$p_D$ 的取得与有限精度误差均由实际协议承担。记忆状态维数变小不等于可以删除全部已获档案，也不等于已提供外部期限内的算法。

### 34.7 跨尺度未来接口的开放边界

**约定 34.7（本桥梁的适用边界）。** 这里将有限自伴隐藏关系、完整初始准备、静态生成元误差和完整档案上的指定未来任务接在同一来源上；动力学估计归恢复卷第29节，行为闭合、随机预测充分性和一般组合方法仍取各自既有合同。一般合法干预及改反馈后的稳定性、物理重整化中特定重标／截断与动态指数、含记忆中间层的受控多层近似，以及档案一致的不确定模型估计，仍需各自的模型和证明，不属于本节结论。预测律也不推出已取得的未来事实；既有相位／初始参考关系及独立增益恢复问题保持各自范围。

## 34.99 追加锚

## 35. 完整档案上的概率修复、准备域与联合过程合同

### 35.1 一份完整档案与一份共同实现关系

**定义 35.1（概率任务的完整档案可行族）。** 沿用定义13.1、命题13.2、定义13.3、约定15.1和定义34.1的完整已获记录语义，用 $C_{\rm acq}$ 表示整份实际已获档案，以区别于[恢复卷定义30.1](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)的隐藏算子 $C$ 与容量矩阵 $D$。$C_{\rm acq}$ 同时保留全部已取得的内部／外部记录、来源身份及共同来源关系、实际准备与初始参考、校准和误差合同、可访问控制、合法动作及失败信息、外部参考关系、各局部钟及联合取得顺序。记录中未知的模型参数或隐藏准备由全体旧约束共同限制，不因当前任务摘要未显示而被删除。

固定完整实现类 $\Omega$ 及档案相容关系 $\mathscr R_{\rm acq}$，定义
$$
\mathcal F(C_{\rm acq})
=\{\theta\in\Omega:(\theta,C_{\rm acq})\in\mathscr R_{\rm acq}\},\qquad
\mathcal F(C_{\rm acq})\ne\varnothing,\qquad
\theta_{\rm act}\in\mathcal F(C_{\rm acq}).
\tag{35.1}
$$
非空性须由一份满足全部关系的实际可行实现见证支持；仅满足若干残差不等式的数值向量不是见证。$\theta_{\rm act}$ 的成员资格是预测用于真实世界的前提，找到另一个相容见证并不自动证明它。若合同来自统计置信域，真实世界成员资格须落实于已声明的共同覆盖事件；以下确定性蕴含不生成一个新的置信水平。

在本节的图分支，每个 $\theta$ 同时给出一个有限连通对称加权图 $L_\theta$、同次初始概率 $p_{0,\theta}$、其合法准备历史、共同来源及误差实现，以及所用未来协议。比较时共同固定 $V,R,D,N_v$ 和时间视界 $I_T$，$T\in(0,\infty]$；若采用不同时间坐标，先按第12节运输同一事件、时钟与误差合同。令
$$
p_\theta(t)=e^{-tL_\theta}p_{0,\theta},\qquad
x_\theta(t)=Pp_\theta(t),\qquad
X_\theta(t)=e^{-tS_\theta}Pp_{0,\theta},
$$
$$
b_\theta(t)=R^{\mathsf T}p_\theta(t)\in\Delta_m,\qquad
\widehat b_\theta(t)=R^{\mathsf T}X_\theta(t),\qquad
\mathbf1^{\mathsf T}\widehat b_\theta(t)=1.
\tag{35.2}
$$
初态若是条件概率，就必须在同一整份档案与同一联合模型下条件化，并仍满足所声明的后续热演化合同。每个 $\theta$ 供应的是由自己的一份联合准备和模型产生的整条路径。路径上的每个时刻不得重新选一个世界，也不能把一个世界的 $S$ 与另一个世界的 $h_0$ 拼成初值问题。

记录的共同来源、概率独立性与动作次序是不同条件。本卷第5节的共享变量、第13节的合法割及第15节的联合仪器分别承担这些关系；两个动作可换序并不推出读数独立。有符号中间预测与修复输出都只是附着于 $C_{\rm acq}$ 的任务视图 $g(C_{\rm acq})$，不替代实际档案。本卷命题15.8已经给出当前预测态相同、已获来源信息却不同的反例。

### 35.2 保留模型散布的同世界概率管

**约定 35.2（已有轨迹证书在质量空间的实例化）。** 对定义35.1的每个固定 $\theta$，使用恢复卷第29节一份满足全部前提的证书
$$
\|x_\theta(t)-X_\theta(t)\|_2\le E^{(2)}_\theta(t)\qquad(t\in I_T).
$$
图的正隙按该卷命题29.9仅用于共同守恒分量之外；准备失配、速度或能量坐标参数均来自同一个 $\theta$。恢复卷命题30.9运输为两种可用质量证书
$$
E^{(D^{-1})}_\theta(t)=E^{(2)}_\theta(t),\qquad
E^{(1)}_\theta(t)=\sqrt{N_v}\,E^{(2)}_\theta(t),\qquad
\|b_\theta(t)-\widehat b_\theta(t)\|_\nu\le E^{(\nu)}_\theta(t),
\tag{35.3}
$$
其中 $\nu=1$ 或 $D^{-1}$。也可使用一份直接取得、更紧而满足相同适用前提的 $\ell_1$ 证书。

固定一条仅由合法可访问 $C_{\rm acq}$ 计算的质量一预测路径 $\widehat b_0:I_T\to\mathbb R^m$。命题34.2在上述质量范数中的实例化首先给修复前的界
$$
\|b_\theta(t)-\widehat b_0(t)\|_\nu
\le E^{(\nu)}_\theta(t)+\|\widehat b_\theta(t)-\widehat b_0(t)\|_\nu.
\tag{35.4}
$$
右侧第二项是围绕所选预测的模型散布，不因第一项小而删除。以同一可行关系和同一视界定义
$$
B_\nu^T
=\sup_{\theta\in\mathcal F(C_{\rm acq})}\sup_{t\in I_T}
\left[E^{(\nu)}_\theta(t)+\|\widehat b_\theta(t)-\widehat b_0(t)\|_\nu\right],
$$
$$
E_\nu^T=\sup_{\theta\in\mathcal F(C_{\rm acq})}\sup_{t\in I_T}E^{(\nu)}_\theta(t),\qquad
M_\nu^T=\sup_{\theta\in\mathcal F(C_{\rm acq})}\|\widehat b_\theta-\widehat b_0\|_{\nu,\infty,I_T},\qquad
B_\nu^T\le E_\nu^T+M_\nu^T.
\tag{35.5}
$$
声称有限半径时，须取得这些表达式中实际使用的有限共同上界。最后一步是上界放宽，不声称误差极值与模型散布极值能在同一个世界同时达到。模型和可见初态由完整档案确定且 $\widehat b_0=\widehat b_\theta$ 时，模型散布为零；仍需履行预测的计算与访问合同。

对 $\mathcal Q\in\{\mathcal R_+,\Pi_D\}$，恢复卷命题30.7–30.8对每个固定真值 $b_\theta(t)\in\Delta_m$ 给
$$
\|b_\theta(t)-\mathcal Q\widehat b_0(t)\|_1
\le\|b_\theta(t)-\widehat b_0(t)\|_1.
$$
因此式（35.4）–（35.5）直接成为整条修复预测的界
$$
\sup_{\theta\in\mathcal F(C_{\rm acq})}\|b_\theta-\mathcal Q\widehat b_0\|_{1,\infty,I_T}
\le B_1^T,\qquad
\sup_{\theta,t}\operatorname{TV}\bigl(b_\theta(t),\mathcal Q\widehat b_0(t)\bigr)
\le\min\{1,B_1^T/2\}.
\tag{35.6}
$$
这里保留原来的 $\ell_1$ 半径，没有 $2B_1^T$ 的修复损失，也没有使用任意两份有符号输入之间的 $\ell_1$ 非扩张。若选 $\Pi_D$，该卷命题30.8–30.9还给
$$
\sup_{\theta\in\mathcal F(C_{\rm acq})}\|b_\theta-\Pi_D\widehat b_0\|_{D^{-1},\infty,I_T}
\le B_{D^{-1}}^T,\qquad
\sup_{\theta,t}\operatorname{TV}(b_\theta(t),\Pi_D\widehat b_0(t))
\le\min\{1,\sqrt{N_v}B_{D^{-1}}^T/2\}.
\tag{35.7}
$$
这要求一份公共 $D$；$\mathcal R_+$ 不继承加权 Hilbert 非扩张。式（35.6）–（35.7）的证明内容分别由既有命题34.2的三角界和恢复卷的修复／度量定理承担，不另作动力学估计。

同世界整路径的逻辑仍是
$$
\{b_\theta:\theta\in\mathcal F(C_{\rm acq})\}
\subseteq\bigcup_{\theta\in\mathcal F(C_{\rm acq})}
\{y:\forall t\in I_T, \|y(t)-\widehat b_\theta(t)\|_\nu\le E^{(\nu)}_\theta(t)\}.
\tag{35.8}
$$
右侧先固定一个世界再控制所有时间；不能将它改成任意逐时选择的候选边缘乘积。对一条已经合法定义的 $\widehat b_0$ 逐时修复可给统一路径误差，即使修复映射不满足半群律；这种函数误差也不等于两个随机过程的联合路径律距离。

**约定 35.3（有限计算、可行性与实际效果）。** 若计算输出 $\widetilde b_0$ 已认证质量一，且
$$
\|\widetilde b_0-\widehat b_0\|_{\nu,\infty,I_T}\le\varepsilon_{{\rm eval},\nu},\qquad
\widetilde z(t)\in\Delta_m,\qquad
\|\widetilde z-\mathcal Q\widetilde b_0\|_{\nu,\infty,I_T}\le\varepsilon_{{\rm rep},\nu},
\tag{35.9}
$$
则在 $\nu=1$、两种修复的情况下，或在 $\nu=D^{-1}$、$\mathcal Q=\Pi_D$ 的情况下，式（35.6）或式（35.7）的范数半径替换为
$$
A_\nu^T=B_\nu^T+\varepsilon_{{\rm eval},\nu}+\varepsilon_{{\rm rep},\nu}.
\tag{35.10}
$$
这是先在式（35.4）插入 $\widetilde b_0$、再应用相对真值的修复界、最后加入实际修复残差的同一三角界。没有要求两份有符号预测的修复结果互相收缩。质量一若因浮点误差尚未认证，须先给恢复质量一的实际操作及其误差，再进入式（35.9）；不能把带质量缺口的向量直接放入仅适用于质量一的阈值和尖锐界。

对实际概率效果 $0\le f_i\le1$，恢复卷式（30.20）给修复概率和真值的效果差至多 $\min\{1,A_1^T/2\}$；使用加权证书时为 $\min\{1,\sqrt{N_v}A_{D^{-1}}^T/2\}$。若最后输出的标量 $\widetilde v(t)$ 还满足
$|\widetilde v(t)-f^{\mathsf T}\widetilde z(t)|\le\varepsilon_{\rm dec}(t)$，则再加这一实际解码误差。投影残差小不自动证明 $\widetilde z\in\Delta_m$，一份可行数值也不自动证明可行族非空或真实世界成员资格。所有这些数值证书须可由声明权限实际取得；存在一个上确界不提供求解算法、准备手段或无条件外部截止。

### 35.3 预测、准备与可复用接口的三种输出

**定义 35.4（概率边界的三种使用合同）。** 对定义35.1的同一档案与共同来源，区分以下三种结论。

1. 概率值预测：输出 $z_C(t)\in\Delta_m$，并有同世界、同视界的概率或效果误差证书。式（35.6）–（35.10）供应这一结论；它不要求把预测向量实际制备出来。
2. 可执行准备：在已声明的准备关系 $\mathscr P_{C_{\rm acq}}$ 中给出合法操作及其实际结果，满足微观概率／态、参考关系、来源及费用条件。要求极小提升时，必须另外有 $J_\theta z_C(t)\ge0$、$R^{\mathsf T}J_\theta z_C(t)=z_C(t)$，并满足同一档案对该准备的全部限制。恢复卷式（30.13）给四点例的精确域，命题30.6给静态生成元合法而极小准备非法的严格正反例。若 $\theta$ 未确定，实际准备必须由一份基于可访问档案的共同协议实现，不能为不可区分世界暗选不同控制。全域正保参考极小提升的强要求按该卷推论30.5等价于 $B=0$；受限族的合法性可以更弱。
3. 可复用动态接口：除合法状态及准备外，还给定全体允许后续实验的同一联合路径律、干预规则、共同来源、参考／控制器关系、每步实际域以及统一缺陷和费用合同。精确替换须在实际像上运输所有相关操作与读出；近似替换须满足本卷第3–6节、第12节的合法混合链或有类型逐步误差条件。若采用 Markov 接口，还须验证其转移核及组合律；若采用有记忆接口，则保留其记忆、完整历史及相应顺序生成合同。

这三项没有从第一项自动到后两项的蕴含。恢复卷命题30.3将能量正性与实际概率正性分开，命题30.6将静态概率生成元与极小准备分开，命题30.10又在同一个 $T,t_*$ 上分别否定 $\mathcal R_+$ 与 $\Pi_D$ 修复的半群律。故修复后的每时刻概率，不能直接充当满足原过程干预规则的随机更新核。该反例没有否定一切有记忆联合过程的存在；任选一个独立乘积耦合也没有证明恢复了任务实际联合历史。

这里的精确像正性仍取定理15.3、命题15.7：若 $q$ 把实际正锥 $\mathcal C$ 送到 $q(\mathcal C)$，且 $qT=\overline Tq$ 真正成立，则每个 $q(c)$ 被送到 $q(Tc)\in q(\mathcal C)$。实际概率质量坐标 $R^{\mathsf T}p$ 的像是整个 $\Delta_m$，因为每个粗概率均有自然提升 $RD^{-1}b$。恢复卷的四点静态预测离开这个实际像，所以它没有满足该精确下降前提，并非定理15.3的反例。对带符号的可逆表示 $E$，状态锥应运输为 $E(\mathcal C)$，效果同时运输为 $f\circ E^{-1}$；只看坐标符号不能改变合法性。

一个紧凑的联合表提醒是
$$
W=\begin{pmatrix}-1/4&3/4\\3/4&-1/4\end{pmatrix}.
$$
四格和一，两种边缘均为 $(1/2,1/2)$，但联合表仍有负格。上述事实只需逐行逐列求和，不提供这个有符号表的实际正联合实现。一般有符号切片甚至可以总质量零而各格非零，例如 $(1,-1)$，不能据此作条件除法。概率值边缘、正联合实现与合法条件化分别需要各自的域条件。

### 35.4 量子逆表示、参考与实际取得

**约定 35.5（有符号逆的任务及记录边界）。** 恢复卷定义30.11、定理30.12固定已知 $0<\lambda\le1$、全部 qubit CPTP 单位价格字典、有限实系数和一份共同线性恢复，得到确切表示成本 $\lambda^{-1}$ 及负系数质量 $(\lambda^{-1}-1)/2$；其显式对偶 $\ell(\Phi)=\operatorname{Tr}[X\Phi(\rho_+)]$ 对整个字典有效。应用时必须保留这些量词。整个实际输出椭球上的同一线性恢复与全 Hermitian 任务等价，已由该定理后的仿射内部论证承担；一份已知准备态或仅对角任务可以成本一。

若允许惰性参考 $R_{\rm ref}$，状态须是声明域中的联合态，效果须是同一合法联合实验的 $0\preceq F\preceq I$；采用 $[-1,1]$ 读数时则指定相应有界可观测量。全线性等式可以张量恒等运输：
$$
(\mathcal D_\lambda^{-1}\otimes\operatorname{id}_{R_{\rm ref}})
(\mathcal D_\lambda\otimes\operatorname{id}_{R_{\rm ref}})(\rho_{SR_{\rm ref}})
=\rho_{SR_{\rm ref}}.
\tag{35.11}
$$
这条代数等式在实际正像上恢复合法联合态，但没有把 $\lambda<1$ 时的逆变成全域 CPTP 操作。实际有符号估计使用恢复卷命题30.13的非负调用概率 $|a_j|/\Gamma$ 与带符号权重，必须能够执行各原子、取得指定输入和效果的真实样本，并保留制备与参考访问条件。其 $\Gamma^2$ 二阶矩上界只属于这一协议，不是普遍样本或方差下界。未知参数、变价格、受限字典及适应性任务不能从这个代价公式跳过校准或新任务论证。

量子分支的 $\theta$ 是由本卷第11–12节的共同联合态、仪器、活动记忆、参考及实际控制历史定义的合法实验实现。它不为互不相容的所有反事实测试同时指定经典取值。已执行实验的旗标与记录仍属于 $C_{\rm acq}$，成功后的条件化只在有正概率及所需共同下界时使用；失败信息不得删去。[量子实在卷定理222.1–222.2](QUANTUM-REALITY.md)已经区分相同约化相位阻尼、不同环境实现和不同可读记录。恢复约化线性映射不确定观察者实际已取得哪些环境知识，也不恢复被摘要丢弃的来源档案；访问这些记录须另给其共同实现与合法操作。

形式逆 $\mathcal D_{-t}$ 与其有符号系数在此只服务于指定恢复或估计任务，不给逆向因果推断。由旧档案计算新的预测视图也不是取得未来样本。本节把有限隐藏关系、实际概率域和可执行／可组合使用条件接回第34节，适用范围不包含由尺度消元推出物理负时间、负能量或所有反事实的共同经典概率空间。

## 35.99 追加锚

## 36. 编码的离散限制、完成接口与完整已获观察者

本节接回[恢复卷§31](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)的全 $k$ 共同生成器。定量矩阵、两种精确容量、一步计数收缩、短窗口误差、全加指数和换码障碍均由该节一次证明；这里说明它们在同一实际来源、相容读数和合法获取历史中何时可使用。第35节保留实际正域与可操作性的独立职责。本节继续关系空间、时序、边界和记忆相互恢复的研究，不把一种编码模型当成全计划的终点。

### 36.1 三种限制箭头及其相容数据

**定义 36.1（词、概率与完整量子输出的三层接口）。** 对每个固定有限 $k\ge2$，沿用恢复卷定义31.1、命题31.3和31.11的 $X_k,\mathcal W_n^{(k)},\lambda_k,\mu_k,H_n,\rho_{k,n}$，其中 $X_k$ 为全部不含 $1^k$ 的单侧无限二元串，坐标从零开始。令 $q_n:X_k\to\mathcal W_n^{(k)}$ 取最先 $n$ 位，$q_0$ 为空词。三种限制分别为
$$
\begin{aligned}
b_n &: \mathcal W_{n+1}^{(k)}\to\mathcal W_n^{(k)},&&b_n(wa)=w,\\
\mathsf m_n &: \operatorname{Prob}(\mathcal W_{n+1}^{(k)})\to\operatorname{Prob}(\mathcal W_n^{(k)}),&&
(\mathsf m_n p)(w)=\sum_{a:\,wa\text{ 合法}}p(wa),\\
\mathsf t_n &: \mathcal D(H_{n+1})\to\mathcal D(H_n),&&\mathsf t_n(\rho)=\operatorname{Tr}_{B_{n+1}}\rho.
\end{aligned}
\tag{36.1}
$$
$\mathcal D(H)$ 表示完整 $H$ 上的密度矩阵。量子层保留全部 $2^n$ 个基标签；本族仅在非法词的行列为零。一般密度的计算基对角先落到全部二元词的概率单纯形，只有支撑于合法词时才落到式（36.1）的合法词概率层。记此对角操作为 $\mathsf d_n$，则在相应支撑域上
$$
b_nq_{n+1}=q_n,\qquad
\mathsf m_n\mu_{k,n+1}=\mu_{k,n},\qquad
\mathsf t_n\rho_{k,n+1}=\rho_{k,n},\qquad
\mathsf d_n\mathsf t_n=\mathsf m_n\mathsf d_{n+1},\qquad
\mathsf d_n\rho_{k,n}=\mu_{k,n}.
\tag{36.2}
$$
这里 $\mu_{k,n}(w)=\mu_k[w]$。第一式来自删除前缀末位；概率及量子式的全矩阵证明在恢复卷命题31.3，含非法前缀与 $n=0$。这组方块没有把三种对象认成同一个类型。特别是相容密度族是已发出前缀的约化族，不是把每一步正在演化的活动记忆也当成不变的逆系统坐标。

词空间与这些额外结构的供应关系有确定归属。[主卷§132.3.3](RECURSIVE_RELATIONAL_OBSERVATION.md)已给全 $k$ 合法串的逐位共同实现；[Q123.3、命题124.2和124.13](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)分别负责有限支持缺失线程、$k=2$ 前缀拓扑／稠密性和实际像加层间相容的区别。Q125.1–125.5拥有 $k=2$ 全输出态与完成代数，Q130.1拥有二维共同记忆及纯顺序最小性。这里使用恢复卷的全阶扩展，不重复这些通用与 $k=2$ 证明。

**应用 36.2（指定前缀距离下的完成识别）。** 令 $X_{k,\rm fs}\subset X_k$ 为最终全零的合法串，$J(x)=(q_nx)_{n\ge0}$。对 $x\ne y$ 置
$$
p(x,y)=2^{-\min\{j\ge0:x_j\ne y_j\}},\qquad p(x,x)=0.
\tag{36.3}
$$
在主卷§132.3.3的既有识别 $X_k\cong\varprojlim\mathcal W_n^{(k)}$ 下，前缀读数联合分离且每个相容线程具有同一个实现：线程的第 $j$ 位取自长度 $j+1$ 的前缀，相容性保证更长层不改它；若所得串含 $1^k$，某个有限前缀就不合法。反过来每个合法串给这一线程。因此可直接使用 [InverseLimitCompletion.stateThread_bijective_iff_complete_and_separates](../../../D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean)；[LocalGlobalAtlasExactness.local_global_atlas_exactness](../../../D5/S3/ConceptDynamics/RefinementGeometry/LocalGlobalAtlasExactness.lean)把同一条件写成核为对角、线程像为全部。这两条是 Type 层的分离／共同实现判据，本身没有拓扑完成的结论。

拓扑部分需保留距离刻度。[主卷定义91.1、式（91.2）](RECURSIVE_RELATIONAL_OBSERVATION.md)按首个不同的“层”定义线程距离，而 $q_0$ 恒为空，故首个不同位为 $j$ 时首个不同层为 $j+1$。精确地，
$$
d_{91}(Jx,Jy)=\tfrac12p(x,y),\qquad
\widetilde d:=2d_{91}\quad\Longrightarrow\quad
\widetilde d(Jx,Jy)=p(x,y).
\tag{36.4}
$$
相等串两边均零。若未重标号或乘二，只能说同拓扑及比例相似，不能称按式（36.3）等距。主卷定义91.1已经给出观察商的完成为 $\overline{J[X]}$；等于整个逆极限还需要此像稠密。这里每个合法有限词补零仍合法，故所有有限实际像都等于 $\mathcal W_n^{(k)}$。Q124.13的有限实际像稠密判据可直接使用：线程的基本邻域只约束有限多层，选择最大受限层的实际代表便同时满足较小层。于是 $J[X_{k,\rm fs}]$ 稠密，按重标距离 $\widetilde d$ 的完成正好为 $(X_k,p)$。

同一个结论也可用截断 $\tau_Nx$ 验证所需稠密性：保留前 $N$ 位后补零不制造禁词，且 $p(\tau_Nx,x)\le2^{-N}$。全部合法串在二元乘积中闭，因此在此首差距离下紧且完备；这使用 Q124.2的既有前缀构造，把禁词从 $11$ 换成 $1^k$。有限支持域自身缺共同实现：Q123.3的交替串 $1010\ldots$ 对所有 $k\ge2$ 均合法，每个有限前缀可补零实现，却无同一个最终全零的串实现全部层。此例说明“每层有实际代表且相互相容”与“有原类型中的共同代表”仍不同；各层分别有代表而不相容，连线程也不是。

离散前缀和完成对象可据此称为同一关系的有限限制与相容整体，或一个声明清楚的体／边界接口。对有限观察 $q_N$，其纤维通常仍有许多整体，不能从一个有限边界凭空恢复全部层；对全层族，唯一性和存在性刚好是上述两项条件。这一识别不赋予任何概率。根 Perron 柱律是额外的相容权重；恢复卷的 Gram 数据和等距又是相干结构的额外选择。完成字符串本身既不产生 Born 规则，也不选定实际发生的历史。

### 36.2 允许操作的精度运输与实际读数

**接口 36.3（换精度的后续操作合同）。** 若要在上述表示上实现实际操作 $T:X_k\to X_k$，允许声明非负整数函数 $m(n)$ 及有限映射
$$
\overline T_n:\mathcal W_{m(n)}^{(k)}\to\mathcal W_n^{(k)},\qquad
q_nT=\overline T_nq_{m(n)}\quad(n\ge0).
\tag{36.5}
$$
该式要求每个 $q_{m(n)}$ 纤维中的状态在操作后有相同 $n$ 位输出；若成立，$\overline T_n$ 在全部实际像上良定。反之这种纤维不变性给唯一映射。因为合法有限词全可补零，不能以不实际的标签填补矛盾。对同一个 $T$，两层式（36.5）经限制给一致输出；若从候选 $\overline T_n$ 反构 $T$，则须在每个输入上核对该一致性，再用应用36.2的共同实现，不能仅凭各层有函数就拼成动力学。

一个具体例子是位置删除 $\sigma x=(x_{j+1})_j$：$m(n)=n+1$，$\overline\sigma_n$ 删除输入前缀的首位。这不同于式（36.1）删除末位的限制箭头，也不同于 Zeckendorf 算术后继。在 $k=2$ 的 Zeckendorf 载体 $X_2$ 上，主卷定理20.5、20.7、20.9已经证明算术后继的行程复杂度和零熵，以及位置删除的 $\log\phi$ 熵；这里的数值熵比较限定于 $k=2$，编码载体相同不消去操作差别。

对连续 $T$，紧性保证每个有限输出 $q_nT$ 可由某个有限输入深度决定：各点附近有使这个有限值恒定的前缀柱，取有限覆盖并取最大深度即可。这只提供数学上的某个 $m(n)$；没有给其可计算性、最小值或代价。实际接口须写出可使用的 $m(n)$、需要取得哪些来源的读数、阈值计算、动作合法性、费用及顺序。若 $T$ 只定义在有限支持核心，向完成载体延拓还须满足已有 Q124 的连续性条件；恢复卷命题31.14的保 Zeckendorf 数值到 $\mathbb Z_2$ 映射因奇偶障碍就不具备它。即使某种映射连续可表示，恢复卷命题31.11–31.13仍分别约束保律性、总连续公平位采样和实际读位预算。

一组相容值作为数学对象可被指定，不表示观察者已经取得全部值。只有其所需读数已通过真实来源和合法历史供应，它才能作为当前可用的新观察对象。全层规则、实际有限读数、读取一个新层的操作是不同资源。层的起点是分析坐标的声明；本节不从此前缀模型推出物理的首层、自动自相似、所有时间均为幻觉或完成化就是概率。

### 36.3 完整档案、共同参考与一个继续运行的记忆

**定义 36.4（本模型的完整获取合同）。** 沿用定义13.1、命题13.2、定义13.3、约定15.1及定义35.1，$C$ 保留全部已获、带来源身份的内外记录和已取得的关系，$H_t$ 保留 $C$ 及到时刻 $t$ 的完整合法历史。它包括准备、共同来源、相位及其它校准、允许的动作和次序、各局部钟读数及共同约束、误差合同、失败、停止和已有结果。活动记忆 $M$ 是当前任务的一个工作端口；已发出而尚相干的寄存器和可访问量子参考 $R$ 仍作为量子系统保留，不给互不相容测试预填经典取值。非正交标签 $m_i$ 不是一份可随意复制的经典档案，相关限制见定理11.15。

使用按 $c$ 条件化的态公式时，明确假设经典档案有正则条件核，例如 $C$ 取标准 Borel 值，实际模型给可测密度核 $c\mapsto\sigma_{MR\mid c}$；有限维量子端口采用第11节约定。也可直接以已有的实际联合 cq 态和对应仪器陈述，而不对无正则条件的零质量单点任意写态。根准备所需的是对几乎每个允许 $c$，实际满足
$$
\sigma_{MR\mid c}=|m_0\rangle\langle m_0|\otimes\tau_{R\mid c},
\qquad
\text{每个新空白均为与当时全部联合系统独立的 }|0\rangle\langle0|,
\qquad W\text{ 在各轮固定}.
\tag{36.6}
$$
$k$、基、相位和 $W$ 在此比较中固定；若它们随校准档案变化，须先给逐纤维的明确识别再使用相应公式。式（36.6）不要求档案各部分或 $C,R$ 彼此独立；它要求当前根记忆与参考在给定完整档案后确为所写纯积准备。法定动作的先后关系也不蕴含这项概率独立。

若实际准备不满足式（36.6），应以真实 $\sigma_{CRM}$ 开始，在保留 $C,R$ 的联合系统上应用 $I_{CR}\otimes W$ 并继续计算。记忆的边缘、旧来源标签或部分档案相同都不能授权插入一个独立根态。第11节的历史仪器、有限梳和参考规范提供这种共同实现的类型；第13节负责完整已获关系，第15节负责有扰动、反馈时的实际联合核。它们不是由本编码模型替代的新通用过程理论。

**命题 36.5（计算基获取的条件追加律）。** 在定义36.4及式（36.6）的真实准备下，若已按计算基获得合法前缀 $w$ 并保留它，且生成继续使用同一个 $W$，没有其它记忆干预，则对任意有限续词 $v$，
$$
\Pr(v\mid C=c,w)
=\mathbf1_{wv\text{ 合法}}\lambda^{-|v|}\frac{r_{i(wv)}}{r_{i(w)}}.
\tag{36.7}
$$
这是几乎每个 $c$ 上的正概率分支合同。获得 $w$ 后的活动记忆为 $|m_{i(w)}\rangle\langle m_{i(w)}|$，参考条件态仍为 $\tau_{R\mid c}$；档案则扩充为 $(C,w)$，不能用这个记忆态替换它。

证明。恢复卷式（31.9）的 $w$ 分支为 $\sqrt{\mu_k[w]}\,m_{i(w)}$。给定 $c$，参考因实际积准备独立于该生成分支，因此测得 $w$ 后保持 $\tau_{R\mid c}$。合法 $w$ 的根质量正；同一单 Kraus 仪器连续应用到 $v$，各步振幅平方中的 $r$ 因子望远镜相消，得式（36.7），非法分支为零。等价地由同一个根联合律取比 $\mu_k[wv]/\mu_k[w]$；两种计算使用的是同一准备与同一历史，不是分别选出的边缘律。$\square$

例如前缀 $0$ 与 $00$ 都留下 $m_0$，但已获长度、输出记录、发生事件及费用不同。工作记忆只对所声明的未来生成任务充分；即使该任务今后精确闭合，也不恢复被它省略的完整已获观察者。若控制器会依据旧前缀选动作，就必须保留其访问档案，不能以末态相同合并控制器情境。这与命题15.8的来源档案区别及第35节的实际可行族语义一致。

### 36.4 相干端口实验、参考安全与有限窗口使用

**命题 36.6（固定生成下的输出实验及联合误差运输）。** 固定有限时域 $n$，在定义36.4的同一真实联合准备上，后续生成始终只对 $M$ 和新鲜空白使用相同 $W$。允许 tester 对已经发出的端口、它自己的保留系统及允许参考施加仪器，保留全部结果；允许根据先前结果选择后续输出仪器，但这些选择不反馈改变生成器、空白或活动记忆。则这些实验的完整结果律可在先生成全部 $n$ 个输出后的同一联合态上计算。

若两种实现具有共同档案／参考类型、相同控制器和相同允许 tester，且其实际联合输入态（含 $C,R$ 和所有被测试输出）的半迹距离不超过 $\eta$，则所有这种保留完整记录的保迹 tester 的输出距离不超过 $\eta$，最终经典结果的 TV 也不超过 $\eta$。有限经典档案可直接写 cq 矩阵；一般标准 Borel 档案使用同一条件核的可积分块及对应联合范数。仅输出边缘的距离界不具有任意参考安全性。

证明。给定一条未归一化仪器分支，已发出端口上的分支映射与下一步作用于 $M$、新空白的等距通道作用在不交因子，因此作为张量线性映射交换。已有端口与记忆即使纠缠也不影响这个代数等式。把各输出分支逐次移到全部生成之后，保留其未归一化权重，就得到相同联合分支。自适应仪器沿每条已记录历史固定分支，再对所有历史求和；因为未来 $W$ 和空白没有反馈变化，仍可这样移动。归一化条件态只在最后按该支真实概率取得，不能在中途忘掉选择权重。

完整 tester 含全部结果旗标时为 CPTP，直接应用本卷引理10.6及定义11.18的历史接口即可；经典终端测量后迹距离就是 TV。该引理允许不同有限维输入输出并保留参考，已有 [FiniteTraceDistance.traceDistance_contract](../../../D5/S3/Quantum/Foundation/FiniteTraceDistance.lean)是同型载体供应，不将它的原声明范围扩大冒领。可积 cq 条件块的版本逐块应用同一界并积分。相反，令 $C$ 公平，一份二元输出等于 $C$，另一份输出与 $C$ 独立公平，则输出边缘相同，联合 TV 为 $1/2$；所以输出零误差本身不能控制有权读取 $C$ 的 tester。$\square$

后选择还需要成功率。若相同分支的次归一化态为 $X,Y$，概率 $p,q\ge s>0$，则
$$
\left\|X/p-Y/q\right\|_1
\le\frac{\|X-Y\|_1+|p-q|}{p}.
\tag{36.8}
$$
因此联合距离至多 $\eta$ 时，利用同一不增迹分支的 $\|X-Y\|_1\le2\eta$、$|p-q|\le2\eta$，得到保守的条件半迹距离上界 $2\eta/s$。若没有成功概率下界，小的未条件化误差不能保证小的归一化分支误差。失败旗标和其概率属于完整实验，不因选中成功而删除。

在式（36.6）下，同一独立档案／参考准备可接到两种比较输出上：根相干输出为 $\rho_{k,n}$，乘积比较输出为 $p_n$。给定同一个 $c$，二者共同张量 $\tau_{R\mid c}$ 不改迹距离，保留共同 $C$ 后积分也不改。因此恢复卷定理31.8的
$$
D(\rho_{k,n},p_n)\le\sqrt{4n2^{-k}/3}\quad(0\le n<k)
\tag{36.9}
$$
可在这一真实共同独立合同下控制命题36.6的全部输出 tester。若档案或参考与输出具有别的实际相关，须先证明它们的联合界，不能把式（36.9）自动提升。恢复卷命题31.7的均匀长词弃尾误差也只有在同样声明联合准备后才具有这种使用方式。有限窗口 $n$、弃尾长度 $m$ 和阶数 $k$ 分别占不同坐标。

反过来，恢复卷命题31.9和定理31.10已说明：每个固定有限 $k$ 的全部时域上并无趋零的统一乘积近似，完成 UHF 态的半泛函距离为一；指定全加概率和到最大有限距离的缺口按 $\log2-\log\lambda_k$ 衰减。它们比较的是约定输出实验，既不推导近似活动记忆下界，也不声称任意仪器的秩下界。

全加实验需保持相干端口和共同可访问相位参考。依命题36.6，可对每个已发出的 qubit 顺序测量同一加减基，并保留所有结果；全加支概率正是恢复卷式（31.33），不需直接访问活动记忆。若输出已不可逆地变成可区分计算基记录，约化输出已退相干，同一实验概率改为恢复卷式（31.41）的 $2^{-n}$。能否在更大联合系统中恢复相干需另有实际访问和操作证明，不能只因为写过一个相同的经典词律就恢复它。[EnvironmentRecords](../../../D5/S3/Quantum/EnvironmentRecords.lean)的记录重叠公式及[量子实在卷定理222.1–222.2](QUANTUM-REALITY.md)正是此区别的来源；相同约化通道也不能确定观察者已取得哪些环境知识。

记忆干预、结果反馈改变 $W$、相位重置、共享隐藏环境、择时停止生成或未记录后选择不属于命题36.6的上述交换论证。应按定义11.5、11.8–11.11的有限梳、共同初态和历史仪器给实际扩大模型，再评价允许任务。仅知道所有未干预输出族相等，不能由此取得这些能力。

### 36.5 条件档案下的换码与重复试验资源

保律换码在完整观察者中是一个联合任务。对每个档案值 $c$，若实际条件输入正是恢复卷命题31.11的 $\mu_l$，所要求的条件目标正是 $\mu_k$，并且 $F(c,\cdot)$ 总连续确定，则其域包含必要条件适用。若只要求无条件输出律相同、或 $c$ 已携带相关随机选择信息，不能把这个条件结论未经检查施加到每个纤维。恢复卷命题31.12给至多 $M$ 个公平位的第一边缘误差；其“公平独立”必须在给定完整已获 $C$ 后成立。档案中已有的随机性是资源，删除其来源后再称采样器只用 $M$ 位会改变问题。

对实际目标首位零概率 $p_c$，应使用 $\min_j|p_c-j/2^M|$；这类条件界的平均只在保留 $C$ 的共同联合任务中有相应含义，不自动下界无条件 TV，恢复卷已给混合抵消的反例。阈值可测采样几乎处处逐前缀终止，也不承诺统一位数、统一计算时间或输入来源相关性的恢复。加随机核和添加档案读取权限都应连同取得合同计费，而不是从完成对象存在性推出采样器可执行。

**推论 36.7（实际独立完整准备下的重复全加试验）。** 固定 $k\ge2,n\ge1$。在完整档案和实际参考合同下，另有 $N$ 次长度 $n$ 的完整根准备，每次内部使用同一个继续运行的 $M,W$；各次输出的联合态实际为这些声明准备的乘积，或给定完整 $C=c$ 后实际条件独立且每次成功概率均为同一个 $f_{k,n}$。所有试验具有所需共同相位校准与相干输出访问，各次新准备的资源已供应，不把同一未重备记忆上的相邻窗口假装成独立试验。则至少一次全加的概率为
$$
\Pr(\text{至少一次全加})=1-(1-f_{k,n})^N.
\tag{36.10}
$$
给定固定失败容限 $\delta\in(0,1)$，该协议达到成功率至少 $1-\delta$ 的最小整数试验数为
$$
N_{\min}=\left\lceil\frac{\log\delta}{\log(1-f_{k,n})}\right\rceil,
\qquad
N_{\min}\sim\frac{\log(1/\delta)}{C_k}(2/\lambda_k)^n
\quad(n\to\infty,\ k\text{ 固定}).
\tag{36.11}
$$

证明。合同中的实际独立性使全部失败概率为 $(1-f_{k,n})^N$；条件版本在每个合法 $c$ 上给同一数值，积分后不变。恢复卷定理31.10给 $f_{k,n}>0$。$n\ge1$ 时该密度秩至少二，所以在一个秩一投影上的概率严格小于一；故对数有限且负，解失败率不等式得到整数式。固定 $k$ 时 $f_{k,n}\to0$，$-\log(1-f)/f\to1$，再用恢复卷式（31.35），得到渐近式。$\square$

这是这个独立重复协议的成本结论，不是所有区分策略或所有实验的普遍试验数下界。若实际协议在首次成功时停止，可在上述可供应的 $N$ 次独立准备合同内截断，成功概率仍为式（36.10）；须保留此前所有失败、停止时刻、发生的动作及已消耗资源，不能只交成功样本。若根本没有这些独立准备，推论不适用。$n=0$ 的空全加事件恒真，不属于式（36.11）的对数成本情形。

### 36.6 同一关系网络的范围与继续研究接口

现在能够连起的箭头是：合法有限读数经相容和密度条件接到完成载体；根权重接到经典概率；额外 Gram／相位／准备结构接到完整量子输出；同一活动记忆接续所有有限历史；合法 tester 在同一档案和参考合同上读取这些输出。各箭头的可恢复性取决于其纤维、共同实现、访问权限和精度预算。一个层的输出可以在下一个任务中作为内部输入，多个档案可以交叠共享来源；没有哪一个层因为编号较小而自动成为优先本体。

这一结构保留离散与完成的体／边界解释，也保留观察者包含全部已获信息的要求。共同记忆只是其中一条工作接口，不是观察者的替身。局部钟的次序和联合约束依第13节及第30–32节的合同保留；发射编号、精度深度、尺度参数和物理时间并不因此同一。移动或动作若改变可取得的信息，应体现为历史、访问端口或联合仪器改变，不能通过给同一个参数换名字处理。波、频率、粒子式编码、层叠与分形仍要分别给可检验的动力学、谱、共同来源和尺度条件；本节没有从编码名称推出物理波粒二象性。

后续仍需研究的接口包括：具体可用门集下的精确／近似准备及计价；在保留真实档案与量子参考时，允许干预族的误差与最低资源；超出 $k=2,3$ 域次数反例后的保律运输充分条件。它们保持原任务和完成判据，不被本节有限模型的证明替代。本次是既有研究网络的一段源卷进展；全部结论为所写假设下的普通数学推导，不宣称新增形式核验、完整物理统一或持续计划完成。

## 36.99 追加锚

## 37. 有限循环的合法边界、联合来源与世界实现

### 37.1 完整档案上的同一实际律与局部运输

**定义 37.1（有限循环的完整观察合同）。** 沿用定义35.1的完整档案可行族，以 $H$ 固定全部已获的内部／外部记录、来源及其关系、参考、各局部钟与联合顺序、校准及误差证书、准备、允许操作和已经取得的费用信息。声明一个非空的世界—概率律可行关系及其中的实际律 $\rho$；可行关系同时约束记录解释、来源相关、策略和干预。定义36.4中档案、活动记忆和外部参考的区别继续适用：当前循环、成对表或解码律只是该观察者使用的任务视图。本节是经典有限模型，不附加式（36.6）的编码专用纯根准备；量子参考仍需原来的联合态合同，不能替不相容实验填入共同经典值。

给合法世界集 $W_H$ 和标签映射 $\lambda$，实际标签律为 $P=\lambda_*\rho$。仅有 $W_H$ 与 $\lambda$ 不规定允许哪些概率律。也可直接声明一个实际标签律 $P$，把其世界提升留作额外前提；分别供应的边缘表相容不证明已经存在这一个 $P$。以下所有比较均固定同一 $H$ 和一份声明实验。

令 $n\ge3$，各 $B_i$ 有限非空，$h_i:B_i\to B_{i+1}$ 为双射，指标模 $n$。给节点概率 $\mu_i$，要求包括闭合边在内的 $(h_i)_*\mu_i=\mu_{i+1}$，并要求同一实际联合律的 $X_i$ 边缘为 $\mu_i$。定义
$$
U_0=\mathrm{id},\quad U_j=h_{j-1}\cdots h_0,\quad
B=B_0,\quad \mu=\mu_0,\quad g=h_{n-1}\cdots h_0,
\quad Y_j=U_j^{-1}X_j.
\tag{37.1}
$$
于是 $g_*\mu=\mu$，每个 $Y_j$ 的边缘均为 $\mu$。内部理想关系为 $Y_{i+1}=Y_i$，闭合关系为 $Y_0=gY_{n-1}$；闭合成对表始终按 $(Y_{n-1},Y_0)$ 排列。坐标变换是原子的双射重标，保持 TV；坐标含义和来源是接口的一部分。下文仍以 $P$ 表示运输后的同一联合律。

对已声明 $S\subseteq B^n$，置
$$
\mathcal C_S=\{P\in\operatorname{Prob}(B^n):P(S)=1,
\ (Y_j)_*P=\mu\text{ 对每个 }j\},\qquad
\mathcal C_{B^n}\text{ 为无限制支撑类}.
\tag{37.2}
$$
这是仅限制支撑及节点边缘的比较类。更强的概率准入类可以非凸；任何应用都须有实际成员，且须准入所用的具体构造。逐标签有合法元组并不保证某个联合律被准入。

换锚点到节点 $j$ 时，闭路置换变为 $U_jgU_j^{-1}$，节点律变为 $(U_j)_*\mu$，所以轨道质量及移动质量不变；锚只是参考选择。[主卷命题133.1](RECURSIVE_RELATIONAL_OBSERVATION.md)在同一来源、相等观察核及完整实际像上给规范双射和余循环律，那种闭路的 holonomy 为恒等。本节非平凡 $g$ 描述另行提出的局部兼容关系或声明操作，不反驳该供应结果。编码重置矩阵不必可逆，不能充当这里的 $h_i$。本节“割”只表示省去一条循环边，与第13节的因果序理想割不同。

### 37.2 所有相位合法的割与精确预算

**定理 37.2（合法总误差面）。** 使用[恢复卷定理32.3](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)的完整分类、固定对角 $D(x)$ 和单割元组 $T^k(x)$。对正质量移动轨道 $O$，令
$$
L_{O,k}=\{x\in O:T^k(x)\in S\},\qquad
K_O=\{k:L_{O,k}=O\},\qquad w_O=\mu(O).
\tag{37.3}
$$
$\mathcal C_S$ 含总误差为 $a=\mu(\{x:gx\ne x\})$ 的律，当且仅当每个正质量固定点的 $D(x)$ 合法，且每个正质量移动轨道满足 $K_O\ne\varnothing$。此时全部这类律组成
$$
\mathcal F_S=\prod_O\Delta(K_O),\qquad
\dim\mathcal F_S=\sum_O(|K_O|-1).
\tag{37.4}
$$
没有移动轨道时乘积是一点；零质量轨道不附加条件。对更强准入类，式（37.4）只是容纳其最优律的支撑面，还须取交集并检查成员资格。

证明。恢复卷定理32.3说明每一正轨道的割列质量在所有相位上相同；若该列正，就在 $O$ 的每个 $x$ 使用 $T^k(x)$，故必须 $k\in K_O$。固定点的质量不能移动到其他标签，故对应对角必须合法。反过来，每轨道任选 $K_O$ 上的概率，配以必需的固定对角质量，即得合法且边缘精确的最优律。移动元组的 $(x,k)$ 唯一，因而这些概率坐标无额外识别；各因子的维数相加。$\square$

**定理 37.3（最优面上的加权 Hall 预算）。** 假设定理37.2的面非空，给有限 $\varepsilon_k\ge0$。在 $\mathcal F_S$ 中存在每边误差不超过 $\varepsilon_k$ 的律，当且仅当对任意正质量移动轨道子集 $A$ 有
$$
w(A):=\sum_{O\in A}w_O\le\sum_{k\in N(A)}\varepsilon_k,
\qquad N(A)=\bigcup_{O\in A}K_O.
\tag{37.5}
$$
等价的分配是 $z_{O,k}\ge0$、$k\notin K_O$ 时为零，且
$$
\sum_kz_{O,k}=w_O,\qquad \sum_Oz_{O,k}\le\varepsilon_k.
\tag{37.6}
$$
若 $a>0$，面内最小最大边误差为
$$
\min_{P\in\mathcal F_S}\max_k\delta_k(P)
=\max_{\varnothing\ne A}\frac{w(A)}{|N(A)|}.
\tag{37.7}
$$
分母均正；$a=0$ 时值为零。

证明。恢复卷的误差投影为 $\delta_k=\sum_Oz_{O,k}$。将 $A$ 的行求和即得必要性。充分性用有限网络：源到 $O$ 的容量 $w_O$，每条允许的 $O\to k$ 容量 $C=a+\sum_k\varepsilon_k+1$，$k$ 到汇的容量 $\varepsilon_k$。实容量可行流集合非空、闭且有界，因此流值取得最大值。若最大值 $v<a$，其残量网络没有正容量的源汇路径，否则沿该有限路径加其最小正残量即提高流值。令 $A,J$ 分别为源可达的轨道和割节点。每条中间弧流量至多 $a<C$，所以 $N(A)\subseteq J$。从可达集到不可达集的弧饱和，反向跨割弧流量为零；对可达节点守恒求和，得到
$$
v=w(\text{全部轨道}\setminus A)+\sum_{k\in J}\varepsilon_k<a.
$$
这给 $w(A)>\sum_{k\in J}\varepsilon_k\ge\sum_{k\in N(A)}\varepsilon_k$，违背（37.5）。故有满值 $a$ 的流，饱和各轨道供给而给出（37.6），再用定理37.2构造律。令所有容量 $\varepsilon_k=t$，Hall 条件恰为 $t\ge w(A)/|N(A)|$，得到（37.7）。$\square$

这是 Ford–Fulkerson 的成熟流机制在本有限分配中的应用[^rroctx37_flow]。证明只用实流的紧性和最大流的残量割，不声称任意无理容量的逐次增广会终止。[RationalSTCutCertificate.lean](../../../D5/S0/Certificates/RationalSTCutCertificate.lean)负责已供应有理流／割证书的会计、弱对偶与可靠检查，不供应此实容量存在性或一个流生成器。

**命题 37.4（超额预算不能只查最优面）。** 若 $\sum_k\varepsilon_k=a$，任一满足预算的 $P\in\mathcal C_S$ 由恢复卷定理32.1被迫属于 $\mathcal F_S$，故 Hall 亦是全类的判据。若预算总和大于 $a$，这个结论不成立。

证明及反例。取 $n=3$、$B=\mathbb Z/3\mathbb Z$、$g(x)=x+1$、均匀 $\mu$，仅允许
$$
T^0(x)=(x,x-1,x-1),\qquad U(x)=(x,x,x+1).
\tag{37.8}
$$
仅割 $0$ 的全部相位合法。两族各自的均匀律都保留所有节点边缘，误差分别为 $(1,0,0)$ 与 $(0,1,1)$；其半混合误差为 $(1/2,1/2,1/2)$。对应预算的面内 Hall 要求 $1\le1/2$，不成立，但这份总误差 $3/2>a=1$ 的实际律满足预算。第一项由 $a\le\sum_k\delta_k\le\sum_k\varepsilon_k=a$ 直接得出。$\square$

### 37.3 更强概率准入的障碍与固定多面体替代

**命题 37.5（凸性、逐点合法与共同割仍不足）。** 恢复卷定理32.7、定义32.10和定理32.14的输出属于 $\mathcal C_S$；它们不因逐元组合法或准入类凸而自动属于更强类。即使全部共同割混合已准入，依轨道修复仍可能不被准入。

证明及反例。二元翻转三角形中让全部元组合法，却只准入独立均匀乘积律构成的凸单点类。它的三边误差都是 $1/2$，所以预算 $(1/3,1/3,1/3)$ 不可行，尽管预算和等于 $a=1$。这里缺失的是割律的准入。

再取 $n=3$、$g=(01)(23)$、均匀 $\mu$，令 $\mathcal F_c=\operatorname{conv}\{P^0,P^1,P^2\}$，$J$ 为独立均匀乘积。令 $Q_*$ 在轨道 $\{0,1\}$ 选割 $0$，在轨道 $\{2,3\}$ 选割 $1$。对共同割混合 $Q_\pi$，重叠质量为 $(\pi_0+\pi_1)/2$，故 $\operatorname{TV}(Q_*,Q_\pi)\ge1/2$。置
$$
\varepsilon=1/100,\quad P_\varepsilon=(1-\varepsilon)Q_*+\varepsilon J,
\qquad \mathcal A_\varepsilon=\operatorname{conv}(\mathcal F_c\cup\{P_\varepsilon\}).
\tag{37.9}
$$
所有成员节点边缘相同。$Q_*$ 的误差是 $(1/2,1/2,0)$，$J$ 的误差是 $(3/4,3/4,3/4)$，所以 $P_\varepsilon$ 的误差及剩余量为
$$
(201/400,201/400,3/400),\qquad R(P_\varepsilon)=1/80.
\tag{37.10}
$$
$R$ 在这同一固定节点类上非负且仿射，故 $\mathcal A_\varepsilon$ 的零面恰为 $\mathcal F_c$。三角不等式与 $\operatorname{TV}(P_\varepsilon,Q_*)\le\varepsilon$ 给
$$
\operatorname{dist}_{\rm TV}(P_\varepsilon,\mathcal F_c)\ge49/100.
\tag{37.11}
$$
无限制支撑时 $M_{\max}=1/2$，恢复卷（32.18）的界为 $2R=1/40$；可见其构造不能直接作为此更强类的成员。$\square$

**命题 37.6（一个固定紧凸类没有线性剩余量界）。** 在命题37.5的四标签模型中，令
$$
B_t=(1-t-t^2)P^0+tQ_*+t^2J\quad(0\le t\le1/2),\qquad
\mathcal A=\operatorname{conv}\bigl(\mathcal F_c\cup\{B_t:0\le t\le1/2\}\bigr).
\tag{37.12}
$$
$\mathcal A$ 是固定紧凸概率类，零剩余面为 $\mathcal F_c$，但不存在有限 $L$ 使所有 $P\in\mathcal A$ 满足 $\operatorname{dist}_{\rm TV}(P,\mathcal F_c)\le LR(P)$。

证明。系数非负且和为一，生成集合紧；有限维空间中紧集的凸包仍紧。具体可由仿射依赖消元把任意凸组合缩到环境维数加一项，从而凸包是紧的“点组乘单纯形”连续像。$R(B_t)=5t^2/4$，非负仿射性及有限凸分解说明零剩余只使用 $\mathcal F_c$ 与 $B_0=P^0$，故零面如述。

定义 $f$ 在第一轨道锚的割 $0$ 元组上为 $+1$，在第二轨道锚的割 $0$ 元组上为 $-1$，其余为零。则 $|f|\le1$，在 $\mathcal F_c$ 与 $J$ 上的期望均为零，在 $Q_*$ 上的期望为 $1/2$。于是 $\mathbb E_{B_t}f=t/2$；对任意 $Q\in\mathcal F_c$，有限和三角不等式给 $|\mathbb E_{B_t}f-\mathbb E_Qf|\le2\operatorname{TV}(B_t,Q)$，从而
$$
\operatorname{dist}_{\rm TV}(B_t,\mathcal F_c)\ge t/4,\qquad
\frac{\operatorname{dist}_{\rm TV}(B_t,\mathcal F_c)}{R(B_t)}\ge\frac1{5t}\quad(t>0).
\tag{37.13}
$$
令 $t\downarrow0$ 即得。$\square$

在一个固定紧类上，若连续非负剩余量有非空零集，则剩余量趋零仍蕴含到零集的距离趋零。否则有距离统一大于某个正数的序列；紧性给收敛子列，连续性使极限落在零集，与距离下界矛盾。这一定性命题与恢复卷命题32.9的变字母集族相容。

**定理 37.7（固定概率多面体的顶点间隙界）。** 令 $\mathcal D$ 是一个固定非空概率多面体，$R$ 为其上非负仿射函数，且 $\mathcal F=\{\rho\in\mathcal D:R(\rho)=0\}\ne\varnothing$。全部来源和记录约束须包含在 $\mathcal D$ 中；应用于循环时也固定节点律以保证剩余量非负。若所有顶点剩余量为零，则 $\mathcal F=\mathcal D$；否则定义最小正顶点剩余量 $\gamma>0$，有
$$
\operatorname{dist}_{\rm TV}(\rho,\mathcal F)\le\min\{1,R(\rho)/\gamma\}.
\tag{37.14}
$$
证明。写 $\rho=\sum_v\alpha_vv$，令 $\eta=\sum_{R(v)>0}\alpha_v$，则 $R(\rho)\ge\gamma\eta$。选任一 $f\in\mathcal F$，令
$$
\rho_* =\sum_{R(v)=0}\alpha_vv+\eta f\in\mathcal F.
$$
有限和的三角不等式给 $\operatorname{TV}(\rho,\rho_*)\le\sum_{R(v)>0}\alpha_v\operatorname{TV}(v,f)\le\eta$，即得。$\square$

这个明确顶点证明处于 Hoffman 型多面体误差界的成熟背景[^rroctx37_hoffman]，只给某个被准入最优律的存在性，不是指定解码输出 $Q$ 的提升。计算 $\gamma$、顶点分解及见证另需资源，换多面体不能保留同一常数。仿射性不可省：在 $\rho_t=(1-t,t)$ 上取非线性剩余量 $t^2$，零集为 $\{\rho_0\}$、正顶点间隙为一，但距离 $t>t^2$（$0<t<1$）。非负性则防止顶点剩余量相互抵消。空零面及额外非线性准入不属该定理。

### 37.4 标签纤维的抵消与指定目标的世界提升

**命题 37.8（同一纤维内不可见的质量抵消）。** 固定有限 $W=W_H,Z$、实际概率 $\rho$、$\lambda:W\to Z$ 及 $P=\lambda_*\rho$。给一个指定目标标签概率 $Q$，对任一满足 $\lambda_*\rho'=Q$ 的候选世界律置
$$
A_z=\sum_{\lambda w=z}(\rho'(w)-\rho(w))_+,\qquad
B_z=\sum_{\lambda w=z}(\rho(w)-\rho'(w))_+.
\tag{37.15}
$$
则
$$
\operatorname{TV}(\rho,\rho')-\operatorname{TV}(P,Q)
=\sum_z\min(A_z,B_z).
\tag{37.16}
$$
等 TV 的条件是亏损纤维只减质量，盈余纤维只加质量，总量不变的纤维逐点不变。

证明。$A_z-B_z=Q(z)-P(z)$，世界及标签 TV 分别为 $\tfrac12\sum_z(A_z+B_z)$、$\tfrac12\sum_z|A_z-B_z|$；用 $a+b-|a-b|=2\min(a,b)$ 得（37.16）。一般的等 TV 无符号混合判据由 [D5/S3/TotalVariation/Equality/DataProcessingEquality.lean](../../../D5/S3/TotalVariation/Equality/DataProcessingEquality.lean) 的 `total_variation_channel_eq_iff_no_sign_mixing` 供应：在这里取确定核 $\mathbf1_{\lambda w=z}$。它要求每个纤维的差只取一种符号；结合纤维总差即得所述三种情况。$\square$

（37.16）计量的是标签遗忘后隐藏的世界改变量，不是物理耗散公式；此处复用一般等号定理，不另立一套通用 TV 等号理论。

**命题 37.9（无额外律限制时的等距离提升）。** 若允许 $W$ 上任意概率律，则 $Q$ 可提升当且仅当每个 $Q(z)>0$ 的纤维 $W_z$ 非空；满足时可选 $\rho'$ 使 $\operatorname{TV}(\rho,\rho')=\operatorname{TV}(P,Q)$。

证明。必要性由推前定义。对 $P(z)>0$，在纤维内设 $\rho'(w)=Q(z)\rho(w)/P(z)$；对 $P(z)=0<Q(z)$，选择 $W_z$ 上任意概率并赋总量 $Q(z)$；对 $P(z)=Q(z)=0$ 直接置零，不选择条件坐标或见证。各纤维改变量同号，命题37.8给等距离。$\square$

正旧质量且正目标质量的纤维保留旧条件分布；这是主卷定义67.7、定理67.8的正质量纤维分解在指定标签任务上的应用。它可能改变外部来源。若 $Q=P$，唯一距离零的提升为 $\rho$ 本身。

### 37.5 保留联合来源的满流判据

**定理 37.10（指定标签的来源保留等距离提升）。** 在命题37.8下另给有限 $U$、$\sigma:W\to U$ 及 $\nu=\sigma_*\rho$，准入全部且仅有满足此来源边缘的 $W$ 上概率律。若多个来源或参考须共同保留，$\sigma$ 编码其联合记录，或施加等价的完整联合约束；分别保留各来源边缘不足以保留其联合律。定义
$$
D=\{z:P(z)>Q(z)\},\quad A=\{z:Q(z)>P(z)\},\quad
\tau=\operatorname{TV}(P,Q),\quad
 d_z^-=P(z)-Q(z)\ (z\in D),\quad d_z^+=Q(z)-P(z)\ (z\in A),
$$
$$
r_{z,u}=\rho(\lambda=z,\sigma=u),\qquad
W_{z,u}=\{w:\lambda w=z,\sigma w=u\}.
\tag{37.17}
$$
用互相区别的节点层构造网络：源 $s$ 到 $z\in D$ 容量 $d_z^-$；$z\in D$ 到 $u$ 容量 $r_{z,u}$；若 $W_{z',u}\ne\varnothing$，则 $u$ 到 $z'\in A$ 容量 $\tau$，否则无弧；$z'\in A$ 到汇容量 $d_{z'}^+$。则存在来源保留且满足
$$
\lambda_*\rho'=Q,\qquad \sigma_*\rho'=\nu,\qquad
\operatorname{TV}(\rho,\rho')=\tau
\tag{37.18}
$$
的律，当且仅当此网络有值为 $\tau$ 的流。$\tau=0$ 使用零流并返回 $\rho$。

证明。必要性使用命题37.8的既有等号判据：仅亏损标签可移除，仅盈余标签可加入，标签总量不变的纤维不能作中转储库。聚合每个亏损单元的移除量为 $f_{z,u}\le r_{z,u}$，每个合法盈余单元的加入量为 $h_{u,z'}$。标签总量给出饱和供需 $d^-,d^+$；来源边缘保留给出 $\sum_zf_{z,u}=\sum_{z'}h_{u,z'}$，即中间层守恒。总流量为 $\tau$，故接收弧容量 $\tau$ 足够，构成满流。

反之，满流的总值等于全部供给及需求之和，故每条源出弧与汇入弧饱和。在 $r_{z,u}>0$ 的移除单元，逐世界移除 $f_{z,u}\rho(w)/r_{z,u}$，容量保证不致负值；$r_{z,u}=0$ 时流量为零，不作除法。每个有正接收流的单元选一个合法世界加入 $h_{u,z'}$，或在该单元内分布它。守恒保留 $\nu$，供需饱和给 $Q$，移除与加入的标签不交，故世界总移除／加入量各为 $\tau$，世界 TV 正好为 $\tau$。$\square$

初始质量零但非空的接收单元可以接收；旧移除质量零的单元容量就是零。$\nu(u)=0$ 的来源没有移除供给，不能得到新质量。任何必需而空的标签纤维同时阻止满流和一切提升。$\tau=0$ 不需新见证。保留 $\sigma$ 的联合律仍不自动保留来源—标签条件机制。若另加概率、策略、机制或资源限制，此流条件对等 TV 仍必要，但充分性还需准入刚才的具体构造。

来源保留且标签为 $Q$ 的目标提升集若非空，是紧多面体；连续 TV 在其上取得最小值。因此满流失败时，要么根本不可提升，要么最小世界 TV 严格大于 $\tau$，不能把两者混同。

**命题 37.11（四世界上的放大与不可行分离）。** 取按所写顺序排列的
$$
W=\{(u_0,A),(u_0,B),(u_1,B),(u_1,C)\},\qquad
\rho=(1/2,0,1/2,0),\qquad \nu=(1/2,1/2).
\tag{37.19}
$$
若 $Q(B)=Q(C)=1/2$，标签 TV 为 $1/2$，等距离网络的最大流为零，却有唯一来源提升 $(0,1/2,0,1/2)$，世界 TV 为 $1$。

证明。唯一亏损标签 $A$ 只能供给 $u_0$，唯一盈余标签 $C$ 只能接收 $u_1$，故没有源汇通路。目标 $A$ 质量为零迫使 $u_0$ 的全部 $1/2$ 转到 $B$，目标 $C$ 质量 $1/2$ 又迫使 $u_1$ 全部转到 $C$，给唯一提升。标签 $B$ 内加减各 $1/2$，所以（37.16）的额外抵消正是 $1/2$。$\square$

同一载体上 $Q=P$ 成本为零；$Q$ 集中在 $B$ 时满流及等 TV 成本均为 $1/2$；$Q$ 集中在 $A$ 则因 $u_1$ 无 $A$ 世界而不可行，其等距离流也为零。相同的失败流值可对应放大或不可行。

若恢复卷给某个指定 $Q$ 的 $\operatorname{TV}(P,Q)\le E_{\rm label}$，命题37.9的无限制纤维提升或定理37.10的来源满流证书，就把同一误差界原值运输到世界 TV。来源网络需要真实 $r_{z,u}$ 及合法接收单元的证书，成对标签表一般不识别它们。此网络是概率重分配证书，不是因果转移图、可执行干预或改写已获历史的许可；有限观察也不自动取得这些容量。

### 37.6 记录选择器、后续实验与固定尺度

**命题 37.12（真实割选择器的档案条件化）。** 真实选择器 $K$ 是已获记录，须保留于 $H'=(H,K)$。在固定 $H$ 下令其核为 $\kappa(k\mid x,H)$，其中固定锚上的取值也必须明确；对
$$
p_k=\sum_x\mu(x)\kappa(k\mid x,H)>0
$$
有
$$
P(X_0=x\mid H,K=k)=\frac{\mu(x)\kappa(k\mid x,H)}{p_k}.
\tag{37.20}
$$
若核在每个移动轨道内恒定，条件相位仍为轨道均匀，但轨道质量变成 $w_O\kappa_{O,k}/p_k$。在每个正概率选择器值下都保留原 $\mu$，当且仅当对所有正 $\mu$ 支撑上的 $x$ 有 $\kappa(k\mid x,H)=p_k$，即给定 $H$ 后 $K$ 与 $X_0$ 独立。

证明。（37.20）是同一联合律的 Bayes 公式。轨道内 $\mu(x)=w_O/\ell_O$，代入常数核并求和得新轨道质量。若条件律等于原律，对正 $\mu(x)$ 消去该因子即得核恒为 $p_k$；反向直接代入。$p_k=0$ 时非负求和迫使正 $\mu$ 支撑上该核为零，不作条件除法。$\square$

固定锚上实际记录的割是额外档案，不是标签面中增加的重数坐标。决策时可否访问锚或轨道信息、是否有随机源、准备和费用，均需合法执行合同；忘掉 $K$ 不能证明完整观察者得到保留。

同一个共同非负行随机核若合法且因子化通过标签接口，既有 `total_variation_channel_le` 将标签误差运输到它的输出；具体供应为 [D5/S3/TotalVariation/DataProcessing.lean](../../../D5/S3/TotalVariation/DataProcessing.lean)。双方使用不同策略，或实验读取未恢复的参考相关时，不能使用该结论。认证世界提升后可对共同合法世界核作相同运输。操作顺序合法与随机独立不同，保留来源的联合边缘也弱于保留全部来源—标签机制。

每个定理固定 $n,\mu,g,S$ 和接口。系数不显含 $n$ 不消去取得 $n$ 张表、累积误差、认证 $K_O$ 全部相位和控制轨道长度的成本。若精确表已按单元索引且合法集已供应，检测提取至多需 $n$ 乘正质量移动标签数次单元查询，归一化处理 $\sum_O|K_O|$ 项；读入稠密表可需 $n|B|^2$ 项。认证全部合法割可需 $n$ 乘移动标签数次关于长度 $n$ 元组的支撑查询。这里计数的是在这些输入访问前提下的操作次数，不是位复杂度、样本界、支撑可判程序或世界准备成本。截在 $1$ 的界可能没有区分力。

不同尺度各有有限最优律不提供相容选择。即使常值塔的限制映射全为恒等，二元翻转循环交替选择 $P^0,P^1$ 也都是总误差最优而不相容。已有第36.1–36.3节区分词限制、概率边缘化和量子偏迹箭头，也区分完成对象与原来源实现；活动记忆随实际历史演化，不是一个静态逆系统坐标。完成应用须额外声明限制映射、相容律、共同来源／记录和拓扑，并逐项满足既有延拓或实现定理的假设。有限字母表上的概率单纯形通常无限，不能直接套有限集合线程存在性。完成标签律可能还需回到原世界的来源提升，也不提供有限时间访问；恢复卷命题32.9限制的是随轨道增大的统一稳定性。

恢复卷定理31.2–31.5已经给全 $k$、全有限历史的共同记忆及两个分别限定模型的精确容量，不把这些已得结果列为未证。任意仪器、近似记忆、反馈、真实参考的更广任务、跨尺度原来源实现和物理识别仍需各自条件。本节的有限循环修复不能替代它们，也不从关系名称推出物理时空、波／频率、半衰期、量子不确定性、局部钟或 PDE 定律。

### 37.7 理想经验模型、供应归属与适用边界

**命题 37.13（理想循环的 contextual fraction 与实际联合律不同）。** 本节规定的理想边经验模型由各 $M_i$ 组成；它的非上下文分数为 $1-a$、上下文分数为 $a$。实际 $P$ 的成对边缘经验模型已有 $P$ 作全局延拓，因此上下文分数为零，即使 $a>0$ 也如此。

证明。采用被每个经验边缘逐点支配的全局子概率定义非上下文质量。理想图外质量为零，故受支配全局子概率只能支撑于全部关系成立的元组，即固定点对角；其每个固定点质量至多 $\mu(x)$，总质量至多 $\mu(\operatorname{Fix}g)=1-a$，固定对角子概率达到此值。实际模型中 $P$ 本身是质量一的全局延拓，故非上下文分数为一。$\square$

上述理想模型身份是 Katende 定理3.3的循环特例[^rroctx37_katende]：该文在有限连通简单图、反向边取逆置换且根律对 holonomy 群 $H_{\rm hol}$ 不变时，给 $\mathrm{NCF}=p(\operatorname{Fix}H_{\rm hol})$。这里该群由 $g$ 生成。contextual fraction 及受支配子概率框架归于 Abramsky、Barbosa、Mansfield[^rroctx37_cf]，不作为新的框架。它不分类修复律、合法性、源提升或解码。两个仅共一个顶点的二元翻转挫折三角形，取共同公平锚，理想模型的 $\mathrm{CF}=1$；然而每份全局赋值在每个三角形至少失败一条边，故总期望失败至少 $2$，各三角形各指定一割并由共同公平锚生成即可达到。由此不能把单循环的修复目标直接等同于一般图的 contextual fraction。

本节和恢复卷第32节连接已有接口，其供应范围如下；各普通有限推导的假设与证明已在对应命题中给出，不把源码引用视为本节新增的 Lean 核验。

| 本节供应定位 | 已有结论及本节使用边界 |
| --- | --- |
| 37·主卷纤维与共同律 | [主卷67.7–67.8、77.1](RECURSIVE_RELATIONAL_OBSERVATION.md)分别给正质量纤维条件分解，以及严格正共同固定律／闭路势的另一模型；这里的固定节点轨道割面有自己的分类，不能把全部闭路共同律联系宣称为新内容。 |
| 37·主卷拼接与规范运输 | 主卷124.5、124.14–124.17给运行交集、条件乘积与逐行拼接；最大熵拼接不必恢复原来源。主卷133.1的单源等核规范运输具有恒等闭路，本节非平凡局部关系不反驳它。 |
| 37·档案与误差使用 | 本卷5.3–5.5、13.1–13.13、34.1–34.3、定义35.1及36.4保留边缘／联合来源、完整记录、顺序、共同可行纤维及合法误差运输的区别；第36.1–36.3节负责限制箭头与原实现边界。 |
| 37·TV 既有基础 | [Metric.lean](../../../D5/S3/TotalVariation/Metric.lean)、[Convexity.lean](../../../D5/S3/TotalVariation/Convexity.lean)、[DataProcessing.lean](../../../D5/S3/TotalVariation/DataProcessing.lean)分别供应度量／事件、联合凸性和共同随机核收缩；[Equality/DataProcessingEquality.lean](../../../D5/S3/TotalVariation/Equality/DataProcessingEquality.lean)拥有命题37.8调用的一般无符号混合等号判据。 |
| 37·局部关系与树拼接 | [D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction.lean](../../../D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction.lean)给局部集合关系兼容而无整体状态的障碍；[RunningIntersectionRecords.lean](../../../D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.lean)给完整分隔一致的树延拓。两者不替代循环概率准入和 TV 修复。 |
| 37·有限因果耦合 | [FiniteCouplingPushforwardLift.lean](../../../D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.lean)给有理指定粗耦合的双载体边缘保留提升；[BooleanOutcomeMarginalTransport.lean](../../../D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.lean)给在耦合中保留旧分布的有理 Boolean 边缘修正；[CompleteMediatorCutSharpBounds.lean](../../../D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorCutSharpBounds.lean)给指定共同中介下的 Boolean MaxCut／三角形尖锐界。它们各有指定对象，不是任意联合来源提升或合法循环支撑定理。 |
| 37·证书与其他恢复 | [RationalSTCutCertificate.lean](../../../D5/S0/Certificates/RationalSTCutCertificate.lean)检查所给有理流割证书；恢复卷10.2–10.4是正时间／矩与加权 Hilbert 投影；[量子时空卷§100](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)是指定三 qutrit 编码。均不提供这里的一般成对标签解码。 |
| 37·已有完成接口 | [InverseLimitCompletion.lean](../../../D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean)、[StableObservationInverseLimit.lean](../../../D5/S3/ConceptDynamics/RefinementGeometry/StableObservationInverseLimit.lean)负责已声明相容限制、分离／完备及稳定观察线程；[CompactLocalRealization.lean](../../../D5/S3/Observer/Completion/CompactLocalRealization.lean)需紧性与闭纤维；[FiniteCofilteredLimit.lean](../../../D5/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit.lean)需有限对象，不能以有限字母代替有限概率律空间。这里只引用适用边界，不证明新完成结论。 |

有限观察、柱延拓、相容完成和原来源实现的既有区别还见主卷3.4–3.6、4.2、5.2、5.4、33.1、39.12–39.13、78.1、124.9–124.10，以及本卷9.8、24.12–24.15；它们各按原假设使用。这里的有限综合不据此取得原创性结论，也不提供新的跨尺度来源完成定理。它所连接的是提出的局部运输、同一联合标签律、合法修复、可取得边界与有来源约束的世界实现。

[^rroctx37_katende]: Ronald Katende, *Contextual Fraction on Permutation Gain Graphs: Exact Algorithms, Query Lower Bounds, and Dynamic Maintenance*, arXiv:2607.16037v1, [Theorem 3.3](https://arxiv.org/html/2607.16037v1#S3.Thmtheorem3)。引用限于所写置换增益图、holonomy 不变根律的理想经验模型。

[^rroctx37_cf]: Samson Abramsky, Rui Soares Barbosa, Shane Mansfield, *The contextual fraction as a measure of contextuality*, [arXiv:1705.07918](https://arxiv.org/abs/1705.07918)。成熟的上下文分数与受支配非上下文子概率框架。

[^rroctx37_flow]: L. R. Ford, Jr. and D. R. Fulkerson, *Maximal Flow Through a Network*, Canadian Journal of Mathematics **8** (1956), 399–404, [doi:10.4153/CJM-1956-045-5](https://doi.org/10.4153/CJM-1956-045-5)。无理容量增广的终止边界见 Spencer Backman and Tony Huynh, *Transfinite Ford-Fulkerson on a Finite Network*, [arXiv:1504.04363](https://arxiv.org/abs/1504.04363)；定理37.3只用紧最大值及残量割。

[^rroctx37_hoffman]: Alan J. Hoffman, *On approximate solutions of systems of linear inequalities*, Journal of Research of the National Bureau of Standards **49** (1952), 263–265, [doi:10.6028/jres.049.027](https://doi.org/10.6028/jres.049.027)；Javier Peña, Juan C. Vera, Luis F. Zuluaga, *New characterizations of Hoffman constants for systems of linear constraints*, [arXiv:1905.02894](https://arxiv.org/abs/1905.02894)。仅作多面体误差界背景；（37.14）的有限顶点证明在本节完整给出，不归托未指明的论文定理。

## 37.99 追加锚

## 38. 完成循环边界、完整观察者与自然解码的界限

### 38.1 整份已获档案与三个概率对象

**定义 38.1（来源、完成标签及合法取得的联合合同）。** 保留第13节及定义37.1中的完整已获档案 $C$：内在与外部记录、来源身份与版本、已经取得的关系、可访问记忆、参考、动作及合法时间顺序，以及适用的相对钟约束，均以来源索引保留。第13节的记录商定理原本固定有限共同世界；若使用无限完成空间，另行指定一个共同可测空间、这些记录的可测映射及其实际联合律，不把有限世界定理无条件外推。

取[恢复卷定义33.1](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)的固定 $n\ge3$ 循环塔，其 $X_\infty=B_\infty^n$ 是这个完整观察者的一个任务读数。分清以下三种数据：$X_\infty$ 上的 Borel 标签律；在某个指定原来源或指定完成来源上表示的律；在固定准备、读出、全部已获档案和合法实验历史下实际取得的联合律。它们的关系须由明确映射给出。

具体地，给定可测来源 $(\Omega,\Sigma_\Omega,\rho)$ 和可测读出 $h:\Omega\to X_\infty$，实际标签律为 $h_*\rho$。若 $h,\rho$ 都固定，声称目标 $Q$ 是实际标签律的充要条件就是
$$
Q=h_*\rho.
\tag{38.1}
$$
逐点可达、有限边缘可达或 Borel 延拓存在均不替代此等式。若需要保留来源档案联合，则必须比较 $(C,h)_*\rho$，并在 $C$ 中保留上述所有已获成分，而非仅比较 $h_*\rho$。若所需记录尚未纳入共同可测模型，标签定理没有对这些未列出的联合关系作出保证。更换准备或读出属于另一个操作，须给其合法性和资源条件。

恢复卷 $F_l$ 只约束支撑、精确节点边缘和零剩余量。附加来源条件想使用其紧选择，须另证非空、紧性、投影保持及正确的完成联合语义；恢复卷命题33.16说明仅有限可满足及映入还不够。这里不引入新的来源保留完成最优化定理。

### 38.2 稠密原来源、固定准备与档案关联的三个障碍

**命题 38.2（每个有限词可达而公平完成律不可在原来源上实现）。** 取 $B_l=\{0,1\}^l$（$B_0$ 为单点）、前缀限制、$g_l=\mathrm{id}$、均匀 $\mu_l$、$n=3$ 和全支撑。每个 $F_l$ 是均匀对角律的单点，完成零面为公平无限位律的对角推前。令原来源 $\Omega$ 仅由最终恒零的二元序列组成，读出为对角嵌入，事件域取 $\Omega$ 的幂集。则来源在无限位空间中可数且稠密，每个有限目标词都可达，却没有任何来源概率能够实现全部均匀前缀律。

证明。恒等闭合置换的零剩余量要求零失败，故全对角；指定均匀节点边缘唯一确定各层律。恢复卷定理33.4及33.6给公平乘积律的对角延拓。任意有限词后接全零都在 $\Omega$ 中，故逐层的对角有限目标均可达，且对角像 $\Delta(\Omega)$ 在 $\Delta(B_\infty)$ 中稠密。若一个来源概率有全部均匀前缀，对每个 $x\in\Omega$、每个 $l$，单点包含于其长 $l$ 前缀柱，故 $\rho(\{x\})\le2^{-l}$，从而每个单点质量零。可数可加性便给 $\rho(\Omega)=0$，与概率总质量一矛盾。$\square$

这与主卷定理46.5的完成解不在原自然来源、以及定义91.1的实际像／闭包之别相接。全部有限标签可由不同来源点实现，不保证一个来源分布同时实现全部联合柱律。此例没有把来源完成后可承载的概率倒算为原来源已经具有的概率。

**命题 38.3（标签全部可达仍不保固定准备）。** 取二元翻转三循环的均匀割律 $D_0,D_2$，其不交支撑的并作为来源，读出为到标签元组的恒等映射。规定
$$
\rho=\tfrac34D_0+\tfrac14D_2,\qquad
Q=\tfrac12D_0+\tfrac12D_2.
\tag{38.2}
$$
目标只用可达元组，所有节点边缘仍均匀，且仍为最优律，但不等于固定准备的实际输出律。

证明。割律及混合的最优性来自恢复卷定理32.2–32.3。割 $0$ 扇区在实际律下质量 $3/4$，在 $Q$ 下质量 $1/2$，所以两律不同，TV 为 $1/4$。读出固定为恒等时（38.1）失败。$\square$

更换混合权重需要一个额外允许的准备操作；完成、可达支撑或相同边缘均不授权它。第37.4–37.5节的有限世界纤维抵消及来源满流判据仍按其有限合同使用，不能仅因标签完成而略去其中的来源条件。

**命题 38.4（相同标签律与相同档案边缘可有最大联合差）。** 令 $C$ 为已获公平位，$n=3$，比较联合律
$$
Y_0=Y_1=Y_2=C
\qquad\text{与}\qquad
Y_0=Y_1=Y_2=1-C.
\tag{38.3}
$$
两者的 $Y$ 律相同，$C$ 边缘相同，但 $(C,Y)$ 联合律的 TV 为一。

证明。两种 $Y$ 律均在 $000,111$ 上各放 $1/2$，档案均公平。第一律支撑于 $C=Y_0$，第二律支撑于 $C\ne Y_0$，支撑不交。$\square$

所以零任务标签误差不能认证完整观察者与既有记录的关联。逐坐标逆极限也不会自动补回未列入的来源—参考联合关系。此例还区分概率律与单次记录身份：即使两个输出具有完全相同的分布，它们在同一个已获 $C$ 下仍可逐次相反。重采一个同分布记录不等于保留原记录或原历史。

### 38.3 单层、全塔、来源与完成的体边对应

**命题 38.5（全尺度表示等价的范围）。** 在恢复卷定义33.1的载体、拓扑及事件合同下，一个相容的全部有限标签族确定一个完成线程，一个相容的全部有限联合概率族确定一个 Borel 律。一个有限读数一般只确定完成对象的一条纤维。对于额外指定原来源 $\Omega$ 及相容读数 $h_l$，令
$$
\iota:\Omega\to X_\infty,\qquad \iota(\omega)=(h_l(\omega))_l.
\tag{38.4}
$$
原来源集合与完整线程空间通过此映射等价，当且仅当读数分离原状态且每个线程由原状态实现；观察商的完成则识别为 $\overline{\iota[\Omega]}$，只有实际像稠密时才为全部 $X_\infty$。

证明。线程的各个坐标就是其定义数据，故全坐标唯一确定它；概率结论是恢复卷定理33.4。指定一层的实现集为 $(\pi_l^n)^{-1}\{z_l\}$，一般含多个线程。原来源映射的单射恰为分离性，满射恰为全部线程实际可实现，二者合取等价于双射。最后在可数有限坐标上取首差超度量，并拉回来源伪度量；零距离商等距于实际像，其完成为紧完备环境中的像闭包。这是[主卷定义91.1及定理91.2](RECURSIVE_RELATIONAL_OBSERVATION.md)的既有观察商与实际像构造。$\square$

这里“离散的全部相容边界”与“完成对象”可以是同一关系结构的两种表示；一个尺度、全塔、原来源与来源完成并非可任意替换的四个名字。[InverseLimitCompletion.lean](../../../D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean) 的 `stateThread_bijective_iff_complete_and_separates` 对应显式完备性及分离性这一类型层陈述；概率延拓由恢复卷的测度证明另负其责。

拓扑规定哪些读数相容、怎样逼近，不选取概率赋值。命题38.2中，原来源对角像的闭包是对角相容子空间 $\Delta(B_\infty)$，它通过对角嵌入与 $B_\infty$ 典范同胚；即使完成空间取这整个子空间，原来源仍不能承载其上的公平对角概率。正文24.12–24.15已经区分有限球、完整 p 进状态、额外 Haar 概率及实际取得；本节没有用分布存在替代取得无限档案或未来样本。完整观察者还包括其实际来源、参考和历史关系，只有将这些联合量明确纳入并证明对应，才能声称恢复了整个来源而非一个任务视图。

### 38.4 同一合法延续核如何消费联合误差

**命题 38.6（共同读出与共同随机核的 TV 运输）。** 给同一可测空间上的概率 $P,Q$，共同可测读出 $f$，或到同一输出可测空间的共同 Markov 核 $K$，则
$$
\operatorname{TV}(f_*P,f_*Q)\le\operatorname{TV}(P,Q),\qquad
\operatorname{TV}(PK,QK)\le\operatorname{TV}(P,Q).
\tag{38.5}
$$
此处的输入若用于保留完整观察者，必须是包含全部所需档案、来源关联与历史的联合律。

证明。确定读出的每个输出事件拉回为输入事件，给第一式。对核及输出事件 $A$，令 $u(x)=K(x,A)\in[0,1]$。层蛋糕积分给
$$
\int u\,dP-\int u\,dQ
 =\int_0^1\bigl(P\{u>t\}-Q\{u>t\}\bigr)\,dt,
\tag{38.6}
$$
故绝对值不超过 $\operatorname{TV}(P,Q)$。对 $A$ 取上确界得第二式。$\square$

有限非负行随机核的收缩已由 [DataProcessing.lean](../../../D5/S3/TotalVariation/DataProcessing.lean) 的 `total_variation_channel_le` 供应；上面的积分证明说明此处一般可测核的精确使用条件。恢复卷定理33.11选出的同一个完成见证，对每个符合本命题的共同核都保持同一全局误差界，不需要为每个输出任务重新选择另一最优律。它没有赋予该见证源世界实现，也没有保证一个有限算法能取得它。

自适应实验只有在其对完整档案的依赖、允许随机源及全部输入都已表示为双方相同的合法联合核时，才属于（38.5）。若核只读取标签，标签界可直接使用；若核读取 $C$ 或参考，必须先有对应联合界。两方使用不同机制，或遗忘实验实际读取的输入，均不满足此前提。合法操作次序与概率独立是不同条件；若声称新随机源独立，应针对完整 $C$ 条件化后检验，而非仅检验无条件边缘。

全局联合 TV 界不是每个档案事件上的统一条件界；条件使用还需该事件的正概率及相应分母控制，零概率事件不能直接条件化。含噪有限估计首先要针对同一个实际相容模型。如果需要同时使用所有层的概率证书，须在一个共同成功事件上结算；例如逐层失败概率 $\alpha_l$ 满足 $\sum_l\alpha_l\le\alpha$，可数并界给总失败概率至多 $\alpha$，不需独立性。它并不使无限多次测量免费或已经完成。

### 38.5 指定成对解码器的自然性方块

**定义 38.7（解码与尺度限制的交换要求）。** 令 $\mathcal D_l$ 为恢复卷定义32.10、式（32.25）–（32.28）的轨道平均成对解码器，各层使用已声明的合法割集合、节点边缘及默认。若欲让这些具体输出组成一个完成候选，须在一个共同声明的合法输入域上另证
$$
(q_l^n)_*\mathcal D_{l+1}(P)
 =\mathcal D_l((q_l^n)_*P).
\tag{38.7}
$$
输入与其投影须分别在两解码器的定义域，两个输出还须满足各自支撑及节点边缘合同。正归一化总量只保证除法有定义，不保证这个方块交换。恢复卷的共同半径选择是另一个存在性结论，不是这个解码器或它的实现算法。

**命题 38.8（模四到模二的正总量解码不自然）。** 取 $n=3$、$B_1=\mathbb Z/4\mathbb Z$、$B_0=\mathbb Z/2\mathbb Z$、$q(x)=x\bmod2$、两层 $g(x)=x+1$，全支撑、均匀节点边缘，三个割全部合法。每层只有一个非固定传递轨道且轨道质量一，所以恢复卷定义32.10的聚合计数正好是
$$
c_k(P)=P(Y_{k+1}=g^{-1}Y_k)\quad(k=0,1),\qquad
c_2(P)=P(Y_2=Y_0).
\tag{38.8}
$$
当 $s=\sum_kc_k>0$ 时，该解码器以 $c_k/s$ 作为均匀割律的权重。令模四元组律为
$$
U=\operatorname{Unif}\{(x,x+1,x+2):x\in B_1\},\qquad
D_2=\operatorname{Unif}\{(x,x,x):x\in B_1\},
$$
$$
P_1=(1-\epsilon)U+\epsilon D_2,\qquad
P_0=q_*^3P_1,\qquad0<\epsilon<1.
\tag{38.9}
$$
则细层解码为纯割 $2$，粗层解码权重为
$$
\frac{(1-\epsilon,1-\epsilon,1)}{3-2\epsilon}.
\tag{38.10}
$$
在 $\epsilon=1/2$ 时，两层总量分别为 $1/2,2$，且
$$
\operatorname{TV}\bigl(q_*^3\mathcal D_1(P_1),\mathcal D_0(P_0)\bigr)=\tfrac12,
\qquad R_1(P_1)=R_0(P_0)=1.
\tag{38.11}
$$

证明。各列都是均匀 $x$ 的置换，两层输入边缘精确；半共轭及全支撑保证输入投影合法，全部割输出也合法。恢复卷式（32.25）按 $x$ 求和就是（38.8），式（32.28）的 $w_O=1$，故得到所写权重，没有替换归一化单位。

模四下 $x+1\ne x-1$，$x+2\ne(x+1)-1=x$，且 $x+2\ne x$，故 $c(U)=(0,0,0)$；对角律只击中闭合对角检测，故 $c(D_2)=(0,0,1)$。因此 $c(P_1)=(0,0,\epsilon)$，细层解码为 $D_2$。

$U$ 的粗投影为 $(y,1-y,y)$，模二下 $g^{-1}=g$，它满足全部三个检测事件。粗对角律只满足第三个，故 $c(P_0)=(1-\epsilon,1-\epsilon,1)$，总量 $3-2\epsilon$，得到（38.10）。在 $\epsilon=1/2$，粗权重为 $(1/4,1/4,1/2)$。纯细割 $2$ 投影为纯粗割 $2$；粗层三个非固定割扇区两两不交，故输出 TV 等于权重向量的半 $\ell^1$ 距离，即 $1/2$。

两层 $U$ 均有三条失败边，移动锚指标一；$D_2$ 仅闭合边失败，剩余量零。剩余量对同一律的混合线性，所以两层均为 $2(1-\epsilon)$，得到（38.11）。细层以上保持全部模型数据并用恒等限制，便得到一个完整相容塔。$\square$

粗投影可创造新的检测命中，所以即使双方归一化始终合法，归一化权重也不必相容。在这个单传递非固定轨道模型中，均匀细割恰投为对应均匀粗割，且粗割扇区不交；因此（38.7）等价于两个归一化计数向量相等，也等价于两个正总量计数向量正比例。若投影合并轨道，或把若干割压成固定对角，须先聚合实际推前测度再比较，不能沿用逐分量比例判据。

恢复卷命题33.8还说明：任何试图在所有合法输入上逐层选取最近点的规则，都不能仅靠改变并列最优时的选取方式取得普遍自然性。该例两层最近点都唯一而不相容。共同半径内存在一个相容最优完成见证与这些障碍并不冲突。

### 38.6 延迟细化与有限停止的不可判别前缀

**命题 38.9（没有统一有限深度的完成误差停止证书）。** 对任意预先指定的有限检查深度 $M$，存在两座满足恢复卷定义33.1的塔及各自的实际相容律，在所有 $l\le M$ 的载体、边缘、置换、支撑及联合律，以及 $0\le l<M$ 的内部限制映射上相同，且这些有限最近距离全为零；但两者完成最近距离分别为零和一。

证明。前 $M+1$ 层都取二元翻转三循环、全支撑、均匀节点边缘、恒等限制，并取均匀割 $0$ 为实际律。一座塔永久保持这些数据，实际完成律就在零面，完成距离零。

另一座塔在层 $M+1$ 放入恢复卷命题33.8的模四模型：置换加一、均匀边缘、支撑为该处（33.17），实际律均匀于 $(x,x-1,x+1)$，$q_M(x)=x\bmod2$。此律下投影恰为前面已固定的粗割 $0$，故整族相容。更高层复制此细模型并用恒等限制。由该命题，层 $M+1$ 及以上最近距离一，完成最近距离一。两座塔的已检查前缀完全相同。$\square$

因此仅凭任何有限前缀都不能普遍认证完成距离小于一；若一个仅观察前缀的确定停止程序在永久粗塔上于有限层认证小误差，同一前缀后的延迟细化塔就推翻其认证。额外尾部信息可改变这个问题，定理本身没有提供这种信息、统一收敛模、有限取得成本、运行时或样本界。这里的不可判别性来自两个具体塔，不是从尚未找到停止算法推断不存在算法。

### 38.7 共同来源的组合条件与尺度的语义

主卷第124.9节的共同分支条件、第124.10节的共同联合权重求和仍是组合的前提：两份边界可以分别有完成律，而未必来自同一实际来源、同一分支或同一份档案。保留整个相容联合塔才支持恢复卷的柱 TV 等式；单独坐标上的延拓不能清除未列入的联合义务。恢复卷第3.2–3.4节的联合合法状态区别及第9.3节的值／实现收敛区别，在这里分别表现为来源提升、档案关联与指定解码器相容性的独立条件。

共同来源上的等核规范运输还满足主卷命题133.1的 cocycle 恒等式：若 $h_{ij}(q_i\omega)=q_j\omega$ 且这些读数核相同，则 $h_{jk}h_{ij}=h_{ik}$，绕坐标循环的复合为恒等。本节循环约束中的非平凡闭合置换 $g$ 是另行规定的关系数据，并非这种规范等核运输的反例。

层指标 $l$ 表示分辨率，不是物理钟或执行次数。恢复卷的定理固定同一个有限 $n$；跨尺度相容不等于所有时间长度上的联合相容。只有经典标签 Borel 律及 TV 的结论，也不提供量子外部参考安全、动态共轭、物理波方程、熵产生、时间涌现或稳定内部参数识别。第36节的共同量子记忆与参考合同、第37节的实际档案／合法准备和其他相对钟、动力学接口，各自继续要求其原有的联合实现、允许操作、误差及资源条件。

这一体边对应具体连接的是有限联合关系、全尺度相容边界、完成概率及一个共同半径中的恢复见证。比较对象若是整个来源与完整观察者，就必须把全部已获记录、来源关系和历史同时保留在相应联合模型中；用任务摘要替换它们会改变问题。命题38.2–38.4给出的来源承载、固定准备及记录身份障碍，均不因拓扑完成而消失。

## 38.99 追加锚

## 39. 保留共同来源的完成化、最优世界总变差与抵消缺口

### 39.1 同一世界、标签与联合来源的可数塔

**定义 39.1（声明来源的完成化合同）。** 对每个 $l\in\mathbb N_0$，给有限非空离散空间 $W_l,Z_l,U_l$，以及处处定义的连接映射
$$
\alpha_l:W_{l+1}\to W_l,\qquad
\beta_l:Z_{l+1}\to Z_l,\qquad
\gamma_l:U_{l+1}\to U_l.
$$
不要求任何连接映射满射。标签读出 $\lambda_l:W_l\to Z_l$、来源读出 $\sigma_l:W_l\to U_l$ 满足
$$
\lambda_l\alpha_l=\beta_l\lambda_{l+1},\qquad
\sigma_l\alpha_l=\gamma_l\sigma_{l+1}.
\tag{39.1}
$$
写 $W_\infty=\varprojlim(W_l,\alpha_l)$，并同样定义 $Z_\infty,U_\infty$；均取紧可度量逆极限拓扑及其 Borel $\sigma$ 代数。坐标记为 $\pi_l^W,\pi_l^Z,\pi_l^U$。交换式逐坐标诱导连续读出 $\lambda_\infty:W_\infty\to Z_\infty$、$\sigma_\infty:W_\infty\to U_\infty$。

固定一个实际 Borel 概率 $\rho_\infty$，只用它的投影 $\rho_l=(\pi_l^W)_*\rho_\infty$，并定义
$$
P_l=(\lambda_l)_*\rho_l,\quad \nu_l=(\sigma_l)_*\rho_l,\qquad
P_\infty=(\lambda_\infty)_*\rho_\infty,\quad
\nu_\infty=(\sigma_\infty)_*\rho_\infty.
\tag{39.2}
$$
$U_l$ 是该层所声明全部来源条目的联合取值空间，$\nu_l$ 是它们的联合律；分别列出来源边缘会定义一个较弱的问题。各层实际律来自这同一个实际对象，不能独立拟合后只保留若干相同边缘。

给定相容目标概率 $(\beta_l)_*Q_{l+1}=Q_l$；其唯一完成 Borel 律 $Q_\infty$ 由定理39.3构造。给合法世界集合 $A_l\subseteq W_l$，满足
$$
\alpha_l(A_{l+1})\subseteq A_l,\qquad
A_\infty=\bigcap_{l\ge0}(\pi_l^W)^{-1}(A_l).
\tag{39.3}
$$
有限及完成准入类规定为全部且仅有
$$
\begin{aligned}
\mathcal L_l=\{\theta_l\in\operatorname{Prob}(W_l):\;&
(\lambda_l)_*\theta_l=Q_l,\quad
(\sigma_l)_*\theta_l=\nu_l,\quad\theta_l(A_l)=1\},\\
\mathcal L_\infty=\{\theta\in\operatorname{Prob}_{\rm Borel}(W_\infty):\;&
(\lambda_\infty)_*\theta=Q_\infty,\quad
(\sigma_\infty)_*\theta=\nu_\infty,\quad\theta(A_\infty)=1\}.
\end{aligned}
\tag{39.4}
$$
假设对每个 $l$ 都有 $\mathcal L_l\ne\varnothing$。这是来源、目标和支撑的同时可行性，不由各边缘分别可行推出。概率允许任意实数质量及零质量；例子的严格正性不是一般前提。若改为要求所有候选逐点严格正，闭性和最小值达到性可能丢失。

实际合法性 $\rho_\infty(A_\infty)=1$ 不属于下述距离定理的必要假设。将实际律作为可行候选或合法供给律时，须另加相应合法性及目标条件。额外的档案、参考、准备、机制或原来源限制，须以自己的非空紧有限类、投影保持及准确完成语义接入；称 $U$ 为联合来源不证明全部已获关系已被纳入。任意 $W_l$ 不是字面上的循环元组字母表 $B_l^n$；本节不假设循环置换、割支撑或循环剩余量。

**命题 39.2（已获标签的来源因子化障碍）。** 若某层 $\lambda_l=f_l\sigma_l$，则有限可行性强制 $Q_l=P_l$。若另有 $\rho_l(A_l)=1$，实际律即为可行候选，最小世界距离为零。在完成层，若有可测 $f_\infty:U_\infty\to Z_\infty$ 使 $\lambda_\infty=f_\infty\sigma_\infty$，同样强制 $Q_\infty=P_\infty$；再加实际合法性才得到零最小距离。

证明。对任一有限可行 $\theta_l$，
$$
Q_l=(\lambda_l)_*\theta_l=(f_l)_*(\sigma_l)_*\theta_l
=(f_l)_*\nu_l=(\lambda_l)_*\rho_l=P_l.
\tag{39.5}
$$
加上实际合法性后，$\rho_l$ 满足（39.4）的全部条件，且到自身距离为零。完成情形使用同一推前等式及可行类非空性，证明相同。$\square$

因此已经由保留档案确定的标签不能在声称保留该档案时改成不同目标。非平凡修复只能针对尚未固定的任务变量、完整记录合同中仍有的不确定性，或另有等价及取得条件的新表示。实际合法性本身不使任意目标的费用为零；也不授权改写已经取得的事件及其来源。

### 39.2 非满射延拓与同一半径中的最优世界律

**定理 39.3（声明来源下的达到最小值与有限上确界）。** 在定义39.1下，每个有限最小值及完成最小值都存在且达到。采用有限概率的 $\operatorname{TV}(p,q)=\frac12\sum_w|p(w)-q(w)|$、Borel 概率的 $\operatorname{TV}(p,q)=\sup_E|p(E)-q(E)|$，记
$$
d_l=\min_{\theta_l\in\mathcal L_l}\operatorname{TV}(\rho_l,\theta_l),\qquad
d_\infty=\min_{\theta\in\mathcal L_\infty}\operatorname{TV}(\rho_\infty,\theta).
\tag{39.6}
$$
则
$$
\boxed{\mathcal L_\infty\ne\varnothing,\qquad
 d_l\uparrow d_\infty=\sup_{l\ge0}d_l.}
\tag{39.7}
$$
对任意固定 $c\ge0$，所有有限层各有距离不超过 $c$ 的可行律，当且仅当有一个完成可行律的距离不超过 $c$。

证明分为以下四个应用检查。紧选择、弱拓扑识别、柱事件逼近及共同半径方法分别使用[恢复卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)引理33.3、定理33.6、33.9、33.11及推论33.12的相应证明步骤；世界、来源及非满射载体条件在这里逐项履行。

#### 39.2.1 有限类的紧性与投影保持

$\mathcal L_l$ 是有限概率单纯形与标签、来源仿射等式及 $A_l$ 外坐标为零条件的交，故为紧凸多面体，且由假设非空。对任一 $\theta_{l+1}\in\mathcal L_{l+1}$，
$$
\begin{aligned}
(\lambda_l)_*(\alpha_l)_*\theta_{l+1}
 &=(\beta_l)_*(\lambda_{l+1})_*\theta_{l+1}
   =(\beta_l)_*Q_{l+1}=Q_l,\\
(\sigma_l)_*(\alpha_l)_*\theta_{l+1}
 &=(\gamma_l)_*(\sigma_{l+1})_*\theta_{l+1}
   =(\gamma_l)_*\nu_{l+1}=\nu_l.
\end{aligned}
\tag{39.8}
$$
最后一个来源等式使用实际律的相容性。由（39.3），该推前在 $A_l$ 上质量为一，所以
$$
(\alpha_l)_*\mathcal L_{l+1}\subseteq\mathcal L_l.
\tag{39.9}
$$
这些限制映射连续仿射，不必满射。恢复卷引理33.3适用于这组非空紧 Hausdorff 空间，给一个相容候选族；它是 Stacks 0A2R 的可数链情形。[^rroctx39_stacks] 此结论不保证任意预定有限候选可延伸。概率多面体通常有无限多个点，不能以“字母表有限”为由把要求对象载体有限的线程定理直接用于它们。

#### 39.2.2 Fremlin 418Q 的非满射概率延拓检查

对选出的相容族 $\theta_l$，每个 $(W_l,\mathcal P(W_l),\theta_l)$ 配有限离散拓扑，是完全、局部确定、Hausdorff、局部有限且对紧集内正则的 Radon 概率空间。$\alpha_l$ 连续，故 almost continuous；并且对任意 $E\subseteq W_l$，
$$
\theta_{l+1}(\alpha_l^{-1}E)=\theta_l(E).
\tag{39.10}
$$
这是 inverse-measure-preserving 条件。Fremlin 418Q 对这样的序列给实际线程空间上的唯一相容 Radon 概率。[^rroctx39_fremlin] 按其411H的完全 Radon 约定，取所得概率的 Borel 限制作为本节的 $\theta$；有限坐标开闭柱生成 $W_\infty$ 的 Borel $\sigma$ 代数，故指定柱概率唯一确定这个 Borel 限制。对 $(Z_l,Q_l,\beta_l)$ 逐项作同一检查，构造 $Q_\infty$。来源完成律已由实际推前 $\nu_\infty$ 给定。

这里没有满射假设，也没有把恢复卷定理33.4依赖投影满射的柱预测度证明删去前提后套用。使用的是418Q，不是不加限定的418O；结论也不扩张至任意额外指定的可测事件域。

零质量点解释了非满射时的空柱。令 $\alpha_{l:m}=\alpha_l\cdots\alpha_{m-1}$，$\alpha_{l:l}=\mathrm{id}$。对固定 $l$，每个相容概率族在 $\alpha_{l:m}(W_m)$ 上质量为一。这些有限集合随 $m\ge l$ 递减，其交恰为可延伸的 $l$ 层坐标：一方向由线程投影成立；另一方向，对交中一点，任意有限组线程方程及指定坐标可用足够高层的一个提升满足，恢复卷引理33.3所用的紧乘积有限交论证遂给完整线程。因此不能延伸的点必有零相容质量，空柱不造成概率冲突，不必删掉零质量载体点。

#### 39.2.3 完成可行类的精确识别

上述延拓的标签推前满足
$$
(\pi_l^Z)_*(\lambda_\infty)_*\theta
=(\lambda_l)_*(\pi_l^W)_*\theta=Q_l.
\tag{39.11}
$$
柱唯一性给 $(\lambda_\infty)_*\theta=Q_\infty$。来源推前同理等于 $\nu_\infty$；每个合法柱质量一，可数交仍质量一，故 $\theta(A_\infty)=1$。这证明延拓在 $\mathcal L_\infty$ 中。

反向，任意 $\theta\in\mathcal L_\infty$ 的坐标投影保持两个读出等式，且 $A_\infty\subseteq(\pi_l^W)^{-1}A_l$，故属于每个 $\mathcal L_l$。于是得到精确仿射双射
$$
\mathcal L_\infty\cong
\varprojlim\bigl(\mathcal L_l,(\alpha_l)_*\bigr).
\tag{39.12}
$$
它在概率弱拓扑下为同胚：坐标开闭柱的指示函数连续，给正向连续；恢复卷定理33.6以共同有限柱分割一致逼近连续函数的论证给逆向连续。该论证只在非空柱分块选函数值，不要求坐标满射。右侧是紧乘积的闭子集，因此 $\mathcal L_\infty$ 弱紧。也可直接看出 $A_\infty$ 闭、固定连续推前条件弱闭。完整相容族确定唯一概率，不等于最优族唯一、原世界唯一或 TV 弱连续。

#### 39.2.4 柱 TV、单调距离与共同半径

实际逆极限上的开闭柱仍构成生成 Borel 事件的代数，有限组柱总能在同一较高层表达。对有限测度 $\rho_\infty+\theta$，恢复卷定理33.9的生成代数事件逼近论证因此适用，给
$$
\operatorname{TV}(\rho_\infty,\theta)
=\sup_l\operatorname{TV}\bigl(\rho_l,(\pi_l^W)_*\theta\bigr).
\tag{39.13}
$$
原先满射条件用于柱内容赋值，不用于此 Borel 逼近步骤。式（39.13）亦适用于共同的 $(\rho_\infty+\theta)$-完成事件域；任意未声明的更大事件域不在内。右侧是弱连续有限目标的上确界，故完成 TV 弱下半连续，一般不弱连续。

有限 TV 连续，有限最小值达到。对任意细层可行律，用（39.9）、实际相容性及有限确定通道收缩，得
$$
d_l\le\operatorname{TV}(\rho_l,(\alpha_l)_*\theta_{l+1})
\le\operatorname{TV}(\rho_{l+1},\theta_{l+1}).
\tag{39.14}
$$
所以 $d_l\le d_{l+1}$。所用有限收缩由 `total_variation_channel_le` 供应，确定核为 $\mathbf1_{\alpha_l(w)=v}$，非负且每行和一。置 $c=\sup_l d_l\in[0,1]$，定义共同半径集
$$
\mathcal G_l(c)=\{\theta_l\in\mathcal L_l:
          \operatorname{TV}(\rho_l,\theta_l)\le c\}.
\tag{39.15}
$$
各集非空紧，且由（39.14）映入前层。再次应用紧选择及39.2.2的延拓检查，得到同一个 $\theta^*\in\mathcal L_\infty$。式（39.13）给其距离不超过 $c$。任意完成可行律投影于每个有限类，距离又至少每个 $d_l$，故至少 $c$。这证明（39.7）和达到性。

对任意共同半径 $c\ge0$，若每个 $\mathcal G_l(c)$ 非空，同一论证给半径内的完成律；反向由投影收缩。这并不声称按各自最小半径独立选出的有限 argmin 相容，也不是不附条件地交换 $\sup$ 与 $\min$。$\square$

**命题 39.4（非满射与零质量载体的边界）。** 取所有 $W_l=\{0,1\}$、$\alpha_l\equiv0$，标签及来源均为单点，$A_l=W_l$，实际律为唯一线程 $(0,0,\ldots)$ 的点质量。则各有限可行类为整个二点概率单纯形，而其连接映射恒为 $\delta_0$，不满射；完成可行类仅有上述实际点律，所有最近距离为零。

证明。每个线程的每个坐标都被下一坐标映到零，故线程空间仅有全零点。有限目标和来源条件只要求总质量一，所以有限类确为整个单纯形。相容族必须在每层等于 $\delta_0$；载体点 $1$ 的柱为空且相容质量零。实际律在所有层可行，到自身距离零。全部非空、紧性、读出交换和支撑保持条件均满足。$\square$

### 39.3 标签距离、额外费用及全尺度量词

**命题 39.5（两个单调极限的差）。** 在定义39.1下，置
$$
\tau_l=\operatorname{TV}(P_l,Q_l),\qquad
\tau_\infty=\operatorname{TV}(P_\infty,Q_\infty),\qquad
g_l=d_l-\tau_l,\quad g_\infty=d_\infty-\tau_\infty.
\tag{39.16}
$$
则 $\tau_l\uparrow\tau_\infty$，且
$$
0\le\tau_l\le d_l\le1,\qquad
0\le\tau_\infty\le d_\infty\le1,\qquad
\boxed{g_\infty=\lim_l g_l=\sup_l d_l-\sup_l\tau_l.}
\tag{39.17}
$$
差 $g_l$ 一般既不递增也不递减，不能以 $\sup_l g_l$ 代替其极限。若 $\tau_\infty>0$，则 $\tau_l$ 最终正且 $d_l/\tau_l\to d_\infty/\tau_\infty$，但没有一般的比值上确界公式。

证明。在标签逆极限上应用39.2.4的柱 TV 检查及投影收缩，得 $\tau_l$ 的单调收敛。对每个可行律经 $\lambda_l$ 或 $\lambda_\infty$ 推前，TV 收缩给标签下界；概率 TV 至多一。定理39.3使两个单调数列都收敛，相减即得（39.17），正分母的比值结论由商的极限法则得到。命题39.9–39.11给出差的两个变化方向及比值上确界失败的具体实现。$\square$

若 $\tau_\infty=0$，各层标签距离也为零，比值没有定义，加法费用仍有意义。此时 $Q_\infty=P_\infty$；只有另加实际合法性，$\rho_\infty$ 才属于 $\mathcal L_\infty$ 并给 $d_\infty=0$，所得 $0/0$ 仍未定义。合法性不能遗漏：取恒等世界塔 $W_l=\{0,1\}$，单点标签、单点来源，实际律 $\delta_0$，合法集 $A_l=\{1\}$，目标为唯一标签律。每层及完成层唯一合法候选为 $\delta_1$，所以 $\tau_l=\tau_\infty=0$，$d_l=d_\infty=1$。这直接由不交点质量的 TV 为一证明；定理39.3容许该比较律，要求实际合法供给的流解释则不容许。

**命题 39.6（完成等距离的共同半径判据）。** 下列条件等价：
$$
\begin{aligned}
d_\infty=\tau_\infty
&\iff \exists\theta\in\mathcal L_\infty:
     \operatorname{TV}(\rho_\infty,\theta)=\tau_\infty\\
&\iff \forall l,\ d_l\le\tau_\infty\\
&\iff \forall l,\ \mathcal G_l(\tau_\infty)\ne\varnothing\\
&\iff \lim_l g_l=0.
\end{aligned}
\tag{39.18}
$$
此外，对每个 $\epsilon\ge0$，
$$
\begin{aligned}
g_\infty\le\epsilon
&\iff \forall l,\ d_l\le\tau_\infty+\epsilon\\
&\iff \forall\eta>0\ \exists N\ \forall l\ge N,\
               d_l\le\tau_l+\epsilon+\eta.
\end{aligned}
\tag{39.19}
$$

证明。（39.18）的第一步使用最小值达到及标签收缩下界；第二步使用 $d_\infty=\sup_l d_l$；第三步使用有限最小值达到；最后一步使用（39.17）。式（39.19）的第一步仍由上确界公式。若 $g_\infty\le\epsilon$，收敛保证对任意 $\eta>0$ 最终有 $g_l\le\epsilon+\eta$；反向，把每个这样的最终不等式取极限，再令 $\eta\downarrow0$，得 $g_\infty\le\epsilon$。$\square$

式（39.18）在每一层使用同一个半径 $\tau_\infty$，不是各自的 $\tau_l$。若所有层，或只在一个无界共尾层集上，有 $d_l=\tau_l$，则收敛的 $g_l$ 有零子序列，完成等距离成立；命题39.9证明全层有限等距离并非必要。有限等距离候选集合也未必被投影保持。这些是全尺度断言，不能当作有限停止程序。

若某一层 $\tau_l=\tau_\infty$，且完成等距离成立，则
$$
\tau_l\le d_l\le d_\infty=\tau_\infty=\tau_l,
\tag{39.20}
$$
该层必等距离。特别地，若所有标签限制对这一个实际／目标概率对都保 TV，则 $\tau_l$ 全相等，逐层等距离与完成等距离等价；这是额外的无抵消条件，不是定义39.1的默认性质。

### 39.4 有限符号约束与合法来源流的准确适用域

**命题 39.7（有限等距离的线性可行条件）。** 固定一层，令未知有符号质量 $h:W_l\to\mathbb R$，并置 $e(z)=Q_l(z)-P_l(z)$。则 $d_l=\tau_l$ 当且仅当以下条件同时可满足：
$$
\begin{cases}
h(w)\ge0,&e(\lambda_l(w))>0,\\
h(w)\le0,&e(\lambda_l(w))<0,\\
h(w)=0,&e(\lambda_l(w))=0,
\end{cases}
\tag{39.21}
$$
$$
\sum_{\lambda_l(w)=z}h(w)=e(z),\qquad
\sum_{\sigma_l(w)=u}h(w)=0,\qquad
\rho_l(w)+h(w)\ge0,
\tag{39.22}
$$
$$
\rho_l(w)+h(w)=0\quad(w\notin A_l).
\tag{39.23}
$$
这些条件保留零质量世界及中性标签纤维，且不要求实际律合法。

证明。若 $d_l=\tau_l$，取达到者 $\theta_l$，设 $h=\theta_l-\rho_l$。用既有 `total_variation_channel_eq_iff_no_sign_mixing`，取有限确定核 $K(w,z)=\mathbf1_{\lambda_l(w)=z}$，其每项非负、每行和一。定理说明 TV 等号恰要求每个标签纤维不混合正负差。结合纤维总差为 $e(z)$，正总差只能逐点非负，负总差只能逐点非正，零总差则逐点零，正是（39.21）；（39.22）–（39.23）由准入条件得到。这也正是命题37.8及（37.15）–（37.16）的确定读出情形，不另证明一般等号机制。

反向，设这些式子成立，定义 $\theta_l=\rho_l+h$。它非负、合法，标签平衡给 $Q_l$，对全部标签求和给总质量一；来源平衡给 $\nu_l$。于是它可行，（39.21）经同一个既有等号定理给世界 TV 为 $\tau_l$。结合标签下界，便有 $d_l=\tau_l$。$\square$

在实际合法的情形 $\rho_l(A_l)=1$，精确匹配定理37.10的方法是把它的世界载体取为 $W'=A_l$，实际律取 $\rho_l|_{A_l}$，标签、来源映射均限制到 $A_l$；候选在 $W_l\setminus A_l$ 置零。这不改变任何实际或候选距离、标签边缘或来源边缘，并使该定理“载体上全部且仅有指定来源边缘的概率律”前提成立。

具体地，亏损标签集为 $D=\{z:e(z)<0\}$，盈余标签集为 $R=\{z:e(z)>0\}$。在亏损世界置 $r_w=-h(w)$，在盈余世界置 $t_v=h(v)$。则 $0\le r_w\le\rho_l(w)$、$t_v\ge0$，只允许合法世界接收；合法零实际质量世界也可接收。标签移除和加入总量分别为 $-e(z)$、$e(z)$，中性标签逐点不变。每个联合来源值 $u$ 内的总移除与总加入相等。

定理37.10的（37.17）在这里取
$$
r_{z,u}=\sum_{\substack{w\in A_l\\\lambda_l(w)=z,\ \sigma_l(w)=u}}\rho_l(w),\qquad
W'_{z,u}=A_l\cap\lambda_l^{-1}\{z\}\cap\sigma_l^{-1}\{u\}.
\tag{39.24}
$$
其网络容量依次为源到亏损标签的 $-e(z)$、亏损标签到来源的 $r_{z,u}$、来源到盈余标签的 $\tau_l$（仅当 $W'_{z,u}\ne\varnothing$ 有此弧）、盈余标签到汇的 $e(z)$。达到值 $\tau_l$ 的满流与（39.21）–（39.23）等价。其证明中的来源内分配可在本符号下写为：对共同来源的亏损世界 $w$ 和合法盈余世界 $v$，若该来源总移除为 $M_u>0$，取 $F_{wv}=r_wt_v/M_u$；若 $M_u=0$，全取零。来源平衡给行和 $r_w$、列和 $t_v$。反向由这类流的行列和恢复 $h$。零来源供给没有除法；初始零质量的非空合法接收格仍可接收。一般有限耦合提升不替代这些支撑、容量及来源条件。

这个流判据判断的是 $d_l=\tau_l$，不是较弱的全局条件 $d_l\le\tau_\infty$。细标签能够分开粗标签内互相抵消的变化，所以细层等距离候选投到粗层后可有严格世界／标签缺口。

若实际律不合法，须保留命题39.7的有符号形式，不能原样套用上述载体限制。式（39.23）强制非法世界 $h(w)=-\rho_l(w)$。若此处实际质量正，等距离就要求它属于亏损标签并移除全部质量，即 $r_w=\rho_l(w)$；非法中性或盈余世界有正实际质量时，等距离不可能。非法零质量世界仍为零、不能接收。这些结论直接由（39.21）和（39.23）得出；它们不把非法实际律当成合法供给律。

### 39.5 同一四世界实现中的两种相反细化

**定义 39.8（四世界共同数据）。** 世界按 $(w_{a0},w_{a1},w_{b1},w_{b2})$ 排列；实际律 $\rho$ 及指定候选 $\bar\theta$、共同来源、两种标签读出规定如下。表39.1的所有世界均合法；世界集合仅有这四个来源／标签关联，不是整个 $U\times Z$。

| 表39.1世界 | 联合来源 | 粗标签 | 分裂标签 | 实际 $\rho$ | 候选 $\bar\theta$ |
|---|---|---|---|---:|---:|
| 39.1a $w_{a0}$ | $a$ | $0$ | $0$ | $3/8$ | $1/4$ |
| 39.1b $w_{a1}$ | $a$ | $1$ | $1_a$ | $1/8$ | $1/4$ |
| 39.1c $w_{b1}$ | $b$ | $1$ | $1_b$ | $3/8$ | $1/4$ |
| 39.1d $w_{b2}$ | $b$ | $2$ | $2$ | $1/8$ | $1/4$ |

目标标签律在各层均取 $\bar\theta$ 的读出推前，实际标签及来源律均取同一 $\rho$ 的推前。世界连接映射在以下各塔中恒为恒等，所以 $W_\infty$ 典范识别为这同一个四世界集合；上述两律同时给出一个实际完成律和一个相容可行完成律。所有显示的质量严格正。

**命题 39.9（分裂标签使有限正缺口消失）。** 第0层取粗标签 $\{0,1,2\}$，第1层起取分裂标签 $\{0,1_a,1_b,2\}$；$\beta_0$ 合并 $1_a,1_b$ 为 $1$，其余标签不变，以后恒等。所有层的来源均为 $\{a,b\}$，来源连接恒等。则
$$
\begin{aligned}
P_0&=(3/8,1/2,1/8),&Q_0&=(1/4,1/2,1/4),\\
d_0&=1/4,&\tau_0&=1/8,&g_0&=1/8,\\
d_l&=1/4,&\tau_l&=1/4,&g_l&=0\quad(l\ge1),\\
d_\infty&=\tau_\infty=1/4,&g_\infty&=0.
\end{aligned}
\tag{39.25}
$$

证明。两层读出交换逐世界成立，来源实际及候选质量都是 $(1/2,1/2)$。粗层端点标签 $0,2$ 各只有一个世界，所以可行候选必须在 $w_{a0},w_{b2}$ 各放 $1/4$。来源质量各为 $1/2$ 又迫使另外两个世界各为 $1/4$；故 $\mathcal L_0=\{\bar\theta\}$。四个差依次为
$$
\bar\theta-\rho=(-1/8,+1/8,-1/8,+1/8),\qquad
Q_0-P_0=(-1/8,0,+1/8).
\tag{39.26}
$$
世界 TV 为 $1/4$，粗标签 TV 为 $1/8$。粗标签1内的两项差 $+1/8,-1/8$ 抵消，总差零却没有逐点不变，违反（39.21）的中性条件，故不存在粗层等 TV 流。

细层标签读出单射，目标强制候选仍为 $\bar\theta$，此时标签没有抵消，TV 与世界 TV 均为 $1/4$。其后恒等，定理39.3和命题39.5给完成数值。$\square$

可行类连接是两个单点间的双射，现象不来自可行映射不满射。这里 $g_\infty=0<\sup_l g_l=1/8$；粗层比值为2、完成比值为1，故比值的上确界也不是完成比值。它同时证明完成等距离不要求所有有限层等距离，细层等距离候选的粗投影可不等距离。

**命题 39.10（细化来源使零缺口变正）。** 保持定义39.8的世界、实际律、粗标签及目标 $(1/4,1/2,1/4)$。第0层来源为单点，第1层起来源读出为 $a/b$，$\gamma_0$ 把两者送到单点，其余连接恒等。则
$$
(d_0,\tau_0,g_0)=(1/8,1/8,0),\qquad
(d_l,\tau_l,g_l)=(1/4,1/8,1/8)\quad(l\ge1),
\tag{39.27}
$$
完成值为 $(d_\infty,\tau_\infty,g_\infty)=(1/4,1/8,1/8)$。

证明。所有读出交换仍成立。粗层的整个可行类可写成
$$
\theta(x)=(1/4,x,1/2-x,1/4),\qquad 0\le x\le1/2.
\tag{39.28}
$$
它与实际律的四项差为 $(-1/8,x-1/8,1/8-x,+1/8)$，故
$$
\operatorname{TV}(\rho,\theta(x))=1/8+|x-1/8|.
\tag{39.29}
$$
因此唯一粗层最优候选
$$
\theta^{(0)}=(1/4,1/8,3/8,1/4)
\tag{39.30}
$$
达到标签下界 $1/8$；中间两个世界不变，符合中性纤维条件。它的细来源质量却为 $(3/8,5/8)$，不等于实际 $(1/2,1/2)$。第1层来源保留强制 $x=1/4$，即唯一候选 $\bar\theta$，由（39.29）得距离 $1/4$。标签一直粗，距离一直 $1/8$；恒等续接给完成值。$\square$

**命题 39.11（共同三层塔的缺口先升后降）。** 在同一四世界上，先细化来源、再分裂标签，形成表39.2的塔；世界律始终为定义39.8的同一 $\rho$，目标始终为同一 $\bar\theta$ 的标签推前。

| 表39.2层 | 来源视图 | 标签视图 | $d_l$ | $\tau_l$ | $g_l$ |
|---|---|---|---:|---:|---:|
| 39.2a 第0层 | 单点 | 粗标签 | $1/8$ | $1/8$ | $0$ |
| 39.2b 第1层 | $a/b$ | 粗标签 | $1/4$ | $1/8$ | $1/8$ |
| 39.2c 第2层及以后 | $a/b$ | 分裂标签 | $1/4$ | $1/4$ | $0$ |

这是一座满足定义39.1全部条件的塔，而 $g_l$ 为 $0,1/8,0,0,\ldots$，故没有任一方向的一般单调性。

证明。世界连接恒等；$\gamma_0$ 合并来源、以后恒等；$\beta_0$ 恒等、$\beta_1$ 合并分裂标签、以后恒等。逐世界读出平方交换，全支撑向下保持。第0层可行类是（39.28），第1层及以后为 $\{\bar\theta\}$，故非空紧并被投影保持；其中 $\bar\theta$ 是一份共同可行线程。两种距离分别由命题39.10的前两层、命题39.9的细层给出。完成来源与标签都是最终视图，实际及候选均没有换律。$\square$

这些层是同一个完成来源合同的不同有限表示。若 $a/b$ 记录已经取得，单点来源问题只是一种数学松弛，其较便宜的 $\theta^{(0)}$ 不是完整观察者的合法修复。细化不能授权删除已获记录；第0层的数值下界与第1层的实际约束属于不同的有限可行问题。

**命题 39.12（延迟细化的共同有限前缀）。** 对任意 $N\ge0$，可以有两座塔在全部 $l\le N$ 的载体、读出、实际律、目标、来源律、合法支撑及前缀内部连接完全相同，完成额外费用却分别为 $1/8$ 和零。也可以令共同前缀的所有费用缺口为零，而两种完成费用分别为零和 $1/8$。

证明。第一对塔把命题39.9的粗层重复至 $N$。一座永远保持粗标签，完成类为 $\{\bar\theta\}$，距离为 $d_\infty=1/4,\tau_\infty=1/8$；另一座在 $N+1$ 才分裂标签，随后恒等，完成距离都为 $1/4$，故缺口零。第二对塔把命题39.10的单点来源阶段重复至 $N$。一座永远保持单点来源，完成最优候选为 $\theta^{(0)}$、缺口零；另一座在 $N+1$ 才显露 $a/b$，随后恒等，完成候选被迫为 $\bar\theta$、缺口 $1/8$。四座塔均使用同一四世界实际律、全合法支撑，目标为 $\bar\theta$ 的相应标签推前；没有在层间替换分布。

更一般，把命题39.11的来源显露延迟到任意 $M>N$、标签分裂延迟到任意 $L>M$，中间都以恒等映射填充，便得同一共同塔上任意延迟的 $0\to1/8\to0$。交换、相容及可行保持由未填充的三个阶段逐段继承。$\square$

因此单凭任意已检查的有限前缀，没有对所有这些续接都正确的完成等号判断：正缺口平台和零缺口平台都能接到另一种完成答案。这是有限前缀的不可区分性结论，不是计算理论的不可判定定理；它不排除带额外尾部证书的程序。

### 39.6 两种真实尾界与严格有限证书

**命题 39.13（标签尾、世界尾及有向区间）。** 假设某应用另外供应对这一实际塔成立的已认证非负界
$$
0\le\tau_\infty-\tau_l\le a_l,\qquad
0\le d_\infty-d_l\le b_l.
\tag{39.31}
$$
则
$$
\boxed{\max\{0,g_l-a_l\}\le g_\infty\le g_l+b_l.}
\tag{39.32}
$$
若还给有限值的严格包围 $d_l\in[d_l^-,d_l^+]$、$\tau_l\in[\tau_l^-,\tau_l^+]$，则
$$
\boxed{\max\{0,d_l^- -\tau_l^+ -a_l\}\le g_\infty
       \le d_l^+ -\tau_l^- +b_l.}
\tag{39.33}
$$

证明。恒等式
$$
g_\infty=g_l+(d_\infty-d_l)-(\tau_\infty-\tau_l)
\tag{39.34}
$$
中，世界尾增加差、标签尾减少差。分别使用（39.31）两端并结合 $g_\infty\ge0$，得（39.32）。把 $g_l=d_l-\tau_l$ 的下界取为 $d_l^- -\tau_l^+$，上界取为 $d_l^+ -\tau_l^-$，得到（39.33）。因此 $g_l>a_l$ 认证严格正完成费用，$g_l+b_l\le\epsilon$ 认证费用至多 $\epsilon$；严格包围的正下端或不超过 $\epsilon$ 的上端给对应结论。$\square$

命题39.9在第0层有 $(g_0,a_0,b_0)=(1/8,1/8,0)$，实际 $g_\infty=0$ 达到下端；命题39.10有 $(g_0,a_0,b_0)=(0,0,1/8)$，实际 $g_\infty=1/8$ 达到上端。两个尾方向都不能省略。命题39.11中，第0层的真实两尾均为 $1/8$，第1层标签尾为 $1/8$、世界尾为零，第2层起均零；这些数值由已知完整恒等续接证明，不能从暂时观察到的平台推得。

式（39.31）要求实际极限的独立证书，不是给未知余项取名。定理39.3的抽象收敛、一个有限最优律或已经经过的计算时间均不供应这些界，本节没有新估计来建立它们。若另外有未来逐步增量的可求和上界 $A_j,B_j$，满足 $\tau_{j+1}-\tau_j\le A_j$、$d_{j+1}-d_j\le B_j$，则对 $j\ge l$ 望远镜求和并取极限可取 $a_l=\sum_{j\ge l}A_j$、$b_l=\sum_{j\ge l}B_j$；这仍以这些上界已证为前提。若已证明整座塔从某层起结构恒等，两尾从该层起为零；有限次观察到恒等不证明全尾恒等。

有理且可取得的有限数据允许用精确可行候选和匹配的优化下界证书认证 $d_l$，用精确算术认证 $\tau_l$。四世界例中的（39.29）及唯一性约束就是这样的解析证书；仅印出数值优化器的小数不是严格包围。任意实数输入不自动提供可计算的数据或判定程序。

若额外尾界可有效趋零，且有限包围宽度也可有效趋零，则（39.33）的两端趋于 $g_\infty$：例如 $0\le d_l-d_l^-\le d_l^+-d_l^-\to0$，标签同理，连同（39.17）即可。于是严格正的 $g_\infty$ 最终给正下端；当 $g_\infty<\epsilon$ 有严格裕量时，最终给上端小于 $\epsilon$。这不保证 $g_\infty=0$ 或恰达阈值时有限终止。要保证这些边界情况的精确停止，还需零上界证书或合适的附加承诺；两极限误差会计本身不产生停止算法。

### 39.7 完整观察者与一个见证的共同合法延续

**定义 39.14（完整已获档案与声明来源的区别）。** 继续采用定义13.1、命题13.2、定义13.3、定理13.4、约定15.1及第35.1–35.3节的档案语义：保留全部已获内部及外部记录、来源身份与版本、相关性和已经取得的来源—标签关系、参考、准备与校准、控制器、可访问记忆、动作及其守卫、失败、时钟和合法联合取得顺序。有限任务标签只是这个观察者的一个视图。原先第13节的记录商以有限共同世界为域；这里另外给出定义39.1的共同可测实现，不从该有限定理无条件推出任意观察者都有可数有限塔表示。

式（39.4）精确保留 $\sigma_\infty$ 中已声明条目的联合律 $\nu_\infty$ 和所写支撑约束。这强于分别保留来源边缘，却不自动保留未列入的来源—标签、参考—世界及历史耦合。命题5.3和命题38.4已经分别给出相同边缘而共同输出不同、相同标签与档案边缘而联合差为一的反例。已获且相关的关系必须放进联合合同或额外准入条件，再验证39.2的非空、紧性、投影保持及精确完成语义；不能用来源边缘替代整个观察者。

同分布也不等于实际记录样本逐项同一。若在 $C=c$ 下分析，实际／候选共同模型须使用同一整份证据、来源和相应准入条件；适用的条件概率版本及支持条件仍需给定。合法操作顺序不等于概率独立；任何独立性主张都须相对于完整 $C$ 验证。命题39.2的因子化障碍仍约束被保留档案已经固定的标签。

**命题 39.15（先选一个最优律，再比较全部共同核）。** 固定定义39.1的一份合同。从定理39.3选择一个最优 $\theta^*\in\mathcal L_\infty$。对声明实验族中的每个 $E$，另外给到完整实验记录空间 $\mathcal T_E$ 的可测归一概率核
$$
K_E:W_\infty\rightsquigarrow\mathcal T_E.
\tag{39.35}
$$
双方输入均须处于此核的共同合法定义域，双方使用完全相同的 $K_E$。过程语义须保留相关来源、参考、控制、记忆和档案依赖，动作守卫、失败、允许随机化、可访问历史及取得次序，并明确实际输出律为 $\rho_\infty K_E$、候选输出律为 $\theta^*K_E$。则量词为
$$
\exists\theta^*\in\mathcal L_\infty:\quad
\operatorname{TV}(\rho_\infty,\theta^*)=d_\infty,\qquad
\forall E,\quad
\operatorname{TV}(\rho_\infty K_E,\theta^*K_E)\le d_\infty.
\tag{39.36}
$$
若完成等距离成立，右端为 $\tau_\infty$。若联合输出同时保留世界与该次记录，其 TV 恰为输入 TV。

证明。有限情况使用命题9.16及既有 `total_variation_channel_le`；一般可测核使用命题38.6的（38.5）–（38.6）。具体地，对任一记录事件 $H$，$f(w)=K_E(w,H)$ 可测且在 $[0,1]$ 中，层蛋糕公式给
$$
\left|\int f\,d(\rho_\infty-\theta^*)\right|
=\left|\int_0^1\bigl(\rho_\infty\{f>t\}-\theta^*\{f>t\}\bigr)\,dt\right|
\le\operatorname{TV}(\rho_\infty,\theta^*).
\tag{39.37}
$$
对 $H$ 取上确界得结论，证明没有改变已选的 $\theta^*$，因而对每个给定共同合法核都成立。保留世界的联合核为 $w\mapsto\delta_w\otimes K_E(w,\cdot)$；共同核收缩给一个方向，投影回世界给反方向，遂为等号。$\square$

式（39.36）不允许每次实验或每个时刻重新选最优世界律，也不从一族分别的输出不等式推出各个不同实验的任意联合耦合。它未提供随输入／目标合同变化的可测最优选择规则，或对所有合同共用的准备算法。静态重加权不供应这里作为前提的过程合同。

自适应实验必须由同一合法历史依赖策略生成，并确实表示为此共同核；若从有限核构造过程，还需它们的投影相容性及准确合法路径律语义。[机器学习卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)定理17.3的联合输出—后继核因子化与命题17.7的分开边缘反例承担相关过程边界。只知道 $\lambda_\infty$ 不使所有后续实验都可从标签执行；标签接口复用须另给核的合法因子化或运输、或已证充分接口。命题39.7针对一个概率对的 TV 等号并不是这个操作充分性定理。

共同核前提不能撤掉：单点输入上的两律相同、TV 为零，恒输出0的核和另一个恒输出1的核却给 TV 为一。这是直接的不交点律计算，不能用（39.36）比较已替换的机制。稀有事件后选择及两方分别重新归一化也不是一个共同归一核；统一条件结论仍需完整联合档案和明确的支撑事件概率下界。

**命题 39.16（原来源实现所需的附加等式）。** 另给可测原域 $(X,\Sigma_X)$ 和可测读出 $j:X\to W_\infty$。最优律的原来源实现要求有概率 $m$ 满足
$$
j_*m=\theta^*,
\tag{39.38}
$$
并满足独立规定的原来源、档案及机制限制。若 $m_0,j$ 都已固定，式（39.38）成为必须另证的 $j_*m_0=\theta^*$；完成律存在本身不改变这个固定推前。若允许选择原概率，且有 Borel 集 $B\subseteq j(X)$、$\theta^*(B)=1$ 及可测截面 $s:B\to X$、$js=\mathrm{id}_B$，则 $m=s_*(\theta^*|_B)$ 供应概率提升；额外限制仍须逐项满足。

证明。固定准备与读出时推前由定义唯一确定。对给定截面，$\theta^*|_B$ 总质量一，且 $j_*s_*(\theta^*|_B)$ 对每个 Borel 事件 $H$ 的值为 $\theta^*(B\cap H)=\theta^*(H)$，所以满足（39.38）。构造只证明推前关系，未证明它等于另一个独立固定准备。$\square$

[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)定理46.4–46.5、定义91.1及定理91.2区分紧拼接、指定有限延伸、完成空间与实际像；本卷命题38.2–38.3分别保留可数稠密来源无法承载完成律、目标可达仍不保固定准备的障碍。逐点可达、稠密性或集合论截面不是可测概率提升；其他提升路线需要自己的随机化、析取、合法性与取得前提。命题39.16没有自动保留独立指定的样本身份。

完成最优律是一份静态准入重加权，不供应合法准备协议、已经取得的未来样本、高效解码器、唯一原世界或存储／运行时间界。分辨率层号不充当物理时钟；经典 Borel 律及共同核 TV 也不供应量子外部参考保证。这些解释各需额外操作、因果、可测或物理假设。

### 39.8 数学供应与应用范围

**约定 39.17（本节的证明归属）。** 本节把既有紧选择、概率延拓和有限通道结果应用于声明联合来源的完成问题，四世界计算及双尾会计为 `repo-derived` 普通数学推导。Stacks 与 Fremlin 所用结论为 `literature-attested`；不主张一般逆极限或数据处理理论的新颖性，不把这些普通应用声明为新增形式化结果。表39.3列明供应对象及不能替代的前提。

| 表39.3项 | 供应对象 | 在本节的精确用途与边界 |
|---|---|---|
| 39.3a 紧选择 | 恢复卷引理33.3，主卷定理46.4；Stacks 0A2R | 非空紧空间及连续连接给相容选择，不需满射；不是任意指定有限候选的延伸算法。 |
| 39.3b 完成概率 | 恢复卷定理33.4；Fremlin 418Q、411H | 本节以39.2.2逐项核对非满射有限 Radon 序列，取 Borel 限制；不直接套用前者的满射柱内容证明。 |
| 39.3c 完成几何 | 恢复卷定理33.6、33.9、33.11及推论33.12，式（33.15）、（33.19）–（33.20）、（33.23）–（33.26） | 复用有限柱连续函数逼近、Borel 事件逼近和共同半径证明；来源、目标、支撑的相容保持由（39.8）–（39.12）承担。 |
| 39.3d 有限收缩 | [DataProcessing.lean](../../../D5/S3/TotalVariation/DataProcessing.lean)，`total_variation_channel_le` | 有限实函数与非负行随机通道；供应确定投影及有限共同后处理收缩，不建立来源可行性或概率完成。 |
| 39.3e 有限等号 | [DataProcessingEquality.lean](../../../D5/S3/TotalVariation/Equality/DataProcessingEquality.lean)，`total_variation_channel_eq_iff_no_sign_mixing`；命题37.8 | 在确定核上的符号同向条件给（39.21）；没有新的通用等号机制。 |
| 39.3f 来源流 | 定理37.10及（37.17）–（37.18） | 实际合法时以 $A_l$ 为世界载体，逐项匹配亏损容量、合法接收关联及共同来源平衡；非法实际支撑使用（39.21）–（39.23），不原样引用合法供给构造。 |
| 39.3g 有限耦合 | [FiniteCouplingPushforwardLift.lean](../../../D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.lean)，`liftCoarseCoupling_marginals`、`liftCoarseCoupling_expectation` | 有理有限析取保持两个原边缘及配对读数，处理零纤维；不自动保留任意合法支撑、档案耦合或固定机制。 |
| 39.3h 状态线程 | [InverseLimitCompletion.lean](../../../D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean)，`stateThread_bijective_iff_complete_and_separates`；主卷定义91.1、定理91.2 | 类型层完备性与分离性、实际像与纤维提升；不提供独立指定原域上的概率提升。 |
| 39.3i 档案与延续 | 命题5.3、9.16、定义13.1–定理13.4、约定15.1、第35.1–35.3节、命题38.4及38.6 | 共同来源、完整已获记录、合法联合仪器及同核延续；固定来源边缘不能替代已获关联，预测、准备与过程接口分别有条件。 |
| 39.3j 联合过程 | 机器学习卷定理17.3、命题17.7 | 联合输出—后继核合同及后续记录反例，不是概率完成定理。 |
| 39.3k 有限载体边界 | [FiniteCofilteredLimit.lean](../../../D5/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit.lean)，`finite_cofiltered_limit_nonempty` | 明确要求对象载体有限，不能直接用于无限点的实概率多面体。 |
| 39.3l 有限事件边界 | [Metric.lean](../../../D5/S3/TotalVariation/Metric.lean)，`total_variation_eq_sup_event_gap` | 等质量有限函数的事件差公式，不是无限 Borel 柱 TV。 |
| 39.3m 特定层级边界 | [ProjectivePrimalConvergence.lean](../../../D5/S3/Weil/Budget/ProjectivePrimalConvergence.lean)，`projective_primal_convergence` | 特定圆周矩／预算层级且假设全可行类非空，不能替代本节的应用检查。 |
| 39.3n 已假设收敛边界 | [ProjectiveStrongDuality.lean](../../../D5/S3/Observer/Budget/ProjectiveStrongDuality.lean)，`projective_strong_duality` | 明确以 `projectiveConverges` 为前提，不能用来消除尚未证明的原始收敛义务。 |

本节的完成距离、有限抵消及后续共同核结论均附着于同一个实际律和声明的联合来源合同。双尾界、原来源提升及合法准备分别仍是额外假设；受限供应关系不构成文献优先权证明。

[^rroctx39_stacks]: The Stacks Project, [Lemma 5.14.6, tag 0A2R](https://stacks.math.columbia.edu/tag/0A2R)：余滤图中每个空间非空、拟紧、Hausdorff，映射连续，则逆极限非空；无满射条件。本节用于紧概率多面体及共同半径子集，不提供可测最优选择算法。

[^rroctx39_fremlin]: D. H. Fremlin, *Measure Theory*, [418Q，Chapter 41，PDF 第116页](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=116)：Radon 概率空间序列及 inverse-measure-preserving、almost continuous 连接函数，在实际线程空间上给唯一相容 Radon 概率。该书[411H，PDF 第5页](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=5)的 Radon 空间要求完全、局部确定、Hausdorff、局部有限及紧集内正则。有限离散幂集概率满足全部条件，包括零质量及非满射连接；本节只使用所得概率的 Borel 限制及柱生成的 Borel 唯一性。

## 39.99 追加锚

## 40. 实际延迟历史的饱和证书与未知基准上的相对间隔

本节把有限历史的 Gram 几何接到实际经过时间的恢复：瞬时端口可以不单射，足够的同源延迟关系可给单射的有效接口；其饱和须由真实嵌套历史认证。[主卷](RECURSIVE_RELATIONAL_OBSERVATION.md)第126节、第137节与[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)第10、12、13、15、21节供应有效空间、平坦性、正对数、残差与误差机制。以下是这些结果在有限历史相对钟任务中的 `repo-derived` 普通数学应用，不主张新的通用实现理论或物理时间定律。本节不以先前有限循环及完成化结论为前提。

### 40.1 完整观察者与实际延迟响应

**定义 40.1（保留全部档案的正伴随来源合同）。** 以 $C_{\rm acq}$ 表示完整已获档案，保留全部内部／外部记录和已取得的关系；以 $\mathcal F(C_{\rm acq})$ 表示满足整份档案、声明先验和合法取得历史的共同世界族。要求它非空并含实际世界。每个世界必须同时解释所有已获矩阵、实际准备、来源及参考身份、版本与关联、输入／输出内积与单位、增益、局部标签、可访问记忆、控制与动作、守卫及失败、联合顺序、误差和允许的联合误差事件。未测量的参数在同一个世界里受这些关系共同约束。使用本节的矩阵统计量只是从该观察者取一个任务视图，不删除其他已获信息；空可行族也不是恢复证书。合法操作顺序不等于概率独立；若另外主张独立，须相对于完整 $C_{\rm acq}$ 验证。本合同复用本卷第30—36节的完整世界、保留参考、联合误差、顺序与合法取得语义，不搬用那些节的 PDE、量子或编码前提。

对族中所比较的每个世界，固定有限维实内积空间 $H,U$、边界内积与
$$
B:H\longrightarrow U,\qquad C=C^*>0,\qquad
K(t)=Be^{-tC}B^*\quad(t\ge0).
\tag{40.1}
$$
输入为实际伴随 $B^*$，输出为 $B$；所有伴随使用指定内积。主卷第126.1节给
$$
\mathcal R=\operatorname{span}\{C^jB^*u:j\ge0,\ u\in U\},\qquad
 d=\dim\mathcal R,\qquad C_{\mathcal R}=C|_{\mathcal R}.
\tag{40.2}
$$
$\mathcal R$ 与 $\mathcal R^\perp$ 约化 $C$，$B\mathcal R^\perp=0$，且 $K$ 仅依赖 $C_{\mathcal R}$ 和 $B|_{\mathcal R}$。允许隐藏空间另有完全不可见的块；这些块不参加以下迹与维数。

取一个实际共同加性延迟 $h>0$，令 $T=e^{-hC}$。对整数 $r\ge0$，在系数空间 $U^{r+1}$ 使用正交直和内积，定义
$$
\begin{aligned}
V_r&=\operatorname{span}\{T^jB^*u:0\le j\le r,\ u\in U\},\\
B_r:H&\longrightarrow U^{r+1},\qquad
B_rx=(BT^ix)_{i=0}^r,\\
\mathsf H_r(s)&=\bigl(K(s+(i+j)h)\bigr)_{0\le i,j\le r}\quad(s\ge0).
\end{aligned}
\tag{40.3}
$$
所谓未知基准 $a\ge0$ 是未知响应年龄，不是给传感器增加一个未解释的加性偏置。实际来源、共同延迟及所有条目的准备与校准由此合同承担；仅有数值相等或一份可行拟合不能建立这些事实。

**引理 40.2（实际 Gram 因子化、共同支撑与采样可达空间）。** 在定义40.1下，对每个有限 $s\ge0$，
$$
\boxed{\mathsf H_r(s)=B_r e^{-sC}B_r^*.}
\tag{40.4}
$$
因此
$$
\begin{aligned}
\ker\mathsf H_r(s)&=\ker B_r^*,\\
\operatorname{ran}\mathsf H_r(s)&=\operatorname{ran}B_r=:E_r,\\
\operatorname{rank}\mathsf H_r(s)&=\operatorname{rank}B_r=\dim V_r.
\end{aligned}
\tag{40.5}
$$
同时有
$$
\operatorname{span}_{j\ge0}T^jB^*U
=\operatorname{span}_{j\ge0}C^jB^*U=\mathcal R.
\tag{40.6}
$$

证明。$B_r^*(u_0,\ldots,u_r)=\sum_{j=0}^rT^jB^*u_j$，故（40.4）的 $(i,j)$ 块为 $BT^ie^{-sC}T^jB^*=K(s+(i+j)h)$；这里使用自伴性及同一 $C$ 的函数相互交换。对任意系数向量 $v$，其二次型为 $\|e^{-sC/2}B_r^*v\|^2$。有限 $s$ 时指数可逆，因而核正是 $\ker B_r^*$；自伴算子的像等于核的正交补，得共同支撑与秩，且 $\operatorname{ran}B_r^*=V_r$。

在 $C$ 的有限实谱上，$c\mapsto e^{-hc}$ 单射。有限谱插值给多项式 $p,q$，使 $T=p(C)$、$C=q(T)$。两方向逐次代入生成跨度，得到（40.6）。这也是恢复卷第10.1—10.2节采样正算子的使用域；谱插值只识别数学子空间，不授权免费实施任意多项式实验动作。$\square$

共同支撑在未饱和时也自动成立；它本身不使压缩与指数或对数交换。

### 40.2 真正饱和后的相对间隔

**定理 40.3（实际相邻秩平台同时认证两个阶数）。** 固定任意实际年龄 $a\ge0$，其数值不必已知。若 $\operatorname{rank}\mathsf H_r(a)=d$，则 $V_r=\mathcal R$，等价于 $B_r|_{\mathcal R}$ 单射。对 $r\ge1$，
$$
\operatorname{rank}\mathsf H_r(a)=\operatorname{rank}\mathsf H_{r-1}(a)
\quad\Longrightarrow\quad V_{r-1}=V_r=\mathcal R.
\tag{40.7}
$$
特别地，对所选任意 $r\ge0$，
$$
\boxed{V_r=\mathcal R\ \Longleftrightarrow\
\operatorname{rank}\mathsf H_{r+1}(a)=\operatorname{rank}\mathsf H_r(a).}
\tag{40.8}
$$
当 $d\ge1$ 时，$r\ge d-1$ 是充分视界；若可见互异谱率数为 $q\ge1$，$r\ge q-1$ 也是充分视界。这些上界是数学条件，不自动是实验者已知的维数或率数。

证明。由（40.5），秩为 $d$ 恰使 $V_r\subseteq\mathcal R$ 具有全维数；又 $\ker(B_r|_{\mathcal R})=\mathcal R\cap V_r^\perp$。相邻秩相等使嵌套子空间 $V_{r-1}\subseteq V_r$ 相等，而 $TV_{r-1}\subseteq V_r$。这个 $T$-不变空间包含 $B^*U$，所以由（40.6）等于 $\mathcal R$。反向，饱和后再加一个延迟不扩张空间，给（40.8）。这是主卷第126.4节及命题137.10、定理137.13的真实 Krylov 平坦机制在 $T$ 上的应用。第126.4节以 $m$ 个向量层计数，这里为 $m=r+1$；未饱和的链每次至少增长一维，给 $r\ge d-1$。对 $q$ 个可见谱值，谱投影在 $T|_{\mathcal R}$ 上均可用次数至多 $q-1$ 的插值多项式表示，因此这 $q$ 层已经生成 $\mathcal R$，给第二视界。$\square$

不同偏移但同一阶数的 $\mathsf H_r(s),\mathsf H_r(t)$ 秩总相等，不能替代相邻嵌套阶数的平台。这里每个块的实际实现由（40.4）供应。对抽象数组，主卷定理137.2—137.5的移位零关系以及定理137.13的偶数正平坦条件仍须核验；命题137.3的前缀 $(1,1,1,2)$ 已有两个正块和普通秩平台，却违反移位核包含，没有自伴实现。不能从它的秩反推一个实际来源。

**定理 40.4（未知基准白化的实际间隔定理）。** 假设 $V_r=\mathcal R$、$d>0$。固定任意实际基准 $a\ge0$，定义以下均使用支撑上的映射：
$$
\begin{aligned}
D&=B_r|_{\mathcal R}:\mathcal R\longrightarrow E_r,&
D_a&=De^{-aC_{\mathcal R}/2},\\
A_a&=\mathsf H_r(a)|_{E_r}=D_aD_a^*,&
F_a&=A_a^{-1/2}D_a:\mathcal R\longrightarrow E_r.
\end{aligned}
\tag{40.9}
$$
则 $F_a$ 为正交同构。对实际经过间隔 $s\ge0$，定义
$$
\begin{aligned}
W_{r,a}(s)&=A_a^{-1/2}
 \bigl(\mathsf H_r(a+s)|_{E_r}\bigr)A_a^{-1/2},\\
G_{r,a}&=F_aC_{\mathcal R}F_a^*>0,\qquad
L_{r,a}(s)=-\log W_{r,a}(s).
\end{aligned}
\tag{40.10}
$$
有
$$
\boxed{W_{r,a}(s)=F_ae^{-sC_{\mathcal R}}F_a^*
=e^{-sG_{r,a}},\qquad L_{r,a}(s)=sG_{r,a}.}
\tag{40.11}
$$
从而对 $s\ge0,t>0$，
$$
\boxed{
\frac{\operatorname{tr}L_{r,a}(s)}{\operatorname{tr}L_{r,a}(t)}=\frac{s}{t},\qquad
\frac{\operatorname{tr}L_{r,a}(s)}{\operatorname{tr}L_{r,a}(h)}=\frac{s}{h}.}
\tag{40.12}
$$

证明。$D$ 在 $\mathcal R$ 上单射且像为 $E_r$，故为同维双射；$e^{-aC_{\mathcal R}/2}$ 可逆，$D_a$ 亦双射。于是 $A_a\succ0$ 且 $F_aF_a^*=I_{E_r}$。两空间维数均为 $d$，余等距升级为正交同构，给 $F_a^*F_a=I_{\mathcal R}$。由（40.4）及指数相乘，$\mathsf H_r(a+s)|_{E_r}=D_ae^{-sC_{\mathcal R}}D_a^*$。代入白化并用正交函数演算得到（40.11），其中正定实对数的唯一性由恢复卷命题10.6承担。迹满足 $\operatorname{tr}G_{r,a}=\operatorname{tr}C_{\mathcal R}>0$，所以（40.12）的分母非零，约去共同斜率即得结论。$\square$

$F_a$ 不必已知，它只承担证明；共同支撑和白化矩阵来自声明的精确数据。若 $h$ 有数值校准，$G_{r,a}=-h^{-1}\log W_{r,a}(h)$ 给数据正交坐标中的生成元；若仅给可重复延迟单位，仍得到 $hG_{r,a}=-\log W_{r,a}(h)$。坐标标架可随 $a$ 改变，但迹斜率不变。若在整个 $U^{r+1}$ 上表达白化，可用 $\mathsf H_r(a)^{\dagger/2}$，随后必须限制到 $E_r$；环境空间的零块没有对数。这里不要求原始 $B$ 单射，单射性由实际延迟接口供应。

若 $B=0$，则 $d=0$、全部响应为零；零有效空间虽已饱和，迹比仍为 $0/0$，不提供钟。完全不可见的附加隐藏块不会进入 $G_{r,a}$ 或其迹。

**推论 40.5（固定支撑行列式与有符号间隔）。** 在定理40.4下，$\det_{E_r}\mathsf H_r(t)$ 指限制到同一个 $E_r$ 后的行列式，也就是环境半正定矩阵非零特征值的乘积 $\operatorname{pdet}\mathsf H_r(t)$。令 $\kappa=\operatorname{tr}C_{\mathcal R}>0$。则
$$
\det_{E_r}\mathsf H_r(t)
=\det_{E_r}\mathsf H_r(0)e^{-t\kappa}\quad(t\ge0),
\tag{40.13}
$$
以及对任意实际年龄 $a,b\ge0$，
$$
\log\operatorname{pdet}\mathsf H_r(a)
-\log\operatorname{pdet}\mathsf H_r(b)=(b-a)\kappa.
\tag{40.14}
$$
实际取得 $\mathsf H_r(a),\mathsf H_r(a+h),\mathsf H_r(b)$ 时，
$$
\boxed{
\frac{\log\operatorname{pdet}\mathsf H_r(a)-\log\operatorname{pdet}\mathsf H_r(b)}
{\log\operatorname{pdet}\mathsf H_r(a)-\log\operatorname{pdet}\mathsf H_r(a+h)}
=\frac{b-a}{h}.}
\tag{40.15}
$$
分母也可换成任何另外实际取得的同源、同接口 $c,c+h$ 对的对数行列式差，其中 $c\ge0$ 不必已知。所有行列式必须使用同一历史阶数、支撑和边界内积。

证明。在（40.11）中以零年龄作为数学基准取行列式，得 $\det W_{r,0}(t)=e^{-t\kappa}$，而白化两侧的行列式为 $\det_{E_r}\mathsf H_r(t)/\det_{E_r}\mathsf H_r(0)$，证明（40.13）。在任意两个非负年龄相减得（40.14）；任意 $c,c+h$ 对的差恒为 $h\kappa>0$，得（40.15）。零年龄在这里仅用于证明恒等式，操作公式没有要求已经观察它，也不要求逐个重建谱率或原始 $B$。$\square$

$b<a$ 时右端为负，仍是两个非负实际年龄之间的有符号差，未使用负年龄实验。定理40.4的未知基准白化给相同的正向间隔结果；任意基准不是准备原点。要恢复距实际准备的年龄仍须对应原点参考；要恢复绝对物理单位仍须校准。对任意 $c_0>0$，$C\mapsto c_0C$、所有年龄和延迟 $t\mapsto t/c_0$ 保持响应样本，且保持间隔比。这是恢复卷命题15.9—15.10已有的尺度规范自由。

### 40.3 倍时与迹对数诊断的既有供应应用

**命题 40.6（基准移位投影与一个正间隔的饱和判据）。** 仍在定义40.1的实际模型中，取任意 $r\ge0$、$E_r\ne0$ 和实际 $a\ge0$，暂不假设饱和。按（40.9）定义 $D,D_a,A_a,F_a$，按（40.10）定义 $W_{r,a}$。此时 $F_a$ 一般只是余等距，且
$$
F_aF_a^*=I_{E_r},\qquad
P_a:=F_a^*F_a=P_{V_r^{(a)}},\qquad
V_r^{(a)}:=e^{-aC_{\mathcal R}/2}V_r.
\tag{40.16}
$$
对任意一个实际正间隔 $s>0$，置 $S=e^{-sC_{\mathcal R}}$，有
$$
\boxed{\Delta_{a,s}:=W_{r,a}(2s)-W_{r,a}(s)^2
=F_aS(I-P_a)SF_a^*\succeq0,}
\tag{40.17}
$$
并且
$$
\boxed{
\Delta_{a,s}=0\ \Longleftrightarrow\ V_r=\mathcal R
\ \Longleftrightarrow\
\operatorname{rank}\mathsf H_{r+1}(a)=\operatorname{rank}\mathsf H_r(a).}
\tag{40.18}
$$

证明。$D_a$ 满射到 $E_r$，故 $A_a$ 正定并有 $F_aF_a^*=I$。$F_a^*F_a$ 自伴且幂等，像为 $\operatorname{ran}D_a^*=e^{-aC_{\mathcal R}/2}V_r$，证明（40.16）。尤其投影通常不是到未经移位的 $V_r$。白化因子化仍给 $W_{r,a}(s)=F_aSF_a^*$、$W_{r,a}(2s)=F_aS^2F_a^*$。

式（40.17）直接取自恢复卷定理13.4的式（13.10）及其残差平方证明。精确代入为：该供应的历史阶数取零，与此处 $r$ 无关；隐藏空间取 $\mathcal R$、边界取 $E_r$，$J=V=F_a^*$，Gram 矩阵 $H=J^*J=I_{E_r}$。其 $K'(s)=W_{r,a}(s)$、$B_s=W_{r,a}(s)$、$Q_s=\Delta_{a,s}$，残差平方正是 $F_aS(I-P_a)SF_a^*$。仅使用这条代数恒等式和正性，不移入该供应的初态 minimax 结论或授权新的准备。

为判定等号，将主卷定理137.13的阶数取一，取真实 $S$、输入 $F_a^*$ 的三个矩
$$
M_0=I_{E_r},\quad M_1=W_{r,a}(s),\quad M_2=W_{r,a}(2s),\qquad
\widehat H_1=\begin{pmatrix}I&W_{r,a}(s)\\W_{r,a}(s)&W_{r,a}(2s)\end{pmatrix},
\quad\widehat H_0=I.
\tag{40.19}
$$
$M_1$ 正定，因为 $S>0$ 且 $F_a^*$ 单射，故该供应的移位块正性成立。以 $W=W_{r,a}(s)$ 作供应证明中的 Schur 合同变换，有
$$
\begin{pmatrix}I&0\\-W&I\end{pmatrix}
\widehat H_1
\begin{pmatrix}I&-W\\0&I\end{pmatrix}
=\begin{pmatrix}I&0\\0&\Delta_{a,s}\end{pmatrix}.
\tag{40.20}
$$
因此 $\Delta_{a,s}=0$ 等价于 $\operatorname{rank}\widehat H_1=\operatorname{rank}\widehat H_0$。主卷定理137.13针对任一实际实现的证明于是给 $S$-不变性：$\operatorname{ran}F_a^*=V_r^{(a)}$ 在 $S$ 下不变。自伴性使它约化 $S$；恢复卷命题10.6的唯一正对数 $C_{\mathcal R}=-s^{-1}\log S$ 及有限谱函数演算又使它在 $C_{\mathcal R}$ 下不变。它包含 $e^{-aC_{\mathcal R}/2}B^*U$，而这批移位输入的全部 $C_{\mathcal R}$-生成空间为
$$
\operatorname{span}_{j\ge0} C_{\mathcal R}^j e^{-aC_{\mathcal R}/2}B^*U
=e^{-aC_{\mathcal R}/2}\mathcal R=\mathcal R.
\tag{40.21}
$$
最后一步使用指数在有限有效空间上可逆。故 $V_r^{(a)}=\mathcal R$，也就 $V_r=\mathcal R$。反向饱和给 $P_a=I_{\mathcal R}$，使残差为零；最后一个等价由定理40.3承担。$\square$

**推论 40.7（迹对数的严格倍时诊断）。** 在命题40.6的实际模型下，不预设 $L_{r,a}(s)=-\log W_{r,a}(s)$ 线性。对每个 $s>0$，
$$
\boxed{\operatorname{tr}L_{r,a}(2s)\le2\operatorname{tr}L_{r,a}(s),
\quad\text{等号当且仅当 }V_r=\mathcal R.}
\tag{40.22}
$$
故未饱和时，对每个实际基准 $a\ge0$ 和每个 $s>0$ 都严格不等。

证明。$W=W_{r,a}(s)>0$、$W_{r,a}(2s)>0$，且 $W_{r,a}(2s)=W^2+\Delta_{a,s}$。由于 $W$ 是 $W^2$ 的正平方根，
$$
\frac{\det W_{r,a}(2s)}{\det(W^2)}
=\det\bigl(I+W^{-1}\Delta_{a,s}W^{-1}\bigr)\ge1.
\tag{40.23}
$$
右端增量是半正定合同。这里应用主卷定理128.5在第128.4节的证明所用的谱行列式机制：$X\succeq0$ 时 $\det(I+X)=\prod_i(1+\lambda_i)\ge1$，等号恰为 $X=0$。不使用其 Gaussian 假设或互信息解释；第128.5节的 Fibonacci 例也不是此证明地址。再用正定矩阵的 $\operatorname{tr}(-\log X)=-\log\det X$，得到（40.22）；等号由（40.18）判定。$\square$

$s=0$ 时白化为 $I$、恒有等号，不能作为证书；零响应同样不给钟。可选 $s=h$，但 $\mathsf H_r(a),\mathsf H_r(a+h),\mathsf H_r(a+2h)$ 与下一 Gram 块都需截至 $a+(2r+2)h$ 的实际前缀，没有取得优势，也没有产生抗噪秩估计。$s,2s$ 必须是实际半群间隔；若实际时间为 $t=f(\tau)$，标签等差不保证
$$
f(\tau+2\eta)-f(\tau)
=2\bigl(f(\tau+\eta)-f(\tau)\bigr).
\tag{40.24}
$$
选择 $s=h$ 仍须履行同一个实际延迟合同。

### 40.4 实际共同支撑上的定量稳定性

**定理 40.8（继承白化与对数界的正间隔统计量）。** 固定历史阶数 $r$ 和共同系数内积。比较两组三元矩阵 $(A,H_e,H_*)$、$(A',H'_e,H'_*)$，其所有矩阵在环境系数空间中都有完全相同的非零支撑 $E$，$m=\dim E>0$；以下矩阵运算均限制在 $E$。实际响应情形写作 $A=\mathsf H_r(a)$、$H_j=\mathsf H_r(a+s_j)$，$j=e,*$ 分别为事件和锚，第二个模型用加撇记号；本定理先只要求矩阵数据条件
$$
\begin{gathered}
\operatorname{spec}(A),\operatorname{spec}(A')\subseteq[\gamma,R_0],\qquad 0<\gamma\le R_0,\\
uA\preceq H_j\preceq vA,\qquad
uA'\preceq H'_j\preceq vA',\qquad 0<u\le v<1\quad(j=e,*).
\end{gathered}
\tag{40.25}
$$
定义同一几何中的 Frobenius 数据差和白化对数
$$
\begin{gathered}
\delta_0=\|A-A'\|_F,\qquad \delta_j=\|H_j-H'_j\|_F,\\
W_j=A^{-1/2}H_jA^{-1/2},\qquad L_j=-\log W_j,\\
W'_j=A'^{-1/2}H'_jA'^{-1/2},\qquad L'_j=-\log W'_j,\\
d_j=\frac{\delta_j}{\gamma}
 +\frac{2v\sqrt{R_0}}{\gamma^{3/2}}\delta_0,\qquad
D_j=\frac{d_j}{u},\qquad
\alpha=-\log v>0,\quad\beta=-\log u.
\end{gathered}
\tag{40.26}
$$
则 $\|W_j-W'_j\|_F\le d_j$、$\|L_j-L'_j\|_F\le D_j$，且
$$
\boxed{
\left|\frac{\operatorname{tr}L_e}{\operatorname{tr}L_*}
-\frac{\operatorname{tr}L'_e}{\operatorname{tr}L'_*}\right|
\le\frac{D_e}{\sqrt m\,\alpha}
 +\frac{\beta D_*}{\sqrt m\,\alpha^2}.}
\tag{40.27}
$$

证明。应用恢复卷定理12.2的代数白化估计，不应用其中另外的矩实现断言。为明确常数，置 $Z=A^{-1/2}$、$Z'=A'^{-1/2}$。该证明的双特征基差商界给
$$
\|Z-Z'\|_F\le\frac{\delta_0}{\gamma^{3/2}},\qquad
\|Z\|_{\rm op},\|Z'\|_{\rm op}\le\gamma^{-1/2},\qquad
\|H_jZ\|_{\rm op},\|Z'H'_j\|_{\rm op}\le v\sqrt{R_0}.
\tag{40.28}
$$
最后一界使用 $H_j=A^{1/2}W_jA^{1/2}$、$\|W_j\|_{\rm op}\le v$，加撇同理。把差写成
$$
W_j-W'_j=(Z-Z')H_jZ+Z'(H_j-H'_j)Z+Z'H'_j(Z-Z'),
\tag{40.29}
$$
逐项应用 $\|XYZ\|_F\le\|X\|_{\rm op}\|Y\|_F\|Z\|_{\rm op}$，得到 $d_j$。

两个白化算子的谱都在 $[u,v]$。恢复卷式（12.7）的双特征基矩阵函数界与定理12.3证明中尚未放宽的对数步骤给
$$
\|L_j-L'_j\|_F
\le\frac{1}{u}\|W_j-W'_j\|_F\le D_j,
\tag{40.30}
$$
因为 $\log$ 在 $[u,v]$ 上的差商至多 $1/u$。这里比较无量纲对数，未除以延迟，因此没有 $h^{-1}$。在环境空间写供应证明时，两个实际支撑投影 $P,P'$ 相同，实际 $\|P-P'\|_F=0$；但供应定义的上界 $d_P=\delta_0/\gamma$ 仍可严格为正，不能把这个有名字的常数改写为零。直接在共同支撑上用（40.30），正是保留实际零投影差的未放宽步骤。此处引用的是恢复卷方程（12.7），不是关于未知初态的命题12.7。

谱映射给 $\alpha I\preceq L_j,L'_j\preceq\beta I$。记 $N=\operatorname{tr}L_e$、$Q=\operatorname{tr}L_*$，加撇同理，则
$$
Q,Q'\ge m\alpha,\qquad 0<N,N'\le m\beta,\qquad
|\operatorname{tr}(L_j-L'_j)|\le\sqrt m\,D_j.
\tag{40.31}
$$
最后一式是 $\langle I,L_j-L'_j\rangle_F$ 的 Cauchy–Schwarz 界，$\|I\|_F=\sqrt m$。故
$$
\left|\frac NQ-\frac{N'}{Q'}\right|
\le\frac{|N-N'|}{Q}+\frac{N'|Q-Q'|}{QQ'}
\le\frac{D_e}{\sqrt m\,\alpha}
+\frac{\beta D_*}{\sqrt m\,\alpha^2},
\tag{40.32}
$$
证明所述常数。$\square$

式（40.27）首先保证矩阵统计量。只有比较的两个完整世界都另行满足实际共同响应、饱和与合法时间顺序合同，才能由定理40.4分别把它解释为 $s_e/s_*$ 与 $s'_e/s'_*$ 的差；一份拟合的存在不认证实际来源。这里 $v<1$、$u>0$ 及正锚保证的是正事件／锚间隔的稳定界，推论40.5的精确有符号恒等式不自动给负间隔的带噪推广。两个统计量内事件与锚共享基准误差 $\delta_0$；所有重复条目使用同一个联合误差事件，未要求误差独立。逐模型严格正定也不供应统一的 $\gamma,u,\alpha$，弱模态、迟时或弱锚均可使这些裕量退化。

### 40.5 八个必要实例与失效边界

**命题 40.9（共同支撑不足，增加历史后恢复精确间隔）。** 取 $h=1$、$H=\mathbb R^2$、$U=\mathbb R$，
$$
T=\operatorname{diag}(1/2,1/4),\qquad
C=\operatorname{diag}(\log2,\log4),\qquad
B=2^{-1/2}(1,1).
\tag{40.33}
$$
有效维数为二。基准 $a=0$、$r=0$ 时，$\mathsf H_0(0)=1$，记 $W_0=W_{0,0}$，则
$$
W_0(s)=K(s)=\tfrac12(2^{-s}+4^{-s}),\qquad
K(2s)-K(s)^2=\tfrac14(2^{-s}-4^{-s})^2>0\quad(s>0).
\tag{40.34}
$$
特别地，
$$
\frac{-\log K(2)}{-\log K(1)}
=\frac{\log(32/5)}{\log(8/3)}\approx1.8925801659\ne2.
\tag{40.35}
$$
而 $r=1$ 时
$$
\mathsf H_1(0)=\begin{pmatrix}1&3/8\\3/8&5/32\end{pmatrix},\qquad
\det\mathsf H_1(0)=1/64,\qquad
\det\mathsf H_1(k)=\frac{8^{-k}}{64}\quad(k=0,1,2,\ldots).
\tag{40.36}
$$

证明。$B^*$ 与 $TB^*$ 线性无关，故有效维数二。把两个标量指数相加后展开平方得到（40.34），再取对数给严格次倍增及（40.35）。一般地，二原子权重 $w_1,w_2$、节点 $x,y$ 的阶一块在年龄 $t$ 的行列式为 $w_1w_2(xy)^t(x-y)^2$；这由 $(w_1x^t+w_2y^t)(w_1x^{t+2}+w_2y^{t+2})-(w_1x^{t+1}+w_2y^{t+1})^2$ 直接展开得到。代入 $w_1=w_2=1/2,x=1/2,y=1/4$ 得（40.36）。因此 $r=0,1,2$ 的嵌套真实秩依次为 $1,2,2$；最后的相邻平台正确认证包括较小 $r=1$ 在内的饱和。所有标量响应支撑始终相同且正定，未饱和时失去的正是对数线性。$\square$

**命题 40.10（非零基准必须移位投影）。** 同一来源取 $a=2,r=0$。则
$$
V_0^{(2)}=\operatorname{span}(2,1),\qquad
F_2=\frac1{\sqrt5}(2,1),\qquad
P_2=\begin{pmatrix}4/5&2/5\\2/5&1/5\end{pmatrix},
\tag{40.37}
$$
以及
$$
W_{0,2}(1)=9/20,\qquad W_{0,2}(2)=17/80,\qquad
\Delta_{2,1}=1/100.
\tag{40.38}
$$

证明。$e^{-aC/2}=T$，所以 $D_2=BT=(1/2,1/4)/\sqrt2$，$A_2=K(2)=5/32$，归一化给（40.37）。又 $K(3)=9/128$、$K(4)=17/512$，分别除以 $K(2)$ 得（40.38）的两个白化值，其差为 $17/80-(9/20)^2=1/100$。用（40.37）的 $P_2$ 代入（40.17）给同一值；若误用未移位的 $P_{V_0}=\tfrac12\left(\begin{smallmatrix}1&1\\1&1\end{smallmatrix}\right)$，则 $F_2T(I-P_{V_0})TF_2^*=9/160\ne1/100$，明确检测出错误投影。阶一饱和时（40.36）给从年龄2到5的比为3，从年龄5到2的比为 $-3$；二者端点年龄均非负、基准均非零，也都无需已获零年龄样本。$\square$

**命题 40.11（任意有限阶的一步移位仍可藏更大实际空间）。** 对长度为 $m\ge1$、顶点 $0,\ldots,m-1$ 的路径，令 $A_m$ 为邻接矩阵，取
$$
T_m=\tfrac12I+\tfrac18A_m,\qquad
B_m=e_0^*,\qquad C_m=-h^{-1}\log T_m.
\tag{40.39}
$$
其采样谱位于 $[1/4,3/4]$，$C_m>0$，有效维数为 $m$。对任意 $r\ge0$，模型 $m=r+1$ 和 $m=r+2$ 满足
$$
\begin{aligned}
e_0^*T_{r+1}^ke_0&=e_0^*T_{r+2}^ke_0 &&(0\le k\le2r+1),\\
e_0^*T_{r+2}^{2r+2}e_0-e_0^*T_{r+1}^{2r+2}e_0&=8^{-2r-2}>0.
\end{aligned}
\tag{40.40}
$$
故两实际模型的 $\mathsf H_r(0),\mathsf H_r(h)$ 完全相同，秩均为 $r+1$，却只有小模型在阶 $r$ 饱和。

证明。恢复卷命题13.8的路径二次型界 $|\langle x,A_mx\rangle|\le2\|x\|^2$ 给所述谱区间；正对数因而合法且生成元严格正。$T_m^je_0$ 在 $e_j$ 上的首达系数为 $(1/8)^j$，在更远坐标为零，$0\le j<m$ 的这些向量呈非零对角的三角形，线性无关并张成全空间。

矩 $e_0^*T_m^ke_0$ 是带等待权 $1/2$ 和边权 $1/8$ 的长度 $k$ 闭路权重之和。大模型相较小模型新增最远顶点 $r+1$；从0访问它并返回至少需 $2r+2$ 条边。因此到 $2r+1$ 为止闭路完全相同。恰在 $2r+2$ 步，新增闭路只有一直向外再一直返回的一条，不能夹等待，权重为 $8^{-2r-2}$。这也覆盖 $r=0$。两块所需最高阶分别为 $2r$ 和 $2r+1$，故数据相等；前 $r+1$ 个 Krylov 向量独立给块秩，证明结论。$\square$

这里把恢复卷命题13.8的路径／Krylov机制用于两个响应来源，而非变化未知初态；它是主卷第137.7—137.12条与恢复卷命题12.6竞争扩张障碍的实例，不是另立一般障碍定理。对每个固定 $r$，共同有限块本身有正 Gram 下界，仍不能从该块与一次移位得知实际未来已闭合；统一于所有 $r$ 的条件数界并未主张。

**命题 40.12（小谱权不供应精确平台）。** 固定 $0<x<y<1$、$0<\epsilon<1$，令
$$
M_j=(1-\epsilon)x^j+\epsilon y^j.
\tag{40.41}
$$
它有实际二维正生成元实现 $T=\operatorname{diag}(x,y)$、$B=(\sqrt{1-\epsilon},\sqrt\epsilon)$、$C=-h^{-1}\log T$，并且
$$
\det\mathsf H_1(0)=\epsilon(1-\epsilon)(x-y)^2>0.
\tag{40.42}
$$
当 $\epsilon\downarrow0$ 时，每个固定有限前缀趋于秩一来源 $x^j$，真实秩却始终为 $\operatorname{rank}\mathsf H_0=1$、$\operatorname{rank}\mathsf H_1=2$。

证明。两个节点不同且两权重为正，给二维可达性；命题40.9证明中的二原子展开给行列式。每个固定 $j$ 的误差为 $\epsilon(y^j-x^j)$，有限多个同时趋零。$\square$

主卷命题137.15与恢复卷命题12.6已经拥有这种弱方向秩不连续边界。固定的正数阈值可把真实弱特征值删去，报告两个块都秩一；秩一拟合即使精确平坦，也不认证附近真实来源平坦。式（40.17）的残差小或式（40.22）接近等号同样不证明精确饱和；定量近饱和需要另给下界和估计。

**命题 40.13（小残差的钟偏差与真实秩二的数据不稳定）。** 对 $0<\epsilon<1/2$ 取 $h=1$，
$$
C_\epsilon=\operatorname{diag}(\epsilon^2,1),\qquad
B_\epsilon=(\sqrt{1-\epsilon},\sqrt\epsilon),\qquad
K_\epsilon(t)=(1-\epsilon)e^{-\epsilon^2t}+\epsilon e^{-t}.
\tag{40.43}
$$
同一实际来源有效维数为二，标量一步 Schur 残差为
$$
K_\epsilon(2)-K_\epsilon(1)^2
=\epsilon(1-\epsilon)(e^{-\epsilon^2}-e^{-1})^2>0,
\tag{40.44}
$$
且趋于零。但错误地把阶零压缩当作饱和钟时，
$$
-\log K_\epsilon(t)=\epsilon(1-e^{-t})+O_t(\epsilon^2)\quad(t>0\text{ 固定}),\qquad
\lim_{\epsilon\downarrow0}
\frac{-\log K_\epsilon(2)}{-\log K_\epsilon(1)}
=1+e^{-1}\ne2.
\tag{40.45}
$$
即使保留真实秩二，使用同一来源、同一 $\mathsf H_1(0),\mathsf H_1(1)$，两个事件块 $\mathsf H_1(2)$ 和 $\mathsf H_1(3)$ 的 Frobenius 差仍为 $O(\epsilon)$，而精确归一年龄分别为2与3。

证明。两个率不同且两权正，给维数二与（40.44）的二原子展开。对固定 $t$，$e^{-\epsilon^2t}=1-\epsilon^2t+O_t(\epsilon^4)$，故
$$
K_\epsilon(t)=1-\epsilon(1-e^{-t})-\epsilon^2t+O_t(\epsilon^3).
\tag{40.46}
$$
再用 $-\log(1-z)=z+O(z^2)$ 得（40.45）的展开。由于 $1-e^{-1}>0$，两个展开之比趋于 $(1-e^{-2})/(1-e^{-1})=1+e^{-1}$。因此把趋零残差当作精确闭合可保留阶一量级的钟偏差。

对每个 $t\ge0$，
$$
0<K_\epsilon(t)-K_\epsilon(t+1)
\le(1-\epsilon)(1-e^{-\epsilon^2})+\epsilon(1-e^{-1})
\le\epsilon^2+\epsilon(1-e^{-1}).
\tag{40.47}
$$
两个阶一事件块的四个条目分别使用 $t=2,3,3,4$，故
$$
\|\mathsf H_1(2)-\mathsf H_1(3)\|_F
\le2\bigl(\epsilon^2+\epsilon(1-e^{-1})\bigr)=O(\epsilon).
\tag{40.48}
$$
阶一接口确已饱和；更直接地，二原子行列式给
$$
\det\mathsf H_1(t)
=\epsilon(1-\epsilon)(e^{-\epsilon^2}-e^{-1})^2
 e^{-(\epsilon^2+1)t}.
\tag{40.49}
$$
所以（40.15）的锚对固定为0与1时，目标2与3的比恰为2与3。基准块行列式趋零而迹趋2，最小 Gram 特征值趋零，故没有共同正的 Gram 下界。$\square$

这说明在未限制来源族上不能断言响应数据统计量的统一连续模；它并非两个完整已获档案相同的例子。若旧档案含能区分这两个事件的外部时间戳，必须保留。要提升成完整观察者的 minimax 碰撞，还须构造同时解释同一整份实际记录、合法历史和联合误差的两个允许世界；本例未提出这种额外结论。

**命题 40.14（独立的弱锚障碍）。** 一维来源 $B=1,C=\epsilon>0,h=1$ 精确饱和，$A=K(0)=1$ 有固定 Gram 下界，但
$$
K(2)-K(3)=e^{-2\epsilon}(1-e^{-\epsilon})=O(\epsilon),\qquad
\frac{-\log K(2)}{-\log K(1)}=2,\quad
\frac{-\log K(3)}{-\log K(1)}=3.
\tag{40.50}
$$

证明。$K(t)=e^{-\epsilon t}$，所以每个非空历史块秩一，相邻阶数精确平坦。$1-e^{-\epsilon}\le\epsilon$ 给数据差界，取对数给两比值；锚分母为 $\epsilon\to0$。$\square$

此例将锚条件与秩／支撑退化分开：即使真实支撑不变、基准 Gram 间隔不退化，没有锚对数下界仍无该来源族上的统一比值稳定性。在定理40.8中，对这个类不能保持统一 $v<1$ 或 $\alpha>0$。

**命题 40.15（数值不能认证来源、校准或响应类型）。** 以下是恢复卷引理15.8、命题15.9—15.10、命题12.7与本卷命题22.2所保留的不同障碍。

取两个不同来源 $C_A=1,C_B=2,B_A=B_B=1$，两只本地钟都等于同一个真实时间。两读数为 $e^{-\tau}$、$e^{-2\sigma}$，沿 $\sigma=\tau/2$ 数值完全匹配，真实钟却同速。未知增益又满足
$$
k e^{-t}=e^{-(t-\log k)}\qquad(k>0),
\tag{40.51}
$$
所以未校准或改变增益可与年龄混淆；矩阵条目间来源、增益与内积一致是实质条件。

任意给定的自由轨迹 $Be^{-tC}x_0$ 并不自动供应完整核 $Be^{-tC}B^*$。例如一维 $B=C=1$ 时 $x_0=1$ 与 $x_0=-1$ 具有相同核，输出分别为 $e^{-t}$ 与 $-e^{-t}$；把这些轨迹堆成 Hankel 阵并不消去初态。实际核取得须有合法的基准／脉冲或其他已校准协议，完整矩阵还须覆盖声明的输入方向。证明分别是指数代入与线性系统解式
$$
y(t)=Be^{-tC}x_0+\int_0^tBe^{-(t-v)C}B^*f(v)\,dv,
\tag{40.52}
$$
其中核仅确定积分项；这正是恢复卷命题12.7的分离。

未参考的准备原点仍不能从任意未知基准恢复，绝对单位受推论40.5的尺度变换约束；不同来源或准备不能逐条拼接。非线性标签的相同初始速率也不足以支持等距延迟：例如 $f(\tau)=\tau+\tau^2$ 在零点导数为1，但 $f(2\eta)-f(0)=2\eta+4\eta^2\ne2\eta+2\eta^2=2(f(\eta)-f(0))$。恢复卷命题15.10还证明这种重标一般不保持固定生成元。本卷命题22.2给更强的完整标记曲线歧义：$e^{-\phi(s)}=\tfrac12(e^{-s}+e^{-2s})$，其中 $\phi(s)=-\log[\tfrac12(e^{-s}+e^{-2s})]$、$1<\phi'(s)\le3/2$；实际一率与二率来源在共同有界钟率合同内仍可有相同完整标记流。这不满足此处已认证的同一个加性半群延迟合同，不能拿曲线数值补足该合同。$\square$

**命题 40.16（抽象对数射线可行性不认证实际延迟块）。** 对一个非零有限内积空间 $E$，给 $A>0$ 及含指定锚 $*$ 的非空正定事件矩阵族 $(H_e)$，要求 $L_e=-\log(A^{-1/2}H_eA^{-1/2})>0$。在这个抽象矩阵数据类内，全部 $L_e$ 是一条正射线上的正倍数，当且仅当它们可写成同一个正生成元的单射响应 $A=DD^*$、$H_e=De^{-s_eG}D^*$，其中 $D:E\to E$ 可逆、$G>0$、$s_e>0$。由单射实现推出射线条件，使用定理40.4的正交白化论证；由射线条件构造实现，选锚 $L_*$、写 $L_e=c_eL_*$，取 $G=L_*$、$D=A^{1/2}$、$s_e=c_e$（锚为1），直接代入即可。这只证明该抽象类有实现，不认证实际来源、年龄或延迟重叠。对于阶 $r$ 的块数据，记 $W(s)=A^{-1/2}H(s)A^{-1/2}$（限制到 $E$），在环境 $U^{r+1}$ 中将 $A^{1/2}$ 延拓为支撑外零，令 $E_i:U\to U^{r+1}$ 插入第 $i$ 个系数块、$F_i=A^{1/2}E_i:U\to E$、$T_E=W(h)$；要把这份规范单射响应解释成真实延迟结构，必须另外满足
$$
F_i=T_E^iF_0\quad(0\le i\le r),\qquad
W(s_e)=T_E^{s_e/h},\qquad
H(s_e)[i,j]=F_0^*T_E^{i+j+s_e/h}F_0,
\tag{40.53}
$$
以及共同来源与重叠合同；最后一式由前两式及 $H(s_e)[i,j]=F_i^*W(s_e)F_j$ 推出。反例取 $U=\mathbb R,r=1,A=I_2,H(h)=\eta I_2$、$0<\eta<1$：$L(h)=(-\log\eta)I_2>0$ 完全满足抽象射线条件，却把同一个声称的 $K(h)$ 赋值为 $A[0,1]=0$ 和 $H(h)[0,0]=\eta$，矛盾；亦有 $F_1=e_1\ne\eta e_0=T_EF_0$。这条重叠反证足以阻止把数据可行性提升为实际历史，不另建实现理论；本卷命题22.2的完整曲线歧义仍是更强的既有边界。定理40.4的 $D_a$ 也只是证明因子，不是已获授权的新实际准备。$\square$

### 40.6 实际取得、联合误差与适用边界

**命题 40.17（响应矩阵计数及较小接口）。** 固定定义40.1的来源与延迟合同。一个阶 $r$ 块 $\mathsf H_r(b)$ 由 $K(b),K(b+h),\ldots,K(b+2rh)$ 共 $2r+1$ 个不同时间的响应矩阵构成；其 $(r+1)^2$ 个块条目包含重复。表40.1给足够的响应矩阵数，不是最少标量读取或准备次数。

| 表40.1项 | 共同基准所需时间范围 | 不同响应矩阵数及作用 |
|---|---|---|
| 40.1a 一个阶 $r$ 块 | $b,b+h,\ldots,b+2rh$ | $2r+1$；目标块若未取得，需实际获取这段响应。 |
| 40.1b 基准及一步锚 | $a,a+h,\ldots,a+(2r+1)h$ | $2r+2$；构成 $\mathsf H_r(a),\mathsf H_r(a+h)$。 |
| 40.1c 下一 Gram 或 $s=h$ 倍时 | $a,a+h,\ldots,a+(2r+2)h$ | $2r+3$；分别构成 $\mathsf H_{r+1}(a)$ 或三块 $\mathsf H_r(a),\mathsf H_r(a+h),\mathsf H_r(a+2h)$，两诊断无取得差别。 |
| 40.1d 已见相邻平台，$r\ge1$ | $a,a+h,\ldots,a+2rh$ | $2r+1$；$\mathsf H_r(a),\mathsf H_{r-1}(a)$ 秩相等时认证较小阶 $r-1$，其一步锚已在此范围。 |
| 40.1e 平台后较小目标 | $b,b+h,\ldots,b+(2r-2)h$ | $2r-1$，除非这些同源实际读数已经取得；之后所有行列式均用同一个较小阶 $r-1$。 |

证明。块指标和 $i+j$ 逐个覆盖整数 $0,\ldots,2r$，一次和两次移位分别多一个、两个末端时间，给前三行。较小阶的一步锚最多用到 $a+(2r-1)h$，包含在认证较大阶平台所需的范围内；其新目标块有 $2(r-1)+1=2r-1$ 个时间。平台确认证较小接口由定理40.3承担。$\square$

**假设 40.18（矩阵取得与同一个联合误差事件）。** 这些响应矩阵必须来自实际输入 $B^*u$ 及校准输出 $B$，并具有共同年龄、来源、耦合、内积、单位和增益。完整矩阵列要求声明的输入方向与输出读数。可以通过重复准备取得，前提是已认证共同来源、起点、耦合、增益、可重复性和定时等价；发生测量扰动时，还需等价响应实验的理由。未知当前年龄不妨碍从当前事件开始使用已知后续延迟，却既不供应这些延迟，也不认证原始读数是核实验。异步数字时间戳本身不足以断言真实时间为 $a+(i+j)h$。恢复卷引理15.8、命题15.9—15.10、定理21.2、命题21.3及21.6处理共同源钟与有限谱接入；其中21.7明确是假设合同，不是自动证书。

设在一个允许的联合事件上，每个实际响应矩阵及其比较值满足 $\|K(t)-\widetilde K(t)\|_F\le\epsilon$，取值覆盖全部用到的实际时间。重复出现的原始读数仍是同一个随机量，不另造独立误差。恢复卷推论12.5于是直接给
$$
\|\mathsf H_r(b)-\widetilde{\mathsf H}_r(b)\|_F^2
=\sum_{i,j=0}^r\|K(b+(i+j)h)-\widetilde K(b+(i+j)h)\|_F^2
\le(r+1)^2\epsilon^2.
\tag{40.54}
$$
因此块误差至多 $(r+1)\epsilon$，同一基准的共享误差继续进入定理40.8的两个 $d_j$。若真实块与一份已选合法拟合各自对同一原始块有误差界，则按恢复卷推论12.5先作三角相加；拟合一侧的谱间隔不能替代真实一侧的谱间隔。式（40.54）只在指定联合事件上作确定性会计，不供应该事件概率，也不要求噪声独立。

取得费用分别计输入方向、矩阵与标量读数、重复准备、等待、来源／校准认证、存储、数值精度和计算；表40.1不把任何项设为零。精确期望、精确秩和真实谱间隔是这里的数学输入，经验有限样本要认证它们仍需实验专属证明。

**约定 40.19（供应归属与尚未涵盖的任务）。** 本节的主链依次使用主卷第126.1—126.5节的有效／不可见分解、Gram 配对、Krylov增长与正交识别；第137.2—137.5、137.7—137.13条的实际／抽象实现条件、竞争扩张和精确平坦；主卷定理128.5在第128.4节证明中的半正定行列式等号机制。恢复卷第10.1—10.2节与命题10.6供应采样正性和唯一自伴对数；定理12.2、方程（12.7）、定理12.3未放宽的对数步骤供应矩阵误差，推论12.5供应共享块会计，命题12.6—12.7分别保留真实维数与未知初始化边界；定理13.4的方程（13.10）及其证明只供应残差平方，命题13.8供应路径可见性机制。主卷第137.15—137.18条已有的弱方向及统一性限制继续有效。这里的延迟消费者和具体解析例是普通数学应用，既有证明与文献归属保持原处，不把它们宣称为新的通用定理、新 Lean 结果或已做完的外部新颖性审查。

恢复卷第15.8—15.10、21.2—21.3、21.6条与假设21.7只在各自共同来源、原点、增益、尺度和实际谱取得前提下接入；本卷命题22.2以及第30—36节的完整档案、保留参考、联合误差、顺序和合法取得纪律继续限制解释。有限任务恢复不替代整个观察者，也不把单一任务的数学闭合提升为任意后续实验的接口等价。

本节没有建立带噪支撑／饱和认证、定量近饱和估计、变化支撑上的间隔稳定性、有符号间隔的噪声推广、置信界或最优取得复杂度。它也不识别任意未知钟函数、未观测事件、无参考来源纪元、绝对物理单位或不可见方向，不保证扩大干预语言后的恢复。迟时的 Gram 与对数下界、锚分母下界和实际数据误差仍需另证。空间、时间、边界与记忆之间可恢复的关系在这里限于同一有限正伴随来源和已声明合法历史；这些结论不构成整个持续关系统一问题的完成。

## 40.99 追加锚

## 41. 固定发射档案的共同终端恢复与合法来源距离

### 41.1 固定装置、完整参考与终端任务

**定义 41.1（同一次准备的相干发射接口）。** 本节记 [量子上下文卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) 为 Q，[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md) 为恢复卷。固定 Q 命题130.1、131.1 的基、相位和装置：
$$
\begin{gathered}
\alpha=(\sqrt5-1)/2,\qquad \alpha+\alpha^2=1,\qquad M=B=\mathbb C^2,\\
m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,
\qquad P_j=|m_j\rangle\langle m_j|,\\
T|j\rangle=|j\rangle\otimes m_j,\qquad
H_n=B^{\otimes n},\quad H_0=\mathbb C,\\
T_0=I_M,\qquad T_{n+1}=(I_{H_n}\otimes T)T_n,\qquad
\Gamma_n(X)=\operatorname{Tr}_M(T_nXT_n^*),\\
E(X)=\operatorname{Tr}_B(TXT^*)=X_{00}P_0+X_{11}P_1.
\end{gathered}
\tag{41.1}
$$
输出在前、活动记忆在后；$E$ 是记忆通道，不是环境寄存器。$T$ 是发射等距，下文 $R_n$ 是交叉算子，均不与 Q 定理13.3 所用的交叉算子符号 $T$ 混同。Q 命题130.1 的整个四维酉为
$$
R_{\rm rot}=\begin{pmatrix}\sqrt\alpha&-\alpha\\\alpha&\sqrt\alpha\end{pmatrix},\qquad
W=\bigl(|0\rangle\langle0|\otimes R_{\rm rot}
       +|1\rangle\langle1|\otimes I_M\bigr)\operatorname{SWAP},\qquad
W(|0\rangle\otimes\psi)=T\psi.
\tag{41.2}
$$
每步空白是与此前全部系统独立的实际纯态 $|0\rangle$；整个运行只使用同一个 $W$。不允许生成期间的反馈改变 $W$、空白准备或活动 $M$。

固定有限维 $J$，一次运行的初态是同一个 $\theta\in\mathcal D(J\otimes M)$；各时域是这次准备的不同前缀，不逐时域另选初态。$J$ 保留模型中声明的有限经典档案、有限量子参考及其联合关系，不要求 $J$ 与 $M$ 独立。这正接续本卷定义36.4允许的真实非根联合准备以及命题36.6的固定生成器终端访问。完整已获观察者仍按第13、35、36节保留内外记录、来源和装置身份、相位与其它校准、时间戳和钟的共同约束、动作守卫及顺序、误差、失败、停止和既有结果；新增已获约束限制合法来源类，不能通过删档案制造自由准备。若真实档案大于这里的 $J$，必须另给它的表示；有限 $J$ 不自动穷尽真实观察者。

对每个固定整数 $n\ge1$，任务是找一个
$$
\mathcal D_n:\mathcal L(H_n)\longrightarrow\mathcal L(M)
\tag{41.3}
$$
的共同 CPTP 终端解码器，恢复未知初始 qubit 及其与任意有限保留参考的关系。它只访问全部已发出的相干寄存器，不访问 $J$ 或最终活动 $M$；竞争解码器也必须具有完全相同的输入输出类型和访问范围。$H_n$ 随 $n$ 改变，所以 $(\mathcal D_n)_{n\ge1}$ 是通道族，不是一个与时域无关的通道。允许操作须包含下文的受控极分解酉及丢弃；抽象 CPTP 优化不证明受限门集具有同样的实现费用或精确综合能力。相干输出可被终端解码消耗；若已不可逆地按计算基测量，则此项访问已失去，控制更大环境能否恢复它须另证。本任务不含在线记忆干预、无损复制、复位或未知装置校准。

先固定全部范数约定：
$$
\begin{gathered}
F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1
\quad\text{（根保真度）},\qquad
D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1,\\
\epsilon_n=\|\mathcal D_n\Gamma_n-\operatorname{id}_M\|_\diamond
\quad\text{（完整 diamond 范数）},\qquad
\kappa_n=\epsilon_n/2
=d_\diamond(\mathcal D_n\Gamma_n,\operatorname{id}_M).
\end{gathered}
\tag{41.4}
$$
$D$ 即本卷第10节的 $d_1$；$d_\diamond$ 采用命题10.7、式（10.12）的半范数约定，包含所有有限参考。Uhlmann 的 transition probability 是这里根保真度的平方，不是 $F$ 本身。以下保真度、解码器及最优性均从 $n\ge1$ 开始；$n=0$ 仅用于局部代数与档案记账。

### 41.2 条件记忆、共同解码器与精确有限误差

**定理 41.2（固定装置的最优档案恢复及显式尾界）。** 在定义41.1的访问合同下，置
$$
\lambda=-\alpha^2,\qquad
\pi_0=\frac1{1+\alpha^2},\qquad
\pi_1=\frac{\alpha^2}{1+\alpha^2},\qquad
\tau(u)=(1-u)P_0+uP_1.
\tag{41.5}
$$
对每个 $n\ge1$，条件终端记忆与其根保真度为
$$
\begin{gathered}
E^n(|0\rangle\langle0|)=\tau(a_n),\qquad
E^n(|1\rangle\langle1|)=\tau(b_n),\\
a_n=\pi_1(1-\lambda^{n-1}),\qquad
b_n=\pi_1+\pi_0\lambda^{n-1},\qquad a_n-b_n=-\lambda^{n-1},\\
c_n=F(\tau(a_n),\tau(b_n)),\qquad
c_n^2=1-\alpha^2
 \left[\sqrt{a_n(1-b_n)}-\sqrt{b_n(1-a_n)}\right]^2.
\end{gathered}
\tag{41.6}
$$
有 $c_1=\sqrt\alpha$、$\alpha\le c_n^2<1$，且 $c_n\to1$。存在只由装置与 $n$ 决定的单个 $\mathcal D_n$，在所有 $X\in\mathcal L(M)$ 上满足
$$
\mathcal D_n\Gamma_n(X)
=\begin{pmatrix}X_{00}&c_nX_{01}\\c_nX_{10}&X_{11}\end{pmatrix}
=\frac{1+c_n}{2}X+\frac{1-c_n}{2}ZXZ,
\qquad Z=|0\rangle\langle0|-|1\rangle\langle1|.
\tag{41.7}
$$
其完整 diamond 误差恰为
$$
\boxed{\epsilon_n=1-c_n
=\min_{\substack{\mathcal D:\mathcal L(H_n)\to\mathcal L(M)\\
                         \mathcal D\ {\rm CPTP}}}
\|\mathcal D\Gamma_n-\operatorname{id}_M\|_\diamond>0.}
\tag{41.8}
$$
若实际允许通道类包含所构造的 $\mathcal D_n$，同一最优值也在该类达到；未证明受限操作能执行它时，只保留全 CPTP 类的数学最优值和对受限类的下界。对 $n\ge3$，另有
$$
0<\epsilon_n\le\frac{\alpha^{4n-6}}4,\qquad
\epsilon_n\sim\frac{(1+\alpha^2)^2}{8}\alpha^{4n-4}.
\tag{41.9}
$$
因此给定完整误差容限 $\eta>0$，一个充分的发射数为
$$
n\ge\max\left\{3,
\left\lceil\frac32+
\frac{\log(1/(4\eta))}{4\log(1/\alpha)}\right\rceil\right\}.
\tag{41.10}
$$

证明。先直接应用 Q 命题131.1的记忆通道。第一步的两个条件态分别是 $P_0,P_1$，对应权重 $a_1=0,b_1=1$；由
$$
\tau(u)_{11}=\alpha^2(1-u),\qquad
E(\tau(u))=\tau\bigl(\alpha^2(1-u)\bigr)
\tag{41.11}
$$
知以后每步都把 $u$ 送到 $\alpha^2(1-u)$。该仿射映射的不动点为 $\pi_1$，偏差每步乘 $\lambda$；以两个初值求解即得（41.6）的 $a_n,b_n$。特别地二者始终在 $[0,1]$，差的绝对值为 $\alpha^{2n-2}>0$。

在固定基中，
$$
\tau(u)=\begin{pmatrix}
\alpha(1-u)+u&\alpha\sqrt\alpha(1-u)\\
\alpha\sqrt\alpha(1-u)&\alpha^2(1-u)
\end{pmatrix},\qquad
\det\tau(u)=\alpha^2u(1-u).
\tag{41.12}
$$
若 $s_1,s_2$ 是 $\sqrt\rho\sqrt\sigma$ 的两个奇异值，则
$$
F(\rho,\sigma)^2=(s_1+s_2)^2
=\operatorname{Tr}(\rho\sigma)+2\sqrt{\det\rho\det\sigma}.
\tag{41.13}
$$
这是因为 $s_1^2+s_2^2=\operatorname{Tr}(\rho\sigma)$，$s_1s_2=|\det(\sqrt\rho\sqrt\sigma)|$；零奇异值时同样成立，无需求逆。由 $\operatorname{Tr}(P_0P_1)=\alpha$ 及 $1-\alpha=\alpha^2$，
$$
\operatorname{Tr}(\tau(a)\tau(b))=1-\alpha^2(a+b-2ab).
\tag{41.14}
$$
代入（41.12）并展开（41.13），即得（41.6）的平方根差公式。取 $a=0,b=1$ 得 $c_1^2=\alpha$。括号内两个非负数都至多一，差的平方至多一，故 $c_n^2\ge1-\alpha^2=\alpha>0$；差等于零当且仅当 $a_n(1-b_n)=b_n(1-a_n)$，也就是 $a_n=b_n$，已被排除，所以 $c_n<1$。两权重趋于 $\pi_1$，同一公式给 $c_n\to1$。

现在保留实际纯化而构造同一个解码器。令
$$
K_n=B^{\otimes(n-1)},\qquad
\psi_{j,n}=T_{n-1}m_j\in K_n\otimes M,\qquad
T_n|j\rangle=|j\rangle\otimes\psi_{j,n},\qquad
R_n=\operatorname{Tr}_M|\psi_{0,n}\rangle\langle\psi_{1,n}|.
\tag{41.15}
$$
递推给上述分解；两 $\psi_{j,n}$ 均为单位向量，对 $K_n$ 取偏迹正是（41.6）的条件记忆，因而
$$
\|R_n\|_1=c_n.
\tag{41.16}
$$
这里使用有限纯化的交叉偏迹恒等式：将 $M$ 放到左因子后，Watrous 的 Theorem 3.22、Corollary 3.23 给出记忆边缘的根保真度等于另一因子上的交叉偏迹范数；互换两向量只把交叉算子变为伴随，不改变迹范数。实际纯化已经供应所需维数，包括 $K_1=\mathbb C$ 时两个记忆态均为纯态的端点。文献中的一般恒等式保持其归属；此处只计算这两个实际条件态。[^rroctx41_fidelity]

取 $R_n=V_n|R_n|$ 的极分解。有限方阵的初、终支撑同维，补空间也同维，故将部分等距延拓为 $K_n$ 上的酉，仍记 $V_n$。在 $H_n=\mathbb C^2\otimes K_n$ 上置
$$
U_{{\rm dec},n}=|0\rangle\langle0|\otimes I_{K_n}
                 +|1\rangle\langle1|\otimes V_n,\qquad
\mathcal D_n(Y)=\operatorname{Tr}_{K_n}
                  (U_{{\rm dec},n}YU_{{\rm dec},n}^*).
\tag{41.17}
$$
酉共轭后偏迹为 CPTP。在（41.15）的首位分块中，$\Gamma_n(X)$ 的 $ij$ 块为 $X_{ij}\operatorname{Tr}_M|\psi_{i,n}\rangle\langle\psi_{j,n}|$。两个对角块的迹均为一，上非对角块经过控制酉后其迹为
$$
\operatorname{Tr}(R_nV_n^*)
=\operatorname{Tr}(V_n|R_n|V_n^*)
=\operatorname{Tr}|R_n|=c_n;
\tag{41.18}
$$
下非对角系数为其共轭，亦为 $c_n$。这证明了所有矩阵单位上的（41.7），再由线性性得到全算子恒等式。因此张量任意有限参考恒等通道时仍成立，不是为每个输入重新选择一次极分解。此操作是 Q 第13.2—13.3节受控极分解恢复的同一机制：其中 $S$ 对应首个输出 qubit，$F$ 对应 $K_n$，不可访问的 $B$ 对应最终活动 $M$。本节取单结果 POVM $M_{\rm POVM}=I_{K_n}$，只留常值经典输出；它不承担 Q 定理13.3要求的额外非平凡同时经典预测。

两个酉通道之差的 diamond 范数至多二，而 $|+\rangle$ 在 $\operatorname{Ad}_Z$ 与恒等通道下分别成为正交的 $|-\rangle$、$|+\rangle$，故 $\|\operatorname{Ad}_Z-\operatorname{id}\|_\diamond=2$。由（41.7），完整误差为 $((1-c_n)/2)\cdot2=1-c_n$。另一方面，对任意所述类型的 CPTP 竞争者 $\mathcal D$，写 $\delta=\|\mathcal D\Gamma_n-\operatorname{id}\|_\diamond$。两个输入 $\rho_\pm=|\pm\rangle\langle\pm|$ 的距离为一，档案差为
$$
\Gamma_n(\rho_+)-\Gamma_n(\rho_-)
=\begin{pmatrix}0&R_n\\R_n^*&0\end{pmatrix},\qquad
D(\Gamma_n(\rho_+),\Gamma_n(\rho_-))=\|R_n\|_1=c_n.
\tag{41.19}
$$
块矩阵的平方为 $\operatorname{diag}(R_nR_n^*,R_n^*R_n)$，所以其迹范数为 $2\|R_n\|_1$。本卷引理10.6的收缩和命题10.9的两态比较现在给
$$
1\le D(\rho_+,\mathcal D\Gamma_n(\rho_+))
 +D(\mathcal D\Gamma_n(\rho_+),\mathcal D\Gamma_n(\rho_-))
 +D(\mathcal D\Gamma_n(\rho_-),\rho_-)
\le\delta/2+c_n+\delta/2.
\tag{41.20}
$$
故 $\delta\ge1-c_n$，所构造的共同解码器达到它，证明（41.8）。该最优性针对完整未知输入类；受限合法来源类仍继承上界，却可能有更小最优误差。每个有限 $n$ 的正误差与极限趋零同时成立。

最后证明尾界。权重前两次更新给 $a_3=\alpha^3,b_3=\alpha^2$。映射 $f(u)=\alpha^2(1-u)$ 递减，且
$$
f(\alpha^2)=\alpha^3,\qquad
\alpha^3\le f(\alpha^3)\le\alpha^2,
\tag{41.21}
$$
后一式使用 $\alpha^3\le\alpha^2$ 和 $0\le\alpha^3$。故区间 $[\alpha^3,\alpha^2]$ 不变，对所有 $n\ge3$ 两权重均在此区间。有理化平方根差及 $1-c_n$ 得
$$
\epsilon_n=
\frac{\alpha^2(a_n-b_n)^2}
 {\left[\sqrt{a_n(1-b_n)}+\sqrt{b_n(1-a_n)}\right]^2(1+c_n)}.
\tag{41.22}
$$
这时 $u\ge\alpha^3$、$1-u\ge1-\alpha^2=\alpha$，所以分母方括号的每个平方根至少为 $\alpha^2$。用 $1+c_n\ge1$ 和 $(a_n-b_n)^2=\alpha^{4n-4}$ 得（41.9）的上界。又两权重趋于 $\pi_1$、$c_n\to1$，（41.22）的分母趋于 $8\pi_0\pi_1$；而 $\pi_0\pi_1=\alpha^2/(1+\alpha^2)^2$，给所述渐近等价。对 $\alpha^{4n-6}/4\le\eta$ 取对数便得（41.10）。$\square$

式（41.10）是充分发射数，不是最优整数时域或门、测量、样本及计算复杂度；相干档案存储和实际取得仍是资源。发射指标不等于物理时长、半衰期或熵产生率。

### 41.3 活动记忆的运输与整个像空间的终端重建

**命题 41.3（同一完整观察者的两种嵌入及保迹左逆）。** 定义41.1下，完整有限观察者为
$$
G_n=J\otimes H_n\otimes M,\qquad
\Omega_n^\theta=(I_J\otimes T_n)\theta(I_J\otimes T_n^*).
\tag{41.23}
$$
令 $\Sigma_{M,B}:M\otimes B_{\rm blank}\to B_{\rm blank}\otimes M$ 为末两因子交换，按 Q 的 $W$ 输入次序定义
$$
U_n=(I_{J\otimes H_n}\otimes W)
    (I_{J\otimes H_n}\otimes\Sigma_{M,B})
   :G_n\otimes B_{\rm blank}\longrightarrow G_{n+1}.
\tag{41.24}
$$
则
$$
\begin{gathered}
\Omega_{n+1}^\theta=U_n(\Omega_n^\theta\otimes|0\rangle\langle0|)U_n^*,\\
j_n(A)=U_n(A\otimes I_B)U_n^*,\qquad
\operatorname{Tr}(\Omega_{n+1}^\theta j_n(A))
=\operatorname{Tr}(\Omega_n^\theta A).
\end{gathered}
\tag{41.25}
$$
$j_n:\mathcal L(G_n)\to\mathcal L(G_{n+1})$ 为单射幺星同态。对被动档案代数 $\mathcal L(J\otimes H_n)$，取
$$
i_n(A_{\rm out})=A_{\rm out}\otimes I_M,\qquad
p_n(A_{\rm out})=A_{\rm out}\otimes I_B,
\qquad j_n\circ i_n=i_{n+1}\circ p_n.
\tag{41.26}
$$
方块的定义域只是被动代数；含活动 $M$ 的可观测量由 $j_n$ 运输。直接对新输出取偏迹则给另一操作
$$
\operatorname{Tr}_{B_{\rm new}}\Omega_{n+1}^\theta
=(\operatorname{id}_{JH_n}\otimes E)(\Omega_n^\theta),
\tag{41.27}
$$
不必等于 $\Omega_n^\theta$。

此外，在整个 $H_n\otimes M$ 上取 $Q_n=I-T_nT_n^*$，固定任意 $\tau_0\in\mathcal D(M)$，则
$$
\mathcal L_n(Y)=T_n^*YT_n+\operatorname{Tr}(Q_nY)\tau_0
\tag{41.28}
$$
是 CPTP，并在全 $\mathcal L(M)$ 上满足 $\mathcal L_n\operatorname{Ad}_{T_n}=\operatorname{id}_M$。对每个 $n\ge1$，从被动档案恢复完整等距像的最优终端误差亦为
$$
\min_{\substack{\mathcal R:\mathcal L(H_n)\to\mathcal L(H_n\otimes M)\\
                         \mathcal R\ {\rm CPTP}}}
\|\mathcal R\Gamma_n-\operatorname{Ad}_{T_n}\|_\diamond=\epsilon_n.
\tag{41.29}
$$

证明。（41.2）在全记忆输入上为线性恒等式，张量旧档案及参考恒等后仍成立；在右端插入独立纯空白并按（41.24）交换到 $W$ 的输入次序，便给（41.25）的态运输。$U_n$ 是两个酉的乘积，故共轭保持单位、乘法与伴随；$A\mapsto A\otimes I_B$ 单射，$j_n$ 也单射。循环移迹并用 $\operatorname{Tr}|0\rangle\langle0|=1$ 得期望恒等式。

对（41.26），$i_n(A_{\rm out})\otimes I_B$ 经末两因子置换后为 $A_{\rm out}\otimes I_B\otimes I_M$；$W$ 只作用于这两个恒等因子，故共轭不改变它。这证明被动方块。相反，对（41.23）的 $M$ 矩阵块分别应用 $\operatorname{Tr}_B(TXT^*)=E(X)$ 得（41.27）；块中可以含全部旧档案关联，不使用乘积假设。已经在 $n=0$、$J$ 平凡、$\theta=|0\rangle\langle0|$ 时，右端为 $P_0\ne|0\rangle\langle0|$，故直接丢弃新输出不是旧活动记忆的恒等运输。

等距性使 $Q_n$ 为正交投影。压缩 $Y\mapsto T_n^*YT_n$ 是 CP。选 $\operatorname{ran}Q_n$ 的正交标准基 $(e_a)_a$，并将 $\tau_0=\sum_b p_b|u_b\rangle\langle u_b|$ 谱分解。附加 Kraus 算子
$$
K_{ba}=\sqrt{p_b}|u_b\rangle\langle e_a|
\quad\text{满足}\quad
\sum_{a,b}K_{ba}YK_{ba}^*
=\operatorname{Tr}(Q_nY)\tau_0,\qquad
\sum_{a,b}K_{ba}^*K_{ba}=Q_n.
\tag{41.30}
$$
加上 Kraus 算子 $T_n^*$，伴随平方之和为 $T_nT_n^*+Q_n=I$，故（41.28）在整个输入空间上保迹且完全正，不只在等距像上成立。由 $Q_nT_n=0$、$T_n^*T_n=I$，直接代入任意 $X$ 得左逆。单独压缩在像外没有保迹性，不能替代（41.28）。张量 $\operatorname{id}_J$ 给联合左逆，并不取迹或替换 $J$。

取 $\mathcal R=\operatorname{Ad}_{T_n}\mathcal D_n$，通道后处理收缩给（41.29）的上界。任取竞争 $\mathcal R$，$\mathcal L_n\mathcal R$ 是（41.8）允许的档案到初始记忆通道，所以
$$
\epsilon_n\le
\|\mathcal L_n\mathcal R\Gamma_n-\operatorname{id}_M\|_\diamond
\le\|\mathcal R\Gamma_n-\operatorname{Ad}_{T_n}\|_\diamond.
\tag{41.31}
$$
下界与上界相合。$\square$

完整等距态保留初态和全部参考关联；被动档案只是它的任务边界。（41.29）构造一个新的终端重建输出，不同时保留一份未知输入的额外副本，也不撤销已取得的不可逆测量。

### 41.4 保留同一有限参考的完成距离与紧来源极小值

**定理 41.4（统一恢复尾控制同一来源类的完成距离）。** 固定定义41.1的有限 $J$，取两个联合来源 $\theta_0,\theta\in\mathcal D(J\otimes M)$。定义
$$
q_n(\theta)=(\operatorname{id}_J\otimes\Gamma_n)(\theta)\quad(n\ge1),
\qquad q_0(\theta)=\operatorname{Tr}_M\theta,\qquad
d_n(\theta)=D(q_n(\theta_0),q_n(\theta)).
\tag{41.32}
$$
则 $d_n(\theta)$ 随 $n\ge0$ 单调不减，且对 $n\ge1$ 有
$$
0\le D(\theta_0,\theta)-d_n(\theta)\le\epsilon_n,
\qquad \sup_{n\ge0}d_n(\theta)=D(\theta_0,\theta).
\tag{41.33}
$$
在有限参考局部代数塔
$$
\mathcal A_n^J=\mathcal L(J)\otimes\mathcal L(H_n),\quad n\ge0,
\qquad A\longmapsto A\otimes I_B,
\qquad \mathcal A^J=\overline{\bigcup_{n\ge0}\mathcal A_n^J}^{\|\cdot\|}
\tag{41.34}
$$
上，存在唯一态 $\omega_\theta$ 满足 $\omega_\theta(A)=\operatorname{Tr}(q_n(\theta)A)$，$A\in\mathcal A_n^J$，并且
$$
\boxed{\tfrac12\|\omega_{\theta_0}-\omega_\theta\|_{(\mathcal A^J)^*}
=\sup_{n\ge0}d_n(\theta)=D(\theta_0,\theta).}
\tag{41.35}
$$
这里 $\mathcal A^J$ 为固定有限矩阵因子 $\mathcal L(J)$ 与单侧 qubit UHF 代数的空间张量积。

若 $\Theta\subseteq\mathcal D(J\otimes M)$ 是固定非空紧的合法来源类，$\theta_0$ 可在其外，令
$$
E_* =\min_{\theta\in\Theta}D(\theta_0,\theta),\qquad
e_n =\min_{\theta\in\Theta}d_n(\theta).
\tag{41.36}
$$
则两极小值均达到，$e_n\le e_{n+1}$，并且
$$
e_n\le E_*\le e_n+\epsilon_n\quad(n\ge1),\qquad
E_*=\sup_{n\ge0}e_n.
\tag{41.37}
$$
一个实际取得的 $\theta_n\in\Theta$ 若满足 $d_n(\theta_n)\le e_n+\eta$、$\eta\ge0$，则同一来源的完成距离满足
$$
\tfrac12\|\omega_{\theta_0}-\omega_{\theta_n}\|
=D(\theta_0,\theta_n)\le e_n+\eta+\epsilon_n.
\tag{41.38}
$$

证明。$q_n$ 是保留 $J$ 的通道输出，故引理10.6给 $d_n(\theta)\le D(\theta_0,\theta)$。将同一个 $\operatorname{id}_J\otimes\mathcal D_n$ 用于两个来源，写恢复态为 $\widehat\theta_0,\widehat\theta$。（41.4）、（41.8）及命题10.7保证 $D(\theta_0,\widehat\theta_0),D(\theta,\widehat\theta)\le\kappa_n$，所以
$$
D(\theta_0,\theta)
\le\kappa_n+D(\widehat\theta_0,\widehat\theta)+\kappa_n
\le d_n(\theta)+2\kappa_n
=d_n(\theta)+\epsilon_n.
\tag{41.39}
$$
两个单态误差相加产生这里的 $\epsilon_n$，不是 $\kappa_n$。

从实际递推 $T_{n+1}=(I_{H_n}\otimes T)T_n$ 和 $T^*T=I$，对每个 $A\in\mathcal A_n^J$ 有
$$
\operatorname{Tr}\bigl(q_{n+1}(\theta)(A\otimes I_B)\bigr)
=\operatorname{Tr}(q_n(\theta)A).
\tag{41.40}
$$
故对最新发射端口取偏迹给 $q_n(\theta)$，包括 $n=0$ 时保留的 $J$ 边缘。这里已经忽略最终活动记忆，不与（41.27）对完整观察者取偏迹混淆。偏迹收缩给 $d_n\le d_{n+1}$，再用 $\epsilon_n\to0$ 证明（41.33）。

完成态沿用 Q 命题125.2的构造，但将固定的左参考因子显式保留。（41.34）的每个嵌入都等距、幺且保持乘法和伴随，因此按这些嵌入识别后的代数并具有一致算子范数。（41.40）使局部定义 $\omega_\theta(A)=\operatorname{Tr}(q_n(\theta)A)$ 良定。局部正元的期望非负，$\omega_\theta(I)=1$，而密度的迹范数为一，给 $|\omega_\theta(A)|\le\|A\|$；故唯一连续延拓到 $\mathcal A^J$。为验证延拓正性，取任意 $C\in\mathcal A^J$ 及局部 $C_k\to C$，则 $C_k^*C_k\to C^*C$，从而 $\omega_\theta(C^*C)=\lim_k\omega_\theta(C_k^*C_k)\ge0$。每个正元是其正平方根的平方，单位值仍为一，因此延拓为态，范数亦为一。这不是把具有不同类型的固定左因子偷偷代入齐次张量定理。[^rroctx41_extension]

令 $\delta=\omega_{\theta_0}-\omega_\theta$。在第 $n$ 层，有限矩阵的迹范数／算子范数对偶给
$$
\|\delta|_{\mathcal A_n^J}\|
=\|q_n(\theta_0)-q_n(\theta)\|_1=2d_n(\theta).
\tag{41.41}
$$
具体地，迹不等式给上界；对自伴差取其谱符号算子，范数至多一且期望为差的迹范数，达到上界。由于局部单位球包含在完成单位球中，$\|\delta\|\ge\sup_n2d_n(\theta)$。反向取 $\|A\|\le1$，选局部 $B_k\to A$，再置
$$
C_k=\frac{B_k}{\max\{1,\|B_k\|\}}.
\tag{41.42}
$$
每个 $C_k$ 是某一有限层的单位球元素；且
$\|C_k-B_k\|=\max\{0,\|B_k\|-1\}\le\|B_k-A\|$，故 $C_k\to A$。连续性和（41.41）给 $|\delta(A)|\le\sup_n2d_n(\theta)$，再取单位球上确界证明反向。结合（41.33）得（41.35）。这是恢复卷命题31.9、式（31.31）—（31.32）的局部范数与范数稠密方法在固定 $J$ 上的应用；因子 $1/2$ 来自（41.41），不能只用一个投影的读数代替整个泛函范数。

最后，来源空间有限维，$D(\theta_0,\theta)$ 及 $d_n(\theta)$ 都是有限线性映射后的连续迹范数。非空紧性使（41.36）达到。逐点 $d_n\le d_{n+1}$ 给 $e_n\le e_{n+1}$。在 $E_*$ 的一个极小点 $\theta_*$ 上评价 $d_n\le D$，得 $e_n\le d_n(\theta_*)\le E_*$；在 $e_n$ 的一个极小点 $\theta^{(n)}$ 上评价（41.33），得
$$
E_*\le D(\theta_0,\theta^{(n)})
\le d_n(\theta^{(n)})+\epsilon_n=e_n+\epsilon_n.
\tag{41.43}
$$
令 $n\to\infty$，得到（41.37）。对实际近极小点直接用（41.33）、（41.35）即得（41.38）。此证明在同一个 $\Theta$ 内利用统一尾界，没有交换任意的 $\inf$ 与 $\sup$，也没有把彼此不相容的有限极小点拼成一个来源。$\square$

（41.35）是完成代数上的态泛函范数等式；它不供应事先指定无限表示中的 normal 密度，不断言实际来源映满全部相容目标，也不构造可执行的无限终端解码器。Q 命题125.4的表示边界继续有效。这里的量子迹距离不是第38—39节有限经典世界／标签上的 TV 尾；没有一个已证明的映射将那些 $d_\ell,\tau_\ell$ 与 $\epsilon_n$ 等同，不能直接替换它们的预算。

**假设 41.5（紧合法准备类与较大经典档案的表示条件）。** 定理41.4的 $\Theta$ 必须是实际允许的同一联合来源类。固定来源／参考边缘、闭支撑、对称性与交叉读数的闭约束，可以在有限密度空间内形成紧类，但只固定分开边缘不保留已知联合关系。非空性需实际见证或明列为假设。一个来源忠实的充分模型是：真实供给与准备合同固定，允许参数集 $K$ 非空紧，实际联合准备映射 $s:K\to\mathcal D(J\otimes M)$ 连续，且 $\Theta=s(K)$；连续像因而非空紧。这不要求凸性，也不因数学可行就授权某种准备。精确秩条件、严格不等式或成功概率趋零的后选择可能不闭，不能不加论证地套用紧性。紧性和极小值存在亦不供应可计算的优化器。

若另有实际保留的较大经典档案 $C$，一个可用的扩展合同是：$C$ 为标准 Borel 空间，档案律 $\mu$ 与实际正则条件密度核 $c\mapsto\theta_c\in\mathcal D(J\otimes M)$ 一并给定且可测，每个条件纤维使用相同已知装置、相位、独立空白及终端访问，档案本身原样保留。该 cq 态在 $L^1(\mu;\mathcal L(J\otimes M))$ 的迹范数表示中为 $c\mapsto\theta_c$；解码后的核为 $c\mapsto(\operatorname{id}_J\otimes\mathcal D_n\Gamma_n)(\theta_c)$。统一有限参考界逐纤维积分给
$$
\frac12\int_C
\|\theta_c-(\operatorname{id}_J\otimes\mathcal D_n\Gamma_n)(\theta_c)\|_1\,\mu(dc)
\le\int_C\kappa_n\,\mu(dc)=\kappa_n.
\tag{41.44}
$$
若比较两份条件来源核，也必须保留它们声明的同一个实际档案律；可对各纤维的（41.33）积分。条件密度核及共同 $\mu$ 是实际表示假设，不由“有档案”三个字自动推出。装置随 $c$ 变化时还需另外声明逐纤维识别和可实施性，本节不借此省去固定装置前提。（41.44）不建立任意无限量子参考上的定理，也不建立无限档案准备类的紧性。

### 41.5 实际像、根准备与保留联合关系的精确实例

**命题 41.6（共同恢复预算的可达见证与来源边界）。** 在定义41.1的固定装置中，下述实例各按其实际准备合同成立。

第一，$n=1$ 的输出通道为
$$
\Gamma_1(X)=\begin{pmatrix}X_{00}&\sqrt\alpha X_{01}\\
                         \sqrt\alpha X_{10}&X_{11}\end{pmatrix},
\qquad \epsilon_1=1-\sqrt\alpha>0.
\tag{41.45}
$$
不存在输入密度使 $\Gamma_1(X)=|+\rangle\langle+|$。因而任意相容目标族不一定属于同一实际来源像；例如各层全加乘积纯态构成相容族，却已在第一层被排除。证明是（41.1）的直接偏迹：内积 $\langle m_1,m_0\rangle=\sqrt\alpha$ 给非对角乘子。目标强迫 $X_{00}=X_{11}=1/2$、$X_{01}=1/(2\sqrt\alpha)>1/2$，从而 $\det X=1/4-1/(4\alpha)<0$，违反正性。另一方面，（41.11）给 $a_2=\alpha^2,b_2=0$ 以及 $a_3=\alpha^3,b_3=\alpha^2$，同时展示奇异端点和尾界的起点；这些公式不定义零时域保真度或解码器。

第二，若准备合同固定已知纯源 $P_0=|m_0\rangle\langle m_0|$，则它的任意联合扩展都分解为 $\theta_J\otimes P_0$，故档案到 $M$ 的替换通道 $Y\mapsto\operatorname{Tr}(Y)P_0$ 给零来源恢复误差。为证明分解，置 $P=I_J\otimes P_0$。$\operatorname{Tr}((I-P)\theta)=0$ 和 $\theta\ge0$ 给 $(I-P)\theta^{1/2}=0$，因而 $\theta=P\theta P$；$P_0$ 的像一维，所以 $\theta=\theta_J\otimes P_0$。$q_n(\theta)$ 的 $J$ 边缘仍为 $\theta_J$，张量恒等参考后的替换确实恢复它。这里 $P_0$ 不是计算基态 $|0\rangle\langle0|$；这个结论也不推广到任意已知纠缠联合单例。即使联合目标事先已知，只在 $M$ 端替换也只产生与不可访问 $J$ 的乘积态，不能重建该纠缠目标。因此（41.8）的未知全输入最优值不能冒充 Q130 固定纯根任务的最优值。

第三，假定允许实际准备具有共同相位校准的 $|+\rangle,|-\rangle$。以 $\theta_0=\rho_+$、$\Theta=\{\rho_-\}$，或二者共同张量同一独立 $J$ 态，则
$$
E_*=1,\qquad e_n=c_n,\qquad E_*-e_n=\epsilon_n\quad(n\ge1).
\tag{41.46}
$$
证明由正交输入及（41.19）给出；共同张量一个密度不改变迹范数，因为该因子的迹范数为一。这证明（41.33）的统一来源距离亏损不能普遍缩小；准备许可是该尖锐性实例的前提。

第四，令 $J=\mathbb C^2$，取真实 Bell 准备
$$
|\Phi_\pm\rangle=(|00\rangle\pm|11\rangle)/\sqrt2,\qquad
\theta_\pm=|\Phi_\pm\rangle\langle\Phi_\pm|,
\qquad X_{\rm P}=|0\rangle\langle1|+|1\rangle\langle0|.
\tag{41.47}
$$
两态分开的 $J,M$ 边缘均为 $I/2$，但 $X_{\rm P}\otimes X_{\rm P}$ 的确定性奇偶分别为 $+1,-1$。由（41.7），
$$
(\operatorname{id}_J\otimes\mathcal D_n\Gamma_n)(\theta_\pm)
=(1-\kappa_n)\theta_\pm+\kappa_n\theta_\mp.
\tag{41.48}
$$
证明只需 $I_J\otimes Z$ 将 $\Phi_+$ 与 $\Phi_-$ 互换。因此解码后终端联合奇偶测试的错误概率精确为 $\kappa_n$。这个 tester 读取允许的联合参考；解码器本身仍不访问 $J$，也未另外产生非平凡的同时经典预测输出。仅比较分开边缘会漏掉此处全部奇偶关系。

第五，若实际准备合同允许未额外记录混合标签的家庭
$$
\theta_p=(1-p)\theta_++p\theta_-,\qquad 1/2\le p\le1,
\qquad \theta_0=\theta_+,\qquad
\Theta=\{\theta_p:1/2\le p\le1\},
\tag{41.49}
$$
则这是一个非单例紧合法类，同一 $p$ 供应整个发射历史，并有
$$
D(\theta_+,\theta_p)=p,\qquad
d_n(\theta_p)=pc_n,\qquad
E_*=1/2,\quad e_n=c_n/2,\quad E_*-e_n=\epsilon_n/2.
\tag{41.50}
$$
证明。Bell 两态正交，故第一距离为 $p$。将参考和首位输出联合分块，$q_n(\theta_+)-q_n(\theta_-)$ 只在
$(|0\rangle_J|0\rangle_{B_1})\otimes K_n$ 与
$(|1\rangle_J|1\rangle_{B_1})\otimes K_n$ 的直和上非零，在这个支撑上恰为（41.19）的交叉块矩阵，故其半迹范数为 $c_n$。来源与输出差均随 $p$ 线性缩放，给第二距离；在 $[1/2,1]$ 上取最小值即得其余等式。参数映射连续，紧性与非空性亦直接成立。各态的分开边缘相同，变化的是联合关系。Bell 准备和随机化仍是资源假设；若 $p$ 或随机分支标签已被实际记录，必须把它们留在完整来源／观察者中重新评价距离，不能删去标签来制造（41.49）的约化家庭。$\square$

### 41.6 共同终端实验与可组合接口的接入

**命题 41.7（Context12的参考安全终端预算）。** 在每个固定 $n\ge1$，对定义41.1的任意实际联合输入 $\theta$，以及两种表示后使用的同一个合法终端 CPTP 通道
$\Lambda:\mathcal L(J\otimes M)\to\mathcal L(Y)$，有
$$
D\!\left(\Lambda(\theta),
\Lambda\bigl[(\operatorname{id}_J\otimes\mathcal D_n\Gamma_n)(\theta)\bigr]\right)
\le\kappa_n=\frac{1-c_n}{2},\qquad
\kappa_n\le\frac{\alpha^{4n-6}}8\quad(n\ge3).
\tag{41.51}
$$
对一个实际合法终端测量，完整结果律的经典 TV 因而至多 $\kappa_n$；对损失 $0\le\ell\le L$，期望差至多 $L\kappa_n$。本卷定义12.1、定理12.2的接入为
$$
\mathcal E=\Gamma_n,\qquad \mathcal Q=\operatorname{id}_M,
\qquad \mathcal S=\mathcal D_n,
\qquad \kappa=\kappa_n.
\tag{41.52}
$$
若另有同型合法完整操作 $\mathcal T_r:M\to M$ 与边界操作 $\overline{\mathcal T}_r:H_n\to H_n$，并另证其半 diamond 交织缺陷
$$
\delta_r=d_\diamond(\Gamma_n\mathcal T_r,
                         \overline{\mathcal T}_r\Gamma_n),
\tag{41.53}
$$
则直接应用定理12.2，$m$ 次操作的任务误差至多
$\min\{1,\kappa_n+\sum_{r=1}^m\delta_r\}$。会参与中间操作的旧记录和参考须按定义12.1计入活动类型；不能仍将其视为惰性 $J$，也不能由（41.51）自动获得新的交织缺陷界。

证明。（41.7）是全算子恒等式，（41.8）是含参考的完整 diamond 范数，故对同一 $\theta$ 恢复前后的半迹距离至多 $\kappa_n$。左接共同 $\Lambda$ 后用引理10.6收缩即得（41.51）；尾界来自（41.9）。测量通道的输出为经典对角态，其半迹距离等于 TV。两结果律差的正、负部分质量均为 TV，故 $\ell\in[0,L]$ 的积分差绝对值至多 $L\operatorname{TV}$，给损失界；这也适用于声明了可测结果空间的终端测量。将（41.52）逐项代入定义12.1后，$\kappa$ 恰为（41.4）的 $\kappa_n$；在另行满足（41.53）的同一合法接线中，由定理12.2的通道望远镜界即得后续预算。$\square$

终端相干访问是本命题的前提。命题36.6允许的输出实验若已消耗相干资源，并不因此允许再实施（41.17）；完整历史、失败及可访问装置仍须留在实际模型中。$n$ 是取得档案的发射数，$m$ 是另行声明的后续操作数，二者均不自动等于物理时间。固定任务可用一个共同解码器恢复到可控误差，不意味着整个观察者对任何扩大后的操作语言都具有同一接口。

**约定 41.8（既有供应与此消费者的量词边界）。** Q 命题130.1、131.1拥有固定发射装置与输出／记忆通道；Q 定理13.3拥有受控极分解方法；Q 命题125.2、125.4拥有局部态完成与表示限制。恢复卷命题31.9拥有局部范数与完成范数比较的方法，本节只显式保留有限左参考并计算同一装置的尾。本卷引理10.6、命题10.7—10.9、定义12.1与定理12.2供应不同有限维输入输出收缩、外部参考和共同恢复预算；第13、35节及定义36.4、命题36.6供应完整档案和合法联合准备／访问的类型。这些供应结论均保留原条件。

有限读出纤维的非空紧性可由 [PhysicalFiber 的 finite_dimensional_physical_fiber](../../../D5/S3/Quantum/Fibers/PhysicalFiber.lean) 在正性、归一化及固定线性读出的前提下供应；[CompactLocalRealization 的 compact_local_realization](../../../D5/S3/Observer/Completion/CompactLocalRealization.lean)处理紧空间中的闭局部记录相容。本节（41.37）使用同一个合法来源类上的统一定量尾，不重建一般紧性或逆极限定理。已有 [FiniteTraceDistance.traceDistance_contract](../../../D5/S3/Quantum/Foundation/FiniteTraceDistance.lean) 的类型为相同指标载体上的 `QuantumChannel i i`，不将其称为任意维数或 diamond 恢复的形式供应；此处所需的不同有限输入输出收缩由本卷引理10.6的证明承担。

Q 第145—149节仍是固定纯根来源下未知左滤波、条件报告及有限历史复现的任务；Q 第146节的 $(1-\sqrt\alpha)/2$ 是其 CP 噪声阈值，不因数字相同就成为本节未知源恢复的证明。本节为这些既有模型和成熟方法的普通数学应用；（41.6）—（41.10）的精确常数由所列条件态计算、实际解码器及两态下界共同承担，不从一般信息—扰动估计套出。[^rroctx41_background] 这里不作外部文献优先性断言，也不把源卷证明等同于新增形式核验。

[^rroctx41_fidelity]: John Watrous，*The Theory of Quantum Information*，Cambridge University Press，2018，[作者全文](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，Theorem 3.22及Corollary 3.23，式（3.145）—（3.149）：有限维纯化和交叉偏迹的根保真度恒等式。A. Uhlmann，*The “transition probability” in the state space of a \*-algebra*，Reports on Mathematical Physics **9**（1976），273–279，[doi:10.1016/0034-4877(76)90060-4](https://doi.org/10.1016/0034-4877(76)90060-4)，其式（1）采用根保真度的平方。本节未将平方约定混入（41.4）。

[^rroctx41_extension]: Sam Staton、Ned Summers，*Quantum de Finetti Theorems as Categorical Limits, and Limits of State Spaces of C\*-algebras*，[arXiv:2207.05832v2](https://arxiv.org/abs/2207.05832v2)，Theorems 2.24及4.1的塔为同一个 $C^*$ 代数的齐次张量幂。这里含固定左因子 $\mathcal L(J)$ 的具体延拓由（41.34）—（41.42）及 Q125.2的方法直接完成，不扩大这些外部定理的字面类型。

[^rroctx41_background]: Dennis Kretschmann、Dirk Schlingemann、Reinhard F. Werner，*The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation*，[arXiv:quant-ph/0605009](https://arxiv.org/abs/quant-ph/0605009)，Theorem 3为一般信息—扰动背景，采用 Heisenberg 通道及完全有界范数的约定；本节的精确最优值不依赖该定理的估计常数。

## 41.99 追加锚

## 42. 被动相干接收、完整联合来源与已获词记录的熵

本节把同一关系的两种保存任务接起来：相干发射档案可由固定四维接收器逐步保存其全部来源关联；一旦计算基词已被实际取得，精确保留那一次记录则有随词长增长的零误差容量。两者使用同一个装置，却有不同的访问、准备和输出资源合同。[量子上下文卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)以下记为 Q，[恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)以下记为恢复卷。Q130—131和恢复卷31供应共同生成器，Q125供应固定根相干态与柱律，本卷第41节供应固定档案的来源恢复。本节是这些供应及成熟相干接收、容量和熵机制的普通数学应用，不重建一般顺序压缩定理，不主张文献新颖性或新增 Lean 认证。

### 42.1 同一装置上的联合任务与纯根任务

**定义 42.1（被动接收的准备与访问合同）。** 固定
$$
\begin{gathered}
\alpha=(\sqrt5-1)/2,\qquad \phi=\alpha^{-1},\qquad
0<\alpha<1,\qquad \alpha+\alpha^2=1,\qquad B=M=\mathbb C^2,\\
m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,
\qquad P_j^{\rm mem}=|m_j\rangle\langle m_j|\in\mathcal L(M),\\
T:M\to B\otimes M,\qquad T|j\rangle=|j\rangle\otimes m_j,\\
H_n=B^{\otimes n},\quad H_0=\mathbb C,\quad T_0=I_M,\quad
T_{n+1}=(I_{H_n}\otimes T)T_n,\\
E(X)=\operatorname{Tr}_B(TXT^*)=X_{00}P_0^{\rm mem}+X_{11}P_1^{\rm mem},\qquad
\Gamma_n(X)=\operatorname{Tr}_M(T_nXT_n^*).
\end{gathered}
\tag{42.1}
$$
输出在前、活动记忆在后。上标 $\mathrm{mem}$ 明确区分记忆准备投影与后文 $H_n$ 上的支撑投影 $P_n$；它们不能互换。Q命题130.1和本卷（41.2）给固定空白酉
$$
R_{\rm rot}=\begin{pmatrix}\sqrt\alpha&-\alpha\\\alpha&\sqrt\alpha\end{pmatrix},\qquad
W=(|0\rangle\langle0|\otimes R_{\rm rot}+|1\rangle\langle1|\otimes I_M)
\operatorname{SWAP},\qquad W(|0\rangle\otimes\psi)=T\psi.
\tag{42.2}
$$
每个新空白均是与当时整个联合系统独立的纯态 $|0\rangle$。整个运行使用同一个 $W$，保留同一个活动 $M$，不插入重选来源、复位或生成器反馈。

联合任务以任意固定有限维参考 $J$ 及一次合法准备 $\theta\in\mathcal D(J\otimes M)$ 开始，保存
$$
\Omega_n(\theta)=(I_J\otimes T_n)\theta(I_J\otimes T_n^*)
\in\mathcal D(J\otimes H_n\otimes M).
\tag{42.3}
$$
这里声明的全输入类包含所有这样的密度，并允许实际准备一个 $JM$ Bell 对。接收器只访问已发出系统和它自己的、起初独立的寄存器 $K$，不访问 $J$ 或活动 $M$。若改用受限物理来源类，存在性可限制到该类；四维必要性则须先核对该类是否实际允许下文的 Bell 见证，不能从抽象全输入类移入一项非法准备。

接收酉序列只依赖已知装置、基、相位及发射计数 $n$，不依赖未知输入或接收测量结果。同一序列适用于每个事先指定的有限终端时域。由旧档案外生选定有限时域时，保留选择标签，逐实际条件来源核对相同的空白独立性和生成合同；无界经典标签另需正则条件 cq 表示。接收测量决定的任意在线停止、向 $M$ 反馈以及无限终端解码不在此合同内。

熵应用另固定初态为 $P_0^{\rm mem}$，不是 $|0\rangle\langle0|$，也不是平稳混合态。若有限联合态的 $M$ 边缘纯且等于 $P_0^{\rm mem}$，则它必为 $\theta_J\otimes P_0^{\rm mem}$：令 $P=I_J\otimes P_0^{\rm mem}$，由正性和 $\operatorname{Tr}((I-P)\theta)=0$ 得 $(I-P)\theta^{1/2}=0$，故 $\theta=P\theta P$；记忆支撑一维给出分解。这是第41.5节的同一准备事实。保留更大的旧经典档案时使用定义36.4的实际条件纯根准备，而非只凭边缘相同替换来源。全文使用自然对数；$n$ 只计发射，不是物理持续时间。

### 42.2 实际联合支撑与四列 Gram 的精确秩

**命题 42.2（所有来源块的共同档案支撑）。** 令
$$
T_n|i\rangle=\sum_{a=0}^1v^n_{i,a}\otimes|a\rangle,
\qquad v^n_{i,a}=(I_{H_n}\otimes\langle a|)T_n|i\rangle,
\qquad S_n=\operatorname{span}\{v^n_{i,a}:i,a\in\{0,1\}\}.
\tag{42.4}
$$
$\Omega_n(\theta)$ 支撑在 $J\otimes S_n\otimes M$。内积第一变量共轭线性时，以 $(0,0),(0,1),(1,0),(1,1)$ 排序的 Gram 矩阵满足
$$
G_n[(i,a),(j,b)]=\langle v^n_{i,a},v^n_{j,b}\rangle
=[E^n(|j\rangle\langle i|)]_{b,a},
\qquad \operatorname{rank}G_n=\dim S_n.
\tag{42.5}
$$
特别地，
$$
\dim S_n=1,2,3,4,4,\ldots\quad(n=0,1,2,3,4,\ldots),
\qquad S_2=\operatorname{span}\{|00\rangle,|01\rangle,|10\rangle\}.
\tag{42.6}
$$
这些是已知来源族在 $H_n$ 中的支撑，不是整个 $H_n$ 的维数。

证明。写 $\theta=\sum_{i,j}\theta^J_{ij}\otimes|i\rangle\langle j|$，直接展开
$$
\Omega_n(\theta)=\sum_{i,j,a,b}\theta^J_{ij}\otimes
|v^n_{i,a}\rangle\langle v^n_{j,b}|\otimes|a\rangle\langle b|.
\tag{42.7}
$$
每一个参考／来源非对角块也在声明支撑内。对 $T_n|j\rangle\langle i|T_n^*$ 取档案偏迹，得到
$$
E^n(|j\rangle\langle i|)
=\sum_{b,a}\langle v^n_{i,a},v^n_{j,b}\rangle|b\rangle\langle a|,
\tag{42.8}
$$
即（42.5）。若 $V_n$ 为这四列组成的映射，则 $G_n=V_n^*V_n$，两者核相同，给秩等式。这里复用 Q定理3.1的 Gram 因子化论证，保留各列的实际范数；列可能为零或非单位向量，不能原样套用其单位对角陈述。

$n=0$ 时 $v^0_{i,a}=\delta_{ai}\in\mathbb C$，因此
$$
G_0=uu^*,\qquad u=(1,0,0,1)^{\mathsf T},\qquad \operatorname{rank}G_0=1.
\tag{42.9}
$$
从 $n\ge1$ 才有 $E^n(|0\rangle\langle1|)=E^n(|1\rangle\langle0|)=0$。沿用定理41.2的条件记忆权重，置
$$
\begin{gathered}
\tau(u)=(1-u)P_0^{\rm mem}+uP_1^{\rm mem},\qquad
\lambda=-\alpha^2,\quad \pi_1=\frac{\alpha^2}{1+\alpha^2},\quad
\pi_0=\frac1{1+\alpha^2},\\
a_n=\pi_1(1-\lambda^{n-1}),\qquad b_n=\pi_1+\pi_0\lambda^{n-1},\\
G_n=\tau(a_n)^{\mathsf T}\oplus\tau(b_n)^{\mathsf T}\quad(n\ge1).
\end{gathered}
\tag{42.10}
$$
转置来自（42.5）的 $b,a$ 次序，即使本装置的所选基中矩阵为实，也不得省去这一类型关系。该分块式不用于 $G_0$。

第一步权重是 $(a_1,b_1)=(0,1)$。由 $\tau(u)_{11}=\alpha^2(1-u)$ 得
$$
E(\tau(u))=\tau(\alpha^2(1-u)),\qquad
\operatorname{Tr}\tau(u)=1,\qquad \det\tau(u)=\alpha^2u(1-u).
\tag{42.11}
$$
仿射递推的不动点为 $\pi_1$，偏差每步乘 $\lambda$，解出（42.10）。实际前三组权重为 $(0,1)$、$(\alpha^2,0)$、$(\alpha^3,\alpha^2)$。端点 $0,1$ 给秩一，内部权重给正行列式与秩二，而 $0<u<1$ 蕴含 $0<\alpha^2(1-u)<1$。于是两块的秩依次为 $(1,1),(2,1),(2,2)$，以后均为 $(2,2)$，加上（42.9）即得全 $n$ 秩序列。

也可直接看第二步的四列：
$$
\begin{aligned}
v^2_{0,0}&=\alpha|00\rangle+\alpha|01\rangle,&
v^2_{0,1}&=\alpha\sqrt\alpha|00\rangle,\\
v^2_{1,0}&=\sqrt\alpha|10\rangle,&
v^2_{1,1}&=\alpha|10\rangle.
\end{aligned}
\tag{42.12}
$$
它们张成所列 $S_2$；前三列在行 $00,01,10$ 的子式为 $-\alpha^3\ne0$，所以不是仅凭数值阈值判断秩。最后，源非对角单位在记忆通道中消失不表示其从联合态或档案消失：
$$
\Gamma_1(|0\rangle\langle1|)=\langle m_1,m_0\rangle|0\rangle\langle1|
=\sqrt\alpha\,|0\rangle\langle1|.
\tag{42.13}
$$
$\square$

### 42.3 一个对所有有限终端适用的被动接收器

**命题 42.3（四维持续接收与八维门构造）。** 取 $K=\mathbb C^4$。存在已知装置决定的线性映射 $F_n:H_n\to K$，在 $S_n$ 上等距、在 $S_n^\perp$ 上为零，以及 $K\otimes B$ 上的酉 $U_n$，满足
$$
U_n[(F_n\otimes I_B)s]=F_{n+1}s\otimes|0\rangle
\qquad(s\in S_{n+1}\subseteq S_n\otimes B).
\tag{42.14}
$$
初始接收态为 $F_0(1)$。在定义42.1的实际无干预来源族上，依次接收每个发出 qubit 后，完整联合态为
$$
\widehat\Omega_n=(I_J\otimes F_n\otimes I_M)\Omega_n
                         (I_J\otimes F_n^*\otimes I_M).
\tag{42.15}
$$
每次消耗的 $B$ 在丢弃前已是与整个其余系统乘积的纯空白，包含与 $J$ 和活动 $M$ 的关系；不留下输入相关信息。

证明。对（42.4）的活动记忆施加同一个 $T$，逐坐标有
$$
v^{n+1}_{i,a}=\sum_{b=0}^1(m_b)_a\,v^n_{i,b}\otimes|b\rangle.
\tag{42.16}
$$
所以 $S_{n+1}\subseteq S_n\otimes B$，且两侧指定映射在该子空间上都等距，有限等距延拓可给（42.14）。为明确给出不需构造 $2^n$ 阶矩阵的门，令
$$
w^n_{i,a}=\sqrt{G_n}\,e_{i,a}\in\mathbb C^4,\qquad
F_nv^n_{i,a}=w^n_{i,a}.
\tag{42.17}
$$
对任意四列系数 $z$，原像与目标的范数平方同为 $z^*G_nz$，故两列映射有相同核，指定映射良定并保持所有内积，包括相关列和零列。再在正交补上置零，即得所需 $F_n$。

构造 $K\otimes B$ 中四个输入、输出列：
$$
x_{i,a}=\sum_b(m_b)_a\,w^n_{i,b}\otimes|b\rangle,
\qquad y_{i,a}=w^{n+1}_{i,a}\otimes|0\rangle.
\tag{42.18}
$$
它们都是 $8\times4$ 矩阵的列。正交输出基使
$$
\begin{aligned}
\langle x_{i,a},x_{j,c}\rangle
&=\sum_b\overline{(m_b)_a}(m_b)_c\,
      G_n[(i,b),(j,b)]\\
&=\sum_b\overline{(m_b)_a}(m_b)_c
      [E^n(|j\rangle\langle i|)]_{b,b}\\
&=[E^{n+1}(|j\rangle\langle i|)]_{c,a}
 =G_{n+1}[(i,a),(j,c)]
 =\langle y_{i,a},y_{j,c}\rangle.
\end{aligned}
\tag{42.19}
$$
记列矩阵为 $X_n,Y_n$，则 $X_n^*X_n=Y_n^*Y_n$。直接使用既有 [GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq](../../../D5/S3/Quantum/Algebra/GramUnitaryExtension.lean)，以其 $B=Y_n,A=X_n$，得到 $Y_n=U_nX_n$。该声明允许任意有限矩形复矩阵，无满秩假设；因此初期秩亏也被覆盖。[SequentialRegisterCircuit.exists_unitary_agree](../../../D5/S3/Quantum/Entanglement/SequentialRegisterCircuit.lean)及同文件的 `rectangular_unitary` 是相应等距／填充寄存器供应，不另立通用包装。实际门规格只需（42.10）的 $4\times4$ 正平方根和八维正交补完成；$n=0$ 使用（42.9）。

酉共轭后偏迹
$$
\mathcal A_n:\mathcal L(K\otimes B)\to\mathcal L(K),\qquad
\mathcal A_n(Y)=\operatorname{Tr}_B(U_nYU_n^*)
\tag{42.20}
$$
在整个输入空间上 CPTP。在 $J\otimes K\otimes B\otimes M$ 的因子次序中，（42.14）逐列作用于实际来源展开，给出的向量恰为（42.15）下一步的 $J,K,M$ 向量插入空白 $|0\rangle_B$；在密度层面就是张量积 $\widehat\Omega_{n+1}\otimes|0\rangle\langle0|_B$，按上述固定次序置换因子。混态及所有参考块由线性性给出。因此先保留再丢弃这个 $B$ 不损失任何联合关系。由 $F_0(1)$ 起归纳即得（42.15）。生成器作用于活动 $M$ 与新空白，接收器作用于 $K$ 与已经发出的 $B$；不交因子的张量线性作用可交换，即使态纠缠也成立。这是操作交换，不是概率独立。

这一归纳的域是实际像族 $\operatorname{Ad}_{T_n}(\theta)$。不能把仅有支撑 $J\otimes S_n\otimes M$ 当成任意下一步的来源闭合。例如 $|1\rangle_{B_1}\otimes|1\rangle_M\in S_1\otimes M$，但
$$
(I_B\otimes T)(|1\rangle\otimes|1\rangle)
=|11\rangle\otimes|0\rangle\notin S_2\otimes M.
\tag{42.21}
$$
静态支持态可逆性仍可成立，因果接续却需要实际联合像。

同一门序列不依赖未来终端 $N$：对 $n\le N$，后续 $T_{N-n}$ 是每个前缀切口另一侧的等距，保持前缀约化态与支撑；（42.16）和 $G_n$ 本身也未使用 $N$。这正是 Blume-Kohout、Croke、Zwolak 的相干逐步收卷机制在来源子空间 $T_N(\mathbb C^2)$ 上的应用，把 $J$ 和终端活动 $M$ 放在未处理／参考一侧。[^rroctx42_bcz] 所需的是每个前缀秩受控与相干访问，不是仅有最终小维数；该文的高纠缠前缀例子排除了后一推断。$\square$

**命题 42.4（真实可达的干预失效）。** 同一装置从合法纯源 $|0\rangle$ 开始，第一步为 $|0\rangle\otimes m_0$。翻转已发出位后继续原生成器，实际得到
$$
(I_B\otimes T)(X\otimes I_M)T|0\rangle
=\sqrt\alpha\,|10\rangle\otimes m_0
 +\alpha|11\rangle\otimes m_1,
\qquad X=|0\rangle\langle1|+|1\rangle\langle0|.
\tag{42.22}
$$
非法前缀 $11$ 的概率为 $\alpha^2$。因为 $S_1=H_1$，这个逻辑翻转可在编码像 $F_1S_1$ 上实施并延拓为 $K$ 上的酉，但其继续历史已不属于命题42.3的被动来源族。或者，对第一位作 $X$ 基测量并在概率 $1/2$ 的加分支条件化，此时第一位为 $|+\rangle$、记忆仍为 $m_0$，下一步 $11$ 的条件概率为 $\alpha^2/2$；不条件化的该分支质量为 $\alpha^2/4$。这些数值直接由 $Tm_0$ 的两个正交输出分支计算。

另在 $n=2$，对第一旧位翻转会把 $|01\rangle\in S_2$ 送到非法 $|11\rangle$。即使某个中间测量保持当时支撑，它也会改变原联合源态。命题36.6可把无反馈输出实验的完整分支移到一个固定终端计算，却不证明干预后的历史仍在此被动 $S_n$ 链内，也不供给真实早期访问期限或任意接收结果驱动停止。$\square$

### 42.4 全域通道延拓与原权限内的终端运输

**命题 42.5（支撑逆与完整终端接口）。** 保持 $F_n:H_n\to K$ 在补空间为零，定义
$$
P_n=F_n^*F_n\in\mathcal L(H_n),\qquad Q_n=F_nF_n^*\in\mathcal L(K).
\tag{42.23}
$$
它们分别投影到 $S_n$ 与 $F_nS_n$。任取密度 $\omega_n\in\mathcal D(K)$ 及支撑在 $S_n$ 的密度 $\xi_n$，令
$$
\begin{aligned}
\mathcal C_n(X)&=F_nXF_n^*+\operatorname{Tr}((I_{H_n}-P_n)X)\omega_n,
&&X\in\mathcal L(H_n),\\
\mathcal B_n(Y)&=F_n^*YF_n+\operatorname{Tr}((I_K-Q_n)Y)\xi_n,
&&Y\in\mathcal L(K).
\end{aligned}
\tag{42.24}
$$
两者在整个声明载体上 CPTP，且
$$
\mathcal B_n\mathcal C_n(X)=X\qquad(X=P_nXP_n).
\tag{42.25}
$$
这是全支撑算子恒等式，不限于密度或来源边缘；与任意有限参考恒等张量后仍成立，特别可保留 $J$ 和实际活动 $M$。

证明。对任一补投影 $R$，取其像的正交基 $(e_l)$，并把所准备密度写成 $\sum_jt_j|u_j\rangle\langle u_j|$。映射 $X\mapsto\operatorname{Tr}(RX)\sum_jt_j|u_j\rangle\langle u_j|$ 的 Kraus 算子为
$$
K_{jl}=\sqrt{t_j}|u_j\rangle\langle e_l|,\qquad
\sum_{j,l}K_{jl}^*K_{jl}=R.
\tag{42.26}
$$
对 $\mathcal C_n$ 加入主 Kraus $F_n$，平方和为 $P_n+(I-P_n)=I_{H_n}$；对 $\mathcal B_n$ 加入 $F_n^*$，平方和为 $Q_n+(I-Q_n)=I_K$。这同时证明全域 CP 与 TP，包括补支撑分支。若 $X=P_nXP_n$，第一补项为零，$F_nXF_n^*$ 支撑在 $Q_n$，第二补项也为零，复合恰为 $P_nXP_n=X$。参考版本按其矩阵单位展开即可，不增加独立性前提。命题42.3的顺序接收在实际来源族上与 $\mathcal C_n$ 一致；它在任意不受此合同约束的 $H_n$ 输入上的行为不必等于这个方便的静态补空间延拓。$\square$

**推论 42.6（合法解码类、仪器和 POVM 的运输）。** 任何原来合法的完整终端通道或仪器 $\Lambda$，可在 $\operatorname{id}_J\otimes\mathcal B_n\otimes\operatorname{id}_M$ 后使用同一个 $\Lambda$。在（42.3）的实际族上，每个仪器分支的次归一化联合态、概率、失败和保留记录完全相同。若 $\Lambda$ 原本只访问档案，就仍只访问档案；若原本可读 $J$ 或活动 $M$，也只保留原有权限。接收器本身未得到这些权限。

具体地，任意原档案解码器 $\mathcal D:\mathcal L(H_n)\to\mathcal L(O)$ 对应 $\widehat{\mathcal D}=\mathcal D\mathcal B_n$；反向，任意接收解码器 $\widehat{\mathcal D}:\mathcal L(K)\to\mathcal L(O)$ 对应 $\widehat{\mathcal D}\mathcal C_n$。由于
$$
\mathcal B_n\mathcal C_n\Gamma_n=\Gamma_n
\quad\hbox{在全部源算子上成立},
\tag{42.27}
$$
两个无限制 CPTP 解码类可实现的来源到 $O$ 通道集合相同。故对这些通道的任意相同范数目标，最优值相等。对 $n\ge1$、$O=M$，精确接入定理41.2：
$$
\begin{gathered}
c_n=\|\sqrt{\tau(a_n)}\sqrt{\tau(b_n)}\|_1,\qquad
c_n^2=1-\alpha^2
 [\sqrt{a_n(1-b_n)}-\sqrt{b_n(1-a_n)}]^2,\\
\inf_{\widehat{\mathcal D}\ {\rm CPTP}}
 \|\widehat{\mathcal D}\mathcal C_n\Gamma_n-\operatorname{id}_M\|_\diamond
=\inf_{\mathcal D\ {\rm CPTP}}
 \|\mathcal D\Gamma_n-\operatorname{id}_M\|_\diamond
=1-c_n.
\end{gathered}
\tag{42.28}
$$
这里是根保真度和完整 diamond 范数；半 diamond 最优误差仍是 $(1-c_n)/2$。达到值的通道为已有 $\mathcal D_n\mathcal B_n$，其中 $\mathcal D_n$ 正是（41.17）的受控极分解解码器，本节不重证其最优恢复定理。受限硬件类仅在实际允许这两方向的所需复合时继承集合等价；抽象 CPTP 存在性不保证硬件封闭性。

对原档案 POVM $(E_y)$，伴随运输为
$$
\widehat E_y=\mathcal B_n^*(E_y)
=F_nE_yF_n^*+\operatorname{Tr}(\xi_nE_y)(I_K-Q_n),
\qquad \sum_y\widehat E_y=I_K.
\tag{42.29}
$$
证明。联合逆（42.25）之后接同一仪器的每个 CP 分支，便得完整分支恒等；两方向复合给（42.27）及可实现集合等价。最后对（42.24）逐项作迹配对得到（42.29），正性逐项成立，归一化用 $\sum_yE_y=I_{H_n}$、$\operatorname{Tr}\xi_n=1$。仅用 $F_nE_yF_n^*$ 则总和为 $Q_n$，初期 $\dim S_n<4$ 时并非环境空间上的 POVM。必须运输完整仪器或整个联合 POVM，不能由此声称独立端口代数均被保留。$\square$

**命题 42.7（合法词空间不是源支撑）。** 在三位合法词空间中
$$
\psi=(|000\rangle-|010\rangle)/\sqrt2
\tag{42.30}
$$
与 $S_3$ 正交。因而任何由（42.24）的 $\mathcal B_3$ 输出的密度 $\zeta$ 都满足
$D(|\psi\rangle\langle\psi|,\zeta)=1$，特别包括 $\zeta=\mathcal B_3\mathcal C_3(|\psi\rangle\langle\psi|)$；这里 $D=\tfrac12\|\cdot\|_1$。

证明。$W_3=\{000,001,010,100,101\}$ 张成的合法词空间维数为五，而命题42.2给 $\dim S_3=4$。更具体地，
$$
\begin{aligned}
T_3|0\rangle
 &=\alpha|000\rangle m_0+\alpha\sqrt\alpha|001\rangle m_1
      +\alpha|010\rangle m_0,\\
T_3|1\rangle
 &=\sqrt\alpha|100\rangle m_0+\alpha|101\rangle m_1.
\end{aligned}
\tag{42.31}
$$
前一行的 $000,010$ 记忆列完全相同，后一行二者均为零，故 $\psi$ 正交于四列。$\mathcal B_3$ 的两项都支撑在 $S_3$，所以与 $|\psi\rangle$ 支撑正交；两密度之差在不交支撑上正负分块，迹范数为二。这里排除的是把任意合法编码态当作可接收的实际相干来源态。$\square$

### 42.5 Bell 联合见证的尖锐容量与端口代数

**命题 42.8（普遍联合任务的最小接收维数）。** 在定义42.1确实允许 Bell 准备的来源类中，经档案一侧 CPTP 编码与恢复而精确保留原来的 $J,H_n,M$ 联合态，所需有效寄存器维数至少是
$$
d_n=\dim S_n=1,2,3,4,4,\ldots.
\tag{42.32}
$$
在各固定时域取 $S_n$ 的等距编码可达到这个维数；命题42.3以单一 $K=\mathbb C^4$ 的序列实现所有时域，从 $n\ge3$ 起四维尖锐。

证明。实际准备 $|\Phi\rangle_{JM}=(|00\rangle+|11\rangle)/\sqrt2$，使用相同独立空白和同一 $T$。仅为写 Schmidt 分解，把档案放到左侧，演化纯向量为
$$
|\Psi_n\rangle=\frac1{\sqrt2}\sum_{i,a}v^n_{i,a}\otimes|i\rangle_J\otimes|a\rangle_M,
\qquad \operatorname{Tr}_{JM}|\Psi_n\rangle\langle\Psi_n|
=\Gamma_n(I_M/2)=\frac12\sum_{i,a}|v^n_{i,a}\rangle\langle v^n_{i,a}|.
\tag{42.33}
$$
正项之和的核是四列共同正交补，故其支撑恰为 $S_n$。因此 Schmidt 分解为
$|\Psi_n\rangle=\sum_{r=1}^{d_n}\sqrt{s_r}|e_r\rangle|f_r\rangle$，所有 $s_r>0$，$e_r$ 张成 $S_n$，$f_r$ 位于实际 $JM$。

设编码 $\mathcal C$ 与恢复 $\mathcal B$ 经过 $k$ 维寄存器，且
$(\mathcal L\otimes\operatorname{id}_{JM})(|\Psi_n\rangle\langle\Psi_n|)=|\Psi_n\rangle\langle\Psi_n|$，$\mathcal L=\mathcal B\mathcal C$。用 $\langle f_r|$、$|f_s\rangle$ 夹取参考／记忆块得
$$
\sqrt{s_rs_s}\,\mathcal L(|e_r\rangle\langle e_s|)
=\sqrt{s_rs_s}\,|e_r\rangle\langle e_s|.
\tag{42.34}
$$
非零系数强迫 $\mathcal L$ 固定每个支撑矩阵单位，不仅是一个对角混合态。于是 $r\ne s$ 时，迹距离收缩给
$$
1=D(|e_r\rangle\langle e_r|,|e_s\rangle\langle e_s|)
\le D(\mathcal C(|e_r\rangle\langle e_r|),
       \mathcal C(|e_s\rangle\langle e_s|))\le1.
\tag{42.35}
$$
距离一的密度具有正交支撑：达到距离的二元 Helstrom 效应对一态概率一、对另一态概率零，正性使其分别位于该效应的本征值一、零子空间。故编码密度的 $d_n$ 个非零支撑两两正交，$k\ge d_n$。等价地可用 Q定理7.5的零错误容量结论。这些基态测试是单个合法 Bell 联合约束的代数后果，不需要另假设每个 $e_r$ 都是可单独准备的源态。任何额外携带输入相关信息的接收系统，也须计入编码资源，不能藏在 $K$ 之外。$\square$

这个下界只属于所声明的普遍联合任务。仅恢复来源 qubit、固定已知纯根、复现输出边缘或准备一个已知混态，都不是它的替代假设。Q125.1及恢复卷31.3已给固定 $P_0^{\rm mem}$ 根的档案在 $n\ge1$ 恰为秩二，下文也由记忆行列式核对；它不能见证此处普遍任务的四维必要性。

**命题 42.9（压缩不保留两个独立尖锐端口）。** 在 $n=2$ 写
$$
P=P_2=|00\rangle\langle00|+|01\rangle\langle01|+|10\rangle\langle10|,
\qquad A=P(X\otimes I)P,\qquad B'=P(I\otimes X)P.
\tag{42.36}
$$
虽然未压缩的两个 Pauli 算子对易，但
$$
[A,B']|01\rangle=|10\rangle.
\tag{42.37}
$$
证明。$B'|01\rangle=|00\rangle$，$A|00\rangle=|10\rangle$，而 $A|01\rangle=0$，所以按 $[A,B']=AB'-B'A$ 得所列等式。$F_2$ 在 $S_2$ 等距，故 $F_2AF_2^*$、$F_2B'F_2^*$ 的交换子在 $F_2|01\rangle$ 上仍非零。这是压缩不保持乘法的具体实例，接续 Q125.2的压缩反例和 Q定理7.5的独立片段访问边界。

仍可把原来两个 Pauli 的整个联合 POVM
$$
E_{st}=\tfrac14(I+sX)\otimes(I+tX),\qquad s,t\in\{-1,1\},
\tag{42.38}
$$
按（42.29）运输成 $K$ 上正且总和为 $I_K$ 的联合 POVM。其边缘一般为非尖锐效应，在 $Q_2$ 子空间上的一阶矩就是上面的非对易压缩算子。非对易的非尖锐边缘不意味着不联合可测；这里已有明确联合 POVM。若需恢复原来的有限张量端口，可实施 $\mathcal B_2$，但输出空间、空白、路由和门须另计。这不提供同时独立端口或无损连续解码副本。$\square$

### 42.6 实际纯根的词律与两个有限熵

**命题 42.10（同一个固定根的完整词熵）。** 现在只用定义42.1的纯根合同。记 $\Xi_n=T_nm_0$、$\rho_n=\Gamma_n(P_0^{\rm mem})$，$W_n$ 为无相邻 $11$ 的长度 $n$ 二元词，$\ell(w)$ 为非空词末位。则对 $n\ge1$，
$$
\Xi_n=\sum_{w\in W_n}\alpha^{(n+\ell(w))/2}|w\rangle\otimes m_{\ell(w)},
\qquad p_n(w)=\Pr(Y_1\cdots Y_n=w)
=\begin{cases}\alpha^{n+\ell(w)},&w\in W_n,\\0,&w\notin W_n.\end{cases}
\tag{42.39}
$$
$Y$ 是整份实际计算基记录。以 $q_0=0$ 作为初始根权重、$q_n=\Pr(Y_n=1)$（$n\ge1$），有
$$
q_{n+1}=\alpha^2(1-q_n),\qquad q_n=\pi_1(1-\lambda^n),\qquad
H(Y_1,\ldots,Y_n)=(n+q_n)\log\phi.
\tag{42.40}
$$
$n=0$ 只有一个空词，熵为零；不为空词另造一个末位随机变量。

证明。Q130.1的两个源恒等式为
$Tm_0=\sqrt\alpha|0\rangle m_0+\alpha|1\rangle m_1$、$Tm_1=|0\rangle m_0$。第一步给系数 $\sqrt\alpha,\alpha$。若末位为零，原系数 $\alpha^{n/2}$ 分别乘 $\sqrt\alpha,\alpha$，恰为下一步末位零、一所需的 $\alpha^{(n+1)/2},\alpha^{(n+2)/2}$；若末位为一，原系数 $\alpha^{(n+1)/2}$ 只延长零，仍是所需系数。每个合法延长出现一次，附一到一之后的振幅为零。归纳给（42.39），记忆向量单位范数给实际 Born 概率。这保留 Q125.3和Q130.1对固定左根律的所有权。

因此转移矩阵为
$$
P_{\rm word}=\begin{pmatrix}\alpha&\alpha^2\\1&0\end{pmatrix},
\qquad \Pr(Y_1=0,1)=(\alpha,\alpha^2).
\tag{42.41}
$$
它是虚拟左邻位固定为零后的根律，不是初始分布 $(\pi_0,\pi_1)$ 的平稳 Parry 律。由第二列读出 $q_{n+1}=\alpha^2(1-q_n)$，解出（42.40）；例如 $q_1=\alpha^2$、$q_2=\alpha^3\ne q_1$。对每个合法词，$-\log p_n(w)=(n+\ell(w))\log\phi$，取期望就得词熵。无反馈的旧输出计算基获取可依命题36.6移到终端计算，保留相同完整记录律与分支权重；这不删除真实已获记录，也不让早期可用结果凭空出现。$\square$

**命题 42.11（相干档案与活动记忆的共同谱）。** 同一纯 $\Xi_n$ 的记忆边缘为
$$
\sigma_n=E^n(P_0^{\rm mem})=\tau(q_n),\qquad
\nu_\pm(u)=\frac{1\pm\sqrt{1-4\alpha^2u(1-u)}}2,
\tag{42.42}
$$
且
$$
S(\rho_n)=S(\sigma_n)=h_2(\nu_-(q_n))\le\log2,
\qquad h_2(t)=-t\log t-(1-t)\log(1-t).
\tag{42.43}
$$
端点采用 $0\log0=0$。$n\ge1$ 时 $\rho_n$ 恰为秩二，$n=0$ 时 $\rho_0=(1)$、$\sigma_0=P_0^{\rm mem}$ 均纯。

证明。根权重从零开始，与（42.11）同一递推给记忆公式；迹一和行列式 $\alpha^2u(1-u)$ 给二次特征根（42.42）。有限纯二分态的互补边缘共享全部非零谱，故用既有 [InputInformationBalance.pure_complementary_entropy](../../../D5/S3/Quantum/Information/InputInformationBalance.lean) 的机制得到熵等式，二元谱熵至多 $\log2$。对 $n\ge1$，$q_n\in(0,1)$，行列式正，两个特征值都正，因而两边非零谱恰有两项。这里评价的是 Q125.1的实际根密度，而非把它换成 $\Gamma_n(|0\rangle\langle0|)$ 或 $\Gamma_n(\tau(\pi_1))$。$\square$

### 42.7 相干差、保留活动记忆的条件熵与显式余项

**命题 42.12（实际 cq 记录的条件熵）。** 在每个固定 $H_n$ 上令 $\Delta_n$ 为计算基完全去相位，定义与通道 $\mathcal C_n$ 不同的标量
$$
\chi_n=D_{\rm rel}(\rho_n\|\Delta_n\rho_n)
=H(Y)-S(\tau(q_n))\ge0.
\tag{42.44}
$$
$D_{\rm rel}$ 是量子相对熵，不是半迹距离。实际测量后保留活动记忆的状态为
$$
\xi_{YM}=\sum_{w\in W_n}p_n(w)|w\rangle\langle w|\otimes P_{\ell(w)}^{\rm mem},
\qquad \xi_M=\tau(q_n),
\tag{42.45}
$$
其中 $n=0$ 单独取空记录与 $P_0^{\rm mem}$。于是
$$
S(\xi_{YM})=H(Y),\qquad H(Y\mid M)_\xi=\chi_n,\qquad
I(Y:M)_\xi=S(\tau(q_n))\le\log2.
\tag{42.46}
$$

证明。$\Delta_n\rho_n=\sum_wp_n(w)|w\rangle\langle w|$，且每个合法词的 $p_n(w)>0$。$\rho_n$ 支撑在合法词张成空间，后者恰是 $\Delta_n\rho_n$ 的支撑，所以相对熵的支撑包含条件成立。在该支撑上对角对数给
$$
\operatorname{Tr}(\rho_n\log(\Delta_n\rho_n))
=\sum_wp_n(w)\log p_n(w).
\tag{42.47}
$$
代入相对熵定义和（42.43）即得（42.44）；非负性是有限维相对熵非负性／pinching 恒等式的既有结论。对应 Q89.1—89.4及 [EntropyProductionCoherenceDeletionIdentity.entropy_production_coherence_deletion_identity](../../../D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.lean) 时，固定一个 $H_n$，在该载体取酉 $I$、从 $\rho_n$ 到 $\Delta_n\rho_n$ 的一步，随后保持去相位态即可；不把不同 $n$ 的增长载体当成其一个固定载体上的时间迭代。相对熵相干量的标准表达也见 Baumgratz–Cramer–Plenio 的式（8）。[^rroctx42_coherence]

对（42.39）作实际计算基测量，词 $w$ 的条件记忆正是纯态 $P_{\ell(w)}^{\rm mem}$，故得（42.45）。不同词的经典块彼此正交，各块只有一个非零本征值 $p_n(w)$，所以联合熵为 $H(Y)$；偏迹后的记忆为 $(1-q_n)P_0^{\rm mem}+q_nP_1^{\rm mem}$。按条件熵及互信息定义相减即得（42.46）。这里真正保留了活动 $M$，没有替换它；$\langle m_0,m_1\rangle=\sqrt\alpha>0$，两个记忆标签不能作为完美可读的末位旗标。$\square$

**命题 42.13（熵率与全 $n$ 有限量的定量尾）。** 有
$$
n\log\phi-\log2\le\chi_n\le(n+1)\log\phi,
\qquad
\lim_{n\to\infty}\frac{H(Y_1,\ldots,Y_n)}n
=\lim_{n\to\infty}\frac{H(Y_1,\ldots,Y_n\mid M)}n=\log\phi.
\tag{42.48}
$$
更精确地，置 $s(u)=h_2(\nu_-(u))$、$s_*=s(\pi_1)$ 和
$$
I_\alpha=[\alpha^3,\alpha^2]\subset(0,1),\qquad
L=\max_{u\in I_\alpha}|s'(u)|<\infty.
\tag{42.49}
$$
对每个 $n\ge1$，
$$
\left|\chi_n-[n\log\phi+\pi_1\log\phi-s_*]\right|
\le\pi_1(\log\phi+L)\alpha^{2n}.
\tag{42.50}
$$
所以余项为 $O(\alpha^{2n})$，但这里只对有限时域的数列作渐近陈述，不给一个假定无限密度矩阵赋熵。

证明。用 $0\le q_n\le1$、$0\le s(q_n)\le\log2$ 与（42.40）、（42.44）立即得界和速率。$q_1=\alpha^2$、$q_2=\alpha^3$；递推把区间 $I_\alpha$ 映到自身，因为下端像为 $\alpha^2(1-\alpha^3)\le\alpha^2$，上端像为 $\alpha^2(1-\alpha^2)=\alpha^3$。$\pi_1$ 也在此区间：$\pi_1<\alpha^2$，而 $\pi_1>\alpha^3$ 等价于 $\alpha+\alpha^3<1$，由 $\alpha^3<\alpha^2$ 得到。于是所有 $n\ge1$ 都可使用同一个紧内部区间。

在此区间 $\alpha^2u(1-u)>0$，且 $1-4\alpha^2u(1-u)\ge1-\alpha^2=\alpha>0$，故 $\nu_-(u)\in(0,1/2)$，$s$ 为 $C^1$，其导数最大值有限。由
$$
q_n-\pi_1=-\pi_1\lambda^n,\qquad
\chi_n-[n\log\phi+\pi_1\log\phi-s_*]
=(q_n-\pi_1)\log\phi-[s(q_n)-s(\pi_1)]
\tag{42.51}
$$
和中值定理得（42.50）。若需不用极值符号的保守常数，写
$r(u)=\sqrt{1-4\alpha^2u(1-u)}$，则
$\nu_-'(u)=\alpha^2(1-2u)/r(u)$；在 $I_\alpha$ 上有
$|\nu_-'|\le\alpha^{3/2}$、$\nu_-\ge\alpha^2u(1-u)\ge\alpha^6$，所以
$|s'|=|\nu_-'\log((1-\nu_-)/\nu_-)|\le6\alpha^{3/2}\log\phi$。
$n=0$ 时 $\chi_0=0$，不把它强塞入（42.49）的区间。$\square$

在同一纯根准备下，旧有限 $J$ 与新生成 $YM$ 因初始分解和局部作用而保持乘积，故 $H(Y\mid JM)=H(Y\mid M)=\chi_n$。较大旧经典档案须具有定义36.4所述标准 Borel 值空间、实际可测正则条件密度核及逐纤维相同准备；相同公式才可在该核上逐纤维使用。这不是关于任意无限量子参考的紧性结论。更不能把（42.48）称为相对于整个最终观察者的正条件熵：那个观察者一旦已含实际取得的 $Y$，就有 $H(Y\mid Y,\text{其它记录})=0$。旧精确副本 $Y$ 作为解码侧信息，也会把合同改成 $H(Y\mid M,Y)=0$。

### 42.8 测量扩张、原样本身份与已获记录容量

**命题 42.14（相干复制不产生全局熵）。** 在固定时域把空白记录 $A$ 相干写入为
$|w\rangle_H|0\rangle_A\mapsto|w\rangle_H|w\rangle_A$。纯根的完整态变成
$$
|\Upsilon_n\rangle_{HAM}
=\sum_{w\in W_n}\sqrt{p_n(w)}\,|w\rangle_H|w\rangle_A m_{\ell(w)},
\qquad S(HAM)=0.
\tag{42.52}
$$
$n=0$ 使用空词和 $m_0$。对 $H$ 偏迹得到（42.45）的 $AM$ 版本，故 $S(A)=H(Y)$。若在复制之前已对 $M$ 偏迹，则复制后的 $HA$ 联合态熵为 $S(\rho_n)$，并非必为零。

证明。不同 $w$ 的复制基像正交，故复制是等距并保持纯向量范数；可用有限空白酉延拓实现。偏迹 $H$ 消去不同词交叉项，留下所写纯条件记忆的 cq 块。若输入为混合 $\rho_n$，等距保持其非零谱，故联合熵为 $S(\rho_n)$。这是 Q89及 [CoherentCopyCorrelationTax.vonNeumannEntropy_coherentCopyState](../../../D5/S3/Quantum/Information/CoherentCopyCorrelationTax.lean) 的直接应用；同文件 `coherent_copy_correlation_tax` 还把复制系统的互信息分解为记录熵加相干差，未将它认作热力学成本。这里 $\chi_n$ 量化约化访问所失去的相干，不是总熵的产生。$\square$

**命题 42.15（保留同一次已获词的零错误容量）。** 若 $Y$ 已实际取得，要求没有可访问解码侧信息的存储器日后精确读出同一个来源索引词，则其量子存储维数至少为
$$
N_n=|W_n|=F_{n+2},\qquad F_0=0,\quad F_1=1;
\tag{42.53}
$$
固定长度经典存储至少为 $\lceil\log_2F_{n+2}\rceil$ 位。

证明。每个合法词在（42.39）下都有正概率。若编码词 $w$ 为密度 $\zeta_w$，精确读出的 POVM $(M_w)$ 必须对每个词有 $\operatorname{Tr}(M_w\zeta_w)=1$ 且对其它标签概率零；即使只先要求实际平均零错误，所有正权重也强迫逐标签零错误。正性使不同标签密度落在读出效应的正交确定性子空间中，所以这些密度有互相正交的非零支撑；Q定理7.5的 $\beta=0$ 容量也直接给维数至少 $N_n$。计数的初值是 $N_0=1,N_1=2$；$n\ge2$ 时，以零结尾的词有 $N_{n-1}$ 个，以一结尾的词前一位须为零，有 $N_{n-2}$ 个，故 $N_n=N_{n-1}+N_{n-2}=F_{n+2}$。经典 $b$ 位至多有 $2^b$ 个状态，给上取整位数下界。该结论是零错误支撑／基数结论，不等于 Shannon 熵，不覆盖侧信息辅助或可变长编码。$\square$

实际不可逆计算基测量后的档案为 $\Delta_n\rho_n$，对所有 $W_n$ 具有正对角支撑。其支撑是整个合法词空间：$n\ge3$ 时已超过四维，尤其 $n=3$ 的维数是五，而不是 $S_3$。若把原结果保留为不可访问参考，要求档案一侧恢复与它的对角复制关联，夹取每个正概率参考标签就强迫逐词恢复；四维相干接收定理不涵盖此已测档案任务。

相干资源失去也有一位例子。令 $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$，则
$$
\Gamma_1(|\pm\rangle\langle\pm|)
=\tfrac12\begin{pmatrix}1&\pm\sqrt\alpha\\\pm\sqrt\alpha&1\end{pmatrix}.
\tag{42.54}
$$
两态计算对角完全相同，相干相位不同；只拿到不可逆去相位后的档案不能同时恢复它们。取得测量环境的相干访问会改变操作合同，不能从原来的经典记录推断。

四维 $K$ 允许具有多于四个结果的 POVM；执行它新产生的实际结果寄存器是额外资源，不能据此断言这些标签此前已作为可区分态储存在 $K$。另抽一份同边缘的独立 $Y'$ 也不保存原样本。令保留参考中的原词为 $R$，正确复制的联合律为 $p_n(w)\mathbf1_{v=w}$，独立重抽则为 $p_n(w)p_n(v)$，直接分开对角与非对角项得
$$
\operatorname{TV}(\text{原词的对角复制},\text{独立乘积})
=\tfrac12\left[\sum_wp_n(w)(1-p_n(w))+
                 \sum_{w\ne v}p_n(w)p_n(v)\right]
=1-\sum_wp_n(w)^2>0\quad(n\ge1).
\tag{42.55}
$$
严格性因至少两个合法词具有正概率。由此必须保留实际样本身份及其原关系；仅同边缘律不够。这里没有单次擦除成本、热、功或物理熵产生等式，这些量需要额外能量、温度、环境与允许操作合同。

### 42.9 共同关系接口的资源、供应与边界

**约定 42.16（分开计量的实现资源）。** 四维只计两次发射之间的持续接收 $K$；每步交互为八维 $K\otimes B$。活动生成记忆 $M$、外部参考 $J$、既有经典档案、控制器／计数器、时序安排、校准的 $n$ 依赖门描述、门综合与精度、路由、终端结果寄存器及重新展开的输出端口／空白分别计量。通常计数到 $n$ 的经典计数器需要增长的存储；外部预排时序也有实际描述和时钟成本。本证明给每一步理想有限矩阵，未给有界总经典控制内存、常数总观察者容量或常数运行时间。

终端 $\mathcal B_n$ 可以需要 $n$ 个输出空白、$O(n)$ 个输出端口以及实际展开门。只有在相应硬件允许时，可直接实现运输后的 POVM 来避免显式物化所有端口；许多可能结果仍需要实际保留结果的空间。源 qubit 的生成容量二、普遍接收容量四以及已获词容量 $F_{n+2}$ 是三个不同资源任务，不相互抵消。

完整观察者始终按定义36.4保留一切已获设备／来源／版本身份、内外记录及关系、相位与校准约定、局部钟读数和已知钟关系、时间顺序、动作守卫、结果与失败。本节只换相干发射子系统的表示，未删除这些背景和联合约束。第39节所要求的共同实际来源在（42.3）中表现为同一个 $\theta$ 产生全部前缀；第40节的相对钟必须由实际历史和其饱和合同取得，本节的发射数不能替代它。离散前缀、完成态和体／边表示的联系仍受第36、39节及 Q125的分离、共同实现、拓扑与获取条件约束；逐个有限终端能恢复不等于已经取得一个无限终端解码器。

对任意有限量子 $J$，支撑逆恒等式统一成立。若旧经典档案 $C$ 无界，一个明确扩展是：$C$ 取标准 Borel 值，保留其实际概率 $\mu$ 和可测正则条件密度核 $c\mapsto\theta_{JM\mid c}$，每个纤维采用相同装置，或有明确可测的校准坐标识别；独立空白和生成合同逐纤维成立。于是（42.25）在实际 cq 核上逐纤维成立，保留 $C$ 再积分即可。外生有限时域标签也须如此保留，不能在后选择后丢失选择律。这里不声称任意无限量子参考、某个固定表示中的无限密度矩阵、normal 性或共同无限解码器。

精确代数构造不是任意有限门字母表的精确综合、实验室可行性、泄漏／门噪声鲁棒性或真实早期截止的证明。在线干预、接收结果反馈和改变停止规则要重新证明可达来源族；静态逆不能替代该义务。空间、边界、记忆和发射顺序在这里通过同一有限关系接口连接，不由名称推出物理波、时空密度、全波本体或普遍时空定律。

**约定 42.17（供应的准确归属）。** Q定理3.1提供保留范数的 Gram 因子化方法，本节不用其单位对角条件冒充任意列；`GramUnitaryExtension` 的矩形等 Gram 声明直接供应（42.19）的八维酉，`SequentialRegisterCircuit` 供应有限等距延拓与空白寄存器实现。Q定理7.5供应完美区分容量及独立片段访问警示；Q定理13.3供应受控极分解和联合预测约束，本卷定理41.2已专门构造固定档案解码器，本节仅复合（42.24）。Q89及上述互补熵、相干复制、pinching 的 Lean 声明分别供应熵机制，它们的有限载体和纯度条件保持原样，本节普通计算不等于编译了这些特殊化。

Q命题125.1—125.4拥有固定根相干密度、秩二、相容局部态、固定左根非平稳词律和指定无限表示限制；Q130.1、131.1拥有确切的 $T$、独立空白酉、纯联合展开、持续记忆关联和 $E$ 的根混合递推。恢复卷定义31.1、定理31.2、命题31.3拥有全 $k$ 的对应结构；在 $k=2$，其（31.8）仅交换记忆基，输出次序不交换。该卷第31.2节的最小生成容量与本节接收容量不同。Context定义36.4、命题36.5—36.6拥有完整档案、真实条件准备、追加记录和固定生成的参考安全终端推迟；推迟不授予提前行动能力。Q98、Q104及 [CoherentHistorySchmidt](../../../D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.lean) 的占据多重集切口秩结论保留其占据扇区假设，不能直接代替本装置的四列 Gram 或 Bell 联合容量论证。

外部相干收卷方法归 Blume-Kohout–Croke–Zwolak，尤其其保留参考关联和将消耗位清空的 Section II。Schön等人的有限开边界 MPS／顺序等距方法提供相邻背景；其纯发射态刻画要求最终辅助系统解耦，本节档案通常混合且活动 $M$ 仍相关，不能由生成 bond 维数二推出接收维数二。[^rroctx42_schon] Koashi–Imoto 的固定态族分解区分经典、量子与冗余部分；保留族边缘而丢弃冗余混合因子不自动保留真实纯化，其 VIII.E 的 iid 渐近压缩也不是这里相关顺序来源的精确容量依据。[^rroctx42_ki]

[^rroctx42_bcz]: Robin Blume-Kohout, Sarah Croke and Michael Zwolak, *Ideal state discrimination with an O(1)-qubit quantum computer*, [arXiv:1201.6625v1](https://arxiv.org/pdf/1201.6625v1), Section II：以参考纯化已知矩阵乘积子空间，把每个前缀 Schmidt 支撑相干转移到接收器并留下空白位；前缀纠缠和相干访问条件不能只以最终子空间小来替代。

[^rroctx42_schon]: C. Schön, E. Solano, F. Verstraete, J. I. Cirac and M. M. Wolf, *Sequential generation of entangled multi-qubit states*, [arXiv:quant-ph/0501096v1](https://arxiv.org/pdf/quant-ph/0501096v1), *Physical Review Letters* **95**, 110503 (2005)：有限顺序等距与 MPS、受控辅助维数；纯输出态刻画的最终辅助解耦条件须单独保留。

[^rroctx42_ki]: Masato Koashi and Nobuyuki Imoto, *What is Possible Without Disturbing Partially Known Quantum States?*, [arXiv:quant-ph/0101144v2](https://arxiv.org/pdf/quant-ph/0101144v2)：固定态族的不扰动结构及经典／量子／冗余区分；VIII.E 讨论渐近忠实独立来源压缩，不供应本节的精确实际纯化保持任务。

[^rroctx42_coherence]: T. Baumgratz, M. Cramer and M. B. Plenio, *Quantifying Coherence*, [arXiv:1311.0275](https://arxiv.org/abs/1311.0275), equation (8)：相对熵相干量为 $S(\Delta\rho)-S(\rho)$。本节同时沿用 Q89的访问边界，不将该差值解释为未经建模的热或功。

## 42.99 追加锚

## 43. 递归有理数组的体、边界与形式完成：有限任务及来源起点的相容恢复

本节把离散层与完成对象的体／边关系落实在一个明确的递归族上：边界为一列有理数，体为满足后继关系的三角数组，完成表示为常数项一的形式幂级数。三者的恢复须同时保留限制映射、首差尺度和已经取得的全部观察者记录。顶行全一的自然数组另有既有形式结果；这里的变动有理族不预设顶行、正性、概率或物理时间。

### 43.1 既有自然源的归属与本节的有理域

本节的形式供应固定在 `1fae30cf331dd943f49e44f88c9ee0feb3829770`。[AntidiagonalArraySourceSeries 的 `result`](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.lean#L78) 给出自然数组的存在唯一性、归一化有理源级数的存在唯一性、其自然系数序列的存在唯一性，以及包括 $n=0$ 在内的首列恒等式 $T(n,0)=[X^{n+1}]F$。其 `IsArray` 除后继关系外还要求整条第零行等于一；`IsSource` 要求 $F(0)=1$ 及 $F(X/F(X))=(1-X)^{-1}$。`sourceCoeff` 先从源方程独立构造系数，再由证明接上数组；不能把任意有理边界都称为该唯一源。

该证明中的局部 `hrow`（第117行）建立行级数关系，`hrowrec`、`htel`、`hbridge`（第222、228、241行）给出从第零行展开及逐系数余项消失的机制；这些是证明内部事实，不是可另行调用的公开定理名。第275—293行用源方程与唯一性识别 $1+X$ 乘首列级数。另一个供应 [QuotientThetaCompositionModFour 的 `quotient_triangular`](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.lean#L72) 要求两级数常数项均为一、在次数 $d$ 以下相同，并断言在次数不超过 $d$ 时，商代入后的系数差等于原系数差；它直接用于上述源构造与唯一性，但自身不识别这个数组。

自然对象及方程的来源分别归 Mikhail Kurkov 的 A392095 与 Paul D. Hanna 的 A088713。[^rroctx43_oeis] 本节的任意有理边界、有限多项式逆、离散前缀完成及具体任务应用属于仓内推导（`repo-derived`）；固定核的 Riordan 系数方法属于成熟方法（`literature-attested`），归属见第43.8节。这里不作原创优先权或新的形式化声明。

### 43.2 有限约束体与无除法的边界恢复

**定义 43.1（有限有理体与首列边界）。** 对整数 $M\ge0$ 令 $\Delta_M=\{(n,k)\in\mathbb N^2:n+k\le M\}$。令 $\mathcal A_M$ 为所有 $T:\Delta_M\to\mathbb Q$ 中恰满足以下后继关系的数组：
$$
T(n+1,k)=T(n,k+1)+\sum_{j=0}^{k}T(n,j)T(k-j,0)
\qquad(n+k<M).
\tag{43.1}
$$
这里不加第零行条件，也不加正性条件。$M=0$ 没有方程；严格不等式使每个出现的坐标均在 $\Delta_M$，不使用负上界或自然数截断减法来描述方程域。定义
$$
\beta_M:\mathcal A_M\longrightarrow\mathbb Q^{M+1},\qquad
\beta_M(T)=(T(0,0),T(1,0),\ldots,T(M,0)).
\tag{43.2}
$$

**定理 43.2（有限多项式互逆）。** 每个 $a=(a_0,\ldots,a_M)\in\mathbb Q^{M+1}$ 恰有一个扩张 $\mathcal E_M(a)\in\mathcal A_M$，且 $\mathcal E_M$ 的每个坐标都是 $a$ 的整系数多项式。边界提取与扩张是互逆的有理多项式映射，无任何边界非零假设。

证明。先放置第零列 $T(n,0)=a_n$。已构造第零至第 $k$ 列时，对 $n+k+1\le M$ 置
$$
\boxed{T(n,k+1)=T(n+1,k)-\sum_{j=0}^{k}T(n,j)a_{k-j}.}
\tag{43.3}
$$
右侧全部坐标都在此前已构造的列中，包括 $T(n+1,k)$；所用边界下标也未越界。故这是有限的加、减、乘构造，没有除法。重新移项即得（43.1），首列按定义等于 $a$。反过来，任何具有该首列且满足（43.1）的数组都必须服从（43.3）；列归纳遂给逐坐标唯一性。同一列归纳表明每个输出坐标都是整系数多项式。$\beta_M$ 为坐标投影，因此两映射均为多项式，且
$$
\beta_M\mathcal E_M=\mathrm{id}_{\mathbb Q^{M+1}},\qquad
\mathcal E_M\beta_M=\mathrm{id}_{\mathcal A_M}.
\tag{43.4}
$$
第一式由指定首列得，第二式由唯一性得。$\square$

$\Delta_M$ 虽显示 $(M+1)(M+2)/2$ 个坐标，却恰有 $M+1$ 个自由有理参数。后继方程共 $M(M+1)/2$ 条，在列次序中每条解出一个非边界坐标；自由度结论来自已构造的多项式逆，不能仅凭方程数相减。一个有理参数的精度可以任意大，故该计数不是位数或 Shannon 信息量。

### 43.3 一个形式级数对任意行的精确恢复

**定义 43.3（归一化形式表示）。** 给任意 $a=(a_i)_{i\ge0}\in\mathbb Q^{\mathbb N}$，在 $\mathbb Q[[X]]$ 中令
$$
F(X)=1+X\sum_{i\ge0}a_iX^i,\qquad
Y=XF^{-1},\qquad C_n(X)=\sum_{j\ge0}a_{n+j}X^j.
\tag{43.5}
$$
条件 $F(0)=1$ 指常数系数，使 $F$ 为形式乘法单位；$Y(0)=0$ 保证无限外级数的形式代入逐系数良定。记 $\mathcal A_\infty$ 为所有在 $\mathbb N^2$ 上、对每个 $n,k\ge0$ 满足（43.1）所示后继等式的有理数组，不加顶行条件。

**定理 43.4（任意起始行的有限展开与系数公式）。** 对每个上述 $a$，其唯一无限扩张 $T\in\mathcal A_\infty$ 的行级数 $R_n(X)=\sum_{k\ge0}T(n,k)X^k$ 为
$$
\boxed{R_n(X)=F(X)^{-1}C_n\!\left(X/F(X)\right).}
\tag{43.6}
$$
等价地，每个 $n,k\ge0$ 有有限和
$$
\boxed{T(n,k)=\sum_{j=0}^{k}a_{n+j}[X^{k-j}]F(X)^{-(j+1)}.}
\tag{43.7}
$$
任意给定的递归数组也满足同一公式，其推导不需要解析极限。

证明。先用（43.6）定义行。由 $C_n(Y)=a_n+YC_{n+1}(Y)$ 及 $Y=XF^{-1}$ 得
$$
FR_n=a_n+XR_{n+1},\qquad R_n(0)=a_n.
\tag{43.8}
$$
用（43.5）展开左侧并取 $X^{k+1}$ 系数，得到 $T(n,k+1)+\sum_{j=0}^kT(n,j)a_{k-j}=T(n+1,k)$，正是（43.1）。每个有限三角上的定理43.2给全数组唯一性。再把（43.6）写成 $\sum_{j\ge0}a_{n+j}X^jF^{-(j+1)}$；$j>k$ 时第 $k$ 次系数为零，得到（43.7）。

也可从任意已给递归数组出发。其每一行的乘法系数正好给（43.8），故 $R_n=F^{-1}a_n+YR_{n+1}$。对任意 $N\ge0$，有限迭代给
$$
R_n=F^{-1}\sum_{j=0}^{N-1}a_{n+j}Y^j+Y^NR_{n+N}.
\tag{43.9}
$$
$N=0$ 的和为空，等式是 $R_n=R_n$。若等式对 $N$ 成立，在其末行代入一步关系，添上 $F^{-1}a_{n+N}Y^N$，余项成为 $Y^{N+1}R_{n+N+1}$，即得下一步。因此（43.9）对所有 $n,N$ 成立。余项为 $X^NF^{-N}R_{n+N}$，明确被 $X^N$ 整除；固定系数次数 $k$ 后取 $N=k+1$，余项该系数严格等于零，再次得到（43.7）及（43.6）。这是任意起始行的有限系数证明；第43.1节形式供应在第零行使用了这一机制。没有把 $X$ 赋实数或复数值。$\square$

**引理 43.5（有限依赖与反对角首项）。** $T(n,k)$ 仅依赖 $a_0,\ldots,a_{n+k}$，且有整系数多项式 $P_{n,k}$ 使
$$
T(n,k)=a_{n+k}+P_{n,k}(a_0,\ldots,a_{n+k-1}),\qquad
P_{n,0}=0,
\tag{43.10}
$$
其中 $P_{0,0}=0$ 是无变量零多项式。因而 $F\bmod X^{M+2}$ 足以恢复整个 $\Delta_M$。

证明。写 $F=\sum_{i\ge0}f_iX^i$、$F^{-1}=\sum_{d\ge0}b_dX^d$，则
$$
f_0=b_0=1,\qquad b_d=-\sum_{i=1}^{d}f_i b_{d-i}\quad(d\ge1).
\tag{43.11}
$$
故 $b_d$ 是 $f_1,\ldots,f_d$ 的整系数多项式；负整数幂 $F^{-p}$ 的第 $d$ 次系数由这些 $b_i$ 的有限卷积给出，也只依赖 $F$ 至第 $d$ 次。在（43.7）的第 $j$ 项中，逆幂系数最多用到 $a_0,\ldots,a_{k-j-1}$，外面的乘子为 $a_{n+j}$；当 $k-j=0$ 时前一变量表为空。因此全部下标不超过 $n+k$。$j=k$ 的项恰为 $a_{n+k}$，其余项的所有下标严格较小，得到（43.10）。

给有限边界时，可直接在（43.7）中使用多项式 $F_M=1+X\sum_{i=0}^M a_iX^i$ 及其形式逆。对 $n+k\le M$，任何无限延伸给的相关系数相同；所得三角独立于延伸选择，并由定理43.2等于 $\mathcal E_M(a)$。$\square$

### 43.4 限制方块、共同实现与首差几何

**命题 43.6（限制及每层唯一的新参数）。** 对 $M\ge1$，令 $\pi_M:\mathbb Q^{M+1}\to\mathbb Q^M$ 删除最后边界坐标，$\rho_M:\mathcal A_M\to\mathcal A_{M-1}$ 限制到较小三角。则
$$
\rho_M\mathcal E_M=\mathcal E_{M-1}\pi_M,\qquad
\beta_{M-1}\rho_M=\pi_M\beta_M.
\tag{43.12}
$$
两种限制均为满射；固定较小三角后，扩张恰由一个新有理参数 $a_M$ 决定。

证明。限制后的每条关系仍是原三角的关系，且首列为缩短后的边界。定理43.2的唯一性给第一式，坐标提取给第二式。任意较短边界均可添任意有理末项，扩张其边界即给一个原三角，所以满射不是方程计数的推断。反过来，任何扩张的旧边界已固定，故只剩末项可选。（43.10）将新反对角线 $n+k=M$ 上的每个坐标都写成 $a_M$ 加旧边界多项式；显示的 $M+1$ 个新坐标并非 $M+1$ 个独立选择。$\square$

**定理 43.7（全有理来源的相容族共同实现与分离）。** 每个相容有限边界族都有唯一完整有理序列实现；每个相容三角族都有唯一 $\mathcal A_\infty$ 中的数组实现。有限逆映射在全层诱导互逆的 $\beta_\infty(T)=(T(n,0))_{n\ge0}$ 与 $\mathcal E_\infty:\mathbb Q^{\mathbb N}\to\mathcal A_\infty$，后者由（43.6）或（43.7）给出。

证明。若 $u^{(M)}\in\mathbb Q^{M+1}$ 且 $\pi_Mu^{(M)}=u^{(M-1)}$，定义
$$
a_i=u^{(i)}_i.
\tag{43.13}
$$
反复应用相容性得 $u^{(M)}_i=a_i$（$i\le M$），所以这是共同实现。任何共同实现的第 $i$ 项必须如此，故唯一。

若 $U_M\in\mathcal A_M$ 且 $\rho_MU_M=U_{M-1}$，定义
$$
T(n,k)=U_{n+k}(n,k).
\tag{43.14}
$$
反复限制表明对每个 $L\ge n+k$，该值亦等于 $U_L(n,k)$。检验位置 $(n,k)$ 的后继关系时，取同一个有限阶段 $L=n+k+1$。其中包含 $T(n+1,k)$、$T(n,k+1)$，也包含每个 $T(n,j)$ 和 $T(k-j,0)$；这些坐标全与 $U_L$ 一致，而 $U_L$ 满足该关系，故 $T$ 满足无限关系。每个坐标都在某个有限三角中，因而共同实现唯一。其边界为 $a_i=U_i(i,0)$；定理43.2识别 $U_M=\mathcal E_M(a_0,\ldots,a_M)$。

反过来，每个序列及每个无限数组显然产生相容限制族，（43.12）使两个有限逆在限制下交换。因此全层逆确实保留全部同源坐标，且分离完整序列与数组。这里明确构造了源状态，没有从有限满射直接跳到共同实现，也没有调用有限字母表紧性。一个有限边界仍只决定有限三角，后来边界项在全有理来源中可以自由选取。$\square$

**命题 43.8（首个反对角层及级数的一位尺度偏移）。** 对不等序列 $a,b$ 及其数组 $T=\mathcal E_\infty(a),S=\mathcal E_\infty(b)$，置
$$
m=\min\{i:a_i\ne b_i\},\quad d_\partial(a,b)=2^{-m},\qquad
m_\Delta=\min\{n+k:T(n,k)\ne S(n,k)\},\quad
 d_\Delta(T,S)=2^{-m_\Delta};
\tag{43.15}
$$
相等对象的距离为零。这两个函数是超度量，且
$$
m_\Delta=m,\qquad
T(n,k)-S(n,k)=a_m-b_m\quad(n+k=m),\qquad
\boxed{d_\Delta(T,S)=d_\partial(a,b).}
\tag{43.16}
$$
若 $F,G$ 为相应归一化级数，令相等时 $d_X=0$，否则 $d_X(F,G)=2^{-\operatorname{ord}_X(F-G)}$，则
$$
\operatorname{ord}_X(F-G)=m+1,\qquad
\boxed{d_X(F,G)=\tfrac12d_\partial(a,b)=\tfrac12d_\Delta(T,S).}
\tag{43.17}
$$

证明。任意不等序列有最小差异下标；任意不等数组的不同坐标总次数集合也有最小值。非负性、对称性及零距离分离随定义成立。如果两个相邻对象对各自在某个前缀或三角内相等，则首尾两对象也在那里相等；取两次首差次数的较小者，得首尾距离不超过另外两个距离的最大值，即超度量不等式。相同论证适用于级数次数。

在次数 $m$ 以前，引理43.5使两个数组完全相同；坐标 $(m,0)$ 已经不同，故 $m_\Delta=m$。对该反对角线的任意 $(n,k)$，式（43.10）的较早多项式两边相同，相减即得同一增量 $a_m-b_m$。最后，$F,G$ 的常数系数均固定为一，$a_m-b_m$ 出现在 $X^{m+1}$，给（43.17）。$\square$

这仅是已指定过滤超度量的等距性，不是系数值的欧氏几何。级数度量须乘二，或删去固定常数项后重新编号，才与边界等距；不能省略该偏移。若再选定唯一的自然源，则所得域为单点，不含上述变动族的非平凡成对几何。

### 43.5 离散有理系数的实际完成及非紧性

本节给每个系数的 $\mathbb Q$ 配置**离散的精确相等拓扑**。前缀超度量产生相应乘积拓扑：固定有限初始前缀即为基本柱邻域，任意有限坐标约束可由足够长的初始前缀细化。这里不使用有理数通常绝对值的完备性；事实上该通常度量的有理数域并不完备。无限字母表 $\mathbb Q$ 也不满足先前有限字母表模型的紧性前提。

**定理 43.9（坐标稳定所给的度量完备性）。** $(\mathbb Q^{\mathbb N},d_\partial)$、$(\mathcal A_\infty,d_\Delta)$ 以及常数项一的形式级数空间配以 $d_X$ 都完备。

证明。设 $(a^{(r)})_{r\ge0}$ 是边界的 Cauchy 序列。对每个整数 $L\ge0$ 可选 $N_L$，使
$$
r,s\ge N_L\quad\Longrightarrow\quad
 d_\partial(a^{(r)},a^{(s)})<2^{-L}.
\tag{43.18}
$$
若首次差异下标不超过 $L$，距离便至少为 $2^{-L}$。因此上述严格不等式意味着第零至第 $L$ 项在这之后逐项精确相同。把第 $i$ 项最终稳定的有理数定义为 $a_i$；不同有限窗口的重叠处给同一最终值，故定义相容。对每个 $r\ge N_L$，$a^{(r)}$ 与 $a$ 的前 $L+1$ 项相同，因此
$$
d_\partial(a^{(r)},a)\le 2^{-(L+1)}.
\tag{43.19}
$$
随 $L$ 任意增大即得收敛。若还有另一极限且在第 $i$ 项与 $a$ 不同，对两种收敛都取距离小于 $2^{-i}$ 的足够后项，会强迫该项同时等于两个不同值，矛盾。于是极限唯一。定理43.7给全部数组与全部常数项一级数的对应；（43.16）的等距及（43.17）的常数比例分别运输 Cauchy 性、极限与唯一性，得到其余两个完备性结论。$\square$

**命题 43.10（稠密有限表示与坐标逆极限）。** 有限支持有理边界在全边界空间稠密，其度量完成为 $\mathbb Q^{\mathbb N}$。常数项一的多项式相应完成为常数项一的形式级数；由有限支持边界重建的数组在 $\mathcal A_\infty$ 稠密，但这些数组本身未必有限支持。各表示与系数逆极限的坐标实现相容。

证明。把 $a_0,\ldots,a_M$ 保留，后来系数设为零，得到 $a^{[M]}$。则
$$
d_\partial(a^{[M]},a)\le2^{-(M+1)},\qquad
F_{a^{[M]}}=1+\sum_{i=0}^Ma_iX^{i+1}.
\tag{43.20}
$$
这给稠密性；定理43.9及固定的包含映射给其度量完成。（43.17）给多项式的对应完成及一位次数偏移，（43.16）给数组的稠密性。截断的是边界，不能把重建后的整个数组也当成有限支持。例如边界 $(1,0,0,\ldots)$ 有 $F=1+X$、$C_0=1$，故 $R_0=(1+X)^{-1}=\sum_{k\ge0}(-1)^kX^k$，第零行已无限非零。

另给纯坐标实现：对相容的剩余类族 $v_N\in\mathbb Q[X]/(X^N)$，用任意 $N>i$ 的唯一次数小于 $N$ 的代表多项式读取第 $i$ 项。两个这样的阶段可提升到较大阶段比较，相容性使读数相同。全部读数定义唯一形式级数，其模 $X^N$ 的剩余类就是 $v_N$。反过来，任何形式级数给出相容剩余类，故
$$
\mathbb Q[[X]]\cong\varprojlim_N\mathbb Q[X]/(X^N).
\tag{43.21}
$$
$N=0$ 是平凡剩余类；常数项一的子空间在 $N=1$ 固定该常数。$N=M+2$ 恰保留固定常数及 $a_0,\ldots,a_M$。截断系数即限制剩余类，因而该构造与（43.13）的边界线程和（43.14）的三角线程保持同一限制关系。$\square$

**命题 43.11（非紧性与原来源遗漏的完成点）。** 全有理边界空间完备但不紧。若原来源只取有限支持边界，则每个有限前缀都能由原来源实现，却有完整相容线程没有原来源代表。

证明。对各 $q\in\mathbb Q$ 置
$$
a^{(q)}=(q,0,0,\ldots),\qquad
 d_\partial(a^{(q)},a^{(q')})=1\quad(q\ne q').
\tag{43.22}
$$
由超度量不等式，半径严格小于一的球至多包含其中一点。因有无限多个有理数，有限多个这种球不能覆盖该集合，所以空间不全有界。若空间紧，所有半径 $1/2$ 开球构成的开覆盖应有有限子覆盖，与前句矛盾，因此不紧。

有限支持来源通过补零实现每个有限前缀，但全一边界 $(1,1,1,\ldots)$ 不最终为零，因而没有该来源代表。其所有前缀相容，定理43.7给它在完整来源 $\mathbb Q^{\mathbb N}$ 中的唯一实现及递归数组，命题43.10又把它作为完成点。可实现的有限层、一个相容全线程、原来源实现和来源完成点是四个不同断言；本节对完整来源证明的共同实现不能自动转授给任意真子集。$\square$

### 43.6 一个保留全部档案的有限任务消费者及来源重编号

**定义 43.12（同源的两种有限读出）。** 对 $a\in\mathbb Q^{\mathbb N}$ 令
$$
p_M(a)=(a_0,\ldots,a_M),\qquad
q_M(a)=\mathcal E_M(p_M(a)),\qquad
\ker p_M=\ker q_M.
\tag{43.23}
$$
核相等由（43.4）得。全有理来源上的两个实际像分别为 $\mathbb Q^{M+1}$ 和 $\mathcal A_M$，因为每个有限边界能补零。这正核对[主卷命题133.1](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#L50708)同来源、等核、实际像上的规范运输前提。

令 $\mathcal C$ 为完整已获档案的集合，包含已获内外记录、来源及版本身份、已获关系、参考、校准、失败、停止信息、合法历史、局部钟读数及其已知共同约束。数学工作边界只替换任务端口的表示，$c\in\mathcal C$ 始终逐字保留。

**定理 43.13（双向任务、精确深度与有界自适应记录）。** 任给集合 $Z$ 和确定性任务 $h:\mathcal C\times\mathcal A_M\to Z$，同一个映射 $\mathrm{id}_{\mathcal C}\times\mathcal E_M$ 运输该域上的所有任务。反方向使用 $\mathrm{id}_{\mathcal C}\times\beta_M$。单个坐标 $(n,k)$ 的一致初始前缀最大下标 $n+k$ 充分且尖锐；整个 $\Delta_M$ 的一致初始前缀最大下标 $M$ 充分且尖锐。在共同深度界 $M$ 下，使用同一初始档案及确定性控制器的有界自适应查询，包括根据已得答案决定停止的规则，产生相同记录。

证明。定义 $h_\partial(c,v)=h(c,\mathcal E_M(v))$，则对每个有效 $T$ 有
$$
h_\partial(c,\beta_M(T))=h(c,\mathcal E_M\beta_M(T))=h(c,T).
\tag{43.24}
$$
反之，任意 $g:\mathcal C\times\mathbb Q^{M+1}\to Z$ 可定义 $g_B(c,T)=g(c,\beta_M(T))$，再由 $\beta_M\mathcal E_M=\mathrm{id}$ 得 $g_B(c,\mathcal E_M(v))=g(c,v)$。这里不是对未知输入逐次另选解码器，而是两条固定互逆映射。

引理43.5给坐标任务的深度。若保持全部更早边界不变，只改变 $a_{n+k}$，式（43.10）使该坐标改变同样数值，所以不能在全有理族上一致使用更短的初始前缀。$n+k=0$ 时此断言指空前缀不能确定 $a_0$。该尖锐性不意味着每个坐标都需要所有更早的单项。三角上所有查询都由 $p_M$ 支持，而边界查询 $T(M,0)=a_M$ 已排除更小的统一深度。

明确的细胞读数为
$$
T(1,1)=a_2-a_0a_1,\qquad
T(0,2)=a_2-3a_0a_1+a_0^3.
\tag{43.25}
$$
第一式由（43.3）得。第二式在（43.7）中使用 $[X^2]F^{-1}=a_0^2-a_1$、$[X]F^{-2}=-2a_0$ 及 $[X^0]F^{-3}=1$，相加即得。特别地，$(a_0,a_1,a_2)=(1/2,-1/3,2/5)$ 给 $T(0,2)=2/5+1/2+1/8=41/40$。

对自适应查询作实际答案归纳：首步两边的初始档案和控制器相同；若此前查询、答案及停止信息相同，确定性控制器就选择同一下一任务或同一停止决定。下一任务在边界侧取上述运输，式（43.24）给相同答案，添入的记录也相同。对每个至多预定步数的阶段归纳，得到完整 transcript 与停止决定相同；若允许无预定步数的运行，该归纳也只断言每个实际有限前缀相同，并不证明运行终止。本定理的有界结论不含随机独立性或任意干预。$\square$

若指定实际来源 $\Omega$，以 $c:\Omega\to\mathcal C$ 记录完整已获观察者，以 $a:\Omega\to\mathbb Q^{\mathbb N}$ 给数学读出，只比较同一 $\omega$ 的
$$
\omega\longmapsto(c(\omega),p_M(a(\omega))),\qquad
\omega\longmapsto(c(\omega),q_M(a(\omega))).
\tag{43.26}
$$
（43.4）使上述固定运输在这两个**对应实际像**上仍为双射，逆也保持 $c$。即使 $c$ 与 $a$ 有约束或共同来源关系，也没有独立性前提；更不能由 $a$ 一项便声称分离 $\Omega$。已知递推、有效域、编号、已供应的精确有理数及控制器是数学输入，不证明这些值已被合法测量、准备、取得或以可负担精度提供。

**命题 43.14（重建式来源移位及其有类型深度复合）。** 对 $r\ge0$ 定义来源重编号及全数组上的相应操作
$$
(\sigma^ra)_i=a_{i+r},\qquad
U_r=\mathcal E_\infty\circ\sigma^r\circ\beta_\infty.
\tag{43.27}
$$
有限实现为
$$
S_{M,r}:\mathcal A_{M+r}\longrightarrow\mathcal A_M,\qquad
S_{M,r}(T)=\mathcal E_M(T(r,0),\ldots,T(M+r,0)).
\tag{43.28}
$$
它满足有类型输入／输出方块及尖锐初始前缀深度
$$
q_M\circ\sigma^r=S_{M,r}\circ q_{M+r},\qquad
m_r(M)=M+r.
\tag{43.29}
$$
对 $M\ge1$，限制方块为
$$
\rho_M\circ S_{M,r}=S_{M-1,r}\circ\rho_{M+r}
:\mathcal A_{M+r}\longrightarrow\mathcal A_{M-1}.
\tag{43.30}
$$
对 $M,r,s\ge0$，正确的复合类型为
$$
\boxed{S_{M,r}\circ S_{M+r,s}=S_{M,r+s}
:\mathcal A_{M+r+s}\longrightarrow\mathcal A_M,}\qquad
m_s(m_r(M))=M+r+s.
\tag{43.31}
$$
全层有 $U_rU_s=U_{r+s}$；$r=0$ 时各相应映射为恒等。

证明。$q_{M+r}(a)$ 的首列正是 $a_0,\ldots,a_{M+r}$，提取从 $r$ 到 $M+r$ 的子块并重建，得到 $q_M(\sigma^ra)$，所以（43.29）两路径相同。实际用到的是子块 $a_r,\ldots,a_{M+r}$，初始前缀约定下的最大下标却是 $M+r$。输出边界坐标 $(M,0)$ 为 $a_{M+r}$，只改这一项的两个输入在任何更短初始前缀上相同，输出不同，证明尖锐性；若 $M+r=0$，更短输入为空。由（43.12），（43.30）两路径都提取 $a_r,\ldots,a_{M+r-1}$ 并施以 $\mathcal E_{M-1}$。

为验（43.31），任取输入三角，其边界记为 $a_0,\ldots,a_{M+r+s}$。第一步 $S_{M+r,s}$ 重建的边界为 $a_s,\ldots,a_{M+r+s}$；再提取这个新边界的第 $r$ 至第 $M+r$ 项，得到 $a_{r+s},\ldots,a_{M+r+s}$。施以 $\mathcal E_M$ 即右侧，所以同时给深度复合。全层以 $\beta_\infty\mathcal E_\infty=\mathrm{id}$ 消去中间逆对，再用 $\sigma^r\sigma^s=\sigma^{r+s}$ 得半群律。$S_{M,0}=\mathcal E_M\beta_M=\mathrm{id}_{\mathcal A_M}$，全层同理。$\square$

这正实现[接口36.3](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#L6185)的输入深度／输出深度合同；这里给出了显式深度，未借连续性推断统一深度。工作操作是 $(c,T)\mapsto(c,S_{M,r}T)$，其输入深度须已供应。已记录在 $c$ 中的较早系数、关系及来源身份保持不变；更多系数须经明确获取合同才进入实际观察者。代数重编号不取得未来值，也不宣称物理演化。

重建一般不同于原数组的行平移。若边界始于 $(1,2,3)$，正确移位的新边界始于 $(2,3)$，所以
$$
U_1(T)(0,1)=3-2^2=-1,\qquad T(1,1)=3-1\cdot2=1.
\tag{43.32}
$$
证明是（43.3）的直接计算：移位后卷积由新边界驱动，故必须重建；只改行号一般不满足运输后的递归关系。此反例同时区分本节的来源起点变化与删去最后一层的限制映射。

**命题 43.15（连续任务没有普遍的统一有限深度）。** 定义
$$
\ell(q)=\begin{cases}q,&q\in\mathbb Z_{\ge0},\\0,&\text{其它},\end{cases}
\qquad H(a)=a_{\ell(a_0)}.
\tag{43.33}
$$
第一种情形的 $q$ 作为自然数下标使用。$H:\mathbb Q^{\mathbb N}\to\mathbb Q$ 在离散系数前缀拓扑中局部常值，但不存在对全部输入有效的有限初始前缀深度。

证明。固定 $a$，令 $L=\ell(a_0)$；在固定前缀至 $L$ 的邻域内，第零项不变，所选下标不变，该下标的值也不变，所以 $H$ 局部常值，因而连续到离散 $\mathbb Q$。反之，对任意 $M\ge0$，取两序列的第零项均为 $M+1$，在下标至 $M$ 的整个前缀相同，而第 $M+1$ 项一个为零、一个为一。它们的 $H$ 值不同，故 $H$ 不能通过 $p_M$ 因子化。$\square$

有限字母表紧空间中可从局部常值柱覆盖取有限子覆盖，再取最大深度；命题43.11已排除本有理空间的紧性，不能移用那一步。命题43.15限制的是一般连续任务的推断，不否定（43.29）—（43.31）已明确证明的 $S_{M,r}$ 深度与复合。

### 43.7 顶行约束选回既有自然对象

**命题 43.16（顶行与源方程的等价及有限逐项选择）。** 在定义43.3的完整有理族中，顶行全一恰等价于既有归一化源方程；在 $\Delta_M$ 中，仅要求 $T(0,k)=1$（$0\le k\le M$）就逐项唯一选定边界和三角。

证明。由（43.5）、（43.6）直接得到
$$
F(Y)=1+YC_0(Y)=1+XR_0(X).
\tag{43.34}
$$
$\mathbb Q[[X]]$ 中乘 $X$ 是单射，而 $1+X(1-X)^{-1}=(1-X)^{-1}$，故
$$
\boxed{T(0,k)=1\ (\forall k)\quad\Longleftrightarrow\quad
R_0=(1-X)^{-1}\quad\Longleftrightarrow\quad
F(X/F(X))=(1-X)^{-1}.}
\tag{43.35}
$$
反向可从（43.34）两侧减一，得到 $XR_0=X(1-X)^{-1}$，再消去 $X$；未除以非单位 $Y$。

有限情况下，（43.10）在 $n=0$ 给第 $k$ 条方程 $a_k+P_{0,k}(a_0,\ldots,a_{k-1})=1$。从 $k=0$ 开始，每一步恰选一个有理数；定理43.2再给其唯一三角。既有 `AntidiagonalArraySourceSeries.result` 的自然数组限制到 $\Delta_M$ 满足这些条件，因此就是该选择，所有选中体坐标和边界项均为自然数。$\square$

无限处的存在、唯一性、自然系数及首列识别由第43.1节的现有形式供应承担，不重立一个一般形式化结果。前面的（43.6）—（43.7）联系的是任意有理边界与**满足指定后继关系**的数组，既不是任意数组与任意级数的等价，也不是单凭 $F(0)=1$ 就得顶行全一。该附加源方程把变动有理族选成一个对象，没有概率或物理定律含义。

### 43.8 固定重建核的 Riordan 方法归属

**命题 43.17（固定 $F$ 的下三角系数作用）。** 固定边界 $a$ 因而固定 $F$，定义
$$
D_{k,j}=[X^k]\bigl(F^{-1}(XF^{-1})^j\bigr)
=\begin{cases}[X^{k-j}]F^{-(j+1)},&j\le k,\\0,&j>k.\end{cases}
\qquad D_{k,k}=1.
\tag{43.36}
$$
这是形式对 $(g,h)=(F^{-1},XF^{-1})$ 的 proper Riordan 系数矩阵，属于 Bell 形式 $(g,Xg)$。其对任意形式级数的作用在每个坐标都是有限和；取输入 $C_n$ 即（43.7）。

证明。更一般地，对 $g,h,H\in\mathbb Q[[X]]$，若 $h(0)=0$（零级数也允许），则每个 $h^j$ 被 $X^j$ 整除，因此
$$
[X^k]\bigl(g(X)H(h(X))\bigr)
=\sum_{j=0}^{k}[X^k]\bigl(g(X)h(X)^j\bigr)[Z^j]H(Z).
\tag{43.37}
$$
高于 $k$ 的项贡献为零，所以这是有限系数恒等式。在本节中 $g(0)=1$，$h=XF^{-1}$ 的一次系数为一、阶恰为一，满足 proper 核的非退化条件。分离 $X^j$ 得（43.36）；对角元为 $F^{-(k+1)}$ 的常数项一。令 $H=C_n$，其第 $j$ 项为 $a_{n+j}$，便得所需重建公式。证明只用有理系数逆和有限卷积。$\square$

Tian-Xiao He 与 Yuanziyi Zhang 的 *Centralizers of the Riordan Group*，arXiv:2105.07262v1（2021年5月15日），引言给出 $D_{k,j}=[X^k]g(X)h(X)^j$、作用 $(g,h)H=gH(h)$ 及 Bell 子群的这些定义。[^rroctx43_riordan] 其表述采用实或复系数；（43.37）直接给出本应用所需的有理有限系数证明。成熟方法归属限于这项系数机制，不是对当前递归或 OEIS 识别结论的外部定理引用。

只有固定 $F$ 的重建核 $D$ 是上述下三角矩阵。递归数组 $T$ 一般不是下三角 Riordan 矩阵：例如 $T(0,1)=a_1-a_0^2$ 可以非零。（43.7）的输入还是依赖 $n$ 的尾序列 $a_{n+j}$；让 $a$ 变化时 $F$ 和 $D$ 也随之变化。因此整个边界到体的映射是多项式且一般非线性的，不能把它说成一个固定线性 Riordan 变换。此处不引入其它 Riordan 恒等式或未经给出条件的成熟结论。

### 43.9 正性、形式语义及操作资源的边界

**命题 43.18（自由有理对应不能自动加强的结论）。** 以下反例分别界定正性、有限信息、归一化及数值稳定性的范围。

证明。先取 $M=1$ 和自然边界 $(a_0,a_1)=(1,0)$。由（43.3）得
$$
T(0,1)=a_1-a_0^2=-1.
\tag{43.38}
$$
所以自然边界也未必给非负体；既有形式供应的正性来自特选顶行数组，不能仅从单位常数或形式可逆推出。

其次，对任何 $M\ge0$，零边界与唯一非零项为 $a_{M+1}=1$ 的边界在 $\Delta_M$ 上重建相同，到下一反对角层便不同，见引理43.5和命题43.8。这说明一个有限前缀没有确定自由完成对象。

零边界还给 $F=1$，所以 $F(X/F)=1\ne(1-X)^{-1}$；归一化自身不提供源方程。若放弃可逆的常数项，形式逆可能不存在，例如 $F=X$，其任何倍数常数项都为零，不可能等于一。若把非零常数的级数代入任意无限外级数，也未必逐系数有定义，例如 $H(Z)=\sum_{j\ge0}Z^j$ 代入 $Z=1$ 令常数系数成为无限多个一的和，而有理形式系数环没有这项操作。本节的 $F(0)=1$ 和 $Y(0)=0$ 明确避开这些障碍。

最后，把 $a_0=0$ 换成任意非零有理数，无论普通绝对值多小，前缀距离都是一；它没有测量系数大小。即使 $M=1$，固定 $a_1$ 而把 $a_0$ 从 $u$ 改为 $u+\delta$，也有
$$
T_{u+\delta}(0,1)-T_u(0,1)=-2u\delta-\delta^2.
\tag{43.39}
$$
取 $\delta=1$ 并让有理 $u$ 无界，输出差与输入欧氏距离之比无界。因此精确前缀等距不给全域欧氏 Lipschitz 常数；数值稳定性需要另选度量及幅度域界。$\square$

（43.9）的余项在任一固定次数经过有限步后为零，（43.21）的完成则存储全部相容系数。这些是形式语义，不断言实／复解析收敛或非零收敛半径，不给概率归一化、TV 尾界、噪声估计、量子实现或物理钟。完成是所声明的拓扑和包含映射的结果，不是自动赋予一项概率律。

第零列边界与三角体只是组合坐标；其等价没有把 $n$ 指定为物理时间，也没有把数组体指定为空间区域。操作上取得精确有理值仍需来源及合法历史合同。算法虽只做有理加减乘，固定 $M$ 时分子、分母及中间数的位长仍可无界；$M+1$ 个自由参数不给位复杂度、样本复杂度、最优运行时间或抗噪性。确定性任务运输没有隐含概率独立；合法操作次序与概率独立也不同。若另引随机来源，独立性须针对保留的完整档案条件化后验证，不能由本节代数恢复替代。

完整有理域与顶行全一的自然域不能混用：后者由既有定理选成单点，前者才承载首差几何、非紧性和任意边界任务。第40—42节各自的相对钟、量子档案及接收资源条件没有因本节的形式完成而被免除。

### 43.10 离散全层与完成体／边实际等价的内容

**推论 43.19（同一递归关系的相容表示链）。** 对声明的完整有理来源，有以下每箭头都带逆或坐标共同实现的表示链：
$$
\boxed{
\text{有理边界序列}
\ \longleftrightarrow\ \text{无限约束数组}
\ \longleftrightarrow\ \text{相容的全部有限三角}
\ \longleftrightarrow\ \text{常数项一的形式级数}.}
\tag{43.40}
$$
相容的全部有限边界通过 $\beta_M,\mathcal E_M$ 给同一个全层对象。有限深度上的恢复是多项式互逆；全部深度上的边界和体首差等距，级数带（43.17）的一位归一化偏移。有限支持表示稠密，完成增添相容无限选择。该链的有限任务与来源重编号保持第43.6节规定的完整档案和获取义务。

证明。定理43.2给有限逆；定理43.4给级数到行及边界到无限数组的公式；从归一化级数读取 $[X^{i+1}]F$ 给回边界，反向由（43.5）重建同一级数。定理43.7及命题43.10的坐标构造给全相容族与形式剩余类的共同实现。（43.12）使限制交换，命题43.8给尺度，定理43.9和命题43.10给实际完成，定理43.13及命题43.14给档案任务和操作的对应。$\square$

这是一项带明确递归、来源、分离和拓扑条件的体／边应用。保留全部相容有限层可以保存整个对象，一条轨道的最终标量极限却不保证如此：例如序列 $x_n=0$ 与 $y_n=1/(n+1)$ 的通常实数极限同为零，而完整记录不同。命题43.11也表明，原来源可以遗漏完成点。因此离散步骤和完成对象在本模型中具有精确的共同关系表示，不意味着任意有限数据、任意标量极限与任意原来源可以互相恢复。坐标起点并不给出物理底层，重编号也不丢弃已获过去或取得未知未来。

### 43.11 供应接口的精确适配与文献边界

**约定 43.20（既有供应的作用域）。** 本节的特选自然数组和源恒等式保留第43.1节 `AntidiagonalArraySourceSeries.result` 的归属，以及同快照的 [Problems 卷宗](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/Problems/oeis-a392095-antidiagonal-source-series.md)、Library 引文与对应 Blueprint。引用锚是确切公开定理和不可变源码，不声称重新生成了声明的 statement hash；证明内部的局部名字仍只用来说明证明机制。

[InverseLimitCompletion 的 `stateThread_bijective_iff_complete_and_separates`](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean) 给 Type 层的通用判据。对本节取状态 $\mathbb Q^{\mathbb N}$、第 $M$ 层坐标 $\mathcal A_M$、读出 $q_M$，该模块从 level $M+1$ 到 level $M$ 的 `restrict M` 对应这里 $\rho_{M+1}$。命题43.6给相容性；若全部 $q_M(a)=q_M(b)$，提取第 $i$ 层的 $(i,0)$ 即得 $a_i=b_i$，这是分离性；定理43.7给每个线程的实际共同序列。模块的 `ThreadComplete` 是 `stateThread` 的满射性，不是度量完备性；后者由定理43.9另行证明，未从 Type 判据导入拓扑、紧性、概率或取得能力。

[LocalGlobalAtlasExactness 的 `local_global_atlas_exactness`](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/D5/S3/ConceptDynamics/RefinementGeometry/LocalGlobalAtlasExactness.lean) 是分离及像条件的另一既有表述，不是这里待重证的新一般定理。[CompletionIsomorphismCriterion](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/D5/S3/ObserverMemory/InverseLimits/CompletionIsomorphismCriterion.lean) 与 [StableObservationInverseLimit](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/D5/S3/ConceptDynamics/RefinementGeometry/StableObservationInverseLimit.lean) 保留各自域及前提，不能仅因都使用完成一词便移入本族。

主卷命题133.1拥有等核实际像的规范运输；（43.23）和（43.26）核对前提，（43.24）提供其保留档案的具体消费者，没有另建一个等核通用框架。[Context 接口36.3](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#L6185)拥有换精度合同，（43.29）—（43.31）为本消费者证明输入深度、输出深度及复合。其紧有限字母表上的连续性结论不能覆盖离散有理字母表，命题43.15给明确边界。

[Context 命题38.5](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#L6610)区分有限读数、全相容族、原来源实现与完成。它的有限坐标及概率前提不转移到有理族；本节直接以稳定坐标、共同实现和非紧性证明所需有理结论。第36.4、38.4节的完整记录区别落实为 $\mathrm{id}_{\mathcal C}\times\mathcal E_M$ 及保留 $c$ 的移位操作，未将工作边界等同于全部观察者。

邻近的 `PerrierPeriodicGeneratingFunctions` 属于另一有限维线性递推，不直接实例化到这里随边界变化的非线性族；不同具名三角、一般 Gram 结构或概率完成也不是（43.3）、（43.7）的精确所有者。本节的扩大有理应用及其普通证明不构成新增 Lean 声明、kernel 检验或定理准入结论。

[^rroctx43_oeis]: Mikhail Kurkov，OEIS A392095，数组后继关系与首列 A088713 偏移识别；Paul D. Hanna，OEIS A088713，源方程 $F(X/F(X))=(1-X)^{-1}$。固定 OEIS 导出为 `892a05dd4941ae76caee5906ea33ceedf3389b1d`：[A392095](https://github.com/oeis/oeisdata/blob/892a05dd4941ae76caee5906ea33ceedf3389b1d/seq/A392/A392095.seq)、[A088713](https://github.com/oeis/oeisdata/blob/892a05dd4941ae76caee5906ea33ceedf3389b1d/seq/A088/A088713.seq)。相应仓内引文为 [kurkov2025a392095](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/Library/Recurrence/kurkov2025a392095.md) 及 [hanna2003a088713](https://github.com/the-omega-institute/trureturing/blob/1fae30cf331dd943f49e44f88c9ee0feb3829770/Library/Recurrence/hanna2003a088713.md)，保留其 OEIS Foundation [CC-BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/) 归属。上述固定源不代表实时条目新鲜性或全球优先权。

[^rroctx43_riordan]: Tian-Xiao He and Yuanziyi Zhang, *Centralizers of the Riordan Group*, [arXiv:2105.07262v1](https://arxiv.org/abs/2105.07262v1), 15 May 2021，Introduction，第1—2页的系数定义、基本作用及 Bell 子群。经典历史文献为 L. W. Shapiro, S. Getu, W.-J. Woan and L. C. Woodson, *The Riordan group*, *Discrete Applied Mathematics* **34** (1991), 229–239, DOI [10.1016/0166-218X(91)90088-E](https://doi.org/10.1016/0166-218X(91)90088-E)。本节依据上述版本化引言及（43.37）的有理有限系数证明，不把经典全文或其余 Riordan 定理当作已核对的应用前提。

## 43.99 追加锚

## 44. 实际历史压缩的二阶响应与校准短区间时钟

本节把同一个正伴随来源的内部演化、延迟历史、边界压缩和相对时钟连成一个有限维接口。先在有限实或复 Hilbert 空间证明压缩响应的二阶缺陷界，再把它精确代入本卷第40节的实际有限实历史。误差控制依赖共同实现、实际支撑、谱裕量、校准和已获关系，不能由表示名称推得物理定律。结论属于既有数学机制在该接口上的普通综合，这里的结论只在所列数学假设下成立，不判断形式系统或文献新颖性。

### 44.1 同一实际来源、移位历史与解析模型

**定义 44.1（解析模型与实际消费者的类型）。** 下列未加下标的范数均为相应有限维 Hilbert 空间间的算子范数；Frobenius 范数明确记为 $\|\cdot\|_F$。解析模型允许实或复数，$*$ 始终使用给定内积的伴随，复数时含共轭。

设 $h>0$，$C=C^*>0$ 作用于有限维空间 $R$，$F:R\to E$ 是余等距映射，即 $FF^*=I_E$。置
$$
P=F^*F,\qquad S=e^{-hC},\qquad aI_R\le S\le bI_R,
\qquad 0<a\le b<1,
$$
$$
A=FSF^*,\qquad
\Delta=FS^2F^*-A^2=FS(I-P)SF^*.
$$
令
$$
Q=I-P,\quad \delta=\|\Delta\|,\quad
\ell=\|QSF^*\|=\sqrt\delta.
$$
**引理 44.2（残差平方和交换子）。** 由 $S=S^*$，
$$
\|[P,S]\|=\|QSP\|=\ell,\qquad
 aI_E\le A\le bI_E.
$$
证明。$FF^*=I_E$ 使 $P=P^*=P^2$，$F^*$ 等距到 $\operatorname{ran}P$；插入 $P+Q=I_R$ 给残差恒等式。这里 $\Delta=(QSF^*)^*(QSF^*)$；交换子的范数等式由相对于 $P\oplus Q$ 的自伴分块形式得到。
进一步，令 $T=QSP:\operatorname{ran}P\to\operatorname{ran}Q$，交换子分块为 $\begin{pmatrix}0&T^*\\-T&0\end{pmatrix}$，其伴随乘自身为 $\operatorname{diag}(T^*T,TT^*)$，故范数为 $\|T\|$。$F^*$ 对 $\operatorname{ran}P$ 的满等距性给 $\|T\|=\|QSF^*\|$，残差平方再给 $\ell^2=\delta$。证毕。

把 $R$ 具体取为以下 $\mathcal R$。要将解析模型解释为本卷第40节的实际历史，须完整保留其定义40.1的合同：$C_{\rm archive}$ 包含全部已获内部／外部记录、来源与参考身份、版本与关联、实际准备、输入／输出内积与单位、增益、设备身份、相位与校准、局部时钟及已知关系、局部标签、可访问记忆、动作、守卫及失败、联合顺序和允许的联合误差事件；与档案及先验相容的共同世界族非空并含实际世界。以下每个候选世界都须同时解释整份档案，矩阵统计量仅是任务视图。

在每个这样的世界中，源核为
$$
K(t)=Be^{-tC}B^*,\qquad C=C^*>0,
$$
且输入是指定内积下的实际伴随 $B^*$。有效循环空间为
$$
\mathcal R=\operatorname{span}\{C^jB^*u:j\ge0,\ u\in U\},
\qquad C_{\mathcal R}=C|_{\mathcal R}.
$$
共同加性延迟 $h$ 必须实际成立。令
$$
V_k=\operatorname{span}\{e^{-jhC}B^*u:0\le j\le k\},\qquad
B_kx=(Be^{-ihC}x)_{i=0}^k,
$$
$$
\mathsf H_k(s)=\bigl(K(s+(i+j)h)\bigr)_{0\le i,j\le k},
\qquad E_k=\operatorname{ran}B_k.
$$
Context40 引理40.2供应
$$
\mathsf H_k(s)=B_ke^{-sC}B_k^*,\qquad
\operatorname{ran}\mathsf H_k(s)=E_k\quad(s\ge0).
$$
要求 $E_k\ne0$，并且全部白化、对数、迹与行列式只在这个实际共同支撑上计算。记
$$
D=B_k|_{\mathcal R}:\mathcal R\longrightarrow E_k,\qquad
D_{(t_0)}=De^{-t_0C_{\mathcal R}/2},
$$
$$
M_{(t_0)}=\mathsf H_k(t_0)|_{E_k}=D_{(t_0)}D_{(t_0)}^*,
\qquad
F_{(t_0)}=M_{(t_0)}^{-1/2}D_{(t_0)}.
$$
实际基准 $t_0$ 可未知，但必须有限且非负。$M_{(t_0)}$ 是白化基准矩阵；本节的 $A$ 是白化后的一步响应，二者不是同一个矩阵。本卷第40节的基准符号 $a$ 在此替换为 $t_0$，其 $A_a$ 替换为 $M_{(t_0)}$，其 $F_a$ 替换为 $F_{(t_0)}$；第40节历史阶数 $r$ 替换为 $k$。

$D_{(t_0)}$ 满射到 $E_k$，故 $M_{(t_0)}>0$ 且 $F_{(t_0)}F_{(t_0)}^*=I$。对任意满射 $J$，$J^*(JJ^*)^{-1}J$ 自伴幂等，像为 $\operatorname{ran}J^*$；这里 $\operatorname{ran}D^*=V_k$，所以投影的像恰为 $e^{-t_0C_{\mathcal R}/2}V_k$。指数的相乘及与 $C_{\mathcal R}$ 交换给
$$\mathsf H_k(t_0+t)|_{E_k}=D_{(t_0)}e^{-tC_{\mathcal R}}D_{(t_0)}^*.$$
固定这份实际基准及历史接口，定义
$$
W(t)=M_{(t_0)}^{-1/2}
\bigl(\mathsf H_k(t_0+t)|_{E_k}\bigr)M_{(t_0)}^{-1/2}
=F_{(t_0)}e^{-tC_{\mathcal R}}F_{(t_0)}^*.
$$
Context40 命题40.6供应
$$
F_{(t_0)}F_{(t_0)}^*=I_{E_k},\qquad
P_{(t_0)}=F_{(t_0)}^*F_{(t_0)}
=P_{e^{-t_0C_{\mathcal R}/2}V_k}.
$$
投影一般不是未经基准移位的 $P_{V_k}$。于是一般模型的精确代入为
$$
F=F_{(t_0)},\qquad S=e^{-hC_{\mathcal R}},\qquad
A=W(h),\qquad\Delta=W(2h)-W(h)^2.
$$
这里另行要求用于定量估计的实际有效谱界 $aI\preceq S\preceq bI$；正定性逐模型成立，不自动供应模型族共用的裕量。仅凭压缩矩阵 $A$ 的谱下界，不能将其冒充整个有效 $S$ 的谱下界。

以下设 $m=\dim E_k>0$（一般模型为 $m=\dim E>0$），定义
$$
\mathcal T=\operatorname{tr}(-\log A),\qquad
\tau=\mathcal T/m,\qquad\beta=-\log b>0,
$$
$$
R(r)=\frac{\operatorname{tr}(-\log W(rh))}{\mathcal T}.
$$
由 $aI\preceq A\preceq bI<I$，有 $\mathcal T\ge m\beta>0$、$\tau\ge\beta$。$\tau$ 是同一实际基准上的平均对数衰减量；未饱和时，它可以依赖 $t_0$，不能借用饱和情形的基准不变性。零维支撑给 $0/0$，不属于本比值定理。

这里明确取有限维实内积空间 $H,U$，输入是实际准备的伴随 $B^*$；解析引理允许复数不改变此实际来源合同。合法操作顺序与概率独立是不同条件，任何独立性主张须条件于完整 $C_{\rm archive}$ 检验。历史阶数为 $k$，经过时间指数为 $r=t/h$；它们均不同于源核 $K$、基准年龄 $t_0$、谱下界 $a$ 和后文的误差系数 $K_{\rm err}$。

### 44.2 离散两次跨越与固定阶数尖锐性

**定理 44.3（离散压缩响应）。** 交换子展开给
$$
[P,S^k]=\sum_{j=0}^{k-1}S^j[P,S]S^{k-1-j},
\qquad
\|QS^kF^*\|\le k b^{k-1}\ell\quad(k\ge1).
$$
交换子求和由 $[P,XY]=[P,X]Y+X[P,Y]$ 归纳成立；又 $Q[P,S^k]F^*=-QS^kF^*$，从而每项范数至多 $b^{k-1}\ell$。置 $E_n=FS^nF^*-A^n$。由 $FF^*=I_E$ 及 $A=FSF^*$，端点 $E_0=E_1=0$。对 $n\ge2$ 插入 $P+Q$，得到
$$
E_n=AE_{n-1}+FSQ\,S^{n-1}F^*,\qquad E_1=0.
$$
因此
$$
\|E_n\|\le b\|E_{n-1}\|+(n-1)b^{n-2}\delta,
$$
归纳中 $E_1=0$，而 $b\binom{n-1}{2}b^{n-3}\delta+(n-1)b^{n-2}\delta=\binom n2 b^{n-2}\delta$，故得到
$$
\boxed{\|FS^nF^*-A^n\|
\le {n\choose2}b^{n-2}\delta,\qquad n\ge2.}
$$
两次跨越观察子空间产生 $\ell^2=\delta$；普通单侧交织界只有 $O(\sqrt\delta)$。

该系数对每个固定整数 $n\ge2$，在 $\varepsilon\downarrow0$ 时渐近锐；不声称对随 $\varepsilon$ 增长的 $n$ 有一致相对锐性。固定 $0<a<b<1$，取
$$
S_\varepsilon=
\begin{pmatrix}b-\varepsilon&\varepsilon\\
\varepsilon&b-\varepsilon\end{pmatrix},
\quad F=(1,0),\quad
0<2\varepsilon<b-a.
$$
其谱为 $b,b-2\varepsilon$，且 $A=b-\varepsilon,\ \delta=\varepsilon^2$。于是
$$
FS_\varepsilon^nF^*-A^n
=\frac{b^n+(b-2\varepsilon)^n}{2}-(b-\varepsilon)^n
={n\choose2}b^{n-2}\varepsilon^2+O(\varepsilon^3).
$$
$n=2$ 为精确等号；$C_\varepsilon=-h^{-1}\log S_\varepsilon>0$ 满足原模型。

### 44.3 一个正 resolvent 引擎与三种对数缺陷

**定理 44.4（正二阶余项）。**

令
$$
S_0=PSP+QSQ,\quad V=S-S_0,\quad
R_u=(S+uI_R)^{-1},\quad R_u^0=(S_0+uI_R)^{-1}
\quad(u\ge0).
$$
两条逆差恒等式 $R_u-R_u^0=-R_u^0VR_u=-R_uVR_u^0$ 相互代入，得到二阶 resolvent 恒等式
$$
R_u-R_u^0
=-R_u^0VR_u^0+R_u^0VR_uVR_u^0.
$$
定义 $D(u)=FR_uF^*-(A+uI_E)^{-1}$。
压缩到 $P$ 后首项消失；余项半正定，而且
$$
0\le FR_uF^*-(A+uI_E)^{-1},\qquad
\|FR_uF^*-(A+uI_E)^{-1}\|
\le\frac{\delta}{(a+u)^3}.
$$
更具体地，余项为
$$
(A+uI_E)^{-1}FSQ\,R_u\,QSF^*(A+uI_E)^{-1},
$$
其半正定性及范数界直接来自 $R_u\succeq0$、$\|R_u\|\le(a+u)^{-1}$ 和 $\|FSQ\|=\sqrt\delta$。
$FSQ:R\to E$ 与 $QSF^*:E\to R$ 互为伴随；两边的 $(A+uI_E)^{-1}$ 自伴。故该式为 $X^*R_uX$，其中 $X=QSF^*(A+uI_E)^{-1}$，正性不要求这些因子交换。$S_0\succeq aI$ 是两个角各自的下界，因此所有逆存在，三个逆因子共同给 $(a+u)^{-3}$。这一个 $D(u)$ 将同时供应对数及两段分数幂。

**推论 44.5（生成元、非对角块和矩形交织）。** 定义
$$G=-h^{-1}\log A,\qquad C_c=FCF^*,\qquad c_0=-\log b/h>0.$$
有限谱演算给 $C,C_c,G\succeq c_0I$。对任意正定 $X$，
$$\log X=\int_0^\infty\left((1+u)^{-1}I-(X+uI)^{-1}\right)du.$$
该积分在零端有界，远端为 $O(u^{-2})$；它来自每个正标量的初等积分并在有限谱上逐项相加。于是同一截断积分中常数项消去，给
$$C_c-G=h^{-1}\int_0^\infty D(u)\,du\succeq0,$$
$$\boxed{\|C_c-G\|\le\frac{\delta}{2ha^2},\qquad0\preceq C_c-G.}$$
这里使用 $\int_0^\infty(a+u)^{-3}du=1/(2a^2)$。又 $[P,R_u]=-R_u[P,S]R_u$，故
$$[P,\log S]=\int_0^\infty R_u[P,S]R_u\,du.$$
由自伴分块 $\|[P,C]\|=\|QCP\|$ 及 $\int_0^\infty(a+u)^{-2}du=1/a$，得到
$$\boxed{\|QCP\|\le\frac{\sqrt\delta}{ha}.}$$
这些是算子积分估计，单独引用标量对数 Lipschitz 性不构成该证明。

单侧对数交织另有安全备选界。精确矩形 resolvent 恒等式为
$$
\boxed{
F(S+uI_R)^{-1}-(A+uI_E)^{-1}F
=-(A+uI_E)^{-1}FSQ(S+uI_R)^{-1}.
}
$$
这是因为 $FS-AF=FSQ$。对数积分表示给
$$
F\log S-(\log A)F
=\int_0^\infty
(A+uI_E)^{-1}FSQ(S+uI_R)^{-1}\,du.
$$
由 $\int_0^\infty(a+u)^{-2}du=a^{-1}$ 得
$$
\|FC-GF\|\le\frac{\sqrt\delta}{ha}.
$$
对 $e^{-(t-s)G}Fe^{-sC}$ 求导，导数为 $e^{-(t-s)G}(GF-FC)e^{-sC}$。积分后右接 $F^*$；两个半群分别以 $c_0$ 衰减，所以得到
$$
\|Fe^{-tC}F^*-e^{-tG}\|
\le \frac{t}{ha}b^{t/h}\sqrt\delta.
$$

### 44.4 连续响应的两次 Duhamel 与全时间控制

**定理 44.6（全时间响应）。** 令 $L=\|QCP\|$。有限维乘积法则给
$$[P,e^{-sC}]=-\int_0^s e^{-(s-v)C}[P,C]e^{-vC}\,dv.$$
左右接 $Q,F^*$，用 $Q[P,e^{-sC}]F^*=-Qe^{-sC}F^*$，得到
$$
\|Qe^{-sC}F^*\|\le s e^{-c_0s}L.
$$
对 $e^{-(t-s)C_c}Fe^{-sC}F^*$ 求导，使用 $C_cF=FCP$，导数恰为 $-e^{-(t-s)C_c}FCQe^{-sC}F^*$。积分得
$$
Fe^{-tC}F^*-e^{-tC_c}
=-\int_0^t e^{-(t-s)C_c}FCQe^{-sC}F^*\,ds,
$$
故
$$
\|Fe^{-tC}F^*-e^{-tC_c}\|
\le \tfrac12t^2e^{-c_0t}L^2.
$$
同时，对 $e^{-(t-s)C_c}e^{-sG}$ 求导，导数为 $e^{-(t-s)C_c}(C_c-G)e^{-sG}$，积分和两边的 $c_0$ 衰减给
$$
\|e^{-tC_c}-e^{-tG}\|
\le te^{-c_0t}\|C_c-G\|.
$$
合并得到
$$
\boxed{
\|Fe^{-tC}F^*-e^{-tG}\|
\le
\frac{\delta\,b^{t/h}}{2a^2}
\left(\frac{t^2}{h^2}+\frac th\right),\qquad t\ge0.
}
$$
这是连续时间可用界，不宣称其常数最优；整数时刻应使用上面的更锐离散界。特别地，$t=0$ 时两响应均为 $I_E$，而 $t=h$ 时
$$
Fe^{-hC}F^*=A=e^{-hG},
$$
故误差精确为零。上面的三角估计没有保留 $t=h$ 处的抵消。另一方面，
$$
\left.\frac{d}{dt}\left(Fe^{-tC}F^*-e^{-tG}\right)\right|_{t=0}
=G-C_c
$$
一般非零，所以不能把该连续响应误差普遍替换成固定模型下的 $O(t^2\delta)$ 小时间界。

若模型族共用 $a>0$ 和 $b<1$，置 $\beta=-\log b>0$，则还有统一全时间界
$$
\boxed{
\sup_{t\ge0}\|Fe^{-tC}F^*-e^{-tG}\|
\le\frac{\delta}{2a^2}
\left(\frac{4}{e^2\beta^2}+\frac{1}{e\beta}\right).
}
$$
证明。令 $x=t/h\ge0$，则 $b^{t/h}=e^{-\beta x}$。分别使用
$$
\sup_{x\ge0}x^2e^{-\beta x}=\frac4{e^2\beta^2},
\qquad
\sup_{x\ge0}xe^{-\beta x}=\frac1{e\beta},
$$
再以上确界的次可加性应用于前式即可。这个常数不宣称最优；共同谱界固定时，它给出随 $\delta\to0$ 的全时间一致压缩响应收敛，不提供隐藏态或物理时钟恢复。
例如 $F=(1,0)$、$S=\begin{pmatrix}s&\varepsilon\\\varepsilon&s\end{pmatrix}$，$0<\varepsilon<\min(s,1-s)$，有
$$C_c-G=-\frac1{2h}\log(1-\varepsilon^2/s^2)>0.$$
因此固定此模型、$t\downarrow0$ 时误差含非零线性项，明确排除 $O(t^2\delta)$。对每个整数时刻，定理44.3的界仍可更精细。


### 44.5 两段谱分数幂、显式 Beta 常数与端点

**定理 44.7（分数幂正差及其范数）。** 本节首先只要求有限维实或复 Hilbert 空间、$FF^*=I_E$、$S=S^*\succeq aI_R$，其中共同谱下界 $a>0$。仍令
$$
A=FSF^*,\qquad \Delta=FS^2F^*-A^2\succeq0,
\qquad \delta=\|\Delta\|.
$$
不需要 $b<1$、预先给定 $h$ 或 $S=e^{-hC}$，也不要求 $S$ 与 $P=F^*F$ 交换。共同正谱下界用于控制负指数因子 $a^{r-2}$；有限维保证谱有界。

对 $0<r<1$，有
$$
\boxed{
0\preceq A^r-FS^rF^*,\qquad
\|A^r-FS^rF^*\|
\le \frac{r(1-r)}2a^{r-2}\delta.
}
$$
对 $1<r<2$，有
$$
\boxed{
0\preceq FS^rF^*-A^r,\qquad
\|FS^rF^*-A^r\|
\le \frac{r(r-1)}2a^{r-2}\delta.
}
$$
这里分别给出半正定方向及算子范数控制，不将范数估计改写成缺陷矩阵受同一常数乘以 $\Delta$ 控制的 Loewner 序断言。

证明。先给两段标量表示及共同截断。

沿用定理44.4的精确二阶 resolvent 恒等式，令
$$
D(u)=F(S+uI_R)^{-1}F^*-(A+uI_E)^{-1},\qquad u\ge0.
$$
则
$$
D(u)\succeq0,\qquad
\|D(u)\|\le\frac{\delta}{(a+u)^3}.
$$
对 $0<r<1$，标量公式及有限维谱演算给出
$$
x^r=\frac{\sin(\pi r)}\pi
\int_0^\infty u^{r-1}\frac{x}{x+u}\,du.
$$
标量式由 $u=xv$ 给 $x^r\int_0^\infty v^{r-1}/(1+v)dv$，后者为 $B(r,1-r)=\pi/\sin\pi r$；端点收敛由 $0<r<1$ 保证。使用 $x/(x+u)=1-u/(x+u)$ 及 $FF^*=I_E$，在相同截断积分中相减，再取极限，得到
$$
A^r-FS^rF^*
=\frac{\sin(\pi r)}\pi
\int_0^\infty u^rD(u)\,du\succeq0.
$$
不能将这一步写成分别计算发散的常数项积分。

对 $1<r<2$，使用另一段标量表示
$$
x^r=\frac{\sin(\pi(r-1))}\pi
\int_0^\infty u^{r-2}\frac{x^2}{x+u}\,du.
$$
此式用 $u=xv$ 化为 $x^r B(r-1,2-r)$，正弦归一化来自同一反射公式。由 $x^2/(x+u)=x-u+u^2/(x+u)$，压缩前后的仿射项在相同截断处精确抵消，因此
$$
FS^rF^*-A^r
=\frac{\sin(\pi(r-1))}\pi
\int_0^\infty u^rD(u)\,du\succeq0.
$$
两段积分的系数均为正，故正性来自同一份 $D(u)$。

归一化、收敛与端点如下。

令 $u=av$，再令 $z=v/(1+v)$，则
$$\int_0^\infty\frac{u^r}{(a+u)^3}du
=a^{r-2}\int_0^1 z^r(1-z)^{1-r}dz.$$
共同的范数积分为
$$
\begin{aligned}
\int_0^\infty\frac{u^r}{(a+u)^3}\,du
&=a^{r-2}B(r+1,2-r)\\
&=\frac{a^{r-2}}2\Gamma(r+1)\Gamma(2-r).
\end{aligned}
$$
其零点附近为 $O(u^r)$，无穷远为 $O(u^{r-3})$，故上述两段均可积。在 $0<r<1$，$\Gamma(r+1)\Gamma(2-r)=r(1-r)\pi/\sin(\pi r)$；在 $1<r<2$，写 $p=r-1$，该乘积为 $r(r-1)\pi/\sin(\pi(r-1))$。这里逐次使用 $\Gamma(z+1)=z\Gamma(z)$ 与 $\Gamma(p)\Gamma(1-p)=\pi/\sin\pi p$。乘以各自正弦系数并除以二，恰好得到
$$
\frac{r|r-1|}{2}a^{r-2}.
$$
端点单独计算，不将 $r=2$ 代入已发散的积分：
$$
FS^0F^*-A^0=0,\qquad
FSF^*-A=0,\qquad
FS^2F^*-A^2=\Delta.
$$
所以统一范数界为
$$
\boxed{
\|FS^rF^*-A^r\|
\le\frac{r|r-1|}{2}a^{r-2}\delta,
\qquad 0\le r\le2.
}
$$
此处不将分数幂序方向或此系数外推到 $r>2$；定理44.3的整数范数界仍独立成立。

**命题 44.8（下谱端点的固定指数尖锐性）。**

固定 $a<b$，取靠近下谱端点的二维模型
$$
S_\varepsilon=
\begin{pmatrix}
a+\varepsilon&\varepsilon\\
\varepsilon&a+\varepsilon
\end{pmatrix},\qquad
F=(1,0),\qquad 0<2\varepsilon<b-a.
$$
其谱为 $a,a+2\varepsilon$，并且
$$
A=a+\varepsilon,\qquad \delta=\varepsilon^2.
$$
对每个固定 $r\in(0,1)\cup(1,2)$，Taylor 展开给出
$$
\begin{aligned}
FS_\varepsilon^rF^*-A^r
&=\frac{a^r+(a+2\varepsilon)^r}{2}-(a+\varepsilon)^r\\
&=\frac{r(r-1)}2a^{r-2}\varepsilon^2+O(\varepsilon^3).
\end{aligned}
$$
因此绝对缺陷与所给上界之比趋于 $1$，任何严格较小的统一系数都不能覆盖该固定 $r$ 下的全部模型。$r=2$ 为精确等号，$r=0,1$ 两边均为零；不声称 $r$ 同时趋于端点时的一致相对尖锐性。若另有 $S\preceq bI_R$ 且 $a=b$，则 $S=aI_R$、$\delta=0$，没有非平凡尖锐性问题。

若还要求原模型中的 $b<1$，同一例子的
$$
C_\varepsilon=-h^{-1}\log S_\varepsilon>0
$$
满足原契约。定理44.3整数界的尖锐性使用上谱端点 $b$，本节因 $r<2$ 而使用下谱端点 $a$，二者不混用。

**推论 44.9（保留单步抵消的短时间响应）。**

回到 $S=e^{-hC}$、$G=-h^{-1}\log A$，令 $r=t/h$。谱演算给出
$$
FS^rF^*=Fe^{-tC}F^*,\qquad A^r=e^{-tG}.
$$
从而
$$
\boxed{
\|Fe^{-tC}F^*-e^{-tG}\|
\le\frac{\delta}{2}\frac th
\left|\frac th-1\right|a^{t/h-2},
\qquad 0\le t\le2h.
}
$$
并且具有随区间切换的 Loewner 序：
$$
Fe^{-tC}F^*\preceq e^{-tG}\quad(0\le t\le h),
$$
$$
e^{-tG}\preceq Fe^{-tC}F^*\quad(h\le t\le2h).
$$
在 $t=0,h$ 两响应相等；在 $t=2h$，响应差等于 $\Delta$，范数恰为 $\delta$。这保留定理44.6的全时间三角估计未体现的 $t=h$ 精确抵消，仍只是一条 $[0,2h]$ 上的加强界，不替代定理44.6的全时间结论。对每个固定 $t/h\in(0,1)\cup(1,2)$，命题44.8给出对应的渐近尖锐性。

还可核对小时间衔接：将本节估计除以 $t=rh$ 后令 $r\downarrow0$，利用
$$
\left.\frac{d}{dt}\bigl(Fe^{-tC}F^*-e^{-tG}\bigr)\right|_{t=0}
=G-C_c,
$$
恢复 $\|C_c-G\|\le\delta/(2ha^2)$。线性小时间项与单步时刻的精确抵消可以同时成立。

这里的连续参数由严格正算子的谱函数 $S^{t/h}$ 产生，并以正谱下界和积分估计控制误差；它不是形式幂级数按系数或理想过滤得到的完成化。两者的对象、收敛条件、拓扑和可操作含义不同，不凭共有的“幂”字样建立互换关系。

### 44.6 有限矩形 Jensen 的归属与算子序反例

分数幂的序方向属于成熟算子 Jensen 机制。对 $P=F^*F$ 令 $U_0=2P-I_R$，则 $U_0$ 自伴酉，$S_0=(S+U_0SU_0)/2$。Hansen–Pedersen，[*Jensen's Operator Inequality*](https://arxiv.org/abs/math/0204049v1)，Theorem 2.1(ii)，在正谱区间上以 $I_R/\sqrt2,U_0/\sqrt2$ 作 unital operator combination，给算子凸 $f$ 的
$$f(S_0)\preceq(f(S)+U_0f(S)U_0)/2.$$
$S_0$ 分块对角，函数演算的 $P$ 角是 $f(S_0|_{\operatorname{ran}P})$。$F$ 在该角上为等距同构、$FS_0F^*=A$，所以取角得到 $f(A)\preceq Ff(S)F^*$；凹函数方向反转。这里不向区间外补零，故不用 $f(0)$。该文 Corollary 2.3 的 contractive 版本另有零点属于区间及 $f(0)\le0$ 的假设；无限空间等距表述不能未经桥接便当作有限矩形 $F$ 的直接特例。上节的积分已经独立证明两段幂序及其定量常数。

Balakrishnan，[*Fractional powers of closed operators and the semigroups generated by them*](https://msp.org/pjm/1960/10-2/pjm-v10-n2-p03-s.pdf)，*Pacific J. Math.* 10(2) (1960), 419–437，[DOI 10.2140/pjm.1960.10.419](https://doi.org/10.2140/pjm.1960.10.419)，印刷页420式(2.1)、(2.3)给成熟 resolvent-power 构造。将其生成元变量取为 $-S$，则 $\|\lambda(\lambda I+S)^{-1}\|\le1$，有限维定义域为全空间。式(2.1)成为 $0<r<1$ 的表示，递推并乘以 $S$ 给 $1<r<2$；不移入该文更一般 Banach 生成元结论。显式常数所用 Euler Beta 积分、Gamma 递推与反射分别见 NIST DLMF [5.12.1](https://dlmf.nist.gov/5.12.E1)、[5.5.1](https://dlmf.nist.gov/5.5.E1)、[5.5.3](https://dlmf.nist.gov/5.5.E3)。

**命题 44.10（同一个三维来源中的两种算子序障碍）。** 取 $F=(I_2\ 0)$，
$$S=\begin{pmatrix}1/2&1/10&1/10\\1/10&1/2&0\\1/10&0&1/2\end{pmatrix},\qquad
A=\begin{pmatrix}1/2&1/10\\1/10&1/2\end{pmatrix},\qquad
v=\binom{1/10}{0},\quad d=1/2.$$
$S$ 的特征多项式为 $(\lambda-1/2)((\lambda-1/2)^2-1/50)$，谱是 $1/2,1/2\pm\sqrt2/10$，故为严格正收缩。分块乘法给 $\Delta=vv^*=\operatorname{diag}(1/100,0)$。对 $e_2\in\ker\Delta$ 和每个 $u\ge0$，
$$((A+uI)^{-1}e_2)_1=-\frac{1/10}{(u+1/2)^2-1/100}\ne0.$$
因此定理44.4的因子分解给
$$\langle e_2,D(u)e_2\rangle
=\langle e_3,(S+uI)^{-1}e_3\rangle
 |v^*(A+uI)^{-1}e_2|^2>0.$$
两段幂积分权重分别严格为正且可积，故每个固定 $r\in(0,1)\cup(1,2)$ 的正差在 $e_2$ 上严格正。$e_2^*\Delta e_2=0$，所以不存在有限标量 $c$ 使该差在 Loewner 序中不超过 $c\Delta$；标量范数界不受影响。

同一矩阵的三次幂角直接计算为
$$FS^3F^*-A^3=A\Delta+\Delta A+d\Delta
=\begin{pmatrix}3/200&1/1000\\1/1000&0\end{pmatrix},$$
其行列式为 $-1/1000000<0$。实对称二阶矩阵的特征值乘积负，故此差不定，证明 $r=3$ 已不保留上述正序；定理44.3的整数范数估计仍成立。证毕。

### 44.7 固定实际基准上的迹时钟与倍时诊断

**定理 44.11（维数消去的短区间比值界）。**

对 $0\le r\le2$，
$$
\boxed{
|R(r)-r|
\le\frac{r|r-1|}{2a^2\tau}\delta
\le\frac{r|r-1|}{2a^2(-\log b)}\delta.
}
$$
第一个界保留实际已校准的 $\tau$，比只使用 $-\log b$ 更精细。

证明。先对任意正定 $X,Y\succeq uI$、$u>0$，使用对数的 resolvent 积分及逆矩阵差恒等式：
$$
\begin{aligned}
\|\log X-\log Y\|
&\le\int_0^\infty
\|(Y+vI)^{-1}-(X+vI)^{-1}\|\,dv\\
&\le\|X-Y\|\int_0^\infty(u+v)^{-2}\,dv
=\frac{\|X-Y\|}{u}.
\end{aligned}
$$
这是算子范数估计，不只引用标量对数的 Lipschitz 常数。对每个 $r\ge0$，谱演算及余等距性给
$$
W(rh)=FS^rF^*\succeq a^rI,\qquad A^r\succeq a^rI.
$$
由于 $\log(A^r)=r\log A$，
$$
\begin{aligned}
|R(r)-r|
&=\frac{|\operatorname{tr}(\log W(rh)-\log A^r)|}{\mathcal T}\\
&\le\frac{m}{\mathcal T a^r}\|FS^rF^*-A^r\|\\
&\le\frac{r|r-1|}{2a^2\tau}\delta.
\end{aligned}
$$
最后一步使用第44.5节分数幂界，$a^r$ 与其 $a^{r-2}$ 相消；再以 $\tau\ge-\log b$ 得第二个界。维数通过 $\mathcal T=m\tau$ 精确消去。端点 $r=0,1,2$ 使用第44.5节的直接端点结论，不从发散积分取值。

符号由同一分数幂序及对数算子单调性给出：
$$
\boxed{
R(r)\ge r\quad(0<r<1),\qquad
R(r)\le r\quad(1<r\le2),
\qquad R(0)=0,\ R(1)=1.
}
$$
具体地，$FS^rF^*\preceq A^r$ 时 $-\log(FS^rF^*)\succeq-r\log A$；另一段反向。所有比较都固定同一个 $F_{(t_0)}$，不将不同基准或不同历史阶数的响应混入一次估计。

**推论 44.12（整数时间比值）。**

对每个整数 $n\ge2$，定理44.3的离散界给
$$
\boxed{
|R(n)-n|
\le\binom n2\frac{b^{n-2}}{a^n\tau}\delta
\le\binom n2\frac{b^{n-2}}{a^n(-\log b)}\delta.
}
$$
证明。$W(nh)$ 与 $A^n$ 都不小于 $a^nI$，故按第44.7节先取对数差、再取迹并除以 $\mathcal T$：
$$
|R(n)-n|
\le\frac{\|FS^nF^*-A^n\|}{a^n\tau}
\le\binom n2\frac{b^{n-2}}{a^n\tau}\delta.
$$
$n=0,1$ 精确成立。此处只延伸整数范数估计，不将第44.5节的 $r\le2$ 算子序声明外推到 $n>2$；也不把可能随 $n$ 增大的右端当作无时间范围的精确相对钟恢复。

**命题 44.13（精确倍时差及其饱和前提）。**

令 $W(2h)=A^2+\Delta$。有精确恒等式
$$
\boxed{
2-R(2)
=\frac{\log\det(I+A^{-1}\Delta A^{-1})}{\mathcal T}.
}
$$
证明。因
$$
A^2+\Delta=A(I+A^{-1}\Delta A^{-1})A,
$$
取行列式并用正定矩阵的 $\operatorname{tr}\log X=\log\det X$ 即得。合同增量 $A^{-1}\Delta A^{-1}$ 半正定，因此
$$
2-R(2)\ge0,\qquad R(2)=2\Longleftrightarrow\Delta=0.
$$
这就是 Context40 推论40.7的谱行列式机制在归一读数上的表达，不另宣称发现了该等号判据。

还有严格范围
$$
\boxed{0\le2-R(2)<1.}
$$
因为 $0<S<I$ 给 $S-S^2\succ0$；$F^*$ 单射，故 $A-W(2h)=F(S-S^2)F^*\succ0$。正定行列式严格单调于是给 $\operatorname{tr}(-\log W(2h))>\operatorname{tr}(-\log A)$，即 $R(2)>1$。结合 $R(2)\le2$ 得结论。

**一般余等距模型。** $\Delta=( (I-P)SF^*)^*((I-P)SF^*)$，所以 $\Delta=0$ 等价于 $\operatorname{Im}F^*$ 在自伴 $S$ 下约化。此时 $W(t)=A^{t/h}$，对全部 $t\ge0$ 有精确 $R(t/h)=t/h$。但一般模型允许未耦合隐藏直和，所以这不推出任意给定隐藏空间已被全部观察。

**Context40 的实际生成历史。** 此处不能停留在上一段较弱结论，更不能用它否定已发表的实际饱和定理。在定义40.1、引理40.2与命题40.6的完整前提下，工作空间已经取有效循环 $\mathcal R$，且
$$
\operatorname{Im}F_{(t_0)}^*=e^{-t_0C_{\mathcal R}/2}V_k
\supseteq e^{-t_0C_{\mathcal R}/2}B^*U.
$$
若 $\Delta=0$，约化性和唯一正对数使它在 $C_{\mathcal R}$ 下不变；这批移位输入的全部循环跨度为
$$
\operatorname{span}_{j\ge0}
C_{\mathcal R}^{j}e^{-t_0C_{\mathcal R}/2}B^*U
=e^{-t_0C_{\mathcal R}/2}\mathcal R=\mathcal R.
$$
最后使用有限基准指数的可逆性。故命题40.6已经供应
$$
\boxed{
\Delta=0\Longleftrightarrow V_k=\mathcal R
\Longleftrightarrow
\operatorname{rank}\mathsf H_{k+1}(t_0)
=\operatorname{rank}\mathsf H_k(t_0).
}
$$
结合前式，实际模型中 $R(2)=2$ 当且仅当该历史真正饱和；未饱和时 $R(2)<2$，与推论40.7完全一致。有效空间以外原本不可见的直和仍不参加这条饱和断言。把精确零改为很小的正数，只能得到本节有裕量条件的数值误差界，不保留精确秩或饱和结论。

**命题 44.14（二维时钟和通用系数尖锐性）。**

固定 $s\in(0,1)$，取
$$
S_\varepsilon=
\begin{pmatrix}s&\varepsilon\\\varepsilon&s\end{pmatrix},
\qquad F=(1,0),\qquad
0<\varepsilon<\min(s,1-s).
$$
则
$$
A=s,\qquad\delta=\varepsilon^2,\qquad
W(rh)=\frac{(s-\varepsilon)^r+(s+\varepsilon)^r}{2},
\qquad\tau=-\log s.
$$
对于每个固定 $r\in(0,1)\cup(1,2]$，对称 Taylor 展开给
$$
W(rh)=s^r+\frac{r(r-1)}2s^{r-2}\varepsilon^2+O(\varepsilon^4),
$$
从而
$$
\boxed{
R(r)-r
=-\frac{r(r-1)}{2s^2(-\log s)}\varepsilon^2
+O(\varepsilon^4).
}
$$
选取该模型的紧谱界 $a_\varepsilon=s-\varepsilon$、$b_\varepsilon=s+\varepsilon$，实际绝对误差与第44.7节两个上界之比均趋于 $1$。因此在允许任意合法谱界的通用公式中，前系数不能统一缩小。这里谱区间随 $\varepsilon$ 收紧；不宣称对每一组预先固定且分离的 $a<b$，粗常数 $1/(a^2(-\log b))$ 都最优，也不声称随 $r$ 变化的一致相对尖锐性。$r=0,1$ 两边恒为零。

取 $s=1/2,\varepsilon=1/20$，谱为 $9/20,11/20$，有
$$
\delta=\frac1{400},\qquad
2-R(2)=\frac{\log(101/100)}{\log2}\approx0.0143553.
$$
由共同谱界得到的上界为
$$
\frac{1/400}{(9/20)^2(-\log(11/20))}\approx0.0206506.
$$
这些是精确模型的代数读数及其数值显示，不是实际实验精度声明。

这组模型也满足实际历史合同的数学来源部分：取 $H=\mathbb R^2$、$U=\mathbb R$、$B=(1,0)$、$C=-h^{-1}\log S_\varepsilon>0$、$t_0=0$、$k=0$，则 $M_{(0)}=BB^*=1$、$F_{(0)}=B$。因 $\varepsilon\ne0$，$B^*$ 与 $S_\varepsilon B^*$ 线性无关，有效循环空间为二维，而阶零历史为一维，确实未饱和。合法实际取得仍需第44.11节的实验条件；给出数学来源不等于已取得该档案。

### 44.8 每一项独立裕量与耦合边界

**命题 44.15（弱耦合不提供秩阈值）。** 上述锐性模型中，每个 $\varepsilon>0$ 的 $F^*$-循环空间均为二维，极限为一维，而 $\delta\to0$。证明。在定理44.3的族中，$e_1,S_\varepsilon e_1$ 的行列式为 $\varepsilon\ne0$；当 $\varepsilon=0$ 则跨度为一。精确 $\delta=0$ 等价于 $P$ 约化 $S$；只有另有循环最小性时，才能推出观察空间等于整个相关内部空间。没有该条件，还能添加任意不耦合的隐藏直和。

**命题 44.16（缩放源的归一化与生成元缺口）。** 缺少共同正谱下界 $a>0$，绝对缺陷不能控制以下两项。 固定 $h>0$，取
$$
S_\varepsilon=\varepsilon\operatorname{diag}(1,2),
\quad F=2^{-1/2}(1,1),\quad0<\varepsilon<1/2.
$$
则
$$
A=3\varepsilon/2,\quad \delta=\varepsilon^2/4\to0,
\quad \frac{\Delta}{A^2}=\frac19,
\quad C_c-G=\frac{\log(9/8)}{2h}>0.
$$
每个实例仍有严格正谱下界，但随 $\varepsilon\downarrow0$ 不存在适用于整个模型族的共同 $a>0$。这是对上述两个具体目标的反例，不泛称排除了所有“归一化时钟”定义。

**命题 44.17（全时间一致性需要共同衰减）。** 缺少共同严格衰减界 $b<1$，不能由绝对缺陷趋零推出全时间一致收敛。 固定 $h>0$，取
$S_\varepsilon=\operatorname{diag}(e^{-\varepsilon},e^{-2\varepsilon})$，同一 $F$。虽然 $\delta\to0$，在 $t/h=1/\varepsilon$ 时，
$$
Fe^{-tC}F^*\to\tfrac12(e^{-1}+e^{-2}),
\qquad e^{-tG}\to e^{-3/2},
$$
二者差不趋零。每个实例都有 $b_\varepsilon=e^{-\varepsilon}<1$，但模型族没有共同 $b<1$，等价地没有共同的正生成元下界 $-h^{-1}\log b$。
在命题44.16中，$FS^2F^*=5\varepsilon^2/2$，减去 $A^2=9\varepsilon^2/4$ 得残差；$C_c=-h^{-1}(\log\varepsilon+\tfrac12\log2)$，$G=-h^{-1}\log(3\varepsilon/2)$，相减即得显示的常数。命题44.17中 $\delta=(e^{-\varepsilon}-e^{-2\varepsilon})^2/4\to0$，而 $\log((e^{-\varepsilon}+e^{-2\varepsilon})/2)=-3\varepsilon/2+O(\varepsilon^2)$，所以 $A^{1/\varepsilon}\to e^{-3/2}$。严格凸的标量指数使 $\tfrac12(e^{-1}+e^{-2})>e^{-3/2}$；这证明非零极限误差。

以下命题44.18和44.19的两个反例都取固定 $F=(1,0)$、$0<\varepsilon<1/4$，且 $\delta=\varepsilon/4\to0$。

**命题 44.18（源谱下界与大分母不能互换）。** 取
$$
S_\varepsilon=
\begin{pmatrix}
\varepsilon&\sqrt\varepsilon/2\\
\sqrt\varepsilon/2&1/2
\end{pmatrix}.
$$
矩阵对角元正、行列式为 $\varepsilon/4>0$，故 $S_\varepsilon>0$。而 $\frac34I-S_\varepsilon$ 的对角元正、行列式为 $3/16-\varepsilon/2>0$，故有共同上谱界 $S_\varepsilon<\frac34I$。另一方面 $\lambda_{\min}(S_\varepsilon)\le\langle e_0,S_\varepsilon e_0\rangle=\varepsilon$，不存在共同正的下谱界。

直接计算
$$
A=\varepsilon,\qquad W(2h)=\varepsilon^2+\varepsilon/4,
\qquad\mathcal T=\log(1/\varepsilon),
$$
$$
R(2)
=1+\frac{\log(1/(\varepsilon+1/4))}{\log(1/\varepsilon)}
\longrightarrow1.
$$
所以即使共同 $b<1$ 保留、校准分母还趋于无穷，$\delta\to0$ 也不保证钟偏差消失；倍时短缺趋于其可能范围的上端 $1$。

**命题 44.19（固定源谱下界不控制归一分母）。** 取
$$
S_\varepsilon=
\begin{pmatrix}
1-\varepsilon&\sqrt\varepsilon/2\\
\sqrt\varepsilon/2&1/2
\end{pmatrix}.
$$
$S_\varepsilon-\frac14I$ 的对角元正、行列式为 $3/16-\varepsilon/2>0$；$I-S_\varepsilon$ 的对角元正、行列式为 $\varepsilon/4>0$。所以
$$
\frac14I<S_\varepsilon<I.
$$
共同正谱下界保留，但由 $\lambda_{\max}(S_\varepsilon)\ge1-\varepsilon$，不存在共同 $b<1$。此时
$$
A=1-\varepsilon,\quad
W(2h)=(1-\varepsilon)^2+\varepsilon/4
=1-\tfrac74\varepsilon+\varepsilon^2,
$$
$$
\mathcal T=\tau=-\log(1-\varepsilon)\longrightarrow0,
\qquad
R(2)\longrightarrow\frac74.
$$
这里 $-\log W(2h)=\tfrac74\varepsilon+O(\varepsilon^2)$、$\mathcal T=\varepsilon+O(\varepsilon^2)$，故极限明确。小残差仍留下 $1/4$ 的归一倍时偏差。

这两个模型都可按第44.7节的二维模型取 $B=F,t_0=0,k=0,C=-h^{-1}\log S_\varepsilon$，得到非零耦合、二维有效循环空间中的实际未饱和来源。因此反例不依赖附加不可见直和，也不与 Context40 的精确饱和判据冲突。

准确边界是：共同 $b<1$ 可以由实际 $\tau$ 的共同正下界替代，但在不另加任何分母控制时没有该统一稳定保证；正谱下界也不能仅由小 $\delta$ 推出。这是允许来源族中的统一估计反例，不是已经构造了两个完整档案相同的世界。若 $C_{\rm archive}$ 中还有区分这些来源的外部记录或时间戳，必须保留；完整观察者的 minimax 不可识别结论需要另证共同档案与联合误差相容性。

**命题 44.20（固定压缩地板仍不认证真实源地板）。** 对 $F=(1,0)$ 和 $0<\varepsilon<1/4$，取
$$S_\varepsilon=\begin{pmatrix}1/2&\varepsilon\\\varepsilon&3\varepsilon^2\end{pmatrix}.$$
对角元正且 $\det S_\varepsilon=\varepsilon^2/2>0$；$3I/4-S_\varepsilon$ 的对角元正、行列式为 $3/16-7\varepsilon^2/4>0$。二阶 Sylvester 判据给 $0<S_\varepsilon<3I/4$。但 $A=1/2$ 固定、$\delta=\varepsilon^2$，且 Rayleigh 商给 $\lambda_{\min}(S_\varepsilon)\le3\varepsilon^2\to0$。$e_1,S_\varepsilon e_1$ 的行列式为 $\varepsilon$，非零耦合产生二维循环空间。以 $B=F,t_0=0,k=0,C=-h^{-1}\log S_\varepsilon$ 实现它，不需附加不可见块。故测得 $A$ 的固定正地板和小残差不能替代独立的有效 $S$ 下界。证毕。

### 44.9 同支撑、同联合事件上的测量证书

**命题 44.21（真实残差及正锚分母的确定性包络）。** 在已知实际非零支撑 $E$、$m=\dim E$ 上，令 $A=W(h)$、$W_2=W(2h)$。假设同支撑 Hermitian 估计在一个声明的联合误差事件上同时满足
$$\|\widetilde A-A\|\le e_1,\qquad\|\widetilde W_2-W_2\|\le e_2.$$
置
$$\widetilde\Delta=\widetilde W_2-\widetilde A^2,\quad
\widetilde\delta=\|\widetilde\Delta\|,\quad
q_\Delta=e_2+(2b+e_1)e_1.$$
则
$$\boxed{\max\{0,\widetilde\delta-q_\Delta\}\le\delta
\le\overline\delta:=\widetilde\delta+q_\Delta.}$$
证明。无交换性假设也有
$$A^2-\widetilde A^2=A(A-\widetilde A)+(A-\widetilde A)\widetilde A.$$
$\|A\|\le b$、$\|\widetilde A\|\le b+e_1$，故平方差范数至多 $(2b+e_1)e_1$。加 $W_2$ 的误差给 $\|\Delta-\widetilde\Delta\|\le q_\Delta$，再用范数反三角不等式及 $\delta\ge0$。不要求 $\widetilde\Delta$ 半正定。任何独立认证的 $\|A\|$ 上界可替换 $b$；实际正收缩允许安全值 $1$。它是依赖矩阵误差证书的真实残差上下界，不认证支撑或带噪饱和。

若 $\widetilde A>0$ 且有实际 Frobenius 对数误差
$$\|\log A-\log\widetilde A\|_F\le D_1,\qquad
\widetilde\tau=\operatorname{tr}(-\log\widetilde A)/m,$$
则 $|\operatorname{tr}X|=|\langle I,X\rangle_F|\le\sqrt m\|X\|_F$ 给
$$|\tau-\widetilde\tau|\le D_1/\sqrt m.$$
要求一个真实正下界 $\underline\tau>0$，例如正数 $\widetilde\tau-D_1/\sqrt m$；若独立认证共同 $b<1$，也可取
$$\underline\tau=\max\{-\log b,\widetilde\tau-D_1/\sqrt m\}>0.$$
计算测量比值还须另有 $\widetilde\tau>0$。配合独立实际有效源证书 $S\succeq\underline aI>0$，定义
$$\boxed{K_{\rm err}=\frac{\overline\delta}{2\underline a^2\underline\tau}.}$$
它控制定理44.11的真实系数 $\delta/(2\underline a^2\tau)$。$K_{\rm err}$ 不是源核 $K$ 或历史阶数 $k$。若无法取得这些正裕量，结论仍是未履行前提的条件结论，数值阈值不能补上证书。所有复用的基准误差属于同一联合事件，未假设独立。证毕。

**定理 44.22（允许零事件与高于单位估计的直接比值界）。** 独立声明真实 $r=t/h\in[0,2]$，令 $W=W(t)$、$\widetilde W$ 为同一实际支撑上的正估计。给实际误差
$$\|\log W-\log\widetilde W\|_F\le D_e,\qquad
\|\log A-\log\widetilde A\|_F\le D_1,$$
且 $\widetilde\tau>0$、$\tau\ge\underline\tau>0$。定义
$$N=\operatorname{tr}(-\log W),\quad
\widetilde N=\operatorname{tr}(-\log\widetilde W),\quad
q=\widetilde N/(m\widetilde\tau).$$
则
$$\boxed{|R(r)-q|\le\eta:=\frac{D_e+|q|D_1}{\sqrt m\,\underline\tau}.}$$
证明。直接相减而不预设事件的上谱界，
$$R(r)-q=\frac{N-\widetilde N}{m\tau}
 +\frac{\widetilde N(\widetilde\tau-\tau)}{m\tau\widetilde\tau}.$$
分别用 $|N-\widetilde N|\le\sqrt m D_e$ 和命题44.21的锚迹误差即得。若正的 $\widetilde W$ 有谱值大于一，$q$ 可以为负，故保留 $|q|$，证明仍成立。

实际正下界可以提供对数误差的一个有效选择。若 $W,\widetilde W\succeq u_eI>0$，逆差恒等式给
$$(\widetilde W+vI)^{-1}-(W+vI)^{-1}
=(\widetilde W+vI)^{-1}(W-\widetilde W)(W+vI)^{-1}.$$
用 $\|XYZ\|_F\le\|X\|\|Y\|_F\|Z\|$ 和对数积分，得到
$$\|\log W-\log\widetilde W\|_F
\le\|W-\widetilde W\|_F\int_0^\infty(u_e+v)^{-2}dv
=\|W-\widetilde W\|_F/u_e.$$
因此可选 $D_e=\|W-\widetilde W\|_F/u_e$；并非要求任一预先给定的误差上界 $D_e$ 反而小于这个值。锚矩阵有自己的正下界时同理供应 $D_1$。

$r=0$ 时 $W=I$，故上述证明覆盖零事件。若零事件块恰复用同一个实测基准及相同白化，则数学上 $\widetilde W=\widetilde M^{-1/2}\widetilde M\widetilde M^{-1/2}=I$、$q=0$；独立重复测量不继承该等式，数值计算的舍入若存在也须纳入误差。证毕。

本卷定理40.8仍是正事件统计量的一条供应途径，其实际假设包括同一非零支撑、基准 Gram 裕量和事件／锚共同的严格上界 $v<1$。零事件 $W=I$ 不满足后者，$r\downarrow0$ 时也没有共同严格事件上界。该供应的命名常数 $d_P=\delta_0/\gamma$ 不因实际支撑投影差为零而被改写为零。本节从已经合法给定的白化矩阵误差或对数误差出发；若改用原始白化误差，须履行定理40.8相应步骤的实际假设。不据此宣布新的原始数据、支撑、置信概率或样本保证。

### 44.10 严格单调、分支保持与有限事件区间

**定理 44.23（带测量误差的事件集合）。** 在同一实际 $F,S$ 下，对 $0\le r<s$，每个源特征值 $\lambda\in(0,1)$ 满足 $\lambda^r-\lambda^s>0$。故 $S^r-S^s\succ0$；$F^*$ 单射使 $W(rh)-W(sh)\succ0$。若 $X\succ Y\succ0$，$Y^{-1/2}XY^{-1/2}\succ I$ 的特征值全大于一，因而 $\det X>\det Y$。应用于这两个响应得到 $R(r)<R(s)$。所以 $R(0)=0,R(1)=1$ 和 $1<R(2)\le2$ 区分锚点两侧；单独的分数幂符号不足以得此严格分支信息。

使用命题44.21的 $K_{\rm err}$ 和定理44.22的 $q,\eta$，令
$$L=\max(0,q-\eta),\qquad U=\min(2,q+\eta).$$
若 $L>U$，测量与证书不能同时满足所声明合同。否则真实 $r$ 属于 $I_-\cup I_0\cup I_+$，其中空区间删除，且
$$I_-=
\begin{cases}
[\max(0,L-K_{\rm err}/4),\min(1,U)]\cap[0,1),&L<1,\\
\varnothing,&L\ge1,
\end{cases}$$
$$I_0=\begin{cases}\{1\},&L\le1\le U,\\\varnothing,&\text{否则},\end{cases}$$
$$I_+=
\begin{cases}
[\max(1,L),\min(2,U+2K_{\rm err})]\cap(1,2],&U>1,\\
\varnothing,&U\le1.
\end{cases}$$
证明。真实 $R(r)\in[0,2]\cap[q-\eta,q+\eta]=[L,U]$。在 $0\le r<1$，定理44.11给 $0\le R-r\le K_{\rm err}r(1-r)\le K_{\rm err}/4$，所以 $R-K_{\rm err}/4\le r\le R$；并且严格单调迫使 $R<1$，故必须 $L<1$。在 $1<r\le2$，$0\le r-R\le K_{\rm err}r(r-1)\le2K_{\rm err}$，于是 $R\le r\le R+2K_{\rm err}$，且 $R>1$ 迫使 $U>1$。与真实区间和对应严格分支相交恰给上述两项，$r=1$ 时 $R=1$ 给中项。

因此 $q+\eta<1$ 排除 $r\ge1$，$q-\eta>1$ 排除 $r\le1$。等号只给对应非严格侧，跨越一时保留并集。未反演可能非单调的二次包络，公式对每个 $K_{\rm err}\ge0$ 都有效。把集合乘以实际已校准的 $h$ 即包围 $t$；三角不等式及 $\max_{[0,2]}r|r-1|=2$ 还给
$$\boxed{|hq-t|\le h\eta+2hK_{\rm err}.}$$
源谱下界、固定真实支撑、$h$ 的校准和事件范围仍是独立前提，比值不能认证自己的范围或产生未观测事件。证毕。

### 44.11 实际取得、时间校准和完整观察者

**推论 44.24（同一接口的取得与时间误差）。** 若 $h$ 已有数值校准，并且事件的实际经过间隔已知属于 $0\le t\le2h$，定义
$$
\widehat t
=h\,\frac{\operatorname{tr}(-\log W(t))}{\operatorname{tr}(-\log W(h))}.
$$
则
$$
\boxed{
|\widehat t-t|
\le\frac{h\delta}{2a^2\tau}
\frac th\left|\frac th-1\right|
\le\frac{h\delta}{a^2\tau}.
}
$$
最后一步用 $\max_{0\le r\le2}r|r-1|=2$。若只有可重复的延迟单位而没有绝对校准，得到的是 $t/h$ 的误差界，不自动得到绝对物理单位。若已有共同有效谱下界证书 $a\ge\underline a>0$、真实校准量下界 $\tau\ge\underline\tau>0$ 与真实缺陷上界 $\delta\le\overline\delta$，可把统一界写成 $h\overline\delta/(\underline a^2\underline\tau)$；这些证书的实际取得仍是独立义务。

$W(t)$ 在此是实际事件块的白化响应；定义式中的未知 $t$ 描述该事件的真实间隔，并不要求先知道 $t$ 才能从已取得矩阵计算比值。然而，$[0,2h]$ 的范围条件和 $h$ 的实际加性校准不能由这个比值反向无条件认证。超过此区间、未知尾部、任意未知非线性钟函数或任意准备原点，不由本估计自动恢复。

Context40 命题40.17的矩阵取得计数保持不变。对阶 $k$，基准、一步和倍时三块
$$
\mathsf H_k(t_0),\quad\mathsf H_k(t_0+h),\quad\mathsf H_k(t_0+2h)
$$
需要实际前缀 $K(t_0+jh)$、$0\le j\le2k+2$，即 $2k+3$ 个不同时间的响应矩阵；它与下一 Gram 块的诊断没有取得优势。一般事件块 $\mathsf H_k(t_0+t)$ 还要求从该实际事件起至 $t_0+t+2kh$ 的 $2k+1$ 个响应矩阵，除非它们已经合法取得。分数幂公式不能将没有取得的非整数时刻响应直接当作已知数据。

取得的必须是同一实际核 $Be^{-tC}B^*$：指定输入方向、伴随准备、输出内积、来源与参考、共同年龄、增益和延迟一致。未知自由轨迹 $Be^{-tC}x_0$ 不自动供应这个完整核；重复准备、测量扰动及定时等价按 Context40 假设40.18另证。相同局部数字标签不保证真实加性延迟，$F_{(t_0)}$ 这个证明因子也不授权新的实际准备。

本节的误差是同一实际模型中压缩响应相对于幂半群的偏差，不是测量误差。$\delta$ 使用真实 $W(2h)-W(h)^2$ 或其已认证上界；真实 $\tau$ 可由精确基准及锚数据计算，而经验估计仍需真实正下界。不得把带噪矩阵的近零残差、拟合的一致性或阈值秩当成精确饱和。需要叠加数据误差时，Context40 定理40.8只在其同一实际支撑、Gram、对数及锚裕量条件下供应统计量稳定性；第40.6节要求所有重复条目保留同一个联合误差事件，不擅自宣布独立。支撑变化、置信概率和样本预算不由本节供应。

完整档案 $C_{\rm archive}$ 始终保留。固定 $t_0,k$ 的矩阵比值只是一个任务读数，不是整个观察者的新定义；档案扩展导致接口或历史阶数改变时，要另证跨接口运输。存储、输入方向、矩阵与标量读取、重复准备、等待、来源和校准认证、数值精度及计算成本仍分别计账。

### 44.12 固定供应者与推导的归属边界

本节项目引用均可在不可变提交 `a492391be5b09240e6be894c3e742a75a945feb1` 下按以下路径和声明编号定位；编号是主地址，行号只说明该快照的位置。表中的“恢复卷”是 [RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)，“主卷”是 [RECURSIVE_RELATIONAL_OBSERVATION.md](RECURSIVE_RELATIONAL_OBSERVATION.md)。这些供应各保留原有证明归属。

| 44.12供应 | 实际使用和不迁移的结论 |
|---|---|
| 44.12a `D5/S3/Observer/Approximation/IntertwiningDefectPropagation.lean`，`intertwining_defect_telescope`、`uniform_norm_intertwining_defect_le` | 一般交织展开及 $nb^{n-1}\sqrt\delta$ 单侧算子范数界；没有直接供应本节两次跨越的二次泄漏。 |
| 44.12b 本卷定义40.1、引理40.2，7183、7211；定理40.3、40.4，7240、7258 | 完整已获档案、实际有限实正伴随来源、Gram 因子化、共同支撑、有效循环空间和真实饱和后精确相对间隔；不以拟合存在认证来源。 |
| 44.12c 本卷命题40.6、推论40.7，7326、7375 | 移位投影、倍时残差平方、实际生成历史的零缺陷当且仅当饱和、严格迹对数诊断。一般余等距与实际循环模型的等号前提不同。 |
| 44.12d 恢复卷定理13.4，2340，式(13.10)及2370起证明 | 残差平方的精确代入：该供应历史阶数零，隐藏空间 $\mathcal R$，边界 $E_k$，$J=V=F_{(t_0)}^*$，Gram 为 $I$；不移入初态 minimax 或新准备许可。 |
| 44.12e 主卷定理137.13，52697、尤其52732任一实际实现证明 | 在阶数一、三个实际矩 $I,A,W(2h)$ 上，Schur 合同与真实平坦给不变性；抽象可行数组不是实际延迟历史。 |
| 44.12f 恢复卷命题10.6，1545 | 正自伴采样算子的唯一实自伴对数，及有限压缩前缀不等于整个算子的边界；用有效循环跨度接回饱和。 |
| 44.12g 主卷定理128.5在第128.4节的证明，48674、48691 | 半正定增量行列式为 $\prod_i(1+\lambda_i)$、等于一恰当增量零；不移入 Gaussian、熵或互信息解释。 |
| 44.12h 恢复卷11.1—11.4，1590起 | 既有 Krylov／多项式响应逼近及共同谱下的全时间保证；本节是指定压缩 $A=FSF^*$ 的残差消费者。 |
| 44.12i 恢复卷式(12.7)、定理12.3，1965起、2003及2048起对数步骤 | 双特征基函数差、生成元、Duhamel 与长期扰动；原界为 Frobenius 范数。本节算子范数对数界由 resolvent 另证。 |
| 44.12j 恢复卷定理12.4，2074 | 额外真实 Gram／投影裕量下的秩与正交对齐，不能由 $\delta$ 小替代。 |
| 44.12k 主卷命题137.15、137.17、137.18，52765、52802、52814 | 精确秩不连续、弱输入不足和无共同衰减的全时间障碍；本节反例各针对所显示的目标。 |
| 44.12l 本卷定理12.6，1441 | 连续交织 Duhamel 方法的量子通道／diamond 范数版本，不是本节算子范数结论。 |
| 44.12m 本卷定理40.8，7401；命题40.17、假设40.18、约定40.19，7653起 | 共同支撑及指定 Gram、对数和锚裕量下的正事件统计、实际矩阵计数、来源校准、共享联合误差与费用。本节直接比值证明另覆盖零事件。 |
| 44.12n 恢复卷第29节，5564起 | 给定初始化和速度条件下的静态 Schur 补轨迹比较；其生成元不是 $G=-h^{-1}\log(FSF^*)$。 |
| 44.12o [PROOF_TOPOLOGY_DIAGONAL_ESCAPE_THEORY.md](PROOF_TOPOLOGY_DIAGONAL_ESCAPE_THEORY.md)，PM6、PM7，2999、3030 | 形式级数响应／记忆反演和有限前缀运输；对象、拓扑及收敛条件不同，不供应谱分数幂。 |

`D5/S3/Observer/BlockStructure/UniformResolventRemainder.lean` 的 `inverse_control_of_lower_bound` 对有限指标实对称 $M\succeq cI,c>0$ 给可逆及真实 Euclidean 算子范数 $\|M^{-1}\|\le c^{-1}$；它不直接覆盖复压缩。`perturbed_lower_bound`、`inverse_bounds` 要求 $M\succeq2I$、实对称 $E$、$\|E\|\le1$，给 $M+E\succeq I$ 和两逆范数界。`remainder_bound` 在这些条件下给
$$\|M^{-1}EM^{-1}E(M+E)^{-1}\|\le\|E\|^2/4.$$
该五因子估计不包含余等距压缩、首阶消去、压缩余项正性或 Beta 常数。

Mathlib 使用 `lake-manifest.json` 钉定的 `db584cd6d46c92f209a44c0f1c829460d327499d`。路径 `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean` 的 `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁`（481）与 `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂`（525），分别在 $0<p<1$ 和 $1<p<2$ 的相应完备有序实非幺连续函数演算接口中，存在量化一个测度并给表示及可积性。公开陈述不直接给本节的正弦归一化，其内部由正标量积分的倒数构造常数。`Order.lean` 的 `CFC.concaveOn_rpow`（150）对 $p\in[0,1]$ 给有序 star-ordered C* 代数上凸组合的算子凹性，仍需有限矩形压缩桥和函数演算运输；该版本未提供 $(1,2)$ 段算子凸性声明，积分表示不冒充该声明。实 CFC 标量域也不自动解决具体实／复矩阵接口的全部实例条件。

本节把上述既有来源的适用关系与完整积分推导连接起来，供应者与例子的作用范围仅限所列数学条件；它们不扩大本节结论。其未解决范围包括实际源谱地板、真实共同支撑和精度的实验认证，变化接口的运输，带噪精确饱和、隐藏态恢复、完整档案上的 minimax 不可识别、置信概率和样本预算；这些都未由所列条件定理消除。未知非线性钟、无参考准备原点、未取得事件、无限时间精确时钟或物理时空身份也不由本节推出。

## 44.99 追加锚

## 45. 固定量子装置的来源判据、完成距离与有符号档案恢复

同一固定装置的完整第一层联合读数可以强制唯一线性来源候选，但它是否为正的归一密度、是否属于合法来源类，以及是否生成指定全部后续层，是必须履行的不同条件。本节把这些判据、任意目标的完成距离和同一相干档案的有符号恢复代价接在同一个观察者与实验合同上，分别处理精确见证、闭包逼近、达到的最小距离和实际估计。

### 45.1 固定装置、完整观察者与相容完成

令 $M=B=\mathbb C^2$，固定各自计算基、相位及装置
$$
\alpha=\frac{\sqrt5-1}{2},\qquad \alpha+\alpha^2=1,
$$
$$
m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,
\qquad m_1=|0\rangle,
\qquad T|j\rangle=|j\rangle\otimes m_j.
$$
这里 Q 指[量子上下文卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)，恢复卷指[边界恢复与原子代价几何](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)。装置及全输入等距由 Q130.1、Q131.1和本卷定义41.1供应：两基像的范数为一，输出基标签使它们正交，所以 $T^*T=I_M$。记
$$
H_n=B^{\otimes n},\quad H_0=\mathbb C,\quad
T_0=I_M,\quad T_{n+1}=(I_{H_n}\otimes T)T_n,
$$
$$
\Gamma_n(X)=\operatorname{Tr}_M(T_nXT_n^*),
\qquad\Gamma_0(X)=\operatorname{Tr}X.
$$
输出寄存器依次编号 $1,2,\ldots$，这是对 Q130 零下标词的索引平移。所有张量积依次排列为外部参考、已发出输出、活动记忆。

固定参考空间 $J$，$1\le\dim J<\infty$，并固定来源类
$$
\Theta\subseteq\mathcal D(J\otimes M),
$$
它在精确来源问题中可以为空、非闭、非紧或非凸；距离下确界、极小值与一致收敛分别在对应小节明列所需条件。合法准备、已取得的联合记录、参考关系及其他约束共同决定这一个 $\Theta$；不能在不同深度换来源类。一个 $\theta\in\Theta$ 承担整条输出历史。先在整个输入算子空间定义线性通道
$$
q_n(X)=(\operatorname{id}_J\otimes\Gamma_n)(X)
\quad\bigl(X\in\mathcal L(J\otimes M)\bigr),
\qquad q_0(X)=\operatorname{Tr}_M X,
$$
再将它限制到来源密度 $\theta\in\Theta$。
任意初态在 $J,M$ 之间可以纠缠，不预设独立根态。每一步必须使用与当时全部系统独立的纯空白 $|0\rangle\langle0|$ 及同一个 Q130 幺正装置，已发出端口不再参与生成；生成中不以反馈、重置或其它介入改变装置、空白准备或活动记忆。Q130 的基像恒等式在整个输入空间上成立，因而可张量上 $I_J$。有限维等距及偏迹给每个 $q_n$ 连续、CPTP，并且
$$
\operatorname{Tr}_{B_{n+1}}q_{n+1}(\theta)=q_n(\theta).
$$

一个待检目标是固定的相容密度族
$$
\xi_n\in\mathcal D(J\otimes H_n),\qquad
\operatorname{Tr}_{B_{n+1}}\xi_{n+1}=\xi_n\quad(n\ge0).
$$
它可以在装置的来源像以外。相容只保证这些有限密度属于同一个输出态，不保证该固定装置能产生它。所有层必须来自这一个目标；不能每次优化后换成不同的目标延拓。半迹距离统一记为
$$
D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1.
$$

用 $C_{\rm archive}$ 表示完整已获观察者档案。$J$ 只承载本有限量子模型明确表示的已保留参考与记录，不自动穷尽整个 $C_{\rm archive}$。来源类须保留实际准备、来源身份、装置和校准、旧内外记录、已知联合关系、时间戳、各局部钟读数及其共同约束、合法动作及顺序、失败、停止和误差合同。这些合同沿用本卷定义36.4、定义41.1与假设41.5；动作的合法先后不推出统计独立。当某项结论另外要求来源类非空且紧时，这两项是实质前提：例如一个非空紧允许参数集经过连续的实际联合准备映射，才由连续像保证这两点；严格不等式、精确秩条件或成功概率趋零的后选择未必给闭类。一个纯数学来源见证不自动授权实际准备；紧性也不供应操作成本。更大经典档案若需逐纤维讨论，必须另有同一实际联合 cq 模型、保留的共同档案律及可测正则条件核；本节不由有限 $J$ 推出任意无限量子参考结论。

**相容完成与紧来源像。**

置
$$
\mathcal A_n^J=\mathcal L(J\otimes H_n),\qquad
\iota_n(A)=A\otimes I_B,
\qquad
\mathcal A^J=\overline{\bigcup_n\mathcal A_n^J}^{\|\cdot\|}.
$$
有限左因子 $J$ 始终保留。每个嵌入为等距幺星同态，$\mathcal A^J$ 是 $\mathcal L(J)$ 与单侧 qubit UHF 代数的空间张量积。本卷定理41.4的式（41.34）、（41.40）—（41.42）已经在这座固定左因子塔上给出态延拓和局部／完成范数的证明，沿用 Q125.2与恢复卷命题31.9的方法。以下只核对该证明用于任意相容目标所需的前提；延拓与范数比较本身不使用目标具有实际来源见证，也不使用恢复尾界。

在局部代数上定义
$$
\xi(A)=\operatorname{Tr}(\xi_n A),\qquad
\omega_\theta(A)=\operatorname{Tr}(q_n(\theta)A)
\quad(A\in\mathcal A_n^J).
$$
偏迹相容使定义与所选层无关。局部正元取值非负，单位取值为一，且绝对值不超过 $\|A\|$。因此两者唯一连续延拓到 $\mathcal A^J$。若 $B_k$ 为局部元素且 $B_k\to B$，则 $B_k^*B_k\to B^*B$，在这些平方上取极限给延拓的正性；每个正元是其正平方根的平方。故延拓确实为态。以后同一个符号 $\xi$ 也表示这个完成态。

对完成态定义
$$
\mathsf d_\infty(\xi,\zeta)
=\frac12\|\xi-\zeta\|_{(\mathcal A^J)^*}.
$$
这是泛函范数的一半所定义的度量，不是在另行选择的无限 Hilbert 表示中断言存在全局迹类密度。Q125.4 的表示边界仍保留。

对任意两个相容态族，有限维迹／算子范数对偶及局部稠密性给
$$
\boxed{
\mathsf d_\infty(\xi,\zeta)
=\sup_{n\ge0}D(\xi_n,\zeta_n).
}
\tag{45.1}
$$
为核对从实际来源对到任意相容态对的适用条件，记 $\ell=\xi-\zeta$。在有限层，密度差是自伴矩阵 $X_n=\xi_n-\zeta_n$；由迹范数对偶，
$$
\|\ell|_{\mathcal A_n^J}\|=\|X_n\|_1=2D(\xi_n,\zeta_n).
$$
上界是 $|\operatorname{Tr}(X_nA)|\le\|X_n\|_1\|A\|$，等号可由 $X_n$ 的谱符号算子取得，零特征空间任取范数不超过一的值。所以整个泛函范数不小于这些限制范数的上确界。

反向，取完成代数中 $\|A\|\le1$，用局部 $B_k\to A$ 逼近，并置
$$
C_k=\frac{B_k}{\max(1,\|B_k\|)}.
$$
每个 $C_k$ 为局部单位球元素；由 $\|B_k\|\to\|A\|\le1$ 得 $C_k\to A$。因而
$$
|\ell(A)|=\lim_k|\ell(C_k)|
\le\sup_n\|\ell|_{\mathcal A_n^J}\|.
$$
对完成单位球取上确界得到另一方向，证明（45.1）。这里直接使用本卷定理41.4已有的局部单位球证明及恢复卷31.9的方法，保留因子二；上述检查说明证明所需的是相容密度和局部稠密性，不能只将其原陈述的实际来源量词改名。

有限维通道收缩还给
$$
D(q_n(\theta),q_n(\theta'))\le D(\theta,\theta').
$$
因此由（45.1），
$$
\boxed{
\mathsf d_\infty(\omega_\theta,\omega_{\theta'})
\le D(\theta,\theta').
}
\tag{45.2}
$$
上面的收缩推导不要求单射，也不使用恢复尾界。在本装置的实际来源对上，本卷式（41.35）还直接给出更精确的既有结论
$$
\boxed{\mathsf d_\infty(\omega_\theta,\omega_\vartheta)
=D(\theta,\vartheta)
\quad\bigl(\theta,\vartheta\in\mathcal D(J\otimes M)\bigr).}
\tag{45.3}
$$
这是实际来源像上的等距性，不把任意相容目标断言为来源输出。来源像记为
$$
\mathcal S_\Theta=\{\omega_\theta:\theta\in\Theta\}
$$
若 $\Theta$ 非空紧，则 $\mathcal S_\Theta$ 在完成距离中非空紧，特别地闭。这里由连续像即可得到紧性，式（45.3）还给精确等距识别；输出字母表有限本身不供应来源类的非空性或紧性。

全篇使用 $D=\|\rho-\sigma\|_1/2$、根保真度 $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$，以及完整 diamond 范数；半 diamond 距离另写为完整范数的一半。完整联合密度是数学输入律，或须另有误差合同的层析数据，不是一份单次测量结果。参数逆的矩阵读数、合法来源身份、可执行状态恢复及重复实验中的估计是不同任务。

档案恢复原子的类型固定为 $\mathcal L(H_n)\to\mathcal L(M)$，只作用于已发出且仍相干的档案，不读取惰性 $J$ 或最终活动记忆。若终端目标涉及 $J$，还须实际允许同一个联合测试；这不扩大解码器的访问类型。生成期反馈、独立空白、相干档案与额外记录均按上述完整合同判定，不能删除已记录的混合标签来改变来源问题。

### 45.2 一步线性逆与完整联合正像

本卷式（41.45）及 Q131.1供应一步全算子通道；恢复卷定义30.11、定理30.12供应一般相位阻尼逆。下面核对这个既有逆用于本装置、完整复算子和有限参考的条件。

首先以一般已知参数 $0<c\le1$ 写

$$
\mathcal D_c(X)=
\begin{pmatrix}X_{00}&cX_{01}\\cX_{10}&X_{11}\end{pmatrix}.
$$

本装置有 $\Gamma_1=\mathcal D_c$，其中 $c=\sqrt\alpha$。令

$$
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
a=\frac{1+c}{2c},\qquad b=\frac{1-c}{2c},
$$
$$
L_c=a\,\operatorname{id}-b\,\operatorname{Ad}_Z,
\qquad\operatorname{Ad}_Z(X)=ZXZ.
$$

因为 $a-b=1$、$a+b=c^{-1}$，$L_c$ 保持对角元并将非对角元除以 $c$。逐矩阵单位比较给

$$
L_c\mathcal D_c=\mathcal D_c L_c=\operatorname{id}_{\mathcal L(\mathbb C^2)}.
\tag{45.4}
$$

这是全部复算子上的等式，因而也可张量任意有限参考恒等映射。不仅是对角概率或某一个来源上的等式。

对全部 $Y\in\mathcal L(J\otimes\mathbb C^2)$，恒等与酉共轭保持迹范数，三角不等式给

$$
\|(\operatorname{id}_J\otimes L_c)(Y)\|_1
\le(a+b)\|Y\|_1=c^{-1}\|Y\|_1.
\tag{45.5}
$$

记 $\rho_\pm=|\pm\rangle\langle\pm|$。$L_c(\rho_+)$ 的矩阵为

$$
\frac12\begin{pmatrix}1&c^{-1}\\c^{-1}&1\end{pmatrix},
$$

特征值为 $(1\pm c^{-1})/2$，迹范数恰为 $c^{-1}$。它是计算线性算子范数的合法测试，不是声称 $\rho_+$ 已属于阻尼后的实际像。结合所有有限参考上的上界，得到完整范数

$$
\boxed{\|L_c\|_\diamond=c^{-1}.}
\tag{45.6}
$$

即使只比较真实像中的态对，该放大常数也不能改小：

$$
D(\mathcal D_c\rho_+,\mathcal D_c\rho_-)=c,
\qquad D(\rho_+,\rho_-)=1.
\tag{45.7}
$$

共同张量任意独立密度 $\tau_J$ 不改变这些迹范数。因此在任意固定有限参考类型中都可实现相同尖锐比值；若要实际开展这一尖锐性实验，仍需允许对应的共同相位准备。

这些公式直接应用恢复卷定义30.11、定理30.12 的逆表示。$c=1$ 为恒等；$c=0$ 丢失非对角方向而没有线性逆，不在结论范围内。

**含奇异块的联合像。** 以下对固定装置取 $c=\sqrt\alpha$，以 $L_c$ 作用于第一层。

给定 $\xi_1\in\mathcal D(J\otimes B)$，按 qubit 基将 $J\otimes B$ 识别为 $J\oplus J$。本小节的 $B_{01}$ 表示交叉块，与输出空间 $B$ 区分：

$$
\xi_1=
\begin{pmatrix}A&B_{01}\\B_{01}^*&D\end{pmatrix},
\qquad
\theta_{\rm cand}=(\operatorname{id}_J\otimes L_c)(\xi_1)
=\begin{pmatrix}A&B_{01}/c\\B_{01}^*/c&D\end{pmatrix}.
\tag{45.8}
$$

由 $\xi_1$ 为密度，$A,D\succeq0$、$\operatorname{Tr}(A+D)=1$。候选自动自伴、迹一，且其 $J$ 边缘仍为 $A+D$。由（45.4）与唯一性，

$$
\boxed{
\xi_1\in q_1[\mathcal D(J\otimes M)]
\iff\theta_{\rm cand}\succeq0.
}
\tag{45.9}
$$

令 $A^\dagger$ 为有限维 Moore–Penrose 逆：若 $A=\sum_{a>0}aP_a$ 是正特征值的谱分解，则 $A^\dagger=\sum_{a>0}a^{-1}P_a$，在 $\ker A$ 上为零；$AA^\dagger=\sum_{a>0}P_a$ 是 $\operatorname{ran}A$ 的正交投影，$A^{\dagger/2}=(A^\dagger)^{1/2}$。无需假设 $A$ 可逆，（45.9）的正性等价于

$$
\boxed{
(I-AA^\dagger)B_{01}=0,
\qquad D-c^{-2}B_{01}^*A^\dagger B_{01}\succeq0.
}
\tag{45.10}
$$

所用方法已有明确归属：恢复卷定理13.2、式（13.5）使用实空间中标量下块的奇异 Schur 补；定理15.4、式（15.10）—（15.11）处理有限实矩形块及奇异余量的收缩因子化；Q13.3的证明使用复矩阵中两对角块相同的情形，Q 第13.8节注明其一般方法来源。这里需要的是任意有限参考下、两个正对角块可不同且可奇异的复矩阵判据，不能将上述受限陈述只改名后直接使用。该一般因子化见 Watrous 的 Lemma 3.18，以及其完全有界范数论文 §2.1、Lemma 2；Moslehian、Kian、Xu 的 Theorem 5.11也给正算子块的收缩表述。[^rro_signedsource_blocks] 以下保留本像检验的范围条件、合同变换及正性证明，不另建一般块矩阵理论。

若候选正，对 $u\in\ker A$ 及任意 $v$，在向量 $(u,tv)$ 上的二次型是一个常数项为零的二次多项式。对任意小的正负实 $t$，并在需要时将 $u$ 乘相位，都要求非负，迫使 $u^*B_{01}v=0$。所以 $\operatorname{ran}B_{01}\subseteq\operatorname{ran}A$，即第一个条件。在此条件下有

$$
\theta_{\rm cand}=
\begin{pmatrix}I&0\\B_{01}^*A^\dagger/c&I\end{pmatrix}
\begin{pmatrix}A&0\\0&D-c^{-2}B_{01}^*A^\dagger B_{01}\end{pmatrix}
\begin{pmatrix}I&A^\dagger B_{01}/c\\0&I\end{pmatrix}.
\tag{45.11}
$$

两侧三角矩阵可逆且互为伴随，故候选正性等价于中间矩阵正性。这同时证明必要性与充分性，包括 $A=0$ 时必须 $B_{01}=0$ 的端点。

另一等价表达为

$$
B_{01}=cA^{1/2}KD^{1/2}
\quad\text{存在算子 }K\text{ 满足 }\|K\|\le1.
\tag{45.12}
$$

为从（45.10）得到它，置 $F=B_{01}/c$、$U=A^{\dagger/2}F$。有 $U^*U\preceq D$，从而 $U$ 消去 $\ker D$。取 $K=UD^{\dagger/2}$，则 $K^*K\preceq\operatorname{supp}D\preceq I$，且 $A^{1/2}KD^{1/2}=F$。反向若（45.12）成立，则

$$
\theta_{\rm cand}=
\begin{pmatrix}A^{1/2}&0\\0&D^{1/2}\end{pmatrix}
\begin{pmatrix}I&K\\K^*&I\end{pmatrix}
\begin{pmatrix}A^{1/2}&0\\0&D^{1/2}\end{pmatrix}\succeq0;
$$

中间矩阵正性由 $I-K^*K\succeq0$ 的普通 Schur 分解得到。

当 $J=\mathbb C$ 时，（45.10）等价于 $|B_{01}|^2\le c^2AD$；用 Bloch 向量就是恢复卷式（30.35）的实际椭球

$$
\frac{r_x^2+r_y^2}{c^2}+r_z^2\le1.
$$

具体地，标量情形 $A=(1+r_z)/2$、$D=(1-r_z)/2$、$B_{01}=(r_x-\mathrm i r_y)/2$，故 $|B_{01}|^2\le c^2AD$ 恰为所写椭球条件；逆候选的特征值是 $\bigl(1\pm\sqrt{(r_x^2+r_y^2)/c^2+r_z^2}\bigr)/2$。边界等号时候选秩一；$A=0$ 时条件迫使 $B_{01}=0,D=1$，所以极点也包含在内。

这些是完整联合态的条件。参考边缘和输出边缘各自合法，不足以推出联合候选正。例如 $J=\mathbb C^2$ 时取第一层目标
$$
\xi_1=|\Phi_+\rangle\langle\Phi_+|,
\qquad |\Phi_+\rangle=(|00\rangle+|11\rangle)/\sqrt2.
$$
它的两边缘均为 $I/2$。逆候选只在 $\operatorname{span}\{|00\rangle,|11\rangle\}$ 上非零，该块为 $\frac12\left(\begin{smallmatrix}1&c^{-1}\\c^{-1}&1\end{smallmatrix}\right)$，故当 $c<1$ 时有负特征值 $(1-c^{-1})/2$。这直接排除以分开边缘代替联合正性。正性只给数学状态成员资格，额外的已获档案、控制、实际准备、来源与费用限制仍须逐项检验。

### 45.3 精确共同来源、零下确界与闭包边界

固定任意子集 $\Theta\subseteq\mathcal D(J\otimes M)$，可非闭、非紧、非凸。它必须是同一实验合同下的合法来源联合态类。给定相容密度族

$$
\xi_n\in\mathcal D(J\otimes H_n),\qquad
\operatorname{Tr}_{B_{n+1}}\xi_{n+1}=\xi_n,
\quad n\ge0.
\tag{45.13}
$$

实际通道也满足同一前缀关系；本卷式（41.40）由固定等距直接证明这一点。第一层强制唯一候选 $\theta_{\rm cand}=(\operatorname{id}_J\otimes L_c)(\xi_1)$，即（45.8）；这里 $c=\sqrt\alpha$。于是

$$
\boxed{
\exists\theta\in\Theta\ \forall n\ge0,\ q_n(\theta)=\xi_n
\iff
\theta_{\rm cand}\in\Theta\ \land\ \forall n\ge1,\ q_n(\theta_{\rm cand})=\xi_n.
}
\tag{45.14}
$$

证明：左侧的第一层等式经一步逆给 $\theta=\theta_{\rm cand}$。右侧直接给共同见证；第零层由第一层取偏迹和目标相容性得到。

进一步，

$$
\boxed{
\bigl[\forall n\ge1\ \exists\theta_n\in\Theta:
q_n(\theta_n)=\xi_n\bigr]
\iff
\bigl[\exists\theta\in\Theta\ \forall n\ge0:
q_n(\theta)=\xi_n\bigr].
}
\tag{45.15}
$$

证明：将每份第 $n$ 层等式偏迹到第一层，得到 $q_1(\theta_n)=\xi_1$。$q_1$ 在全部算子上单射，所以每份见证都是 $\theta_{\rm cand}$。第一层的一份见证已经保证 $\theta_{\rm cand}\in\Theta$；任意一层的见证保证该层由它实现。这里不取子列、不用闭集交性质，也不需要紧性。反向使用同一个来源即可。若 $\Theta=\varnothing$，第 $1$ 层没有见证，（45.14）的两侧都为假；（45.15）的逐层条件及共同来源条件也都为假。因此这些精确存在等价式明确覆盖空来源类，不对空类宣称最小值。

在此装置中，精确逐层见证由第一层单射性强制成为共同见证，证明不需要紧性。第45.4节对任意目标的距离优化另以非空紧来源类作为充分条件；这既不把它添加到（45.15），也不声称每个特殊模型的达到性或共同半径结论都以紧性为逻辑必要条件。

唯一线性候选首先是一个自伴、迹一算子；只有确有合法来源时，它才是固定模型中唯一的来源密度。这不意味着微观世界或准备程序也唯一。不同合法程序可能产生同一联合密度；被模型之外的来源记录区分的程序不得因此合并。第一层也不供应对任意相容目标的有限深度完备证书：后续层仍可能偏离 $q_n(\theta_{\rm cand})$，必须有逐层验证或另一个覆盖全部层的实际结构证明。

**零下确界与闭包候选。**

现在令 $\Theta\ne\varnothing$，仍不假设闭或紧；以下下确界均在这个非空类上取值。以同一相容目标定义

$$
e_n=\inf_{\theta\in\Theta}D(q_n(\theta),\xi_n),\qquad n\ge1,
$$

闭包取有限维来源空间的迹范数拓扑。则

$$
\boxed{
\forall n\ge1,\ e_n=0
\iff
\theta_{\rm cand}\in\overline\Theta
\ \land\ \forall n\ge1,\ q_n(\theta_{\rm cand})=\xi_n.
}
\tag{45.16}
$$

证明：固定 $n$，取 $\theta_k\in\Theta$ 使该层距离趋零。逆在第一层上的等式、（45.5）及对自伴差的偏迹收缩给

$$
\frac12\|\theta_k-\theta_{\rm cand}\|_1
\le c^{-1}D(q_1(\theta_k),\xi_1)
\le c^{-1}D(q_n(\theta_k),\xi_n)\longrightarrow0.
\tag{45.17}
$$

即使尚未知道候选正，左侧的自伴差迹范数仍良定；取 $n=1$ 的逼近序列就证明候选是密度极限并属于 $\overline\Theta$。对任意固定 $n$，相同估计与通道连续性给 $q_n(\theta_{\rm cand})=\xi_n$。反向用 $\Theta$ 中趋于候选的序列及通道收缩，即得每层下确界为零。这个证明直接利用有界线性逆，不使用来源类的紧性。

明确反例取 $J=\mathbb C$，声明允许的来源类为

$$
\Theta=\{\theta\in\mathcal D_2:
\langle0|\theta|0\rangle>0\},
\qquad \theta_{\rm cand}=|1\rangle\langle1|,
\qquad \xi_n=\Gamma_n(\theta_{\rm cand}).
\tag{45.18}
$$

这是密度空间中的相对开、非闭类，候选不在其中。对 $0<\varepsilon<1$，

$$
\theta_\varepsilon
=\varepsilon|0\rangle\langle0|
 +(1-\varepsilon)|1\rangle\langle1|\in\Theta,
\qquad D(\theta_\varepsilon,\theta_{\rm cand})=\varepsilon.
$$

每层通道收缩给 $D(q_n(\theta_\varepsilon),\xi_n)\le\varepsilon$，故所有 $e_n=0$。若任何 $n\ge1$ 层有精确合法见证，偏迹到第一层和单射性便迫使该见证等于 $\theta_{\rm cand}$，矛盾。所以没有精确第一层见证，也没有共同合法来源。

本卷式（41.35）还给这两份实际来源的完成态距离等于来源距离，即

$$
\tfrac12\|\omega_{\theta_\varepsilon}-\omega_{\theta_{\rm cand}}\|
=\varepsilon.
$$

因此完成距离的下确界也为零而不达到。该用法只应用已有的实际来源对完成范数等式；没有断言任意相容目标自动属于实际来源像。可以共同张量固定参考态得到带参考的同类反例，但一般任务中的已知联合参考关系仍须保留。

空来源类的精确判据已由（45.14）—（45.15）处理；这里不为它定义实数值的 $e_n$ 或声称极小值。若另采用扩展实数距离约定，应取 $\inf\varnothing=+\infty$，不能把它当作零下确界情形。

### 45.4 紧来源类上的任意目标距离与共同半径

**非空紧来源类下的任意目标优化。** 本小节额外假设 $\Theta\ne\varnothing$ 且在来源迹范数中紧；不要求凸。此前精确见证与闭包结论不依赖这一新增假设。

本卷定理39.3的共同半径方法在此需要的是同一个紧量子来源类及其闭约束纤维。以下逐项核对这些条件，直接使用既有紧局部实现声明。

固定任意相容目标 $\xi$，它可以完全没有正的来源候选。记号 $\theta_{\rm cand}$ 始终只指第一层逆强制的算子；下文 $\theta_{\rm opt}$ 指优化所得的允许来源，两者不作等同。例如相容的全加乘积目标第一层为 $\rho_+$，其 $\theta_{\rm cand}$ 有负特征值 $(1-\alpha^{-1/2})/2$，已由本卷式（41.45）排除；对任何非空紧 $\Theta$，下述最近来源仍然存在。令
$$
f_n(\theta)=D(\xi_n,q_n(\theta)),\qquad
f(\theta)=\mathsf d_\infty(\xi,\omega_\theta)=\sup_n f_n(\theta).
$$
每个 $f_n$ 连续，且由于目标和来源的偏迹相容性，
$$
0\le f_n(\theta)\le f_{n+1}(\theta)\le1.
$$
紧性使有限最小值
$$
e_n(\xi)=\min_{\theta\in\Theta}f_n(\theta)
$$
存在并达到；这里的下确界已经达到，因而与第45.3节 $n\ge1$ 的 $e_n$ 记号一致；现在也包括 $n=0$。同一 $\Theta$ 上逐点单调性给 $e_n\le e_{n+1}$。

完成距离也达到，而且
$$
\boxed{
E(\xi):=\min_{\theta\in\Theta}f(\theta)
=\sup_{n\ge0}e_n(\xi),\qquad e_n(\xi)\uparrow E(\xi).
}
\tag{45.19}
$$
不能仅凭形式上的单调性交换 $\min$ 与 $\sup$；所需共同来源由以下紧子水平集证明供应。

置 $r=\sup_ne_n\in[0,1]$，在同一个来源空间中定义
$$
K_n(r)=\{\theta\in\Theta:f_n(\theta)\le r\}.
$$
各 $K_n(r)$ 是闭紧集；有限最小值达到且 $e_n\le r$，所以非空。$f_n\le f_{n+1}$ 给
$$
K_{n+1}(r)\subseteq K_n(r).
$$
任意非空有限组集合的交等于其中最高层的集合，故非空；空组的交为非空来源类 $\Theta$。紧性于是给同一个 $\theta_{\rm opt}\in\bigcap_nK_n(r)$。由（45.1），
$$
f(\theta_{\rm opt})\le r.
$$
反向，对任意 $\theta\in\Theta$ 和任意 $n$，
$$
f(\theta)\ge f_n(\theta)\ge e_n,
$$
从而 $f(\theta)\ge r$。因此 $f(\theta_{\rm opt})=r$，同时证明（45.19）和完成最小值的达到性。各层独立选择的最优输入不必相同；证明没有把它们当成同一历史。

上述紧步骤直接由 [CompactLocalRealization](../../../D5/S3/Observer/Completion/CompactLocalRealization.lean) 的 `D5.S3.Observer.Completion.CompactLocalRealization.compact_local_realization` 实例化，准确代入为
$$
X=\Theta,\quad\mathrm{Context}=\mathbb N,\quad\mathrm{Record}=\mathbb R,
$$
$$
\mathrm{beta}(n,\theta)=\max\{f_n(\theta)-r,0\},
\qquad\mathrm{target}(n)=0.
$$
在 $\Theta$ 的子空间拓扑上有紧空间结构；$\mathrm{beta}(n,\cdot)$ 连续，其目标纤维恰为 $K_n(r)$，因而闭。有限上下文集合非空时取最大层，在该层取满足 $f_n\le r$ 的来源，即同时满足全部有限约束；上下文为空时使用 $\Theta\ne\varnothing$。定理输出恰是 $\theta_{\rm opt}$。该既有声明不要求记录类型 `Record` 带拓扑；这里的实数拓扑只用于核对所写纤维闭性。使用共同实数记录，也避免把不同层矩阵塞入一个未声明的固定矩阵类型。

同一证明对任何固定 $r\ge0$ 给
$$
\boxed{
E(\xi)\le r
\Longleftrightarrow\forall n,\ e_n(\xi)\le r
\Longleftrightarrow\exists\theta\in\Theta\ \forall n,\ f_n(\theta)\le r.
}
\tag{45.20}
$$
正向可投影完成最小值的见证；反向按同一共同半径构造。$r>1$ 时也成立，但此时条件自动满足。

**严格阈值与精确成员身份。**

由（45.19）或（45.20），对任何固定 $r\ge0$，
$$
\boxed{E(\xi)>r\Longleftrightarrow\exists n,\ e_n(\xi)>r.}
\tag{45.21}
$$
若 $E>r$ 而所有 $e_n\le r$，则（45.20）矛盾；反向由 $e_n\le E$。所以完成距离严格越过阈值，必在某个有限窗口已严格越过同一阈值。

完成最小值达到还给
$$
\boxed{
\xi\in\mathcal S_\Theta
\Longleftrightarrow E(\xi)=0
\Longleftrightarrow\forall n,\ e_n(\xi)=0.
}
\tag{45.22}
$$
若 $E=0$，达到它的 $\theta_{\rm opt}$ 满足两个完成态范数差为零，故 $\xi=\omega_{\theta_{\rm opt}}$。因此非来源目标不仅在某层不能精确实现，而且有某层严格正的有限距离间隙：
$$
\boxed{\xi\notin\mathcal S_\Theta\Longleftrightarrow\exists n,\ e_n(\xi)>0.}
\tag{45.23}
$$
这是一条有限分离存在性结论。要把 $e_n>r$ 变成实际证书，必须能取得该层目标与装置读数、控制其误差，并认证整个来源类上的优化下界；数值优化器的一次输出或一份可行拟合不是这个下界。一般实数数据和抽象紧集不自动供应算法或可计算期限。

另一方面，单层 $e_n\le r$ 只给有限层候选，不能认证 $E\le r$；有限层 $e_n=0$ 也不能认证目标属于来源像。存在一份已证明精确产生全部目标的合法来源，当然给成员证书，但那是全目标关系及合法准备的额外证据。没有这种关系或尾证书时，成员身份和恰达阈值情形不由有限前缀自动终止。

**非凸来源类与共同观测量。** 上述“有限分离”指目标到整个来源像的严格正距离。$\Theta$ 不要求凸，所以这个结论不自动供应一个仿射观测量，在同一方向上将目标与所有来源严格分开。具体地，取平凡 $J$、$\rho_\pm=|\pm\rangle\langle\pm|$、$\Theta=\{\rho_+,\rho_-\}$，目标为 $\xi=\omega_{I_M/2}$。本卷式（41.45）给
$$
q_1(\rho_\pm)=\frac12
\begin{pmatrix}1&\pm\sqrt\alpha\\\pm\sqrt\alpha&1\end{pmatrix},
\qquad \xi_1=I_B/2,
\qquad e_1(\xi)=\frac{\sqrt\alpha}{2}>0.
$$
但线性性使 $\xi=(\omega_{\rho_+}+\omega_{\rho_-})/2$；任意自伴观测量的目标期望都是两个来源期望的平均，不能同时严格大于二者或同时严格小于二者。这个例子的来源类须由允许准备合同供应。第45.6节将另外构造一个确实对全部来源有效的共同投影；其存在由该例的支撑关系证明。

以上将非空紧性用作任意目标达到性及共同半径论证的充分条件。精确来源见证另有（45.14）—（45.15）的较强适用范围；非闭类的零下确界则只能按（45.16）判断闭包。不能由某个特殊类恰好达到最小值，反推该类必须紧，也不能以第一层线性候选取代最近来源优化。

### 45.5 固定目标与范数紧目标族的一致收敛

继续采用第45.4节的非空紧来源类 $\Theta$，并保留同一个目标及同一个来源合同。

对任意 $\theta,\theta'\in\Theta$，三角不等式和通道收缩给
$$
|f_n(\theta)-f_n(\theta')|
\le D(q_n(\theta),q_n(\theta'))
\le D(\theta,\theta').
$$
取上确界后仍有
$$
|f(\theta)-f(\theta')|\le D(\theta,\theta').
$$
故所有 $f_n$ 与 $f$ 都在来源距离上 $1$-Lipschitz；特别地，$f$ 连续。对于每个固定目标 $\xi$，
$$
\boxed{
\forall\varepsilon>0\ \exists N_{\xi,\varepsilon}\;
\forall n\ge N_{\xi,\varepsilon}\ \forall\theta\in\Theta,
\quad0\le f(\theta)-f_n(\theta)<\varepsilon.
}
\tag{45.24}
$$
有限网证明不需要另设一般极限定理。取 $\Theta$ 的有限 $\varepsilon/4$-网 $\theta_1,\ldots,\theta_s$。每个网点上 $f_n(\theta_i)\uparrow f(\theta_i)$，所以存在共同 $N$ 使全部网点缺口小于 $\varepsilon/2$。任意 $\theta$ 选择距离小于 $\varepsilon/4$ 的网点，由两次 Lipschitz 估计，
$$
f(\theta)-f_n(\theta)
\le2D(\theta,\theta_i)+f(\theta_i)-f_n(\theta_i)
<\varepsilon.
$$
单调性保证所有 $n\ge N$ 同时成立，证明（45.24）。也可将其识别为紧空间上连续单调收敛的 Dini 机制，但这里已完整给出所需有限网证明。

由此得到具体的候选输入保证。若 $n\ge N_{\xi,\varepsilon}$，且某个实际允许候选满足
$$
f_n(\widehat\theta_n)\le e_n(\xi)+\eta,\qquad\eta\ge0,
$$
则
$$
\boxed{
f(\widehat\theta_n)<e_n(\xi)+\eta+\varepsilon
\le E(\xi)+\eta+\varepsilon.
}
\tag{45.25}
$$
这是同一个候选初态 $\widehat\theta_n$ 产生整条历史后的保证，不是逐层选择多个来源再拼接。

（45.24）的 $N_{\xi,\varepsilon}$ 依赖固定目标及来源类。有限网中各点的收敛深度没有显式求出，不能将这个存在量冒称可取得速率或停止条件。仅从当前有限数据看见小缺口或平台，仍不能知道已超过该深度。

**非空完成范数紧目标族。**

固定同一个 $\Theta$。对任意相容目标 $\xi,\zeta$，有限层三角不等式给
$$
|e_n(\xi)-e_n(\zeta)|
\le D(\xi_n,\zeta_n)
\le\mathsf d_\infty(\xi,\zeta).
$$
例如，对所有 $\theta$ 有 $D(\xi_n,q_n\theta)\le D(\xi_n,\zeta_n)+D(\zeta_n,q_n\theta)$；取下确界，再交换 $\xi,\zeta$ 即得。完成距离到固定集合 $\mathcal S_\Theta$ 同样满足
$$
|E(\xi)-E(\zeta)|\le\mathsf d_\infty(\xi,\zeta).
$$
因此 $e_n$ 与 $E$ 都对目标完成距离 $1$-Lipschitz。

若目标族 $\Xi\ne\varnothing$ 在 $\mathsf d_\infty$ 下紧，则
$$
\boxed{
\sup_{\xi\in\Xi}\bigl(E(\xi)-e_n(\xi)\bigr)\longrightarrow0.
}
\tag{45.26}
$$
证明。取 $\Xi$ 的有限 $\varepsilon/4$-网 $\xi_1,\ldots,\xi_s$。由（45.19），各网点缺口趋零，选共同 $N$ 使网点缺口都小于 $\varepsilon/2$。任意目标与近网点之间，两次 Lipschitz 估计给
$$
E(\xi)-e_n(\xi)
\le2\mathsf d_\infty(\xi,\xi_i)+E(\xi_i)-e_n(\xi_i)
<\varepsilon\qquad(n\ge N).
$$
这证明额外目标紧性下的一致收敛，但未提供有效有限网或网点收敛期限，故仍不是自动可计算的尾速率。

这里要求的是完成泛函范数所给的紧性。即使来源类固定且紧，所有相容目标的集合也不因而完成范数紧。第45.6节给一个已经弱星紧、但仍完全没有一致尾收敛的明确目标族。

范数紧性是此处一致收敛的充分条件，不声称每一个一致收敛的目标族都必须范数紧。这两项有限网论证是既有紧性／Dini机制在所声明来源检验中的应用。

### 45.6 延迟相邻 11 与有限前缀的检测边界

沿用第45.4节的非空紧来源类；下面的算子支撑证明本身对全部输入算子成立。

Q130的全输入基像与 Q131的算子通道供应下面的支撑计算；Q126.2与恢复卷31.9供应支撑事件的距离方法。本卷命题39.12已有延迟前缀障碍的经典图景，这里核对固定量子装置及任意联合来源上的精确距离一反例。

**支撑约束覆盖全部未知联合初态。**

定义输出分支算子
$$
K_j=(\langle j|\otimes I_M)T=|m_j\rangle\langle j|.
$$
Q130 的基像给
$$
K_1=|0\rangle\langle1|,\qquad K_1^2=0.
$$
对词 $w=(w_1,\ldots,w_n)$，空词的算子乘积约定为 $I_M$，等距的顺序递推给
$$
(\langle w|\otimes I_M)T_n=K_{w_n}\cdots K_{w_1}.
$$
若 $w$ 包含相邻 $11$，右端包含相邻因子 $K_1K_1=0$，所以整个分支算子为零。令 $P_n^{\rm legal}$ 投影到不含相邻 $11$ 的词张成空间，$P_0^{\rm legal}=I_{H_0}$，则
$$
((I_{H_n}-P_n^{\rm legal})\otimes I_M)T_n=0.
$$
张量上 $I_J$ 后仍成立。令 $V_n=I_J\otimes T_n$、$Q_n=I_J\otimes P_n^{\rm legal}$，则 $(Q_n\otimes I_M)V_n=V_n$，取伴随也得对应右乘恒等式。因此对**每一个输入算子** $X\in\mathcal L(J\otimes M)$，无须正性或自伴性，都有
$$
V_nXV_n^*=(Q_n\otimes I_M)V_nXV_n^*(Q_n\otimes I_M).
$$
取活动记忆的偏迹并将 $Q_n$ 提出，得到
$$
\boxed{
q_n(X)=(I_J\otimes P_n^{\rm legal})q_n(X)(I_J\otimes P_n^{\rm legal})
\quad\forall X\in\mathcal L(J\otimes M).
}
$$
将上式限制到密度，便覆盖任意混合、相干、纠缠初态及任意有限 $J$，不局限于 Q130 的指定根态 $P_0$。它依赖同一固定等距及无改变生成规则的介入；允许重置或反馈后，不能继续无条件使用。

**固定一个目标，同时定义全部深度。**

固定 $\theta_0\in\Theta$。对每个预先固定的 $N\ge0$，一次定义完整目标族
$$
\xi_n^{(N)}=
\begin{cases}
q_n(\theta_0),&0\le n\le N,\\
q_N(\theta_0)\otimes|1\rangle\langle1|,&n=N+1,\\
q_N(\theta_0)\otimes|11\rangle\langle11|
\otimes|0^{n-N-2}\rangle\langle0^{n-N-2}|,&n\ge N+2.
\end{cases}
$$
$N=0$ 时前因子为 $q_0(\theta_0)=\operatorname{Tr}_M\theta_0$。所有因子正且归一；从深度 $N+1$ 到 $N$、从 $N+2$ 到 $N+1$，迹掉最后一个纯位分别返回前一层；从 $N+3$ 开始，迹掉最后一个纯零位也返回前一层。较早层用 $q_n$ 的相容性。因此这是一份同一目标的相容密度族，由第45.1节给完成态 $\xi^{(N)}$。

目标保留完整的 $J,H_N$ 联合前缀，并在其后接两个确定 $1$，再接零尾。对固定 $N$ 没有在检查不同深度时更换目标。它是完整输出代数上的合法态，但不是这个固定生成器的合法输出。

在第 $N+2$ 层取局部投影
$$
\Pi_N=I_{J\otimes H_N}\otimes|11\rangle\langle11|.
$$
有
$$
\operatorname{Tr}(\Pi_N\xi_{N+2}^{(N)})=1,
\qquad
\operatorname{Tr}(\Pi_Nq_{N+2}(\theta))=0
\quad\forall\theta\in\Theta.
$$
有限维效应变分界 $|\operatorname{Tr}(P(\rho-\sigma))|\le D(\rho,\sigma)$ 给距离至少一；态的迹距离至多一，故恰为一。更深层沿用同一局部投影并张量恒等，得到
$$
\boxed{
D(\xi_n^{(N)},q_n(\theta))=1
\quad(n\ge N+2,\ \theta\in\Theta).
}
\tag{45.27}
$$
完成层也可不借交换极限而直接认证：$2\Pi_N-I$ 为范数一的局部自伴算子，在两态上的期望相差二；两态泛函范数都为一，故差的范数恰为二。于是
$$
\boxed{
\mathsf d_\infty(\xi^{(N)},\omega_\theta)=1
\quad\forall\theta\in\Theta.
}
\tag{45.28}
$$
另一方面，在 $n\le N$ 时来源 $\theta_0$ 精确实现目标。因此
$$
\boxed{
e_n(\xi^{(N)})=0\ (n\le N),\qquad
e_n(\xi^{(N)})=1\ (n\ge N+2),\qquad
E(\xi^{(N)})=1.
}
\tag{45.29}
$$
不需要断言第 $N+1$ 层的最优距离是多少；可能更早发现额外约束，所证明的是任意给定前缀长度 $N$ 仍能完全匹配，而第 $N+2$ 层一定严格分离。

**没有全部相容目标共用的检测期限或消失尾界。**

固定有限 $n$，取任意 $N\ge n$，则（45.29）给 $E-e_n=1$。由于所有这些距离都在 $[0,1]$，
$$
\boxed{
\sup_{\xi\text{ 相容目标}}\bigl(E(\xi)-e_n(\xi)\bigr)=1
\quad\text{对每个有限 }n.
}
\tag{45.30}
$$
即使固定 $\Theta=\{\theta_0\}$ 这个紧单点来源类，反例仍成立。只读取统一有限前缀的规则，不能同时正确判定实际目标 $\omega_{\theta_0}$ 和具有相同此前缀的 $\xi^{(N)}$ 是否属于来源像。这里排除的是无额外承诺的统一有限前缀期限，不是计算理论不可判定命题；已给目标整体生成公式或另有尾部证书，属于不同访问条件。

这不与第45.4节冲突：每个固定的 $\xi^{(N)}$ 都在有限 $N+2$ 层被排除，不能对全部 $N$ 共用一个期限。

**弱星紧目标族仍失败，完成范数紧性才是第45.5节的前提。**

令
$$
\Xi_{\rm w}=\{\omega_{\theta_0}\}\cup\{\xi^{(N)}:N\ge0\}.
$$
对任意固定局部 $A\in\mathcal A_m^J$，只要 $N\ge m$，就有 $\xi^{(N)}(A)=\omega_{\theta_0}(A)$。对一般 $A\in\mathcal A^J$，取局部 $A'$ 满足 $\|A-A'\|<\varepsilon$，两态范数均为一，故足够大 $N$ 时
$$
|\xi^{(N)}(A)-\omega_{\theta_0}(A)|\le2\varepsilon.
$$
于是 $\xi^{(N)}\to\omega_{\theta_0}$ 弱星。“一个收敛序列及其极限”的集合紧：任意开覆盖中覆盖极限的开集覆盖所有充分晚的项，其余有限项各取一个覆盖集即可。因此 $\Xi_{\rm w}$ 弱星紧。

然而（45.29）给
$$
\sup_{\xi\in\Xi_{\rm w}}(E(\xi)-e_n(\xi))=1
\quad\text{对每个有限 }n.
$$
它并非完成距离紧。取偶数下标子序列；若 $M>N$ 且二者为偶数，则 $M\ge N+2$，较晚目标 $\xi^{(M)}$ 的前 $N+2$ 位仍等于实际 $q_{N+2}(\theta_0)$，而 $\xi^{(N)}$ 的同一窗口在 $\Pi_N$ 上概率为一。故
$$
\mathsf d_\infty(\xi^{(N)},\xi^{(M)})=1.
$$
无限个两两距离一的点不可能有有限小半径网，所以不全有界，更不紧。弱星紧性没有供应第45.5节需要的完成范数有限网。

### 45.7 实际来源定量尾与全档案有符号恢复成本

**实际来源承诺下的定量尾。** 本卷定理41.2、41.4已经针对同一装置及同一个有限参考证明：对任意 $\theta_0,\theta\in\mathcal D(J\otimes M)$，
$$
0\le D(\theta_0,\theta)-D(q_n(\theta_0),q_n(\theta))
\le\epsilon_n\qquad(n\ge1),
\qquad
\mathsf d_\infty(\omega_{\theta_0},\omega_\theta)=D(\theta_0,\theta).
\tag{45.31}
$$
其中 $\epsilon_n=1-c_n$ 是式（41.8）的完整 diamond 恢复误差，$c_n$ 是式（41.6）的条件记忆根保真度；两份来源分别恢复的半迹误差为 $\kappa_n=\epsilon_n/2$，二者相加才给（45.31）的 $\epsilon_n$。这些常数及共同解码器归定理41.2，式（41.33）、（41.35）供应这里的距离结论，不在此重新构造。其显式速率
$$
0<\epsilon_n\le\frac{\alpha^{4n-6}}4
\qquad(n\ge3)
$$
仍保留原起点。$n=0$ 只进入前缀相容、$q_0$ 与完成上确界，不为它定义恢复误差。

以下距离极小化应用仍假设 $\Theta$ 非空且紧。若整份目标已被认证为 $\xi=\omega_{\theta_0}$，即使 $\theta_0\notin\Theta$，式（41.35）、（41.37）直接给
$$
\boxed{
E(\xi)=\min_{\theta\in\Theta}D(\theta_0,\theta),
\qquad 0\le E(\xi)-e_n(\xi)\le\epsilon_n\quad(n\ge1).
}
\tag{45.32}
$$
具体的代入检查是：在同一个 $\Theta$ 上逐点应用（45.31），对 $e_n$ 的一个极小点 $\theta_{{\rm opt},n}$ 有
$$
E(\xi)\le D(\theta_0,\theta_{{\rm opt},n})
\le e_n(\xi)+\epsilon_n,
$$
而逐点收缩给 $e_n\le E$。对 $n\ge1$、$\eta\ge0$，一个实际取得且满足 $f_n(\widehat\theta_n)\le e_n+\eta$ 的允许来源，同样由式（41.38）得 $f(\widehat\theta_n)\le e_n+\eta+\epsilon_n$。这是既有实际来源定理的直接应用。

任意相容目标不自动具有供共同解码器回接的初态见证。第45.6节的 $\xi^{(N)}$ 不属于固定装置的来源像，不能代入（45.31）。第45.4节仍给 $e_n\uparrow E$，第45.5节给固定目标的来源一致近似，以及额外非空范数紧目标族上的一致收敛；这些结论都不继承一个对所有相容目标通用的 $\epsilon_n$。式（45.30）直接排除这种转移。任意目标的共同半径、有限网及延迟反例证明使用相容性、距离和明列的紧性条件；它们不从实际来源承诺继承一个任意目标尾界。

**全发射长度的有符号左逆及单位原子成本。** 以下是全来源算子空间上的共同恢复任务，与上段受限来源类 $\Theta$ 的距离极小化相互独立；不以该类的非空或紧性作为左逆前提。

本卷定理41.2、式（41.7）与（41.17）对每个整数 $n\ge1$ 供应一份仅依赖装置与 $n$、且对所有输入共同使用的解码器

$$
\mathcal D_n:\mathcal L(H_n)\longrightarrow\mathcal L(M)
\quad\text{为 CPTP},
$$
$$
\mathcal D_n\Gamma_n=\mathcal D_{c_n}
\quad\text{在全部来源算子上成立},
\qquad 0<c_n<1,
\qquad c_1=\sqrt\alpha,
\qquad c_n\longrightarrow1.
\tag{45.33}
$$

其构造仅在相干档案上作受控极分解酉再丢弃，不读取 $J$ 或最终活动 $M$。本卷式（41.17）拥有这个具体通道，不在这里重造。

为固定可计算参数，直接沿用本卷式（41.5）—（41.6）的条件记忆公式：
$$
\lambda=-\alpha^2,\quad
\pi_0=(1+\alpha^2)^{-1},\quad
\pi_1=\alpha^2(1+\alpha^2)^{-1},
$$
$$
a_n=\pi_1(1-\lambda^{n-1}),\qquad
b_n=\pi_1+\pi_0\lambda^{n-1},
$$
$$
c_n^2=1-\alpha^2
\left[\sqrt{a_n(1-b_n)}-\sqrt{b_n(1-a_n)}\right]^2
\qquad(n\ge1).
$$
这些条件态及 $c_n$ 的证明归本卷定理41.2；这里不另建恢复器或根保真度计算。该节同时证明

$$
D(\Gamma_n\rho_+,\Gamma_n\rho_-)=c_n,
\qquad
\epsilon_n=1-c_n
=\min_{\mathcal E\ {\rm CPTP}}
\|\mathcal E\Gamma_n-\operatorname{id}_M\|_\diamond.
\tag{45.34}
$$

竞争通道类型均为 $\mathcal L(H_n)\to\mathcal L(M)$。定义同一类型、全 CPTP 单位价格字典的有限实系数代价

$$
\gamma_n=
\inf\left\{
\sum_{i=1}^m|a_i|:\quad
\begin{array}{l}
m\in\mathbb N,\ a_i\in\mathbb R,\\
\mathcal E_i:\mathcal L(H_n)\to\mathcal L(M)\ {\rm CPTP},\\
\displaystyle\sum_{i=1}^m a_i\mathcal E_i\Gamma_n
=\operatorname{id}_M
\end{array}
\right\}.
\tag{45.35}
$$

等式要求全部来源算子；等价地可先在 Hermitian 实空间说明，再由复线性延拓。它自动保留任意有限惰性参考。原子是档案到来源类型的通道，不能误写成仅作用在来源 qubit 上的同型通道字典。

直接把恢复卷定理30.12的逆取 $\lambda=c_n$，与既有 $\mathcal D_n$ 复合，即 $\mathcal S_n=L_{c_n}\circ\mathcal D_n$，得到

$$
\mathcal S_n=
a_{+,n}\mathcal D_n+
a_{-,n}\operatorname{Ad}_Z\circ\mathcal D_n,
\qquad
a_{\pm,n}=\frac{1\pm c_n^{-1}}2.
\tag{45.36}
$$

这两个原子都为所需类型的 CPTP。由（45.33）与恢复卷的逆恒等式，$\mathcal S_n\Gamma_n=\operatorname{id}_M$，系数绝对值和为 $c_n^{-1}$。

恢复卷定理30.12的原字典是 qubit 到 qubit；这里的原子输入为整个 $H_n$，一般竞争者未必经 $\mathcal D_n$ 分解，故其成本下界仍须按此输入类型履行。为证明整个档案字典不能更便宜，对任意（45.35）的表示取 $\Delta=\rho_+-\rho_-$。同一档案差由（45.34）满足 $\|\Gamma_n(\Delta)\|_1=2c_n$。每个竞争通道对自伴差的迹范数收缩，所以

$$
2=\|\Delta\|_1
\le\sum_i|a_i|\,
\|\mathcal E_i\Gamma_n(\Delta)\|_1
\le2c_n\sum_i|a_i|.
\tag{45.37}
$$

因此极小值达到且

$$
\boxed{
\gamma_n=\frac1{c_n}=\frac1{1-\epsilon_n}.
}
\tag{45.38}
$$

对任意迹一来源输入取（45.35）的迹，得到 $\sum_i a_i=1$。若正、负系数质量为 $P_a,N_a$，则 $P_a-N_a=1$；在最优表示中 $P_a+N_a=\gamma_n$。所以每份最优表示均有

$$
\boxed{N_a=\frac{\gamma_n-1}{2}.}
\tag{45.39}
$$

不要求或宣称分解唯一。若受限可执行类包含（45.36）的两个通道，也达到这个值；否则全 CPTP 下界仍成立，但受限字典的可行性、代价和实现成本须重新检验。

作为同一计算的稳定性表达，

$$
\|\mathcal S_n\|_\diamond=c_n^{-1}.
\tag{45.40}
$$

上界来自两 CPTP 通道的完整 diamond 范数均为一；下界用迹范数归一化档案差 $\Gamma_n(\Delta)/(2c_n)$，其经 $\mathcal S_n$ 的像迹范数为 $1/c_n$。同一个归一化档案差也给任意线性精确左逆的 diamond 范数下界 $1/c_n$。因此真实来源对在任意有限参考下满足

$$
D(\theta,\vartheta)
\le c_n^{-1}D(q_n(\theta),q_n(\vartheta)),
\tag{45.41}
$$

且共同独立参考下的 $\pm$ 对达到等号。$n>1$ 时 $\mathcal S_n$ 是来源像上的左逆，不是整个高维档案算子空间上的双侧逆；任意档案目标经它所得候选正，也不能省去真实像一致性的检查。

由实际档案的前缀关系，对同一 $\rho_\pm$ 态对取偏迹并用收缩，式（45.34）给 $c_n\le c_{n+1}$，所以 $\gamma_n$ 不增。活动记忆的谱率 $-\alpha^2$ 可交替，不能据此推断档案代价交替。设 $\phi=(1+\sqrt5)/2=\alpha^{-1}$，则

$$
\gamma_1=\sqrt\phi,
\qquad\gamma_n>1\text{ 对每个有限 }n,
\qquad\gamma_n\longrightarrow1,
\qquad
\gamma_n-1=\frac{\epsilon_n}{1-\epsilon_n}.
\tag{45.42}
$$

本卷式（41.9）对 $n\ge3$ 的 $\epsilon_n\le\alpha^{4n-6}/4$ 可直接运输为

$$
0<\gamma_n-1
\le\frac{\alpha^{4n-6}}{4-\alpha^{4n-6}}.
\tag{45.43}
$$

这一步只是同一正分母上的单调代换，不是新的一般尾定理。单位原子价格不计算发射长度、档案相干存储、受控酉综合、校准或终端测量的真实成本。

所有有限 $n\ge1$ 的 $q_n$ 已因可偏迹到单射 $q_1$ 而单射。因此增长档案在这里改善的是逆的条件数、所需正负权重和最优物理恢复误差；不能写成“一步没有来源识别性，长记录才有”。这里的识别性以完整联合密度读数为对象，不以单个物理样本提供完整矩阵为前提。

这份单位价格逆成本属于已有有符号通道实现理论的具体装置应用。Jiang、Wang、Wang 的相位阻尼参数 $p$ 对应 $c=1-2p$，其 $2^{\nu}=1/c$ 是系数绝对值总量，$\nu$ 为它的二进制对数；在本装置取 $p=(1-c_n)/2=\kappa_n=\epsilon_n/2$，不能将文献的 $p$ 误作完整 diamond 误差。[^rro_signedsource_cost] 该文献的 qubit 逆成本与恢复卷30.12供应上式的两原子构造；（45.37）另外承担所有 $H_n\to M$ 竞争通道的下界。

### 45.8 正概率调用、独立试验与实际取得边界

恢复卷命题30.13供应一般抽样协议，本卷约定35.5供应带参考的实际输入、效果和访问条件。这里将（45.36）的两个实际可调用原子代入。

假设实验能按声明合同取得相同来源 $\theta$ 的新准备及其第 $n$ 层相干档案，能执行这两个原子，并能读取所需自伴终端可观测量 $O=O^*$，$\|O\|_\infty\le1$。若目标是联合关系，$O$ 必须是允许的同一联合参考测试；解码操作本身仍仅作用于档案。

用非负概率

$$
p_{+,n}=\frac{|a_{+,n}|}{\gamma_n}
=\frac{1+c_n}{2},\qquad
p_{-,n}=\frac{|a_{-,n}|}{\gamma_n}
=\frac{1-c_n}{2}
\tag{45.44}
$$

分别调用 $\mathcal D_n$ 与 $\operatorname{Ad}_Z\circ\mathcal D_n$。它们之和为一。分支抽样须独立于该次已准备的联合输入，或由实际条件合同保证各分支具有所声明的同一输入律。设实际测量结果 $Y\in[-1,1]$，条件期望等于指定同一输入和效果的原子预测。记录

$$
Z_{\rm est}=\begin{cases}
\gamma_nY,&+\text{ 分支},\\
-\gamma_nY,&-\text{ 分支}.
\end{cases}
\tag{45.45}
$$

全期望和（45.36）给

$$
\mathbb E Z_{\rm est}
=\operatorname{Tr}\!\left[
O(\operatorname{id}_J\otimes\mathcal S_n)q_n(\theta)
\right]
=\operatorname{Tr}(O\theta),
\qquad
\mathbb E Z_{\rm est}^2\le\gamma_n^2.
\tag{45.46}
$$

这里输出端 qubit 与来源 $M$ 按固定基识别。若另有 $N$ 次完整试验的独立重复合同，包含新的相同联合准备、相干档案生成、分支随机化及终端测量，并保持同一目标与完整已获档案条件，则

$$
\operatorname{Var}(\overline Z_N)\le\frac{\gamma_n^2}{N}.
\tag{45.47}
$$

这是因为每次的方差 $\operatorname{Var}(Z_{{\rm est},j})=\mathbb E Z_{{\rm est},j}^2-(\mathbb E Z_{{\rm est},j})^2\le\gamma_n^2$，独立性使不同试验的协方差为零，对均值求方差即得（45.47）。

完整独立性若只在某份保留档案条件下成立，上式先是相应的条件方差界；要无条件使用，还须核对共同准备、条件均值及额外随机性。一般地，
$$
\operatorname{Var}(\overline Z_N)
=\frac1{N^2}\left(
\sum_{j=1}^N\operatorname{Var}(Z_{{\rm est},j})
+2\sum_{i<j}\operatorname{Cov}(Z_{{\rm est},i},Z_{{\rm est},j})
\right).
$$
共同漂移、相关校准误差、复用同一量子系统或其它跨次关联不能被单次二阶矩界删除。该上界属于指定协议，不是任何估计器的最优方差或普遍样本下界，也不把旧样本重新读取当成新实验。

有符号估计没有制备负概率状态。一步逆在实际正像上得到合法来源密度，但 $c<1$ 时 $L_c(\rho_+)$ 有负特征值，所以 $L_c$ 不是全域正映射，更不是 CPTP。即使只要求某个 CPTP 映射在整个实际像上恢复，它也会将距离 $c$ 的输出态对变成距离一，违反收缩。对任意有限 $n$，同样由（45.34）的 $c_n<1$ 排除完整未知来源类的精确 CPTP 恢复。

必须保留下列任务区别：

* **已知完整矩阵律的反演**：由读数矩阵计算唯一候选、检查 PSD 与来源约束，再检验全部输出关系。
* **重复实验中的目标估计**：用实际允许的原子与终端测试，有符号后处理恢复期望；须计准备、样本、相关性及误差。
* **一个未知物理样本的状态恢复**：要求实际 CPTP 操作，受上述收缩和本卷定理41.2 的最优正误差限制。

同样，已知且与不可访问参考无额外纠缠要求的单例来源，可由允许的常值准备通道以成本一处理，对角子任务也可成本一；它们的量词不同于（45.35）的全来源共同算子恒等式。若单例为与不可访问参考纠缠的联合态，局部常值准备不能自动恢复该联合态，本卷命题41.6 已明确这一限制。对独立可准备的已知单例 $\tau_M$，上述档案原子具体为 $Y\mapsto\operatorname{Tr}(Y)\tau_M$；对计算基对角来源及其经典量子联合扩展 $\sum_j A_j\otimes|j\rangle\langle j|$，原子取先迹掉第 $2,\ldots,n$ 个输出、再对首输出作计算基去相干（$n=1$ 时无额外输出可迹掉）。第一层保持这两个对角块，故该 CPTP 原子精确恢复所述子任务。两类均有系数一的表示；任一可行表示在一个迹一输入上取迹又给 $\sum_i a_i=1$，从而质量至少一，证明其单位价格最优值确为一。

未知 $c$、改变原子价格、改变可调用字典、生成期间反馈、已经破坏相干的档案，均须重新指定任务。

上述正概率调用、带符号输出和 $\gamma_n^2$ 二阶矩机制也见 Temme、Bravyi、Gambetta 的概率误差抵消构造。[^rro_signedsource_sampling] 它给这里指定协议的可执行估计方式，不替代实际输入与参考合同，也不把（45.38）的最小表示成本提升成任意估计器的最优样本复杂度。

**实际来源检验的取得条件。** 这些结果用于同一固定装置、同一完整档案约束的来源类：有限目标矩阵给完成来源距离的单调下界，一个经过认证的严格有限下界能排除指定误差半径内的全部合法来源。对于非空紧来源类，数学最优来源存在，且每个固定非来源目标在某有限窗口严格分离；它不保证从当前数据有效计算该窗口。本卷命题39.13的证书边界在这里继续保留：可行拟合给 $e_n$ 的上界，排除整个来源类需要 $e_n$ 的已认证下界；数值优化器的一个输出不自动具有后者。存在一份已经证明精确产生全部目标的合法来源，可提供成员证书，但有限前缀精确匹配本身不提供它。恰达阈值也不自动有限停止。

相容目标可以是设计要求或待核验的候选输出规律。第45.6节接出的非法尾是完整输出代数中的比较态，不是已经由固定装置取得的事件，更不能通过改写旧档案伪造合法生成史。若整份已获档案规定了未来机制关系，违反它们恰是要检测的来源失败；不能删除这些关系，只留匹配的矩阵边缘来宣称世界相容。本卷命题41.6已经给出第一层可排除的非来源目标；这里增加的是任意相容目标的紧来源距离，以及保留任意长完整联合前缀后才显露的最大距离障碍，不把来源非满射本身重列为新结论。

所有来源候选共同解释第45.1节的 $C_{\rm archive}$，以及已保留的参考联合关系。固定分开边缘不自动保留联合态。数学态的可表达性不等于合法准备的可取得性；非空紧类与极小值存在不给优化算法、受限控制门集、读数精度、样本数、等待时间或存储预算。一般非凸类的正距离和共同观测量之间的区别按第45.4节保留；第45.6节的 $\Pi_N$ 才是经直接证明的共同支撑见证。

完成范数允许全部局部有界可观测量作为数学比较，实际可访问的测试族可以更小。$\Pi_N$ 仅需要两个指定输出端口的联合计算基事件，但读取它们仍须合法，并保留失败、来源身份、误差与顺序。若输出已经被不可逆测量，完整相干态检验及此前的相干恢复任务会改变；不能继续把原相干资源当作仍可访问。若允许生成中反馈、重置、复用已发出端口、改变装置或空白准备，来源像会改变，须按新合同重建约束，不能继续无条件沿用 $K_1^2=0$ 的旧生成器结论。

深度 $n$ 计数已发出的寄存器及所比较的前缀，不自动等于物理经过时间、半衰期或熵产生率。较大经典档案与无限量子参考的差别、纯数学见证与实际取得的差别，均按第45.1节及假设41.5保留。本文所用完成化、紧性、迹范数对偶和有限网机制保持既有归属；这里只给固定装置的目标来源检验、完成距离、有符号档案恢复及其估计协议的具体应用与反例。

[^rro_signedsource_blocks]: John Watrous，*The Theory of Quantum Information*，2018，[作者全文](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，Lemma 3.18，印刷页144—145：正半定复矩阵对角块允许奇异，正块矩阵等价于收缩因子化。另见 Watrous，[*Simpler semidefinite programs for completely bounded norms*](https://arxiv.org/html/1207.5726v2)，§2.1，Lemma 2；M. S. Moslehian、M. Kian、Q. Xu，[*Positivity of 2×2 block matrices of operators*](https://arxiv.org/html/1904.08680v1)，Theorem 5.11。这里的伪逆范围条件、合同变换与收缩因子化已逐项给出；正定内部块的 Schur 最小化声明不能替代奇异情形。

[^rro_signedsource_cost]: Jiaqing Jiang、Kun Wang、Xin Wang，[*Physical Implementability of Linear Maps and Its Application in Error Mitigation*](https://arxiv.org/html/2012.10959v2)，Theorem 3、Lemma 15及§4.1；*Quantum* **5**, 600（2021），[doi:10.22331/q-2021-12-07-600](https://doi.org/10.22331/q-2021-12-07-600)。其相位阻尼 $F_p=(1-p)\operatorname{id}+p\operatorname{Ad}_Z$、$0\le p<1/2$ 的逆满足 $2^{\nu(F_p^{-1})}=1/(1-2p)$；原子类型和任务仍须按第45.7节核对。

[^rro_signedsource_sampling]: Kristan Temme、Sergey Bravyi、Jay M. Gambetta，[*Error mitigation for short-depth quantum circuits*](https://arxiv.org/html/1612.02058v3)，式（9）—（10）的有符号重采样；*Physical Review Letters* **119**, 180509（2017），[doi:10.1103/PhysRevLett.119.180509](https://doi.org/10.1103/PhysRevLett.119.180509)。其特定电路与噪声条件不自动成为本装置的准备、参考访问或全竞争字典下界。

## 45.99 追加锚

## 46. 递归数组的幅度、数值恢复模量与统一量程条件数

本节接续第43节的同一递归体／边关系，在固定有限深度和通常数值范数下证明幅度极值、精确内外误差模量及恢复条件数。第43.2—43.5节供应多项式恢复、有限依赖和离散前缀几何；下文的数值完成使用另一种明确指定的拓扑。全部表示仍保留同源的完整已获档案，数值误差合同不增加合法获取能力。

### 46.1 同一个递归体／边映射，改用幅度度量

固定整数 $M\ge0$，记
$$
\Delta_M=\{(n,k)\in\mathbb N^2:n+k\le M\}.
$$
Context 定理43.2已经给出有理边界 $a=(a_0,\ldots,a_M)$ 的唯一递归三角 $\mathcal E_M(a)$，由整系数多项式构造，并与首列提取 $\beta_M$ 互逆。本节研究这些**同一坐标多项式**在通常数值扰动下的大小与敏感性；不重复取得已有自然数组的存在唯一性。

为避免覆盖 Context 式（43.10）中表示低阶余项的 $P_{n,k}$，用直立符号
$$
\mathsf P_{n,k}(a)=\mathcal E_M(a)(n,k)
\qquad(n+k\le M)
$$
表示整个坐标多项式。旧式（43.10）对应 $\mathsf P_{n,k}=a_{n+k}+P_{n,k}$，两者不是同一个多项式。有限依赖说明 $\mathsf P_{n,k}$ 只用 $a_0,\ldots,a_{n+k}$，与所选更大 $M$ 无关。其列递推为
$$
\mathsf P_{n,0}=a_n,\qquad
\mathsf P_{n,k+1}
=\mathsf P_{n+1,k}-\sum_{j=0}^{k}\mathsf P_{n,j}a_{k-j}.
\tag{46.1}
$$
所有等式都是有限多项式恒等式，故同样定义实边界上的 $\mathcal E_M$。在实数上继续用（46.1）列归纳，或者直接评价同一整系数恒等式，得到相同的递归约束及两逆恒等式。这里的实数评价不赋予形式变量任何解析值。

对 $A\ge0$，令
$$
K_M(A)=[-A,A]^{M+1},\qquad
I_M(A)=\mathcal E_M(K_M(A)).
\tag{46.2}
$$
边界和三角都采用通常坐标上确界范数：
$$
\|a-b\|_\infty=\max_{0\le i\le M}|a_i-b_i|,
\qquad
\|T-S\|_\infty=\max_{n+k\le M}|T(n,k)-S(n,k)|.
$$
这是固定有限维空间的数值距离，不是 Context43 的“首个不相等下标”超度量。来源可为有理点，也可为同一多项式的实扩张；对应范围将在每个达到性结论中说明。不加顶行全一、正性、概率或独立性假设。

### 46.2 非负系数列递推与一个共同的最坏边界

在同一组变量 $x_i$ 上定义
$$
Q_{n,k}(x)=-\mathsf P_{n,k}(-x).
$$
将（46.1）中的每个边界变量替换为 $-x_i$，逐项计算符号，得
$$
\boxed{
Q_{n,0}=x_n,\qquad
Q_{n,k+1}=Q_{n+1,k}+\sum_{j=0}^{k}Q_{n,j}x_{k-j}.
}
\tag{46.3}
$$
因此列归纳证明：每个 $Q_{n,k}$ 都是系数非负的整系数多项式，没有常数项，次数至多 $k+1$。归纳允许 $n=0$ 以及不同因子指向同一个变量的情形；相同单项式合并只会增加非负系数，不产生符号抵消。反过来，$\mathsf P_{n,k}$ 的每个非零、总次数为 $d$ 的系数具有符号 $(-1)^{d-1}$。

这个符号结论也与 Context 式（43.7）的有限系数公式一致。这里对边界取任意无限延伸，并令 $F(z)=1+z\sum_{i\ge0}a_i z^i$；每个待用系数只依赖所需有限前缀。形式展开
$$
F^{-(j+1)}
=\sum_{\ell\ge0}(-1)^\ell\binom{j+\ell}{\ell}(F-1)^\ell
$$
中，$F-1$ 的每项对边界变量为一次；再乘外侧 $a_{n+j}$ 后总次数为 $\ell+1$，符号正好为 $(-1)^\ell$。对一个固定形式次数只有有限项贡献。合并重复变量不会改变总次数，因此没有不同符号混入同一单项式。主证明仍是无需形式展开的正列递推（46.3）。

将全部相关变量同时取 $A\ge0$。由（46.3）归纳，$Q_{n,k}(A,\ldots,A)$ 与 $n$ 无关，记为 $u_k(A)$；它满足
$$
\boxed{
u_0(A)=A,\qquad
u_{k+1}(A)=u_k(A)+A\sum_{j=0}^{k}u_j(A).
}
\tag{46.4}
$$
这同时证明每个 $u_k$ 的系数非负，且 $u_{k+1}-u_k$ 系数非负。对 $A>0$，所有 $u_k(A)>0$，并且它们随 $k$ 严格增加。

对任意 $a\in K_M(A)$，非负系数给
$$
|\mathsf P_{n,k}(a)|
\le Q_{n,k}(|a_0|,\ldots,|a_{n+k}|)
\le Q_{n,k}(A,\ldots,A)=u_k(A).
\tag{46.5}
$$
而**同一个**边界 $a^-=-A\mathbf1$ 对全部坐标同时给出
$$
\boxed{
\mathsf P_{n,k}(a^-)=-u_k(A),\qquad
\max_{a\in K_M(A)}|\mathsf P_{n,k}(a)|=u_k(A),\qquad
\max_{a\in K_M(A)}\|\mathcal E_M(a)\|_\infty=u_M(A).
}
\tag{46.6}
$$
最后一个等号由 $k\le M$ 及坐标 $(0,M)$ 取得。这里没有把分别达到的最优值拼成一个不存在的共同实现：所有等号都来自这一个实际边界及其唯一递归三角。若实际来源类另有约束排除了这个边界，式（46.5）仍是上界，式（46.6）的达到性不能自动转移。

### 46.3 幅度多项式的公式与成熟归属

令形式级数 $U_A(z)=\sum_{k\ge0}u_k(A)z^k$。在（46.4）上乘 $z^{k+1}$ 求和；每个系数只含有限项，得到
$$
U_A-A=zU_A+\frac{Az}{1-z}U_A.
$$
因此
$$
\boxed{
U_A(z)=\frac{A(1-z)}{1-(A+2)z+z^2}
=\frac{A}{1-z}\sum_{\ell\ge0}
\left(\frac{Az}{(1-z)^2}\right)^\ell.
}
\tag{46.7}
$$
后一几何级数的公比有零常数项，故形式恒等式良定。取 $z^k$ 系数：第 $\ell$ 项为 $A^{\ell+1}z^\ell(1-z)^{-(2\ell+1)}$，只需 $0\le\ell\le k$，从而
$$
\boxed{
u_k(A)=\sum_{\ell=0}^{k}\binom{k+\ell}{2\ell}A^{\ell+1}.
}
\tag{46.8}
$$
特别地，各次数 $1,\ldots,k+1$ 的系数均严格正。$Q_{n,k}$ 的总次数为 $d$ 的系数总量，等于（46.8）中 $A^d$ 的系数 $\binom{k+d-1}{2d-2}$，与 $n$ 无关。

将（46.7）乘分母后逐系数比较，给
$$
\boxed{
u_0=A,\qquad u_1=A(A+1),\qquad
u_{k+2}=(A+2)u_{k+1}-u_k.
}
\tag{46.9}
$$
该二阶递推的减号不与（46.4）的非负系数构造矛盾；（46.4）负责系数正性，（46.9）是同一族的简短标量递推。

**Morgan–Voyce 与当前 Chebyshev 约定。** Swamy 原文第73页式（7）的小写 $b_n$ 族满足 $b_0(x)=1$、$b_1(x)=x+1$、$b_n(x)=(x+2)b_{n-1}(x)-b_{n-2}(x)$。[^rroctx46_arrayamp_swamy] 初值与（46.9）完全一致，因此多项式恒等式为
$$
\boxed{u_k(A)=A b_k(A).}
\tag{46.10}
$$
Swamy 印刷第79页式（40）还给出这一族的系数公式，其中
$$
\binom{n+j}{n-j}=\binom{n+j}{2j},
\qquad
b_n(x)=\sum_{j=0}^{n}\binom{n+j}{n-j}x^j
=\sum_{j=0}^{n}\binom{n+j}{2j}x^j.
$$
这与（46.8）在 $u_k(A)=A b_k(A)$ 下逐项对应；前面的形式生成函数取系数证明完整保留。Swamy 印刷第80页式（42b）给出的是较早的缩放 Chebyshev 表示，其归一化与下文 DLMF 当前约定须分别核对，不能直接将旧符号视为当前 $V/W$ 记号。

这个标量多项式族已有成熟归属；它自身不提供当前非线性边界恢复映射的最优幅度、Lipschitz 或有限噪声结论，那些结论由本节的共同非负系数结构证明。

按 DLMF 当前第三类 Chebyshev 记号，$V_0(x)=1$、$V_1(x)=2x-1$；这一点必须明确，因为 DLMF 在版本1.0.28（2020年9月15日）更正时交换了旧版的 $V,W$ 约定。[^rroctx46_arrayamp_dlmf] 令 $U_{-1}=0$，以相同的二阶递推及初值核对，得
$$
\boxed{
u_k(A)=A V_k(1+A/2)
=A\bigl(U_k(1+A/2)-U_{k-1}(1+A/2)\bigr).
}
\tag{46.11}
$$
DLMF18.12.10 给的是 $U_k$ 的生成式，不是直接给 $V_k$ 的生成式：在其形式恒等式上乘 $1-z$，才得到 $U_k-U_{k-1}$ 的生成式及（46.7）。同样，Context 第43.8节已归属的固定重建核 Riordan 系数法保持原作用域；随边界变化的整份恢复映射不能被当成固定线性核来求敏感性。本节不引入额外未核对的 Riordan 或条件数文献作为证明前提。

**闭式。** 对 $A>0$，置
$$
s(A)=\sqrt{A^2+4A},\qquad
\lambda(A)=\frac{A+2+s(A)}2>1.
$$
有 $\lambda+\lambda^{-1}=A+2$、$\lambda-\lambda^{-1}=s$。二阶递推（46.9）的两个根为 $\lambda,\lambda^{-1}$。直接代入两个初值并应用递推唯一性，得到
$$
\boxed{
u_k(A)=A\,\frac{\lambda^{k+1}+\lambda^{-k}}{\lambda+1}.
}
\tag{46.12}
$$
例如 $k=0$ 时为 $A$；$k=1$ 时 $(\lambda^2+\lambda^{-1})/(\lambda+1)=\lambda+\lambda^{-1}-1=A+1$。DLMF18.5.3的当前 $V_k$ 表达也给同一闭式，但本式已经由初值和递推验证。

（46.7）首先是形式系数恒等式，无解析收敛要求。若对固定 $A>0$ 将 $z$ 赋复数值，分母为 $(1-\lambda z)(1-\lambda^{-1}z)$，最近的极点为 $\lambda^{-1}$，而分子在该点不为零。因此该展开的解析收敛圆为 $|z|<\lambda^{-1}$；不能从正交区间 $[-1,1]$ 的默认条件直接移用其它半径。这里的 Chebyshev 参数为 $1+A/2>1$。$A=0$ 时 $u_k(0)=0$，整份 $U_0$ 为零，另按零多项式处理。

在 $A=1$ 时，令 $\phi=(1+\sqrt5)/2$，则 $\lambda=\phi^2$，且（46.9）的初值为 $1,2$、递推系数为 $3$，故 $u_k(1)=F_{2k+1}$，其中 $F_0=0,F_1=1$：Fibonacci 后继关系直接给 $F_{m+4}=3F_{m+2}-F_m$，所以奇数子列与（46.9）具有相同初值和递推。这只识别一个已有标量递推；达到幅度界的全负边界不是 Context43 中由顶行全一选出的自然源。

### 46.4 精确的立方体全局 Lipschitz 常数及逆向常数

先固定 $A>0$。记
$$
\boxed{
L_k(A)=u'_k(A)
=\sum_{\ell=0}^{k}(\ell+1)\binom{k+\ell}{2\ell}A^\ell.
}
\tag{46.13}
$$

**导数序列的形式生成函数。** 在评价实参数之前，将 $A$ 视为不定元，在 $\mathbb R[A][[z]]$ 中逐系数定义 $\partial_A$。（46.8）保证每个系数 $u_k(A)$ 都是多项式；每个 $z$ 系数的乘积只包含有限次卷积，故逐系数求导满足乘积法则。令
$$
D=1-(A+2)z+z^2.
$$
它的常数系数为一，因此存在唯一形式逆 $D^{-1}$，且该逆的每个系数仍属于 $\mathbb R[A]$。对 $DD^{-1}=1$ 使用乘积法则，结合 $\partial_A D=-z$，得到
$$
-zD^{-1}+D\,\partial_A(D^{-1})=0,
\qquad
\partial_A(D^{-1})=zD^{-2}.
$$
于是由（46.7）逐系数计算
$$
\partial_A U_A
=(1-z)D^{-1}+A(1-z)zD^{-2}
=\frac{(1-z)(D+Az)}{D^2},
\qquad
D+Az=1-2z+z^2=(1-z)^2.
$$
因此
$$
\boxed{
\sum_{k\ge0}u'_k(A)z^k
=\frac{(1-z)^3}{[1-(A+2)z+z^2]^2}.
}
\tag{46.13a}
$$
这是多项式系数环中的形式恒等式，对每个实 $A$ 的逐系数评价仍成立；证明不交换解析极限、无穷和或积分，也不需要解析收敛假设。$A=0$ 时导数序列各项为一，与下文单点域最小 Lipschitz 常数为零的区别仍保留。

在 $[-A,A]^{n+k+1}$ 内，由 $\mathsf P(a)=-Q(-a)$ 及 $Q$ 系数非负，对每个变量有
$$
|\partial_i\mathsf P_{n,k}(a)|
\le\partial_i Q_{n,k}(|a|)
\le\partial_i Q_{n,k}(A,\ldots,A).
$$
沿全对角方向求导，得
$$
\sum_{i=0}^{n+k}|\partial_i\mathsf P_{n,k}(a)|
\le\sum_i\partial_i Q_{n,k}(A,\ldots,A)
=u'_k(A)=L_k(A).
\tag{46.14}
$$
重复变量已经包含在偏导数的重数中。该行导数的 $\ell^\infty$ 输入到标量输出范数正是偏导绝对值之和。

对立方体内任意 $a,b$，线段 $a+t(b-a)$ 留在同一凸立方体内。沿线段积分梯度并用（46.14），给
$$
|\mathsf P_{n,k}(a)-\mathsf P_{n,k}(b)|
\le L_k(A)\|a-b\|_\infty.
\tag{46.15}
$$
这一步在实立方体证明，再限制到有理点；不需要声称有理点本身对实参数线段闭合。

证明常数不能缩小，使用同一对共同边界
$$
a=-A\mathbf1,\qquad b=-(A-h)\mathbf1,
\qquad 0<h\le A.
$$
由（46.6），其输入距离为 $h$，输出坐标差为 $u_k(A)-u_k(A-h)$。所以
$$
\frac{|\mathsf P_{n,k}(a)-\mathsf P_{n,k}(b)|}{\|a-b\|_\infty}
=\frac{u_k(A)-u_k(A-h)}h
\longrightarrow u'_k(A)
\quad(h\downarrow0).
\tag{46.16}
$$
结合上下界，$L_k(A)$ 恰为该坐标映射在完整立方体上的最小非负 Lipschitz 常数。

从（46.4）求导可见
$$
L_{k+1}-L_k=\sum_{j=0}^{k}u_j+A\sum_{j=0}^{k}L_j
$$
系数非负；因此 $k\le M$ 时 $L_k(A)\le L_M(A)$。对全三角取坐标最大值，再用（46.16）的 $(0,M)$ 坐标给最优下界，得到
$$
\boxed{
\|a-b\|_\infty
\le\|\mathcal E_M(a)-\mathcal E_M(b)\|_\infty
\le L_M(A)\|a-b\|_\infty,
\qquad a,b\in K_M(A).
}
\tag{46.17}
$$
右边的最小常数为 $L_M(A)$。左边因为边界坐标就是三角坐标的一部分，故首列提取在像 $I_M(A)$ 上为 $1$-Lipschitz。

其逆向常数 $1$ 同样最优。比较零边界与 $t e_M$，其中 $0<|t|\le A$。Context 式（43.10）的反对角首项或（46.1）表明：前 $M$ 个反对角层均为零，最后一层 $n+k=M$ 全为 $t$。所以两边界距离和两三角距离都等于 $|t|$。此例对 $M=0$ 仍成立。

**端点与达到方式。** 对 $A>0$，$k=0$ 的坐标是 $a_n$，故最优常数为 $1$，有不同输入对达到；$M=0$ 的全三角就是恒等映射，正逆最优常数均为 $1$。对 $A=0$，边界域和三角像各为零单点，最小非负正逆 Lipschitz 常数均为 $0$。多项式导数 $u'_k(0)=1$ 不是该单点域的最优常数，它描述放开域后在原点附近的变化。

对 $A>0$、$k\ge1$，$L_k(A)$ 是割线比值的上确界，没有不同输入对达到它；全三角在 $M\ge1$ 时同样如此。这个严格性将在下一节用精确有限误差模量证明，不能只从一族角点割线不取等号便推出所有输入对不取等号。

### 46.5 两个输入都留在幅度立方体时的精确模量

本小节假设 $A>0$，且 $0\le h\le A$。两份输入都必须留在同一个 $K_M(A)$。先给控制每个单项式所需的完整乘积引理。

**乘积引理。** 对任意 $d\ge1$，若 $r_i,s_i\in[-A,A]$ 且 $|r_i-s_i|\le h$，则
$$
\boxed{
\left|\prod_{i=1}^{d}r_i-\prod_{i=1}^{d}s_i\right|
\le A^d-(A-h)^d.
}
\tag{46.18}
$$
证明。$h=0$ 时两列逐项相同。一般地先考虑两个非零乘积异号。至少有一对因子 $r_j,s_j$ 异号，因此 $|r_j|+|s_j|=|r_j-s_j|\le h$。余下因子绝对值至多 $A$，故
$$
\left|\prod r_i-\prod s_i\right|
=\left|\prod r_i\right|+\left|\prod s_i\right|
\le hA^{d-1}
\le A^d-(A-h)^d.
$$
最后一步由
$$
A^d-(A-h)^d
=h\sum_{j=0}^{d-1}A^{d-1-j}(A-h)^j
\ge hA^{d-1}
$$
得到，且 $d=1$ 时成立。

其余情况两个乘积同号或至少一个为零。置 $p_i=|r_i|,q_i=|s_i|$，交换两列后可令 $\prod p_i\ge\prod q_i$。绝对值的反三角不等式给 $|p_i-q_i|\le h$，所以 $q_i\ge(p_i-h)_+$。于是
$$
\left|\prod r_i-\prod s_i\right|
=\prod p_i-\prod q_i
\le\prod p_i-\prod(p_i-h)_+.
$$
右侧在 $[0,A]^d$ 上逐坐标不减。为完整核对，固定其余坐标，置
$$
P=\prod_{i\ne j}p_i,\qquad Q=\prod_{i\ne j}(p_i-h)_+,
\qquad 0\le Q\le P.
$$
该坐标为 $t$ 时的函数是 $tP-(t-h)_+Q$；在 $t\le h$ 时斜率为 $P$，在 $t\ge h$ 时斜率为 $P-Q$，两段均非负且在接点连续。因此最大值在全部 $p_i=A$ 时取得，等于 $A^d-(A-h)^d$。两种情形穷尽，证明引理。空的其余乘积取一，故 $d=1$ 的证明亦完整。$\square$

定义单坐标和全三角的同立方体模量
$$
\omega_{n,k,A}(h)
=\sup_{\substack{a,b\in[-A,A]^{n+k+1}\\\|a-b\|_\infty\le h}}
|\mathsf P_{n,k}(a)-\mathsf P_{n,k}(b)|,
$$
$$
\omega_{M,A}(h)
=\sup_{\substack{a,b\in K_M(A)\\\|a-b\|_\infty\le h}}
\|\mathcal E_M(a)-\mathcal E_M(b)\|_\infty.
$$
则有精确公式
$$
\boxed{
\omega_{n,k,A}(h)=u_k(A)-u_k(A-h),\qquad
\omega_{M,A}(h)=u_M(A)-u_M(A-h),
\quad 0\le h\le A.
}
\tag{46.19}
$$
证明。对 $\mathsf P_{n,k}$ 的每个次数 $d$ 单项式应用（46.18）。同一变量可以在乘积中重复出现：引理对每个出现的因子成立，没有要求这些因子是独立变量，更没有概率独立性。总次数为 $d$ 的系数绝对值之和正是 $u_k$ 的 $A^d$ 系数。逐单项式三角不等式于是给上界 $u_k(A)-u_k(A-h)$。

在同一共同角点对 $a=-A\mathbf1,b=-(A-h)\mathbf1$ 上，每个坐标的两个值分别是 $-u_k(A),-u_k(A-h)$，故上界达到。由于 $u_M-u_k$ 系数非负，且 $A\ge A-h\ge0$，有
$$
u_k(A)-u_k(A-h)\le u_M(A)-u_M(A-h)
\qquad(k\le M).
$$
取坐标 $(0,M)$ 即得全三角公式；同一输入对使各坐标各自的界同时达到。$h=0$ 时模量为零。$h=A$ 的角点内侧为零边界，公式仍精确。本结果未给出 $A<h\le2A$ 的全部模量，不能无条件把（46.19）外推到那里。

**最优 Lipschitz 常数没有非平凡有限割线达到。** 对 $k\ge1$，由（46.8）的 $A^2$ 项严格正，$u''_k(t)>0$ 对所有 $t\ge0$ 成立。因此对每个 $0<h\le A$，
$$
u_k(A)-u_k(A-h)=\int_{A-h}^A u'_k(t)\,dt<h u'_k(A).
\tag{46.20}
$$
任取立方体内不同的 $a,b$，其距离 $d=\|a-b\|_\infty$ 满足 $0<d\le2A$。以中点把线段分为两半，每半的距离 $d/2\le A$。对两半应用（46.19）和（46.20），再用三角不等式，得到
$$
|\mathsf P_{n,k}(a)-\mathsf P_{n,k}(b)|
<dL_k(A).
$$
对全三角直接用 $u_M$ 的模量重复该证明，得 $M\ge1$ 时任意不同输入对均严格小于 $dL_M(A)$。因此（46.16）给的是逼近最优值的割线序列，而非一份非零距离最优对。线性端点 $k=0$、$M=0$ 不受这个严格凸性结论约束。

### 46.6 真值在立方体内、近似值允许越界时的精确噪声包络

本节的域不同于上一节。固定 $A\ge0$、$\eta\ge0$；只要求真实边界 $a\in K_M(A)$，近似输入为 $a+e$，其中 $\|e\|_\infty\le\eta$。近似点不必仍在 $K_M(A)$，但多项式 $\mathcal E_M$ 在全部实边界上仍然有定义。

对一个次数 $d\ge1$ 的单项式，将重复变量也当作其 $d$ 个出现位置，记该位置的输入因子与误差为 $a_{i_j},e_{i_j}$。有限乘积展开给
$$
\prod_{j=1}^d(a_{i_j}+e_{i_j})-\prod_{j=1}^d a_{i_j}
=\sum_{\varnothing\ne S\subseteq\{1,\ldots,d\}}
\left(\prod_{j\in S}e_{i_j}\right)
\left(\prod_{j\notin S}a_{i_j}\right).
\tag{46.21}
$$
这里只删掉无扰动的空集项。即使不同出现位置是同一个变量，展开仍是逐因子分配律；它不使用不同误差之间的独立性。取绝对值并逐项用幅度界，有
$$
\left|\prod_{j=1}^d(a_{i_j}+e_{i_j})-\prod_{j=1}^d a_{i_j}\right|
\le\sum_{s=1}^d\binom ds\eta^sA^{d-s}
=(A+\eta)^d-A^d.
$$
对 $A=0$，指数零的空乘积按一解释，也直接由有限乘积恒等式成立。

再按多项式次数的绝对系数总量求和，得到
$$
\boxed{
\sup_{\substack{\|a\|_\infty\le A\\\|e\|_\infty\le\eta}}
|\mathsf P_{n,k}(a+e)-\mathsf P_{n,k}(a)|
=u_k(A+\eta)-u_k(A),
}
\tag{46.22}
$$
以及全三角的精确公式
$$
\boxed{
\sup_{\substack{a\in K_M(A)\\\|e\|_\infty\le\eta}}
\|\mathcal E_M(a+e)-\mathcal E_M(a)\|_\infty
=u_M(A+\eta)-u_M(A).
}
\tag{46.23}
$$
上下界匹配的证明仍使用同一对共同输入：真实边界 $a=-A\mathbf1$，误差 $e=-\eta\mathbf1$，故近似边界为 $-(A+\eta)\mathbf1$。这使每个坐标的差等于对应的负幅度之差；系数非负及 $k\le M$ 使全三角最大值出现在 $(0,M)$。没有将不同坐标的扰动分别优化后拼接。

当 $\eta=0$ 时两个端点相同，（46.22）—（46.23）均为零。

在 $A>0$ 的固定小误差极限中，内侧模量与外侧包络除以误差后都趋于 $L_k(A)$ 或 $L_M(A)$，但它们在有限误差下不同。对 $k\ge1$，严格凸性还给 $u_k(A+\eta)-u_k(A)>L_k(A)\eta$（$\eta>0$）；因此用原立方体的线性常数控制可能越界的近似点，会漏掉高阶项。可用的简单线性上界是 $L_k(A+\eta)\eta$，它由对 $[A,A+\eta]$ 积分得到，但精确式（46.22）更细。

$A=0$ 时，同立方体任务的两端都是零，模量为零；本节却允许近似点离开零单点，故其噪声包络为 $u_k(\eta)$ 或 $u_M(\eta)$。这两个结论对应不同的输入域，没有矛盾。

### 46.7 有理端点、上确界与固定维数的实完成

记 $K_M^{\mathbb Q}(A)=K_M(A)\cap\mathbb Q^{M+1}$，$A$ 可以是实数。实域证明限制到这些点，给全部已述上界。

有理有限误差任务要求**比较的两个端点都为有理边界**。同立方体任务的允许对精确为
$$
a,b\in K_M^{\mathbb Q}(A),
\qquad \|a-b\|_\infty\le h,
\qquad 0\le h\le A.
$$
越界任务的允许对精确为
$$
a,\widehat a\in\mathbb Q^{M+1},
\qquad a\in K_M^{\mathbb Q}(A),
\qquad \|\widehat a-a\|_\infty\le\eta,
\qquad A,\eta\ge0.
$$
这里 $\widehat a$ 允许在原立方体之外；等价地，可写 $\widehat a=a+e$，并同时要求 $a,e\in\mathbb Q^{M+1}$。不能只要求真实端点有理而把近似端点留在未声明的实域。对于单坐标 $\mathsf P_{n,k}$，以上所有端点的维数改为 $n+k+1$，幅度域相应使用 $K_{n+k}^{\mathbb Q}(A)$。参数 $A,h,\eta$ 均允许为实数；下文的内向有理逼近证明这些明确有理端点域具有与实端点域相同的上确界。

若 $A>0$ 为有理数，全负角点属于有理域，故（46.6）的幅度最大值及全三角最大值仍达到；在（46.16）中取有理 $h\downarrow0$，得到同样的最小 Lipschitz 常数。逆常数 $1$ 的见证可取任意合法非零有理 $t$。若 $A>0$ 为无理数，则取有理半径 $r\uparrow A$：角点 $-r\mathbf1$ 给幅度趋向 $u_k(A)$；再在每个半径 $r$ 内取有理内向小扰动，割线比趋近 $u'_k(r)$，最后使 $r\uparrow A$。因此有理域的幅度上确界和最小 Lipschitz 常数仍分别为 $u_k(A)$、$L_k(A)$，全三角同理。对任意实半径 $A>0$ 均可选有理 $0<|t|\le A$，故逆向常数仍由 $t e_M$ 见证为一。

但对无理 $A$，任何一份有理边界均有 $r=\max_i|a_i|<A$。由 $u_k$ 严格递增，$|\mathsf P_{n,k}(a)|\le u_k(r)<u_k(A)$。所以幅度上确界不达到。不能把不存在的无理角点当成实际有理来源。线性端点的 Lipschitz 常数仍可由普通有理输入对达到；非线性坐标／全三角仍按第46.5节仅有割线上确界。

两种有限误差公式在有理点上也保留相同**上确界**。内侧可取有理 $r_j\uparrow A$ 和有理 $0\le h_j\le\min(h,r_j)$、$h_j\to h$，使用共同角点 $-r_j\mathbf1,-(r_j-h_j)\mathbf1$；$h=0$ 单独取零差。外侧取有理 $r_j\uparrow A$、有理 $\eta_j\uparrow\eta$，使用 $-r_j\mathbf1,-(r_j+\eta_j)\mathbf1$；$A=0$ 时直接用真实零输入。多项式连续性给精确实值上确界。若相应 $A,h$ 或 $A,\eta$ 都是有理数，所写极值对属于有理域，故达到；其它参数情形只使用已证上确界，不无条件宣称同一极值对可取得。

在**固定 $M$、通常数值范数**下，有
$$
\boxed{
\overline{K_M^{\mathbb Q}(A)}^{\|\cdot\|_\infty}=K_M(A),\qquad
\overline{\mathcal E_M(K_M^{\mathbb Q}(A))}^{\|\cdot\|_\infty}=I_M(A).
}
\tag{46.24}
$$
证明。有限维有理点在实立方体中稠密，包括用内向有理逼近端点；实立方体闭且完备。（46.17）的上界保证 $\mathcal E_M$ 一致连续，其实多项式评价给唯一连续延拓。每个实点用有理点逼近，像也逼近；反向，$I_M(A)$ 是紧实立方体的连续像，因而闭。首列提取的 $1$-Lipschitz 性保留逆向延拓。这给两个有理度量空间的实际完成；$A=0$ 为单点完成。

这种完成允许一份有限坐标中的有理数沿通常绝对值逼近实数。Context43 的离散前缀完成则要求每个固定坐标最终**严格相同**，其完整系数仍是有理数。两者使用不同拓扑、不同 Cauchy 条件和不同补入对象。一个新增数值误差界没有推翻旧前缀等距，也没有把它改解释为数值等距。

### 46.8 固定幅度下的深度增长及其非一致边界

以下固定 $A>0$，让整数 $M\to\infty$。令
$$
C_+(A)=\frac{A\lambda}{\lambda+1},\qquad
C_-(A)=\frac{A}{\lambda+1}.
$$
由（46.12），$u_M=C_+\lambda^M+C_-\lambda^{-M}$。从 $\lambda+\lambda^{-1}=A+2$ 求导，得到
$$
\frac{d\log\lambda}{dA}=\frac1{s(A)}.
$$
因此精确导数为
$$
\boxed{
L_M(A)
=\left(C'_++\frac{MC_+}{s}\right)\lambda^M
+\left(C'_- -\frac{MC_-}{s}\right)\lambda^{-M}.
}
\tag{46.25}
$$
固定 $A>0$ 时，$s,\lambda,C_\pm,C'_\pm$ 均为有限常数，$s>0,\lambda>1,C_+>0$。将（46.25）除以 $(MC_+/s)\lambda^M$，第一括号给 $1+O_A(1/M)$，另一项为指数衰减乘有界的 $M$ 比值，故
$$
\boxed{
u_M(A)\sim\frac{A\lambda}{\lambda+1}\lambda^M,\qquad
L_M(A)\sim
\frac{A\lambda}{(\lambda+1)\sqrt{A^2+4A}}\,M\lambda^M.
}
\tag{46.26}
$$
上述导数主项的相对误差为 $O_A(M^{-1})$；对足够大的 $M$，它的绝对值小于 $1/2$。由 $\log_2(1+t)=O(t)$，对正值取二进制对数，得
$$
\boxed{
\log_2 L_M(A)
=M\log_2\lambda+\log_2 M
+\log_2\!\frac{A\lambda}{(\lambda+1)\sqrt{A^2+4A}}
+O_A(M^{-1}).
}
\tag{46.27}
$$
这里的常数与误差记号依赖固定的 $A$；不是 $A\downarrow0$ 时的一致渐近。明确地，对每个固定 $M\ge1$，多项式（46.13）给 $L_M(A)\to1$；而（46.26）的主项因 $s\sim2\sqrt A$、$\lambda\to1$，在 $A\downarrow0$ 时趋于零。故不能让这个大 $M$ 比值近似对所有任意小的正 $A$ 同时有效。$A=0$ 的单点域常数为零，又与多项式导数极限是不同问题。

对每个固定 $A>0$，$L_M(A)$ 随深度无界增长。更直接地，完整负边界 $a_i=-A$ 是一个有界输入序列，但其体坐标绝对值为 $u_k(A)$，随 $k$ 指数增长。因而不能把同一全层重建直接声称为“有界序列到有界无限数组”的 $\ell^\infty$ 映射，也没有与 $M$ 无关的这个通常上确界范数 Lipschitz 常数。全层逐坐标代数恢复仍然成立；两项结论谈的是不同的函数空间要求。

### 46.9 统一量程归一后的条件数

对 $A>0$ 定义
$$
\boxed{\kappa_M(A)=\frac{A u'_M(A)}{u_M(A)}.}
\tag{46.28}
$$
它是将输入按统一量程 $A$ 归一、输出按整个三角的统一幅度上界 $u_M(A)$ 归一后所得映射的最小全局 Lipschitz 常数。具体映射为 $x\mapsto\mathcal E_M(Ax)/u_M(A)$，定义域是 $[-1,1]^{M+1}$；变量与输出的两次线性缩放把（46.17）的最优常数恰变为（46.28）。

将（46.8）按次数写成 $u_M(A)=\sum_{d=1}^{M+1}c_{M,d}A^d$，其中
$$
c_{M,d}=\binom{M+d-1}{2d-2}>0,
\qquad
w_d(A)=\frac{c_{M,d}A^d}{u_M(A)}.
$$
这些是正权重且 $\sum_d w_d=1$，所以
$$
\boxed{
\kappa_M(A)=\sum_{d=1}^{M+1}d w_d(A),
\qquad1\le\kappa_M(A)\le M+1.
}
\tag{46.29}
$$
$M=0$ 时恰为一；$M\ge1$、有限 $A>0$ 时各次数权重都正，故严格位于 $1$ 与 $M+1$ 之间。固定 $M$ 时，$A\downarrow0$ 由一次项主导，$\kappa_M\to1$；$A\to\infty$ 由最高次项主导，$\kappa_M\to M+1$。

固定 $A>0$、$M\to\infty$ 时，将（46.26）的两个等价式相除，得
$$
\boxed{
\kappa_M(A)\sim\frac{A}{\sqrt{A^2+4A}} M.
}
\tag{46.30}
$$
也可以直接对闭式（46.12）求对数导数得到以下精确式，无需增加一个独立问题：
$$
\boxed{
\kappa_M(A)
=1+\frac{A}{s}\left(
M+\frac1{\lambda+1}
-\frac{2M+1}{\lambda^{2M+1}+1}
\right).
}
\tag{46.31}
$$
证明。对分子 $\lambda^{M+1}+\lambda^{-M}$ 求对数导数，得到
$$
\frac1s\,
\frac{(M+1)\lambda^{M+1}-M\lambda^{-M}}
{\lambda^{M+1}+\lambda^{-M}}
=\frac1s\left(M+1-\frac{2M+1}{\lambda^{2M+1}+1}\right).
$$
对分母 $\lambda+1$ 的对数导数为 $\lambda/[s(\lambda+1)]$；加上外因子 $A$ 的对数导数并乘 $A$，便得（46.31）。$M=0$ 时括号为零，仍与恒等映射一致。

这里的归一化是**固定域的统一输入／输出量程**。它不是用某个实际输入的 $\|a\|$ 与实际输出的 $\|\mathcal E_M(a)\|$ 定义的点态相对条件数，也不消除输出可能为零、相消或特别小的问题。不能把（46.29）的线性深度界当成每一个实际输出都有同样相对精度保证。

### 46.10 有限误差预算与“额外位数”的准确含义

若真实边界和近似边界均在 $K_M(A)$、$A>0$，输入误差至多 $\delta$，且多项式输出按精确实数／有理数算术评价，则（46.17）给输出误差至多 $L_M(A)\delta$。因此对输入绝对误差 $2^{-q}$ 和目标输出误差 $2^{-p}$，以下整数预算充分：
$$
\boxed{q\ge p+\lceil\log_2 L_M(A)\rceil.}
\tag{46.32}
$$
这是统一的**线性充分预算**。它的线性放大因子在小误差极限中尖锐，但不能称为每个固定非零容差下必要且充分的额外位数。

当 $0\le\delta\le A$ 时，允许输入对明确为 $a,b\in K_M(A)$ 且 $\|a-b\|_\infty\le\delta$。这个完整同立方体任务的准确必要充分条件是
$$
\boxed{
\text{对全部允许输入对保证输出误差}\le\varepsilon
\quad\Longleftrightarrow\quad
u_M(A)-u_M(A-\delta)\le\varepsilon.
}
\tag{46.33}
$$
这是（46.19）的上确界定义；有理点即使没有极值对，具有相同上确界，故同样得到统一误差条件。越界任务则由（46.23）给对应的条件 $u_M(A+\delta)-u_M(A)\le\varepsilon$，不能混用内侧模量。

明确反例取 $A=1,M=1$。坐标 $\mathsf P_{0,1}=a_1-a_0^2$，$u_1(A)=A+A^2$、$L_1(1)=3$，而
$$
\omega_{1,1}(\delta)=u_1(1)-u_1(1-\delta)
=3\delta-\delta^2\qquad(0\le\delta\le1).
$$
在 $\delta=1/2$ 时，最坏全三角误差是 $5/4$，由 $(-1,-1)$ 与 $(-1/2,-1/2)$ 达到。因此输入误差 $1/2$ 已经统一保证容差 $5/4$，尽管 $\delta\le\varepsilon/L_1$ 会要求 $\delta\le5/12$。这反驳线性预算对任意有限容差的必要性，不反驳最优 Lipschitz 常数。

结合（46.27），固定 $A>0$ 时线性充分预算中的额外位数按 $M\log_2\lambda+\log_2 M+O_A(1)$ 增长。这不等于算法总位复杂度、最优读取或采样次数，也不保证某一浮点多项式评价程序达到该误差；舍入、溢出、中间量、截断与运算成本都需要独立的算法合同。这里没有新增相应算法结论。

上述结论控制数值重建误差。若下游任务再取阈值、符号或分类等不连续决定，小数值误差本身不保证决定不变；还须由该任务自己的裕度或连续性条件，将数值误差界传递到所需输出。本节在此仅限定适用范围，不新增下游决策定理。

### 46.11 保留整个观察者及实际来源的适用范围

令 $\Omega$ 为实际共同来源域，$c:\Omega\to\mathcal C$ 保留全部已获内部／外部信息与记录、来源／参考／版本身份、已获联合关系与相关性、准备和校准、相关相位／单位／增益数据、可访问记忆、局部钟及其已知关系、允许动作及其顺序、结果／失败／停止信息，以及共同误差与资源合同。给辅助坐标命名不授予未获信息的访问权。令 $a:\Omega\to K_M(A)$ 为该来源的边界读数。比较的始终是
$$
\omega\longmapsto(c(\omega),a(\omega)),\qquad
\omega\longmapsto(c(\omega),\mathcal E_M(a(\omega))).
\tag{46.34}
$$
在对应实际像上，$\mathrm{id}_{\mathcal C}\times\mathcal E_M$ 与 $\mathrm{id}_{\mathcal C}\times\beta_M$ 互逆，字面保留同一 $c$。不假设 $c$ 和 $a$ 独立，不把其像扩成未经证明的笛卡儿积，也不把边界本身等同于完整观察者。 具体地，在边界像上的复合把 $(c(\omega),a(\omega))$ 送回自身，因为 $\beta_M\mathcal E_M a(\omega)=a(\omega)$；在体像上的反向复合也由 $\mathcal E_M\beta_M\mathcal E_M a(\omega)=\mathcal E_M a(\omega)$ 送回自身。因此每一步都落在对应实际像中。

若 $\mathcal C$ 另有指定度量并给乘积用最大度量，则对 $A>0$，提升后的正向映射有上界 $\max(1,L_M)=L_M$，逆向有上界 $1$。这是分别对记录差和工作数据差取最大值得到的：若 $d_c=d_{\mathcal C}(c,c')$、$d_a=\|a-a'\|_\infty$、$d_T=\|\mathcal E_M(a)-\mathcal E_M(a')\|_\infty$，则 $\max(d_c,d_a)\le\max(d_c,d_T)\le L_M(A)\max(d_c,d_a)$，其中 $L_M(A)\ge1$。完整乘积且记录域非空时，可固定同一个 $c$ 使用角点割线或逆向见证，故标量最优常数保留；但受限实际像可能排除这些共同来源对，不能自动报告同样的最优下界。

例如固定 $M\ge1$、$A>0$ 和一个记录 $c_0$，实际边界只取 $a=t e_M$（$|t|\le A$）。由末反对角见证的同一递推，前 $M$ 层全零、最后一层全为 $t$；任意两个参数的边界差和体差均为 $|t-s|$。所以这个受限实际像上的正逆最优常数均为一，小于完整立方体的正向常数 $L_M(A)>1$。这给出了排除共同角点后最优下界不能移植的具体来源。

$A=0$ 时，单独的边界与三角都是单点，正逆最优常数为零。若完整记录 $c$ 仍可在两个正距离值之间变化，提升映射保留这些记录，便可具有最优常数一；若实际像也只剩一个零距离类，则最优常数为零。记录的恒等传递与数值工作空间的退化须分别计量。

若主张观察不可分辨，每个候选都必须解释同一份完整已获档案，且共同候选族须包含实际实现。数值距离也可以比较已经声明的实际点及其不同记录 $c,c'$，但其记录差必须计入最大乘积度量；不得删去该差来制造不可分辨性。

确定性噪声界可以比较同一真实边界与其误差记录，也可以比较两份已声明共同约束下的允许来源。它们不要求误差坐标独立；共享噪声、共同校准或重复因子不会破坏逐项确定性不等式。但数学上的角点来源和最坏扰动不证明实验能够制备、测量或合法取得它们。若要作概率或 minimax 结论，仍须对同一完整档案及联合误差事件另给实际模型。

逆映射只在递归像上恢复体。以 $M=1$ 为例，任意给出的三角数据
$$
T(0,0)=0,\qquad T(1,0)=0,\qquad T(0,1)=1
$$
违反后继关系。提取其边界得到零，重建后整个三角为零，并不返回原数据。因此不能把像上 $1$-Lipschitz 的首列提取说成任意带噪体数据的双侧逆。近似边界的多项式评价虽仍给一个递归三角，也不使它自动属于原始合法来源类。

本节建立的是既有递归体／边关系在**幅度受限、固定有限深度、通常数值范数**下的最优放大及误差模量。它与精确前缀几何并存，不能据此前向推广为全部无限有界数组映射、任意原来源的达到性、无限深度统一精度、物理时空／频率定律、算法舍入稳定性、原创优先权或新增 Lean 形式认证。

[^rroctx46_arrayamp_swamy]: M. N. S. Swamy, “Properties of the Polynomials Defined by Morgan-Voyce,” *The Fibonacci Quarterly* 4(1) (1966), pp.73–81，[原始扫描](https://www.fq.math.ca/Scanned/4-1/swamy.pdf)。本文使用的印刷页码与公式锚为：第73页式（7）的 $b_0=1,b_1=x+1$ 与二阶递推；第79页式（40）的系数公式，其中 $\binom{n+k}{n-k}=\binom{n+k}{2k}$；第80页式（42b）的较早缩放 Chebyshev 表示。后者的旧归一化不替代 DLMF 当前 $V/W$ 约定。归属只承担这个成熟多项式族，不承担本文特定非线性重建的最优噪声结论。

[^rroctx46_arrayamp_dlmf]: NIST DLMF [18.5.3](https://dlmf.nist.gov/18.5#E3) 的当前第三类 $V_n$ 约定；该处注明版本1.0.28（2020年9月15日）的 $V/W$ 对调更正。[18.12.10](https://dlmf.nist.gov/18.12#E10) 为第二类 $U_n$ 的生成式，乘 $1-z$ 才得到这里的 $V_n=U_n-U_{n-1}$。本文先按多项式／形式系数恒等式迁移；当 $A>0$ 时的解析半径另由（46.7）的极点明确给出。

## 46.99 追加锚

## 47. 同一递归关系的加权完成、解析半径与标签几何

本节接续第43节的递归体／边关系和第46节的有限幅度结果。同一递归系数决定指定加权拓扑下的恢复稳定性、完成与解析球；另行选择标签及正权以后，同一生成函数给出归一化、矩与信息几何。全部结论保留共同来源、完整已获记录、范数及有限取得条件。

离散片段与完整数组是相容关系的不同呈现；完成化仍须声明哪一种误差趋于零。不同一致结构的完成、正项求和和真实观察概率各有独立条件。本节给出普通数学证明，不据此推出物理定律或新的 Lean 认证。

### 47.1 定义、实际递归像与有限供应

固定实数 $A>0$、$0<\rho<1$，令
$$
K_A=[-A,A]^{\mathbb N}.
$$
每个 $a\in K_A$ 的数组 $\mathcal E(a)$ 由同一列递推定义：
$$
T(n,0)=a_n,\qquad
T(n,k+1)=T(n+1,k)-\sum_{j=0}^{k}T(n,j)a_{k-j}.
\tag{47.1}
$$
对 $k$ 归纳，右端只使用已经构造的列。每个坐标是 $a_0,\ldots,a_{n+k}$ 的整系数多项式，且没有常数项。因此每份实边界唯一给出一个满足 (47.1) 的实际全层数组，所有有限三角彼此相容。反向由第一列
$$
\beta(T)_n=T(n,0)
$$
提取边界。只有在对应递归像上，$\beta$ 与 $\mathcal E$ 互逆。

使用第46.2—46.5节中已经建立的以下结果：共同负角点及幅度为（46.6），系数与根为（46.8）、（46.11）—（46.12），坐标 Lipschitz 性为（46.14）—（46.17），同立方体模量为（46.19）。对每个 $n,k\ge0$，
$$
|\mathcal E(a)(n,k)|\le u_k(A),\qquad
\mathcal E(-A\mathbf1)(n,k)=-u_k(A),
\tag{47.2}
$$
其中
$$
u_k(A)=\sum_{d=1}^{k+1}\binom{k+d-1}{2d-2}A^d
=\frac{A}{\lambda+1}\bigl(\lambda^{k+1}+\lambda^{-k}\bigr),
$$
$$
s=\sqrt{A^2+4A},\qquad \lambda=\lambda(A)=\frac{A+2+s}2>1,\qquad
L_k(A)=u'_k(A).
\tag{47.3}
$$
由 \(\lambda\) 的定义，它与 \(\lambda^{-1}\) 是
\(x^2-(A+2)x+1=0\) 的两个正根，故
\(\lambda+\lambda^{-1}=A+2\)、\(\lambda-\lambda^{-1}=s\)。

同一有限依赖坐标的最优 Lipschitz 常数为 $L_k(A)$。对 $0\le h\le A$，
$$
|\mathcal E(a)(n,k)-\mathcal E(b)(n,k)|
\le u_k(A)-u_k(A-h)
\quad\text{若 }\|a-b\|_\infty\le h.
\tag{47.4}
$$
共同角点对 $a=-A\mathbf1,\ b=-(A-h)\mathbf1$ 同时使所有坐标达到 (47.4)。这些是同一组无限序列的有限限制，不是分别为不同坐标选择不相容的见证。$h=A$ 时约定 $u_k(0)=0$，与多项式公式一致。

定义加权数组空间及其范数：
$$
\mathcal B_\rho=
\left\{T:\mathbb N^2\to\mathbb R:
\|T\|_\rho:=\sup_{n,k\ge0}\rho^{n+k}|T(n,k)|<\infty\right\}.
\tag{47.5}
$$
逐坐标乘以 $\rho^{n+k}$ 将它线性等距映到通常的 $\ell^\infty(\mathbb N^2)$，因此 $\mathcal B_\rho$ 是 Banach 空间。以下“映射有界”指整个 $K_A$ 的像在这个范数下统一有界，不把非线性 $\mathcal E$ 称为线性算子。

记
$$
q=\rho\lambda(A).
$$
当 $\mathcal E(K_A)\subseteq\mathcal B_\rho$ 时，记实际像为
$$
\mathcal I_{A,\rho}=\mathcal E(K_A).
$$
不把 $\mathcal I_{A,\rho}$ 与任意加权有界数组空间混同。

### 47.2 有界映射的精确阈值

**命题 47.1（精确有界阈值）。** 全层映射 $\mathcal E:K_A\to\mathcal B_\rho$ 取值良定且统一有界，当且仅当 $q\le1$。在这一范围内，
$$
\max_{a\in K_A}\|\mathcal E(a)\|_\rho=A.
\tag{47.6}
$$

证明。由 (47.2) 及 $\rho^n\le1$，
$$
\sup_{a\in K_A}\|\mathcal E(a)\|_\rho
=\sup_{k\ge0}\rho^k u_k(A),
$$
等号由同一个全负边界在 $n=0$ 的全部坐标给出。由 (47.3)，
$$
\rho^ku_k(A)
=\frac{A}{\lambda+1}
\left[\lambda q^k+\left(\frac{\rho}{\lambda}\right)^k\right].
\tag{47.7}
$$
若 $q\le1$，两个幂都至多一，故右端至多 $A$；$k=0$ 时恰为 $A$。若 $q>1$，第一项随 $k$ 无界增长，全负边界的数组不属于 $\mathcal B_\rho$。证毕。

同一幅度恒等式也说明：若只把输出读法改为列权重
\(\sup_{n,k}\rho^k|T(n,k)|\)，完整自由边界族的幅度阈值仍是 \(q\le1\)，且最优幅度仍为 \(A\)。这只是另一指定范数下的幅度结论；其对行指标的尾部、紧性或完成条件不从下文的反对角权重结果自动继承。以下全部数组拓扑继续使用 (47.5)。

### 47.3 次临界的最优 Lipschitz 常数与统一尾界

**命题 47.2（最优全层 Lipschitz 常数）。** 当 $q<1$ 时，$\mathcal E$ 从输入通常上确界距离到输出加权范数的最优全局 Lipschitz 常数为
$$
C_\rho(A)=\sup_{k\ge0}\rho^kL_k(A)<\infty.
\tag{47.8}
$$
这个上确界在某个有限 $k$ 处取得，并且 $C_\rho(A)\ge1$。

证明。由 $u_k$ 的正系数及次数至多 $k+1$，
$$
L_k(A)\le\frac{k+1}{A}u_k(A)\le(k+1)\lambda^k.
$$
最后一步来自 (47.3)：
$$
u_k(A)
=A\lambda^k\,\frac{\lambda+\lambda^{-2k}}{\lambda+1}
\le A\lambda^k.
\tag{47.9}
$$
所以 $0\le\rho^kL_k(A)\le(k+1)q^k\to0$。$L_0(A)=1$，故此正序列的上确界有限，且可在一个有限初始段内取到最大值。

逐坐标使用有限 Lipschitz 界，再取所有 $n,k$ 的上确界，得到
$$
\|\mathcal E(a)-\mathcal E(b)\|_\rho
\le C_\rho(A)\|a-b\|_\infty.
\tag{47.10}
$$
为证最优性，固定任意 $k$，比较共同角点 $-A\mathbf1$ 与 $-(A-h)\mathbf1$，其中 $0<h\le A$。其输入距离是 $h$，第 $(0,k)$ 个坐标的加权割线比为
$$
\rho^k\frac{u_k(A)-u_k(A-h)}h
\longrightarrow\rho^kL_k(A)\quad(h\downarrow0).
$$
任何全局 Lipschitz 常数均须大于等于每个这样的极限，因此不能小于 (47.8)。有限索引取得 $C_\rho(A)$ 不等于有不同输入对取得最优割线比。证毕。

**精确统一尾界。** 更一般地，只要 $q\le1$，对每个整数 $N\ge0$，
$$
\sup_{a\in K_A}\sup_{n+k\ge N}\rho^{n+k}|\mathcal E(a)(n,k)|
=\rho^Nu_N(A)\le A q^N.
\tag{47.11}
$$
证明。$u_k(A)$ 关于 $k$ 增加，这可由 (47.3) 的正系数逐项比较得到。因此在反对角层 $n+k=m$ 上，
$$
\rho^{n+k}|\mathcal E(a)(n,k)|\le\rho^m u_k(A)\le\rho^m u_m(A).
$$
共同全负边界在 $(n,k)=(0,m)$ 取得这个层上界。又由 (47.7)，$\rho^m u_m(A)$ 是两个非负几何项之和，其底数分别为 $q\le1$ 和 $\rho/\lambda<1$，所以关于 $m$ 不增。所有 $m\ge N$ 的最大值就在 $m=N$，并由同一个全负边界的 $(0,N)$ 坐标取得。最后由 (47.9) 得 $\rho^Nu_N(A)\le Aq^N$。证毕。

因此 (47.11) 的右侧也是每份输入的统一尾界。次临界时它趋于零；临界时它趋于第47.5节的正常数 $c_A$，不能把临界尾部当成统一消失的尾部。

### 47.4 全层精确有限误差模与共同见证

在 $q\le1$ 时定义
$$
\omega_{\rho,A}(h)=
\sup_{\substack{a,b\in K_A\\\|a-b\|_\infty\le h}}
\|\mathcal E(a)-\mathcal E(b)\|_\rho,
\qquad 0\le h\le A.
$$

**命题 47.3（精确全层有限误差模）。**
$$
\boxed{
\omega_{\rho,A}(h)=
\sup_{k\ge0}\rho^k\bigl(u_k(A)-u_k(A-h)\bigr).
}
\tag{47.12}
$$
同一个角点对 $-A\mathbf1,\ -(A-h)\mathbf1$ 取得这一范数模量。

证明。对每对允许输入逐坐标应用 (47.4)，并用 $\rho^n\le1$，得到右侧上界。该共同角点对在每个坐标上给出 $u_k(A)-u_k(A-h)$ 的绝对差，所以其实际范数距离恰好是右侧。这一证明不需要为各坐标分别拼接见证，也不需要交换极限和上确界。即使索引上确界不在有限 $k$ 取得，固定输入对仍取得作为上确界定义的范数距离。

$h=0$ 时两边为零；$h=A$ 时第二个角点是零边界，右侧由 (47.6) 等于 $A$。证毕。

在次临界情形，(47.10) 给 $\omega_{\rho,A}(h)\le C_\rho(A)h$。固定 $k$ 再令 $h\downarrow0$，并取 $k$ 的上确界，可得
$$
\lim_{h\downarrow0}\frac{\omega_{\rho,A}(h)}h=C_\rho(A).
$$
这里没有把同立方体模量改成允许近似点越界的外向噪声包络。

### 47.5 临界点：有界但在全负边界不连续

令 $q=1$，即 $\rho=1/\lambda(A)$，并记
$$
c_A=\frac{A\lambda(A)}{\lambda(A)+1}>0,\qquad
b_A=\frac{A}{\lambda(A)+1}.
$$
由 (47.7)，
$$
\rho^ku_k(A)=c_A+b_A\lambda^{-2k}.
\tag{47.13}
$$

因此，对全负边界的实际数组作有限反对角坐标截断时，尾部范数由 (47.11) 精确给出，并趋于 \(c_A\)，不会趋零。这说明环境数组中的有限坐标截断在临界范数下不能逼近该对象；它不等同于“有限支撑边界生成的实际无限数组”。第47.9节将证明：在完整自由来源类中，后者的闭包恰为具有消失加权尾的实际像，任意实际数组到该闭包的距离等于其剩余尾幅度；这个全负数组的距离特别为 \(c_A\)。
对每个固定 $0<h<A$，$\lambda(A-h)<\lambda(A)$，所以
$$
\rho^ku_k(A-h)\longrightarrow0.
$$
当 $h=A$ 时此项恒为零，结论仍成立。故
$$
\lim_{k\to\infty}
\rho^k\bigl(u_k(A)-u_k(A-h)\bigr)=c_A
\qquad(0<h\le A).
\tag{47.14}
$$
共同角点对因此满足
$$
\|(-A\mathbf1)-(-(A-h)\mathbf1)\|_\infty=h,\qquad
\|\mathcal E(-A\mathbf1)-\mathcal E(-(A-h)\mathbf1)\|_\rho
=\omega_{\rho,A}(h)\ge c_A.
\tag{47.15}
$$
令 $h\downarrow0$，得到 $\mathcal E$ 在全负边界处不连续。因此临界情形没有全局 Lipschitz 常数。

事实上，整个允许区间上的临界模量都有闭式：
$$
\omega_{\rho,A}(0)=0,\qquad
\omega_{\rho,A}(h)=\max\{h,c_A\}\quad(0<h\le A),
\qquad
\lim_{h\downarrow0}\omega_{\rho,A}(h)=c_A.
\tag{47.16}
$$
证明。令 $B=A-h\in[0,A)$。$u_k$ 的一次项为 $B$，其余系数非负，故 $u_k(B)\ge B$，包括 $B=0$。由于 $0<\rho<1$，
$$
\rho^k u_k(B)\ge B\rho^k\ge B\rho^{2k}.
$$
结合 (47.13)、$\rho=\lambda^{-1}$ 及 $b_A-B=h-c_A$，
$$
\rho^k\bigl(u_k(A)-u_k(B)\bigr)
\le c_A+(h-c_A)\rho^{2k}
\le\max\{h,c_A\}.
$$
深度零的差值恰为 $h$；(47.14) 的深度极限给下界 $c_A$。取上确界即证精确式，并得到零处的跳跃。$0<h<c_A$ 时，共同角点对取得范数距离 $c_A$，但其任何有限深度坐标都没有取得该距离（其他行还多一个不超过一的因子 $\rho^n$）；$h\ge c_A$ 时，深度零已经取得模量。证毕。

结合第47.2、47.3节，整个 $K_A$ 到 $\mathcal B_\rho$ 的全局 Lipschitz 映射存在，当且仅当 $q<1$。临界结论只证明特定全负边界的不连续性，不声称每个输入处都不连续。

**临界实际像闭、有界、完备，但不紧。** 闭性实际上对所有 $q\le1$ 都成立。设 $T_r=\mathcal E(a^{(r)})$ 在 $\mathcal B_\rho$ 范数中收敛到 $T$。每个坐标的评价都是连续泛函，第一列极限 $a_n=T(n,0)$ 仍在闭区间 $[-A,A]$ 内。每个递归坐标只使用有限前缀的多项式，故
$$
T(n,k)=\lim_r\mathcal E(a^{(r)})(n,k)
=\mathcal E(a)(n,k).
$$
因此 $T\in\mathcal I_{A,\rho}$，实际像闭；(47.6) 给有界性，$\mathcal B_\rho$ 的完备性给实际像完备。

现在取临界情形及 $h_m=A/(m+2)$，令 $T_m=\mathcal E(-(A-h_m)\mathbf1)$。每个固定坐标都趋于 $\mathcal E(-A\mathbf1)$ 的相应坐标，但 (47.15) 保证两者范数距离至少为 $c_A$。若 $T_m$ 有范数收敛子列，其极限的全部坐标必须等于 $\mathcal E(-A\mathbf1)$，与这个距离下界矛盾。故该有界序列没有收敛子列，临界实际像不紧。以上结论仍然只针对完整 $K_A$ 的实际像。

### 47.6 乘积拓扑、加权范数拓扑及逆映射

每个输入实坐标均使用通常绝对值拓扑。因为每个输出坐标只依赖有限输入坐标且是多项式，$\mathcal E$ 在输入乘积拓扑到输出乘积拓扑之间连续。第一列提取是坐标投影，故两者在实际递归像上互为乘积拓扑同胚。这一结论不依赖全层加权有界性。

在 $q<1$ 时，输入乘积收敛进一步推出输出加权范数收敛。事实上，若 $a^{(r)}\to a$ 逐坐标，则对给定 $\varepsilon>0$，先由 (47.11) 选 $N$ 使 $2Aq^N<\varepsilon/2$。有限头部 $n+k<N$ 的多项式读数最终全部相差小于对应的 $\varepsilon/2$ 加权阈值；剩余尾部的差由 $2Aq^N$ 控制。于是
$$
\|\mathcal E(a^{(r)})-\mathcal E(a)\|_\rho\longrightarrow0.
\tag{47.17}
$$
具体地，固定 $a$ 和输出误差 $\varepsilon$，先如上选择 $N$。对每个 $n+k<N$，坐标多项式的连续性给一个含 $a$ 的输入乘积开邻域，使加权坐标差小于 $\varepsilon/2$；有限多个这样的邻域之交仍是乘积开邻域。在该邻域内有限头部差小于 $\varepsilon/2$，共同尾部差小于 $\varepsilon/2$，故输出范数差小于 $\varepsilon$。这证明乘积到范数的连续性，而不只给序列陈述。

反方向，在所有 $q\le1$ 的情形，只要两个数组属于 $\mathcal I_{A,\rho}$，其第一列满足
$$
\sup_{n\ge0}\rho^n|a_n-b_n|
\le\|\mathcal E(a)-\mathcal E(b)\|_\rho.
\tag{47.18}
$$
因而逆映射到加权输入范数
$$
\|a\|_{\partial,\rho}:=\sup_n\rho^n|a_n|
$$
是 $1$-Lipschitz，并且逆映射到输入乘积拓扑连续：固定 $n$ 时，坐标差至多为 $\rho^{-n}$ 倍输出范数差。

常数一最优。取 $0<\alpha\le A$ 且 $\rho\alpha<1$，比较 $\alpha e_0$ 与零。由 (47.1)，所有 $n>0$ 的行全零，而
$$
\mathcal E(\alpha e_0)(0,k)=\alpha(-\alpha)^k.
$$
因此加权输出范数和加权输入范数均为 $\alpha$，取得等号。

但逆映射到通常输入上确界范数，在次临界和临界情形都不连续。统一取 $\alpha=A/2$，令
$$
a^{(N)}=\alpha e_N,\qquad q_\alpha=\rho\lambda(\alpha)<1.
$$
严格不等式由 $\lambda(\alpha)<\lambda(A)$ 及 $q\le1$ 给出。若 $n+k<N$，有限依赖和零常数项使 $\mathcal E(a^{(N)})(n,k)=0$。对其余坐标使用半径 $\alpha$ 的 (47.11)，得到
$$
\|\mathcal E(a^{(N)})\|_\rho\le\alpha q_\alpha^N\longrightarrow0,
\qquad
\|a^{(N)}\|_\infty=\alpha.
\tag{47.19}
$$
所以普通上确界逆连续性在零数组处失败。此见证不与临界全负边界的正向不连续性混同。

### 47.7 次临界的紧像与完整数值完成

本节全部假设 $q<1$。定义拉回输出距离
$$
d_\rho(a,b)=\|\mathcal E(a)-\mathcal E(b)\|_\rho.
\tag{47.20}
$$
它是有限值的真正度量：范数给三角不等式；若距离为零，第一列相同，故 $a=b$。由第47.6节，它在 $K_A$ 上诱导通常实坐标的乘积拓扑。

**紧性与完备性。** 每个区间 $[-A,A]$ 紧。给定 $K_A$ 中任意序列，对第零坐标取收敛子列，再依次对每个坐标取子列；对角子列在每个固定坐标收敛于某个仍在 $[-A,A]$ 中的值。全部极限给 $a\in K_A$，由 (47.17)，相应数组在加权范数中收敛到 $\mathcal E(a)$。因此 $\mathcal I_{A,\rho}$ 是度量空间中的序列紧集，从而紧且完备。

也可直接验证拉回度量的完备性。若 $a^{(r)}$ 是 $d_\rho$-Cauchy，则 (47.18) 使每个固定实坐标成为 Cauchy 序列，其极限 $a_n$ 仍在闭区间 $[-A,A]$。由 (47.17)，整个数组收敛于 $\mathcal E(a)$。所以 $(K_A,d_\rho)$ 完备，$\mathcal E$ 是它到 $\mathcal I_{A,\rho}$ 的等距双射。特别地，紧像是 $\mathcal B_\rho$ 中的闭子集。

令有限支撑边界类为
$$
\mathcal F_A^{\mathbb R}
=\{a\in K_A:\exists N,\ \forall i\ge N,\ a_i=0\},
$$
$$
\mathcal F_A^{\mathbb Q}
=\{a\in\mathcal F_A^{\mathbb R}:\forall i,\ a_i\in\mathbb Q\}.
\tag{47.21}
$$
它们的实际数组像分别记为
$$
\mathcal J_{A,\rho}^{\mathbb R}=\mathcal E(\mathcal F_A^{\mathbb R}),
\qquad
\mathcal J_{A,\rho}^{\mathbb Q}=\mathcal E(\mathcal F_A^{\mathbb Q}).
$$
这里是“有限支撑边界所生成的实际无限数组”，不是把有限三角的外部数组坐标补零。后者一般不满足 (47.1)。例如 $\alpha e_0$ 的第零行在所有 $k$ 上均非零。

**实有限支撑稠密性。** 给定 $a\in K_A$，令 $a^{<N}$ 保留下标 $i<N$ 的坐标，之后全部设零。它逐坐标趋于 $a$，所以在乘积拓扑中稠密。更直接地，有限依赖使两数组在 $n+k<N$ 时完全相同，由 (47.11) 得
$$
d_\rho(a^{<N},a)\le2Aq^N\longrightarrow0.
\tag{47.22}
$$
因此实有限支撑边界在 $d_\rho$ 中稠密，其实际数组在 $\mathcal I_{A,\rho}$ 中稠密。

**有理有限支撑稠密性，包括无理幅度端点。** 对每个 $N\ge1$ 和每个 $i<N$，选
$$
r_i^{(N)}\in\mathbb Q\cap[-A,A],
\qquad |r_i^{(N)}-a_i|<1/N,
$$
并令 $r_i^{(N)}=0$ 对 $i\ge N$。这样的选择始终存在：对任何 $a_i\in[-A,A]$，其半径 $1/N$ 的邻域与 $(-A,A)$ 的交集包含非空开区间，因此含有有理数。这个论证不要求 $A$ 有理，且在端点 $\pm A$ 处使用内向逼近。

由构造 $r^{(N)}\in\mathcal F_A^{\mathbb Q}$，它逐坐标趋于 $a$。此外，$r^{(N)}$ 与 $a^{<N}$ 都在原立方体内、尾部同为零，所以
$$
\|r^{(N)}-a^{<N}\|_\infty<1/N.
$$
由 (47.10)、(47.22) 及三角不等式，
$$
d_\rho(r^{(N)},a)
\le \frac{C_\rho(A)}N+2Aq^N\longrightarrow0.
\tag{47.23}
$$
这同时证明有理有限支撑边界的乘积稠密性和拉回输出度量稠密性；其数组坐标也均为有理数，因为每个坐标是整系数多项式。

**完成的识别。** 由已证稠密性、实际包含映射及完备性，规范度量完成满足
$$
\boxed{
\widehat{(\mathcal F_A^{\mathbb R},d_\rho)}
\cong (K_A,d_\rho)
\cong
\widehat{(\mathcal F_A^{\mathbb Q},d_\rho)}.
}
\tag{47.24}
$$
在数组侧，
$$
\boxed{
\widehat{(\mathcal J_{A,\rho}^{\mathbb R},\|\cdot-\cdot\|_\rho)}
\cong\mathcal I_{A,\rho}
\cong
\widehat{(\mathcal J_{A,\rho}^{\mathbb Q},\|\cdot-\cdot\|_\rho)}.
}
\tag{47.25}
$$
这些是等距同构，分别延续已有的包含映射和 $\mathcal E$。为了明确不存在额外完成点：任意源侧 Cauchy 序列由上面的坐标论证给唯一 $a\in K_A$；任意数组侧 Cauchy 序列在完备的闭像中给唯一 $\mathcal E(a)$。反过来，每个这样的点都由 (47.22) 或 (47.23) 的允许有限支撑来源逼近。因此既无遗漏，也没有把不满足递归关系的任意加权数组补入。

此处的源侧完成使用的是 $d_\rho$，不是通常输入上确界距离。第47.6节已经给出两者不能以连续逆混用的具体序列。本节不将次临界的有限支撑稠密及紧像结论直接推广到临界点。

### 47.8 与 Context43 精确前缀完成的区别

Context43 给每个有理坐标使用离散的精确相等拓扑，其前缀超度量为
$$
d_{\mathrm{pref}}(a,b)=2^{-\min\{i:a_i\ne b_i\}}
$$
（相同时为零）。成为 Cauchy 序列，要求每个固定有限前缀最终逐项精确相同。因此最终稳定的每个坐标仍是有理数；有限支撑有理边界完成为全部有理序列，而不会仅因数值逼近引入无理系数。

若也把来源限制在当前幅度区间内，同一论证将有限支撑有理边界在这个离散前缀度量下完成为
$$
(\mathbb Q\cap[-A,A])^{\mathbb N},
$$
因为每个稳定坐标仍属于该集合，且有理序列的有限截断给稠密性。

本节 (47.24) 则使用通常数值误差构造的 $d_\rho$，允许固定坐标中的有理值收敛到实数。例如选择无理数 $\xi\in(-A,A)$ 及互异有理数 $r_m\in\mathbb Q\cap[-A,A]$、$r_m\to\xi$，令 $a^{(m)}=r_me_0$。由 (47.10)，该序列在 $d_\rho$ 下是 Cauchy，极限为 $\xi e_0$；但任意两项在第零坐标不同，故前缀距离恒为一，在 $d_{\mathrm{pref}}$ 下不是 Cauchy。

因此，同一类有限有理表示可以在不同度量下有不同完成。新结论没有修改原来的前缀等距、形式级数语义或有理共同来源结论，也没有把形式变量自动赋予解析数值。

还可精确识别第三种完成。对同一 $\mathcal F_A^{\mathbb Q}$ 改用通常输入上确界距离，则
$$
\widehat{(\mathcal F_A^{\mathbb Q},\|\cdot-\cdot\|_\infty)}
\cong c_0(\mathbb R)\cap K_A,
$$
其中 $c_0(\mathbb R)$ 是趋于零的实序列空间，右侧使用通常上确界距离。

证明一方向。若有限支撑边界 $a^{(r)}$ 在上确界范数中收敛到 $a$，则每个 $|a_n|\le A$。给定 $\varepsilon>0$，先取某个 $r$ 使 $\|a-a^{(r)}\|_\infty<\varepsilon$，再取该有限支撑的末端 $N$；对所有 $n\ge N$，有 $|a_n|<\varepsilon$，所以 $a_n\to0$。为同时证明完备性，设一般的 $a^{(r)}\in c_0(\mathbb R)\cap K_A$ 在 $\ell^\infty$ 中收敛到 $a$：先取 $\|a-a^{(r)}\|_\infty<\varepsilon/2$，再取该 $a^{(r)}$ 的尾部小于 $\varepsilon/2$，便得 $a$ 的尾部小于 $\varepsilon$；坐标极限仍在 $[-A,A]$。因此 $c_0(\mathbb R)\cap K_A$ 是 $\ell^\infty(\mathbb R)$ 中的闭集，因而完备。

反方向，给定 $a\in c_0(\mathbb R)\cap K_A$ 和 $\varepsilon>0$，选 $N$ 使 $n\ge N$ 时 $|a_n|<\varepsilon/2$。对前 $N$ 个实坐标分别用 $\mathbb Q\cap[-A,A]$ 中的数逼近到误差小于 $\varepsilon/2$，之后补零。所得允许有理有限支撑边界与 $a$ 的上确界距离小于 $\varepsilon$。端点逼近仍用第47.7节的内向有理选择，故不要求 $A$ 有理。稠密性与完备性给该完成。实有限支撑边界在同一范数下也有相同完成。

三种结论作用于同一个允许有理有限支撑集合，区别在所声明的距离：

| 来源距离 | 完成对象 | 固定坐标的极限规则 |
| --- | --- | --- |
| 离散精确前缀 $d_{\mathrm{pref}}$ | $(\mathbb Q\cap[-A,A])^{\mathbb N}$ | 最终精确相同，保留有理坐标 |
| 次临界拉回输出距离 $d_\rho$ | $K_A$，等距对应完整紧数组像 | 允许实数极限及非零无限尾部 |
| 通常上确界距离 | $c_0(\mathbb R)\cap K_A$ | 允许实数极限，但尾部须统一趋零 |

### 47.9 临界有限来源的消失尾、正距离与完成

本节固定 \(A>0\) 和临界 \(\rho=1/\lambda(A)\)，沿用第47.7节的有限支撑边界
\(\mathcal F_A^{\mathbb R},\mathcal F_A^{\mathbb Q}\) 及其实际数组像
\(\mathcal J_{A,\rho}^{\mathbb R},\mathcal J_{A,\rho}^{\mathbb Q}\)，以及完整像
\(\mathcal I_{A,\rho}\)。有限支撑修饰边界，数组仍满足全部递归关系，不能替换为补零的有限三角。

记同一个全负来源及其数组为
\[
a^\star=-A\mathbf1,\qquad T^\star=\mathcal E(a^\star).
\]
(47.2)、(47.13) 给
\(T^\star(n,k)=-u_k(A)\)、
\(\rho^ku_k(A)=c_A+b_A\rho^{2k}\)，其中
\(c_A=A\lambda/(\lambda+1)>0\)、\(b_A=A/(\lambda+1)\)。
(47.11) 的完整自由来源统一尾界不趋零；下面先证明每个固定有限支撑类具有另外的消失尾界。

#### 47.9.1 固定有限支撑的消失尾

定义
$$
\mathcal B_{\rho,0}
=\left\{T\in\mathcal B_\rho:
\lim_{L\to\infty}
\sup_{n+k\ge L}\rho^{n+k}|T(n,k)|=0\right\}.
\tag{47.26}
$$
这是加权坐标下的 $c_0(\mathbb N^2)$；有限三角穷尽全部有限坐标集。

**命题 47.4（固定有限支撑的统一消失尾）。** $\mathcal E(\mathcal F_A^{\mathbb R})\subseteq\mathcal B_{\rho,0}$。对固定支撑上界 $M$，尾收敛对所有满足 $b_i=0\ (i\ge M)$ 的 $b\in K_A$ 一致。

证明。取 $M\ge1$ 使上述支撑条件成立；零边界也允许这样选。第43.3节定理43.4及式（43.6）—（43.9）的有限系数证明只用单位常数项、加减乘及有限卷积，所以在实系数与复系数上仍成立。置
$$
F_b(z)=1+z\sum_{i=0}^{M-1}b_i z^i,\qquad
C_{n,b}(w)=\sum_{j=0}^{M-1-n}b_{n+j}w^j\quad(n<M).
$$
实际第 $n$ 行的形式级数是以下有理函数在零点的 Taylor 级数：
$$
R_{n,b}(z)
=\frac1{F_b(z)}C_{n,b}\!\left(\frac z{F_b(z)}\right)
=\sum_{j=0}^{M-1-n}\frac{b_{n+j}z^j}{F_b(z)^{j+1}}
\quad(n<M),
\qquad
R_{n,b}=0\quad(n\ge M).
\tag{47.27}
$$
后一结论亦可由 (47.1) 对列归纳验证。$C_{n,b}$ 为多项式，没有额外的无限复合级数收敛要求。

由 $A>0$ 得
$$
\lambda-(1+A)=\frac{\sqrt{A^2+4A}-A}{2}>0,
\qquad \rho<\frac1{1+A}<1.
$$
固定
$$
\rho<r<\frac1{1+A},\qquad
\delta_r=1-\frac{Ar}{1-r}>0.
\tag{47.28}
$$
对 $|z|\le r$，
$$
|F_b(z)-1|
\le A\sum_{i=0}^{M-1}|z|^{i+1}
\le\frac{Ar}{1-r}=1-\delta_r.
$$
故 $|F_b(z)|\ge\delta_r$；特别地，$F_b$ 在
$|z|<1/(1+A)$ 无零点，(47.27) 在包含闭圆盘 $|z|\le r$ 的开集上解析。

在 $|z|=r$ 上，非零行具有共同上界
$$
|R_{n,b}(z)|
\le K_{M,r}:=\frac A{\delta_r}
\sum_{j=0}^{M-1}\left(\frac r{\delta_r}\right)^j.
$$
常数可依赖 $M,A,r$，不依赖 $b,n,k$。Cauchy 系数估计给
$|\mathcal E(b)(n,k)|\le K_{M,r}r^{-k}$ 对 $n<M$ 成立。
当 $L\ge M-1$、$n+k\ge L$ 且 $n<M$ 时，
$k\ge L-M+1$，所以
$$
\sup_{\substack{b\in K_A\\b_i=0\ (i\ge M)}}
\sup_{n+k\ge L}\rho^{n+k}|\mathcal E(b)(n,k)|
\le K_{M,r}\left(\frac\rho r\right)^{L-M+1}
\longrightarrow0.
\tag{47.29}
$$
这是对固定 $M$ 的一致尾界，不对全部有限支撑长度一致。$\square$

$\mathcal B_{\rho,0}$ 是闭的：若 $T_j\to T$ 为范数收敛，先使
$\|T_j-T\|_\rho<\varepsilon/2$，再使该 $T_j$ 的尾小于
$\varepsilon/2$，就使 $T$ 的尾小于 $\varepsilon$。因此
$$
\overline{\mathcal J_{A,\rho}^{\mathbb R}}^{\,\|\cdot\|_\rho}
\subseteq\mathcal B_{\rho,0}.
\tag{47.30}
$$

#### 47.9.2 到有限来源像及其闭包的精确距离

**命题 47.5（全负角点到有限来源像的距离）。**
$$
\operatorname{dist}_\rho(T^\star,\mathcal J_{A,\rho}^{\mathbb R})
=\operatorname{dist}_\rho
\left(T^\star,\overline{\mathcal J_{A,\rho}^{\mathbb R}}^{\,\|\cdot\|_\rho}\right)
=c_A.
\tag{47.31}
$$

证明下界。任取 $S\in\mathcal B_{\rho,0}$，沿第零行有
$\rho^kS(0,k)\to0$，因而 (47.2)–(47.13) 给
$$
\rho^k\bigl(T^\star(0,k)-S(0,k)\bigr)\longrightarrow-c_A.
$$
故 $\|T^\star-S\|_\rho\ge c_A$；命题47.4和 (47.30) 同时给两个下界。

证明上界。对 $N\ge0$ 定义同一个全负边界的实际前缀截断
$$
a^{\star,<N}_i=
\begin{cases}-A,&i<N,\\0,&i\ge N,\end{cases}
\qquad T_N=\mathcal E(a^{\star,<N}).
\tag{47.32}
$$
有限依赖给 $T_N(n,k)=T^\star(n,k)$ 对 $n+k<N$ 成立。
第46.2节式（46.3）的 $Q_{n,k}(x)=-\mathcal E(-x)(n,k)$ 具有非负系数，且
$0\le-a^{\star,<N}_i\le A$，因此
$$
0\le Q_{n,k}(-a^{\star,<N})\le Q_{n,k}(A\mathbf1)=u_k(A).
$$
两数组的差满足单份幅度界，而不是一般三角不等式的两倍界：
$$
|T^\star(n,k)-T_N(n,k)|
=u_k(A)-Q_{n,k}(-a^{\star,<N})\le u_k(A).
$$
头部差为零，尾部使用 (47.11)，得到
$$
c_A\le\|T^\star-T_N\|_\rho
\le\rho^Nu_N(A)=c_A+b_A\rho^{2N}.
\tag{47.33}
$$
令 $N\to\infty$ 即得 (47.31)。$\square$

这些截断逐坐标收敛到 $T^\star$，范数距离却趋于 $c_A>0$。
它们不是范数 Cauchy 序列：否则 Banach 完备性给范数极限，坐标连续性迫使其等于 $T^\star$，与 (47.33) 矛盾。

**闭包中的角点最近距离取得且不唯一。** 任取 \(0<h\le c_A\)，令
\(B=A-h\)。因为 \(c_A<A\)，有 \(B\ge A-c_A=b_A>0\)，且 \(B<A\)，所以
\(q_B=\rho\lambda(B)<1\)。常值边界 \(-B\mathbf1\) 的有限前缀属于
\(\mathcal F_A^{\mathbb R}\)，由 (47.22) 在半径 \(B\) 的版本，其数组以误差
\(2Bq_B^M\to0\) 逼近 \(\mathcal E(-B\mathbf1)\)。
故这个实际数组属于 \(\overline{\mathcal J_{A,\rho}^{\mathbb R}}\)。
同一角点对的精确临界模量 (47.16) 又给
\[
\|T^\star-\mathcal E(-B\mathbf1)\|_\rho
=\max\{h,c_A\}=c_A.
\]
不同的 \(h\) 给不同首列，因而给无穷多个闭包中的最近点。
这些常值边界都具有无限支撑；有限支撑来源的距离达到性与任意实际数组的一般最近闭包点存在性，均不在本单元中断言或证明。显式前缀序列的 (47.33) 仍只给距离逼近率。

#### 47.9.3 分次缩放与精确剩余尾距离

对任意环境数组 \(T\in\mathcal B_\rho\)，记
\[
\tau_N(T)=\sup_{n+k\ge N}\rho^{n+k}|T(n,k)|,
\qquad
L_\rho(T)=\lim_{N\to\infty}\tau_N(T).
\tag{47.34}
\]
\(\tau_N(T)\) 非负、不增且有界，故此极限存在且有限；
\(L_\rho(T)=0\) 当且仅当 \(T\in\mathcal B_{\rho,0}\)。
这里是尾幅度，不是概率或热力学熵。

对数学缩放参数 \(\tau\ge0\)，定义
\[
(\mathsf D_\tau a)_i=e^{-(i+1)\tau}a_i,\qquad
(\mathsf U_\tau T)(n,k)=e^{-(n+k+1)\tau}T(n,k).
\tag{47.35}
\]
**分次相容恒等式。**
\[
\boxed{\mathcal E(\mathsf D_\tau a)=\mathsf U_\tau\mathcal E(a).}
\tag{47.36}
\]
证明按列归纳。首列由定义成立。若此前各列成立，(47.1) 中移位项
\(T(n+1,k)\) 的缩放因子是 \(e^{-(n+k+2)\tau}\)；每个乘积项的指数之和为
\[
(n+j+1)+(k-j+1)=n+k+2.
\]
所以所有项有同一因子，下一列也成立。每个递推和有限，证明不交换无穷运算。该恒等式在每个有限窗口与完整实际数组上同时成立。

当 \(\tau>0\) 时，
\(\mathsf D_\tau a\in K_{A_\tau}\)，其中
\(A_\tau=e^{-\tau}A<A\)，而在本节固定的临界 \(\rho\) 下
\[
q_\tau=\rho\lambda(A_\tau)<\rho\lambda(A)=1.
\]
对固定 \(\tau>0\)，取有限前缀
\(b^{\tau,M}=(\mathsf D_\tau a)^{<M}\in\mathcal F_A^{\mathbb R}\)。
已证次临界截断界 (47.22) 应用于半径 \(A_\tau\)，给
\[
\|\mathsf U_\tau T-\mathcal E(b^{\tau,M})\|_\rho
\le2A_\tau q_\tau^M\longrightarrow0
\quad(M\to\infty),\qquad T=\mathcal E(a).
\tag{47.37}
\]
因此对每个实际 \(T\in\mathcal I_{A,\rho}\) 及每个 \(\tau>0\)，
\(\mathsf U_\tau T\in\overline{\mathcal J_{A,\rho}^{\mathbb R}}\)。
这一步的有限来源确实来自同一缩放后的边界，不是任意环境坐标截断。

现在在全部环境空间中证明精确尾距离极限。对任意
\(S\in\mathcal B_{\rho,0}\)，三角不等式给
\[
\tau_N(T)\le\|T-S\|_\rho+\tau_N(S).
\]
令 \(N\to\infty\)，得 \(L_\rho(T)\le\|T-S\|_\rho\)。
另一方面，对任意 \(\tau>0\)，
\[
\tau_N(\mathsf U_\tau T)
\le e^{-(N+1)\tau}\|T\|_\rho\longrightarrow0,
\]
故 \(\mathsf U_\tau T\in\mathcal B_{\rho,0}\)，已有下界适用。
固定 \(N\ge1\)，按 \(n+k<N\) 与 \(n+k\ge N\) 分开，得到
\[
L_\rho(T)\le\|T-\mathsf U_\tau T\|_\rho
\le
\max\{(1-e^{-N\tau})\|T\|_\rho,\ \tau_N(T)\}.
\tag{47.38}
\]
头部用 \(n+k+1\le N\)，尾部用 \(0\le1-e^{-(n+k+1)\tau}\le1\)。
先令 \(\tau\downarrow0\)，再令 \(N\to\infty\)，上下界相合，故
\[
\boxed{
\lim_{\tau\downarrow0}\|T-\mathsf U_\tau T\|_\rho=L_\rho(T)
\quad(T\in\mathcal B_\rho).
}
\tag{47.39}
\]

对实际 \(T\in\mathcal I_{A,\rho}\)，(47.30) 的有限来源闭包包含于
\(\mathcal B_{\rho,0}\)，所以到它的距离至少为 \(L_\rho(T)\)。
(47.37) 则把每个 \(\mathsf U_\tau T\) 放入该闭包；(47.39) 给反向距离上界。
一个集合与其闭包到固定点的距离相等，因为范数连续且闭包点可用原集合逼近。
由此
\[
\boxed{
\operatorname{dist}_\rho(T,\mathcal J_{A,\rho}^{\mathbb R})
=
\operatorname{dist}_\rho
(T,\overline{\mathcal J_{A,\rho}^{\mathbb R}})
=L_\rho(T)
\quad(T\in\mathcal I_{A,\rho}).
}
\tag{47.40}
\]
例如可取 \(\tau_m=1/m\)，再对每个 \(m\) 选有限 \(M_m\) 使 (47.37) 右侧小于 \(1/m\)；
所得实际有限来源数组到 \(T\) 的误差趋于 \(L_\rho(T)\)。
这给任意实际数组的距离下确界逼近构造，一般最近点存在性不在本单元中断言或证明；前文全负角点的闭包达到性由其特定常值边界见证单独证明。

这些缩放满足
\(\mathsf U_0=I\)、\(\mathsf U_{\tau+\sigma}=\mathsf U_\tau\mathsf U_\sigma\)；
从坐标因子直接得其环境算子范数为 \(e^{-\tau}\)，由仅在 \((0,0)\) 非零的数组取得。
(47.39) 说明零点强连续的向量恰好是 \(\mathcal B_{\rho,0}\)；
在这个不变闭子空间上，它们构成强连续半群。
确切地，对其中的固定 \(T\) 及 \(\tau\ge\sigma\)，
\[
\|\mathsf U_\tau T-\mathsf U_\sigma T\|_\rho
\le e^{-\sigma}\|\mathsf U_{\tau-\sigma}T-T\|_\rho,
\]
所以零点的连续性给所有参数处的连续性。
在整个 \(\mathcal B_\rho\) 上不声称逐向量强连续，例如
\(L_\rho(T^\star)=c_A>0\)。
这里的参数只记分次缩放，不作物理时间、动力学生成元或相位解释。

(47.40) 的上界与等式属于完整自由来源类。若改用受限实际联合来源 \((c,a)\)，
须另证缩放及所用有限逼近仍在允许的共同记录纤维中；
保留同一个档案符号不能替代这项可行性。
对任意目标子类若其数组确实属于 \(\mathcal B_{\rho,0}\)，距离下界
\(L_\rho(T)\le\|T-S\|_\rho\) 仍可逐对象使用，但不自动取得该子类上的等号。

**同档案受限来源的反例。** 固定同一个常值档案 $c_0$，令实际边界来源仅为
\[
\Gamma=\{0,-B\mathbf1\},\qquad 0<B<A,\qquad \rho=1/\lambda(A),
\]
其中 $a$ 为包含映射。这个来源中唯一有限支撑边界是零。对 $T=\mathcal E(-B\mathbf1)$，严格不等式 $\rho\lambda(B)<1$ 及（47.11）给 $L_\rho(T)=0$，而（47.6）在半径 $B$ 的版本给
\[
\operatorname{dist}_\rho(T,\mathcal E(\Gamma\cap\mathcal F_A^{\mathbb R}))
=\|T-0\|_\rho=B>0.
\]
受限有限来源像 $\{0\}$ 本身闭，故到其闭包距离亦为 $B$。分次缩放的非零边界及其非空有限前缀不属于这个同档案纤维，正是（47.37）的可行性在此失败。环境尾下界仍成立，完整自由来源的等号却不能转授。这里直接应用已证结果，没有增加一般受限来源闭包定理。

#### 47.9.4 临界有限来源的完成及有理闭包

沿用 (47.20) 的拉回公式，在临界 \(\mathcal F_A^{\mathbb R}\) 上定义 \(d_\rho\)。临界有界性保证距离有限，首列恢复保证距离为零当且仅当边界相同；因此它仍是真距离，\(\mathcal E\) 是到
\(\mathcal J_{A,\rho}^{\mathbb R}\) 的等距双射。Banach 空间中该像的闭包完备，而像按闭包定义在其中稠密，所以
$$
\widehat{(\mathcal F_A^{\mathbb R},d_\rho)}
\cong\overline{\mathcal J_{A,\rho}^{\mathbb R}}^{\,\|\cdot\|_\rho}.
\tag{47.41}
$$
第47.5节已经以首列极限与有限坐标多项式连续性完整证明
\(\mathcal I_{A,\rho}\) 是闭的。有限来源像的闭包因此留在实际像中；
(47.40) 又说明实际数组到这个闭包距离为零，当且仅当它的尾幅度为零。
因为闭包是闭集，这给出完整自由来源类的精确刻画：
$$
\overline{\mathcal J_{A,\rho}^{\mathbb R}}^{\,\|\cdot\|_\rho}
=\mathcal I_{A,\rho}\cap\mathcal B_{\rho,0}
\subsetneq\mathcal I_{A,\rho},
\qquad T^\star\notin\overline{\mathcal J_{A,\rho}^{\mathbb R}}^{\,\|\cdot\|_\rho}.
\tag{47.42}
$$
严格性由 (47.13)、(47.31) 给出。因此，对实际数组还有等价判据
\[
T\in\overline{\mathcal J_{A,\rho}^{\mathbb R}}
\quad\Longleftrightarrow\quad L_\rho(T)=0
\quad\Longleftrightarrow\quad
\|\mathsf U_\tau T-T\|_\rho\longrightarrow0
\quad(\tau\downarrow0).
\]
这刻画的是完整 \(K_A\) 下的临界有限来源闭包，不推广为任意受限来源的闭包结论。

这不与 Context43 的精确前缀完成冲突。若给实系数采用逐字相等的前缀距离，同一组截断是 Cauchy，而 (47.33) 证明它们在临界数值距离中不是 Cauchy；当 \(A\) 有理时，这组截断也就在 Context43 的有理来源类内。当 \(A\) 无理时，不把含 \(-A\) 的截断称为有理来源。合法无限来源不必属于每一种有限来源完成。

**有理有限来源的补充。** 对第47.7节已定义的有理有限来源类
\(\mathcal F_A^{\mathbb Q}\)，
固定 $M$ 时，$\mathcal E:[-A,A]^M\to\mathcal B_\rho$ 连续：由 (47.29) 先同时控制任意两份输入的远尾，再对有限头部使用坐标多项式连续性。每个有限实边界可在同一个支撑范围内逐坐标作内向有理逼近，包括 $A$ 无理时的端点，故
$$
\overline{\mathcal E(\mathcal F_A^{\mathbb Q})}^{\,\|\cdot\|_\rho}
=\overline{\mathcal J_{A,\rho}^{\mathbb R}}^{\,\|\cdot\|_\rho}.
\tag{47.43}
$$
有理有限来源的拉回度量完成也等于 (47.41) 的右侧。由相同闭包，
(47.40) 对有理有限来源的距离同样等于 \(L_\rho(T)\)，特别地到 \(T^\star\) 的距离为 \(c_A\)。这是数值闭包结论；不声称当 $A$ 无理时，有限有理来源能逐字复制含精确读数 $-A$ 的访问记录。

### 47.10 保留整个观察者与实际来源

令 $\Gamma$ 为实际共同来源集合，
$$
c:\Gamma\to\mathcal C,\qquad a:\Gamma\to K_A.
$$
$c$ 保留全部已取得内部／外部信息与记录、来源／参考／版本身份、联合关系与相关性、准备与校准、已获相位／单位／增益数据、可访问记忆、局部钟及已知关系、合法动作及顺序、结果／失败／停止信息，以及共同误差与资源合同。给辅助坐标命名不授予尚未取得的信息。比较的完整读数始终是
$$
Q_\partial(\omega)=(c(\omega),a(\omega)),\qquad
Q_{\mathrm{body}}(\omega)=(c(\omega),\mathcal E(a(\omega))).
\tag{47.44}
$$
在这两个读数的对应实际像上，
$$
(c,a)\longmapsto(c,\mathcal E(a)),\qquad
(c,T)\longmapsto(c,\beta(T))
$$
互为双侧逆，并字面保留同一个 $c$。证明只需第一列互逆；没有把 $c$ 与 $a$ 当作独立变量，也没有把实际像扩成未经证明的 $\mathcal C\times K_A$。

若 $\mathcal C$ 另有指定度量、两边使用最大乘积距离，那么次临界正向映射从通常输入上确界版本到数组加权版本有常数上界 $\max(1,C_\rho(A))=C_\rho(A)$；逆向到加权输入版本有常数上界一。记录的恒等传递没有改变这些上界。最优下界只有在相应共同记录纤维中仍有本文所用见证对时才能保留。

本文尖锐幅度、最优放大、模量取得和临界不连续性是在完整自由实边界类 $K_A$ 上证明的。实际来源若另受顶行条件、正性、参数耦合、动作可达性或其他限制，可能排除全负角点、内向角点族或移动单点族；此时统一上界仍可限制使用，最优性和不连续性须重新检查实际见证。数学上存在的角点不证明设备能够准备或读出它。

数值完成也不能自动扩充实际来源。更精确地，在次临界条件下，对任意边界子集 $S\subseteq K_A$，从第47.6、47.7节的同胚可得
$$
\overline{\mathcal E(S)}^{\,\|\cdot-\cdot\|_\rho}
=\mathcal E\!\left(\overline S^{\,\mathrm{product}}\right).
\tag{47.45}
$$
左侧闭包没有离开闭像 $\mathcal I_{A,\rho}$。右侧是实际数学闭包，不断言新增边界由某个原有 $\omega\in\Gamma$ 实现。对完整 $(c,a)$ 读数，还须保留 $c$ 与 $a$ 的联合可行关系；没有给 $\mathcal C$ 另设拓扑时，本节也不主张整个观察者的紧性或完成化。

即使给记录配置了度量并把 $c$ 固定为一个常值，受限实际来源也不自动闭、完备或紧。例如令 $\Gamma=\mathcal F_A^{\mathbb R}$，$a$ 为包含映射。每个允许的有限实前缀都能通过补零在该来源中实现，但常值边界 $(A/2)\mathbf1$ 不属于来源。它的有限截断是实际来源中的 $d_\rho$-Cauchy 序列，由 (47.22) 收敛到被遗漏的常值边界及其数组。因此，对应实际联合像不是闭集，也不完备或紧；携带同一个 $c$ 没有补入这个来源所没有的极限。第47.7节的紧性和完成识别属于完整 $K_A$ 及其完整像，不能自动转授给这种受限实际来源。

逆映射仅在递归像上是双侧逆。对任意带噪、可能违反 (47.1) 的数组提取第一列，再重建，不保证回到原数组；本节不把这一操作当成未经证明的投影或最优去噪器。

### 47.11 有限记录的临界下界与次临界取得合同

本节把已经保留的完整观察者条件落实到明确的取得接口。第一部分固定临界
\(\rho=1/\lambda(A)\)，使用第47.9节的 \(a^\star,T^\star,a^{\star,<N},T_N\)；
第二部分才重新声明次临界权重。两部分使用同一递归关系，访问假设及误差结论分别列明。

#### 47.11.1 临界：相同完整有限记录的二来源下界

允许来源为全部 $K_A$；证明只需
$S_\star=\{a^\star\}\cup\{a^{\star,<N}:N\ge0\}$。
这是实际实边界及其由 (47.1) 生成的共同数组。若应用的合法来源排除这些见证，下界不自动转移。

协议为确定性自适应协议，接口如下：

1. 固定 $A,\rho$、算法及初始完整档案 $c$。所比较来源共享同一个 $c$，其中没有预先区分这些来源的支撑标签、代码身份或证书。
2. 查询仅为边界系数 $a_i$ 或实际数组坐标 $\mathcal E(a)(n,k)$，返回精确实值。下标可由此前完整记录自适应选择，没有预定共同查询深度要求。
3. 查询选择、计算、保存、停止及可见动作/费用/版本/来源元数据由共享初始档案及此前记录决定；坐标查询在所有来源上均有定义。原始读数与动作记录全部保留。
4. 不另供全局尾范数、有限/无限支撑判定、来源程序身份、来源相关时钟或其它全局 oracle；没有随机种子或随机观测。若“输出后”继续访问来源，这些访问仍须计入协议，不能藏进一个已经完成的估计。

精确实值查询是明确的理想接口，不宣称现实设备能以有限成本取得任意实数。下界在这个强接口下成立；这里不另推随机或物理成本结论。

**命题 47.6（完整有限记录的二来源下界）。** 若协议在 $a^\star$ 上经有限次查询终止，输出
$\widehat T\in\mathcal B_\rho$，则存在有限前缀来源
$a^{\star,<N}$，使协议具有完全相同的整份有限记录、动作顺序、停止与输出，并且
$$
\max\left\{
\|\widehat T-T^\star\|_\rho,\qquad
\|\widehat T-T_N\|_\rho
\right\}\ge c_A/2.
\tag{47.46}
$$

证明。取在 $a^\star$ 上已结束的有限执行路径。边界查询 $a_i$ 的依赖下标至多 $i$；数组查询 $(n,k)$ 的依赖下标至多 $n+k$。取 $N$ 严格大于这条路径中全部查询的这些有限上界；若无查询，可取 $N=0$。

在 $a^{\star,<N}$ 上重放：初始记录相同；若此前记录相同，确定性使下一动作相同；若查询，依赖前缀相同使返回值相同，声明的元数据也相同；若停止，则同一步停止且输出相同。对路径长度归纳，得到整份记录相等，不只是摘要相等。无需假设初始记录与边界随机独立；只使用两个合法来源共享该完整记录的明确条件。

三角不等式与 (47.33) 给
$$
c_A\le\|T^\star-T_N\|_\rho
\le\|T^\star-\widehat T\|_\rho+\|\widehat T-T_N\|_\rho,
$$
即得 (47.46)。$\square$

因此任何在 $a^\star$ 上有限停止的这类协议，都不能对全部 $S_\star$ 保证统一误差严格小于 $c_A/2$。这允许任意有限查询深度、完整追加记忆和确定性后处理；额外计算不能分开相同记录。

这是二实现最坏误差下界，不是 $a^\star$ 的点态误差下界：恒输出 $T^\star$ 的协议在该点误差为零，但在有限前缀来源上至少误差 $c_A$。若另要求输出落在 $\overline{\mathcal J_{A,\rho}^{\mathbb R}}$，(47.31) 才给在 $a^\star$ 上误差至少 $c_A$；它依赖额外输出限制。

不声称 $c_A/2$ 的最优性或存在达到它的统一算法。引入非局部读取或来源相关合法性的一般干预不属于此接口，须另核共同记录见证。若来源只允许有理有限边界而 $A$ 无理，精确读数 $-A$ 无法由这些有限来源复制，不能直接使用本文的精确记录对；(47.43) 的范数稠密不替代记录相等。

#### 47.11.2 次临界：实际有限读取的充分合同

本部分重新取 $0<\rho<1/\lambda(A)$，沿用
$$
q=\rho\lambda(A)<1,\qquad
C_\rho(A)=\sup_{k\ge0}\rho^ku_k'(A)<\infty.
$$
由于 $u_0'(A)=1$，有 $C_\rho(A)\ge1$。来源仍为完整 $K_A$。这是（47.8）已证的稳定范围，区别于本节前一部分的临界权重。

选择整数 $N\ge0$ 和误差容限 $\eta\ge0$。接口实际返回前 $N$ 个系数读数
$y_0,\ldots,y_{N-1}$，并在同一份实际误差合同或同一个联合事件下满足
$$
|y_i-a_i|\le\eta\qquad(0\le i<N).
\tag{47.47}
$$
不要求读数或误差独立，不把分别的概率承诺当作未经证明的同时事件。令工作副本与分析中的真实前缀分别为
$$
\widetilde a_i=
\begin{cases}\operatorname{clip}_{[-A,A]}(y_i),&i<N,\\0,&i\ge N,\end{cases}
\qquad
z_i=\begin{cases}a_i,&i<N,\\0,&i\ge N.\end{cases}
$$
原始读数、来源、动作、精度及执行记录保留在档案中；裁剪只改变工作副本。$z$ 用于分析，算法无需取得这个未知精确前缀。

由于 $a_i\in[-A,A]$，裁剪不增加相对它的误差，故
$\|z-\widetilde a\|_\infty\le\eta$。既有前缀尾界与同立方体 Lipschitz 界给
$$
\begin{aligned}
\|\mathcal E(a)-\mathcal E(\widetilde a)\|_\rho
&\le\|\mathcal E(a)-\mathcal E(z)\|_\rho
 +\|\mathcal E(z)-\mathcal E(\widetilde a)\|_\rho\\
&\le2Aq^N+C_\rho(A)\eta.
\end{aligned}
\tag{47.48}
$$
重建的是有限支撑边界的实际完整递归像，不是把输出数组的未读三角补零。

给定 $\varepsilon>0$，选择
$$
N\in\mathbb N,\quad2Aq^N\le\varepsilon/2,\qquad
0\le\eta\le\frac{\varepsilon}{2C_\rho(A)}.
\tag{47.49}
$$
$0<q<1$ 保证有限 $N$ 存在。若条件在 $N=0$ 已成立，允许空读取，此时 $\widetilde a=z=0$、读数误差项实际为零。在 (47.47) 的同一条件下，重建误差至多 $\varepsilon$。

这是充分误差合同，不保证设备能取得所需 $\eta$，不提供采样数、置信度、位复杂度或运行成本。无限目标可由有限数据与递归/有理行公式描述并按坐标求值；这不表示已逐项输出无限多个数。该方法不称最优，亦未与临界下界组成已经闭合的最优算法理论。

这里的次临界上界是 (47.8)、(47.22) 的直接应用，不另计为新数学定理。它与临界二来源下界一起说明指定接口的稳定性变化，但没有给出全局最优查询算法，也没有把有限数学描述等同于有限成本取得全部实值。

### 47.12 阈值的读法与资源范围

写 $\rho=2^{-\sigma}$，其中 $\sigma>0$，则
$$
\sigma_c(A)=\log_2\lambda(A),\qquad
\begin{cases}
\sigma\ge \sigma_c(A) & \text{统一有界},\\
\sigma>\sigma_c(A) & \text{全局 Lipschitz、紧像及本文的数值完成结论},\\
\sigma=\sigma_c(A) & \text{全负边界处出现 (47.16) 的正模量跳跃}.
\end{cases}
\tag{47.50}
$$
在 $A=1$ 时，既有第46节已经识别 $\lambda(1)=\phi^2$，所以
$$
\sigma_c(1)=2\log_2\phi.
$$
这称为指定增长与指定折扣范数之间的正则性阈值，不称作 Hausdorff 维数、物理时间或物理空间的定律。

全层数组在数学上由全部边界坐标共同定义，每个固定坐标仍只有有限依赖。次临界尾界能支持有限窗口的误差控制，但不使观察者免费获得未知的全部边界，不提供对任意非可计算实数的有限数字访问，也不免除读数精度、算术舍入、执行时间与校准成本。上述几何结论尚未指定概率模型；下文另行声明标签赋权。该赋权不自动给出实际采样下界、量子实现或物理信息容量结论。

### 47.13 同一齐次展开的解析球与紧尺度嵌入

本节固定 $0<\rho<1$。只在本节把输入和输出标量扩为复数，令 $X=\ell^\infty(\mathbb N;\mathbb C)$，令 $Y_\rho=\mathcal B_\rho(\mathbb C)$ 使用 (47.5) 的绝对值范数。列递推 (47.1) 的整系数多项式在复数上同样逐坐标有意义。实数立方体上的前述结论及来源限制不变。

**连续齐次多项式与收敛球。** 写
$$
\mathcal E(a)(n,k)=\sum_{d=1}^{k+1}H_d(a)(n,k),
$$
其中 $H_d(a)(n,k)$ 是该坐标多项式的总次数 $d$ 部分，$d>k+1$ 时定义为零。第46.2—46.3节式（46.3）、（46.8）的非负 $Q_{n,k}(x)=-\mathcal E(-x)(n,k)$ 分解说明：这个次数的系数绝对值总和正是
$$
c_{k,d}=\binom{k+d-1}{2d-2}\quad(k\ge d-1).
$$
故
$$
\begin{aligned}
\|H_d(a)\|_\rho
&\le \|a\|_\infty^d\sup_{k\ge d-1}\rho^kc_{k,d}\\
&\le \|a\|_\infty^d\sum_{k\ge d-1}\rho^k
             \binom{k+d-1}{2d-2}\\
&=\|a\|_\infty^d\,
  \frac{\rho^{d-1}}{(1-\rho)^{2d-1}}.
\end{aligned}
\tag{47.51}
$$
最后一步令 \(k=d-1+j\)。把 \(2d-1\) 份几何级数相乘，指数和为 \(j\) 的非负整数元组数为
\(\binom{j+2d-2}{2d-2}\)，从而
\[
\sum_{j\ge0}\binom{j+2d-2}{2d-2}\rho^j=(1-\rho)^{-(2d-1)}.
\]
每份几何级数在 \(0<\rho<1\) 收敛，非负项的有限乘积展开和重排合法。这完整证明 (47.51) 最后一项的系数求和恒等式；后面的概率归一化将直接复用它。

还须说明这确实是 Banach 空间值的连续齐次多项式，而不只是逐坐标的形式表达。对每个坐标的每个次数 $d$ 单项式，把重复出现的输入下标排成一个长度 $d$ 的列表。将第 $r$ 个因子放入第 $r$ 个独立输入，有限求和得到坐标上的 $d$-线性形式。对全部坐标同时使用这个规则，(47.51) 的同一系数界给出
$$
\|\widetilde B_d(a^{(1)},\ldots,a^{(d)})\|_\rho
\le m_d\prod_{r=1}^d\|a^{(r)}\|_\infty,\qquad
m_d=\frac{\rho^{d-1}}{(1-\rho)^{2d-1}}.
$$
因此这些坐标确实定义一个取值于 $Y_\rho$ 的连续 $d$-线性映射。对输入置换取平均得到对称映射 $B_d$，上界不变，且其对角值为 $H_d(a)=B_d(a,\ldots,a)$。

定义
$$
A_{\mathrm{crit}}=\frac{(1-\rho)^2}{\rho}.
$$
对每个 $0<r<A_{\mathrm{crit}}$，
$$
\sum_{d\ge1}m_dr^d
=\frac{r}{1-\rho}\,
  \frac1{1-r/A_{\mathrm{crit}}}<\infty.
\tag{47.52}
$$
于是 $\sum_{d\ge1}H_d$ 在每个闭子球 $\|a\|_\infty\le r$ 上一致范数收敛。连续对称多线性表达还给
$$
\|DH_d(a)\|\le d\,m_dr^{d-1}
 \quad(\|a\|_\infty\le r).
$$
右侧对 $d$ 的级数也收敛。更明确地，连续对称多线性表达给
\[
DH_d(a)h=dB_d(h,a,\ldots,a),\qquad
\|D^2H_d(a)\|\le d(d-1)m_d R^{d-2}\quad(d\ge2,\ \|a\|_\infty\le R).
\]
$H_1$ 的二阶导数为零。对 $\|a\|_\infty+\|h\|_\infty\le R<A_{\mathrm{crit}}$，线段 $a+th$（$0\le t\le1$）留在这个子球。每项沿线段的二阶积分余项及范数三角不等式给
\[
\left\|\mathcal E(a+h)-\mathcal E(a)-\sum_{d\ge1}DH_d(a)h\right\|_\rho
\le\frac{\|h\|_\infty^2}{2}
\sum_{d\ge2}d(d-1)m_dR^{d-2}.
\]
右边的级数是（47.52）的二阶导数，等于
\[
\frac{2}{(1-\rho)A_{\mathrm{crit}}}
(1-R/A_{\mathrm{crit}})^{-3}<\infty.
\]
逐项二阶余项先对有限和成立，再用局部一致收敛及可求和的上界取极限。因此该误差为 $O(\|h\|_\infty^2)$，且
$D\mathcal E(a)=\sum_{d\ge1}DH_d(a)$ 为连续复线性映射。导数级数在每个闭子球一致收敛，故导数连续。这直接给出复 Fréchet 全纯性及显式余项
\[
\boxed{
\|\mathcal E(a+h)-\mathcal E(a)-D\mathcal E(a)h\|_\rho
\le\frac{\|h\|_\infty^2}{2}
\sum_{d\ge2}d(d-1)m_dR^{d-2}.}
\]

每个固定坐标仅有 $d\le k+1$ 的有限项，所以该 Banach 值和逐坐标恰等于原递归映射。由此
$$
\mathcal E:\{a\in X:\|a\|_\infty<A_{\mathrm{crit}}\}
\longrightarrow Y_\rho
$$
是全纯映射。

$\lambda+\lambda^{-1}=A+2$，所以 $\rho\lambda(A)=1$ 等价于 $A=A_{\mathrm{crit}}$。这个原点球不能扩大：若 $R>A_{\mathrm{crit}}$，选 $A_{\mathrm{crit}}<r<R$，则 $a=-r\mathbf1$ 属于半径 $R$ 的开球，但第47.2节已经证明其递归数组不属于 $Y_\rho$。这排除了同一递归映射在更大整个原点球上取 $Y_\rho$ 值；不声称排除所有其他形状的解析延拓域，也不声称临界球面上的一致解析延拓。

**临界齐次截断不在该范数下收敛。** 取 \(A=A_{\mathrm{crit}}\)、
\(a=-A\mathbf1\)，并记
\[
S_D(a)=\sum_{d=1}^{D}H_d(a),\qquad D\ge1.
\]
每个有限和都是已构造的 \(Y_\rho\) 元素。因为总次数 \(d\) 的系数具有同一符号，而输入全部为 \(-A\)，对第零行有
\[
H_d(a)(0,k)=-c_{k,d}A^d\quad(k\ge d-1),
\]
较小 \(k\) 时该次数项为零。对每个固定 \(d\)，
\(c_{k,d}=\binom{k+d-1}{2d-2}\) 关于 \(k\) 至多按 \(2d-2\) 次多项式增长，而 \(0<\rho<1\)。所以
\(\rho^k H_d(a)(0,k)\to0\)，进而
\(\rho^k S_D(a)(0,k)\to0\)。
另一方面，由 (47.13)，
\(\rho^k\mathcal E(a)(0,k)\to-c_A\)。因此对每个固定有限 \(D\)，
\[
\boxed{\|\mathcal E(a)-S_D(a)\|_\rho\ge c_A>0.}
\tag{47.53}
\]
这里用的是同一个临界实际数组，没有把不同次数的见证拼在一起。它说明逐坐标有限多项式等式仍然成立、完整数组仍然有界，却不足以保证齐次级数在该 Banach 范数中收敛。这与 (47.16) 的径向不连续性相容；并未排除其他形状的解析域，也没有把齐次截断当作合法制备动作。

**紧尺度嵌入。** 若 $0<\rho<\eta<1$，则自然包含 $J:Y_\eta\to Y_\rho$ 的范数为一。令 $P_NT$ 保留 $n+k<N$ 的有限个数组坐标，其余置零。它在环境数组空间中是有限秩算子，并且
$$
\|(J-P_N)T\|_\rho
\le\left(\frac{\rho}{\eta}\right)^N\|T\|_\eta.
\tag{47.54}
$$
这个算子范数界可由只在 $(0,N)$ 非零的环境数组取得。右侧随 $N$ 趋零，故 $J$ 是有限秩算子的算子范数极限，从而为紧算子。这里的数组截断用于环境空间证明，不声称它保留递归关系或是实际合法操作。

此嵌入也解释次临界紧性：当 $\rho\lambda(A)<1$，可选 $\rho<\eta<1/\lambda(A)<1$。完整递归像在 $Y_\eta$ 中由 $A$ 统一控制，经紧嵌入在 $Y_\rho$ 中相对紧；第47.5节的闭性使它紧。这与第47.7节的直接证明一致。

**不使用卷积代数假设。** 加权上确界序列空间本身不对同权重卷积封闭。取
$$
x_k=y_k=\rho^{-k}.
$$
两序列的加权范数均为一，但
$$
(x*y)_k=\sum_{j=0}^kx_jy_{k-j}=(k+1)\rho^{-k},
$$
其加权范数无穷。把序列嵌入数组的第零行即可看到相同障碍。因此上述全纯构造依靠明确的连续多线性系数界，不把 $Y_\rho$ 当成未经证明的卷积 Banach 代数。所有解析结论都是成熟幂级数与 Banach 空间方法在本递归上的应用，不赋予物理或原创性含义。

### 47.14 正标签总和与精确归一化区域

概率部分仍取正实 \(A>0\)、\(0<\rho<1\)，使用前文同一
\(u_k,c_{k,d},\lambda,s,A_{\mathrm{crit}}\)。为避免与随机次数混淆，将分母记为
\[
\Delta=1-(A+2)\rho+\rho^2
=(1-\lambda\rho)(1-\rho/\lambda).
\tag{47.55}
\]
下面显式选择一份标签赋权；只有正项总权有限时才定义概率。它不预设实际观察者、世界或传感器遵循这份分布。

定义可数标签集
\[
\mathcal L=
\{(k,d,j):k\ge0,\ 1\le d\le k+1,\ 1\le j\le c_{k,d}\}.
\]
标签权重为
\[
w_{A,\rho}(k,d,j)=\rho^k A^d.
\tag{47.56}
\]
记 \(Z(A,\rho)=\sum_{(k,d,j)\in\mathcal L}w_{A,\rho}(k,d,j)
=\sum_{k\ge0}\rho^ku_k(A)\)，此时允许其值为 \(+\infty\)。
\(j\) 是明确选择的系数重数标签；不声称它天然对应外界样本、不同世界或某一传感器结果。

解析节已经在 (47.51) 中完整证明
\[
m_d=\sum_{k=d-1}^{\infty}\rho^kc_{k,d}
=\frac{\rho^{d-1}}{(1-\rho)^{2d-1}}.
\]
此处直接使用同一系数和，不另设一份生成结构。

引入无量纲权重比
\[
t=\frac{A}{A_{\mathrm{crit}}}=\frac{A\rho}{(1-\rho)^2}>0.
\tag{47.57}
\]
这里的 \(t\) 是参数比，不是时间变量。所有权重非负，故 Tonelli 求和在允许 \(+\infty\) 的意义下成立。由（47.51），
\[
\begin{aligned}
Z
&=\sum_{(k,d,j)\in\mathcal L}\rho^k A^d
=\sum_{d\ge1}A^d\sum_{k\ge d-1}c_{k,d}\rho^k\\
&=\sum_{d\ge1}m_dA^d
=\frac{A}{1-\rho}\sum_{d\ge1}t^{d-1}.
\end{aligned}
\tag{47.58}
\]

这给出准确连接
\(\sum_d m_dA^d=Z(A,\rho)\)：解析节的齐次项范数求和上界，恰好是这份正标签计数的总权。\(m_d\) 是系数求和的精确值，并被用于上界 \(\|H_d\|\)；此处不声称它总等于齐次多项式的最小范数常数。
因此 \(Z\) 有限当且仅当 \(t<1\)。由于
\(\Delta=(1-\rho)^2-A\rho\) 且 \(1-\rho/\lambda>0\)，这等价于 \(\rho\lambda<1\)。在且仅在此严格内部，
\[
\boxed{
Z(A,\rho)=\frac{A}{(1-\rho)(1-t)}
=\frac{A(1-\rho)}{\Delta},
\qquad
p_{A,\rho}(k,d,j)=\frac{\rho^k A^d}{Z}.
}
\tag{47.59}
\]
\(Z>0\)，全部 \(p\) 非负且总和一，从而确实定义概率律。这个 \(Z\) 正是原幅度生成函数在 \(z=\rho\) 的收敛评价，无需引入另一生成对象。

临界点 \(\rho\lambda=1\) 时 \(t=1\)，（47.58）和（47.13）都证明 \(Z=+\infty\)。因此临界有界幅度不能用于归一化此正标签律。超临界 \(1/\lambda<\rho<1\) 时正项总和仍发散；此时有理函数 \(A(1-\rho)/\Delta\) 为负，其代数延拓绝不是正项级数之和，更不是概率归一化常数。

### 47.15 条件次数、深度边缘与同一函数的第二种分解

设随机变量 \(K,\mathsf D,J\) 为标签的三个坐标。直接在固定 \(k\) 的有限标签集求和，得到
\[
\boxed{
\Pr(K=k)=\frac{\rho^k u_k(A)}{Z},
\qquad
\Pr(\mathsf D=d,J=j\mid K=k)=\frac{A^d}{u_k(A)}.
}
\tag{47.60}
\]
条件律与 \(\rho\) 无关，恰好是有限幅度多项式显式归一化的次数—重数族。若只保留次数，
\[
\Pr(\mathsf D=d\mid K=k)=\frac{c_{k,d}A^d}{u_k(A)}.
\]
因此
\[
\mathbb E[\mathsf D\mid K=k]
=\frac{A u'_k(A)}{u_k(A)}=\kappa_k(A).
\tag{47.61}
\]
这是已有有限深度统一量程条件数在这个特定统计族中的均值解释，不把任意条件数认作概率。\(k=0\) 时唯一标签为 \((0,1,1)\)，条件次数为一。

反过来按固定次数求和，（47.51）—（47.59）给出
\[
\boxed{\Pr(\mathsf D=d)=(1-t)t^{d-1},\qquad d\ge1.}
\tag{47.62}
\]
即 \(\mathsf D-1\) 是参数比为 \(t\) 的几何分布。给定 \(\mathsf D=d\)，令 \(M_d=K-d+1\ge0\)。代入归一化因子后
\[
\boxed{
\Pr(M_d=m\mid\mathsf D=d)
=\binom{m+2d-2}{2d-2}(1-\rho)^{2d-1}\rho^m.
}
\tag{47.63}
\]
这是明确形状参数 \(2d-1\) 的负二项分布；（47.51）已经直接验证其总和一，无需先假定原数组具有任何随机独立性。

其概率生成函数为
\[
\mathbb E[z^{M_d}\mid\mathsf D=d]
=\left(\frac{1-\rho}{1-\rho z}\right)^{2d-1}.
\]
写 $r_d=2d-1$、$G_d(z)=((1-\rho)/(1-\rho z))^{r_d}$。该级数在 $|z|<1/\rho$ 收敛，故包含 $z=1$ 的邻域，并可逐项微分。
$G'_d(1)=r_d\rho/(1-\rho)$、$G''_d(1)=r_d(r_d+1)\rho^2/(1-\rho)^2$；
由 $\mathbb E[M_d^2]=G''_d(1)+G'_d(1)$ 减去 $(G'_d(1))^2$，得到
\[
\mathbb E[M_d\mid\mathsf D=d]
=\frac{(2d-1)\rho}{1-\rho},
\qquad
\operatorname{Var}(M_d\mid\mathsf D=d)
=\frac{(2d-1)\rho}{(1-\rho)^2}.
\tag{47.64}
\]
所以
\[
\boxed{
\mathbb E[K\mid\mathsf D]
=\frac{1+\rho}{1-\rho}\mathsf D-\frac1{1-\rho}.
}
\tag{47.65}
\]
这两个相反方向的条件化来自同一个 \(Z\)：固定深度得到有限次数族，固定次数得到明确的深度分布。

### 47.16 无穷微分的严格内部依据

令自然参数
\[
\theta=\log A,\qquad \eta=\log\rho,
\qquad
\psi(\theta,\eta)=\log Z(e^\theta,e^\eta).
\]
这里 $\eta$ 是对数参数，与第47.13节紧嵌入中的权重记号不同。其定义域是开集
\[
\mathcal O=
\{(\theta,\eta):\eta<0,\ e^\eta\lambda(e^\theta)<1\}.
\tag{47.66}
\]
不能把以下光滑结论直接延伸到临界曲线。

固定任一内部参数。由连续性可选择一个闭参数小邻域，使其中
\[
0<A_-\le A\le A_+,\qquad
0<\rho_-\le\rho\le\rho_+<1,\qquad
q_+=\rho_+\lambda(A_+)<1.
\]
\(\lambda(A)\) 随 \(A>0\) 增加；也可直接从其明确公式选择上述上端点。由（47.3），
\[
u_k(A_+)\le A_+\lambda(A_+)^k.
\]
对任意固定非负整数 \(r,\ell\)，逐标签权重的自然参数导数是
\(d^r k^\ell e^{d\theta+k\eta}\)。使用 \(d\le k+1\)，按同一 \(k\) 汇总得到统一控制
\[
\begin{aligned}
\sum_{d=1}^{k+1}\sum_{j=1}^{c_{k,d}}
d^r k^\ell A^d\rho^k
&\le(k+1)^{r+\ell}\rho_+^k u_k(A_+)\\
&\le A_+(k+1)^{r+\ell}q_+^k.
\end{aligned}
\tag{47.67}
\]
右端关于 \(k\) 可求和，且不依赖小邻域内参数。这给所有固定阶偏导级数的局部一致绝对收敛，因而可逐项微分。\(Z\ge A_->0\)，对数与商的微分也合法。特别地，全部次数／深度的有限阶矩均有限。

这一估计同时承担交换无穷求和、参数求导和期望的义务。无需从一个形式级数恒等式未经说明地直接推出解析微分；临界处也没有共同的 \(q_+<1\)。

### 47.17 均值、协方差与二参数信息矩阵

由（47.67）许可的逐项微分，
\[
\nabla\psi=(\mathbb E[\mathsf D],\mathbb E[K]).
\]
直接对（47.59）求导得
\[
\boxed{
\mathbb E[\mathsf D]
=1+\frac{A\rho}{\Delta}
=\frac{(1-\rho)^2}{\Delta}
=\frac1{1-t}.
}
\tag{47.68}
\]
固定 \(A\) 对 \(\rho\) 求导，并用（47.55）分解分母，得
\[
\boxed{
\mathbb E[K]
=-\frac{\rho}{1-\rho}
+\frac{\lambda\rho}{1-\lambda\rho}
+\frac{\rho/\lambda}{1-\rho/\lambda}.
}
\tag{47.69}
\]
（47.62）的几何级数求导独立给出
\[
\operatorname{Var}(\mathsf D)=\frac{t}{(1-t)^2}.
\]
再对（47.65）取期望，得到等价且全正的均值表示
\[
\boxed{
\mathbb E[K]
=\frac{\rho+t}{(1-\rho)(1-t)},
\qquad
\frac{\mathbb E[\mathsf D]}{\mathbb E[K]}
=\frac{1-\rho}{\rho+t}.
}
\tag{47.70}
\]
严格内部 \(A,\rho>0\) 时 \(\mathbb E[K]>0\)，比值合法。

为证明 Hessian 恒等式，不只引用抽象模型名称。逐标签有
\[
\partial_\theta p=(d-\mathbb E[\mathsf D])p,
\qquad
\partial_\eta p=(k-\mathbb E[K])p.
\]
（47.67）保证相应一阶／二阶矩可逐项求导，于是
\[
\boxed{
\nabla^2\psi=
\begin{pmatrix}
\operatorname{Var}(\mathsf D)&\operatorname{Cov}(\mathsf D,K)\\
\operatorname{Cov}(\mathsf D,K)&\operatorname{Var}(K)
\end{pmatrix}.
}
\tag{47.71}
\]
同时，对数概率的两分量导数为
\((d-\mathbb E[\mathsf D],\,k-\mathbb E[K])\)，其二阶期望正好为（47.71）。因此这确实是**此选定二参数标签族、自然参数坐标下**的 Fisher 信息矩阵；更换参数需按 Jacobian 运输，不能把矩阵条目当作不依赖坐标的数值。

明确微分给
\[
\boxed{
\operatorname{Var}(\mathsf D)
=\frac{A\rho(1-\rho)^2}{\Delta^2},
\qquad
\operatorname{Cov}(\mathsf D,K)
=\frac{A\rho(1-\rho^2)}{\Delta^2},
}
\tag{47.72}
\]
\[
\boxed{
\operatorname{Var}(K)
=-\frac{\rho}{(1-\rho)^2}
+\frac{\lambda\rho}{(1-\lambda\rho)^2}
+\frac{\rho/\lambda}{(1-\rho/\lambda)^2}.
}
\tag{47.73}
\]
条件分解给独立检查：
\[
\boxed{
\operatorname{Cov}(\mathsf D,K)
=\frac{1+\rho}{1-\rho}\operatorname{Var}(\mathsf D),
}
\tag{47.74}
\]
因为对 \(K\) 的条件残差与 \(\mathsf D\) 正交；具体地
\(\mathbb E[\mathsf D K]
=\mathbb E[\mathsf D\,\mathbb E(K\mid\mathsf D)]\)，再用（47.65）并减去均值乘积即可。全方差恒等式同样给
\[
\operatorname{Var}(K)
=\frac{\rho(2\mathbb E[\mathsf D]-1)}{(1-\rho)^2}
+\left(\frac{1+\rho}{1-\rho}\right)^2
\operatorname{Var}(\mathsf D),
\]
与（47.73）一致；所有项由二阶矩有限性合法。

Fisher 矩阵在严格内部正定。若某实线性组合
\(a\mathsf D+bK\) 的方差为零，它在所有正概率标签上必须相同。三点
\((K,\mathsf D)=(0,1),(1,1),(1,2)\)
均具有正概率；比较前两点给 \(b=0\)，再比较后两点给 \(a=0\)。故非零参数方向的方差严格正。这个论证只支持本二参数族内部的可区分性，不推出外部观察者的统计可识别性。

### 47.18 临界平均斜率回接有限深度条件数

固定 \(A>0\)，让 \(\rho\uparrow1/\lambda\)，则 \(t\uparrow1\)。由（47.70）直接得到
\[
\boxed{
\lim_{\rho\uparrow1/\lambda}
\frac{\mathbb E[\mathsf D]}{\mathbb E[K]}
=\frac{1-1/\lambda}{1+1/\lambda}
=\frac{\lambda-1}{\lambda+1}
=\frac{A}{\sqrt{A^2+4A}}.
}
\tag{47.75}
\]
最后一步用
\(A=(\lambda-1)^2/\lambda\) 与
\(s=(\lambda^2-1)/\lambda\)。

此极限不是临界点的概率期望：临界点没有这份归一化律。它只比较严格内部的一族有限期望。等价地，令 \(\delta_{\mathrm c}=1-\lambda\rho\downarrow0\)，从（47.68）—（47.69）得
\[
\mathbb E[K]=\delta_{\mathrm c}^{-1}+O_A(1),
\qquad
\mathbb E[\mathsf D]=\frac{A}{s}\delta_{\mathrm c}^{-1}+O_A(1).
\]
两者分别发散，但其比值有上述极限。

第46.9节式（46.28）—（46.31）给
\[
\frac{\kappa_k(A)}{k}\longrightarrow\frac{A}{s}
\quad(k\to\infty,\ A>0\text{固定}).
\]
结合（47.61），同一系数族因此具有两种相容而不同的读法：固定大深度时，条件次数均值的每层增长率趋于 \(A/s\)；将全部深度按 \(\rho\) 混合、并从严格内部接近可归一化边界时，总次数均值与总深度均值之比趋于同一值。这里证明的是“均值之比”，不是未经说明的 \(\mathbb E[\mathsf D/K]\)；后者还有 \(K=0\) 的定义问题。

### 47.19 同一临界尺度：最坏放大与平均深度

本节固定 \(A>0\)，从次临界侧令
\(\rho\uparrow1/\lambda(A)\)。所有幅度导数都是对 \(A\) 求导；所有渐近中的 \(A\) 保持固定。使用前面已经证明的最优常数
\[
C_\rho(A)=\sup_{k\ge0}\rho^ku'_k(A),
\qquad
q=\rho\lambda,\qquad
\epsilon=-\log q>0.
\]
则有
\[
\boxed{
\lim_{\rho\uparrow1/\lambda}\epsilon C_\rho(A)
=\frac{c_A}{e s},
\qquad
\lim_{\rho\uparrow1/\lambda}
\frac{C_\rho(A)}{\mathbb E_{A,\rho}[K]}
=\frac{c_A}{e s},
\quad
c_A=\frac{A\lambda}{\lambda+1},\quad s=\sqrt{A^2+4A}.
}
\tag{47.76}
\]
第二个极限的期望只属于前面显式归一化的标签律，临界点自身没有该概率律。

**一致有界余项。** 由 (47.3)、(47.13) 中同一闭式，
\[
u_k(A)=c_A\lambda^k+b_A\lambda^{-k},
\qquad b_A=\frac{A}{\lambda+1}.
\]
对 \(\lambda+\lambda^{-1}=A+2\) 求导，得
\(\lambda'/\lambda=1/(\lambda-\lambda^{-1})=1/s\)。因此
\[
\boxed{
\rho^ku'_k(A)
=q^k\left(c'_A+\frac{c_A}{s}k\right)
+\left(\frac{\rho}{\lambda}\right)^k
\left(b'_A-\frac{b_A}{s}k\right).
}
\tag{47.77}
\]
这里
\[
c'_A=\frac{\lambda}{\lambda+1}
+\frac{A\lambda}{s(\lambda+1)^2},
\qquad
b'_A=\frac1{\lambda+1}
-\frac{A\lambda}{s(\lambda+1)^2},
\]
均是固定 \(A>0\) 的有限常数。令 \(\beta=\lambda^{-2}<1\)。因
\(\rho/\lambda=q\beta\le\beta\)，从 (47.77) 抽出主项
\((c_A/s)kq^k\) 后，余项 \(R_k(\rho)\) 满足
\[
\begin{aligned}
|R_k(\rho)|
&\le |c'_A|+|b'_A|+\frac{b_A}{s}k\beta^k\\
&\le M_A:=
|c'_A|+|b'_A|
+\frac{b_A}{s}\frac{\beta}{(1-\beta)^2}<\infty.
\end{aligned}
\tag{47.78}
\]
最后使用非负几何导数级数
\(\sum_{k\ge0}k\beta^k=\beta/(1-\beta)^2\)。
这个上界同时对所有 \(k\ge0\) 和所有 \(0<\rho<1/\lambda\) 成立；没有把仅逐 \(k\) 有效的余项误用于上确界。

记
\[
S(\epsilon)=\sup_{k\in\mathbb N} k e^{-\epsilon k}.
\]
(47.78) 对每个 \(k\) 的上下两侧估计给
\[
\boxed{
\left|C_\rho(A)-\frac{c_A}{s}S(\epsilon)\right|
\le M_A.
}
\tag{47.79}
\]
这是同一索引集合上的一致有界扰动下的上确界估计，不需要假定两个上确界由相同整数 \(k\) 取得。

**整数极大值的极限。** 连续函数 \(x e^{-\epsilon x}\) 在 \(x\ge0\) 上的最大值由求导得到，为 \(1/(e\epsilon)\)。所以
\(\epsilon S(\epsilon)\le1/e\)。
对 \(0<\epsilon<1\)，取
\(k_\epsilon=\lfloor1/\epsilon\rfloor\)，则
\(\epsilon k_\epsilon\to1\)，从而
\[
\epsilon S(\epsilon)
\ge \epsilon k_\epsilon e^{-\epsilon k_\epsilon}
\longrightarrow e^{-1}.
\]
合并上下界，
\[
\boxed{\epsilon S(\epsilon)\longrightarrow 1/e.}
\tag{47.80}
\]
将 (47.79) 乘以 \(\epsilon\)，有
\(\epsilon M_A\to0\)，即得 (47.76) 的第一个极限。

**与平均深度的同尺度比较。** 从 (47.69) 写成
\[
\mathbb E[K]
=\frac{q}{1-q}
-\frac{\rho}{1-\rho}
+\frac{\rho/\lambda}{1-\rho/\lambda}.
\]
固定 \(A\) 时，后两项在 \(\rho\uparrow1/\lambda\) 的邻域有界，因为
\(1/\lambda<1\) 且 \(1/\lambda^2<1\)。又 \(q=e^{-\epsilon}\)，所以
\[
\epsilon\frac{q}{1-q}
=\frac{\epsilon}{e^\epsilon-1}\longrightarrow1.
\]
最后一个极限也可由
\(e^\epsilon-1=\int_0^\epsilon e^x\,dx\)
直接夹逼：
\(e^{-\epsilon}\le\epsilon/(e^\epsilon-1)\le1\)。
因此
\[
\boxed{\epsilon\,\mathbb E_{A,\rho}[K]\longrightarrow1.}
\tag{47.81}
\]
均值在严格内部为正；(47.76) 的第二个极限于是由
\[
\frac{C_\rho(A)}{\mathbb E[K]}
=\frac{\epsilon C_\rho(A)}{\epsilon\mathbb E[K]}
\]
直接得到。至此全部极限由一致估计和整数极值证明，不依赖数值拟合。

这个等式比较确定性最坏放大常数与指定标签律的平均深度；它不把最坏放大改解释为实际平均噪声，也不把所选标签律认作观察者的真实来源概率或物理时间。常数与余项依赖固定 \(A>0\)，没有宣称 \(A\downarrow0\) 时的一致结论。

### 47.20 标签 Shannon 熵及粗分组的区别

在严格内部，所有标签概率严格正，且
\[
-\log p(K,\mathsf D,J)
=\log Z-\mathsf D\log A-K\log\rho.
\]
右侧绝对值至多
\[
|\log Z|+|\log A|\mathsf D+|\log\rho|K,
\]
其期望由前面的矩界有限。因此熵级数收敛，可以逐项求和，得到以自然对数计量的
\[
\boxed{
H(K,\mathsf D,J)
=\log Z-\log A\,\mathbb E[\mathsf D]
-\log\rho\,\mathbb E[K]<\infty.
}
\tag{47.82}
\]
该式的非负性也来自其原定义 \(\sum p(-\log p)\)，不能把某个负的代数延拓解释为熵。

若把重数标签 \(j\) 丢掉，概率变为
\[
\Pr(K=k,\mathsf D=d)=\frac{c_{k,d}\rho^kA^d}{Z}.
\]
给定 \(k,d\)，\(J\) 在 \(c_{k,d}\) 个标签上均匀，故
\[
H(K,\mathsf D,J)
=H(K,\mathsf D)+\mathbb E[\log c_{K,\mathsf D}].
\tag{47.83}
\]
该修正项有限：\(c_{k,d}\le2^{k+d-1}\le 2^{2k}\)，从而
\(\mathbb E[\log c_{K,\mathsf D}]\le2\log2\,\mathbb E[K]\)。
所以细标签与按次数合并的对象有不同熵；不能在合并以后沿用细标签公式而忽略重数。这也说明所选计数与赋权属于概率定义的一部分。

（47.82）是组合标签法则的 Shannon 熵，不是世界的不确定性、传感器读数熵、热力学熵或物理时间箭头。若要把它运输到实际观测，必须额外提供共同来源、实际抽样／加权规则、标签与事件的映射，以及该映射保留的关系。现有数组恢复或一个可归一化公式没有自行提供这些条件。

### 47.21 端点与退化不能省略

**\(\rho=0,\ A>0\)。** 把它作为非负权重的独立端点，取 \(\rho^0=1\)，则只有 \(k=0,d=1,j=1\) 有权重，\(Z=A\)。分布退化为单点，\(\mathbb E[K]=0,\mathbb E[\mathsf D]=1,H=0\)。自然参数 \(\eta=\log\rho\) 不再是有限值，严格内部正定 Fisher 结论不在此端点直接适用；均值比也因分母零而未定义。

**\(A=0,\ 0<\rho<1\)。** 所有原标签权重为零，\(Z=0\)，不能归一化为本节原定义的概率律。可是 \(A\downarrow0\) 的概率族有不同意义的极限：
\[
\Pr(K=k,\mathsf D=1,J=1)\longrightarrow(1-\rho)\rho^k,
\]
其它固定标签的概率趋零。证明：\(u_k(A)/A\to1\)，且
\(Z/A=(1-\rho)/[(1-\rho)^2-A\rho]\to1/(1-\rho)\)。
极限点概率总和一。为证明总变差收敛，给定 $\varepsilon>0$，选有限标签集 $F$ 使极限律 $p_0(F^c)<\varepsilon$。有限集上的逐点收敛使充分小的 $A>0$ 满足 $\sum_{\ell\in F}|p_A(\ell)-p_0(\ell)|<\varepsilon$，因此 $p_A(F^c)<2\varepsilon$。从而整个标签集的绝对差之和小于 $\varepsilon+2\varepsilon+\varepsilon=4\varepsilon$，按总变差为该和的一半的约定即得收敛。极限是次数固定为一、深度几何分布，均值分别为
\(1,\rho/(1-\rho)\)。这是重标后的极限律，不是把零总权强行相除所得的 \(A=0\) 原律。

**临界与超临界。** \(\rho=1/\lambda\) 只有有界幅度，没有有限 \(Z\)；\(\rho>1/\lambda\) 两者均失去相应有限性。\(\rho=1\) 在 \(A>0\) 下同样不可能归一化。所有无限微分、有限矩和熵结论都只在严格内部；不能从固定 \(A\) 的边界极限推出任意 \(A\downarrow0,\rho\uparrow1\) 联合极限的一致结论。

**有限条件族。** 每个固定 \(k\) 的次数—重数条件族仅需 \(A>0\)，自身没有全深度归一化阈值。全深度混合额外引入 \(\rho\) 和正项可求和条件；不能把全深度失败误报为某个有限深度条件概率不存在。

### 47.22 可核对的同模型临界反例与有限证据

取 \(A=1/2\)，则 \(\lambda=2\)。临界 \(\rho=1/2\) 下
\[
\rho^k u_k(A)=\frac13+\frac16\,4^{-k}\le\frac12,
\]
但
\[
\sum_{k=0}^N\rho^k u_k(A)
=\frac{N+1}{3}+\frac29(1-4^{-(N+1)})
\longrightarrow+\infty.
\tag{47.84}
\]
这给同一个明确对象上的反例：加权上确界有界不推出这份正标签总权可归一化。

在内部 \(A=1/2,\rho=1/4\)，各式给精确值
\[
Z=\frac67,\quad
\mathbb E[\mathsf D]=\frac97,\quad
\mathbb E[K]=\frac{17}{21},
\]
\[
\operatorname{Var}(\mathsf D)=\frac{18}{49},\quad
\operatorname{Cov}(\mathsf D,K)=\frac{30}{49},\quad
\operatorname{Var}(K)=\frac{758}{441}.
\tag{47.85}
\]
这个有理点的 Fisher 行列式为
\[
\frac{18}{49}\frac{758}{441}-\left(\frac{30}{49}\right)^2
=\frac{88}{343}>0.
\]
按重数 $c_{k,d}$ 汇总 $k=0,\ldots,40$ 的精确有理权重，对
$1,\mathsf D,K,\mathsf D^2,\mathsf DK,K^2$ 得到六个未归一化截断和。
它们均不超过相应全和，误差均小于 $10^{-8}$。一个共同的非负剩余项上界是
\[
Aq^m\left[
\frac{(m+1)^2}{1-q}
+\frac{2(m+1)q}{(1-q)^2}
+\frac{q(1+q)}{(1-q)^3}
\right],\qquad m=41,
\]
本例恰为 $1851/2199023255552$。理由是 $\mathsf D\le k+1$、$K=k\le k+1$，且（47.9）给 $\rho^ku_k(A)\le Aq^k$；每种剩余和至多为
$A\sum_{k\ge m}(k+1)^2q^k$。令 $k=m+j$ 并展开平方，利用几何级数的零、一、二次矩
$1/(1-q)$、$q/(1-q)^2$、$q(1+q)/(1-q)^3$，即得上述界。
矩归一化使用完整 $Z=6/7$，不使用截断总权。若相应归一化原始矩的区间为 $[\ell_f,u_f]$，则方差区间为
$[\ell_{X^2}-u_X^2,u_{X^2}-\ell_X^2]$，协方差区间为
$[\ell_{XY}-u_Xu_Y,u_{XY}-\ell_X\ell_Y]$；这里各原始矩非负。
这保留相减和乘积的误差，不能把截断方差直接当作单向界。
临界例的 $k=0,\ldots,8$ 加权幅度与（47.84）相符，其 $N=0,1,4,8$ 部分和分别为
$1/2,7/8,967/512,422343/131072$。这些有限精确值只佐证公式与下标；无穷归一化、交换次序、所有阶矩、正定性和临界结论由前文普通证明承担。

最坏放大与平均深度的有限数值例取
\(A\in\{1/2,1,4\}\)、\(\epsilon\in\{10^{-1},10^{-2},10^{-3}\}\)，
令 \(q=e^{-\epsilon},\rho=q/\lambda\)，用 (47.77) 在
\(0\le k<N\)、\(N=40/\epsilon\) 的整数范围评价。所有遗漏整数 \(k\ge N\) 的值由
\[
\rho^ku'_k(A)\le(k+1)e^{-\epsilon k}
\le(N+1)e^{-40}<1
\]
控制：函数在这个范围递减；这三档下 \(N\le40000\)，且
\(e^{40}>2^{40}>40001\)。而 \(k=0\) 的值恰为一，所以真正最大值位于这个有限范围。该尾界是解析的；以下数值采用60位和100位十进制精度的公式评价，二者差小于 $10^{-48}$，显示值取九位小数；有限高精度值不作为区间认证。最接近临界的一档给：

| \(A\) | \(\epsilon\) | \(\epsilon C_\rho\)（近似） | \(C_\rho/\mathbb E[K]\)（近似） | \(c_A/(es)\)（近似） |
| ---: | ---: | ---: | ---: | ---: |
| \(1/2\) | \(10^{-3}\) | 0.082023940 | 0.082119612 | 0.081750987 |
| \(1\) | \(10^{-3}\) | 0.119347754 | 0.119460803 | 0.119048288 |
| \(4\) | \(10^{-3}\) | 0.222381654 | 0.222532192 | 0.222034884 |

这九个有限案例仅佐证公式、方向与数量级，所有渐近仍由 (47.78)–(47.81) 的普通证明承担。

### 47.23 同一关系的不同完成、放大与赋权

这一连接只使用一份生成函数：
\[
\boxed{
\sum_k u_k(A)z^k
=\frac{A(1-z)}{1-(A+2)z+z^2}.
}
\]
它的系数来自递归体／边幅度；增长根 \(\lambda\) 给加权幅度的有界阈值；把 \(z=\rho\) 并显式赋予计数标签正权后，同一函数成为归一化常数；它的对数导数给次数、深度、协方差与这个特定统计族的 Fisher 几何。临界斜率与有限深度 \(\kappa_k/k\) 通过已证明的相等极限回接。

统一成立于这些具体关系和转换。有限上确界、绝对可求和、某个完备空间的成员身份、概率归一化和实际可观测性是不同条件；临界反例把它们的边界保留下来。


在次临界范围，离散有限来源与完整数组可通过包含、取极限和体／边互逆相容地连接，但三种来源距离的完成对象仍不同：精确前缀保留有理坐标，通常上确界只补成趋零实序列，拉回输出度量补成整个有界实立方体。它们共同保留有限递归关系，未因此变成相同的一致结构。

本节进一步给出一个具体的共同临界尺度：齐次展开的正求和上界就是 \(Z\)，其次数权重是几何的；确定性最坏放大 \(C_\rho\) 与所选法则的平均深度以同一 \(1/\epsilon\) 级别发散。临界的有界数组、消失尾失败、解析截断失败和归一化失败在同一模型里相互对应，但每项仍有自己的定义和证明。完成中的一个合法极限也不自动成为原实际来源可以有限取得的对象；完整记录与共同实现条件继续按第47.10节保留。


Morgan–Voyce／Chebyshev 生成函数的成熟归属继承自第46.3节；几何／负二项分布、对数配分函数的协方差恒等式和 Shannon 链式分解属于标准方法。这里的内容是对同一已定系数族的普通综合推导，不宣称新的普遍统计框架、文献原创优先权、Lean 核验或实际传感器模型。全部结论限于所声明的递归族、参数域、度量、标签律和合法来源。

### 47.24 精确来源、归属与本单元边界

本节的有限输入归第46节：式（46.1）的递推及有限多项式依赖、式（46.3）的非负系数分解、式（46.6）的共同全负角点、式（46.8）、（46.11）—（46.12）的系数与两根闭式、式（46.14）—（46.17）的坐标 Lipschitz 性、式（46.19）的同立方体精确模量、式（46.28）—（46.31）的统一量程条件数，以及式（46.34）的完整观察者实际像运输。它们共同保留有限深度、同一输入域及共同见证条件。[第46节的不可变正文](https://github.com/the-omega-institute/trureturing/blob/bb03a0b32070a52ae10b180158ad1e4092698f99/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#L10922)提供这些普通证明；本节据此推导全层结论。

[Context43 的不可变正文](https://github.com/the-omega-institute/trureturing/blob/419ffbbb196cb45f824532f8f2c16c12e3268286/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#L8704)中，第43.2—43.4节拥有有限多项式、限制相容与第一列互逆；定理43.4的式（43.6）—（43.9）拥有实际行有限系数公式，引理43.5拥有有限依赖；第43.5节拥有离散有理坐标的精确前缀完成；第43.6及43.11节区分全部已获档案、实际来源和完成对象。第47.9节只将同一有限代数证明运输到实／复系数，再在明确的有限支撑、无零点圆盘与 Cauchy 系数估计条件下给解析尾界，未把形式级数自动当成无条件解析函数。

标量族的成熟归属与记号如下：

- M. N. S. Swamy, “Properties of the Polynomials Defined by Morgan-Voyce,” *The Fibonacci Quarterly* 4(1) (1966), pp.73–81，[原文](https://www.fq.math.ca/Scanned/4-1/swamy.pdf)。印刷第73页式（7）的小写 $b_k$ 满足 $b_0=1,b_1=x+1$ 及 $b_{k+2}=(x+2)b_{k+1}-b_k$，本节 $u_k(A)=A b_k(A)$；印刷第79页式（40）给相同二项式系数。第80页式（42b）为旧缩放 Chebyshev 表示，不能替代当前 $V/W$ 约定。
- NIST DLMF [18.5.3](https://dlmf.nist.gov/18.5#E3) 的当前第三类记号为 $V_0=1,V_1=2x-1$；该处注明版本1.0.28（2020年9月15日）交换旧 $V/W$ 标签的更正。取 $U_{-1}=0$，有 $u_k(A)=A V_k(1+A/2)=A[U_k(1+A/2)-U_{k-1}(1+A/2)]$。
- DLMF [18.12.10](https://dlmf.nist.gov/18.12#E10) 给第二类 $U_k$ 的生成式；乘 $(1-z)$ 才得到 $U_k-U_{k-1}$。本模型的解析半径由实际极点证明，不从默认正交区间移植。

Cauchy 系数估计、Banach 齐次幂级数与紧嵌入、几何／负二项分布、对数配分函数的协方差 Hessian 及 Shannon 链式法则均为标准方法。成熟标量族的归属不代替本递归映射的最优性、临界来源闭包或取得条件证明；本节的综合推导不主张文献原创优先权或穷尽文献搜索。

邻近形式结果 [CanonicalDiscountedFutureGeometry](https://github.com/the-omega-institute/trureturing/blob/a492391be5b09240e6be894c3e742a75a945feb1/D5/S3/Observer/MetricGeometryLaws/CanonicalDiscountedFutureGeometry.lean) 的公开定理 `canonical_discounted_future_geometry` 处理全读出距离有界时的折扣预测伪度量与更新 Lipschitz 性；[DiscountedPrimeTimeUltrametric](https://github.com/the-omega-institute/trureturing/blob/a492391be5b09240e6be894c3e742a75a945feb1/D5/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric.lean) 的 `discounted_prime_time_distance_strong_triangle` 处理有限坐标族上的加权离散相等差异及强三角律。两者不供应本节依赖幅度增长根 $\lambda(A)$ 的数值阈值，其假设不能替代本节证明。第43.1节拥有的 `AntidiagonalArraySourceSeries` 特选自然数组，也不能替代任意实边界族上的全层论证。本节没有新的 Lean 形式认证。

临界有限来源的精确闭包、剩余尾距离、实／有理来源的同一闭包及分次缩放强连续向量刻画见第47.9节；声明查询接口的完整记录下界及次临界充分取得合同见第47.11节。距离等式针对完整自由来源类，任意受限联合来源的完成须另保留同档案纤维可行性，不能由环境尾幅度独自决定。全负角点在闭包中的最近点已由常值边界见证取得且不唯一；有限支撑距离达到性、任意实际数组的一般最近点存在性、随机查询下界与达到下界的最优算法，均不在本单元中断言或证明。无理幅度的有理范数逼近不提供逐字相同的精确读数，数学来源存在性也不认定设备已能制备、读取或认证该来源。

解析球、指定标签归一化与信息矩阵保留各自参数及概率范围；标签统计不是实际来源律，也不导出物理时间、动力学生成元、热力学熵增或普遍信息本体。离散层、数值完成及观察表示的关系在这些已证接口下相容，原有完整研究问题仍超出本单元的结论。

## 47.99 追加锚

## 48. 全幅度最近有限前缀、有理达到性与同一系数的统计几何

对每个 \(A>0\)，临界全负数组都有达到距离 \(c_A\) 的有限前缀来源；其最小允许前缀截止长度是 \(\lceil\log(1-\rho)/\log\rho\rceil\)，其中 \(\rho=\lambda(A)^{-1}\)。固定截止内的有理来源另有精确达到判据：阈值严格超出一，或阈值等于一且 \(A\) 有理。下文先证明这两项近似结论，再把单点来源的 \(A\ge1/2\) 现象作为特例，连接同一递归系数的标签统计、Fisher 几何、临界极限及精确齐次范数。

全部概率属于显式选择的组合标签族 \(\mathbb P_{\mathrm{lab},A,\rho}\)；没有给实际来源、完整档案或物理过程添加概率律。参数比 \(t\) 不是时间。前缀截止、有限支持大小、有限符号描述与实际取得条件分别保留。

### 48.1 共同系数、两种聚合与适用范围

固定 \(A>0\)、\(0<\rho<1\)，定义
\[
s=\sqrt{A^2+4A},\qquad
\lambda=\frac{A+2+s}{2}>1,\qquad
c_A=\frac{A\lambda}{\lambda+1},\qquad
b_A=\frac{A}{\lambda+1}.
\]
由第46.2—46.3节式（46.3）、（46.6）、（46.8）、（46.12）给出的同一递归系数族是
\[
c_{k,d}=\binom{k+d-1}{2d-2},\qquad
u_k(A)=\sum_{d=1}^{k+1}c_{k,d}A^d
=c_A\lambda^k+b_A\lambda^{-k}.
\tag{48.1}
\]
其中 \(k\ge0\)、\(1\le d\le k+1\)。三个基本关系为
\[
\lambda+\lambda^{-1}=A+2,\qquad
\lambda-\lambda^{-1}=s,\qquad
\frac{d\log\lambda}{dA}=\frac1s.
\]

对固定 \(\rho\)，记
\[
A_{\mathrm c}=\frac{(1-\rho)^2}{\rho},\qquad
t=\frac{A\rho}{(1-\rho)^2},\qquad
m_d=\sum_{k\ge d-1}\rho^kc_{k,d}
=\frac{\rho^{d-1}}{(1-\rho)^{2d-1}}.
\tag{48.2}
\]
正标签总权为
\[
Z=\sum_{k\ge0}\rho^ku_k(A)
=\sum_{d\ge1}A^dm_d.
\]
它有限当且仅当 \(t<1\)，等价于 \(\rho\lambda<1\)，并且在此严格内部
\[
Z=\frac{A}{(1-\rho)(1-t)}.
\tag{48.3}
\]
所有概率论断均限于这个严格内部，除非明确讨论从内部趋近边界的极限。临界 \(t=1\) 时正项总权无穷，不存在这份归一化标签律。

Banach 空间部分固定 \(0<\rho<1\)，输入为
\(X=\ell^\infty(\mathbb N;\mathbb C)\)，输出为
\[
Y_\rho=\left\{T:\|T\|_\rho
=\sup_{n,k\ge0}\rho^{n+k}|T(n,k)|<\infty\right\}.
\]
递归映射 \(\mathcal E\) 取（47.1）的逐列定义，\(H_d(a)(n,k)\) 是该坐标实际多项式的总次数 \(d\) 部分，\(d>k+1\) 时为零。第47.13节式（47.51）—（47.52）通过连续对称多线性映射的对角值构造这些连续齐次多项式，并给出 Banach 值解析和；系数绝对值和与共同全负输入的符号饱和分别由（46.3）、（46.6）、（46.8）供应。这些是本节解析结论的供应前提；仅有一个抽象标签计数，并不能推出递归多项式具有这些性质。

### 48.2 全部幅度的最近有限前缀与精确截止长度

固定 \(A>0\)、\(\rho=\lambda(A)^{-1}\)，仍记
\(T^\star=\mathcal E(-A\mathbf1)\)。对整数 \(N\ge1\)，定义
\[
\mathcal F_{A,N}
=\{b\in[-A,A]^{\mathbb N}:b_i=0\text{ 对所有 }i\ge N\},
\qquad
\mathcal J_{A,N}=\mathcal E(\mathcal F_{A,N}),
\]
并取同一负前缀
\[
b^{A,N}_i=
\begin{cases}-A,&i<N,\\0,&i\ge N,\end{cases}
\qquad T_{A,N}=\mathcal E(b^{A,N}).
\]
这里 \(N\) 是允许非零坐标的**前缀截止长度**，不是任意散布坐标的非零个数。本节不把这两个资源量混同。

**有限来源的生成函数与消失尾。** 对任意 \(b\in\mathcal F_{A,N}\)，令
\[
F_b(z)=1+\sum_{i=0}^{N-1}b_i z^{i+1},\qquad
R_{n,b}(z)=\sum_{k\ge0}\mathcal E(b)(n,k)z^k.
\]
递推先在形式幂级数意义下给
\[
F_b(z)R_{n,b}(z)=b_n+zR_{n+1,b}(z).
\]
因为 \(F_b(0)=1\)，它具有形式逆；又因为所有 \(n\ge N\) 行均由递推归纳为零，逐行迭代得到
\[
R_{n,b}(z)
=\sum_{j=0}^{N-n-1}
\frac{b_{n+j}z^j}{F_b(z)^{j+1}}\quad(n<N),
\qquad R_{n,b}=0\quad(n\ge N).
\tag{48.4}
\]
此等式首先是形式恒等式，下面再给解析范围。

临界关系给 \(\lambda-(A+1)=(s-A)/2>0\)，所以
\(\rho<(1+A)^{-1}\)。选
\(\rho<R<(1+A)^{-1}\)。在 \(|z|\le R\) 上，
\[
|F_b(z)-1|
\le A\sum_{i=1}^{N}R^i
\le\frac{AR}{1-R}<1.
\]
因此（48.4）在包含这个闭圆盘的邻域解析。对各有限非零行应用 Cauchy 系数界，有常数 \(C_{b,n,R}\) 使
\[
|\mathcal E(b)(n,k)|\le C_{b,n,R}R^{-k}.
\]
故 \(\rho^k|\mathcal E(b)(n,k)|\to0\)。只有 \(n<N\) 的有限多行，所以该数组具有消失加权尾。特别地，首行目标差满足
\[
\rho^k|T^\star(0,k)-\mathcal E(b)(0,k)|
\longrightarrow c_A,
\quad\text{从而}\quad
\|T^\star-\mathcal E(b)\|_\rho\ge c_A.
\tag{48.5}
\]
这里不需要把一般环境数组截断当作实际递归来源。

**同一个负前缀同时最小化每个坐标的误差。** 令
\(Q_{n,k}(x)=-\mathcal E(-x)(n,k)\)。（46.3）的系数性质说明 \(Q_{n,k}\) 是非负系数多项式。因 \(|b_i|\le A\mathbf1_{i<N}\)，逐坐标有
\[
|\mathcal E(b)(n,k)|
\le Q_{n,k}(|b|)
\le Q_{n,k}(A\mathbf1_{i<N})
=-T_{A,N}(n,k)
\le u_k(A).
\]
三角不等式的反向估计于是给
\[
\begin{aligned}
|T^\star(n,k)-\mathcal E(b)(n,k)|
&\ge u_k(A)-|\mathcal E(b)(n,k)|\\
&\ge u_k(A)+T_{A,N}(n,k)\\
&=|T^\star(n,k)-T_{A,N}(n,k)|.
\end{aligned}
\tag{48.6}
\]
最后一步使用 \(T_{A,N}\le0\) 和上述绝对值上界。故同一个实际前缀取得所有坐标共同的最小误差，特别地
\[
\operatorname{dist}_\rho(T^\star,\mathcal J_{A,N})
=\|T^\star-T_{A,N}\|_\rho.
\]
这不是把分别可达的坐标最优值拼成一个未必存在的来源。

定义
\[
W_N(A)=A\sum_{i=1}^{N}\rho^{-i}.
\]
临界恒等式 \(A=(1-\rho)^2/\rho\) 给
\[
W_N(A)=\frac{1-\rho}{\rho}(\rho^{-N}-1),
\qquad
W_N(A)\ge1\quad\Longleftrightarrow\quad
\rho^N\le1-\rho.
\tag{48.7}
\]

**充分性。** 假设 \(W_N(A)\ge1\)。记
\(p_{n,k}=-T_{A,N}(n,k)\ge0\)、\(p_k=p_{0,k}\)。有限依赖给
\(p_k=u_k(A)\) 对 \(k<N\) 成立；因此这些初始项满足
\(p_k\ge A\rho^k\)。首行递推可改写为
\[
p_k=p_{1,k-1}
+A\sum_{i=1}^{\min(k,N)}p_{k-i}\quad(k\ge1).
\]
对 \(k\ge N\)，若此前各项满足所需界，则
\[
p_k\ge A\sum_{i=1}^{N}p_{k-i}
\ge A^2\rho^k\sum_{i=1}^{N}\rho^{-i}
=A\rho^kW_N(A)
\ge A\rho^k.
\]
故由归纳，\(p_k\ge A\rho^k\) 对所有 \(k\ge0\) 成立。首行的加权误差因此满足
\[
\begin{aligned}
0\le\rho^k[u_k(A)-p_k]
&\le c_A+b_A\rho^{2k}-A\rho^{2k}\\
&=c_A+(b_A-A)\rho^{2k}<c_A.
\end{aligned}
\tag{48.8}
\]
严格性来自 \(b_A<A\)，包括每个有限 \(k\)。当 \(N=1\) 时，基步为 \(p_0=A\)，归纳从 \(k=1\) 开始，仍覆盖全部首行。

现在取 \(n\ge1\)，写 \(m=n+k\)。若 \(m<N\)，有限依赖说明当前前缀与全负边界完全给出同一坐标，误差为零。若 \(m\ge N\)，由 \(0\le p_{n,k}\le u_k(A)\) 得
\[
\begin{aligned}
\rho^{n+k}[u_k(A)-p_{n,k}]
&\le\rho^m u_k(A)\\
&\le\rho^m u_{m-1}(A)\\
&=c_A(\rho+\rho^{2m})\\
&\le c_A\bigl[\rho+(1-\rho)^2\bigr]
<c_A.
\end{aligned}
\tag{48.9}
\]
第二步用 \(k\le m-1\) 以及 \(u_j(A)\) 随非负整数 \(j\) 增加：这也可由其非负系数公式逐项比较得到。等式使用
\(b_A=c_A\rho\)；倒数第二步使用（48.7）。最后
\(\rho+(1-\rho)^2=1-\rho+\rho^2<1\)。结合（48.5），得到范数恰为 \(c_A\)。每个有限坐标的加权误差都严格小于 \(c_A\)，而整个上确界仍等于 \(c_A\)。

**必要性。** 假设 \(W_N(A)<1\)。对负前缀写
\[
F_N(z)=1-A\sum_{i=1}^{N}z^i,\qquad
P_N(z)=\sum_{k\ge0}p_kz^k
=\sum_{j=0}^{N-1}\frac{Az^j}{F_N(z)^{j+1}},
\tag{48.10}
\]
后一个式子是（48.4）的首行符号变换。在 \(|z|\le\rho^{-1}\) 上，
\(A\sum_i|z|^i\le W_N(A)<1\)。因为和式有限且严格小于一，可以再选
\(R>\rho^{-1}\)，使 \(A\sum_iR^i<1\)。于是 \(F_N\) 在整个 \(|z|\le R\) 上无零点，（48.10）解析，Cauchy 系数界给
\[
0\le p_k\le C_RR^{-k}=o(\rho^k).
\]
所以首行误差为
\[
\rho^k[u_k(A)-p_k]
=c_A+\rho^{2k}\left(b_A-\frac{p_k}{\rho^k}\right)
>c_A
\]
对充分大的有限 \(k\) 成立。由（48.6），所有允许的同截止来源都有至少这么大的该坐标误差。因此距离严格大于 \(c_A\)。

充分和必要两部分合并为
\[
\boxed{
\operatorname{dist}_\rho(T^\star,\mathcal J_{A,N})=c_A
\quad\Longleftrightarrow\quad
W_N(A)\ge1
\quad\Longleftrightarrow\quad
\rho^N\le1-\rho.
}
\tag{48.11}
\]
以下严格有限坐标估计只针对所构造的全负前缀，不声称每个任意最近点都具有这个性质。精确最小允许截止长度因而为
\[
\boxed{
N_{\min}(A)
=\left\lceil\frac{\log(1-\rho)}{\log\rho}\right\rceil,
\qquad\rho=\lambda(A)^{-1}.
}
\tag{48.12}
\]
两个对数均为负，商严格为正，故该整数至少为一。特别地，对每个 \(A>0\)，某个有限负前缀已经取得角点到全部有限来源像的距离 \(c_A\)。零截止只有零来源，其误差为 \(A>c_A\)。\(N=1\) 时（48.11）退化为 \(\rho\le1/2\)，也就是第48.4节单点特例的 \(A\ge1/2\)。

例如 \(A=1/6\) 时 \(\rho=2/3\)、\(c_A=1/10\)，最小截止为三。截止二的共同最优负前缀已经在 \((n,k)=(0,11)\) 给出精确超额
\[
\rho^{11}|T^\star(0,11)-T_{A,2}(0,11)|-c_A
=\frac{30677}{104603532030}>0.
\]
该值可直接由首行递推以有理数计算；它是上面一般必要条件的一个有限见证。\(A=1/20\)、\(\rho=4/5\) 时最小截止为八；必要证明只保证不足截止的超额最终出现，不承诺在任意预先选定的小深度内出现。

### 48.3 有理前缀的精确达到条件与未达下确界

仍固定同一个 \(A>0\)、临界 \(\rho\) 和截止 \(N\ge1\)，令
\[
\mathcal F^{\mathbb Q}_{A,N}
=\mathcal F_{A,N}\cap\mathbb Q^{\mathbb N},
\qquad
\mathcal J^{\mathbb Q}_{A,N}
=\mathcal E(\mathcal F^{\mathbb Q}_{A,N}),
\qquad S_N=\sum_{i=1}^{N}\rho^{-i}.
\]
这里实际幅度上限 \(A\) 可以无理，来源坐标要求有理。

先证明一个可用于有理近似的实幅度构造。若
\[
b_A<B\le A,\qquad BS_N\ge1,
\tag{48.13}
\]
取长度 \(N\) 的全负 \(B\) 前缀 \(b^{B,N}\)，则
\[
\|T^\star-\mathcal E(b^{B,N})\|_\rho=c_A,
\]
并且每个有限坐标的加权误差严格小于 \(c_A\)。证明需处理同一来源的全部行。

首行 \(p_k=-\mathcal E(b^{B,N})(0,k)\) 在 \(k<N\) 时为 \(u_k(B)\ge B\rho^k\)。递推归纳与前节相同，只将其系数 \(A\) 换成 \(B\)，由 \(BS_N\ge1\) 得
\(p_k\ge B\rho^k\)。目标仍为幅度 \(A\) 的同一个角点，所以
\[
0\le\rho^k[u_k(A)-p_k]
\le c_A+(b_A-B)\rho^{2k}<c_A.
\]
若 \(n\ge1\)、\(m=n+k<N\)，有限依赖给近似坐标为 \(-u_k(B)\)。因 \(u_k(B)\ge B\)，
\[
\begin{aligned}
\rho^{n+k}[u_k(A)-u_k(B)]
&\le\rho^n[c_A+b_A\rho^{2k}-B\rho^k]\\
&\le\rho^n[c_A+(b_A-B)\rho^{2k}]
<c_A.
\end{aligned}
\]
这也与已证临界模量 \(\max\{A-B,c_A\}=c_A\) 一致，但这里已逐式给出所需估计。若 \(n\ge1\)、\(m\ge N\)，则 \(BS_N\ge1\)、\(B\le A\) 蕴含 \(AS_N\ge1\)，故（48.9）的目标粗界仍适用；近似数组非正且绝对值不超过目标，不需要再给不同来源拼接界。最后用（48.5）的首行极限取得范数下界 \(c_A\)。

**严格超出阈值。** 若 \(W_N(A)=AS_N>1\)，则
\[
\max\{b_A,S_N^{-1}\}<A.
\]
取有理数 \(B\) 严格介于两端即可满足（48.13）。因此在当前固定截止内已有有理来源达到 \(c_A\)，每个有限坐标的误差又都严格小于该范数。

**阈值等号且幅度有理。** 若 \(W_N(A)=1\) 且 \(A\in\mathbb Q\)，直接使用有理负前缀 \(b^{A,N}\)。前节证明已给达到性及每个有限坐标的严格不等式。

**阈值等号且幅度无理。** 若 \(W_N(A)=1\) 且 \(A\notin\mathbb Q\)，对任意 \(b\in\mathcal F^{\mathbb Q}_{A,N}\)，每个 \(|b_i|\) 都严格小于 \(A\)。故
\[
V_b:=\sum_{i=0}^{N-1}|b_i|\rho^{-(i+1)}<AS_N=1.
\]
在 \(|z|\le\rho^{-1}\) 上，\(|F_b(z)-1|\le V_b<1\)。严格性和有限和的连续性再次允许选 \(R>\rho^{-1}\)，使
\(\sum_i|b_i|R^{i+1}<1\)。由（48.4）及 Cauchy 估计，
\[
|\mathcal E(b)(0,k)|=O(R^{-k})=o(\rho^k).
\]
这个论证允许任意符号的有理来源。使用反向三角不等式，其首行误差满足
\[
\begin{aligned}
\rho^k|T^\star(0,k)-\mathcal E(b)(0,k)|
&\ge c_A+\rho^{2k}
\left(b_A-\frac{|\mathcal E(b)(0,k)|}{\rho^k}\right)\\
&>c_A
\end{aligned}
\]
对充分大的有限 \(k\) 成立。因此没有有理来源在这个固定截止内达到距离 \(c_A\)。

若 \(W_N(A)<1\)，前节已经排除所有实来源，当然也排除有理来源。综上，得到完整达到性判据
\[
\boxed{
\exists b\in\mathcal F^{\mathbb Q}_{A,N},\qquad
\|T^\star-\mathcal E(b)\|_\rho=c_A
\quad\Longleftrightarrow\quad
\bigl[W_N(A)>1\bigr]
\quad\text{或}\quad
\bigl[W_N(A)=1\text{ 且 }A\in\mathbb Q\bigr].
}
\tag{48.14}
\]

等号无理情形中的不达到不意味着下确界变大。固定截止 \(N\) 时，来源到数组的映射在通常有限维坐标与 \(\|\cdot\|_\rho\) 之间连续：选择
\(\rho<R<(1+A)^{-1}\)，上述统一估计使所有 \(F_b\) 在 \(|z|=R\) 上远离零；（48.4）的有限个有理函数因而随系数一致连续。若 \(b^{(j)}\to b\) 逐坐标，则各非零行生成函数在该圆周上一致收敛。Cauchy 估计给
\[
\rho^{n+k}|\mathcal E(b^{(j)})(n,k)-\mathcal E(b)(n,k)|
\le\rho^n(\rho/R)^k\varepsilon_j,
\qquad\varepsilon_j\to0,
\]
其中对 \(n<N\) 的有限多行取共同 \(\varepsilon_j\)，其余行恒零。取全部坐标的上确界即得范数收敛。即使 \(A\) 无理，也可在每个坐标的区间内部选有理数逼近端点，保持 \(|b_i|\le A\)。故有理来源在 \(\mathcal F_{A,N}\) 中内向稠密，从而在每个固定截止内
\[
\boxed{
\operatorname{dist}_\rho(T^\star,\mathcal J^{\mathbb Q}_{A,N})
=\operatorname{dist}_\rho(T^\star,\mathcal J_{A,N}).
}
\tag{48.15}
\]
因此，当 \(W_N(A)=1\)、\(A\notin\mathbb Q\) 时，下确界为 \(c_A\)，但任意具体有理来源的误差都严格大于它。可具体选有理幅度 \(B_j\uparrow A\)，其负前缀数组在此固定截止中范数收敛到实负前缀。

对任意 \(A>0\)，可以先选有理数 \(B\in(b_A,A)\)，再选足够大的 \(N\) 使 \(BS_N\ge1\)。因为 \(S_N\to\infty\)，这总能完成。因此所有幅度下都有某个有理有限前缀达到 \(c_A\)。若还要指定最小有理截止，它等于（48.12）的 \(N_{\min}\)，仅当该截止恰满足阈值等号且 \(A\) 无理时才增加一；下一截止的 \(W_N\) 严格更大。不需要另行判断哪些阈值幅度是有理数，条件式判据已经完整。

这些结论属于声明的自由数学来源类。若来源必须与某份完整档案、动作合法性或共同外部约束相容，还须验证所构造前缀确属同一记录纤维；上述存在证明本身不赋予制备、读出或替换权限。


**例 48.3a（实／有理截止不同的无理阈值）。** 取
\[
\rho=\frac{\sqrt5-1}{2},\qquad A=\sqrt5-2=2\rho-1.
\]
有 \(\rho^2=1-\rho\)、\(A=(1-\rho)^2/\rho\)。因为 \(\rho>1/2\)，截止一未达阈值，而 \(\rho^2=1-\rho\) 使 \(W_2=1\)；又 \(A\) 无理，故最小实截止为二，最小有理截止为三。截止三可取 \(B=1/5\)：\(3/5<\rho<2/3\) 给 \(B<A\)，且 \(b_A=A\rho/(1+\rho)=5\rho-3<1/5\)，后一个不等式由 \(\rho<16/25\) 得到；这些有理界可直接代入严格递增的 \(x^2+x-1\) 核对。同时
\[
S_3=\rho^{-1}+\rho^{-2}+\rho^{-3}=4\rho+6>5,
\]
故 \(BS_3>1\)。这是（48.13）—（48.14）的精确应用，不由浮点等号判定。

### 48.4 单坐标来源的完整特例与二分之一阈值

本节固定 \(A>0\)、\(\rho=\lambda(A)^{-1}\)，令
\(T^\star=\mathcal E(-A\mathbf1)\)。对 \(0<B\le A\) 取单点支持边界
\[
b^{(B)}=(-B,0,0,\ldots),\qquad T_B=\mathcal E(b^{(B)}).
\]
直接在递推中对列归纳，得到
\[
T_B(0,k)=-B^{k+1},\qquad T_B(n,k)=0\quad(n\ge1).
\tag{48.16}
\]
首行误差非负，因为 \(u_k(A)\) 包含最高次项 \(A^{k+1}\)，且 \(B\le A\)。因此其加权值恰为
\[
d_k=\rho^k\bigl[u_k(A)-B^{k+1}\bigr]
=c_A+b_A\lambda^{-2k}-B(B/\lambda)^k.
\tag{48.17}
\]
由于 \(B/\lambda\le A/\lambda=(1-\lambda^{-1})^2<1\)，
\(d_k\to c_A\)。其他行误差的上确界恰为
\[
\sup_{n\ge1,k\ge0}\rho^{n+k}u_k(A)=\rho A,
\]
因为 \(\rho^ku_k(A)=c_A+b_A\rho^{2k}\le A\)，且 \((n,k)=(1,0)\) 取到 \(\rho A\)。

从（48.17）可见
\[
d_k\le c_A\ \text{对所有 }k
\quad\Longleftrightarrow\quad
B\ge b_A\ \text{且}\ B\lambda\ge1.
\tag{48.18}
\]
充分性由 \(B(B\lambda)^k\ge b_A\) 直接得到；必要性分别用 \(k=0\)，以及若 \(B\lambda<1\) 则左侧乘积随 \(k\) 趋零。这里始终 \(b_A>0\)。

若 \(A\ge1/2\)，则 \(\lambda\ge2\)，所以
\(\rho A\le c_A\)。选 \(B=A\) 时还满足
\(A>b_A\) 和
\[
A\lambda=(\lambda-1)^2\ge1.
\]
结合首行极限即得
\[
\boxed{
A\ge\tfrac12\quad\Longrightarrow\quad
\|T^\star-T_A\|_\rho=c_A.
}
\tag{48.19}
\]
第47.9节式（47.31）已经证明角点到有限支持来源像的距离为 \(c_A\)，故这个单点支持来源确实是有限来源中的一个最近点。距离的上确界可沿无限深度逼近；这并不妨碍产生近似数组的边界只具有一个非零坐标。

若 \(0<A<1/2\)，则 \(A\lambda<1\)，而任意 \(0<B\le A\) 都满足 \(B\lambda<1\)。由（48.18），这个单点支持族中的每个数组都有某个首行误差严格超过 \(c_A\)。这只排除该特定来源族；第48.2节已经证明，增加前缀截止长度后，所有 \(A>0\) 都有有限来源最近点。

有理来源也可保持这一达到性。\(A=1/2\) 时取有理数 \(B=A\)。\(A>1/2\) 时
\[
\max\{b_A,\lambda^{-1}\}<A,
\]
故可选有理数 \(B\) 严格介于两端。它满足（48.18），仍给
\(\|T^\star-T_B\|_\rho=c_A\)，并且 \(b^{(B)}\) 是幅度不超过 \(A\) 的有理有限来源。此构造不要求在有理来源中精确写下无理数 \(-A\)。这些都是数学来源类中的存在结论；额外的实际来源—档案约束仍需另行验证该有限来源是否合法。

### 48.5 弱组合标签与两阶段几何分布

将原重数标签 \(1\le j\le c_{k,d}\) 参数无关地重新编号为弱组合
\[
g=(g_1,\ldots,g_{2d-1})\in\mathbb N_0^{2d-1},
\qquad \sum_i g_i=k-d+1.
\]
因为非负整数 \(m\) 的长度 \(r\) 弱组合数为
\(\binom{m+r-1}{r-1}\)，此处恰有
\(\binom{k+d-1}{2d-2}\) 个标签。明确取 \(g\) 为这些元组中字典序第 \(j\) 项；其逆为 \(j=1+\#\{h:\sum h_i=k-d+1,\ h<_{\rm lex}g\}\)。这是有限集上的双射；不依赖 \(A,\rho\) 的重新编号保留全部概率和参数统计信息。

令标签空间为所有有限记录 \((d,g)\)，其中 \(d\ge1\)、\(g\) 长度为 \(2d-1\)，并令
\[
D=d,\qquad K=d-1+\sum_i g_i.
\]
原来每个标签的权重是 \(A^d\rho^K\)。使用（48.2）—（48.3），直接计算
\[
\begin{aligned}
\Pr(D=d,G=g)
&=\frac{A^d\rho^{d-1+\sum_i g_i}}{Z}\\
&=(1-t)t^{d-1}
\prod_{i=1}^{2d-1}\bigl[(1-\rho)\rho^{g_i}\bigr].
\end{aligned}
\tag{48.20}
\]
对 \(g\) 求和，每个几何级数均为一，所以
\[
\Pr(D=d)=(1-t)t^{d-1}.
\]
再对 \(d\ge1\) 求和，\(\sum_d(1-t)t^{d-1}=1\)，故联合律归一化。给定 \(D=d\)，坐标 \(G_i\) 相互独立，并各自具有
\(\Pr(G_i=j)=(1-\rho)\rho^j\)。于是
\[
M:=K-D+1\mid D=d
\sim\operatorname{NB}(2d-1,\rho),
\]
这里负二项参数化明确为
\[
\Pr(M=m\mid D=d)
=\binom{m+2d-2}{2d-2}(1-\rho)^{2d-1}\rho^m.
\tag{48.21}
\]
独立性是这份标签律的分解结论，既不预设原递归数组随机，也不声称实际来源系数或测量噪声独立。

几何级数微分给
\(\mathbb E G_i=\rho/(1-\rho)\)、
\(\operatorname{Var}(G_i)=\rho/(1-\rho)^2\)。定义
\[
r=\frac{1+\rho}{1-\rho},\qquad
b=\frac1{1-\rho}.
\]
条件均值与条件方差因此为
\[
\mathbb E[K\mid D]=rD-b,\qquad
\operatorname{Var}(K\mid D)
=\frac{(2D-1)\rho}{(1-\rho)^2}.
\tag{48.22}
\]
全部有限阶矩及固定阶参数微分由第47.16节式（47.67）的局部控制供应：在任一内部点的小邻域选 \(A\le A_+\)、\(\rho\le\rho_+\)，使 \(q_+=\rho_+\lambda(A_+)<1\)，且 \(Z\) 有统一正下界。由 \(d\le k+1\)，每个固定非负整数 \(r,\ell\) 满足
\[
\sum_{d,j}d^r k^\ell A^d\rho^k
\le A_+(k+1)^{r+\ell}q_+^k.
\]
右侧对 \(k\) 可求和，给局部一致绝对收敛、逐项微分和有限矩。光滑坐标变换到 \((\alpha,\eta)\) 后，其任意固定阶导数在缩小的邻域有界，同一控制仍许可下面的 score 计算。

### 48.6 整个内部的正交 Fisher 坐标

参数变换
\[
(A,\rho)\longleftrightarrow(t,\rho),\qquad
A=\frac{t(1-\rho)^2}{\rho}
\]
将严格次临界域双射到 \((0,1)^2\)。取
\[
\alpha=\log t,\qquad\eta=\log\rho,
\]
则参数域是矩形 \(( -\infty,0)^2\)。这是全局坐标声明，不把临界边界纳入参数族。

由（48.20），单个标签的对数概率为
\[
\ell=\log(1-t)+(D-1)\alpha
+(2D-1)\log(1-\rho)+(K-D+1)\eta.
\]
在偏导 \(\partial_\eta\) 中保持 \(\alpha\) 不变，得到两个 score：
\[
S_\alpha=D-\frac1{1-t}=D-\mathbb ED,
\]
\[
S_\eta=K-D+1-\frac{(2D-1)\rho}{1-\rho}
=K-rD+b.
\tag{48.23}
\]
（48.22）给 \(\mathbb E[S_\eta\mid D]=0\)，故
\(\mathbb E[S_\alpha S_\eta]=0\)。此外
\[
\mathbb E[S_\alpha^2]=\frac{t}{(1-t)^2}=:v,
\]
\[
\begin{aligned}
\mathbb E[S_\eta^2]
&=\mathbb E[\operatorname{Var}(K\mid D)]\\
&=\frac{\rho}{(1-\rho)^2}
\left(\frac2{1-t}-1\right)
=\frac{\rho(1+t)}{(1-\rho)^2(1-t)}=:R.
\end{aligned}
\]
因此 Fisher 信息矩阵与相应二次型恰为
\[
I_{(\alpha,\eta)}=
\begin{pmatrix}v&0\\0&R\end{pmatrix},
\qquad ds^2=v\,d\alpha^2+R\,d\eta^2.
\tag{48.24}
\]
两个对角量在内部均严格为正。这个对角化来自总次数 score 与条件深度 score 的正交分解。\((\alpha,\eta)\) 并非原来的自然参数，因此不能不加变换就把新坐标中某个对数归一化函数的 Hessian 当作 Fisher 矩阵；（48.23）直接排除了这种混淆。

### 48.7 自然坐标的协方差分解

回到自然参数 \((\theta,\eta)=(\log A,\log\rho)\)。有
\[
\alpha=\theta+\eta-2\log(1-e^\eta),
\qquad d\alpha=d\theta+r\,d\eta.
\]
Fisher 二次型按 Jacobian 运输，故
\[
I_{(\theta,\eta)}
=v\begin{pmatrix}1&r\\r&r^2\end{pmatrix}
+R\begin{pmatrix}0&0\\0&1\end{pmatrix},
\qquad \det I=vR>0.
\tag{48.25}
\]
也可直接由（48.22）及全方差公式验证：
\[
\operatorname{Var}(D)=v,\quad
\operatorname{Cov}(D,K)=rv,\quad
\operatorname{Var}(K)=r^2v+R.
\]
在所指定的自然对数坐标中，\(\nabla\log t=(1,r)\) 是等值曲线的法向；第一项只在这个方向有秩一贡献。沿 \(d\alpha=0\) 的切向，第一项消失，剩余信息由 \(R\,d\eta^2\) 给出。这是明确坐标与度量中的方向陈述，不把 Euclidean 法向或矩阵特征值冒充任意重参数化下不变的数值。

### 48.8 固定幅度下的临界双尺度

本节及随后临界概率极限均固定 \(A>0\)。令
\[
\rho_0=\lambda^{-1},\qquad
\rho=\rho_0e^{-\varepsilon},\qquad
\varepsilon\downarrow0,
\qquad \beta=\frac As.
\]
在边界
\[
r_0=\frac{1+\rho_0}{1-\rho_0}=\frac sA=\beta^{-1},
\qquad \frac{\rho_0}{(1-\rho_0)^2}=\frac1A.
\tag{48.26}
\]
函数 \(t(\varepsilon)\) 在零附近光滑，且
\[
t(0)=1,\qquad
\frac{d\log t}{d\varepsilon}=-r(\rho),
\]
故
\[
1-t=r_0\varepsilon+O_A(\varepsilon^2),\qquad
r=r_0+O_A(\varepsilon).
\tag{48.27}
\]
代入 \(v,R\)，得到
\[
v\sim\frac{A^2}{s^2}\varepsilon^{-2},\qquad
R\sim\frac2s\varepsilon^{-1}.
\tag{48.28}
\]
因此
\[
\varepsilon^2 I_{(\theta,\eta)}
\longrightarrow
\begin{pmatrix}\beta^2&\beta\\\beta&1\end{pmatrix},
\qquad
\det I\sim\frac{2A^2}{s^3}\varepsilon^{-3}.
\tag{48.29}
\]
极限矩阵非零且秩为一；其非零特征值为 \(1+\beta^2\)。记原矩阵两特征值为 \(\Lambda_+\ge\Lambda_->0\)。二维对称矩阵特征值连续性先给
\[
\Lambda_+\sim\left(1+\frac{A^2}{s^2}\right)\varepsilon^{-2}.
\]
再由 \(\Lambda_-\Lambda_+=\det I\)，得到
\[
\boxed{
\Lambda_-\sim
\frac{2A^2}{s(s^2+A^2)}\varepsilon^{-1}.
}
\tag{48.30}
\]
所以两方向都发散，但阶数不同；经 \(\varepsilon^2\) 缩放后只保留较强的一层。这些特征值结论固定使用 \((\log A,\log\rho)\) 坐标。常数依赖 \(A\)，没有宣称在 \(A\downarrow0\) 的联合极限中一致。

### 48.9 深度的精确双几何混合

令
\[
q=\rho\lambda,\qquad p=\rho/\lambda,
\]
严格内部有 \(0<p<q<1\)。由（48.1）
\[
\rho^ku_k(A)=c_Aq^k+b_Ap^k,
\qquad Z=\frac{c_A}{1-q}+\frac{b_A}{1-p}.
\]
定义
\[
w=\frac{c_A/(1-q)}{Z},\qquad
1-w=\frac{b_A/(1-p)}{Z}.
\]
于是深度的完整概率质量为
\[
\boxed{
\Pr(K=k)=w(1-q)q^k+(1-w)(1-p)p^k.
}
\tag{48.31}
\]
因此 \(K\) 恰是两个非负整数几何分布的混合。这里的混合标签是一种概率表示，可通过扩充概率空间实现；不将它解释为实际来源中已经测得的隐藏分支。

### 48.10 临界指数律、矩与联合尺度

继续固定 \(A>0\)，取 \(q=e^{-\varepsilon}\)、
\(p=e^{-\varepsilon}/\lambda^2\)。此时 \(p\) 与一保持统一正距离，故
\[
\varepsilon Z\longrightarrow c_A,\qquad
w\longrightarrow1,\qquad 1-w=O_A(\varepsilon).
\tag{48.32}
\]
若 \(G_q\) 的质量为 \((1-q)q^k\)，则对每个 \(x\ge0\)
\[
\Pr(\varepsilon G_q>x)
=q^{\lfloor x/\varepsilon\rfloor+1}
\longrightarrow e^{-x}.
\]
另一混合分支的总概率趋零，故由（48.31）
\[
\varepsilon K\Rightarrow E,
\qquad E\sim\operatorname{Exp}(1).
\tag{48.33}
\]
分布收敛本身不保证矩收敛；这里直接计算矩。几何级数给
\[
\mathbb EG_q=\frac q{1-q},\qquad
\mathbb EG_q^2=\frac{q(1+q)}{(1-q)^2}.
\]
利用混合公式，\(p\) 分支的前两阶矩有界，得到
\[
\varepsilon\mathbb EK\longrightarrow1,\qquad
\varepsilon^2\mathbb EK^2\longrightarrow2,\qquad
\varepsilon^2\operatorname{Var}(K)\longrightarrow1.
\tag{48.34}
\]

下面证明同一标签中 \(D,K\) 的联合结论，而非拼接两个边缘极限。记
\[
W=K-\mathbb E[K\mid D]=K-rD+b.
\]
则 \(\mathbb E[W\mid D]=0\)、\(\mathbb EW^2=R\)，从而
\[
K-r_0D=W+(r-r_0)D-b.
\]
交叉项因条件均值为零而消失，因此
\[
\mathbb E[(K-r_0D)^2]
=R+\mathbb E[((r-r_0)D-b)^2].
\tag{48.35}
\]
几何次数律给
\[
\mathbb ED=\frac1{1-t},\qquad
\mathbb ED^2=\frac{1+t}{(1-t)^2}.
\]
由（48.27），\(r-r_0=O_A(\varepsilon)\)、
\(\mathbb ED^2=O_A(\varepsilon^{-2})\)，而 \(b\) 有界。
故（48.35）第二项为 \(O_A(1)\)，第一项为 \(O_A(\varepsilon^{-1})\)。结论是
\[
\boxed{\varepsilon^2\mathbb E_\varepsilon[(K-r_0D)^2]\longrightarrow0.}
\tag{48.36}
\]
这里的 \(L^2\) 陈述就是上述逐律二阶矩趋零。每个期望均在对应 \(\varepsilon\) 的标签律下计算；这一表述不要求事先把整族随机变量放在同一概率空间。

由 Markov 不等式，上述残差在当前概率律下依概率趋零。将向量写为 \((\beta\varepsilon K,\varepsilon K)+(-\beta\varepsilon(K-r_0D),0)\)，结合（48.33）、（48.36）及 \(r_0=\beta^{-1}\)，得到联合弱收敛
\[
\boxed{(\varepsilon D,\varepsilon K)\Rightarrow(\beta E,E).}
\tag{48.37}
\]
由于 \(E>0\) 几乎处处，连续映射定理还给
\[
\frac{D}{K}\longrightarrow\beta\quad\text{依概率，在 }K>0\text{ 上}.
\tag{48.38}
\]
精确地，可先在 \(K=0\) 时将比值任意定义为零；因为
\(\Pr(K=0)=A/Z\to0\)，这个定义不影响极限，条件于 \(K>0\) 的版本也成立。比值结论来自同一联合律及分母极限严格正，不能只用两个期望的比值来替代证明。

这些是从严格内部得到的尺度极限，并未构造 \(t=1\) 的临界标签概率。指数极限也说明深度并不集中在均值附近：其变异系数趋于一。

### 48.11 固定深度的次数高斯涨落

固定 \(A>0\)，对每个整数 \(k\) 使用条件律
\[
\Pr(D=d\mid K=k)=\frac{c_{k,d}A^d}{u_k(A)}.
\]
这一条件律与 \(\rho\) 无关。它的矩母函数在所有有限复数 \(z\) 处都是有限和：
\[
M_k(z)=\mathbb E[e^{zD}\mid K=k]
=\frac{u_k(Ae^z)}{u_k(A)}.
\tag{48.39}
\]
为了从闭式推导统一局部展开，选取 \(A\) 的小复邻域，避开
\(w^2+4w=0\) 的两个零点。选择在 \(w=A\) 取正值的解析平方根
\(s(w)\)，并令
\[
\lambda(w)=\frac{w+2+s(w)}2,\quad
c(w)=\frac{w\lambda(w)}{\lambda(w)+1},\quad
b(w)=\frac w{\lambda(w)+1}.
\]
缩小 \(z=0\) 的固定圆盘，使 \(w=Ae^z\) 留在上述邻域，
\(|\lambda(w)|\ge L>1\)，且 \(c(w)\ne0\)。这些要求由连续性和
\(A>0\)、\(\lambda(A)>1\)、\(c(A)>0\) 同时保证。

有限递推解的代数恒等式在此邻域仍给
\[
u_k(Ae^z)
=c(Ae^z)\lambda(Ae^z)^k
\left[1+\frac{b(Ae^z)}{c(Ae^z)}\lambda(Ae^z)^{-2k}\right].
\]
方括号内的误差在圆盘上一致为 \(O_A(L^{-2k})\)。对足够大 \(k\)，它的模小于 \(1/2\)，可以取以零为基点的解析对数。明确写 \(e_k(z)=[b(Ae^z)/c(Ae^z)]\lambda(Ae^z)^{-2k}\)，并取
\[
E_k(z)=\log(1+e_k(z))-\log(1+e_k(0)).
\]
其解析对数由 \(|e_k|<1/2\) 的幂级数选定。再对 \(c,\lambda\) 选局部解析对数，得到在固定小圆盘内
\[
\log M_k(z)=k\ell(z)+a(z)+E_k(z),
\tag{48.40}
\]
其中
\[
\ell(z)=\log\lambda(Ae^z)-\log\lambda(A),\qquad
a(z)=\log c(Ae^z)-\log c(A),
\]
且 \(\ell(0)=a(0)=E_k(0)=0\)，
\(\sup|E_k|\le C_A\gamma^k\)、\(0<\gamma<1\)。在更小圆盘上使用 Cauchy 导数估计，\(E_k\) 的任意固定阶导数也有这样的指数上界。这一步明确保证了根分离和导数余项控制。

由 \(d\log\lambda/dA=1/s\)，计算
\[
\ell'(0)=\frac As=:\beta,
\]
\[
\ell''(0)=A\frac d{dA}\left(\frac As\right)
=\frac As-\frac{A^2(A+2)}{s^3}
=\frac{2A^2}{s^3}=: \sigma_A^2>0.
\tag{48.41}
\]
对（48.40）在零点求导，得到
\[
\mathbb E[D\mid K=k]=\beta k+a'(0)+O_A(\gamma^k),
\]
\[
\operatorname{Var}(D\mid K=k)
=\sigma_A^2k+a''(0)+O_A(\gamma^k).
\tag{48.42}
\]
若需一个显式均值常数，
\(a'(0)=1+A/[s(\lambda+1)]\)。二阶常数不影响随后极限。

对任意固定实数 \(u\)，代入
\(z=iu/\sqrt{\sigma_A^2k}\)。局部 Taylor 展开给
\[
k\bigl(\ell(z)-\beta z\bigr)
=-\frac{u^2}{2}+O_{A,u}(k^{-1/2}),
\qquad a(z)=O_{A,u}(k^{-1/2}).
\]
因此标准化变量的特征函数趋于 \(e^{-u^2/2}\)，由特征函数连续性定理
\[
\boxed{
\frac{D-\beta k}{\sqrt{\sigma_A^2k}}
\Bigm|\;K=k
\Rightarrow N(0,1).
}
\tag{48.43}
\]
也可用精确条件均值居中，因两种中心相差 \(O_A(1)\)。这完整证明固定深度的高斯结论，无需把尚未核对的文献条件当作前提。

（48.43）与（48.37）研究不同抽样协议。固定深度时，次数在 \(\beta k\) 周围只有 \(\sqrt{k}\) 量级涨落；对全部深度作临界混合时，深度本身在 \(\varepsilon^{-1}\) 尺度上仍有非退化指数涨落。两种结论相容，不能将其中一个替换成另一个。复邻域和误差常数均依赖固定的 \(A>0\)，不声称在 \(A\downarrow0\) 时一致。

### 48.12 齐次多项式的精确范数与整数移动峰

本节再次固定 \(0<\rho<1\)，令
\[
h_d=\sup_{k\ge d-1}\rho^kc_{k,d}.
\]
定义连续齐次多项式的范数为
\(\|H_d\|=\sup_{\|a\|_\infty\le1}\|H_d(a)\|_\rho\)。
系数绝对值和给
\[
\rho^{n+k}|H_d(a)(n,k)|
\le\rho^n\rho^kc_{k,d}\|a\|_\infty^d,
\]
故 \(\|H_d\|\le h_d\)。取同一个单位输入
\(a=-\mathbf1\)，（46.3）、（46.6）、（46.8）的共同符号性质给
\(H_d(-\mathbf1)(0,k)=-c_{k,d}\)。因此
\[
\boxed{\|H_d\|=h_d.}
\tag{48.44}
\]
这是多项式范数；不额外声称任意极化后的多线性算子范数都相同。

令 \(r_d=2d-1\)、\(m=k-d+1\)。由（48.2）逐项相除，得到
\[
\frac{\rho^kc_{k,d}}{m_d}
=\binom{m+r_d-1}{r_d-1}(1-\rho)^{r_d}\rho^m.
\]
所以
\[
\boxed{\frac{h_d}{m_d}
=\max_{m\ge0}\Pr\{\operatorname{NB}(r_d,\rho)=m\}.}
\tag{48.45}
\]
最大值存在，因为多项式乘几何衰减趋零。

为精确定位众数，记右边质量为 \(p_m\)。比值为
\[
\frac{p_{m+1}}{p_m}
=\rho\frac{m+r_d}{m+1}.
\]
令
\[
x_d=\frac{(r_d-1)\rho}{1-\rho}
=\frac{(2d-2)\rho}{1-\rho}.
\]
上述比值大于、等于或小于一，分别等价于
\(m+1<x_d\)、\(m+1=x_d\)、\(m+1>x_d\)。因此：

- \(d=1\) 时 \(x_d=0\)，唯一众数是 \(m=0\)，且 \(h_1=1\)。
- \(d\ge2\) 且 \(x_d\notin\mathbb Z\) 时，唯一众数为 \(\lfloor x_d\rfloor\)。
- \(x_d\) 为正整数时，恰有两个众数 \(x_d-1,x_d\)。

故任一最大深度满足
\[
k_d=d-1+m_d^{\mathrm{mode}}
=\frac{1+\rho}{1-\rho}(d-1)+O(1),
\tag{48.46}
\]
这里 \(m_d^{\mathrm{mode}}\) 表示一个众数，与系数总和 \(m_d\) 不是同一个符号对象。峰值深度随次数线性逃向无穷；这是对深度索引的极大化，不是物理运动轨迹。

### 48.13 Stirling 常数、精确半径与临界截断误差

给出（48.45）的精确渐近证明。令 \(a=2d-2\to\infty\)，选择任意众数
\[
m=\frac{a\rho}{1-\rho}+O(1),\qquad n=a+m.
\]
该点质量可写为
\[
p_m=(1-\rho)\binom{n}{a}(1-\rho)^a\rho^m.
\]
Stirling 公式对 \(a,m,n\) 同时使用，因三个量均线性增长，给
\[
p_m=(1-\rho)
\sqrt{\frac{n}{2\pi am}}\,
\exp\{F_a(m)\}\bigl(1+O_\rho(a^{-1})\bigr),
\]
其中
\[
F_a(m)=(a+m)\log(a+m)-a\log a-m\log m
+a\log(1-\rho)+m\log\rho.
\]
把 \(m\) 暂作实变量，在
\(m_0=a\rho/(1-\rho)\) 处直接代入得
\[
F_a(m_0)=F_a'(m_0)=0,\qquad
F_a''(m)=-\frac{a}{m(a+m)}.
\]
因为 \(m-m_0=O(1)\)，该区间内二阶导数为 \(O_\rho(a^{-1})\)，Taylor 定理给
\(F_a(m)=O_\rho(a^{-1})\)。同时
\[
\frac{n}{am}\sim\frac1{a\rho}.
\]
因此两个可能众数均满足
\[
\frac{h_d}{m_d}
\sim\frac{1-\rho}{\sqrt{2\pi\rho(2d-2)}}
\sim\frac{1-\rho}{\sqrt{4\pi\rho d}}.
\tag{48.47}
\]
这证明了常数，不只给出中心极限定理的量级。

由（48.2）
\[
A_{\mathrm c}^{\,d}m_d=\frac{1-\rho}{\rho}.
\]
结合（48.47）得到
\[
\boxed{
A_{\mathrm c}^{\,d}h_d
\sim\frac{A_{\mathrm c}}{\sqrt{4\pi\rho d}},
\qquad
\lim_{d\to\infty}h_d^{1/d}
=\frac{\rho}{(1-\rho)^2}
=A_{\mathrm c}^{-1}.
}
\tag{48.48}
\]
所以以原点为中心的 Banach 值齐次级数
\(\sum_{d\ge1}H_d(a)\) 具有精确半径 \(A_{\mathrm c}\)：

- 若 \(r<A_{\mathrm c}\)，由（48.48）及根值判别，
  \(\sum_d h_dr^d<\infty\)，故在 \(\|a\|_\infty\le r\) 上一致绝对范数收敛。
- 若 \(r>A_{\mathrm c}\)，同一个输入 \(a=-r\mathbf1\) 对所有次数同时饱和，
  \(\|H_d(a)\|_\rho=r^dh_d\not\to0\)，故级数在该输入处不收敛。

这一证明给精确原点球半径，不排除特定其他输入或非球形区域上的延拓。

在临界输入 \(a=-A_{\mathrm c}\mathbf1\)，每项范数依（48.48）确实趋零，但不能据此推断级数收敛。事实上可以加强式（47.53）的下界：对每个有限 \(D\ge1\)，
\[
\boxed{
\left\|\mathcal E(a)-\sum_{d=1}^{D}H_d(a)\right\|_\rho
=c_{A_{\mathrm c}}.
}
\tag{48.49}
\]
这里 \(\mathcal E(a)-\sum_{d=1}^D H_d(a)\) 按每个坐标的有限次数多项式定义；没有预设临界 Banach 级数收敛。证明如下。常边界使递归数组及每个齐次部分在 \(n\) 上常值，故范数的最大行权为 \(n=0\)。对固定 \(k\)，余项绝对值是正系数尾和
\[
\rho^k\sum_{d>D}c_{k,d}A_{\mathrm c}^{\,d},
\]
其中 \(d>k+1\) 的项为零。由于 \(D\ge1\)，这个量介于零和仅删除次数一项的余量之间。记此处 \(A=A_{\mathrm c}\)、\(\lambda=\rho^{-1}\)，使用 \(c_{k,1}=1\) 与（48.1）得
\[
\begin{aligned}
\rho^k[u_k(A)-A]
&=c_A+b_A\rho^{2k}-A\rho^k\\
&\le c_A,
\end{aligned}
\]
因为 \(b_A\rho^k\le b_A<A\)。于是范数至多 \(c_A\)。另一方面，每个固定次数 \(d\) 的
\(\rho^kc_{k,d}A^d\to0\)，而
\(\rho^ku_k(A)\to c_A\)。对固定有限 \(D\)，余量沿 \(k\to\infty\) 趋于 \(c_A\)，故上确界至少为 \(c_A\)，证明等号。

逐坐标上，当 \(D\ge k+1\) 时已经完全相等；范数中却永远留下（48.49）的正误差。区别由不同聚合与移动深度给出，而不是由不同的递归关系造成。

### 48.14 同一系数的关系、完整观察者及有限记录最近点

#### 48.14.1 聚合方式与数学归属

同一 \(c_{k,d}\) 同时承担标签重数、正总权中的次数质量、齐次多项式的系数界及精确范数：对 \(k\) 求和得到 \(m_d\)，对深度取最大得到 \(h_d\)，再以 \(A^d\) 求正和得到 \(Z\)；选定标签律的 score 给 Fisher 几何。非负递归多项式的共同负输入还给有限前缀的逐坐标共同最优者。这些关系连接了同一个递归体／边对象的不同表达，但上确界、求和、度量完成、概率归一化及实际取得仍是不同操作。

第47.13节式（47.51）—（47.53）已有连续齐次多项式、原点解析球与临界残差下界；第48.12—48.13节给精确多项式范数、Stirling 常数及残差等号。第47.9节式（47.26）—（47.43）已有自由来源的有限尾、闭包与剩余尾距离；第48.2—48.3节进一步证明全负角点的有限来源达到性及最小实／有理截止。\(m_d\) 始终是系数总和，\(h_d\) 才是多项式范数；临界逐坐标相等与范数收敛仍分开。

统计结论限于明确选择的标签族。正交 score 的偏导固定正确的新坐标；数值特征值在 \((\log A,\log\rho)\) 中给出；临界渐近固定 \(A>0\)，联合指数极限来自同一内部律，固定深度高斯极限使用另一个条件抽样协议。\(d=1\) 的唯一众数和正整数双众数各有自己的端点结论。

#### 48.14.2 完整档案上的对应实际像

**命题 48.14a（保留全部档案的体／边互逆）。** 取实际共同实现集合 \(\Omega\)，整个已获档案 \(c:\Omega\to\mathcal C\)，以及合法边界 \(a:\Omega\to K_A\)，其中 \(K_A=[-A,A]^{\mathbb N}\)。\(c\) 包含已获内部与外部记录、来源和版本及关系约束、参考和校准、局部钟及其已知共同关系、合法动作及顺序、失败、停止事件、误差与费用合同。只比较下列对应实际像：
\[
\omega\longmapsto(c(\omega),a(\omega)),\qquad
\omega\longmapsto(c(\omega),\mathcal E(a(\omega))).
\]
在这两个像上，
\[
(c,a)\longmapsto(c,\mathcal E(a)),\qquad
(c,T)\longmapsto(c,(T(n,0))_{n\ge0})
\]
互为逆且字面保留同一个 \(c\)。

证明。第43.2—43.4节的有限多项式互逆与相容性，以及（47.1）的实数逐列评价，给 \(\beta\mathcal E(a)=a\)。对实际体像中的 \(T=\mathcal E(a(\omega))\)，有 \(\mathcal E\beta T=T\)。故两个复合都返回原来的同源读数，且每一步仍在对应实际像内。这是（46.34）、（47.44）的完整档案接口应用，不要求独立性，也不把实际像扩成笛卡儿积。任意带噪数组未必满足递归约束，因而不由本命题变成有效来源。证毕。

另行选择的 \(\mathbb P_{\mathrm{lab},A,\rho}\) 不会自行成为 \(\Omega\) 上的律；若需实际概率解释，必须指定可测标签—事件映射以及合法抽样／赋权规则。坐标或范数近似不删除已经取得的原始记录。

#### 48.14.3 同档案有限记录的最近前缀推论

**推论 48.14b（完整有限记录相等且达到临界最近距离）。** 固定 \(A>0\)、\(\rho=1/\lambda(A)\)，目标为 \(a^\star=-A\mathbf1\)、\(T^\star=\mathcal E(a^\star)\)。使用第47.11.1节命题47.6的确定性精确查询协议：从共同完整初始档案 \(c\) 开始，可查询一个边界系数 \(a_i\) 或一个递归坐标 \(\mathcal E(a)(n,k)\)；动作、可见元数据、顺序、费用、记录追加及停止／输出完全由 \(c\) 和此前可访问的完整记录决定。比较的合法实现必须服从相同观察／准备规则。不另供独立区分来源的身份、全局支撑证书、非局部尾 oracle、来源相关时钟、随机性或未计入的输出后查询。

假设协议在 \(a^\star\) 上经过有限次查询停止。沿这条已终止路径令
\[
M=\max\left(\{i:a_i\text{ 被查询}\}
\cup\{n+k:(n,k)\text{ 被查询}\}\right),
\]
空集时规定 \(M=-1\)。对每个满足
\[
N\ge\max\{1,M+1,N_{\min}(A)\}
\]
且其全负前缀 \(b^{A,N}\) 是**同一初始档案纤维内、具有相同协议合同的合法实现**的整数 \(N\)，整份有限执行有完全相同的 transcript、先后次序、保留元数据、停止决定及输出，而
\[
\|\mathcal E(a^\star)-\mathcal E(b^{A,N})\|_\rho=c_A.
\]
这对数组的每个有限加权坐标误差都严格小于 \(c_A\)。若所有充分长的这些前缀在同一纤维中合法，则有无穷多个不同的有限来源最近点产生相同的已终止完整记录。最小的存在结论只要求至少一个越过上述阈值的合法 \(N\)；自由立方体成员身份不保证这种合法性。

证明。在固定的已终止目标执行中，每个系数查询只依赖自身下标，每个递归坐标查询仅依赖下标至 \(n+k\) 的边界，这是引理43.5及（47.1）的有限多项式依赖。所有这些下标均小于 \(N\)，而全负前缀与 \(a^\star\) 在该范围完全相同。

对整份执行归纳，而非只对数值答案归纳：共同初始完整记录相同；若此前记录相同，协议合同给同一下一动作和可见元数据；若为查询，有限依赖给相同答案，规则遂追加相同事件、费用／钟读数及其它保留记录；若为停止，则在同一步停止并给相同输出。因此归纳达到同一个终止档案。空查询时 \(M=-1\)，只剩共同初始档案上的相同停止／输出规则；所取 \(N\ge\max\{1,N_{\min}\}\) 仍满足结论。

由第48.2节的截止定理，\(N\ge N_{\min}\) 给恰好 \(c_A\) 的范数距离。首行估计（48.8）及高行两个反对角区域的估计（48.9）给每个有限坐标的严格界。更长的合法 \(N\) 保留有限依赖及阈值不等式；两个不同截止的前缀在较小截止的首列坐标上已不同，故对应数组不同。这证明所述无穷族。证毕。

对任意共同输出 \(\widehat T\in Y_\rho\)，三角不等式立即给
\[
\max\{\|\widehat T-\mathcal E(a^\star)\|_\rho,
\|\widehat T-\mathcal E(b^{A,N})\|_\rho\}\ge c_A/2.
\]
这是（47.46）的二来源误差障碍，使用达到最近距离的更精确见证；它不是 \(a^\star\) 上的点态下界，不证明 minimax 最优性或达到下界的算法。构造在有限终止路径已知后选择 \(N\)，不预设对所有来源有效的统一停止步数。

若 \(A\) 有理，精确匹配的负前缀本身有理，在相同合法性假设下仍适用。若 \(A\) 无理，第48.3节的有理达到定理不给一般的精确记录重放：查询 \(a_0\) 的协议记录无理值 \(-A\)，任何有理来源均不能复制。某个具体协议可以要求更少信息，但没有普遍有理重放结论。这两个有限记录实现也不对所有后续实验等价：若随后查询 \(a_N\) 合法，目标回答 \(-A\)，有限前缀回答零。

#### 48.14.4 任务误差及未涵盖的范围

**推论 48.14c（同域 Lipschitz 任务的直接误差传递）。** 设任务 \(f\) 的声明域同时含 \(T^\star,T_{A,N}\)，目标度量为 \(d_Z\)，且该同一任务在该域满足统一界 \(d_Z(f(T),f(S))\le L\|T-S\|_\rho\)。对上述最近前缀，有
\[
d_Z(f(T^\star),f(T_{A,N}))\le Lc_A.
\]
证明。将已证范数等号代入该任务的 Lipschitz 假设即可；标量任务的 \(d_Z\) 可取绝对值。证毕。

任意阈值、新操作、变化的来源纤维和未来自适应策略仍须各自的裕度、连续性、定义域、交换与取得条件。精确表示运输来自命题48.14a的实际像互逆，不由正的近似误差推出。常值无限来源 \(-A\mathbf1\) 可有很短的符号描述，却不属于任何有限支持类；最近点定理计量的是初始前缀截止。

任意目标的最近点存在性／唯一性、任意散布稀疏支撑的最优值、有理位成本、随机协议、最优 minimax 方法、实际制备，以及 \(A\downarrow0\) 的统一临界极限，均不在本单元中断言或证明。这里没有给这些问题作全项目或全球未解判定。上述关系是同一模型下的普通数学综合，不从统计标签、递归深度或完成化名称推出物理时空、波动规律或普遍信息本体。

#### 48.14.5 供应接口及成熟方法

[Context43 的完整正文](https://github.com/the-omega-institute/trureturing/blob/419ffbbb196cb45f824532f8f2c16c12e3268286/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#L8704)中，定理43.2、43.4、引理43.5及第43.6节分别拥有自由递推、多项式逆、形式行恒等式、有限依赖与完整档案接口；这些有限整系数恒等式的实／复评价见第46.1、47.1、47.9节。

[Context46 的完整正文](https://github.com/the-omega-institute/trureturing/blob/bb03a0b32070a52ae10b180158ad1e4092698f99/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#L10922)的（46.3）、（46.6）、（46.8）、（46.12）分别承担非负变换、共同负角点、次数系数质量与两根闭式；（46.34）承担有限对应实际像的完整记录合同。

[Context47 的完整正文](https://github.com/the-omega-institute/trureturing/blob/5b98d110202357e03dbb0861fa2a393f0dc348c9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#L11516)的（47.26）—（47.43）拥有有限来源尾部、自由来源闭包与距离；（47.44）拥有整个观察者；命题47.6及（47.46）拥有确定性有限记录协议；（47.51）—（47.52）拥有实际连续齐次多项式及 Banach 值解析构造；（47.55）—（47.74）拥有选定内部标签律、归一化、局部微分与协方差恒等式。各前提都保持其原来的域与共同实现条件。

标量 Morgan–Voyce 族的成熟归属为 M. N. S. Swamy, “Properties of the Polynomials Defined by Morgan-Voyce,” *The Fibonacci Quarterly* 4(1) (1966), pp.73–81，[原始扫描](https://www.fq.math.ca/Scanned/4-1/swamy.pdf)。印刷第73页式（7）给小写 \(b_k\) 的初值与递推，第79页式（40）给二项式系数，本节 \(u_k(A)=A b_k(A)\)。第80页式（42b）的旧缩放 Chebyshev 表示不同于 NIST DLMF [18.5.3](https://dlmf.nist.gov/18.5#E3) 的当前第三类 \(V_k\) 约定；后者在版本1.0.28更正中交换了旧 \(V/W\) 标签。按当前约定 \(V_0=1,V_1=2x-1\)，有 \(u_k(A)=A V_k(1+A/2)\)。DLMF [18.12.10](https://dlmf.nist.gov/18.12#E10) 是 \(U_k\) 的生成式，乘 \(1-z\) 后才给 \(V_k=U_k-U_{k-1}\)，其中 \(U_{-1}=0\)。这些归属只承担成熟标量族。

Cauchy 系数／导数估计、Stirling 公式、特征函数连续性定理及连续映射定理是标准工具；本节分别给出所需无零点圆盘、固定复邻域和归一化余项、线性增长的阶乘参数，以及同律联合收敛和正分母条件。Stirling 公式亦见 [DLMF 5.11.3](https://dlmf.nist.gov/5.11#E3)。本节组织属于仓内普通综合推导（`repo-derived`），所述成熟方法保留其归属（`literature-attested`），没有穷尽文献搜索或原创优先权声明。

既有 [AntidiagonalArraySourceSeries 的 `result`](https://github.com/the-omega-institute/trureturing/blob/5b98d110202357e03dbb0861fa2a393f0dc348c9/D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.lean#L78) 只认证其归一化自然数组／源方程假设下的结论，不认证任意有界实／复边界、这里的 Fisher 公式、CLT、Banach 范数或有限前缀达到定理。本节全部新结论由所写普通证明承担，不主张新增 Lean 认证。

## 48.99 追加锚

## 49. 临界递归体边几何：相位刚性、有限证书与实际完成

同一递归关系在有限层级上能够逐坐标恢复边界，但全层数值几何还取决于折扣权重。本节固定临界权重，分类哪些实际来源保留非零尾，证明其余来源何时由有限前缀认证，并识别边界乘积拓扑与数组范数拓扑恰在哪里相容。

有限幅度结果提供共同非负系数包络；加权完成结果提供实际数组、消失尾空间与有限来源距离的框架；全幅度有限截止结果提供实负角点的最小最近前缀。本节消费这些结果，证明复来源上的相位分类、有限证书、复数优化运输和临界拓扑。所有比较均使用一个实际来源生成的完整递归数组。相位表示整数分次上的代数作用；本节没有另设物理时间、量子态或来源概率律。


**供应接口。** 以下都指本卷已经给出陈述与证明的同一递归来源，各自保留原有假设与证明归属。

- 定理43.2及式（43.3）—（43.4）供应整系数坐标多项式与有限首列互逆；定理43.4及式（43.6）—（43.9）供应形式行恒等式；引理43.5供应下标至 $n+k$ 的有限依赖；定理43.7供应全相容族的共同实现。定理43.13、命题43.14与推论43.19保留任务、操作和完整档案运输；这里在同一多项式的实／复评价上工作，解析延拓另由下文证明。
- 第46.2—46.3节的式（46.3）、（46.4）、（46.6）供应非负列递推、正标量递推与共同全负极端；式（46.8）、（46.9）、（46.12）分别供应系数公式、两个初值与二阶递推、两根闭式。Morgan–Voyce 标量归属保持在该供应接口内。
- 第47.1—47.2节供应加权有界空间及临界阈值；第47.5节式（47.16）拥有实径向精确模量；第47.9节式（47.26）—（47.43）拥有实有限来源的消失尾、闭包与距离。第47.10节式（47.44）及第47.11.1节命题47.6供应完整联合档案与同记录确定性有限查询合同。
- 第48.2节式（48.6）—（48.12）拥有实负前缀的共同优化、全幅度截止阈值、严格有限坐标界及最小截止；第48.3节式（48.13）—（48.15）拥有实有理来源的达到条件与相同下确界。命题48.14a、推论48.14b—48.14c保留实际像、有限记录及同域任务运输条件。

下文的新证明承担复相位刚性、有限精确与稳健证书、两种共同无零点圆盘、所有行的统一尾界、同前缀逼近、复数支配与相位运输，以及实际来源的达到分类和临界拓扑；实闭包、实截止与实径向估计沿用上述所有者。

### 49.1 同一实际递归像与临界幅度合同

固定实数 $A>0$，令
$$
\lambda=\frac{A+2+\sqrt{A^2+4A}}2,
\qquad \rho=\lambda^{-1}\in(0,1),
\qquad A=\frac{(1-\rho)^2}{\rho}.
$$
分别考虑
$K_A^{\mathbb R}=[-A,A]^{\mathbb N}$ 与
$K_A^{\mathbb C}=\{a\in\mathbb C^{\mathbb N}:|a_i|\le A\}$。
每个来源 $a$ 生成唯一数组
$$
T_a(n,0)=a_n,\qquad
T_a(n,k+1)=T_a(n+1,k)-\sum_{j=0}^{k}T_a(n,j)a_{k-j}.
\tag{49.1}
$$
记 $\mathcal E(a)=T_a$。对列归纳，所有坐标均为输入有限前缀的整系数多项式，且 $T_a(n,k)$ 只依赖下标至 $n+k$ 的边界。因此这是实际递归数组，不是任意环境数组。第一列提取 $\beta(T)_i=T(i,0)$ 与 $\mathcal E$ 只在对应实际像上互逆。

对 $\mathbb F=\mathbb R$ 或 $\mathbb C$，先在环境加权有界数组空间
$$
B_\rho^{\mathbb F}=\left\{T:\mathbb N^2\to\mathbb F:
\sup_{n,k\ge0}\rho^{n+k}|T(n,k)|<\infty\right\}
$$
上定义
$$
\|T\|_\rho=\sup_{n,k\ge0}\rho^{n+k}|T(n,k)|,
\quad
\tau_N(T)=\sup_{n+k\ge N}\rho^{n+k}|T(n,k)|,
\quad
L_\rho(T)=\lim_{N\to\infty}\tau_N(T).
\tag{49.2}
$$
尾量随 $N$ 递减，故该非负极限存在且有限。令
$B_{\rho,0}=\{T\in B_\rho^{\mathbb F}:\tau_N(T)\to0\}$，令 $I_A^{\mathbb F}=\mathcal E(K_A^{\mathbb F})$，
$J_A^{\mathbb F}$ 为其中由有限支持边界生成的实际数组，$\mathbb F=\mathbb R$ 或 $\mathbb C$。有限支持修饰边界，生成的数组可以有无限多非零坐标。

沿用供应接口的正标量包络
$$
u_0=A,\qquad u_{k+1}=u_k+A\sum_{j=0}^{k}u_j.
$$
三角不等式与列归纳直接给 $|T_a(n,k)|\le u_k$，包括复数来源。全负来源 $a_i=-A$ 在所有坐标达到 $T_a(n,k)=-u_k$。包络的两个初值为 $u_0=A$、$u_1=A+A^2$，并满足
$u_{k+2}=(A+2)u_{k+1}-u_k$；供应接口的两根闭式改写为
$$
u_k=c_A\lambda^k+b_A\lambda^{-k},
\qquad
c_A=\frac{A}{1+\rho},\qquad
b_A=\frac{A\rho}{1+\rho}=c_A\rho.
\tag{49.3}
$$
因此
$\rho^ku_k=c_A+b_A\rho^{2k}\le A$，全部实际数组都属于加权 Banach 空间，且范数不超过 $A$。另外 $u_k$ 随 $k$ 严格增加。

这里的坐标多项式及首列互逆沿用开头的供应接口。标量包络 $u_k(A)$ 是 $A$ 乘以 Morgan–Voyce 多项式；其成熟归属沿用有限幅度节对 Swamy 初值、递推与系数公式的核对。[^criticalphase_swamy] 本节没有把该标量族重新计作新的数学对象。

### 49.2 实际各行的共同解析生成式

对任意复来源 $a\in K_A^{\mathbb C}$，在单位圆盘内定义
$$
C_{n,a}(w)=\sum_{j\ge0}a_{n+j}w^j,
\qquad
F_a(z)=1+zC_{0,a}(z)
=1+\sum_{i\ge0}a_i z^{i+1}.
$$
系数统一有界，故这些级数在单位圆盘解析，且
$|C_{n,a}(w)|\le A/(1-|w|)$，常数不依赖 $n$。
在零点附近 $F_a\ne0$、$|z/F_a(z)|<1$，所以
$$
R_{n,a}(z)=\frac1{F_a(z)}
C_{n,a}\!\left(\frac z{F_a(z)}\right)
\tag{49.4}
$$
在那里解析。利用 $C_{n,a}(w)=a_n+wC_{n+1,a}(w)$，得到
$$
F_a(z)R_{n,a}(z)=a_n+zR_{n+1,a}(z).
$$
比较常数项及 $z^{k+1}$ 系数，恰得（49.1），故
$[z^k]R_{n,a}=T_a(n,k)$。这同时证明所用解析对象确实生成同一个实际数组。

只要某个闭圆盘上 $F_a\ne0$ 且 $|z/F_a|<1$，（49.4）就在该圆盘邻域给实际行生成函数的解析延拓。此处没有从形式可逆性直接假定任意解析收敛；所需不等式在第49.5节证明。

### 49.3 分次相位等变与实数的两种极端

对 $|\zeta|=1$，定义边界与数组上的作用
$$
(D_\zeta a)_i=\zeta^{i+1}a_i,
\qquad
(U_\zeta T)(n,k)=\zeta^{n+k+1}T(n,k).
$$
它们都可逆，逆分别取 $\bar\zeta$，并保持幅度域、有限支持和加权范数。列归纳证明
$$
\boxed{\mathcal E(D_\zeta a)=U_\zeta\mathcal E(a).}
\tag{49.5}
$$
确实，初始列的次数为 $n+1$；后继项 $T(n+1,k)$ 的次数为 $n+k+2$，而卷积每项的两个次数相加为
$(n+j+1)+(k-j+1)=n+k+2$，所以同一个相位因子可从完整递推提出。

记
$$
a_i^\zeta=-A\zeta^{i+1},\qquad
T^\zeta=\mathcal E(a^\zeta).
$$
于是
$$
T^\zeta(n,k)=-\zeta^{n+k+1}u_k.
\tag{49.6}
$$
实来源中只有 $\zeta=1,-1$ 允许所有坐标为实数，分别为
$a_i=-A$ 与 $a_i=A(-1)^i$。因为 $a_0^\zeta=-A\zeta$，不同相位给不同边界和不同实际数组。

### 49.4 整圆等号刚性与有限前缀相位排除

在临界圆周 $z=\rho e^{i\theta}$ 上，有
$$
\begin{aligned}
\operatorname{Re}F_a(\rho e^{i\theta})-\rho
&=\sum_{i\ge0}\rho^{i+1}
\left[A+\operatorname{Re}\bigl(a_i e^{i(i+1)\theta}\bigr)\right].
\end{aligned}
\tag{49.7}
$$
恒等式使用 $1-A\rho/(1-\rho)=\rho$。右边每项非负，并一致绝对收敛。

该和为零，当且仅当每项为零。由于 $|a_i|\le A$，
$\operatorname{Re}(a_i e^{i(i+1)\theta})=-A$ 等价于
$a_i e^{i(i+1)\theta}=-A$。因此圆周等号恰强制
$$
a_i=-A\zeta^{i+1}\quad\text{对所有 }i,
\qquad\zeta=e^{-i\theta}.
$$
反过来，这样的相位来源在对应圆周点确实取等号。

还可以将严格性定位在一个有限前缀。对 $J\ge0$，令
$$
g_J(\theta)=\sum_{i=0}^{J}\rho^{i+1}
\left[A+\operatorname{Re}\bigl(a_i e^{i(i+1)\theta}\bigr)\right],
\qquad\gamma_J=\min_{\theta\in[0,2\pi]}g_J(\theta).
$$
若 $a$ 不是相位来源，则存在有限 $J$ 使 $\gamma_J>0$：

- 若 $|a_0|<A$，直接有 $\gamma_0=\rho(A-|a_0|)>0$。
- 若 $|a_0|=A$，令 $\zeta=-a_0/A$。既然整条边界不是 $a^\zeta$，存在 $j\ge1$ 使 $a_j\ne-A\zeta^{j+1}$。若 $g_j(\theta)=0$，首项先强制 $e^{i\theta}=\zeta^{-1}$，第 $j$ 项随后强制刚被排除的等式，矛盾。连续非负函数在紧圆周上无零点，因此 $\gamma_j>0$。

此外，任意单个幅度缺口 $|a_j|\le A-\delta$、$\delta>0$，都直接给
$g_J(\theta)\ge\delta\rho^{j+1}$ 对所有 $J\ge j$ 成立。这给“首个幅度缺口”的明确量化；全幅度但符号不相容时则由上面的有限相位条件给间隔。

固定这样的前缀和 $\gamma=\gamma_J>0$。对任意另一个来源 $b\in K_A^{\mathbb C}$，只要 $b_i=a_i$ 对 $i\le J$，其余尾部仍可完全任意。由于（49.7）的尾项非负，同一个界给
$$
\operatorname{Re}F_b(\rho e^{i\theta})\ge\rho+\gamma
\quad\text{对所有 }\theta.
$$
因此间隔属于有限前缀及幅度合同，不需要猜测或预知后面的来源信息。

**精确前缀的模长证书。** 若给定 $a_0,\ldots,a_J$，另置
$$
P_J(z)=1+\sum_{i=0}^{J}a_i z^{i+1},\qquad
B_J=\frac{A\rho^{J+2}}{1-\rho},\qquad
G_J=\min_{|z|=\rho}|P_J(z)|-\rho-B_J.
\tag{49.8}
$$
这里 $G_J$ 与前面的实部裕度 $\gamma_J=\min g_J$ 是两份不同证书，不能仅因记号相近而视为同一个数。三角不等式给
$|P_J(z)|\ge1-A\sum_{i=0}^{J}\rho^{i+1}=\rho+B_J>0$，所以 $G_J\ge0$。而且在复来源域有
$$
\boxed{G_J>0\quad\Longleftrightarrow\quad
(a_0,\ldots,a_J)\ne(-A\zeta,-A\zeta^2,\ldots,-A\zeta^{J+1})
\text{ 对每个 }|\zeta|=1.}
\tag{49.9}
$$
证明。固定 $|z|=\rho$，令 $s_i=a_i z^{i+1}$，把模长下界完整写为
$$
|P_J(z)|\ge\operatorname{Re}P_J(z)
=1+\sum_{i=0}^{J}\operatorname{Re}s_i
\ge1-\sum_{i=0}^{J}|s_i|
\ge1-A\sum_{i=0}^{J}\rho^{i+1}
=\rho+B_J>0.
$$
若首尾取等号，则每一步都取等号。因此
$$
\sum_{i=0}^{J}(|s_i|+\operatorname{Re}s_i)=0,
\qquad
\sum_{i=0}^{J}(A-|a_i|)\rho^{i+1}=0.
$$
两和均由非负项组成，必须逐项为零；后一式给每个 $|a_i|=A$，前一式给 $s_i=-|s_i|=-A\rho^{i+1}$。于是
$a_i=-A e^{-\mathrm i(i+1)\theta}$，其中 $z=\rho e^{\mathrm i\theta}$，恰为某个相位前缀。反向代入同一角度即可取等号。若不存在这样的前缀，连续函数在紧圆周上处处严格，故其最小差严格为正。实前缀的首项 $a_0=-A\zeta$ 已使允许相位只能为 $\pm1$，所以等价于同时排除全负与指定交替两个前缀。即使 $J=0$ 也如此：这时两前缀分别为 $(-A)$、$(A)$，严格正证书恰为 $|a_0|<A$。$\square$

同一前缀的任何幅度合法延伸 $b$ 都满足
$$
|F_b(z)|\ge|P_J(z)|-B_J\ge\rho+G_J\qquad(|z|=\rho).
\tag{49.10}
$$
故有限模长证书对全部这些延伸有效。实部证书和模长证书均恰在前缀排除所有相位时严格为正，但数值可不同。它们不要求来源的剩余后缀已被读出。

上述无限圆周刚性也可直接写成
$$
\boxed{|F_a(\rho e^{\mathrm i\theta})|=\rho
\quad\Longleftrightarrow\quad
 a_i=-A e^{-\mathrm i(i+1)\theta}\text{ 对所有 }i.}
\tag{49.11}
$$
确实，$|F|\ge\operatorname{Re}F\ge\rho$，所以模长等号使（49.7）的非负无穷和为零。每一项都不超过该和，故每项都为零；$|a_i|\le A$ 再使 $a_i e^{\mathrm i(i+1)\theta}=-A$ 对每个 $i$ 成立。反向将这一来源代入一致绝对收敛的临界几何级数，得到 $F_a(\rho e^{\mathrm i\theta})=\rho$。这直接处理无限项的共同对齐。

对非相位来源，还可明确定义整圆模长裕度
$$
\gamma_a=\min_{|z|=\rho}\bigl(|F_a(z)|-\rho\bigr)>0.
$$
严格性由（49.11）、紧圆周与连续性得到；任一有限实部正证书还给 $\gamma_a\ge\gamma_J>0$。这是来源相关的裕度，不假定已从有限测量中精确取得它。

### 49.5 共同解析圆盘与所有行的指数尾界

**共同解析估计。** 设一族合法来源在 $|z|\le R<1$ 上均有 $F_b\ne0$，并在其边界满足
$\min_{|z|=R}|F_b(z)|\ge R+\gamma/2$，其中 $R>\rho$、$\gamma>0$ 对全族相同。最大模原理应用于 $z/F_b(z)$，给
$$
\max_{|z|\le R}|z/F_b(z)|\le R/(R+\gamma/2)<1.
$$
严格不等式保证实际行公式（49.4）在包含该闭圆盘的开邻域解析。对圆周上的所有行，
$$
|R_{n,b}(z)|\le\frac1{|F_b(z)|}\frac A{1-|z/F_b(z)|}
=\frac A{|F_b(z)|-R}\le\frac{2A}{\gamma}=:M.
\tag{49.12}
$$
Cauchy 系数估计给
$$
\boxed{|T_b(n,k)|\le M R^{-k}\quad(n,k\ge0).}
\tag{49.13}
$$
令 $q=\rho/R<1$。由于 $R<1$，有 $\rho\le q$，所以
$$
\rho^{n+k}|T_b(n,k)|\le M\rho^nq^k\le Mq^{n+k},\qquad
\boxed{\tau_N(T_b)\le Mq^N.}
\tag{49.14}
$$
这些常数同时控制所有行、所有列和每个合法后缀；逐行消失本身不能替代这份全层估计。

**由有限实部裕度取得圆盘。** 若第49.4节给整圆共同实部下界
$\operatorname{Re}F_b(\rho e^{\mathrm i\theta})\ge\rho+\gamma$，取
$$
r_1=\frac{1+\rho}{2},\qquad D=\frac A{(1-r_1)^2},\qquad
h=\min\left\{\frac{1-\rho}{4},\frac{\gamma}{2(D+1)}\right\},
\qquad R=\rho+h.
\tag{49.15}
$$
统一幅度界给 $|F_b'(z)|\le D$ 于 $|z|\le r_1$。沿固定角度的径向线段积分，得到
$\operatorname{Re}F_b(Re^{\mathrm i\theta})\ge\rho+\gamma-Dh\ge R+\gamma/2$。调和最小值原理把同一实部下界延拓至整个闭圆盘，因此无零点。于是共同解析估计适用。

**由模长裕度显式构造圆盘。** 若只知
$|F_b(\rho e^{\mathrm i\theta})|\ge\rho+\gamma$，使用另一组常数
$$
r_0=\frac12\left(\rho+\frac1{1+A}\right),\qquad
M_A=1+\frac A{(1-r_0)^2},\qquad
r=\rho+\min\left\{r_0-\rho,\frac\gamma{2M_A}\right\}.
\tag{49.16}
$$
临界关系给 $\lambda>1+A$，故
$\rho<r\le r_0<1/(1+A)<1$。对整个闭圆盘，
$|F_b(z)-1|\le Ar/(1-r)<1$，直接保证无零点；这一步没有把“边界无零点”错误地等同于“内部无零点”。统一导数界为
$|F'_b|\le A/(1-r_0)^2=M_A-1$。径向积分再减去半径变化，得到
$$
|F_b(re^{\mathrm i\theta})|-r
\ge|F_b(\rho e^{\mathrm i\theta})|-\rho-M_A(r-\rho)
\ge\gamma/2.
\tag{49.17}
$$
因此同一个共同解析估计以 $R=r$ 给出
$$
\boxed{\tau_N(\mathcal E(b))\le\frac{2A}{\gamma}(\rho/r)^N.}
\tag{49.18}
$$
（49.16）是一份显式构造：若 $A,\rho$ 与已认证的正下界 $\gamma$ 都是给定有理数，全部常数可由有理算术计算。任意实参数或仅仅存在的精确最小值不自动提供可计算或已合法取得的数据。若采用有效实数版本，须供应 $A,\rho,\gamma$ 的有效表示（例如可按要求给出认证有理包围区间），并供应 $\gamma>0$ 及 $r_0-\rho>0$ 的认证正下界；也可从这些区间内选择足够小的正有理增量。精炼与评价能力仍服从第49.7节的取得合同。

两组圆盘构造各自是充分条件，不主张哪一组总是给最优半径。实部下界蕴含同样的模长下界，所以也可统一采用后一组常数，尤其在有理证书中。

若某个有限下标 $j$ 的严格幅度缺口为 $\delta=A-|a_j|>0$，则
$|F_b(z)|\ge\rho+\delta\rho^{j+1}$ 对所有保留该缺口的合法来源成立。故可取
$$
\gamma=\delta\rho^{j+1},\qquad
\tau_N(\mathcal E(b))\le\frac{2A}{\delta\rho^{j+1}}(\rho/r)^N,
\tag{49.19}
$$
其中 $r$ 使用（49.16）。其余坐标完全不受额外限制。

### 49.6 实复来源的完整正尾分类

由（49.14），每个非相位来源都满足 $L_\rho(T_a)=0$。相位来源的幅度等于共同角点包络。固定总次数 $m=n+k$，由于 $u_k$ 递增，最大加权幅度在 $(n,k)=(0,m)$ 取得。取全部 $m\ge N$ 的上确界时，$\rho^m u_m=c_A+b_A\rho^{2m}$ 随 $m$ 递减，所以整个尾部的上确界就是第 $N$ 层的值。因此
$$
\tau_N(T^\zeta)=c_A+b_A\rho^{2N},
\qquad L_\rho(T^\zeta)=c_A.
\tag{49.20}
$$
于是复数情形有精确二分
$$
\boxed{
L_\rho(\mathcal E(a))=
\begin{cases}
c_A,&a_i=-A\zeta^{i+1}\ \forall i\text{，某个 }|\zeta|=1,\\
0,&\text{否则}.
\end{cases}}
\tag{49.21}
$$
实情形特别化为
$$
\boxed{
L_\rho(\mathcal E(a))>0
\Longleftrightarrow
\bigl[a_i=-A\ \forall i\bigr]
\quad\text{或}\quad
\bigl[a_i=A(-1)^i\ \forall i\bigr].
}
\tag{49.22}
$$
在本节固定临界权重与完整幅度立方体中，不存在别的正尾值或别的正尾实际来源。最终全负但前面有幅度或符号缺口的来源属于零尾；周期来源只有恰好符合上述相位规则时才有正尾。

这个分类依赖当前递推、统一幅度 $A$ 及其临界权重 $\rho$。它不声称任意递推或任意加权空间都具有相同刚性。

由分类还得到三个具体边界。第一，任意一个严格幅度缺口都消去临界正尾。第二，对实数的任一极端作任何非平凡且合法的有限坐标改动，都得到零尾来源；两极端相互在无限多个坐标不同。第三，幅度处处饱和仍不充分：$a_j=-A(-1)^j$ 是零尾来源。

因此较强断言“存在 $a_j>-A$ 就必为零尾”是假的：指定交替来源 $a_j=A(-1)^j$ 有 $a_0=A$，其尾仍为 $c_A$。绝对幅度缺口与改变相对全负来源的符号，是不同条件。

### 49.7 同时误差、有限角网格与证书的条件完备性

仍固定同一实际来源 $a\in K_A^{\mathbb F}$ 及其完整取得记录。假设一次合法读取给出有限前缀读数 $\widetilde a_0,\ldots,\widetilde a_J$ 和**同时**成立的误差界
$$
|a_i-\widetilde a_i|\le\eta_i\quad(0\le i\le J).
$$
全部未读系数的幅度界 $|a_i|\le A$ 仍是同一来源合同的一部分。不能用彼此不相容的单项误差事件拼成这个合同。读数与真实来源均可在复数域；实数情形是其限制。

定义有限三角多项式及两个显式常数
$$
H(\theta)=\sum_{i=0}^{J}\rho^{i+1}
 \left[A+\operatorname{Re}\bigl(\widetilde a_i e^{\mathrm i(i+1)\theta}\bigr)\right],
\quad E_J=\sum_{i=0}^{J}\rho^{i+1}\eta_i,
\quad \Lambda_J=\sum_{i=0}^{J}(i+1)\rho^{i+1}|\widetilde a_i|.
\tag{49.23}
$$
取圆周上的有限角网格 $\theta_1,\ldots,\theta_m$，其圆周覆盖半径至多 $\Delta$：每个角度到某个网格点的最短圆周距离不超过 $\Delta$。每个网格值均有经认证的下界 $\ell_l\le H(\theta_l)$。可使用经认证的上界 $\Lambda^\sharp\ge\Lambda_J$ 与 $E^\sharp\ge E_J$。若
$$
\boxed{\Gamma:=\min_l\ell_l-\Lambda^\sharp\Delta-E^\sharp>0,}
\tag{49.24}
$$
则这个有限证书保证所有与同一读数和幅度合同相容的完整来源均有
$$
\operatorname{Re}F_a(\rho e^{\mathrm i\theta})\ge\rho+\Gamma
\quad\text{对全部 }\theta.
\tag{49.25}
$$

证明。对真实前缀令
$$
g_J(\theta)=\sum_{i=0}^{J}\rho^{i+1}
 \left[A+\operatorname{Re}\bigl(a_i e^{\mathrm i(i+1)\theta}\bigr)\right].
$$
同时误差界给 $|g_J-H|\le E_J$，逐项求导给 $|H'|\le\Lambda_J$。对任意 $\theta$，取覆盖它的网格点，沿最短圆弧积分，得
$H(\theta)\ge H(\theta_l)-\Lambda_J\Delta\ge\ell_l-\Lambda^\sharp\Delta$。因此 $g_J(\theta)\ge\Gamma$。另一方面，由临界恒等式
$$
\operatorname{Re}F_a(\rho e^{\mathrm i\theta})-\rho
=\sum_{i\ge0}\rho^{i+1}
 \left[A+\operatorname{Re}\bigl(a_i e^{\mathrm i(i+1)\theta}\bigr)\right],
$$
其后缀项逐项非负，保留前缀即得 (49.25)。这是同一个来源的整圆下界，没有将不同角度的不同来源最优值合并。$\square$

现在可在 (49.16) 中取 $\gamma=\Gamma$，得到同一个 $r>\rho$ 及全部相容来源共同的
$$
\tau_N(\mathcal E(a))\le\frac{2A}{\Gamma}(\rho/r)^N.
\tag{49.26}
$$
若数学比较允许将真实前缀保留至 $N>J$ 后置零，所得有限来源与原来源在 $n+k<N$ 的数组坐标完全相同；两者都满足 (49.26)，故其全层范数差至多
$4A\Gamma^{-1}(\rho/r)^N$。这是一份关于真实前缀的数学比较，不代表带误差读数已经取得了真实系数，或该有限来源在当前记录纤维中已可制备。若实际使用 $\widetilde a_i$，还须支付有限头部系数误差并保证替代来源合法。

**条件完备性。** 假定读取协议能够最终访问任意给定有限前缀，并能将该前缀的同时误差界任意精炼；角网格覆盖半径可趋零，网格值下界可以一致趋近真实 $H(\theta_l)$，且使用的 $\Lambda^\sharp$ 保持有界、$E^\sharp\to0$。那么每个非相位来源最终都能得到正证书。

证明。对一个非相位来源，第49.4节给有限 $J$ 排除所有相位前缀；非负函数 $g_J$ 在整圆没有零点，故 $\gamma_J=\min g_J>0$。若网格下界误差至多 $\varepsilon_{\rm eval}$，则
$$
\Gamma\ge\gamma_J-2E^\sharp-\varepsilon_{\rm eval}
-\Lambda^\sharp\Delta.
$$
访问到这一前缀后，将后三项精炼至总和小于 $\gamma_J$，即得正证书。协议须有到达所需见证前缀及精炼同时误差、网格与数值下界的能力；见证前缀取得后不必继续增长下标，只需将该前缀的误差及评价精度精炼到上述严格界内。只重复读取一个仍与相位相容的短前缀并不充分。对相位来源，每个 $g_J$ 都在其相位角取零，故任何有效同时误差合同都不可能给出正证书。$\square$

这些条件不承诺统一停止深度或统一精度预算：非相位缺口可以任意小、任意晚。若误差合同只在一个概率至少为 $1-\delta$ 的共同事件上成立，以上证书在该事件上可靠，因此“输出了错误正证书”的无条件概率至多 $\delta$；不能由此声称条件于输出证书后的错误概率也至多 $\delta$。多次自适应尝试须使用同时覆盖整段尝试的误差合同或另作错误预算。

### 49.8 三个全有理的实际尾证书

固定 $A=1/2,\rho=1/2$，则 (49.16) 的
$$
r_0=7/12,\qquad M_A=97/25.
$$

若任意来源具有 $a_j=0$，可取
$\gamma=2^{-(j+2)}$，故
$$
\boxed{
\tau_N(\mathcal E(a))
\le 2^{j+2}
\left(\frac{388\,2^j}{388\,2^j+25}\right)^N.
}
\tag{49.27}
$$
例如 $j=0$ 时为 $4(388/413)^N$；$j=6$ 时为
$256(24832/24857)^N$。这些界对其余任意系数统一，未要求最终常量。

再看没有任何严格幅度缺口的有限前缀
$a_0=-1/2,a_1=1/2$。在 $z=e^{\mathrm i\theta}/2$、$x=\cos\theta$ 下，
$$
\left|1-\frac14e^{\mathrm i\theta}
+\frac18e^{2\mathrm i\theta}\right|^2
=\frac12(x-9/16)^2+\frac{343}{512}
>\left(\frac{13}{16}\right)^2.
$$
其未指定后缀在临界圆上的绝对和至多 $B_1=1/8$，因此
$G_1>13/16-1/2-1/8=3/16$。保守取 $\gamma=3/16$，得到
$$
\boxed{
\tau_N(\mathcal E(a))\le\frac{16}{3}
\left(\frac{1552}{1627}\right)^N
}
\tag{49.28}
$$
对该前缀的全部允许后缀成立。它给一个完全由有限饱和系数的符号不相容造成的统一消失尾证书。

**有理稳健实例。** 取 $A=\rho=1/2$、$J=1$、$(\widetilde a_0,\widetilde a_1)=(-1/2,1/2)$，以及同时误差 $\eta_0=\eta_1=1/100$。写 $x=\cos\theta$，则
$$
H(\theta)=\frac14-\frac14x+\frac14x^2
=\frac14(x-1/2)^2+\frac3{16},
\qquad E_J=\frac3{400}.
$$
直接使用整圆平方证书即可取
$\Gamma=3/16-3/400=9/50>0$，不需要数值优化角网格。按 (49.16)，$r=1/2+9/388=203/388$，所以同一读数合同的全部合法延伸同时满足
$$
\boxed{\tau_N(\mathcal E(a))\le\frac{50}{9}
\left(\frac{194}{203}\right)^N.}
\tag{49.29}
$$
证明使用的恒等式与常数均为有理数等式；有限近似的三角函数读数本身不构成认证。

### 49.9 有限来源闭包与同前缀的实际逼近

实来源的闭包与距离框架沿用开头的第47.9节供应；下面给复数扩张及同一前缀控制下的定量逼近。每个有限支持边界都不是相位来源，故其数组属于 $B_{\rho,0}$。此外，实际像 $I_A^{\mathbb F}$ 在加权范数下闭：若 $\mathcal E(a^{(j)})\to T$，则第一列逐项收敛到 $a_n=T(n,0)$，其幅度仍不超过 $A$；每个数组坐标是有限输入多项式，故逐坐标极限必为 $\mathcal E(a)$。

加权消失尾空间也是闭的。若 $T_j\to T$ 且各 $L_\rho(T_j)=0$，则
$\tau_N(T)\le\|T-T_j\|_\rho+\tau_N(T_j)$；先固定大 $j$，再令 $N\to\infty$，即得 $L_\rho(T)=0$。所以
$\overline{J_A^{\mathbb F}}\subseteq I_A^{\mathbb F}\cap B_{\rho,0}$。

反向有明确的实际来源逼近。对非相位 $a$，取第49.4节的有限前缀及统一常数 $M,q$。对 $N>J$，令 $a^{[N]}$ 保留下标 $i<N$ 的原值，其余置零。它与 $a$ 共享所需前缀，两者均满足（49.14）。当 $n+k<N$ 时有限依赖给数组坐标精确相同；其余坐标差至多为两份尾界之和。因此
$$
\boxed{
\|\mathcal E(a)-\mathcal E(a^{[N]})\|_\rho\le2Mq^N
\qquad(N>J).
}
\tag{49.30}
$$
这证明
$$
\boxed{
\overline{J_A^{\mathbb C}}
=I_A^{\mathbb C}\cap B_{\rho,0}
=I_A^{\mathbb C}\setminus\{T^\zeta:|\zeta|=1\}.
}
\tag{49.31}
$$
实版本删除的只是两条相位数组。此处实际截断的是边界，重建数组通常仍有无限多非零坐标。

### 49.10 从实数最小截止到复数相位的最近有限来源

记 $\mathcal F_{A,N}^{\mathbb F}=\{b\in K_A^{\mathbb F}:b_i=0\ (i\ge N)\}$，其中 $N\ge1$ 是前缀截止长度；它不是任意散布非零项的支持基数。取实负前缀 $b^{A,N}_i=-A\mathbf1_{i<N}$，并令
$p_{n,k}=-\mathcal E(b^{A,N})(n,k)\ge0$。

**已有实数优化的精确供应。** 开头所列第48.2节全幅度有限截止定理已证明这个同一负前缀逐坐标同时最优，并给
$$
W_N=A\sum_{i=1}^{N}\rho^{-i}
=\frac{1-\rho}{\rho}(\rho^{-N}-1),\qquad
\|T^1-\mathcal E(b^{A,N})\|_\rho=c_A
\quad\Longleftrightarrow\quad W_N\ge1
\quad\Longleftrightarrow\quad\rho^N\le1-\rho.
\tag{49.32}
$$
其达到情形中，每个有限坐标的加权误差都严格小于 $c_A$，首行误差则趋于 $c_A$。这份实数阈值、充分性归纳及必要性的有理行解析证明，均以先前的全幅度截止定理为唯一证明归属；下面只证明复候选不改善它，以及整条相位族怎样运输这个优化问题。

**复数候选的共同支配。** 对 $b\in\mathcal F_{A,N}^{\mathbb C}$，列递推和三角不等式给
$$
|\mathcal E(b)(n,k)|\le p_{n,k}\le u_k.
\tag{49.33}
$$
初始列由 $|b_n|\le A\mathbf1_{n<N}=p_{n,0}$ 成立。若此前各列成立，则下一列至多为
$p_{n+1,k}+A\sum_{j=0}^{k}p_{n,j}\mathbf1_{k-j<N}=p_{n,k+1}$。后一等式是同一负前缀的正递推；由同样归纳与全负包络比较得 $p\le u$。于是对每个坐标，
$$
|T^1(n,k)-\mathcal E(b)(n,k)|
\ge u_k-p_{n,k}
=|T^1(n,k)-\mathcal E(b^{A,N})(n,k)|.
\tag{49.34}
$$
负前缀本身也属于复数候选类，所以它在复数类中仍同时最小化所有坐标误差，且两类最优范数相同。因此复数截止优化的阈值也恰为（49.32），没有分别优化坐标后再假定存在共同实现。

**全相位运输。** 对任意 $|\zeta|=1$，令
$$
b_i^{\zeta,N}=\begin{cases}-A\zeta^{i+1},&i<N,\\0,&i\ge N.\end{cases}
$$
$D_\zeta$ 双射地运输整个自由复数截止类，$U_\zeta$ 保持每个加权绝对差。由（49.5），上面的逐坐标最优性与阈值同时运输至目标 $T^\zeta$。故
$$
\boxed{N_{\min}(A)=\left\lceil\frac{\log(1-\rho)}{\log\rho}\right\rceil,}
\tag{49.35}
$$
$$
\boxed{\|T^\zeta-\mathcal E(b^{\zeta,N})\|_\rho=c_A
\quad\Longleftrightarrow\quad N\ge N_{\min}(A).}
\tag{49.36}
$$
因为 $\log\rho<0$，条件 $\rho^N\le1-\rho$ 在取对数并除以 $\log\rho$ 后成为 $N\ge\log(1-\rho)/\log\rho$，向上取整也包含阈值恰为整数的情形。当达到时仍是每个有限坐标误差严格小于 $c_A$，全层上确界为 $c_A$。当截止更短时，复数共同支配把实数必要性见证运输过来，故所有同截止复来源的误差严格大于 $c_A$。对于实数两相位只需 $\zeta=\pm1$，其变换保留实数来源类。零截止只有零来源，误差 $A>c_A$。

**全部实际来源的距离与达到性。** 实数距离等式保留供应接口中式（47.40）的归属；这里的证明同时给复数扩张，并用相位分类与有限截止识别全部达到情形。加权消失尾空间到目标的距离下界由
$\tau_N(T)\le\|T-S\|_\rho+\tau_N(S)$ 得到：若 $L_\rho(S)=0$，则
$L_\rho(T)\le\|T-S\|_\rho$。第49.9节的截断给所有零尾实际目标距离零；上面的相位前缀给所有正尾目标距离 $c_A$ 并达到。于是实、复两域均有
$$
\boxed{\operatorname{dist}_\rho(T,J_A^{\mathbb F})
=\operatorname{dist}_\rho(T,\overline{J_A^{\mathbb F}})
=L_\rho(T)\qquad(T\in I_A^{\mathbb F}).}
\tag{49.37}
$$
到 $J_A^{\mathbb F}$ 的距离达到，当且仅当来源有限支持或属于相位族。证明零距离达到必使数组相同，取第一列即使来源相同，因此无限支持零尾来源没有有限来源精确最近点；正距离情形则全部由上面的有限前缀达到。

到闭包的距离对每个实际目标都达到：零尾目标自身已在闭包；正尾目标有上述有限来源最近点。这不声称全部环境 Banach 空间都有这项最佳逼近性质。

**实有理来源的范围。** 开头所列第48.3节有理截止定理给实负角点在固定 $N$ 下的达到判据
$$
W_N>1\quad\text{或}\quad[W_N=1\text{ 且 }A\in\mathbb Q].
$$
实分次符号运输保持有理性，因此同一判据适用于另一实极端；其固定截止下确界仍等于实来源的最优值。无理阈值等号时，下确界为 $c_A$ 而该截止无有理达到点；下一截止已有达到点。上述完整复数相位运输一般不保持 Gaussian-rational 系数，故本节不据此给复有理达到性分类。

### 49.11 相位的精确距离与实复可分性差异

对 $|\zeta|=|\xi|=1$，按总分次 $m=n+k+1\ge1$ 分组。相位差只依赖 $m$，同一组中 $u_k$ 随 $k$ 增加，所以最大值在 $(n,k)=(0,m-1)$ 取得。于是
$$
\boxed{
\|T^\zeta-T^\xi\|_\rho
=\sup_{m\ge1}
\bigl(c_A+b_A\rho^{2(m-1)}\bigr)
|\zeta^m-\xi^m|.
}
\tag{49.38}
$$
这不是仅有上界；每个分次的最大值都有同一组实际坐标见证。

若 $\zeta\ne\xi$，记 $r=\zeta/\xi\ne1$。需要估计
$\limsup_{m\to\infty}|r^m-1|$：

- 若 $r$ 有有限偶数阶 $q$，幂序列周期性经过 $-1$，上极限为二。
- 若 $r$ 有有限奇数阶 $q\ge3$，其全部幂组成 $q$ 次单位根，最大弦长为 $2\cos(\pi/(2q))\ge\sqrt3$，且周期性重复，故这也是上极限。
- 若 $r$ 有无限阶，令 $H$ 为其整数幂生成的闭子群。把 $N+1$ 个幂 $1,r,\ldots,r^N$ 放入 $N$ 个等长圆弧，抽屉原理给正整数 $q_N$，使 $r^{q_N}\to1$。这些幂都不等于一；任何有限多个非平凡幂到一的距离有正下界，因此可取子列使 $q_N\to\infty$。必要时取逆，$H$ 遂含 $e^{\mathrm i t_j}$，其中 $0<t_j\to0$。对任意固定 $\theta\in[0,2\pi)$，整数倍 $\lfloor\theta/t_j\rfloor t_j$ 与 $\theta$ 的差小于 $t_j$；相应的单位复数仍属于 $H$，闭性给 $e^{\mathrm i\theta}\in H$，所以 $H$ 是整个圆周。再对任意固定负整数 $p$，充分大的 $q_N$ 使 $q_N+p>0$，并且 $r^{q_N+p}\to r^p$。正幂闭包于是包含全部整数幂及其闭包 $H$，故正幂已经稠密。每条去掉有限前缀的轨道都是稠密正幂轨道的一次旋转，故每条尾轨道仍稠密，最终 $\limsup_m|r^m-1|=2$。

（49.38）的权重趋于 $c_A$，所以
$$
\boxed{
\zeta\ne\xi\quad\Longrightarrow\quad
\|T^\zeta-T^\xi\|_\rho\ge\sqrt3\,c_A>0.
}
\tag{49.39}
$$
相位族不可数且一致分离，因此 $I_A^{\mathbb C}$ 在临界加权范数下不可分：若有可数稠密集，每个相位点附近半径小于 $\sqrt3c_A/2$ 的互不相交球都须包含不同的稠密集元素，矛盾。

另一方面，$B_{\rho,0}$ 通过 $T(n,k)\mapsto\rho^{n+k}T(n,k)$ 与可数指标上的通常 $c_0(\mathbb F)$ 线性等距。后者可分，其任意度量子空间也可分。因此（49.31）中的有限来源闭包可分。实实际像则是相应可分闭包再加两个点，所以仍可分。这里的论证不需要为复数相位构造有理有限来源最近点。

相位参数在每个固定有限坐标上连续；全层加权范数却把所有不同相位一致分开。原因是同一差异以 $\zeta^m$ 沿无界分次反复显露。精确联系是圆群在整数分次上的字符及递归的等变性；它没有把这些整数分次预先指定成物理时间，也没有提供波函数或量子解释。

实数两极端的距离还可直接算出：第 $(0,0)$ 坐标相差 $2A$，而两个数组的范数均为 $A$，所以
$$
\boxed{\|T^1-T^{-1}\|_\rho=2A.}
\tag{49.40}
$$
这与通用相位下界相容；下界不宣称对每一对相位都取等号。

### 49.12 非相位点的局部统一尾界与同胚

在 $X=K_A^{\mathbb F}$、$\mathbb F=\mathbb R$ 或 $\mathbb C$ 上使用乘积拓扑。一个明确的相容度量是
$$
d_\Pi(a,b)=\frac1{2A}\sum_{i\ge0}2^{-(i+1)}|a_i-b_i|.
\tag{49.41}
$$
因为每个坐标差至多为 $2A$，级数统一收敛。正定性、对称性、三角不等式逐项成立；该度量的收敛等价于逐坐标收敛：一个方向由单个正权项受总和控制，另一个方向先控制有限头部，再用几何权重控制尾部。每个坐标取值于紧区间或紧圆盘，故 $X$ 是紧可度量空间；也可逐坐标选收敛子列，再作对角提取及同一尾界得到紧性。

记来源相位集合为
$$
\Phi_{\mathbb C}=\{a^\zeta:|\zeta|=1\},
\qquad \Phi_{\mathbb R}=\{a^1,a^{-1}\},
\qquad U=X\setminus\Phi_{\mathbb F}.
$$
对固定非相位来源 $a\in U$，第49.4节给有限 $J$ 和 $\gamma_J(a)=\gamma>0$。不再要求附近来源与此前缀精确相同，而取乘积开邻域
$$
V=\left\{b\in X:
\sum_{i=0}^{J}\rho^{i+1}|b_i-a_i|<\gamma/2\right\}.
$$
对每个 $b\in V$ 和每个角度 $\theta$，有
$$
|g_{J,b}(\theta)-g_{J,a}(\theta)|
\le\sum_{i=0}^{J}\rho^{i+1}|b_i-a_i|<\gamma/2.
$$
因此 $\gamma_J(b)\ge\gamma/2$，整个 $V$ 都排除相位来源。第49.5节只用这个间隔下界和统一幅度合同，所以可将其中 $\gamma$ 换成 $\gamma/2$，取得不依赖 $b\in V$ 的 $M<\infty$、$q<1$，满足
$$
\boxed{\tau_N(\mathcal E(b))\le Mq^N
\quad\text{对所有 }b\in V\text{ 及 }N\ge0.}
\tag{49.42}
$$

任给范数容差 $\varepsilon>0$，先选 $N$ 使 $2Mq^N<\varepsilon/2$。对有限坐标集 $n+k<N$，每个 $\mathcal E(b)(n,k)$ 都是有限边界坐标的多项式，因此在乘积拓扑连续。有限取交可在 $V$ 内进一步缩小到 $a$ 的一个邻域，使这些坐标的最大加权误差小于 $\varepsilon/2$。其余坐标的误差则由（49.42）小于 $\varepsilon/2$。两部分取上确界，得到
$\|\mathcal E(b)-\mathcal E(a)\|_\rho<\varepsilon$。这证明 $\mathcal E:X\to I_A^{\mathbb F}$ 在每个非相位点连续。

反方向，在整个实际像上定义第一列提取
$\beta(T)_i=T(i,0)$。由范数定义，
$$
|\beta(T)_i-\beta(S)_i|
\le\rho^{-i}\|T-S\|_\rho.
$$
每个固定坐标因而对范数连续；由乘积拓扑的定义，$\beta:I_A^{\mathbb F}\to X$ 连续。这些坐标 Lipschitz 常数随 $i$ 无界，因而此处不推出通常输入上确界范数中的逆向连续性。

递归唯一性和第一列给 $\beta\mathcal E=\mathrm{id}$、$\mathcal E\beta=\mathrm{id}$ 于对应实际像。结合正尾分类，得到
$$
\boxed{
\mathcal E:U\xrightarrow{\ \cong\ }
I_A^{\mathbb F}\cap B_{\rho,0}
}
\tag{49.43}
$$
为乘积子空间拓扑与临界范数子空间拓扑之间的同胚。这比固定来源上的逐坐标收敛更强：有限前缀间隔控制了整个邻域的共同尾部。

### 49.13 尾量的稳定性、孤立点与径向跳跃

对任意两个加权有界数组，三角不等式给
$\tau_N(T)\le\tau_N(S)+\|T-S\|_\rho$。令 $N\to\infty$ 并交换 $T,S$，得到
$$
\boxed{|L_\rho(T)-L_\rho(S)|\le\|T-S\|_\rho.}
\tag{49.44}
$$
因此每个相位数组与每个非相位实际数组的距离至少为 $c_A$。不同相位之间已有（49.39）的 $\sqrt3c_A$ 下界，所以每个相位数组在整个实际像中都是孤立点：以它为中心、半径严格小于 $c_A$ 的相对开球只有该点。

孤立的输出点并不意味着来源乘积拓扑也将它孤立。固定相位 $\zeta$，取 $0<\varepsilon<1$，令
$$
a^{\varepsilon}=(1-\varepsilon)a^\zeta,
\qquad B=(1-\varepsilon)A,
\qquad h=A-B=\varepsilon A.
$$
有 $d_\Pi(a^\varepsilon,a^\zeta)=\varepsilon/2$，甚至输入的普通上确界距离也等于 $\varepsilon A$。但 $a^\varepsilon$ 相对于固定幅度合同 $A$ 是非相位来源，故（49.44）已经给输出距离至少为 $c_A$。

这一特定路径的实数估计由供应接口的式（47.16）给出。令实常边界 $a_A=-A\mathbf1$、$a_B=-B\mathbf1$，则 $a^\zeta=D_\zeta a_A$、$a^\varepsilon=D_\zeta a_B$。由（49.5）的等变性及 $U_\zeta$ 的等距性，
$$
\|\mathcal E(a^\varepsilon)-T^\zeta\|_\rho
=\|\mathcal E(a_B)-\mathcal E(a_A)\|_\rho
=\sup_{k\ge0}\rho^k[u_k(A)-u_k(B)].
$$
最后的上确界来自第零行，其余行多一个 $\rho^n\le1$ 的因子。实估计的上界沿用其拥有者的完整证明；两个下界见证在运输后均保留：深度零给 $h$，而 $0<B<A$ 时严格单调的增长根满足 $\rho\lambda(B)<1$，所以 $\rho^ku_k(B)\to0$，目标加权幅度则趋于 $c_A$。因此把供应的实恒等式等距运输，得到
$$
\boxed{
\|\mathcal E(a^\varepsilon)-T^\zeta\|_\rho
=\max\{\varepsilon A,c_A\}.
}
\tag{49.45}
$$
特别地，当 $0<\varepsilon\le c_A/A$ 时距离恰恒为 $c_A$，没有随着输入的乘积或上确界距离趋零而趋零。

因此整个连续性集合恰好为
$$
\boxed{
\mathcal E:(X,\text{乘积拓扑})\to(I_A^{\mathbb F},\|\cdot\|_\rho)
\text{ 在 }a\text{ 连续}
\quad\Longleftrightarrow\quad a\notin\Phi_{\mathbb F}.
}
\tag{49.46}
$$
径向例证明的是自由来源域中的不连续性；不预设这些扰动在任何受额外约束的实际记录纤维中都存在。

### 49.14 实际像的拓扑分解、局部紧性与紧穷竭

令 $I_0=I_A^{\mathbb F}\cap B_{\rho,0}$、
$S=\{T^\zeta:a^\zeta\in\Phi_{\mathbb F}\}$。由（49.44），两部分之间的所有距离均至少为 $c_A$，所以两部分在 $I_A^{\mathbb F}$ 中都开且闭。上一节又证明 $S$ 的每个点孤立；结合（49.43），得到拓扑不交并
$$
\boxed{
I_A^{\mathbb F}\cong
U\ \sqcup_{\mathrm{top}}\ (\Phi_{\mathbb F},\text{离散拓扑}).
}
\tag{49.47}
$$
这里右边的 $U$ 保留来源乘积拓扑，而相位部分使用离散拓扑。复数情形的参数集合是一整个圆周，但不是圆周通常拓扑；实数情形只是两个孤立点。这是拓扑不交并，不是向量空间直和。

来源相位集合在来源乘积拓扑下却是紧的：$\zeta\mapsto a^\zeta$ 的每个坐标是连续函数，所以该映射从紧圆周到 $X$ 连续；实相位集有限亦紧。因此 $\Phi_{\mathbb F}$ 在紧度量空间 $X$ 中闭，$U$ 是开子空间。对每个 $a\in U$，其到相位集合的乘积距离严格为正。取半径小于该距离的闭球，得到位于 $U$ 内的紧邻域，故 $U$ 局部紧。它还是第二可数度量空间的子空间，因而可分。这些性质经（49.43）运输到 $I_0$。

还可给显式紧穷竭。对整数 $m\ge1$ 令
$$
K_m=\{a\in X:d_\Pi(a,\Phi_{\mathbb F})\ge1/m\}.
$$
距离函数连续，故 $K_m$ 是 $X$ 的闭子集，因而紧，且 $K_m\subset U$。它们随 $m$ 增加，并且并集为 $U$：每个非相位点到闭相位集的距离为某个正数，可选足够大的 $m$；相位点不属于任何 $K_m$。因为 $1/m>1/(m+1)$，每个 $K_m$ 还包含于 $K_{m+1}$ 在 $X$ 中的相对内部。$\mathcal E$ 在 $U$ 连续，所以
$$
\boxed{
I_0=\bigcup_{m\ge1}\mathcal E(K_m),
\qquad\mathcal E(K_m)\text{ 在临界范数中紧}.
}
\tag{49.48}
$$
这证明 $I_0$ 是 $\sigma$-紧的，即可由可数个紧集覆盖。

整个实际像也局部紧：非相位点沿上述紧邻域，相位点则取自身这个紧开邻域。实实际像在 $I_0$ 外只增加两个点，所以仍可分且 $\sigma$-紧。复实际像既不可分也不 $\sigma$-紧：任何紧集都只能包含有限多个相位点，否则（49.39）的统一分离与紧度量空间的全有界性矛盾；可数个紧集因而至多覆盖可数多个相位点，无法覆盖整圆相位族。

来源域的有限支持边界在乘积拓扑中稠密，但它们的实际数组在临界范数中只稠密于 $I_0$。这个差别已由（49.30）、（49.31）及上述开闭分解给出，不需要把表示转换误称为全域拓扑等价。

### 49.15 邻近角度在全层范数中的精确极限

固定 $|\zeta|=1$，让 $\xi\ne\zeta$ 沿单位圆周的通常拓扑趋于 $\zeta$。结论是
$$
\boxed{
\lim_{\substack{\xi\to\zeta\\\xi\ne\zeta}}
\|T^\xi-T^\zeta\|_\rho=2c_A.
}
\tag{49.49}
$$
该极限是实数距离值的极限，不表示数组趋于 $T^\zeta$。

先给上界。任取 $\delta>0$，选整数 $M$ 使
$b_A\rho^{2(M-1)}<\delta$。在（49.38）中，所有 $m\ge M$ 项均至多为 $2(c_A+\delta)$。有限多个 $1\le m<M$ 项则因 $\xi\to\zeta$ 一致趋零。因此距离上极限至多为 $2(c_A+\delta)$；令 $\delta\downarrow0$，得到至多 $2c_A$。

再给下界。在 $\zeta$ 附近唯一写
$\xi/\zeta=e^{i\theta}$，其中 $0<|\theta|<\pi$、$\theta\to0$。取
$m_\theta=\lfloor\pi/|\theta|\rfloor$。则 $m_\theta\to\infty$，并且
$$
\bigl|m_\theta|\theta|-\pi\bigr|<|\theta|,
\qquad
|e^{im_\theta\theta}-1|\longrightarrow2.
$$
代入（49.38）的这一项，其权重趋于 $c_A$，故距离下极限至少为 $2c_A$。与上界合并即证。

任意有限分次的相位差都趋零，见证距离的分次 $m_\theta$ 却随角差缩小而逃向无穷。这给出了“每个有限读数接近，但全层完成几何仍分离”的同源实例。它与（49.45）的径向距离 $c_A$ 不冲突：两式采用不同的实际来源路径，并未声称存在与接近方向无关的统一跳跃常数。实数两相位域中没有这种非平凡的邻近角度极限。

### 49.16 单点缺口、最终常量与周期的实际有理生成式

本节的分类判据限制为实来源；所写有理生成式由同一个实际行公式推出，其代数表达对满足同样结构及 $|a_i|\le A$ 的复系数也成立。

**全负来源的一个早期系数改变。** 对 $0<\varepsilon\le2A$，令
$a=-A\mathbf1+\varepsilon e_j$。这属于原立方体。除 $\varepsilon=0$ 外，它不等于两极端，因而剩余尾为零；即使 $\varepsilon=2A$ 只是把一个符号翻转、所有绝对幅度仍然饱和，结论也成立。

这还可在同一实际生成式中看见。令
$$
F_*(z)=1-\frac{Az}{1-z},
\qquad F_a(z)=F_*(z)+\varepsilon z^{j+1}.
$$
(49.4) 给
$$
R_{n,a}(z)
=-\frac A{F_a(z)-z}
+\begin{cases}\displaystyle\frac{\varepsilon z^{j-n}}{F_a(z)^{j-n+1}},&n\le j,\\[4pt]0,&n>j.\end{cases}
\tag{49.50}
$$
这是实际各行的有理式，不是任意数组拟合。严格幅度缺口 $0<\varepsilon<2A$ 可直接用 (49.19)；端点纯符号翻转使用 (49.9)。

**最终常量。** 设整数 $M\ge0$，且 $a_i=b$ 对全部 $i\ge M$ 成立，$|b|\le A$。此时
$$
F_a(z)=1+z\sum_{i<M}a_i z^i+\frac{b z^{M+1}}{1-z},
$$
$$
C_{n,a}(w)=
\begin{cases}
\displaystyle\sum_{j=0}^{M-n-1}a_{n+j}w^j+
\frac{b w^{M-n}}{1-w},&n<M,\\[4pt]
\displaystyle\frac b{1-w},&n\ge M.
\end{cases}
\tag{49.51}
$$
所以各行均由 (49.4) 得到明确有理函数，尾部行是 $b/(F_a-z)$。分类给精确判据
$$
\boxed{
L_\rho(\mathcal E(a))>0
\Longleftrightarrow b=-A\text{ 且全部前缀系数也等于 }-A.
}
\tag{49.52}
$$
正尾值仍是 $c_A$。若一个实相位最终常量，$A>0$ 使其最终值非零，且相邻项的比值既等于 $\zeta$ 又等于一，所以必有 $\zeta=1$；$\zeta=-1$ 不可能最终常量。$M=0$ 包括完整常量情形。有限前缀中的任何偏离都会消去最终负常量的临界尾。

**周期来源。** 设 $a_{i+p}=a_i$，其中 $p\ge1$ 为指定整数周期。令
$V_{n,p}(w)=\sum_{j=0}^{p-1}a_{n+j}w^j$，下标使用同一周期延伸。则
$$
F_a(z)=1+\frac{zV_{0,p}(z)}{1-z^p},
\quad C_{n,a}(w)=\frac{V_{n,p}(w)}{1-w^p},
$$
$$
R_{n,a}(z)
=\frac{\displaystyle\sum_{j=0}^{p-1}a_{n+j}z^jF_a(z)^{p-1-j}}
{F_a(z)^p-z^p}.
\tag{49.53}
$$
对实来源，正尾相位的首项使 $\zeta\in\{1,-1\}$；因所有相位系数非零，$p$ 周期性等价于 $\zeta^p=1$。$\zeta=1$ 对任何指定 $p$ 都满足，而 $\zeta=-1$ 恰在 $p$ 为偶数时满足。因此周期来源的精确判据是：周期块全部为 $-A$，或 $p$ 为偶数且周期块为
$(A,-A,A,-A,\ldots)$。这两种情形的剩余尾为 $c_A$，其余周期来源全部为零。允许使用非最小周期也不改变该判据。

交替相位不能混淆。两个来源分别给
$$
a_i=A(-1)^i:
\quad R_{n,a}(z)=\frac{A(-1)^n(1+z)}{1+(A+2)z+z^2},
$$
$$
a_i=-A(-1)^i:
\quad R_{n,a}(z)=\frac{-A(-1)^n(1+z)}{1+(2-A)z+z^2}.
\tag{49.54}
$$
前者是分次运输的极端，后者不是。该不对称来自 $F_a$ 固定的单位常数项和递归乘法结构，不能由“都是交替符号”抹去。

首项幅度缺口还有直接实际生成式。令 $A=1/2$、$a_0=0$、$a_i=-1/2$ 对 $i\ge1$，则
$$
F_a(z)=1-\frac{z^2}{2(1-z)},\qquad
R_{n,a}(z)=-\frac{1/2}{F_a(z)-z}\quad(n\ge1),
$$
$$
R_{0,a}(z)=-\frac{z/2}{F_a(z)(F_a(z)-z)}.
$$
其中
$$
F_a(z)-z=\frac{1-2z+z^2/2}{1-z},
$$
较小正根为 $2-\sqrt2>1/2$。而 $F_a$ 的较小模零点为 $\sqrt3-1>2-\sqrt2$，故全部所写行函数在 $|z|<2-\sqrt2$ 解析。这份最终全负的实际来源因而确有大于临界半径的共同解析圆盘；单个首项缺口已足以消除临界正尾。符号缺口与周期例则由第49.4节的有限相位间隔一并覆盖。

### 49.17 有限层剖面的读法与非单调的晚缺口

固定 $A=\rho=1/2$，下表使用有限层剖面
$$
d_m(T)=\max_{n+k=m}\rho^m|T(n,k)|.
$$
它不是无限尾上确界 $\tau_m$。表内小数由精确有理结果取近似，只用于展示不同衰减行为。

| 实际来源 | $d_{16}$ | $d_{32}$ | $d_{48}$ |
| --- | ---: | ---: | ---: |
| 全负 $-1/2$ | 0.333333333 | 0.333333333 | 0.333333333 |
| 分次符号极端 $(1/2)(-1)^i$ | 0.333333333 | 0.333333333 | 0.333333333 |
| 全负来源但 $a_0=0$ | 0.0196070671 | 0.00157461917 | 0.000125028515 |
| 全负来源但 $a_0=1/2$ | 0.00156122318 | 0.0000166549038 | 0.000000167729275 |
| 全负来源但 $a_6=0$ | 0.272407254 | 0.298230685 | 0.296493769 |
| $(a_0,a_1,a_2)=(1/4,-1/2,0)$，之后全负 | 0.00170511872 | 0.0000233715436 | 0.000000266351277 |
| 周期 $(-1/2,-1/2,1/2)$ | 0.0173582149 | 0.00228867304 | 0.000301477758 |
| 反相交替 $-(1/2)(-1)^i$ | 0.00000810623169 | 0.000000000124283396 | $1.89850250\times10^{-15}$ |

两极端的每一有限层都精确等于 $1/3+(1/6)4^{-m}$。单点缺口较晚时，有限层读数可长期接近 $1/3$；例如表中下标六的零缺口满足 $d_{16}<d_{32}$ 而 $d_{48}<d_{32}$，先增后减，因而并非逐层单调；这不推翻 (49.18) 的来源相关指数尾界。零尾的全称结论由前面的共同解析半径与 Cauchy 证明承担，不能从有限深度 48 推断。


另一个不同的有限统计量是在 $N\le n+k\le48$ 的带状区域取最大值。对来源“仅 $a_2=+1/2$，其余为 $-1/2$”而言，该有限带统计量在 $N=8,16,32$ 时分别约为
$0.1116561890,\ 0.0672286091,\ 0.0147494877$。带状最大值与单层剖面 $d_m$ 不同，均不冒充无限尾 $\tau_N$。这份纯符号缺口也由有限相位排除而具有零尾。

### 49.18 完整观察者、实际共同来源与可取得范围

本节使用的自由来源结论不自动在指定完整档案下可执行。若实际对象由共同来源 $\omega$ 给出
$(c(\omega),a(\omega))$，表示转换仍应限制在对应实际像上，保持
$$
(c,a)\longmapsto(c,\mathcal E(a)).
$$
分类（49.21）可用于这个像中的每个已有来源；但有限前缀替换或相位运输是否仍对应同一个 $c$、是否有合法来源、是否可取得，必须另验。自由立方体中的最近点存在不保证约束记录纤维中的最近点存在。

非相位点的连续性在限制到实际来源子空间后仍成立；自由域中的相位不连续性则不能自动转授给任意实际记录纤维，因为该纤维可能不含所用径向或角度逼近，甚至只有一个来源。完整档案的保留与数学工作边界的拓扑必须分别说明，不能从工作边界的连续性宣称整个观察者已获得新信息。

在已声明模型内，正尾来源及其有限达到性已经完整分类，因此本自由来源模型中不存在严格正距离却无有限来源最近点的实际目标。任意其他递推、改变幅度约束、不同权重、限制后的实际来源纤维，以及 Gaussian-rational 复数来源的达到性，均不由本节解决。实数的两相位结果与复数的整圆相位结果也须分别陈述，不能将复数不可分性转述成实数结论。


更明确地，令 $\Omega$ 为实际共同来源集合，$c:\Omega\to\mathcal C$ 保留全部已取得的内部与外部记录、来源与版本、联合关系、参考、校准、局部钟及已知关系、合法动作、顺序、失败、停止和误差合同。两边只比较
$$
Q_\partial(\omega)=(c(\omega),a(\omega)),\qquad
Q_{\mathrm{body}}(\omega)=(c(\omega),\mathcal E(a(\omega))).
\tag{49.55}
$$
在这两个对应实际像上，$(c,a)\mapsto(c,\mathcal E(a))$ 与
$(c,T)\mapsto(c,(T(i,0))_{i\ge0})$ 互逆。确切地，首列恒等式 $\beta\mathcal E(a)=a$ 使第一个复合为 $(c,a)\mapsto(c,a)$；若 $T=\mathcal E(a(\omega))$ 位于对应实际体像，则递归唯一性给 $\mathcal E\beta(T)=T$，使另一个复合为 $(c,T)\mapsto(c,T)$。两个复合逐字保留同一个 $c$。没有把实际像扩成 $\mathcal C\times K_A^{\mathbb F}$，也不要求 $c$ 与边界独立。工作边界中的数学连续性或完成，不等于整个观察者免费取得未知资料。

有限前缀的正证书排除了所有相位延伸；相反，每份相位有限前缀在自由幅度域中都有合法非相位延伸，例如保留此前缀并在下一下标置零。因此使用供应接口中命题47.6的确定性有限系数／数组坐标查询合同，并要求两个见证共享同一初始完整档案和相同合法操作规则时，单凭这些读数不能认证后缀永远保持相位。

具体地，固定协议在某条相位来源上的有限终止执行，令 $M$ 为全部已查询边界下标及数组查询的 $n+k$ 的最大值；无查询时置 $M=-1$。选 $N\ge\max\{1,M+1\}$，保留该相位来源的 $i<N$ 前缀，将 $i\ge N$ 置零。得到的来源具有同一已查询前缀并且不是相位。在固定档案纤维中应用此构造，另须该延伸属于同一初始档案下的合法来源。

对整份执行归纳：初始完整记录相同；若此前记录相同，确定性合同给同一下一动作及可见元数据；若为查询，系数下标或有限依赖 $n+k<N$ 使答案相同，故追加的记录、次序、费用及钟读数相同；若为停止，两边在同一步停止并输出相同。因此有限的全部执行可在非相位延伸上重放，不能输出对整个允许来源类可靠的永久相位认证。一般干预、额外来源身份／支撑标签、非局部尾 oracle、来源相关元数据及未计入的输出后读取均不属于这一合同；若另有这些信息，须重新核对见证。

来源相关的指数尾界也没有给所有非相位来源一个共同正裕度：缺口可以任意小或任意晚，认证半径可以任意接近临界半径。第49.7节的条件完备性不提供统一停止深度、精度成本或未经声明的成功概率。

Cauchy 系数估计、调和最小值／最大模原理、紧乘积空间及圆群字符的性质是证明所用的成熟数学工具。新的连接在于它们如何作用于同一个实际递归来源：有限相位排除给共同全行解析圆盘，随后控制有限来源完成与临界拓扑。整数分次、相位、尾量和拓扑在此都有明确数学定义，不据其名称推断物理波动、熵增或时间产生。

[^criticalphase_swamy]: M. N. S. Swamy, “Properties of the Polynomials Defined by Morgan-Voyce,” *The Fibonacci Quarterly* 4(1) (1966), pp.73–81，[原始扫描](https://www.fq.math.ca/Scanned/4-1/swamy.pdf)。所用标量族的初值与递推为印刷第73页式（7），系数为第79页式（40）；这里沿用先前幅度节已核对的数学归属，不将本文的非线性临界分类归属于该文。

## 49.99 追加锚
