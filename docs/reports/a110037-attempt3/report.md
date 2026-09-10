# A110037 attempt 3 — implementation record

产地：lean4 skill；Codex 主 worker 单点实施与自查，独立评审席 0。
本轮用户 brief 是预登记与本地证明授权；attempt 2 的结果按原提交保留。

## 预登记

目标是具体有限集合计数的 SloaneSellersParity，继而实例化已验的
signed_diff_of_parity，得到 n≥2 的无条件 signed_nonsquashing_diff。
成功须含 kernel 证明、make lean EXIT=0、无 sorry/私 axiom/native_decide、PR。
反例须在 n≥2 给 kernel 见证；blocked 须有实际证明尝试和精确剩余 goal。

拟议新增见证：按最大部件分解直接定义的有限集合，证明 B 的累计和递推。
最大部件等于尾部和允许；仅尾部为同值单例时违反互异而排除。
之后由递推推八个奇偶子句，复用 attempt 2 的强归纳和差分桥。
该无界组合双射是一般数学内容，utility 拟为 none；准入拟为 escape-witness。
不新建理论卷、不 ingest、不造 atom；需要冻结时走 deposit-uncovered
（canonical ledger-align --add）。不修改冻结模块。

## 已有资产与检索收据

起点 dbc4935545b40832ed65edef048525d30d8a3dce，分支 lane/math/a110037，
初始树干净；沿用基线 82938786158c163b50350c14c948e63df61107a8。
完整分段阅读 CLAUDE.md（截断段已补读）、agents/CONTEXT.md、lean4 SKILL.md。
已读 attempt 2 的完整 Bridge.lean、report.md 和 Sloane–Sellers Library note。
八项结构与条件桥目前位于 docs/reports/a110037-attempt2/Bridge.lean，未冻结。

继承已完成的有序检索：D5、钉版 mathlib v4.33.0、第三方 GitHub Lean 检索
均未命中可直接引用的 B 奇偶定理；精确命令和公共面阅读收据见 attempt 2 报告。
本轮没有将该搜索重做或把“无同名结果”当数学失败。
本轮 rg 定位 SloaneSellersParity/signed_diff_of_parity，只命中 attempt 2 工件。
Mathlib Finset.Card 的 card_bij/card_bij' 以及 Max/Sigma API 已粗筛，
将直接使用其一般基数工具，不重证库有定理。

本轮授权明确撤销旧 brief 的“不重证公开 B 奇偶定理”禁令解释。
旧报告的授权阻塞理由只描述 attempt 2，当下不再有效；数学条件结果仍有效。

## 构建收据

make lean-cache-ensure EXIT=0：status=present, method=none, stamp_miss=null,
project_olean_state=warm, mathlib_olean_state=warm, clonefile_attempts=0,
mathlib_missing_olean_files=0。
pin_sha256=sha256:6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e。
后续片段可用热树增量检查；正式门序仍用 make。

## 初始时点的未主张（由后续构建收据更新）

本段记录开工时状态：当时尚未证明八个具体计数子句或无条件主目标，尚未冻结、尚未开 PR。
没有主张有限核对是研究进展、全球检索完备、首创性或多模型共识。
未在本轮打开的外部页面为 ASSUMED-UNVERIFIED；先前阅读收据按历史引用。
开工时公开新增 theorem 为 0；最终逐声明账目见后文。

## 最大部件分解：第一单元已验

已阅读历史 PDF 提取 pages 6–8 的原文；Theorem 2 (14) 正是拟议累计和双射，
等号边界仅排除尾部单例。Corollary 4 的 32 进展式将直接由递推证明，含 m=0。
Mathlib card_bij、card_biUnion、max'_mem、le_max'、sum_erase_add 公共接口已读。

Counting.lean 的 mem_parts、subset_parts、insert_parts、card_cumulative、
erase_max_parts 已经热树 kernel 检查，EXIT=0。后者证明任意 n>0 的原分拆可
删除最大部件，得到累计族 n/2 中尾部，再插入 n−尾部和重建原分拆。
日志：attempt-3/counting-helpers.log；#print axioms erase_max_parts 仅标准三条。
首两次编译错误是 id 的隐式函数推断、rfl 消去变量名与 sum_erase_add 的显式
参数问题，均已修复；未把错误恢复中的 sorryAx 当通过项。
此单元是无界组合构造，非有限核对；基数双射和原目标尚未闭合。
当前上述辅助 theorem 均 private，direct_frozen_dependencies=[]，不单独申请冻结。

## 递推到八项奇偶：第二单元已验

Parity.lean 已从 B(2)=1、正 m 的奇项增一和正偶项差分递推证明所有七条
偶指标进展式。新的核心归纳结论是 B(4m+2)%2=(m+1)%2；继而得
B(4m)%2=(m+B(2m))%2 (m>0)。由它们直接推出 8、16、32 进展式，
两个 32 进展式均包含 m=0。第八项 odd 是奇项增一等式取模。
这是真正尝试并完成递推之后的奇偶证明，尚待具体计数的递推双射闭合。
热树 EXIT=0；parity-checked.log 的公理输出仅 propext/Quot.sound。
首次错误为 proof-only section 参数未 include 和 0<m 的词法解析，已修复。
当前这些 theorem 均 private，冻结依赖为空，不单独申请条件结果冻结。

## 具体计数递推：第三单元已验

Counting.lean 的基数双射现已全闭合，热树 EXIT=0。
日志 counting-recurrence-checked.log：count_odd 与 count_even_step 的 axiom
闭包都仅 propext/Classical.choice/Quot.sound。

count_odd：任意 m>0，B(2m+1)=B(2m)+1。
count_even_step：任意 m>0，B(2(m+1))=B(2m)+B(m+1)。
具体计数始终是原 powerset/filter 定义，没有使用递推重定义 B。
odd_sum 与 even_sum 由 card_extension 活用插入/删除最大部件的双射得到；
even_exception 证明被排除族恰为单例尾部 {m}，并保留所有其余等号边界。
这补齐了 Parity.lean 的所有数学前提；下一步移入正式 D5 模块并实例化旧桥。
公开 count_odd/count_even_step 均 content，直接冻结依赖为空；共同见证
card_extension 在依赖闭包和活推导路径中，非已有投影、非递推结论的定义等价；
准入拟为 escape-witness，最终账目在正式路径的 report 产生后补身份。

## 正式落点与当场来源核对

落点容量实测：D5/S1/Recurrence 直接文件24，Blueprint 同级直接文件48。
新增两个模块需要四个镜像文件，会越 Blueprint 上限，故按同形地址新开
Recurrence/Partitions 子桶；旧地址不迁。两个模块分别为 NonsquashingCounting
与 NonsquashingPaperfold。正式代码复用 attempt 2 的证明项，未重新推导旧桥。

重新 GET A110037/internal 与 A073089/internal 均 EXIT=0，全部 comment/formula/
name/offset 字段已读。前者仍记录 Calderón 2025-08-19 的 n≥2 猜想，后者八分支
与原独立定义一致。新 note 的 Verified locator 逐字包含 frontmatter URL。
Library/Words 新 note 前直接文件31，不越48。未打开其他外链，ASSUMED-UNVERIFIED。

首次 make lean EXIT=2 / 34.967秒，仅新增主模块有一个多余 rfl（此前 rw 已闭合）;
主目标已产生标准三公理证明项，但不以错误退出报成功。移桶后格式化误拆 :=，
第二次 EXIT=2 / 28.519秒；已恢复词法，未更改任何数学陈述或证明路线。

## 无条件主目标已通过正式构建

make lean EXIT=0 / 18.032594秒 / 12842 jobs，macOS ARM 热树。
精确收据 make-lean-final-receipt.json，完整日志 make-lean-final.log。
LEAN_CACHE 仍为 present/none，stamp_miss=null，两层 warm，missing_olean=0。

sloane_sellers_parity 已无条件证明八个具体计数输入；signed_nonsquashing_diff
直接实例化原 signed_diff_of_parity，签名与用户 n≥2 目标一致。
两条 #print axioms 均仅 propext/Classical.choice/Quot.sound；新增四条
elaborated 依赖断言核出主定理→奇偶事实/旧条件桥，以及奇偶事实→两条计数递推。
printed_odd_rule_false 保留为 private；0/1 totalization 和 odd m>0 域不变。

本轮临时 Counting/Parity 报告代码已迁入 D5 正式模块（历史提交保留），
不保留第二份活证明真源。attempt 2 的 Bridge.lean 与报告原样保留。
尚待 canonical report、Scribe、冻结和 PR；不提前报本轮“成”。

Canonical make lean-report EXIT=0 / 78.220363秒；delta added=2/recheck=2，
raw report SHA256=a2d0bb7aa5f236535f2261ff8f52e3f4ede0ebb844a2c48a34fcf084aed2ce3b。
这次报告包含正式 D5 的两模块，已不再仅为 report 目录片段检查。


## Scribe 与集成准备

首轮 make emit EXIT=0 / 66.799955秒，两个正式镜像均生成；随后为八个
量化子句加括号，避免合取作用域的阅读歧义，正在再发射最终投影。
两篇 Scribe 均使用 typed Describe/StatementSource 与已核定位的 Library note。
未新建 Problems、理论源卷或 atom；原独立定义的方向不变。
2026-09-10 git fetch origin dev 成功，origin/dev=a3da3ff01f（完整 SHA 见 git）。
git merge-tree --write-tree HEAD origin/dev EXIT=0，预览 tree=65ae35549b2dc09f0e8a22c41b1a0d973944e78f。
此为合并可行性预检，未合并或宣称 CI 已绿。

## 首冻逐声明账目

比较基线为 82938786158c163b50350c14c948e63df61107a8；两模块均在此基线上未冻结。
下表 C 指 D5/S1/Recurrence/Partitions/NonsquashingCounting，
P 指 D5/S1/Recurrence/Partitions/NonsquashingPaperfold；所有 GID 由此前缀加点号展开。
四条手写公开 theorem 均为 proof_shape=content、admission_basis=escape-witness。
其余私有引理不独立申请义务或冻结。以下直接依赖指内联私有辅助后的公开定理边；
基线既有冻结直接依赖均为空，同 PR 新冻边另明确列出。

| 公开定理 GID | statement_id | 同 PR 新冻直接公开定理依赖 | escape_witness |
| --- | --- | --- | --- |
| C.count_odd | sha256:a054370ef34bea193eac5e382a4842e01757d090a4d69fa3e1eed53686d3aee4 | [] | C.card_extension + C.even_exception |
| C.count_even_step | sha256:e2647ee7751140f0ac9981374a0e9c964a5be8c78108895a44bc18296f13559b | [] | C.card_extension + C.even_exception |
| P.sloane_sellers_parity | sha256:a332571ad483d5422d4aea0570d87acf53eee5ea3de6103ca6349fa4609b7fa0 | C.count_odd、C.count_even_step（身份见上两行） | P.four_two + P.four |
| P.signed_nonsquashing_diff | sha256:56a6f4568bd09e1842e78e68d6d6c38ae8fc8fdfb34d9821f58ea2218b881738 | P.sloane_sellers_parity（身份见上一行） | P.parity_complement + P.complement_of_halving |

计数定义的公开输入身份：C.nonsquashingDistinctPartitions，
statement_id=sha256:d57626962d92cee485a5339466a24e4b7c74678f109fef75bf5d171b22c6243d。
它作为定义出现在两个模块的类型中，不冒充已提供计数结论的冻结定理。
以上依赖为消费者→前置方向。计数模块无仓内 import，直接使用钉版 Mathlib 一般基数 API。
主定理的旧桥处于本模块的私有证明链中，从未在基线冻结；本轮复用其已有证明项，
所以不能把“源码末行是 exact”误判为仅实例化已冻结主结果。

逐项对照第3.2条：

- C.count_odd：i. odd_sum/even_sum 调用 card_extension，后者的双射证明含 erase_max_parts；
  ii. 没有冻结前置提供该分拆族的基数双射；iii. 双射到过滤后的累计族不是奇偶相邻计数等式；
  iv. 去掉它不能得到 odd_sum/even_sum，差一结论使用二者，非丢弃合取分量。
- C.count_even_step：i. 两次 even_sum 均经 card_extension/even_exception；
  ii. 冻结前置没有累计和公式；iii. 最大部件构造不是偶项差分的定义重述；
  iv. 两个累计和等式实际进入 omega 消元，缺少它们便无差分结论。
- P.sloane_sellers_parity：i. eight_two 等七个构造字段实际调用 four_two/four；
  ii. count_odd/count_even_step 的实例化本身不提供所有 m 的模四规律，需新的归纳；
  iii. four_two 是单个模四进展式，不等价于八字段结构；
  iv. 归纳基于 b2，归纳步使用两次 step 与 odd，所得式实用于构造七字段。
- P.signed_nonsquashing_diff：i. signed_diff_of_parity→diff_four/diff_four_one→
  parity_complement→complement_of_halving，已 elaborate 的直接边由 run_cmd 断言；
  ii. 冻结前置的计数或奇偶断言不含独立 c 的互补式，需要强归纳；
  iii. 正 r 的 B(4r)%2+c(4r+1)=1 既不是所有 n 的带符号差分，也非定义等价；
  iv. 该式在模四零、一分支实际用于整型差分推导，没有作为死项或弃置分量塞入。

SloaneSellersParity 自动生成的八个投影 odd/eight_two/eight_six/sixteen_four/
sixteen_twelve/sixteen_zero/thirtytwo_eight/thirtytwo_twentyfour 是具名伴随结果：
proof_shape=bind-only，escape_witness=null，模块 admission_basis=escape-witness。
义务是用户明确列出的八项输入接口；消费者→前置的边为
signed_nonsquashing_diff→signed_diff_of_parity→各差分/折半分支→相应结构投影。
定义、结构构造器及 Lean 自动生成的递推方程/归纳器不冒充额外手写公开定理。

两个模块 utility=none：公开内容均为无界组合等式、归纳性质和符号恒等式，
不是有界枚举、检查器、数值归约或已认证有限实例。私有 b2/边界回声只服务
归纳初始化或源码语义核对，不单独作为正向实例冻结；printed_odd_rule_false
是保留的私有印刷勘误见证，不能用它替其他内容取得用途依据。

## 最终未主张与证据边界

已证明八项奇偶事实及 n≥2 的无条件目标；未发现或主张目标反例。
不主张全球检索完备、数学首创、OEIS 全部附带叙述已证，亦未向 OEIS 发送消息。
没有私有 axiom、目标公理化、循环定义、native_decide 或公开有限枚举交付。
#print axioms 与 canonical report 的四条手写 theorem 均只有
propext、Classical.choice、Quot.sound；不把标准三条说成无任何公理。
ASSUMED-UNVERIFIED：本轮未真正打开的外链与第三方页面，只沿用有出处的历史收据。
单 Codex worker 实施与自查，独立评审席0；未主张独立多模型复核。

最终括号订正后 make emit EXIT=0 / 61.025375秒；make-emit-final-receipt.json。

## 自动生成的公开 theorem 明细

以下亦逐条计入首冻声明集合，不声称其为额外内容。各行 proof_shape=bind-only、
escape_witness=null、基线直接冻结定理依赖=[]，伴随模块 admission_basis=escape-witness。
结构投影义务与方向见前文；eq_def 的义务是独立递推接口，
signed_nonsquashing_diff→c 分支引理→paperfoldVariant.eq_def。

| GID（P 前缀如上） | statement_id |
| --- | --- |
| P.paperfoldVariant.eq_def | sha256:ba33f7e749c40a0ef495299104bc6a216cdc3db2629bf4c41114a59d31b14e90 |
| P.SloaneSellersParity.sixteen_four | sha256:bd9477b1db5547292c572a5e9aa9941467d792fd7affdeda65bdefbd63c4ab3b |
| P.SloaneSellersParity.sixteen_zero | sha256:3ead869f6e4e9fb2fc640275607fc91ea3f7b2ded4edf95355a0a60ce8dd865d |
| P.SloaneSellersParity.sixteen_twelve | sha256:9b1f7000c03aa756aaeba61af5c6fcfa4c2dc8f18989d793595d94670c5ca3ce |
| P.SloaneSellersParity.thirtytwo_eight | sha256:ccbd9110e5429febe60ab00f6c9264268b2af4cd19dd496f50b618e2e70cb2d9 |
| P.SloaneSellersParity.thirtytwo_twentyfour | sha256:b9b6770400ae8e818b4f9b130cae12b20e8e05fdf1f4ede0a428a294ff3403b1 |
| P.SloaneSellersParity.odd | sha256:d615e84b0a23e09ad0aa4851783f286d8fe31ba1202c79e7074be709347d869b |
| P.SloaneSellersParity.eight_six | sha256:41bc65276c75241441078f158758649cb948e4db98116927b4c14a966d97a266 |
| P.SloaneSellersParity.eight_two | sha256:112754547cefe8335f152ff9b5d38c5744b7f39a8d9d8ae264fcb07ecd3f4906 |

计数模块 deposit-uncovered EXIT=0 / 82.623293秒；ledger-align --add 已写入
Golden/Frozen/state/D5/S1/Recurrence/Partitions/NonsquashingCounting.lean.json。
见 deposit-counting.log 与 deposit-counting-receipt.json；未生成或覆盖 atom。

差分模块 deposit-uncovered EXIT=0 / 82.617218秒；ledger-align added=1、conflicts=0。
两个模块均按 NO_ATOM 路径首冻，自动生成的 Freeze 事件与状态片一并提交。

NonsquashingCounting 模块 pin=sha256:978be9cb51fc05c6ba2da4932ca0f8f598d2d56690823b89f7d7057488275680；Freeze event=sha256:6fae1b25abf98cb5e6448b5454008d2fc78cd5094cd258d5600dd872f0af17a0。

NonsquashingPaperfold 模块 pin=sha256:ffa0bdff8e180811684e2595da191b7be46d327af4a4f04b3a1999756be53a26；Freeze event=sha256:133c77e3702a3a8e5304461bb0802cc516baf5a345c21e32e19fbedb789f4c59。

## 本地交付检查已完成

bash tools/scripts/workflow/scribe-content-checks.sh
.lake/build/stratalint/raw-lean-report.json ""
82938786158c163b50350c14c948e63df61107a8：EXIT=0 / 23.757865秒。
实际执行 describe-report --check、markdown-check（真 KaTeX）；
markdown: judged=2 formula(s)=7 red=0。
本 delta 未触及 Golden/Projection 或 Scribe producer，脚本未触发 projections --check；
不把跳过说成执行过。Library 的在线 DOI OBSERVE 只是离线门的能力边界，
本题引用的定位事实按前述当场阅读收据提供。完整日志 scribe-content-checks.log。

git diff --check EXIT=0；正式两模块内 sorry/axiom/native_decide 检索零命中
（rg 的无匹配退出1，非构建错误）。attempt 2 目录相对 dbc4935545b4 无差异。
最终 diff 为17文件：两依赖模块、四个镜像、两个来源 note、四个冻结工件与
五个保留的历次实施文件；超过p75=13是同一证明链和历史留存，不拆散数学依赖。
未改 docs/develop/theory 或 Meta/Digestion。

冻结后合并预检：HEAD=80f0c70f053af033e3ad45ae200c09a1dc56823f，
origin/dev=c6502d134e1483b4a2142f2781cb65372d7b67a9，
merge-tree EXIT=0，tree=e45ecc1ff228682863b8061652d02b4a20e9abc1。
下一步仅开 PR 并等 required-CI 判词；主证明源码自 make lean 成功后未改。

## PR 已创建

PR https://github.com/the-omega-institute/trureturing/pull/6754，base=dev。
make pr-open 已创建成功，正在同步等待三项 required checks；未启用 auto-merge。
本次提交只追加 PR 定位，Lean/Blueprint/Library/冻结面均未变化。
最终 CI 判词与交付 SHA 写入 runner attempt-3/result.json 及 pr-open-receipt.json，
避免为重复记录同一检查而无限追加触发新 CI 的报告提交。
