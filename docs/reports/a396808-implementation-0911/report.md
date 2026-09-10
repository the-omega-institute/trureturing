# A396808 模 3 精确支持：实施记录

产地：Codex 实施席，使用 lean4 skill；单席直接实施与自查，未作独立评审，未主张多模型共识。任务由用户 brief 给定；用户已有探针在下面另行亲跑核验。

基线：`2d8af6a6dd0beb23d4c3a4ac86fc2ea2b263a363`；工作分支 `lane/math/a396808`。

## 预登记目标与判据

第一档，OEIS 评注猜想。目标是对所有 n>1，在同一个定理中结算模 3 两类支持及零值；复用冻结模块的 a 与 source_equation，不修改冻结文件。拟议 escape_witness 为候选 R 满足约化源方程，禁止把该命题当作最终结论的假设。

候选 S = Σ x^((3^k−1)/2)，R = 1+x+2x³S(x³)²。先建立严格前缀分解与唯一性，再证明候选源方程和两类支持不交。若候选源方程需要假定目标本身，停止并给出实际 Lean goal。数值不是形式化进展，不冻结有限正向实例。不创建理论卷，不 ingest、不造 atom。

## 开工读取与数值收据

完整阅读 CLAUDE.md、agents/CONTEXT.md、lean4/SKILL.md、冻结基模块公开面及私有证明；utility 文法已查 spec A5.1，非计算性一般证明使用 `utility: none`。Arith 已注册 S3。`find D5/S3/Arith -maxdepth 1 -type f | wc -l` 得 34；递归计数 123，不将两种口径混用。

`numeric_probe.py` 实现用户指定的严格前缀递推、二进制幂和截断乘法。重现前先 `curl -L https://oeis.org/A396808/b396808.txt -o /tmp/a396808-bfile.txt`，再运行 `python3 docs/reports/a396808-implementation-0911/numeric_probe.py`。实测 0.663 秒；完整读数见 numeric_probe.json。

- 18 项精确整数与实际下载的 https://oeis.org/A396808/b396808.txt 前 18 项相同。
- 2…200：幂支持 {3,9,27,81}；配对支持 {6,15,18,42,45,54,123,126,135,162}；其余 185 项残基零；两条 iff 零反例。
- 0…400：S 方程零差异，R 对递推零差异。
- 已打开 https://oeis.org/A396808/internal，%C 逐字仍标两条模 3 命题为 Conjecture。

## 检索收据

① 本仓 D5：rg A396808/a396808/coeff_pow_eq_strict_trunc_add/source_unique；精确序列仅命中 ArtinSchreierTracePowersOfTwo。完整读其公开面：prefixPolynomial_eq_sum、source_equation、normalized_solution_unique 可复用；F₂ 定理不能参数实例化成 F₃。严格前缀与唯一性 helper 是 private，按 brief 与第 3.1 条④本地证明。

② 钉版 mathlib v4.33.0，rev db584cd6d46c92f209a44c0f1c829460d327499d：rg Lagrange inversion / coeff_pow / trunc / frobenius；未见源方程唯一性或本题精确支持。命中 PowerSeries.trunc_trunc_pow、MvPowerSeries.map_frobenius_expand、PowerSeries.coeff_expand_mul 等，直接用于本地证明。

③ 实测外部搜索：Loogle JSON 查询 `"A396808"` 返回 0；`"coeff_pow"` 返回 25，其中 PowerSeries 的三项均非本题或严格前缀桥；`"Lagrange"` 返回 76，模块仅插值与 Taylor，无反演。`gh search code A396808 --language Lean --limit 20 --json repository,path` 返回 []。未认证 GitHub REST code search 返回 401，不把该请求作为阴性证据。Leansearch 首页可达，但未执行其语义搜索，不计入搜索结果。上述有界范围未命中，按④本地证明。

文献：亲自完整提取并读完 A038464、A396838、A396839 internal 的全部字段；未见模 3 猜想的证明。arXiv API `all:A396808` 和 `all:Hanna AND (all:congruence OR all:"power series")` 均 HTTP 200、totalResults=0。仅在这些明确范围裁 open，不主张全网没有证明。

反演方向校正：记 A 为 A396808、B 为 A396838。A396808 的公式 (4) 声称 A=B(xA)，但二次项给 5≠3；A396838 的公式 (2) 正确方向为 B=A(xB)、A=B(x/A)。这个页面冲突不涉及本题源方程或已核验的数值读数。后续不以任何未经证明的反演联系承重。A396839 的自卷积链接亦未作为形式定理使用。

## 已完成的无限证明

正式模块 `D5/S3/Arith/TernaryTraceSupport.lean` 只公开统一定理 `a396808_mod_three`，对全部 n>1 同时给出两个支持及余下残基零。所有辅助声明均为 private。未修改被冻结的基模块。

1. 对任意交换环建立严格前缀系数分解，以恒等式 (n+1)²−n(n+2)=1 得无除法递推，强归纳得唯一性。将公开 `source_equation` 沿整数到 ZMod 3 的环同态约化。
2. 定义 t(y)=Σ y^(3^r)，由 Frobenius 证明 t³=t−y。证明两项三幂和的排序指标唯一，进而计算 t² 的全部系数：对角为 1，严格异指标为 2，其他为 0。
3. 定义 U=1+y²−t⁶、R(n)=[y^(2n)]U，证明 U=1+t²+t⁴ 及 U=R(y²)。这是给定候选的偶变量表达；数学上 t(y)=yS(y²)。
4. U 与 (t²+t)²、(t²−t)² 均满足 z³=z²+y²z+y⁴。三根的 m 次幂和对应多项式满足 T₀=0、T₁=1、T₂=1+2X 及 Tₘ₊₃=Tₘ₊₂+XTₘ₊₁+X²Tₘ，次数不超过 floor(2m/3)。另两根阶至少 2，推出 floor(2m/3)<n<m 时 [x^n]R^m=0。
5. 消失带加上 n=2,3,4 的私有边界推导，证明 `R_source`。由源方程唯一性得到整数序列的模三约化等于 R，再由配对计数结算统一分类。
6. `supports_disjoint` 由排序指标唯一性排除一个对角配对和一个严格递增配对具有相同幂和。最终定理在配对支持为真的分支直接调用它排除三幂支持，故不交结论在活推导路径上。

## 构建记录

各批证明历史均已 commit、push：严格前缀桥 `ee184f7e60`；Artin–Schreier 与配对唯一性 `853919f53d`；系数计数 `7e91e2660b`；迹次数界 `384c07c4e9`；完整定理 `29b313119e`。对应 bridge.log、sparse.log、trace.log、complete.log 保留。草稿 Lean 文件已合并到正式模块，旧快照可由提交历史取得。

第一次热树 Lean 尝试中的整数约化 `exact_mod_cast` 未关闭环同态 map_mul goal，已改用 `simpa using congrArg ...` 后通过。完整定理与 `R_source` 的 `#print axioms` 均只返回 `[propext, Classical.choice, Quot.sound]`。不存在 sorry、自设 axiom 或 native_decide。

`make lean-cache-ensure` EXIT=0：status=seeded，method=clonefile，donor=/Users/chronoai/trureturing，clonefile_attempts=1，stamp_miss=null，mathlib_olean_state=warm，project_olean_state=warm，mathlib_missing_olean_files=0，pin_sha256=sha256:6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e。

正式 `make lean` EXIT=0，耗时 220.484420334 秒。runner attempt 目录的 make-lean.log 与 make-lean-receipt.json 保留原始输出和计时。`make lean-report` EXIT=0，耗时 64.241444375 秒。make emit、scribe-content-checks、无 atom deposit 及 PR 尚在执行，完成后补录。

## 逐公开定理审计

唯一新增公开定理：`D5/S3/Arith/TernaryTraceSupport.a396808_mod_three`。

- proof_shape: content。
- admission_basis: escape-witness；无额外数学假设，只有题定自然数索引与 n>1。
- escape_witness: 本模块私有 `R_source`，即构造的 R 对所有 n>1 满足模三约化源方程。它已由三根迹次数界证明，不是前提。
- 定理 statement_id: `sha256:1d954b0f0a1049d9e6406a70b8c81999bb8059c5a191a9dbf4a08339071fc00c`，取自本次 canonical report。
- 直接冻结依赖 GID: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.source_equation`；statement_id: `sha256:d1ebb64a4a7a6ebaa947d093e5c021b538303d8d00ca4c24d35b8618a1dc2c55`。
- 使用的冻结序列定义 GID: `D5/S3/Arith/ArtinSchreierTracePowersOfTwo.a`；statement_id: `sha256:9f1fdaa4070faa703edc6a0b374815f5508ec3207cd689a203968973a69a157f`。a₀=a₁=1 由该公开定义的 rfl 得到。
- 上述冻结声明身份直接读取 accepted 事件 `1e65aaf8f505ac0a16730bfcb2a7612743aa5b8b931c50c5a216b0fcfd9d7ea4.json`；不以模块身份代替声明身份。
- utility: none；无界符号分类，非主要计算性结论；其他 utility 字段 not-applicable(kind=none)。

第 3.2 条四项逐项核对：

1. 依赖闭包内：最终定理经 `reduced_eq_R` 调用 `R_source`，后者及其证明项均在编译后的依赖闭包。
2. 非投影可得：冻结源方程只刻画整数序列；迹恒等式与带内系数消失证明了新构造 R 满足方程，并非从冻结结论取投影。
3. 非定义等价：R 的系数方程涉及依 n 变化的幂及对角系数，与最终指标支持公式不定义等价；经迹递推和唯一性完成数学联系。
4. 活推导路径：`R_source` 是源方程唯一性应用必需的输入；移去它就不能推出约化 a=R，最终分类无法得到。`supports_disjoint` 同样在最终条件分支被实际使用。

冻结基模块状态片：sha256:49b268a8489008c167a9fb5758d2fd96efc81d1ec8a1705f01db66d3e4061241（模块身份，不冒充 source_equation 声明身份）。

## 未主张

未主张全球无文献证明；open 仅为上述明确检索范围中的文献裁决。未主张独立评审或多模型共识。数值只作探针，不算形式化进展，不冻结有限正向实例。除明确记录为亲自打开者，外部页面均为 ASSUMED-UNVERIFIED。A038464/A396838/A396839 的反演与自卷积联系不作为已证等价承重，未形式化它们。未修改或重证既有奇偶公开成果；没有自建理论卷、ingest 或新增 atom。
