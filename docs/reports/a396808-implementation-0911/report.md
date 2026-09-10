# A396808 模 3 精确支持：实施记录

产地：Codex 实施席，使用 lean4 skill；单席直接实施与自查，未作独立评审，未主张多模型共识。任务由用户 brief 给定；用户已有探针在下面另行亲跑核验。

基线：`2d8af6a6dd0beb23d4c3a4ac86fc2ea2b263a363`；工作分支 `lane/math/a396808`。

## 预登记目标与判据

第一档，OEIS 评注猜想。目标是对所有 n>1，在同一个定理中结算模 3 两类支持及零值；复用冻结模块的 a 与 source_equation，不修改冻结文件。拟议 escape_witness 为候选 R 满足约化源方程，禁止把该命题当作最终结论的假设。

候选 S = Σ x^((3^k−1)/2)，R = 1+x+2x³S(x³)²。先建立严格前缀分解与唯一性，再证明候选源方程和两类支持不交。若候选源方程需要假定目标本身，停止并给出实际 Lean goal。数值不是形式化进展，不冻结有限正向实例。不创建理论卷，不 ingest、不造 atom。

## 开工读取与数值收据

完整阅读 CLAUDE.md、agents/CONTEXT.md、lean4/SKILL.md、冻结基模块公开面及私有证明；utility 文法已查 spec A5.1，非计算性一般证明使用 `utility: none`。Arith 已注册 S3。`find D5/S3/Arith -maxdepth 1 -type f | wc -l` 得 34；递归计数 123，不将两种口径混用。

`numeric_probe.py` 实现用户指定的严格前缀递推、二进制幂和截断乘法。实测 0.663 秒；完整读数见 numeric_probe.json。

- 18 项精确整数与实际下载的 https://oeis.org/A396808/b396808.txt 前 18 项相同。
- 2…200：幂支持 {3,9,27,81}；配对支持 {6,15,18,42,45,54,123,126,135,162}；其余 185 项残基零；两条 iff 零反例。
- 0…400：S 方程零差异，R 对递推零差异。
- 已打开 https://oeis.org/A396808/internal，%C 逐字仍标两条模 3 命题为 Conjecture。

## 检索收据（持续补充）

① 本仓 D5：rg A396808/a396808/coeff_pow_eq_strict_trunc_add/source_unique；精确序列仅命中 ArtinSchreierTracePowersOfTwo。完整读其公开面：prefixPolynomial_eq_sum、source_equation、normalized_solution_unique 可复用；F₂ 定理不能参数实例化成 F₃。严格前缀与唯一性 helper 是 private，按 brief 与第 3.1 条④本地证明。

② 钉版 mathlib 与③第三方检索正在进行，未宣称 search-complete。

## 构建记录

`make lean-cache-ensure` EXIT=0：status=seeded，method=clonefile，donor=/Users/chronoai/trureturing，clonefile_attempts=1，stamp_miss=null，mathlib_olean_state=warm，project_olean_state=warm，mathlib_missing_olean_files=0，pin_sha256=sha256:6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e。

尚未运行 make lean，退出码及耗时未产生。后续全门按 make lean → make lean-report → make emit → 无 atom deposit 路径执行，PR 前另跑 scribe-content-checks。

## 逐公开定理审计

当前尚无新增公开定理。最终需逐条记录 proof_shape、直接冻结依赖的 GID 与 statement_id、escape_witness、admission_basis；content 的见证逐项核对依赖闭包、非投影、非定义等价、活路径。

冻结基模块状态片：sha256:49b268a8489008c167a9fb5758d2fd96efc81d1ec8a1705f01db66d3e4061241（模块身份，不冒充 source_equation 声明身份）。

## 未主张

尚未证明模 3 分类或候选源方程；数值只作探针。未主张全球无文献证明。除明确写为亲自打开者，brief 转述的外部页面与反演联系均为 ASSUMED-UNVERIFIED；未把 A038464/A396838/A396839 反演联系作为已证等价使用。未修改或重证既有奇偶公开成果。
