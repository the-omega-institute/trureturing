<!-- open-problem-lane reference: Closing comment (prereg issue, MERGED + SHA) and standing-goal round comment templates; placeholders __SHA__/__KPI_*__. -->

**结案：** PR #__PR__ **MERGED**，合入 dev `__SHA__`（REST `merged=true`）。三席盲评 __VERDICTS__。冻结事件 `__EVENT__`，`D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.result`（Refuted，见证合数 219781 = 271·811 同时通过 Fibonacci 测试与 Fermat 测试；n = 2 边界、May 28 变体与 219781 的先行技术均已披露）。Detlefs 2014 的素数刻画 %F 猜想已被内核反驳并落地；本单关闭。
**本轮（A000040）结算：** PR #__PR__ MERGED `__SHA__`。**KPI：本会话累计 __KPI_PR__ PR；origin/dev 全库解决标记 __KPI_MK__**。

- 问题：OEIS A000040 上 Detlefs 2014-05-25 的 %F 猜想「素数 = {5} ∪ {n≠5 : F(n) ≡ ±1 (mod n) ∧ 2^(n−1) ≡ 1 (mod n)}」——**反驳型**（有限证书：合数 219781 = 271·811 通过两测；`Nat.fastFib_eq` + `decide`、`reduce_mod_char`、`norm_num`；无私有引理，形态 (2)）。219781 作为 Fibonacci 型伪素数是已知的（A094401/A093372/A212424，已归属）；对该刻画的反驳此前未见记录；字面陈述在 n = 2 亦失效（已披露）。
- 管线：**GPT Pro 池当日不可用**，候选由 orchestrator 本地 OEIS 全文扫描得出 → 预登记 #7792（探针前）→ 探针 attempt-1（证明编译通过但自报 bind-only）→ orchestrator 依 A049591/A103585/A129598 判例裁定形态 (2) content 并重登记 → 探针 attempt-2 落模块 → Stage B → 三席 __VERDICTS__ → 合并。
- 供给读数：本地扫描五批（Cloitre/Ratajczak/Jovovic/Stephan/Murthy/Karttunen/Ordowski/Krizek/Detlefs/Ianakiev/Yanev/Firoozbakht 等 + 「iff n is prime」「verified up to」短语）：1 条反驳靶（本条）、3 条证明型 backlog（A265310、A008578、A001108）、其余条目内已结算或深题。
