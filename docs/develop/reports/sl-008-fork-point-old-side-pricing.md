# SL-008 fork-point 旧侧迁移离线定价

> **REPORT-ONLY / 测量 worker 产物。** 本轮不修改 harness、CI、admission 或 SL-008；只对本地 `origin/dev=55a4369ce4962d8c979d4418b62555c69c1ec09b` 的历史和生产 helper 做离线测量。

## 0. 一句话结论

**PROCEED：40 个样本中估计 cache 命中 `37/40 = 92.5%`，超过 80% 门槛；一次空 report cache 实产为 `real 149.71s`、`EXIT=0`，低于现有并行 `candidate-engineering=184s`，按 `3/40` miss 率折算的期望产出负担为 `11.23s/PR`。** 这不是“最坏端到端增量为零”的声明：admission 仍依赖 Lean reports，单次 miss 可能延后 admission 起跑；这里只按 brief 指定的命中率和现有并行吸收判据立项。

## 1. 病灶与税

SL-008 当前逐字节要求候选保留 protected base 的冻结账本。冻结账本是 append-only 的内容寻址分片；候选分叉后 dev 新增分片，会被误读成候选删除 protected-base 文件。共享上下文的原始读数是：失败 CI run 口径 `2/35 = 5.7%`，但已合入 PR 中含 merge-dev 追平提交的口径为 `30/40 = 75%`。

其中机制归因必须扣除 #1346 与 #1335：这两个 PR 的 dev 同步没有带入冻结分片。因此 **SL-008 base 追平税的机制归因上界是 `28/40 = 70%`，不是 75%**。`30/40` 只描述同步现象，不能冒充 SL-008 因果数。

正解不是只换账本路径，而是把旧侧的树、Lean report、DAG、冻结账本作为一个能力包一起从 protected base 迁到 fork point。第三份 merge-base Lean report 是这个能力包的成本变量。

## 2. 测量方法

样本选择命令与原始样本数：

```bash
git log --first-parent --format='%H%x09%P%x09%s' origin/dev \
  --grep='^Merge pull request' -n 40
# 40 lines; #1358 through #1313
```

每个 merge 均按以下原命令取父与 fork point：

```bash
base=<merge>^1
head=<merge>^2
fork=$(git merge-base "$base" "$head")
```

为每个 SHA 用 `git archive` 建独立绝对路径临时树，并调用该树内的生产 helper。实际调用原文为：

```bash
/usr/bin/env bash \
  <absolute-tree>/Meta/StrataLint/scripts/report/lean-report-input.sh \
  address --repository <absolute-tree>
```

helper `address` 的原始输出是四列：`repository_address producer_sha lean_sources_sha config_sha`；CI cache key 使用第一列 `repository_address`。80 次调用（40 base + 40 fork）全部 `EXIT=0`。

“跨 PR 命中”严格排除当前样本自身：若同一 PR 的 fork/base 相同，它只计入第一行；只有另一个 PR 的 `addr_base` 相同才计跨 PR。并集是两谓词的逻辑或。

## 3. 命中率读数

| 判据 | 原始计数 | 比例 |
|---|---:|---:|
| 同 PR：`addr_fork == addr_base` | 23/40 | 57.5% |
| 跨 PR：`addr_fork` 命中其它 PR 的 `addr_base` | 34/40 | 85.0% |
| 两者并集（估计命中率） | **37/40** | **92.5%** |
| 并集 miss | 3/40 | 7.5% |

这个 92.5% 是固定 40-PR 窗口内的离线估计，不是 GitHub Actions cache 的在线命中遥测；窗口外已有 base cache 只可能把这里的有限窗口 miss 进一步变成 hit，本报告没有测该在线集合。

## 4. Miss 与原因

三个 miss 都是 fork 到 base 的 **producer 闭包**变化，不是 Lean sources 变化；其 config hash 也未变。

| PR | fork -> base | `.lean` fork->base | producer 差异 | 该 PR 自身是否改 `.lean` |
|---:|---|---:|---|---:|
| #1315 | `d66b0844` -> `1fad2b44` | 0 | 7 个 Engine/CLI `.cs` 路径变化 | 是：新增 `D5/S3/Arith/Congruence/QuarticThirtySix.lean` |
| #1314 | `d88d7290` -> `72193105` | 0 | `EchoVerifyCommand.cs`、`RepositoryPathPolicy.cs` | 否 |
| #1313 | `d88d7290` -> `e1cfc429` | 0 | `EchoVerifyCommand.cs` | 否 |

因此“miss 是那批 PR 真的改了 `.lean`”不成立：#1314、#1313 没改，#1315 虽自身新增 Lean 文件，但它的 fork address miss 由 fork 后、merge 前 dev 上的 producer 演进造成，而不是 fork->base 的 Lean source hash 变化。

## 5. 冷态生产成本

这里的冷态是 **report cache 为空**、Lean build cache 保持现有 CI 常态。命令与原始结果：

```bash
cold_root=$(mktemp -d /tmp/oldside-cold-report-cache.XXXXXXXX)
/usr/bin/time -p env STRATALINT_REPORT_CACHE_ROOT="$cold_root" make lean-report

# LEAN_CACHE status=present method=none
# LEAN_REPORT_PROVENANCE side=candidate mode=produced ...
# real 149.71
# user 178.03
# sys 141.61
# COLD_REPORT_EXIT=0
```

生产输入地址为 `8e7706516aac42673a60f54e87e18bd3c4dba3c977de6af61528e78527078fea`，report SHA 为 `41757118fea1ceb37ed180effb87f27c9c7ee05dacd2f3b700717c193630726a`。以 `3/40` miss 率折算，`149.71 * 3/40 = 11.23s/PR`。单次 149.71s 小于共享上下文实测的并行 candidate-engineering 184s；但由于 admission 等待 reports，最坏端到端增量仍取决于实施后的 job/依赖编排，**ASSUMED-UNVERIFIED：本轮没有改 CI，故没有实测三 report CI DAG 的端到端时间。**

## 6. 已知退回与本方案差别

- #1159 只把冻结账本旧侧迁到 fork point，却仍用 protected-base DAG/Lean report 佐证。
- #1166 实测后，原误拒只换成 `Closed module ... has no Freeze attestation`；误拒频次没有消失，半迁移被退回。#1169 同族亦退回。
- 本方案的区别是**整侧同迁**：fork-point tree、第三份 fork-point Lean report、由其得到的 DAG、fork-point ledger 同属一个 old-side 值；类型上不允许把 protected-base DAG 与 fork-point ledger 混装。它不是 #1159 的路径替换重演。

## 7. PROCEED 的分步骨架

以下只提炼共享上下文与 brief 的六席一致方向，不另造方案。

1. **Expand：增加第三份 fork-point report，不切换判词。** 机器判据：helper 地址、report attestation/provenance 与 merge-base tree 一致，既有 baseline/candidate 两份仍逐字节维持。回退点：删除新增的独立产出/传递，不影响当前 admission。
2. **封装 old-side 能力包。** 将 tree identity、Lean report、DAG、ledger 绑定为一个显式 old-side 类型。机器判据：构造器只接受同一 fork-point 身份，混入 protected-base report/DAG/ledger 的负例编译失败或测试判红。回退点：旧 `Baseline` 通路仍是唯一消费方。
3. **双跑但不改 admission 结果。** 新路径计算 fork-point 整侧判词，旧路径继续承权。机器判据：历史 admit 不能被新路径 reject；覆盖分叉后 dev 新增 Freeze/Closed module、无 dev 同步、以及 #1159/#1166 的混侧回归夹具。回退点：停止影子计算。
4. **切换 SL-008 的旧侧消费。** 树、report、DAG、ledger 在同一提交一起切到 fork-point 包。机器判据：旧 harness admit 的 corpus 全部仍 admit（保守扩展），base 追平夹具不再误拒，真实删除 fork-point 冻结分片仍 reject。回退点：整包切回 protected-base，禁止单字段回退。
5. **Contract：删除可表达混侧的旧入口。** 机器判据：代码搜索与类型测试证明不存在 ledger/report/DAG 分侧注入路径；CI 三份 report 的 cache key/attestation 均可复核。回退点：只回退 contract 提交，保留已验证的显式能力包。

## 8. 40 个样本的原始地址

SHA 列为 8 位展示，两个 address 为 helper 第一列的完整 64 hex。`cross-other` 排除自身。

| PR | merge | base | head | fork | addr_base | addr_fork | same | cross-other | union-hit |
|---:|---|---|---|---|---|---|:---:|:---:|:---:|
| #1358 | `55a4369c` | `e06e7cd9` | `61b798d9` | `fb0a971b` | `4e49515cc2fbdd841a027f3a613ef2a7aad0bd4baa9ad0fd0c906c64c5810382` | `4e49515cc2fbdd841a027f3a613ef2a7aad0bd4baa9ad0fd0c906c64c5810382` | yes | yes | hit |
| #1354 | `e06e7cd9` | `fb0a971b` | `f7dbdc0c` | `922b87b8` | `4e49515cc2fbdd841a027f3a613ef2a7aad0bd4baa9ad0fd0c906c64c5810382` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | no | yes | hit |
| #1356 | `fb0a971b` | `61a6e046` | `1fa249b0` | `922b87b8` | `4e49515cc2fbdd841a027f3a613ef2a7aad0bd4baa9ad0fd0c906c64c5810382` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | no | yes | hit |
| #1353 | `61a6e046` | `c42e121e` | `275d1dc3` | `922b87b8` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | yes | yes | hit |
| #1355 | `c42e121e` | `922b87b8` | `f36dee3c` | `922b87b8` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | `dea6403c3b70b49a5d53f6d805cea534fec66a895febfae7653de931ffb2f824` | yes | yes | hit |
| #1352 | `922b87b8` | `dda7a419` | `a87b1429` | `08304f38` | `bed457fbf8c37e876e39110602be0db8841b812998d9570fd25c7686e192c519` | `bed457fbf8c37e876e39110602be0db8841b812998d9570fd25c7686e192c519` | yes | yes | hit |
| #1350 | `dda7a419` | `08304f38` | `fb886d81` | `08304f38` | `bed457fbf8c37e876e39110602be0db8841b812998d9570fd25c7686e192c519` | `bed457fbf8c37e876e39110602be0db8841b812998d9570fd25c7686e192c519` | yes | yes | hit |
| #1351 | `08304f38` | `cfaee8cf` | `cb39d712` | `84769898` | `bed457fbf8c37e876e39110602be0db8841b812998d9570fd25c7686e192c519` | `a03e1c81c5ae020a283ca2b54fe33d2022f75e64bde3e897dca52d2e6c5dba96` | no | yes | hit |
| #1340 | `cfaee8cf` | `84769898` | `2738aabc` | `0630f49e` | `a03e1c81c5ae020a283ca2b54fe33d2022f75e64bde3e897dca52d2e6c5dba96` | `489c595187d23572a1670a8336f1efb4b327dcb79e57cecc0c971d7ab1d304c0` | no | yes | hit |
| #1345 | `84769898` | `0630f49e` | `559e3ee5` | `35c393a3` | `489c595187d23572a1670a8336f1efb4b327dcb79e57cecc0c971d7ab1d304c0` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | no | yes | hit |
| #1343 | `0630f49e` | `8c2260a0` | `1cf38ddc` | `c321e0de` | `70a5b92b10fdcb25c6ebfef3aeba2b6cca5308657031b62618a25a72c448a3bd` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | no | yes | hit |
| #1349 | `8c2260a0` | `8773ecff` | `844ee012` | `35c393a3` | `a53492f6819a9e95031c7c8578ced5398a83c2538990dd3fbadd432c61d0b701` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | no | yes | hit |
| #1346 | `8773ecff` | `35c393a3` | `ac191b15` | `7e11a956` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | yes | yes | hit |
| #1347 | `c321e0de` | `7e11a956` | `5743d114` | `d18e78f7` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | yes | yes | hit |
| #1339 | `7e11a956` | `d18e78f7` | `3b266523` | `d18e78f7` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | `f8b7d7e08516772521733158ccb977b5971a88527df74bccba0360d5c50a7e6e` | yes | yes | hit |
| #1338 | `d18e78f7` | `995d75c7` | `46220826` | `5ef2909f` | `ad95367cad9f96099db65d5df175dd339b5574ccef2cacf5e0af675ec22b1078` | `ad95367cad9f96099db65d5df175dd339b5574ccef2cacf5e0af675ec22b1078` | yes | yes | hit |
| #1341 | `995d75c7` | `5ef2909f` | `4ee704fb` | `5ef2909f` | `ad95367cad9f96099db65d5df175dd339b5574ccef2cacf5e0af675ec22b1078` | `ad95367cad9f96099db65d5df175dd339b5574ccef2cacf5e0af675ec22b1078` | yes | yes | hit |
| #1332 | `5ef2909f` | `d8e2a181` | `33ec56a9` | `f50c827a` | `5601f8e9fdead4a8b16fa65330c94d1193b124b282b6d8e04fe51e8d04a97cd0` | `9cb1250d9e44fd67a33e4afe1f7b4aa61668ce0d1189defbcbacd9f668620116` | no | yes | hit |
| #1336 | `d8e2a181` | `1bc7b463` | `79d717d2` | `1bc7b463` | `6a3449e098501af542733471827c025e093e23bb829b83adc621a892749eb4bb` | `6a3449e098501af542733471827c025e093e23bb829b83adc621a892749eb4bb` | yes | no | hit |
| #1335 | `1bc7b463` | `a00317a3` | `feaf6045` | `f50c827a` | `14c2fd48c31b03d17f33ad9c5e130172b223adc5b8bee6eb49c88bf255d71b1a` | `9cb1250d9e44fd67a33e4afe1f7b4aa61668ce0d1189defbcbacd9f668620116` | no | yes | hit |
| #1331 | `a00317a3` | `a1480c72` | `b2bea3a7` | `25222201` | `52e88703486f01f18fa166073e5aa89595d11dc71bb92790edbd05be77e9c2a9` | `9e79c9b75205fd194b984339bd1c467d6a2ad131c92519b7e9b9a48bb6cb6970` | no | yes | hit |
| #1334 | `a1480c72` | `f50c827a` | `3f2d75f2` | `f50c827a` | `9cb1250d9e44fd67a33e4afe1f7b4aa61668ce0d1189defbcbacd9f668620116` | `9cb1250d9e44fd67a33e4afe1f7b4aa61668ce0d1189defbcbacd9f668620116` | yes | no | hit |
| #1320 | `f50c827a` | `7ccbfffe` | `5aee88a9` | `738c2d08` | `9e79c9b75205fd194b984339bd1c467d6a2ad131c92519b7e9b9a48bb6cb6970` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | no | yes | hit |
| #1333 | `7ccbfffe` | `25222201` | `9a10881a` | `25222201` | `9e79c9b75205fd194b984339bd1c467d6a2ad131c92519b7e9b9a48bb6cb6970` | `9e79c9b75205fd194b984339bd1c467d6a2ad131c92519b7e9b9a48bb6cb6970` | yes | yes | hit |
| #1330 | `25222201` | `767e2c21` | `a6f0e178` | `1843022f` | `9bceeb6a93f9eeb4e70da09bd187765ee8c7069568a0246fcaf97faf6061b6a5` | `3b37d7c1abf78aad4dc04363bd63321cc7249d2cd2455dbd24967d2435dafd90` | no | yes | hit |
| #1329 | `767e2c21` | `1843022f` | `d3c7310f` | `1843022f` | `3b37d7c1abf78aad4dc04363bd63321cc7249d2cd2455dbd24967d2435dafd90` | `3b37d7c1abf78aad4dc04363bd63321cc7249d2cd2455dbd24967d2435dafd90` | yes | no | hit |
| #1328 | `1843022f` | `429fd56f` | `d4728d48` | `738c2d08` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | yes | yes | hit |
| #1327 | `429fd56f` | `738c2d08` | `e8151a52` | `738c2d08` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | yes | yes | hit |
| #1319 | `738c2d08` | `fe942bc1` | `2863a7ce` | `fe942bc1` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | `ed26db08378648c408e97240bac04c71e6e24f1db02248333c76435b0dc07482` | yes | yes | hit |
| #1324 | `fe942bc1` | `72a382f9` | `631b98d3` | `30973ef4` | `b0a37858026f6e397ceae2c22ea8ca674709e0704b4c4e9cc2161e912fb5f7f2` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | no | yes | hit |
| #1323 | `72a382f9` | `eff93ae6` | `046c2e43` | `30973ef4` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | yes | yes | hit |
| #1325 | `eff93ae6` | `30973ef4` | `9148de53` | `30973ef4` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | yes | yes | hit |
| #1322 | `30973ef4` | `38020e03` | `b7f0fb58` | `38020e03` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | yes | yes | hit |
| #1321 | `38020e03` | `7665a09e` | `4b4ab1b3` | `7665a09e` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | `a5a125d14c6857e3dedce86483da89bb3b4bcd2fa5048a5b94e98481da32f826` | yes | yes | hit |
| #1318 | `7665a09e` | `81cd92cb` | `76458622` | `fc5476ad` | `5b0c19a1c0bfec7aced1c8b51eb60584bde18beb6144220c787024badaccd01b` | `5b0c19a1c0bfec7aced1c8b51eb60584bde18beb6144220c787024badaccd01b` | yes | yes | hit |
| #1316 | `81cd92cb` | `fc5476ad` | `cd29ad09` | `fc5476ad` | `5b0c19a1c0bfec7aced1c8b51eb60584bde18beb6144220c787024badaccd01b` | `5b0c19a1c0bfec7aced1c8b51eb60584bde18beb6144220c787024badaccd01b` | yes | yes | hit |
| #1317 | `fc5476ad` | `96855375` | `d1d2cbfe` | `1fad2b44` | `0a081d3cb9e5f0a39499d0c99b9f8aa2f0ff0d5a3b2318897e4ee9ce8774f821` | `08bf68d2c94e9123bf2a81fc7dfcff9df4c580bc4702751e258f112a0876bd2b` | no | yes | hit |
| #1315 | `96855375` | `1fad2b44` | `ec38f257` | `d66b0844` | `08bf68d2c94e9123bf2a81fc7dfcff9df4c580bc4702751e258f112a0876bd2b` | `b8172b90d0d0e6a0583cf9cbce6cde3a98331b19fa9ab2353eae2ea262e39c35` | no | no | MISS |
| #1314 | `1fad2b44` | `72193105` | `965c2b76` | `d88d7290` | `250fae11b16a1f84e5bf311aa949201f9c04aed5986e54840c46c12548a0c901` | `ea03df2274daddf16ee43b47309bb890f21b26916962992706a385fd040aab57` | no | no | MISS |
| #1313 | `72193105` | `e1cfc429` | `dd105a9e` | `d88d7290` | `7043ef2f77909135b1cc5e51bde7cb067b8282f65129521ab8552cc09139dc75` | `ea03df2274daddf16ee43b47309bb890f21b26916962992706a385fd040aab57` | no | no | MISS |

## 9. 范围与偏差

- 未修改 `.github/workflows/**`、admission、SL-008 或任何 harness 行为。
- 本地 `origin/dev` 没有 brief 所称的 `docs/develop/reports/**` FILEMAP 声明；该声明存在于历史提交 `6481c5f94591cb2c165addc505aaae0f91704da1`，但不在本地 `origin/dev` 可达历史中。本提交按该先例新增同一声明；FILEMAP policy 定向测试 44/44 通过。
- 未测 GitHub Actions 在线 cache inventory；所有命中率均来自指定 40 个 base address 的集合。
