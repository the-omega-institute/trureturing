# 冻结账本:字段分层、生产者/消费者链,与 git 固化能力的边界

> 历史报告勘注(2026-08-29):本文记录 v5 以前的字段普查,不再描述现役 schema。当前唯一形态见仓库 spec A14 v5;`witness_id`、坐标 input、Genesis/Reattest/Revoke 持久事件均已退役。

本文汇总冻结账本的字段分层、生产者/消费者链、git 固化能力边界与账本目的四项分析的实测结论。
所有读数取自 2026-08-17 的 dev(1986 事件、955 case)。它记述**已落地的事实**,不是新规范——
规范在 `docs/develop/spec/golden-ledger-repo-spec.md`(A14 系列),判据在 `CLAUDE.md`(第〇节、第Ⅵ节)。

## 一、三分判据(施于**每个字段**,非施于工件)

| 类 | 定义 | 处置 |
|---|---|---|
| **真源** | 树上无物可重导、断言「当时发生了什么」 | 必守 |
| **加工产物** | 由原料哈希而成、携带权威 | 存值即地址;**重算来「验证」即重放** |
| **纯投影** | 同一值的第二个名字 | 当消(一名一址) |

## 二、逐字段分类(schema v4 前的实测)

**Genesis** — `protocol_version` 真源(记录当时选定的协议,不是第二个地址名);
`generator_blob_oid`/`origin_commit_oid`/`origin_tree_oid`/`rule_catalog_root` 加工产物。

**Freeze** — 真源:`axiom_closure`、`declaration_statement_ids` 及其 `declaration_name_key`/`kind`、
`input.descriptor_selector`、`input.materializer`。
加工产物:`statement_id`、`witness_id`、`frozen_node_id`、`prerequisite_frozen_node_ids`、
各 `input.*_oid`、`declaration_statement_ids[].statement_id`。
**纯投影(已于 #2216 退役)**:`input_fingerprint`≡`witness_id`、
`node_path`≡`input.descriptor_selector`、以及常量-only 家族
`case_class`/`evaluation`/`expected.*`/`truth_state`(取值恒定,其嵌套诊断字段**无任何可达的合法取值**)。

**`semantic_receipt` 的分层勘误(2026-08-20 实测,钉 `65a18869e`)**:初稿把它记为 Freeze 的纯投影
「≡`frozen_node_id`,1094/1094 逐字相同」。三处不准:
- **范围**:今日全语料 **1985** 个事件带该字段;**同一 payload 内**与 `frozen_node_id` 相等者
  **1112**(Freeze v2 873 + Freeze v3 84 + **Reattest v2 155**)。故该等式跨 Freeze 与 Reattest 两类,
  写在 Freeze 名下是范围标错;Freeze 自身为 **957**。
- **陈旧**:1112 与初稿 1094 差 18,即三日新增。**对 append-only 语料钉计数,按构造必然陈旧**;
  本节所有计数一律是快照,须连同 SHA 读,不得当作不变量(同理适用于本节其余未重测的计数)。
- **实质遗漏(要害)**:**873 个 schema v3 Reattest 带该字段却没有同 payload 的 `frozen_node_id`**。
  那里的相等对象是**前驱链上首个 id**(873/873),是**既有语料的观测规律,不是被执法的不变量**。
  初稿把它平铺成 event-local 的重复字段,恰好抹掉了这条缝——运行时投影若拿它当当前身份,
  一条伪造别名即可改变后续 Revoke 的判决。该缝已由本 PR 关闭:运行时身份权威回到 `frozen_node_id`,
  别名仅作历史 v2/v3 字节的解析回退;行为钉子见
  `FrozenLedgerBaseViewTests.BaseProjectionConsumesHistoricalLegacyReattestBeforeRevoke`
  与 `CoverageLedgerIndexTests.LegacyReattestSemanticReceiptAliasDoesNotReplaceTheActiveIdentity`。
- **教训**:`case_id` 已因同一形态被纠正过一次(见下段)——**「两个字段取值恒相等」不蕴含
  「后者可由前者 event-local 重导」**;须先问那个相等是同 payload 的,还是沿链的、且谁在执法。

**`case_id` 不是纯投影**(纠正第六轮 F2 的分类):实测 955 个 case、多事件 case 873 个,
其 `frozen_node_id` **全同者 0/873**;`case_id` 后缀恰等于**首次 Freeze** 的 id(匹配数 955 = case 数)。
它是**跨事件的 lineage 身份**,对 Reattest 不是 event-local 重复,不可从当前事件重导。

**Supersede** — `input` 已收窄为五字段;`supporting_blob_oids` 曾是具名 `environment` 三 pin 的
第二次渲染,已退役。**Revoke** — 真源(断言「某节点本不该冻结」,树上无物可重导)。

## 三、生产者 / 消费者链

**断链不产生任何症状**,这是它最危险的性质。本轮两个实例:
- `Revoke` 字段族有 Engine 级生产(`AppendRevocation`)与候选校验器,但 **CLI 无动词**、
  增量准入直接抛 `does not support Revoke` ⟹ 生产者→准入链断。#2216 补 `ledger-revoke` 接通。
- #2216 退役 `node_path` 后,`FrozenCoverageLedger.cs:45` 仍 `RequiredString(payload,"node_path")`。
  **断链是活的**(dev 当时已有 6 条 v4 Freeze),但它不在三 required check 路径上,故零症状。#2245 接通。

**律(第Ⅵ节)**:删字段只有两条合法出路——补检测消费者,或删字段**并同步删掉声称它存在的规范文字**;
**不允许第三条**。我走了第三条一次,代价是一条活断链。

## 四、git 的天然固化能力:它保证什么,不保证什么

**保证**:blob 的字节由其 OID 决定,历史不可改而不改 OID。故「它还是不是当初那个值」
**在写入那一刻就已被回答**——任何重新推导都不增加信息,只增加成本。这是禁重放的全部根据。
本轮据此删掉两处重放:`show-atom` 重算 CAS 哈希后只拿去比对(返回的是原始字节);
writer preparation 重算全部 Closed 模块 material 后与已提交账本比对。
其原 fail-closed 性质现归 **git 对象完整性**——按条款,git 坏了不是本仓该防的。

**不保证**:git 不保证「写入时记录的字段与字节相符」——那是**写入门**的职责,不是读取时重算能补的。
git 也不保证可达性语义:`fetch-depth: 0` 把全部分支的对象拉进本地库,
**剥夺 remote 名字不删对象**,剥夺前记下的原始 OID 仍 `rev-parse` 成功。

## 五、账本的目的与两道门

账本存在的唯一理由:**把已验为真的命题冻住,使其强度不随时间退化**。
强度 = 公理闭包落在许可集内。它由**两道门**保证,不由存档保证:
- **写入门**:能 append 一条 `Freeze` ⟺ 当下这道门验过其闭包 ⊆ 许可集。故**能写入即当时没退化**。
  现状:1986 事件为证,每 PR 在跑。
- **升级门**:bump pin 后用**新**环境重算,每个冻结节点仍落在许可集内才放行。
  现状:**真实 Supersede/Revoke 事件仍为 0**——机制已实现且被测试钉住,但**未在真实升级上跑过**,
  这两件事不可混,不冒领。

**红线**:整个保证压在**许可集**上;若它能被悄悄放宽,「能写入」就不再蕴含「没退化」。
故许可集必须是唯一真源且被测试钉死其成员恰好为该集合。

**升级门曾有两个致命缺陷,均已修**:
① `statement_id` 是 **mathlib 决定的量**(哈希 elaborated kernel `Expr`,`.const` 逐字写入常量名与实例参数),
把它当「定理身份」是范畴错误——本仓 A14.1 实测 v4.31→v4.33 下 672/4262 声明漂移、211 模块受影响,
**而这些模块本仓一个字节未改**。改为 A∨B(#2186)。
② `pinsChanged` **恒真**:legacy Freeze 存 2 个 supporting OID、候选 `EnvironmentPinOids` 有 3 个,
基数不同必然不等 ⟹ 环境未变时也放行。改为按名比对(#2254)。
