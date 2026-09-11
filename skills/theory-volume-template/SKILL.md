---
name: theory-volume-template
description: 新建或追加 docs/develop/theory/ 下的理论卷时使用:给出符合 generic-v1 消化系统、且既有 atom 一个都不被改判的卷骨架、追加骨架与落地判据。
---

# 理论卷模板(消化可用 + 只能追加)

## 用途与不用途

**用**:要在 `docs/develop/theory/` 新建一卷,或给既有卷追加一批内容,而这批内容必须
①被 canonical 消化器正确切分成 atom,②不改判任何既有 atom。

**不用**:消化**外部作者**已写好的卷(那是 `skills/codex-theory-ingest/SKILL.md`);
把 atom 形式化成 Lean(那是 `skills/codex-formalize/SKILL.md`)。

**本文件没有独立权威。** `docs/develop/spec/golden-ledger-repo-spec.md` 是唯一规范,
`CLAUDE.md` 是不动标架,活的 harness 输出是关于当前树的事实裁判。三者与本文件冲突时,本文件是 bug。

## 三个文件

| 文件 | 用法 |
| --- | --- |
| `TEMPLATE.md` | 新卷骨架。复制成 `docs/develop/theory/<VOLUME>.md`,换掉 `<占位符>`,**不要删文末的追加锚**。 |
| `APPEND.md` | 追加批次骨架与三条硬纪律。每批增补照它写。 |
| `SKILL.md`(本文件) | 消化器的机器规则、地址碰撞预检、落地流程与判据。 |

## 一、消化系统对卷的机器要求

真源是代码,不是本节;本节只是它的读法。出处按符号名给,不给行号(行号会漂移)。

**1. 谁会被消化。** `DigestionOpaquePathPolicy.IsTheoryDocument`:凡路径以 `docs/develop/theory/`
开头者即理论卷,**由路径规则判定,不由任何名单枚举**。⟹ 放进那个目录的 `.md` 一定会被消化;
不想被消化的文件(模板、说明、草稿)**不能**放在那里。

**2. 用哪个消化器。** `Meta/Digestion/backfill/<source_id>/source.toml` 的 `atomizer` 字段。
新卷一律用 `generic-v1`(`genre_registry_check = "no-registry"`):它是**规则**不是词表,
不需要往 `Meta/Digestion/atomizers.toml` 登记任何体裁词,也就不会连带改判别的卷。
`source.toml` 由 `make ingest` 首次运行时自动写出,不必手写。

**3. 地址(locator)有四路,全部只看字节。**(`GenericAtomizer` + `MarkdownAstAtomizer`)

| 路 | 触发形状 | 得到的地址 |
| --- | --- | --- |
| 标题 | 任一 heading,其文本以「词+数字」开头 | `<词>/<数字>` |
| 标题 | 其余 heading | `section/<标题文本的 slug>` |
| 段落 | 段落首行形如 `**词 数字…` | `<词>/<数字>` |
| 段落 | 段落首行形如 `**数字.数字…` | `item/<数字>` |
| 表格 | 非表头且首格非空的表格行 | `row/<首格文本的 slug>` |

slug:NFC 归一后把「非字母非数字」的连续段换成 `-`,首尾去 `-`,超过 48 runes 换成短哈希。
「词」必须是纯字母数字(无短横、无下划线),数字形如 `7` 或 `7.2` 或 `7.2a`。
**heading 包含 setext 形**:`$$` 块里单独一行的 `=`/`---` 会被 markdig 判成 setext 标题——
这在数学卷里是常态,不是罕见事故。

**4. 只有五个中文体裁词是可形式化候选。**(`DigestionContentDisposition.FormalizableKinds`)

```
定理  命题  引理  推论  候签定理
theorem  proposition  lemma  corollary  theorem-form
```

写成 `**定理 7.2（…）。**` 的段落 ⟹ 地址 `定理/7.2` ⟹ 计入形式化候选,将来可被 `make cover` 覆盖。
写成 `**定义 7.1（…）。**` ⟹ 地址 `unregistered:定义/7.1` ⟹ 合法、入账、但**不计入可形式化分母**。
这不是缺陷:定义、约定、注记本就不是待证命题。**要它被证,就用上面五个词之一;不打算证,就别用。**
(本条依据是源码里的那张表;`make digestion-readiness` 的运行时分类读数要先跑 `make lean-report`,
本次**未取**,标 `ASSUMED-UNVERIFIED`。)

**5. atom 的边界。** 一个 claim 从它的 lead 起,延伸到**下一个边界**为止:claim 到下一个 claim
或下一个同级/更高级 heading 的起点;非 claim 的 section 到**任何**后续边界的起点。
⟹ 一条定理的 atom 字节 = 陈述 +(若紧跟)证明。
**只剩标题行、正文为空的 heading 不产生 atom**(`dropEmptyHeadingClaims`)——追加锚正是靠这一条工作。

**6. 子句分解(clause chain)。**(`DigestionDecomposition.PlanClauses`)一个 atom 内部,
**除第一行外**任何以 `**` 开头的行都是子句边界;没有粗体行时,`- `/`* ` 列表项 ≥2 个也是。
⟹ 「定理 + `**证明。**`」天然分解成父 + 2 子,子地址 `<父地址>/clause/N`。这是既有机制,不是错误——
既有卷普遍带 chain。**代码块内的行同样计数**:代码块里不要有以 `**` 开头的行。

**7. atom id 全库唯一归属一个卷:两卷之间不要逐字复制段落。**
atom 的身份是它字节的 sha256,与卷无关;`RequireUnclaimedAtomIds` 拒绝把同一个 atom id
登记给第二个 source。**实测(2026-09-10)**:两个内容逐字相同、只有末尾锚不同的探针卷同批消化,
先被处理的那卷拿到 9 条条目,另一卷拿到 **0 条**——它的每一段都被判成「已被别人登记」。
把同一段话原样搬进另一卷,那一段在新卷里就不会有账。要复述就改写,或直接引用对方的编号。

**8. `〔closed〕` 是机器读的状态命名空间,不要用。**(`DigestionAtomStatusMarker.Parse`)
紧跟粗体标题的 `〔closed…〕` 会被解析为状态标记。用它宣告「已闭合」就是手写状态、冒领账目
(CLAUDE.md 第 2.4 条)。其它 `〔…〕` 注解不受影响。

## 二、「只能追加」为什么成立

atom 的身份是**它自己那段字节的 sha256**。所以:

- **改既有的一个字 ⟹ 那条 atom 的指纹变 ⟹ 消化器读成「旧 atom 消失、新 atom 出现」**,
  账上是一次删除;而卷与 atom 不删是建设者纪律(CLAUDE.md 第 1.2 条)。
- **纯尾部追加也可能改到既有字节**:文件里最后一个 atom 的终点是「下一个边界或文件末尾」,
  直接往文件尾追加,会把新增的空行并进那条 atom。

**追加锚解决的就是这一条。** 卷末恒有一行

```
## 追加锚（本行以下为增补区）
```

它自己因「只剩标题行」而不产生 atom,却**是一个边界**:它之前那条 atom 的终点被永久钉在锚的起点上。
于是锚之后追加任何东西——包括前面留多少空行——都不动锚之前的一个字节。
条件只有一个:**追加块的第一个 block 必须是 heading**,否则锚会长出正文、变成一条 atom,
下一批再追加时它就会变。故每批以新的追加锚结尾,首行写 `## <编号>. <标题>`。

**判据不是这段推理,是读数。** 2026-09-10 在 `origin/dev a9b9e97399` 的 lane 上实测,
两卷除末尾锚外逐字同构,追加逐字同构的一块:

| 采集条件 | 无锚卷 | 有锚卷 |
| --- | --- | --- |
| 卷以**段落 claim** 结尾 | 基线 3 atom → 追加后 4,**其中 1 条基线 atom 被改判** | 基线 3 → 4,**零改判** |
| 卷以**表格行**结尾 | 基线 9 → 15,零改判 | 基线 9 → 15,零改判 |

第二行不是反例,是边界:表格行 atom 的终点是行尾而不是文件末尾(`Extend: false`),
那种卷的末条 atom 本来就碰不到追加。**但作者无法保证卷末永远是表格行**,
所以锚是那条不依赖卷末形态的写法。第一行才是有区分力的一侧,它证明:
没有锚,一次纯尾部追加就足以改判末条 atom。

**取这条读数的命令**(追加前后各跑一次,`sid` 是本卷的 source_id):

```bash
find Meta/Digestion/backfill/$sid -name '*.yaml' -exec basename {} .yaml \; | sort > after.txt
comm -23 before.txt after.txt      # 必须为空:基线 atom 一条都没消失
```

**这道纪律有多少是机器守的,如实分栏。** `make ingest` 的写集由
`IngestCommand.RequireAppendOnlyWriteSet` **硬性**限定为「只新增文件」:它既不会删账目条目,
也不会覆盖已有条目——想删想改,当场抛错。但这守的是**账本**,不是**卷**:
你在卷里改掉一段字节,ingest 不会报错,它只是给新指纹**再开一条**新条目,
而指向旧字节的那条**留在账上,从此对不上卷里的任何一段**。仓内当前**没有**判官去比对
「账目条目 ⊆ 卷的当前 atom」(`DigestionCasStore` 的 `orphan CAS blob` 查的是反方向:
没有条目引用的 blob)。⟹ **改判既有 atom 不会变红,只会静静多一条死账**;
本条纪律主要靠上面那条 `comm -23` 读数与评审守,不靠门。

**模板本身的消化读数(2026-09-10 实测)。** 把 `TEMPLATE.md` 的占位符填成一个最小实例
(六章、两条定理级命题、一张表、一个代码块、末尾一个锚)后跑 `make ingest`:
`residual_open_added=25 skipped_existing=0 coarse_fallbacks=0 open_genres=0 cas_objects_written=25`,
EXIT=0,一次通过。逐条查这 25 个 atom 的首行,**含「追加锚」的 atom 数为 0**——锚确实只当边界、不占账。
同一次读数还实证了上面第 7 条:实例里两处证明正文被我填成了同一句话,结果它们**只产出一个 atom**。

## 三、地址碰撞:唯一会咬人的那一类

同名标题、同文本表格首格会产生重复地址。重复本身**不必然出错**(既有卷里 `section/证明` 重复二十几次仍通过),
真正会红的是**既有的单例被撞成重复**:那会让十万行之前、字节一个未动的 atom 换地址,
ingest 判 `INGEST_TRUTH_ALIGNMENT_REQUIRED planned rewrite of existing entry <id>` 或
`INGEST_INVALID … malformed clause chain`。

**三分栏判据**(按 `(dev 侧出现次数, 新版出现次数)`):

| 分栏 | 条件 | 后果 |
| --- | --- | --- |
| **危险** | `dev=1 → new≥2` | 既有单例被撞,既有 atom 改址 ⟹ 红 |
| 良性 | `dev=0 → new≥2` | 两侧皆新,互撞不碰既有 |
| 良性 | `dev=N≥2 → new>N` | 既有已重复,新增排在其后;**纯尾部追加天然落此栏** |

**模板的编号律直接消灭危险栏**:章号只增、定理号写作 `<章号>.<序号>`,新标题的 slug 必含新章号,
不可能与既有标题同名。⟹ 按模板写,预检通常是形式;不按模板写(比如新章又叫「证明」「结论」),
就必须逐条预检。

**预检脚本不要入仓**:它复刻的是 `GenericAtomizer` + markdig 的语义,入仓即第二真源,
且必随消化器漂移而失真。写在 scratchpad,用完即弃。**权威判词始终是 `make ingest` 本身**
——失败的 ingest 零写入,探路安全。

## 四、落地流程

```
1  make worktree KIND=theory NAME=<lane> BASE=origin/dev
2  写卷/写追加块(照 TEMPLATE.md / APPEND.md;编号只增,不动既有字节)
3  git commit 文档 → push(推与本地验证并行,别串行等)
4  make ingest BASE=origin/dev > log 2>&1; echo "EXIT=$?"    # 不需要 lean-report
5  grep -E '^INGEST |EXIT=' log —— 判据见下
6  git commit 账目(Meta/Digestion/**) → push
7  git merge origin/dev → 重跑 ingest → 四零齐 ∧ 工作树零改动
8  make pr-open HEAD=<branch> MESSAGE=<file> [AUTO_MERGE=1]   # 自带同步等待,别在外面套轮询
9  合入后同步主检出、git worktree remove、删分支
```

**判据(第 5 步)**,三项合取:
①`EXIT=0` ∧ `coarse_fallbacks=0`;
②`skipped_existing` 等于本卷追加前的账目条目数——**每一条既有 atom 都仍是当前 atom**;
③上面那条 `comm -23` 为空。`make ingest` 的实际输出行形如
`INGEST residual_open_added=9 skipped_existing=0 coarse_fallbacks=0 open_genres=0 cas_objects_written=9 ledger_changed=true`。
**第 7 步的四零**(`residual_open_added=0`、`cas_objects_written=0`、`ledger_changed=false`、
工作树零改动)是合并前真能取到的闭合判据,别省。

**理论卷是 content 面。** 同一个 PR 里不得夹带 `tools/**`、`.github/**`、`skills/**` 一类判官面改动
(分区门 SL-029 机器强制)。

**别用管道判绿**:`make ingest | tail` 会吞掉真退出码,zsh 里 `${PIPESTATUS[0]}` 恒空。
落文件、读哨兵。

## 五、三种追平税判词(都不要照它说的跑 align)

```
INGEST_TRUTH_ALIGNMENT_REQUIRED existing entry <id> removed; run make align-digestion-status
INGEST_TRUTH_ALIGNMENT_REQUIRED Lean report input closure changed; ...
INGEST_TRUTH_ALIGNMENT_REQUIRED existing entry <id> changed status-authority inputs; ...
```

**统一判据:判词点名的条目若不属于本卷的 `source_id`,那就是追平税**——别人刚合入的账目条目,
`git merge origin/dev` 后重跑即通过。`align → ingest` 是失败不动点,越跑越远。
查 dev 改了什么用 `git diff --name-only $(git merge-base HEAD origin/dev)..origin/dev`,
**不能**用 `HEAD..origin/dev`(那会把自己的追加反算成别人的改动)。

## 六、反面即病

1. 见到自己**回去改**卷里既有的一句话——哪怕只是改错别字。正解是新章勘误,旧字节不动。
2. 见到自己把导航、目录、修订记录写在**卷首**并每批更新它——那是每批都改既有 atom。
   导航按批写在各批开头;卷首只放恒定的读法说明。
3. 见到自己删掉文末的追加锚,或把新内容写在锚**之前**。
4. 见到新章标题与既有标题同名(「证明」「结论」「小结」)——加上所属章号消歧。
5. 见到自己用 `**定义 3.1**` 写一条**打算被形式化**的命题——它不会进候选分母,永远等不到人来证。
6. 见到 `comm -23` 非空(基线 atom 消失了几条)而去重跑、去跑 align——那是在掩盖一次真实的改判。
7. 见到自己在卷里写「已由 Lean 验证」「已冻结」——账上没有的不冒领,状态以冻结账本为准。
