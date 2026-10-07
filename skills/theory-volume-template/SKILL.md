---
name: theory-volume-template
description: 新建或追加 docs/develop/theory/ 下的理论卷时使用:给出 GitHub 可渲染的数学写法、符合 generic-v1 消化系统且不改判既有 atom 的卷骨架与追加骨架。
---

# 理论卷模板(消化可用 + 只能追加)

## 用途与不用途

**用**:要在 `docs/develop/theory/` 新建一卷,或给既有卷追加一批内容,而这批内容必须
①被 canonical 消化器正确切分成 atom,②不改判任何既有 atom。

**不用**:消化**外部作者**已写好的卷(那是 `skills/codex-theory-ingest/SKILL.md`);
把 atom 形式化成 Lean(那是 `skills/codex-formalize/SKILL.md`)。形式化不以理论卷为前置:
无 atom 的内容直接写 D5 Lean 与 Blueprint Scribe,经 `make deposit-uncovered` 冻结(`CLAUDE.md` 第 1.2 条)。

**本文件没有独立权威。** `docs/develop/spec/golden-ledger-repo-spec.md` 是唯一规范,
`CLAUDE.md` 是不动标架,活的 harness 输出是关于当前树的事实裁判。三者与本文件冲突时,本文件是 bug。

## 三个文件

| 文件 | 用法 |
| --- | --- |
| `TEMPLATE.md` | 新卷骨架。复制成 `docs/develop/theory/<VOLUME>.md`,换掉 `<占位符>`,**不要删文末的追加锚**。 |
| `APPEND.md` | 追加批次骨架与三条硬纪律。每批增补照它写。 |
| `SKILL.md`(本文件) | 消化器的内容身份、范围摄入、落地流程与判据。 |

## GitHub 公式

理论卷在 GitHub Markdown 中阅读。按 GitHub 官方的[数学表达式文档](https://docs.github.com/en/get-started/writing-on-github/working-with-advanced-formatting/writing-mathematical-expressions)使用其 MathJax 入口；LaTeX 公式内容合法，不代表外层 Markdown 分隔符也受支持。

- **行内默认用 `$...$`**，例如 `$q(s)=\bar q(\eta(s))$`。中文正文在公式外侧留空格，例如 `读数 $q(s)$ 决定结果`；需要紧邻中文或避开 Markdown 干扰时，用下面示例中的美元号加反引号形式。
- 含 `*` 的行内公式优先使用美元号加反引号形式，避免同段多个伴随符号（如 `A^*`、`F^*`）先被 Markdown 配成强调，连带破坏其间的公式。
- **块级默认用 `$$`**，起止分隔符各占一行，公式块前后留空行。GitHub 也支持 `math` 围栏；使用它时，围栏内不再套 `$$`。
- **不要以 `\(...\)` 或 `\[...\]` 作为 Markdown 的公式分隔符**；它们不会触发 GitHub 的数学渲染。普通代码围栏、`latex` 围栏和单独的反引号也不能替代数学入口。这不限制公式内部的 LaTeX 命令。
- 多行推导在一个数学块内使用 `aligned` 等环境；不要把 `=` 或 `---` 单独放一行，以免仓内 Markdown 消化器识别为 setext 标题。
- 公式内的字面美元号写 `\$`；同一行公式之外的字面美元号按官方示例写 `<span>$</span>`，避免与公式边界混淆。

````markdown
行内： $q(s)=\bar q(\eta(s))$。
避免 Markdown 干扰的行内写法：$`A_n^*A_n`$。

$$
\begin{aligned}
L(s,uv) &= L(s,u)+L(T_u(s),v),\\
L(s,\varepsilon) &= 0.
\end{aligned}
$$

```math
q = \bar q \circ \eta
```
````

以上兼容写法仅作为写作提示，理论推导与实质内容优先。除非用户明确要求，不做 GitHub 公式兼容检测，不调用预览或 Markdown API，不逐式统计或为排版另设验收步骤。按这些提示编写新增正文和未合并草稿即可；已合入卷仍遵守追加纪律，不为统一排版重写旧字节。

## 一、消化系统对卷的机器要求

真源是代码,不是本节;本节只是它的读法。出处按符号名给,不给行号(行号会漂移)。

**1. 谁会被消化。** `DigestionOpaquePathPolicy.IsTheoryDocument`:凡路径以 `docs/develop/theory/`
开头者即理论卷,**由路径规则判定,不由任何名单枚举**。⟹ 放进那个目录的 `.md` 一定会被消化;
不想被消化的文件(模板、说明、草稿)**不能**放在那里。

**2. 用哪个消化器。** `Meta/Digestion/backfill/<source_id>/source.toml` 的 `atomizer` 字段。
新卷一律用 `generic-v1`(`genre_registry_check = "no-registry"`):它是**规则**不是词表,
不需要往 `Meta/Digestion/atomizers.toml` 登记任何体裁词,也就不会连带改判别的卷。
`source.toml` 由 `make ingest SOURCE=<卷路径>` 首次运行时自动写出,不必手写。

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

`make ingest SOURCE=<source-id 或源文件路径>` 只处理指定理论。
写集由 `IngestCommand.RequireAppendOnlyWriteSet` 限定为新增文件；既有记录
及其字节保持原样。这个约束不证明理论正文只追加：正文的追加纪律须由
该卷的 Git diff 核对。

## 三、内容身份与复用

ATOM 的身份是完整 raw 文本的 SHA-256。同一文本在另一理论已经登记时，
摄入复用既有 ATOM，不重复创建；新文本生成新 ATOM。标题、定理号与段落
位置只用于定位正文，不构成 ATOM 身份。摄入不重写既有条目。

## 四、落地流程

在会话工作树写卷或追加块，核对该卷的 diff，再运行指定范围的摄入：

```sh
make ingest SOURCE=<source-id-or-volume-path>
make search-atoms SOURCE=<source-id> TEXT=<new-claim-keyword>
make show-atom SOURCE=<source-id> ATOM_ID=<matched-atom-id>
```

摄入须退出 0，且 `coarse_fallbacks=0`。核对新增命题的 ATOM 文本与正文一致，
确认生成写集没有改动既有 ATOM，再把正文和摄入结果一同提交。搜索只查找
指定范围的存储记录，不认证全账本一致性。无需为了精确计数或账本摘要读取
该卷所有旧记录。

通过普通 PR 与全部 required checks 交付；本地成功不替代远端准入。
理论卷是 content 面，可与必要的判官面改动在同一完整 PR 交付。

## 五、反面即病

1. 见到自己**回去改**卷里既有的一句话——哪怕只是改错别字。正解是新章勘误,旧字节不动。
2. 见到自己把导航、目录、修订记录写在**卷首**并每批更新它——那是每批都改既有 atom。
   导航按批写在各批开头;卷首只放恒定的读法说明。
3. 见到自己删掉文末的追加锚,或把新内容写在锚**之前**。
4. 见到新章标题与既有标题同名(「证明」「结论」「小结」)——加上所属章号消歧。
5. 见到自己把待证命题只写成定义——应明确其假设与结论。
6. 见到自己在卷里写「已由 Lean 验证」「已冻结」——账上没有的不冒领,状态以冻结账本为准。
