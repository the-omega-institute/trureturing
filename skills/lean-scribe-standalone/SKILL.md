---
name: lean-scribe-standalone
description: 在新的独立 Git 仓库中编写 Lean 与 Blueprint Scribe，使用钉版源码完成定向编译、四槽逃逸审计与冻结，无须 trureturing 的共享 Lean cache。适用于独立开源形式化项目。
---

# Lean、Scribe 与独立冷构建

## 范围

交付数学 Lean、对应的 `.scribe.cs`、实际编译的 Reg 证据及程序生成的冻结状态。作者无需建立理论卷、消化账本、共享缓存、工作树池、发布服务或全库构建。已有 trureturing 检出仍遵守其原有入口；本技能不在那个检出中绕过缓存守门。

独立项目复用上游原始 Scribe、Lean inspector、契约和冻结 writer，不另造审计语义。`scripts/standalone.py` 导出源码和实际 Lean import 闭包；只把宿主的缓存运输入口换成普通 Lake 调用。新仓库从空 `.lake` 编译，工具链发行包自带的 Lean 标准库仍是必需依赖。Mathlib 若在 import 闭包中则从源码构建；冷构建不是零编译成本。不得把内核通过、登记证据存在或源码哈希称为四槽审计通过。

## 初始化

需要 Git、Python ≥3.12、Elan/Lake、钉版 .NET SDK，以及首次下载钉版依赖所需的网络。支持 macOS/Linux；不要求 gh、Nyx、账户、令牌或远程写权限。

入口自带不可变的上游提交钉版；省略 `--source` 时，以 Git 的浅取回和 sparse checkout 获取所需源码。已有源码检出时，可加 `--source "$SOURCE"`，并用 `--revision "$UPSTREAM_COMMIT"` 显式选择其完整提交哈希。初始化后运行不再依赖该检出；不得复制其 `.lake`、`bin`、`obj`、报告或缓存标记。保留许可证与实际来源。源码来源是构建依赖，不是项目的真值数据。

```sh
python3 /absolute/path/to/lean-scribe-standalone/scripts/standalone.py init \
  --dest "$PROJECT"
cd "$PROJECT"
python3 formalize.py doctor
```

目标目录必须不存在或为空。初始化产生可单独搬移的 Git 仓库，保留原来的 D5、Blueprint 和 Reg 地址规则。`standalone-source.json` 记录源码来源与受保护的工具、支撑数学和包配置；它不是审计报告。需要复用已有模块时，初始化加可重复的 `--include <dotted.module>`，导出其完整仓内 import 闭包和可用 Scribe/文献来源；不要复制整个 D5。

## 编写与核验

1. 先固定量词、假设、用途和结论，查本项目、钉版 Mathlib 和可准入第三方库。直接调用已有结果。逐声明判断 content/bind-only；只有被实际消费的辅助包装才保留，不能用包装冒充新增数学内容。
2. 数学写在 `D5/<path>.lean`，叙述写在 `Blueprint/D5/<path>.scribe.cs`。参考导出工具中的现行 DSL 和实际使用的邻近源码；Scribe 使用 `Describe.Lean` 精确引用声明，默认用 `StatementSource.FromAuthor` 与类型化公式。写清定义、参数对应、每个合取项、条件和未证桥梁。渲染产物由工具生成。
3. 新公开 theorem/lemma 的证据写在 `Reg/D5/<path>.lean`；数学包不导入 Reg 或判官。使用 `Contract.Registration` 与真正的 `TemplateEnrollment`，交付完整 realization、readout、escapeFrom、continuation 和相关桥梁、variation、sensitivity。无限/依赖族保留原完整 telescope，不能用有限样本代替。`.unknown` continuation 只记录未知残余。
4. 从任意工作目录调用实际的模块名，根列表不得为空：

```sh
python3 "$PROJECT/formalize.py" check --project "$PROJECT" \
  --module D5.S0.Observation.MyResult \
  --module Reg.D5.S0.Observation.MyResult
```

入口只编译所选模块及其依赖，生成并验证 scoped report，用原 Scribe 渲染器生成 Blueprint。检查内核、公理闭包、源绑定和旧冻结源码保护。读取实际报告中每个目标公开定理的登记判词；`declared_validated` 必须来自当前源码的完整编译与绑定证据。完整运行日志仅是本地构建输出，不提交回执副本。

审计失败、缺失或模板不适用时，保留数学结果并在对应成果中如实说明具体缺口；不要硬套模板、削弱目标或更改判官。独立仓库可以继续数学开发，但不得称审计完成。冻结命令要求所选目标定理的审计全部完成；它不使用上游仓库的未完成审计 issue 例外。

## 冻结与交付

```sh
python3 "$PROJECT/formalize.py" freeze --project "$PROJECT" \
  --module D5.S0.Observation.MyResult \
  --module Reg.D5.S0.Observation.MyResult
```

冻结先重用当前检查入口，再调用原 `ledger-align` writer；不手写 `Golden/Frozen/state`。生成的源闭包保护比声明冻结更严格：本路径只追加模块，不编辑已冻结源码或其依赖；需要修改时另做显式迁移，不自动重新钉住旧真值。`check` 核对已记录的冻结源闭包，删除或改动都失败。

提交源码、Scribe、Reg 证据、许可证、依赖钉版与程序维护的冻结数据；忽略 `.lake`、构建日志和缓存。用普通 Git 提交与项目自己的 CI 交付。发布、推送和创建远程项目按用户授权执行，不以采用本技能为授权。

## 验收边界

新路径的验收要在新的目录中从空 `.lake` 执行完整检查、Scribe、真实四槽绑定和冻结；随后改动冻结源码、引入 `sorry`、删除目标登记，分别确认失败。再从不同 cwd、含空格路径和不加载个人 shell 配置的环境调用入口。只报告实际完成的条件和平台；不能将只检查初始化或 Python 语法称为冷构建成功。
