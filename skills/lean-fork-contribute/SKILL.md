---
name: lean-fork-contribute
description: 在 trureturing 的 fork 中贡献 Lean、Blueprint Scribe、逃逸登记和冻结，无需下载整库项目 Lean cache。使用 linked worktree、定向冷构建和仓内验证器；适用于本仓库的开源贡献流程。
---

# Fork 内的轻量形式化贡献

本技能在完整的 trureturing fork 中工作。交付仍是原路径上的 D5 Lean、Blueprint Scribe、Reg 逃逸登记与 canonical 冻结状态。技能可单独安装；所调用的编译器和判官来自 fork 的钉版源码。

无需准备主检出的项目缓存、下载项目 Release cache 或编译全库。首次执行仍需 Lean 工具链、钉版 Mathlib 源码与依赖缓存、`global.json` 指定的 .NET SDK、Python ≥3.12、Git、Make 和冻结命令所需的 jq。现有依赖准备执行 `lake exe cache get`，不保证只下载所选模块的 Mathlib 缓存，也不保证零下载。项目模块只编译所选目标及其 import/utility 闭包。

## 准备 fork 和基线

读取 fork 的 `CLAUDE.md`、`agents/CONTEXT.md` 以及与内容相关的现役规范。数学准入、先库后证、bind-only 禁令、用途和独立评审规则照常适用；本技能仅改变本地准备与验证范围。

开发者先从自己的 fork 克隆源码，设置指向原仓库的 `upstream` remote；`origin` 保持指向自己的 fork。在已有克隆中复用兼容 linked worktree。所有构建和内容修改都在 linked worktree 中执行：

```sh
git fetch upstream dev
make worktree KIND=math NAME=my-contribution BASE=upstream/dev DEST=../trureturing-my-contribution
cd ../trureturing-my-contribution
CONTRIBUTION_BASE=$(git rev-parse upstream/dev)
export STRATALINT_ACCEPT_COLD_BUILD=1
export SCRIBE_DOTNET="$(python3 -c 'import pathlib,shutil; print(pathlib.Path(shutil.which("dotnet")).resolve())')"
```

`CONTRIBUTION_BASE` 是开始贡献时取得的受保护上游提交，后续命令一直使用它。需要同步时 merge 新的上游，并重新确定基线、重做受影响检查。不要把贡献分支自己的 `HEAD` 当成受保护基线来漏掉已提交的新定理；适配器只验证提交存在且为祖先，上游来源是调用方条件。不要为了缓存先运行 `make lean`、`warm-donor` 或项目缓存下载命令。冷构建入口仅在 linked worktree 中成立；fork 的主检出不走这条分支。

## 写内容与定向核验

先检索本仓、钉版 Mathlib 和可准入第三方库，复用已有结果。按现役路由生成数学源码与 Scribe，沿用仓库结构、Lake 配置、工具链和 pins。对应地址是：

```text
D5/<路径>.lean
Blueprint/D5/<路径>.scribe.cs
Blueprint/D5/<路径>.md           ← make emit 生成
Reg/D5/<路径>.lean              ← 新公开定理的四槽登记
Golden/Frozen/state/D5/<路径>.lean.json ← canonical writer 生成
```

内容已有理论卷时，先 ingest 并定位 atom；没有对应理论卷时可直接写 Lean 与 Scribe，不要求先补理论卷。

迭代只选择实际模块和实际保留的 Reg 源码，例如：

```sh
make lean-report-prepare LEAN_TARGETS="D5.My.Module Reg.D5.My.Module"
make lean-report-scoped LEAN_TARGETS="D5.My.Module Reg.D5.My.Module"
make emit BASE="$CONTRIBUTION_BASE"
```

所有命令继承 `STRATALINT_ACCEPT_COLD_BUILD=1` 和绝对路径 `SCRIBE_DOTNET`，后者是 Scribe SDK 执行的宿主；仅有 `dotnet` 在 PATH 上不足以满足 SDK admission。目标必须非空，使用实际 dotted module names。定向报告包含显式 utility 输入与 imports；它不等于全库健康证明。源码未变时复用已有成功读数。长命令使用宿主作业句柄并等待真实退出码。

## 本地 Scribe 和逃逸审计

从技能所在目录调用适配器；可安装到任意目录，无需安装其他个人技能：

```sh
python3 <skill-directory>/scripts/check.py \
  --repository "$PWD" --base "$CONTRIBUTION_BASE" \
  --module D5.My.Module
```

适配器自动纳入相对基线变动的全部 D5/Reg 源码及存在的 Reg mirror，运行 `make emit`，再对选定的目标运行 `make lean-report-prepare` 和 `make lean-report-scoped`。随后直接使用 fork 自身的 scoped report reader、Scribe 内容/公式检查器、四槽证据验证器和冻结状态解析器。临时 host 只提供调用入口，不修改仓内工具；它不执行全局 projection reconciliation，也不是 required checks 的替代品。诊断中的 `FORK_AUDIT` 是本地读数，不是新的持久化状态。

每个新增、源码手写、公开 D5 theorem/lemma 都须尝试忠实的四槽登记。适配器用受保护基线中的源码名排除历史定理，排除 private 和编译器生成声明；utility 指定的 refutation result 只有通过现役 typed utility 校验才能豁免。按源码 owner 的 `Reg/D5/…` mirror 与其 imports 解析证据，不接受 D5 自登记。变动 Reg 的 payload 也交原验证器检查。辅助声明不递归产生 D5 目标。

登记须具有 `declared_validated`、四槽与当前 binding evidence。`.unknown` continuation 只表示残余未知。若无法登记，保留已成功内容，为原定理、具体缺口和失败读数新建或复用 issue，并在交付中披露未完成审计；本地检查仍报非零，不能称审计通过。不得改判官、强塞错误模板、弱化命题或删除成功证据。最终从 pushed head 的 required CI 读取 `DTR-*` 结果。

适配器拒绝所选报告中的 `sorryAx`、直接 axiom、非标准 axiom 闭包和与当前冻结 pin 不符的声明。它不证明内容新意、忠实性或非空洞性，这些仍由数学评审承担。

## 冻结与提交

通过现役准入与冻结前评审后，复用仓内 writer；不要手写状态片或建立第二份冻结账本：

```sh
make deposit BASE="$CONTRIBUTION_BASE" GID=D5/My/Module.theorem_name
```

主仓 writer 按 GID 核验目标模块、生成 Scribe 并写入冻结状态。GID 使用 slash 路径与声明 selector，Lean targets 使用 dotted module name。检查源码、生成 Markdown 和状态片的 diff。若有对应 atom，等声明合入主仓 `dev` 后，在[理论源仓](https://github.com/the-omega-institute/trureturing-source-theories/tree/dev)的检出目录运行 `make cover ATOM_ID="$atom" GID="$gid"`。复用已冻结声明时可直接在理论源仓执行这一步。

用 `git push origin HEAD` 提交到开发者自己的 fork，并向原仓库的 `dev` 提 PR，避免工作分支跟踪 `upstream/dev` 时默认推错 remote。PR 写清数学交付、冻结/覆盖变化、定向验证范围和未完成审计 issue。先看 `make gate-plan BASE="$CONTRIBUTION_BASE"`；不要为本地验证启动全库 gate/build。required CI 由维护端承担完整准入范围。等待准确 head 的 required checks、MERGED 和合并后的首次 dev push 核验后才能称交付完成。发布、合并与消息发送仍受用户授权范围约束。
