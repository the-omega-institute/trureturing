# 官方 Init 的独立内核移植

从仓库根目录运行，使用 `lean-toolchain` 指定的 Lean。以下命令编译严格基础，然后生成一个可直接导入的模块目录。生成目录须尚未存在。

```sh
python3 src/OmegaChecks/strict_lake.py build +OmegaInit
python3 src/OmegaChecks/InitPort/build.py .lake/init-port Init.Prelude
LEAN_PATH=.lake/init-port/lib lean Example.lean
```

`Example.lean` 可以直接使用新生成的积类型与投影。

```lean
prelude
import OmegaInit.Prelude
open Omega

example (a : α) (b : β) : Omega.Eq (Prod.fst (Prod.mk a b)) a := Omega.rfl
```

生成的 `OmegaInit.Prelude` 提供 `Omega.Quot`、`Omega.Quot.mk`、`Omega.Quot.ind` 和 `Omega.Quot.lift`。普通导入支持两个消去子的构造子归约。Lean 内核按固定的根名称识别商类型和等式，在打开 `Omega` 命名空间的外部代码中可用 `Omega.Eq` 指定移植的等式。

普通 Lean 文件可直接写 `import OmegaInit.Prelude`，使用 `LEAN_PATH=.lake/init-port/hosted lean Example.lean`。`hosted/` 复用相同的官方根声明，保留 `Omega.Nat.div`、`Omega.Nat.mod` 和 `Omega.Nat.gcd` 自身的计算定义。原生调用使用逐一核验的全输入等式证书。生成器在宿主内核中重新检查传递依赖和各模块中的重复证明。`lib/` 是带 `prelude` 的独立内核入口，零公理审计和空环境重放读取此目录。`--isolated-only` 可单独生成该入口。仓库种子构建也提供普通导入入口 `python3 src/OmegaChecks/strict_lake.py env lean Example.lean`。

位置参数接受一个或多个官方模块名。省略这些参数会扫描钉版工具链的所有 `Init` 模块，包括需要单独导入的模块。构建整个库可运行 `python3 src/OmegaChecks/InitPort/build.py .lake/init-port-all`。加上 `--seed PATH` 可选择另一个已编译的严格种子，默认读取 `.lake/build/omega-strict/lib/lean`。工具把种子的编译文件复制到独立临时目录，随后从钉版官方模块逐个翻译依赖、证明项、定义、归纳族和递归器。每个候选声明都在 Lean 内核中检查。环境变量 `OMEGA_PORT_HEARTBEATS` 为每个候选声明指定原始心跳预算，默认 5000。

`inventory.jsonl` 按顺序记下官方模块名、声明名、公开标记、移植结果和直接阻塞依赖。`added` 包含内核生成的构造子、递归器、私有及编译器内部声明。`existing` 表示复用种子中的声明。`interface-rejections.jsonl` 保存无法通过仓库官方对应检查的候选。公理、商原语、unsafe 或 partial 声明、未支持的表达式和依赖缺失均有逐项记录。

`lib/` 保存按官方定义模块组织的编译文件。程序对所选的基础库模块运行仓库的 `omegaAudit --exact-roots`，检查模块闭包、公开归属和可计算对应，逐声明检查公理并从空环境重放内核。全量构建还将 OmegaMath 和 OmegaMathlib 的下游源码编译到同一 `lib/`，验证普通 `import OmegaMath`，并审计其实际导入闭包。成功后输出目录才会出现。两次审计的读数分别保存在 `audit.txt` 和 `omegamath-audit.txt`。全量缺口表位于同一目录的 `init-gaps.tsv`。

这个独立制品用于内核类型检查、证明和定义归约。生成器复制已移植结构的字段顺序、父结构和投影信息，并登记已有的类型类实例。普通导入支持用 `{ fst := a, snd := b }` 构造积、用 `{ p with snd := b }` 更新字段。声明覆盖率按内核接口计数。原生可执行代码、语法扩展和完整实例搜索行为仍待核验。

当模块闭包包含 `Init.Core` 时，生成器为 `Omega.Task.spawn`、`map`、`bind` 及任务优先级提供 `native/task.o`。严格的自然数优先级按钉版调度器参数转换。同步与异步映射保留任务依赖。使用 `IO.getTaskState`、`hasFinished`、`wait`、`waitAny`、`waitAny'`、`cancel` 或 `checkCanceled` 的严格消费者可链接 `native/task_io.o`。该对象还提供 `BaseIO.asTask`、`mapTask`、`bindTask`、`chainTask` 与 `mapTasks`。原生调度器即使在最后一个用户句柄释放后也会执行已提交的效应。相同的五个调度操作也支持 `EIO` 和 `IO`，任务可返回成功值或原有的异常。

`OmegaInit.Dynamic` 中的 `Dynamic.mk` 把类型名与值交给钉版运行时，`Dynamic.typeName` 取回名称，`Dynamic.get?` 在名称相等时返回原值。名称跨越严格库与原生库时转换其字符串表示。内核中的载体通过一个私有的有点类型取得，公开读写接口保持不透明。为类型登记名称的 `TypeName.mk` 和三个运行时私有实现保留官方 `unsafe` 标记。[接口及重放](DynamicValue.lean) · [钉版源码](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Dynamic.lean)

若选定模块闭包包含 `Init.System.Promise`，生成器为已移植的 `Omega.IO.Promise.new`、`resolve`、`isResolved`、`result?` 和 `resultD` 生成原生入口。将消费者编译成 C 后，用 `leanc` 链接输出目录中的 `native/promise.o` 与 `native/promise-result-d.o`。后者的回调由钉版官方 Lean 定义编译。普通消费者可在兑现前取得结果任务。兑现后，字段投影、模式匹配和内核原始投影都读取第一次兑现的值。释放最后一个未兑现句柄后，`result?` 返回 `none`，`resultD` 返回传入的默认值。

`IO.Promise.rec`、`recOn` 和 `casesOn` 的分支参数依赖私有的 `IO.PromisePointed`。钉版官方与严格后端均须用 `import all` 才能在定义中调用这三个消去子。盘点程序在两侧分别检查普通导入的内核诊断、`import all` 下的完整官方类型和实际调用。通过的条目在清单与缺口表中标记为 `importAllOriginalTypeChecked`。普通导入的覆盖数使用 `originalTypesChecked`，与官方同样要求 `import all` 的完整类型另计入 `importAllOriginalTypesChecked`。完整性验收逐项核对两类实现，并在最终验收时用待验制品重新运行这三个消去子的消费者。[消费者与内核核对](PromiseAccess.lean)

`native/path_io.o` 支持读取环境变量和当前程序路径、获取与切换进程目录、规范化路径、创建和删除目录与临时目录，以及文件删除、重命名、硬链接和目录枚举。文件句柄使用钉版分配与锁，文本行和任意二进制字节分别按严格库的 `String` 与 `ByteArray` 传递。路径和环境变量按 UTF-8 字节转换。`IO.Error` 的解码由两个库的构造子、字段类型和运行布局生成，保留文件名、系统错误码、说明及世界状态。测试在临时目录中用多字节路径对照官方异常。

`ShareCommon.State.mk` 使用按工厂和宇宙层级索引的私有逻辑句柄。其原生入口调用钉版的 `ShareCommon.mkStateImpl`。`StateFactory.mk` 接受自定义的映射与集合回调，原生入口适配六个回调、初始容量和哈希结果。严格库的 `UInt64` 在原生端擦除为 Lean 的 `Nat`，适配器用 `lean_uint64_to_nat` 转换完整的 64 位结果。构建 `Init.ShareCommon` 时，普通消费者核验容量 1024、小哈希的表示，以及两种官方工厂和自定义函数映射工厂对布尔列表的共享行为。

严格库用私有、不可计算的句柄构造 `ST.Prim.mkRef`，并保留公开的 `ST.RefPointed` 封装。构建 `Init.System.ST` 时，`native/reference.o` 提供引用分配、身份比较、写入和交换的原生入口。交换的逻辑常量保持不透明，原生入口调用钉版 `lean_st_ref_swap` 取得先前的值。`Void.mk` 由钉版原生入口生成世界，严格端的 `runST`、`runEST` 保留各自返回类型。普通编译和独立 IR 消费者验证状态绑定、类型类分派、收尾动作的异常优先级，以及 `EST.Out` 两个构造子的消去。普通消费者验证两枚引用的身份、交换返回旧值、写入后再交换取得新值和世界状态的传递。使用 `Omega.StateRefT'.set` 时，链接 `native/state_ref.o` 和 `native/reference.o`。

严格库能用 `Void.mk ()` 和 `ST.Prim.mkRef ()` 取得具体的世界与引用地址。对引用读取、取出、返回值修改、相应的状态实例以及 `Lean.Order.EST.bot` 和 `Lean.Order.ST.bot'`，盘点器检查由其完整严格类型能否构造 `(α : Type) → Omega.Nonempty α → α`。原官方类型的 `Void.mk` 与 `ST.Prim.mkRef` 可取任意实现。内核核对其应用于严格公共构造器所得的选择器，与宇宙 0 的官方公理 `Classical.choice.{1}` 具有相同的移植类型。每条归约连同构造器依赖从空内核重放，完整性报告在 `strictImpliesAxiom` 和 `strictSelectionWitness` 中给出目标及见证。[严格选择器](../../../strict/OmegaChecks/InitPort/StrictReferenceChoice.lean) · [归约核验](ReferenceChoiceCheck.lean)

`Omega.withPtrAddrUnsafe` 的返回值通过逐输入证明核对。官方实现把对象的机器地址传给回调 `k`，其参数 `h` 证明任意两个地址产生相同结果。`Omega.withPtrAddrUnsafe` 保留官方 `unsafe` 标记和计算体。校验器读取官方的 `@[implemented_by]` 登记、两端签名和实际计算体，用 `h` 证明每个机器地址所得的返回值都等于 `Omega.withPtrAddr` 的结果。[返回值核验](Address.lean) · [官方指针回调](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Util.lean#L102)

`ptrAddrUnsafe`、`ptrEq` 和 `ptrEqList` 能区分内容相等的两个列表。对于分别分配、唯一自然数字段相等的两个 `NonScalar` 对象，`ShareCommon.Object.ptrEq` 与 `ShareCommon.Object.ptrHash` 也能给出不同结果。运行 `lake env lean --run src/OmegaChecks/InitPort/PointerObservations.lean` 可在钉版 Lean 运行时复现。对原类型的任意纯函数，Lean 的等式替换要求这两组输入得到相同结果。对具有相同大自然数载荷或只含标量的单层列表，`ShareCommon.Object.eq` 和 `hash` 的读数一致。外层列表的载荷含子列表地址，两份等值但独立分配的子列表可使比较和哈希结果不同。若还要求纯装箱函数保留这组原生读数，等式替换会导出矛盾。每次盘点都在当前工具链执行观察。嵌套列表通过 `unsafeCast` 装箱的读数记入 `unsafePackedObservation`。两个接口保留官方的 `unsafe opaque` 类型、借用参数和默认体，原生调用使用钉版比较和哈希入口。纯装箱前提仍是上述条件证明的一项假设。只有实际观测到不同返回值且源码中有针对该原类型的内核矛盾证明时，缺口记录才写入 `runtimeConflictWitness`。[内核证明](../InitInventory/PointerObservations.lean) · [运行时样例](PointerObservations.lean)

严格库的 `Omega.isExclusiveUnsafe` 保留官方的 `unsafe opaque` 声明、内核默认值和借用参数。普通 Lean 声明调用它会被内核拒绝。原生入口读取堆对象的引用计数，调用方需传入有效的堆对象。盘点分别核对两端声明和原生签名，并保留要求纯函数区分等值输入时得到的条件反证。盘点器编译并运行原生观测程序。它分别读取运行时创建的单元素数组与内容相同的常量数组，检查元素为 0 和 1 时的两组输入。两组中都观测到前者独占、后者共享时，才登记与纯函数等式替换的冲突。可运行 `lake exe omegaPointerObservations --exclusivity` 复核。[运行时观测和内核证明](../InitInventory/PointerObservations.lean)

严格库保留 `unsafeBaseIO`、`unsafeEIO` 和 `unsafeIO` 的官方类型和 `unsafe` 标记。`unsafeBaseIO` 从 `Void.mk` 使用的区域索引包取得实世界的初始状态，另两个操作使用官方包装体。内核按依赖次序单独重放这三个声明。官方与严格原生程序分别在写入前后执行同一组读取动作，并核对两种异常返回的载荷。纯函数对相同动作的等式替换约束由盘点器的条件定理记录。[读数与内核证明](../InitInventory/EffectObservations.lean)

`Omega.Array.anyMUnsafe` 按官方机器字索引循环执行。自然数区间长度给出递归上界。每一步仍比较机器字，耗尽区间时两端必然相等，读取位置也在原数组内。即使数组长度达到 `USize.size`，这两个结论仍然成立。例如从零开始搜索恰有 `USize.size` 个元素的整个数组时，转换后的终点为零，循环立即返回 `false`。校验器把官方入口和递归分支逐一与全输入证明核对。[循环及证明](ArrayWord.lean) · [官方数组循环](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Data/Array/Basic.lean#L936)

公开覆盖清单按官方定义模块和声明名逐项列出，重复生成的名字在各自模块有独立记录。
`init-inventory.json` 的 `summary` 按模块与名字的组合计数，`uniqueNames` 按名字去重。
对官方提供原生签名、有定义体且安全、全定义的公开声明，`strictNativeSignature` 记录严格库是否在同一模块打包了对应的 LCNF 签名。`nativeByModule` 和 `summary.native` 分别按模块和全库汇总官方签名数、已匹配声明数和严格库签名数。实际运行结果由编译后的消费用例验证。
全量构建也编译可单独导入的 OmegaMath 和 OmegaMathlib 源文件，一同审计它们的传递依赖。
缺口表的 `firstDependencyPath` 和 `reason` 记录本次移植实际遇到的阻塞。只有 `impliesAxiom` 非空的行另有内核证明，从该官方接口可推出所列公理。`logicalConsequence` 与 `logicalConsequenceWitness` 给出官方环境中已验证的其他逻辑后果及其证明。对任意字符串匹配谓词，正向与反向最长匹配的存在性各自推出排中律。报告分别核对严格见证的输入与官方完整类型的翻译，再在空内核中重放证明闭包。对应两行的 `strictLogicalConsequence` 和 `strictLogicalConsequenceWitness` 保存结论和严格见证。`requiredBehavior` 非空时，证明还需要候选实现满足该项行为前提。

对自然数区间转换为列表和数组的 `isSome`、`isNone` 下标规则，`strictEquivalenceWitness` 给出原定理与自然数比较条件的双向证明。条件要求将布尔判定与算术命题写成命题相等，例如对任意 `a b` 有 `(decide (a ≤ b) = true) = (a ≤ b)`。两端都开放的区间在查找失败时只需右侧为正的比较。报告将完整等价证明连同严格库的区间实现一起从空内核重放。[区间下标等价证明](../InitInventory/RangeIndex.lean)

`equationOperand` 记录官方等式左端直接调用的运算。Lean 按该处的宇宙参数核对 `operandReductionWitness` 的完整类型。给定这个运算的通用实现，即可构造 `operandImpliesAxiom`。对选择函数与递归算子的 `congr_simp` 定理，检查器还用相同谓词或递归步骤特化整个官方等式，核对其参数，再从左右两边分别抽出具有完整 `Classical.choice` 类型的函数。等式本身的可移植性继续按其独立证据结算。

`init-public-reductions.tsv` 列出已移植声明到严格库封装实现的一条最短定义体依赖路径。`officialReductionMechanism` 记录钉版 Lean 的官方机制，包括公开定义体、自然数内建运算、归纳类型、构造子和递归器。盘点 JSON 同时保存路径 `publicReductionBoundary` 与机制。严格库中的 `Nat.gcd` 保留了 Lean 内核识别的根名称。在普通导入中，`Nat.Coprime` 用到的最大公约数能直接在具体自然数上归约，包含大于 64 位的输入。`And.rec` 和 `Iff.rec` 在官方环境中使用递归器计算规则。具体输入是否需要走到路径终点取决于归约过程。

例如，普通导入 `OmegaInit.Data.Nat.Div.Basic` 后可用 `Omega.Nat.div_zero` 证明除数为零的等式。对具体自然数，除法和求余均可用内核内建规则直接归约。若需在符号参数上展开严格定义体，可 `import all OmegaInit.Prelude`，并在证明所在节设置 `attribute [local semireducible] Omega.Nat.div Omega.Nat.ble Omega.Nat.sub Omega.Nat.pred`。

直接运行盘点命令时，先执行 `lake build +OmegaChecks.InitInventory`，再执行 `lake env lean --run src/OmegaChecks/InitInventory.lean <lib> <inventory.json>`。以下完整性验收入口会自动准备所需模块。

完整性验收从安装的钉版 Lean 和待验制品重新读取每个官方公开定义点。运行以下命令，退出码 0 表示全部非公理定义点已通过实际接口审计，或已在源码中逐项登记公理归约或运行时行为与纯函数等式替换相矛盾的证据。遇到尚未解决的定义点，命令写出当前清单和缺口数，然后以退出码 1 结束。

```sh
python3 src/OmegaChecks/InitPort/report.py .lake/init-port-all --require-complete
```

逐项登记位于 `src/OmegaChecks/InitInventory/Reductions.lean` 的 `OmegaChecks.InitBoundaries.reductions`。条目包含官方定义模块、声明、目标公理和见证。Lean 核对指定模块内保存的声明类型，并检查见证可将该类型的任意实现转为目标公理的同类型实现，并从空内核重放见证及其传递依赖。受理的结论为任意类型的选择、命题外延性，或由任意类型的无条件取值推出矛盾。编译器公理中也有可构造的类型，例如可以用任意已有类型实现 `lcAny : Type`。例如，对两个等价命题分别应用 `Classical.propComplete`，在同真或同假两种情形下得到命题相等。将 `WellFounded.extrinsicFix` 用于自关联的单位类型，令递归分支直接自调用，原接口就必须从 `Nonempty α` 返回 `α`。给定可在安全证明中使用的 `unsafeCast` 原类型实现，可以将单位类型的元素送到任意类型，得到 `sorryAx`。官方声明带有 `unsafe` 标记，内核拒绝把它传给此见证。该声明及三个带有相同限制的 ST 接口仍须检查符合原安全级别的实现。报告中的 `reductionWitness` 指向对应 Lean 声明。原证明的公理闭包、未支持原语和编译器限制保留在缺口明细中，完整性验收只接受有见证的缺口。

`Lean.Loop.forIn` 和 `Lean.instForInLoopUnitOfMonad` 的选择规约使用官方固定点方程。测试循环每步继续，并在成功结果中翻转布尔标记。对任意非空异常类型，存在一个始终返回异常值的固定点，因此官方方程适用。成功结果的标记不可能等于自身的否定，循环结果只能携带该异常类型的一个值。`WhileChoice` 在空内核中验证从满足这条方程的实现到 `Classical.choice` 的规约。

`formationArgument` 标出原陈述中须提供证明的实参。`Quot.liftIndepPr1` 的等式左端投影自 `Quot.lift`。盘点程序用常值单位类型特化其官方接口，从部分应用读出 `Quot.indepCoherent` 所在参数的类型，并以空内核重放对应见证。能统一提供该参数就能推出 `Quot.sound`。给定所需的一致性证明后，第一投影等式本身可由商归纳证明。

在 `Init.WFExtrinsicFix` 中，良基或可达证明是应用相应方程的前提。在标出 `formationArgument` 的方程中，左端没有使用该证明。逆像方程取恒等映射与相同的递归步骤后，在右端核对同一性质。按钉版原类型抽象相应端点的其余参数，所得闭函数与完整的无终止前提的 `extrinsicFix` 或 `partialExtrinsicFix` 定义相等。把它传给相应元数的零公理归约，得到 `Classical.choice` 的完整类型。[端点与归约核对](../InitInventory/ChoiceOperands.lean)

`transportPathType` 记录四个商递归器的一致性前提中，`Eq.ndrec` 所需的路径类型。用单位类型作为纤维，并取第一代表元的商类作预先给定的商点后，`Quot.rec` 和 `Quot.recOn` 的路径须对任意关系给出 `Quot.sound`。在 `Quotient.rec` 和 `Quotient.recOn` 中，路径只涉及等价关系，其类型为 `Quotient.sound`，这两个接口保留在未移植清单中。

公开定义点全部结清时，验收命令还逐模块复查实际公开公理记录，从空内核重放整个严格 Init，并以 `omegaAudit` 核验官方名称、定义模块、类型及计算接口。

缺口表的 `abstractedDependency` 标明归约中被全称量化的官方对象。例如，任选一个与 `Option.choice` 同类型的函数，若它在每个非空类型上返回的可选值都满足 `toList.length = 1`，就能从该值取出元素，构造 `Classical.choice`。Lean 会从官方声明的类型中抽出该选择函数，核对剩余命题、目标公理和见证的全部参数。

官方正向、反向命题蕴涵分别定义了偏序与完备格，共四个实例。任何保留相应实例 `rel` 字段计算行为的移植，都能将 `p ↔ q` 的两个方向送入反对称律，得到 `p = q`。校验器从钉版实例投影出实际比较关系，核对四条归约的前提与结论，并在空内核中重放见证。缺口表的 `requiredBehavior` 记录这个计算前提。[归约见证](../InitInventory/Order.lean) · [类型核对](../InitInventory/Reductions.lean)

`originalTypeOrderDependencies` 记录原类型中直接使用正向或反向蕴涵偏序实例的公开定理。核验器在官方环境删除该实例并检查原类型确实报告缺少这一个常量。对任意候选偏序，若它接受钉版实例在任意两个命题间的比较，偏序反对称性即推出 `propext`。归约在严格库上从空内核重放。定理使用比较关系投影后的完整表述仍在两侧公共内核核验，原类型所需的实例列入有证明的例外。[检查实现](ImplicationOrderCheck.lean)

`Classical.epsilon_singleton` 的官方类型使用 `Classical.epsilon`，闭区间迭代方程 `Std.Rxc.Iterator.instIteratorLoop.loop.eq_1` 的右端使用 `WellFounded.extrinsicFix₃`。分别从公开内核移除相应算子后，原式在类型检查时报告缺少该常量。给出任一算子的完整多态类型即可构造 `Classical.choice`，两个归约均在严格后端从空内核重放。盘点用 `originalTypeChoiceDependency` 标明两处原型缺口，保留严格后端已有的特化。[核验实现](ChoiceTypeDependencyCheck.lean)

`List.findFinIdx?_eq_pmap_findIdx?` 和 `Array.findFinIdx?_eq_pmap_findIdx?` 的原文在构造 `Fin` 的下标界证明中使用 `propext`。把这一证明换成从已找到下标取得的界，整个命题在官方公开内核中与原文定义等价，在严格公开内核中与导出的定理类型定义等价。两侧普通导入均可直接使用定理证明相同的完整命题；把结论改成总是返回 `none` 时，两侧都拒绝。严格内核从空环境重放这两条定理。`finBoundProofReplacementChecked` 单独计录这种已移植的完整命题。[双端核验](FinBoundCheck.lean)

`Init.Internal.Order.Basic`、`Lemmas` 和 `MonadTail` 中，通过 `pointwiseOrderTypeChecked` 核验的命题包括列表、数组和选项单调性、函数链、逐点下确界与三个运行器的单调性。官方类型从函数、ReaderT 或状态变换器的偏序实例投影出比较关系，严格类型直接使用相应的逐点比较。核验器在普通导入中对两个完整类型作核内转换，把同一份显式命题分别编译，并从空内核重放严格定理。反转关系两端会使对应定理的类型不匹配。[核验实现](PointwiseOrderCheck.lean)




### 范围大小与双重否定消除

给定官方原类型的 `Std.Rxc.size_pos_iff_le` 或 `Std.Rxo.size_pos_iff_lt`，都能推出任意命题的双重否定消除，继而推出排中律。令范围的端点都为 `Unit.unit`，把端点比较定义成待证命题 `p`，把大小定义成 1。在 `¬¬p` 下，假设比较失败就得到矛盾，因而满足比较失败时大小为零的类定律。对大小为正应用官方接口即可得到 `p`。清单生成器会从空内核重放这两条归约及双重否定消除推出排中律的证明。[Lean 归约](../InitInventory/Logic.lean) · [官方范围接口](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Data/Range/Polymorphic/Basic.lean#L78)

同一检查也重放两世界 Kripke 反模型 `TwoWorlds.countermodel`。原子命题只在后继世界成立。根世界强制它的双重否定，也同时见证该命题及其否定都未被根世界强制。这排除了直觉主义命题逻辑中的双重否定消除和排中律。Sato 与 Garrigue 的 §4.2.2 在其依赖类型演算 CCω 中给出排中律反模型。§5 的归纳类型扩展覆盖列表。要用该结果判定 Lean 4.35 零公理内核中的不可导性，仍需证明模型支持该内核的一般归纳族、消去及定义等价规则。两个范围接口因此继续列入未解决项。[Kripke 语义与可靠性](https://plato.stanford.edu/entries/logic-intuitionistic/#KripBethSemaForIntuLogi) · [Sato 与 Garrigue 的模型](https://doi.org/10.1017/S0960129523000087)

`Classical.not_and_iff_not_or_not` 的官方接口与弱排中律 `∀ p, ¬p ∨ ¬¬p` 可互推。三世界分叉 Kripke 模型中，一个叶子强制 `p`，另一个强制 `¬p`，因此根不强制弱排中律。空内核重放两个方向的转换和模型的可达关系、自反性、传递性、原子赋值单调性与根的反例。此反例适用于直觉主义命题逻辑；Lean 完整内核中的不可导性仍属于未解决项。

`Classical.decide_not`、`Classical.ite_not` 和 `Classical.dite_not` 都接受 `Decidable (¬p)`，等式右端通过 `Classical.decidable_of_decidable_not` 取得 `Decidable p`。从官方类型中抽象出此转换函数后，三条等式均由无公理证明给出。实现这个对所有命题适用的转换函数可以推出排中律。
