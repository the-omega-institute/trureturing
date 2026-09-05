using StrataLint.Engine;
using StrataLint.Scribe;
using System.Xml.Linq;

namespace StrataLint.ArchitectureTests;

public sealed class DependencyDirectionTests
{
    /// <summary>
    /// The list is the declaration point for a new trust root, which is why it is written
    /// out rather than derived: anything the engine links against can decide what the
    /// harness admits. Markdig parses the block AST behind the default atomizer; it is
    /// BSD-2-Clause, pure managed code, and has no package dependencies of its own on this
    /// target framework, so adopting it adds exactly one name here and nothing beneath it.
    /// Trureturing.Truth is the packable truth-graph read/write/verify library at the bottom
    /// of the graph; it references nothing StrataLint and only the BCL, so linking the engine
    /// against it adds exactly one name here and nothing beneath it.
    /// </summary>
    [Fact]
    public void EngineReferencesExactlyBclDunetMarkdigPidginRoslynAndTruth()
    {
        Assert.Equal(
            ["Dunet", "Markdig", "Microsoft.CodeAnalysis", "Microsoft.CodeAnalysis.CSharp", "Pidgin", "Tomlyn", "Trureturing.Truth"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(AdmissionPipeline).Assembly));
    }

    [Fact]
    public void CliReferencesExactlyEngineScribeTomlynTruthAndYamlDotNet()
    {
        Assert.Equal(
            ["StrataLint.Engine", "StrataLint.Scribe", "Tomlyn", "Trureturing.Truth", "YamlDotNet"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(StrataLint.Cli.Program).Assembly));
    }

    /// <summary>
    /// Jint runs the vendored KaTeX so the markdown gate parses formulas with the site's
    /// own parser rather than a second reading of its grammar. It is BSD-2-Clause pure
    /// managed code and brings one name beneath it, Acornima (BSD-3-Clause), its
    /// JavaScript parser; nothing it runs is trusted, because the gate keeps the parse
    /// verdict and discards the rendered HTML.
    /// </summary>
    [Fact]
    public void ScribeReferencesExactlyEngineJintQuestPdfTomlynAndTruth()
    {
        Assert.Equal(
            ["Jint", "QuestPDF", "StrataLint.Engine", "Tomlyn", "Trureturing.Truth"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(ScribeEmitter).Assembly));
    }

    [Fact]
    public void FunctionalTestsReferenceOnlyCliEngineAndScribe()
    {
        // 此处曾另有一条产物层(IL)断言,钉 `["StrataLint", "StrataLint.Engine",
        // "StrataLint.Scribe", "StrataLint.TestSupport"]`。**已删,且没有丢失可达的检测**:
        // 该项目直接声明的只有 Cli 与 TestSupport,而 Cli 的引用集由
        // CliReferencesExactlyEngineScribeTomlynTruthAndYamlDotNet 钉死,
        // 故传递可达的 StrataLint* 集合**恰好等于**原 IL 断言钉住的那个集合 ——
        // 再钉一遍不增加信息(第〇节:f 与真源都已被守,投影必然对)。
        // 要让第四个 StrataLint* 程序集变得可达,必须改 Cli 的引用集(已钉)
        // 或给本项目加一条直接声明(拓扑判官判 extra-production-reference)。
        // 删它的收益:该测试方法的唯一 unknown 成因是反射,去掉后它在**原身份上**变 known,
        // 全仓 unknown 债 −1(搬迁会被 SL-003 判新增,原地去反射不会 —— 见 #5419 与撤回的 #5440)。
        Assert.Equal(
            // Engine 经 Cli 传递可得,故这条直接引用是多余的 extra-production-reference 存量债;
            // 本 PR 顺手还掉它(拓扑棘轮要求碰债务面即严格减债)。程序集级引用集不变。
            [
                "../../StrataLint.Cli/StrataLint.Cli.csproj",
                "../../TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj",
            ],
            ProjectReferences(XDocument.Load(Path.Combine(
                RepositoryLayout.FindRoot(),
                "tools",
                "tests",
                "StrataLint.Tests",
                "StrataLint.Tests.csproj"))));
    }

    [Fact]
    // Keep the name: ScribeUnknownDebtPolicy's identity ratchet makes a rename new debt; the assertion body governs.
    public void EngineeringScopeTestsReferenceOnlyEngineeringScope()
    {
        Assert.Equal(
            ["StrataLint.EngineeringScope", "StrataLint.TestSupport"],
            AssemblyReferencePolicy.ApplicationReferences(
                typeof(StrataLint.EngineeringScope.Tests.TestProcessRunnerTests).Assembly));
        Assert.Equal(
            [
                "../../StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
                "../../TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj",
            ],
            ProjectReferences(XDocument.Load(Path.Combine(
                RepositoryLayout.FindRoot(),
                "tools",
                "tests",
                "StrataLint.EngineeringScope.Tests",
                "StrataLint.EngineeringScope.Tests.csproj"))));
    }

    [Fact]
    // Keep the name: ScribeUnknownDebtPolicy's identity ratchet makes a rename new debt; the assertion body governs.
    public void ScribeTestsReferenceOnlyEngineAndScribe()
    {
        // 原为产物层(IL)断言,钉 `["StrataLint.Engine", "StrataLint.Scribe",
        // "StrataLint.TestSupport"]`,是本族三条里唯一**没有**声明层半边的一条。
        // 换成同形的 csproj 断言,理由与 FunctionalTests 那条相同:
        // 直接声明为 {Scribe, TestSupport},而 Scribe 的引用集由
        // ScribeReferencesExactlyEngineJintQuestPdfTomlynAndTruth 钉死 ⟹
        // 传递可达的 StrataLint* 恰为 {Scribe, Engine, TestSupport} = 原 IL 断言的集合。
        // **对照:EngineeringScopeTests 那条不能这样处理** —— 它钉住的 IL 集合是其可达集合的
        // **真子集**(Engine 可达却未被使用),那条断言因此有可达的独有保护,保留不动。
        Assert.Equal(
            [
                "../../StrataLint.Scribe/StrataLint.Scribe.csproj",
                "../../TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj",
            ],
            ProjectReferences(XDocument.Load(Path.Combine(
                RepositoryLayout.FindRoot(),
                "tools",
                "tests",
                "StrataLint.Scribe.Tests",
                "StrataLint.Scribe.Tests.csproj"))));
    }

    [Fact]
    public void ArchitectureTestsReferenceOnlyDeclaredDependencies()
    {
        Assert.Equal(
            [
                "../../StrataLint.Cli/StrataLint.Cli.csproj",
                "../../StrataLint.Engine/StrataLint.Engine.csproj",
                "../../StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
                "../../StrataLint.Scribe/StrataLint.Scribe.csproj",
                "../../TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj",
                "../StrataLint.EngineeringScope.Tests/StrataLint.EngineeringScope.Tests.csproj",
                "../StrataLint.Tests/StrataLint.Tests.csproj",
            ],
            ProjectReferences(XDocument.Load(Path.Combine(
                RepositoryLayout.FindRoot(),
                "tools",
                "tests",
                "StrataLint.ArchitectureTests",
                "StrataLint.ArchitectureTests.csproj"))));
    }

    private static string[] ProjectReferences(XDocument project) => project
        .Descendants()
        .Where(static element => element.Name.LocalName == "ProjectReference")
        .Select(static element => (string?)element.Attribute("Include"))
        .OfType<string>()
        .Order(StringComparer.Ordinal)
        .ToArray();
}
