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
        // YamlDotNet also supplies the parser for SL-030.
        Assert.Equal(
            ["Dunet", "Markdig", "Microsoft.CodeAnalysis", "Microsoft.CodeAnalysis.CSharp", "Pidgin", "Tomlyn", "Trureturing.Truth", "YamlDotNet"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(AdmissionPipeline).Assembly));
    }

    [Fact]
    public void CliReferencesExactlyConfigurationEngineScribeTomlynAndTruth()
    {
        Assert.Equal(
            [
                "StrataLint.Configuration",
                "StrataLint.Engine",
                "StrataLint.ExecutionEvidence",
                "StrataLint.InspectionScope",
                "StrataLint.Lean",
                "StrataLint.ResourcePlanning",
                "StrataLint.Scribe",
                "StrataLint.Scribe.Documents",
                "Tomlyn",
                "Trureturing.Truth",
            ],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(StrataLint.Cli.Program).Assembly));
    }

    [Fact]
    public void ConfigurationReferencesExactlyEngineAndYamlDotNet()
    {
        Assert.Equal(
            ["StrataLint.Engine", "YamlDotNet"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(RegistryLoader).Assembly));
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
        // The owned CLI tests use their owner and explicit shared fixtures.
        Assert.Equal(
            [
                "../../StrataLint.Cli/StrataLint.Cli.csproj",
                "../../TestSupport/StrataLint.AdmissionTestSupport/StrataLint.AdmissionTestSupport.csproj",
                "../../TestSupport/StrataLint.CliTestSupport/StrataLint.CliTestSupport.csproj",
                "../../TestSupport/StrataLint.ConfigurationTestSupport/StrataLint.ConfigurationTestSupport.csproj",
                "../../TestSupport/StrataLint.LeanTestSupport/StrataLint.LeanTestSupport.csproj",
                "../../TestSupport/StrataLint.ProcessTestSupport/StrataLint.ProcessTestSupport.csproj",
                "../../TestSupport/StrataLint.RegistrationTestSupport/StrataLint.RegistrationTestSupport.csproj",
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
    public void EngineeringScopeTestsReferenceOnlyEngineeringScope()
    {
        // 此处曾有一条产物层(IL)断言,钉 `["StrataLint.EngineeringScope", "StrataLint.TestSupport"]`
        // —— 它守的是「`Engine` 传递可达却未被使用」。**已由更强的东西取代,不是删除**:
        // EngineeringScope.Tests 现在声明 <DisableTransitiveProjectReferences>true</…>,
        // `Engine` 在**编译期**即不可达,用了就编译不过(事前不可能 > 事后检测,第 20 条)。
        // 这也去掉了该断言唯一需要的那条 test→test ProjectReference。
        Assert.Equal(
            ["../../StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj"],
            ProjectReferences(XDocument.Load(Path.Combine(
                RepositoryLayout.FindRoot(),
                "tools",
                "tests",
                "StrataLint.EngineeringScope.Tests",
                "StrataLint.EngineeringScope.Tests.csproj"))));
    }

    [Fact]
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
                "../../TestSupport/StrataLint.RegistrationTestSupport/StrataLint.RegistrationTestSupport.csproj",
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
                "../../StrataLint.Configuration/StrataLint.Configuration.csproj",
                "../../StrataLint.Engine/StrataLint.Engine.csproj",
                "../../StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
                "../../StrataLint.ExecutionEvidence/StrataLint.ExecutionEvidence.csproj",
                "../../StrataLint.InspectionScope/StrataLint.InspectionScope.csproj",
                "../../StrataLint.Scribe/StrataLint.Scribe.csproj",
                "../../TestSupport/StrataLint.AdmissionTestSupport/StrataLint.AdmissionTestSupport.csproj",
                "../../TestSupport/StrataLint.ConfigurationTestSupport/StrataLint.ConfigurationTestSupport.csproj",
                "../../TestSupport/StrataLint.ProcessTestSupport/StrataLint.ProcessTestSupport.csproj",
                "../../TestSupport/StrataLint.RegistrationTestSupport/StrataLint.RegistrationTestSupport.csproj",
                "../../TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj",
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
