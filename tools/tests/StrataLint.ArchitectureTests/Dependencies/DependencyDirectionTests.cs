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
    public void RegisteredProgramCompileInputsExcludeBlueprintDefinitions()
    {
        var root = TestRepositoryLayout.FindRoot();
        var paths = StrataLint.FileMap.FileMapPolicy.TrackedPaths(root);
        var registry = EngineeringProjectRegistry.Read(paths.Select(path => new EngineeringSource(path,
            path == EngineeringProjectRegistry.ManifestPath ? File.ReadAllText(Path.Combine(root, path)) : string.Empty)).ToArray());
        Assert.All(registry.Projects, project => Assert.DoesNotContain(project.Include,
            input => input.StartsWith("Blueprint/", StringComparison.Ordinal)));
        foreach (var project in registry.Projects)
        {
            var xml = XDocument.Load(Path.Combine(root, project.Path));
            Assert.DoesNotContain(xml.Descendants("Compile"), compile =>
                ((string?)compile.Attribute("Include"))?.Contains("Blueprint", StringComparison.Ordinal) is true);
        }
    }

    [Fact]
    public void CliReferencesExactlyConfigurationEngineScribeTestEvidenceTomlynAndTruth()
    {
        Assert.Equal(
            [
                "StrataLint.Configuration",
                "StrataLint.Engine",
                "StrataLint.FileMap",
                "StrataLint.Lean",
                "StrataLint.Scribe",
                "StrataLint.TestEvidence",
                "Tomlyn",
                "Trureturing.Truth",
            ],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(StrataLint.Cli.Program).Assembly));
    }

    [Fact]
    public void TestEvidenceReferencesExactlyEngine()
    {
        Assert.Equal(["StrataLint.Engine"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(StrataLint.TestEvidence.Program).Assembly));
        Assert.Equal(["../StrataLint.Engine/StrataLint.Engine.csproj"], ProjectReferences(XDocument.Load(
            Path.Combine(RepositoryLayout.FindRoot(), "tools/StrataLint.TestEvidence/StrataLint.TestEvidence.csproj"))));
    }

    [Fact]
    public void ConfigurationReferencesExactlyEngineAndYamlDotNet()
    {
        Assert.Equal(
            ["StrataLint.Engine", "YamlDotNet"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(RepositoryPolicyLoader).Assembly));
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
            ["Jint", "Microsoft.CodeAnalysis", "Microsoft.CodeAnalysis.CSharp", "QuestPDF", "StrataLint.Engine", "Tomlyn", "Trureturing.Truth"],
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
                "../../TestSupport/StrataLint.CoverTestSupport/StrataLint.CoverTestSupport.csproj",
                "../../TestSupport/StrataLint.DeclaredTemplateTestSupport/StrataLint.DeclaredTemplateTestSupport.csproj",
                "../../TestSupport/StrataLint.DigestionTestSupport/StrataLint.DigestionTestSupport.csproj",
                "../../TestSupport/StrataLint.LeanTestSupport/StrataLint.LeanTestSupport.csproj",
                "../../TestSupport/StrataLint.ProcessTestSupport/StrataLint.ProcessTestSupport.csproj",
                "../../TestSupport/StrataLint.RegistrationTestSupport/StrataLint.RegistrationTestSupport.csproj",
                "../../TestSupport/StrataLint.RuleTestSupport/StrataLint.RuleTestSupport.csproj",
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
    public void ScribeTestsReferenceOnlyEngineAndScribe()
    {
        // 直接项目引用由本断言核对;Scribe 的依赖由
        // ScribeReferencesExactlyEngineJintQuestPdfTomlynAndTruth 核对。
        // 两者共同限定声明层的传递依赖;IL 使用集是独立的检查对象。
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
                "../../StrataLint.FileMap/StrataLint.FileMap.csproj",
                "../../StrataLint.Scribe/StrataLint.Scribe.csproj",
                "../../StrataLint.TestEvidence/StrataLint.TestEvidence.csproj",
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
