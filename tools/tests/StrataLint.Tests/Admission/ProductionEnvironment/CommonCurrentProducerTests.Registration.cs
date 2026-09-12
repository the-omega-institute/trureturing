using System.Text;
using System.Text.Json.Nodes;
using System.Xml.Linq;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using Xunit.Abstractions;

namespace StrataLint.Tests;

public sealed class ScribeInvocationRegistrationTests(ITestOutputHelper output)
{
    private const string Invocation = "tools/StrataLint.Cli/Admission/ProductionCliEnvironment.CurrentChecks.cs";
    private const string Verification = "tools/StrataLint.Cli/Runtime/ScribeEmissionVerifier.cs";
    private const string Producer = "Meta/ReportProducers/scribe-content.json";

    [Theory]
    [InlineData(Invocation)]
    [InlineData(Verification)]
    public void ChangedRegisteredCliBytesExecuteChangedScribeBehaviorAndPreserveUnrelatedProvenance(string changed)
    {
        using var fixture = new InvocationFixture(output);
        var original = fixture.Run();
        fixture.Seed(original.Record);
        fixture.Write("notes/unrelated.md", "metadata-only candidate change");
        var warm = fixture.Run();
        Assert.All(warm.Record.Units, unit => Assert.Equal("reused", unit.Status));
        AssertOriginal(original.Record, warm.Record);
        var source = fixture.Read(changed);
        var modified = changed == Invocation
            ? source.Replace("[\"describe-report\", \"--check\"]", "[\"describe-report\", \"--check\", \"--json\"]", StringComparison.Ordinal)
            : source.Replace("return (definitions is null", "Console.Error.WriteLine(\"verified-material-v2\");\n        return (definitions is null", StringComparison.Ordinal);
        Assert.NotEqual(source, modified);
        fixture.Write(changed, modified);
        fixture.Compile();
        var final = fixture.Run();
        Assert.All(final.Record.Units.Where(unit => unit.Id.StartsWith("scribe-", StringComparison.Ordinal)),
            unit => Assert.Equal("executed", unit.Status));
        var independent = final.Record.Units.Single(unit => unit.Id == "filemap");
        Assert.Equal("reused", independent.Status);
        AssertOriginal(original.Record, final.Record, "filemap");
        if (changed == Invocation)
        {
            var before = fixture.Read(original.Record.Units.Single(unit => unit.Id == "scribe-describe").Operations.Single().Log);
            var after = fixture.Read(final.Record.Units.Single(unit => unit.Id == "scribe-describe").Operations.Single().Log);
            Assert.NotEqual(before, after);
            Assert.StartsWith("{", after.TrimStart(), StringComparison.Ordinal);
        }
        else Assert.Contains("verified-material-v2", final.Error, StringComparison.Ordinal);
        output.WriteLine("Changed CLI behavior executed; all three Scribe units executed; unrelated filemap reused its original execution candidate, round and materials.");
    }

    private static void AssertOriginal(CommonCheckRecord before, CommonCheckRecord after, string? id = null)
    {
        foreach (var unit in after.Units.Where(unit => id is null || unit.Id == id))
        {
            var original = before.Units.Single(previous => previous.Id == unit.Id);
            Assert.Equal(original.ExecutionCandidate, unit.ExecutionCandidate);
            Assert.Equal(original.ExecutionRound, unit.ExecutionRound);
            Assert.Equal(original.Operations, unit.Operations);
            Assert.Equal(original.Materials, unit.Materials);
        }
    }

    private sealed class InvocationFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string program;
        private readonly ITestOutputHelper output;
        internal string Root { get; }
        internal InvocationFixture(ITestOutputHelper output)
        {
            this.output = output;
            Root = Path.Combine(temporary.Path, "repository");
            program = Path.Combine(temporary.Path, "program");
            Directory.CreateDirectory(program);
            var source = TestRepositoryLayout.FindRoot();
            var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(source, Producer)))!;
            Write(Producer, manifest.ToJsonString());
            foreach (var input in manifest["scripts"]!.AsArray().Concat(manifest["materials"]!.AsArray())
                .Select(item => item!.GetValue<string>()).Append(Invocation).Append(Verification).Distinct())
                Write(input, File.ReadAllText(Path.Combine(source, input)));
            var projects = manifest["projects"]!.AsArray().Select(item => item!.GetValue<string>())
                .Append("tools/StrataLint.Cli/StrataLint.Cli.csproj").Append("fixtures/Independent.csproj").ToArray();
            foreach (var path in projects) Write(path, "<Project />");
            Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(projects.Select(path =>
                new EngineeringProjectFixture(path, Path.GetFileNameWithoutExtension(path), "test-support", false,
                    path.Contains("StrataLint.Cli", StringComparison.Ordinal) ? [Invocation, Verification]
                        : path.Contains("Scribe.Documents", StringComparison.Ordinal) ? ["Blueprint/D5/S0/Synthetic/Invocation.scribe.cs"] : [])).ToArray()));
            var checks = JsonNode.Parse(CommonCheckRegistrationFixture.Manifest("fixtures/Independent.csproj"))!;
            var actual = JsonNode.Parse(File.ReadAllText(Path.Combine(source, "Meta/ci-checks.json")))!["checks"]!.AsArray();
            foreach (var row in checks["checks"]!.AsArray().Where(row => row!["id"]!.ToString().StartsWith("scribe-", StringComparison.Ordinal)))
            {
                var registered = actual.Single(item => item!["id"]!.ToString() == row!["id"]!.ToString())!;
                row!["program_projects"] = registered["program_projects"]!.DeepClone();
                row["report_inputs"] = registered["report_inputs"]!.DeepClone();
            }
            Write("Meta/ci-checks.json", checks.ToJsonString());
            Write("lean-toolchain", "leanprover/lean4:v4.33.0");
            Write("lakefile.toml", "name = \"fixture\"");
            Write("lake-manifest.json", "{\"packages\":[]}");
            var policyFixture = new RuleFixture();
            Write("Meta/registry.yaml", policyFixture.Files["Meta/registry.yaml"]);
            Write("Meta/domains.yaml", policyFixture.Files["Meta/domains.yaml"]);
            foreach (var name in new[] { "pilot", "expansion" }) Write($"Golden/Projection/statement-projection-{name}-v1.json",
                "{\"schema\":\"statement-projection-" + name + "-fixture-v1\",\"declarations\":[]}");
            Write("Blueprint/D5/S0/Synthetic/Invocation.scribe.cs", "namespace StrataLint.Scribe.Blueprint.D5.S0.Synthetic;\n");
            Write("D5/S0/Synthetic/Invocation.lean", "-- synthetic module\n");
            Write("Meta/Digestion/backfill/synthetic-source/source.toml", "source_id = \"synthetic-source\"\npath = \"docs/synthetic.md\"\natomizer = \"synthetic-v1\"\ngenre_registry_check = \"collected\"\nunregistered_genres = []\n");
            Write(".gitignore", "build/\n.lake/\n");
            Git("init", "-q"); Git("add", ".");
            RawLeanReportArtifact.WriteFile(Path.Combine(Root, CommonExecutionEvidence.ReportPath), CommonExecutionEvidence.Snapshot(Root),
                LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> { ["D5/S0/Synthetic/Invocation.lean"] = new([], []) }));
            foreach (var suffix in new[] { ".sha256", ".input.attestation", ".provenance.json", ".seed.json" })
                Write(CommonExecutionEvidence.ReportPath + suffix, "fixture companion");
            // Compile these two actual CLI sources. The fixture supplies only the surrounding
            // command host and one document; Scribe and reuse execute production DLLs.
            var project = new XElement("Project", new XAttribute("Sdk", "Microsoft.NET.Sdk"),
                new XElement("PropertyGroup", new XElement("TargetFramework", "net10.0"), new XElement("OutputType", "Exe"),
                    new XElement("AssemblyName", "StrataLint"), new XElement("ImplicitUsings", "enable"), new XElement("Nullable", "enable")),
                new XElement("ItemGroup", new[] { Invocation, Verification }.Select(path =>
                    new XElement("Compile", new XAttribute("Include", Path.Combine(Root, path))))),
                new XElement("ItemGroup", new[] { "StrataLint.EngineeringScope", "StrataLint.Engine", "StrataLint.Scribe", "Trureturing.Truth" }.Select(name =>
                    new XElement("Reference", new XAttribute("Include", name),
                        new XElement("HintPath", Path.Combine(AppContext.BaseDirectory, name + ".dll"))))));
            File.WriteAllText(Path.Combine(program, "Fixture.csproj"), project.ToString());
            File.WriteAllText(Path.Combine(program, "Host.cs"), Host);
            Compile();
        }
        internal void Compile()
        {
            var result = TestProcessRunner.Run("dotnet", ["build", "Fixture.csproj", "--configuration", "Release", "--nologo"],
                program, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
            foreach (var path in new[] { Path.Combine(Root, Invocation), Path.Combine(Root, Verification),
                Path.Combine(program, "bin/Release/net10.0/StrataLint.dll") })
                output.WriteLine(path + " sha256=" + Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(path))));
        }
        internal (CommonCheckRecord Record, string Error) Run()
        {
            Git("add", ".");
            Write("build/ci/fixture.log", "fixture build");
            var build = CommonExecutionEvidence.SealBuild(Root, CommonExecutionEvidence.Candidate(Root), ["build/ci/fixture.log"],
                CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/fixture.log")).ToArray());
            var result = TestProcessRunner.Run("dotnet", [Path.Combine(program, "bin/Release/net10.0/StrataLint.dll"), Root, build.Round],
                Root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
            var error = Encoding.UTF8.GetString(result.StandardError);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + error
                + string.Join("\n", Directory.GetFiles(Path.Combine(Root, "build/ci"), "*.log", SearchOption.AllDirectories).Select(File.ReadAllText)));
            return (CommonExecutionEvidence.ValidateChecks(Root, "current", build,
                ["filemap", "scribe-describe", "scribe-markdown", "scribe-projections"]), error);
        }
        internal void Seed(CommonCheckRecord record)
        {
            var seed = Path.Combine(Root, CommonExecutionEvidence.CheckSeedPath("current"));
            foreach (var material in record.Units.SelectMany(unit => unit.Materials).Distinct())
            {
                var target = Path.Combine(seed, material.Path);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(Path.Combine(Root, material.Path), target);
            }
            CommonExecutionEvidence.Write(seed, "checks.json", record);
        }
        internal string Read(string path) => File.ReadAllText(Path.Combine(Root, path));
        internal void Write(string path, string value)
        {
            var target = Path.Combine(Root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.WriteAllText(target, value);
        }
        private void Git(params string[] args) => Assert.Equal(0,
            TestProcessRunner.Run("git", args, Root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024).ExitCode);
        public void Dispose() => temporary.Dispose();
        private const string Host = """
            using StrataLint.Engine;
            using StrataLint.EngineeringScope;
            using StrataLint.Scribe;
            namespace StrataLint.Scribe.Documents { public sealed class DocumentAssembly { } }
            namespace StrataLint.Cli {
                internal sealed class FixtureDocument : IScribeDocumentDefinition {
                    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
                        DefinitionDsl.Header("D5/S0/Synthetic/Invocation", "Invocation fixture."), DefinitionDsl.H("Invocation"),
                        DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Invocation body.")))),
                        "Blueprint/D5/S0/Synthetic/Invocation.scribe.cs");
                }
                internal sealed record ExplicitCommandResult(int ExitCode, string Output, string Error);
                internal sealed partial class ProductionCliEnvironment {
                    private readonly string repositoryRoot;
                    private ProductionCliEnvironment(string root) { repositoryRoot = root; }
                    private ExplicitCommandResult FileMapConform(string[] args) => new(0, "independent fixture", "");
                    private ExplicitCommandResult RenderStage(RuleExecutionOutcome result) => throw new InvalidOperationException("unexpected rule execution");
                    public static int Main(string[] args) {
                        var snapshot = CommonExecutionEvidence.Snapshot(args[0]);
                        var report = RawLeanReportArtifact.ReadFile(Path.Combine(args[0], CommonExecutionEvidence.ReportPath), snapshot, validateMaterials: true);
                        var result = new ProductionCliEnvironment(args[0]).ExecuteCommonCurrent(args[1], snapshot, null!, null!, report,
                            ["filemap", "scribe-describe", "scribe-markdown", "scribe-projections"]);
                        Console.Write(result.Output); Console.Error.Write(result.Error); return result.ExitCode;
                    }
                }
            }
            """;
    }
}
