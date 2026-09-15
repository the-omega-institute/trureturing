using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class UpstreamProbeVerifierTests
{
    internal const string Source = "import Mathlib\ntheorem probe : True := by trivial\n#print axioms probe\n";
    internal const string Output = "'probe' depends on axioms: [propext, Classical.choice, Quot.sound]\n";
    internal const string Manifest = "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"}]}";

    [Theory]
    [InlineData("import D5.S0.Carrier.Probe\n", "PROBE_IMPORTS_PROJECT")]
    [InlineData("import Mathlib D5.S0.Carrier.Probe\n", "PROBE_IMPORTS_PROJECT")]
    [InlineData("import Unpinned\n", "PROBE_IMPORTS_PROJECT")]
    [InlineData("", "PROBE_IMPORTS_PROJECT")]
    [InlineData("import Mathlib\n/- sorry -/\n", "PROBE_FAILED")]
    [InlineData("import Mathlib\naxiom secret : True\n", "PROBE_FAILED")]
    [InlineData("import Mathlib\n-- native_decide\n", "PROBE_FAILED")]
    public void RejectsInvalidImportsAndForbiddenSourceBeforeExecution(string imports, string code)
    {
        using var fixture = new ProbeFixture();
        var source = Source.Replace("import Mathlib\n", imports, StringComparison.Ordinal);
        var error = Assert.Throws<UpstreamSettlementException>(() => fixture.Verify(source));
        Assert.Equal(code, error.Code);
        Assert.Empty(fixture.Runner.Sources);
    }

    [Theory]
    [InlineData(1, "", "", "PROBE_FAILED")]
    [InlineData(0, "warning: declaration uses sorry\n", "", "PROBE_FAILED")]
    [InlineData(0, "", "sorryAx", "PROBE_FAILED")]
    [InlineData(0, "'probe' depends on axioms: [secret]\n", "", "PROBE_AXIOMS")]
    [InlineData(0, "", "", "PROBE_AXIOMS")]
    [InlineData(0, "'other' depends on axioms: [propext]\n", "", "PROBE_AXIOMS")]
    public void RejectsCompileAndAxiomFailuresBeforeResolution(int exit, string stdout, string stderr, string code)
    {
        using var fixture = new ProbeFixture();
        fixture.Runner.Results.Enqueue(new(exit, Encoding.UTF8.GetBytes(stdout), Encoding.UTF8.GetBytes(stderr)));
        var error = Assert.Throws<UpstreamSettlementException>(() => fixture.Verify());
        Assert.Equal(code, error.Code);
        Assert.Single(fixture.Runner.Sources);
        Assert.Empty(Directory.EnumerateFiles(Path.Combine(fixture.Root, ".lake"), "upstream-*", SearchOption.AllDirectories));
    }

    [Theory]
    [InlineData("theorem probe : True := by trivial\n")]
    [InlineData("example : True := by trivial\n#print axioms probe\n")]
    [InlineData("lemma probe : True := by trivial\n#print axioms probe\n")]
    [InlineData("theorem probe : True := by trivial\n#print axioms probe\n#check True\n")]
    public void RequiresNamedTheoremsAndTrailingPrints(string body)
    {
        using var fixture = new ProbeFixture();
        var error = Assert.Throws<UpstreamSettlementException>(() => fixture.Verify("import Mathlib\n" + body));
        Assert.Equal("PROBE_AXIOMS", error.Code);
        Assert.True(fixture.Runner.Sources.Count <= 1);
    }

    [Fact]
    public void CollectsSortedUnionAndResolvesAllDeclarationsInOneCleanFile()
    {
        using var fixture = new ProbeFixture();
        fixture.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes(Output + "'second' depends on axioms: [propext]\n"), []));
        var source = Source.Replace("#print axioms probe", "theorem second : True := by trivial\n#print axioms probe\n#print axioms second", StringComparison.Ordinal);
        Assert.Equal(new[] { "Classical.choice", "Quot.sound", "propext" }, fixture.Verify(source).ToArray());
        Assert.Equal(2, fixture.Runner.Sources.Count);
        Assert.Equal(source, fixture.Runner.Sources[0]);
        Assert.Equal("import Mathlib\n#check @Nat.add_comm\n#check @True.intro\n", fixture.Runner.Sources[1]);
        Assert.All(fixture.Runner.Paths, path => Assert.False(File.Exists(path)));
    }

    [Fact]
    public void AcceptsNoAxiomForm()
    {
        using var fixture = new ProbeFixture();
        fixture.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes("'probe' does not depend on any axioms\n"), []));
        Assert.Empty(fixture.Verify());
    }

    [Fact]
    public void ReportsFirstUnresolvedDeclarationAndAllDiagnostics()
    {
        using var fixture = new ProbeFixture();
        fixture.Runner.Results.Enqueue(new(0, Encoding.UTF8.GetBytes(Output), []));
        fixture.Runner.Results.Enqueue(new(1, Encoding.UTF8.GetBytes("check.lean:3:8: error: Unknown constant `True.intro`\n"), Encoding.UTF8.GetBytes("full resolver diagnostics")));
        var error = Assert.Throws<UpstreamSettlementException>(() => fixture.Verify());
        Assert.Equal("DECLARATION_UNRESOLVED", error.Code);
        Assert.StartsWith("True.intro", error.Message, StringComparison.Ordinal);
        Assert.Contains("full resolver diagnostics", error.Message, StringComparison.Ordinal);
        Assert.Equal(2, fixture.Runner.Sources.Count);
        Assert.All(fixture.Runner.Paths, path => Assert.False(File.Exists(path)));
    }

    [Fact]
    public void HangGuardIsInfrastructureAndScratchIsRemoved()
    {
        using var fixture = new ProbeFixture();
        fixture.Runner.Failure = new TimeoutException("infrastructure-hang-guard expired");
        Assert.Throws<TimeoutException>(() => fixture.Verify());
        Assert.All(fixture.Runner.Paths, path => Assert.False(File.Exists(path)));
    }

    internal sealed class ProbeFixture : IDisposable
    {
        private readonly TemporaryDirectory directory = new();
        internal string Root => directory.Path;
        internal CannedRunner Runner { get; } = new();
        internal ProbeFixture()
        {
            TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(Root, ".lake/packages/mathlib"));
            TemporaryFileSystem.File.WriteAllText(Path.Combine(Root, ".lake/packages/mathlib/Mathlib.lean"), "", Encoding.UTF8);
        }
        internal ImmutableArray<string> Verify(string source = Source) => new UpstreamProbeVerifier(Runner, "synthetic-lake", PinnedProductionBudgets.UpstreamProbeBudget)
            .Verify(Root, Encoding.UTF8.GetBytes(source), Manifest, ["Nat.add_comm", "True.intro"]);
        public void Dispose() => directory.Dispose();
    }

    internal sealed class CannedRunner : IUpstreamLeanProcessRunner
    {
        internal Queue<ProcessOutput> Results { get; } = new();
        internal List<string> Sources { get; } = [];
        internal List<string> Paths { get; } = [];
        internal Exception? Failure { get; set; }
        public ProcessOutput Run(string executable, IReadOnlyList<string> arguments, string root, TimeSpan budget)
        {
            Assert.Equal("synthetic-lake", executable);
            Assert.Equal(new[] { "env", "lean" }, arguments.Take(2));
            Assert.Equal(PinnedProductionBudgets.UpstreamProbeBudget, budget);
            var path = arguments[2];
            Assert.StartsWith(Path.Combine(root, ".lake") + Path.DirectorySeparatorChar, path, StringComparison.Ordinal);
            Sources.Add(File.ReadAllText(path));
            Paths.Add(path);
            if (Failure is not null) throw Failure;
            return Results.TryDequeue(out var result) ? result : new(0, Encoding.UTF8.GetBytes(Output), []);
        }
    }
}
