using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeCheckAdmissionBoundaryTests
{
    [Fact]
    public void CanonicalScribeCheckPathDoesNotEnterAdmissionVerification()
    {
        var root = FindRepositoryRoot();
        var files = new[]
        {
            "Meta/StrataLint/scripts/scribe.sh",
            "Meta/StrataLint/StrataLint.Scribe/Emission/ScribeCli.cs",
            "Meta/StrataLint/StrataLint.Cli/Commands/Dag/DagRenderCommand.cs",
        }.Select(path => new GuardedSource(
            path,
            File.ReadAllText(Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar)))));

        Assert.Empty(ScribeAdmissionBoundaryPolicy.Inspect(files));
    }

    [Fact]
    public void DagRenderDispatchCallsRenderDagWithoutEnteringAdmissionCheck()
    {
        var environment = new StubCliEnvironment(
            new AdmissionOutcome.InfrastructureFailure("check must not be called"));
        var console = new BufferedConsole();

        CliApplication.Run(["dag-render", "--check"], environment, console);

        Assert.Equal(1, environment.RenderDagCallCount);
        Assert.Equal(0, environment.CheckCallCount);
    }

    [Fact]
    public void DagRenderImplementationDoesNotReferenceAdmissionSymbols()
    {
        var root = FindRepositoryRoot();
        var environment = File.ReadAllText(Path.Combine(
            root,
            "Meta/StrataLint/StrataLint.Cli/Admission/ProductionCliEnvironment.cs"));
        var renderDagStart = environment.IndexOf("public CommandResult RenderDag(", StringComparison.Ordinal);
        var nextMethod = environment.IndexOf("public CommandResult GenerateLedger(", renderDagStart, StringComparison.Ordinal);
        Assert.True(renderDagStart >= 0 && nextMethod > renderDagStart);
        var renderDag = environment[renderDagStart..nextMethod];
        Assert.DoesNotContain("VerifyScribeForAdmission", renderDag, StringComparison.Ordinal);
        Assert.DoesNotContain("Check", renderDag, StringComparison.Ordinal);

        var cli = File.ReadAllText(Path.Combine(root, "Meta/StrataLint/StrataLint.Cli/Commands/CliApplication.cs"));
        var handlerStart = cli.IndexOf("[\"dag-render\"]", StringComparison.Ordinal);
        var nextHandler = cli.IndexOf("[\"digest-status\"]", handlerStart, StringComparison.Ordinal);
        Assert.True(handlerStart >= 0 && nextHandler > handlerStart);
        var handler = cli[handlerStart..nextHandler];
        Assert.DoesNotContain("VerifyScribeForAdmission", handler, StringComparison.Ordinal);
        Assert.DoesNotContain("Check", handler, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionBoundaryPolicyRejectsTheForbiddenSymbolAsARedFixture()
    {
        var findings = ScribeAdmissionBoundaryPolicy.Inspect(
        [
            new GuardedSource(
                "Meta/StrataLint/scripts/scribe.sh",
                "ProductionCliEnvironment.VerifyScribeForAdmission(candidate)"),
        ]);

        var finding = Assert.Single(findings);
        Assert.Contains("scribe.sh:1", finding, StringComparison.Ordinal);
        Assert.Contains("VerifyScribeForAdmission", finding, StringComparison.Ordinal);
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}

internal sealed record GuardedSource(string Path, string Content);

internal static class ScribeAdmissionBoundaryPolicy
{
    private const string ForbiddenSymbol = "VerifyScribeForAdmission";

    internal static IReadOnlyList<string> Inspect(IEnumerable<GuardedSource> files) => files
        .SelectMany(static file => file.Content.Split('\n').Select((line, index) => (file.Path, Line: line, Number: index + 1)))
        .Where(static line => line.Line.Contains(ForbiddenSymbol, StringComparison.Ordinal))
        .Select(static line => $"{line.Path}:{line.Number}: {ForbiddenSymbol} is forbidden on the Scribe check path")
        .ToArray();
}
