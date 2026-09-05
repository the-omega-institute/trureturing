using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CurrentEdgeValidatorTests
{
    [Theory]
    [InlineData("missing", "target-declaration-missing", "resolves to 0 current report declarations", false)]
    [InlineData("ambiguous", "target-declaration-ambiguous", "resolves to 2 current report declarations", false)]
    [InlineData("non-standard-axiom", "lean-state-tail", "current report module must be Closed", true)]
    public void CurrentEdgeValidatorRejectsInvalidCurrentEdge(
        string scenario,
        string expectedCode,
        string expectedDiagnostic,
        bool expectedResolved)
    {
        var spec = scenario switch
        {
            "missing" => new CoverSpec
            {
                ReportDeclarations = ["unrelated"],
            },
            "ambiguous" => new CoverSpec(),
            "non-standard-axiom" => new CoverSpec
            {
                TargetAxioms = ["customAxiom"],
            },
            _ => throw new ArgumentOutOfRangeException(nameof(scenario)),
        };
        var inputs = spec.Materialize();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(CoverWorld.Raw(inputs.Files))).Snapshot;
        var report = inputs.Report;
        if (scenario == "ambiguous")
        {
            var files = report.Files.ToDictionary(
                static pair => pair.Key.Value,
                static pair => pair.Value,
                StringComparer.Ordinal);
            var targetPath = spec.ModuleGid + ".lean";
            var declaration = Assert.Single(files[targetPath].Declarations);
            files[targetPath] = files[targetPath] with
            {
                Declarations =
                [
                    declaration,
                    declaration with { Name = "Namespace." + declaration.Name },
                ],
            };
            report = LeanAxiomReport.Create(files);
        }

        var lean = AcceptedLeanClosure.Create(report);
        var states = LeanTruthStates.Resolve(snapshot, lean);
        var result = CurrentEdgeValidator.Validate(
            inputs.Gid,
            snapshot,
            report,
            states,
            FrozenStatementIndex.Create(FrozenStateCatalog.Load(snapshot), report));

        Assert.Equal(expectedResolved, result.IsResolved);
        Assert.False(result.IsClosed);
        Assert.Equal(expectedCode, result.Code);
        Assert.Contains(expectedDiagnostic, result.Diagnostic, StringComparison.Ordinal);
    }

    [Fact]
    public void ExcludedDeclarationWithSameShortNameDoesNotMakeIncludedTargetAmbiguous()
    {
        var spec = new CoverSpec();
        var inputs = spec.Materialize();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(CoverWorld.Raw(inputs.Files))).Snapshot;
        var files = inputs.Report.Files.ToDictionary(
            static pair => pair.Key.Value,
            static pair => pair.Value,
            StringComparer.Ordinal);
        var targetPath = spec.ModuleGid + ".lean";
        var declaration = Assert.Single(files[targetPath].Declarations);
        files[targetPath] = files[targetPath] with
        {
            Declarations =
            [
                declaration,
                declaration with
                {
                    Name = "Private." + declaration.Name,
                    IncludeInStatement = false,
                },
            ],
        };
        var report = LeanAxiomReport.Create(files);
        var states = LeanTruthStates.Resolve(snapshot, AcceptedLeanClosure.Create(report));

        var result = CurrentEdgeValidator.Validate(
            inputs.Gid,
            snapshot,
            report,
            states,
            FrozenStatementIndex.Create(FrozenStateCatalog.Load(snapshot), report));

        Assert.True(result.IsResolved, result.Diagnostic);
        Assert.True(result.IsClosed, result.Diagnostic);
        Assert.Null(result.Code);
    }
}
