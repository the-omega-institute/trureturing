using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CurrentEdgeValidatorTests
{
    [Theory]
    [InlineData("missing", "target-declaration-missing", "resolves to 0 report declarations", false)]
    [InlineData("ambiguous", "target-declaration-ambiguous", "resolves to 2 report declarations", false)]
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
            "ambiguous" => new CoverSpec
            {
                ReportDeclarations = ["probe", "Namespace.probe"],
            },
            "non-standard-axiom" => new CoverSpec
            {
                TargetAxioms = ["customAxiom"],
            },
            _ => throw new ArgumentOutOfRangeException(nameof(scenario)),
        };
        var inputs = spec.Materialize();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(CoverWorld.Raw(inputs.Files))).Snapshot;
        var lean = AcceptedLeanClosure.Create(inputs.Report);
        var states = LeanTruthStates.Resolve(snapshot, lean);
        var result = CurrentEdgeValidator.Validate(inputs.Gid, snapshot, inputs.Report, states);

        Assert.Equal(expectedResolved, result.IsResolved);
        Assert.False(result.IsClosed);
        Assert.Equal(expectedCode, result.Code);
        Assert.Contains(expectedDiagnostic, result.Diagnostic, StringComparison.Ordinal);
    }
}
